-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnParts.lean
import AbsSatBingo.Model.ForbidOnTop
import AbsSatBingo.Model.TopsFrom
import AbsSatBingo.Model.SenderLink

/-!
# `TopSideAt` en piezas

`TopSideAt A B R`: una cima viva `t` de la unión fijada `pinOn (joinOn A B) R` está viva en un lado fijado. La
conclusión es «`t` está viva en `pinOn A R`», y un nodo sobrevive a un pin revisado si está en una estructura cerrada
del estado, con testigos buenos, que cumple los pins (`downInv_pinOn_core`). La estructura que se construye es **la
unión fijada, además, en el color del padre de `t`** (`b`, el nodo de mapa del remitente de su lado):
`u' = pinOn (joinOn A B) (R ++ [b])`. Hacen falta tres cosas:

1. **`TopKeepAt`** (hipótesis): fijar el color del padre de una cima viva no la mata. Habla solo de la unión.
2. **`sideGraph`** (demostrado): `u'` es, como grafo, parte del lado de `b`. Sus cimas son de ese lado (su padre tiene
   el color `b`), todo vivo es vecino de una cima, y toda arista tiene en la cima un testigo bueno, cuyo triángulo el
   join habría prohibido si el lado no tuviera la arista (`tF_joinOn_of_cut`).
3. **`TriSideAt`** (hipótesis): un triángulo de `u'` prohibido en el lado está prohibido en `u'`.

Con eso `u'` entero vive en `pinOn A (R ++ [b])` y, por la monotonía de los pins, en `pinOn A R`
(`topSideAt_of_parts`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Driver Machine MachineOn

-- ============================================================
-- El join guarda todo triángulo de la unión que cortan los dos lados
-- ============================================================

/-- **Un triángulo de la unión `:on` que cortan los dos lados está prohibido en la unión.** -/
theorem tF_joinOn_of_cut {g₁ g₂ : GPathB} (hea₁ : EdgesAlive g₁) (hea₂ : EdgesAlive g₂) {x y z : PathNodeId}
    (hxy : (joinOn g₁ g₂).Adj x y) (hxz : (joinOn g₁ g₂).Adj x z) (hyz : (joinOn g₁ g₂).Adj y z)
    (nxy : x ≠ y) (nxz : x ≠ z) (nyz : y ≠ z)
    (s1 : SideForbids g₁ (TF g₁) x y z) (s2 : SideForbids g₂ (TF g₂) x y z) : TF (joinOn g₁ g₂) x y z := by
  let U := join g₁ g₂
  obtain ⟨T', hT⟩ := joinOn_eq g₁ g₂
  have hadjU : ∀ x y, (joinOn g₁ g₂).Adj x y → U.Adj x y := fun x y h => by rw [hT] at h; exact h
  let u : GPathB := { join g₁ g₂ with trios := [] }
  have htr : (joinOn g₁ g₂).trios = (u.addTrios (Idx.of u) (joinForbid g₁ g₂)).1.trios := rfl
  have exy := hasEdge_of_adj (hadjU _ _ hxy) nxy
  have exz := hasEdge_of_adj (hadjU _ _ hxz) nxz
  have eyz := hasEdge_of_adj (hadjU _ _ hyz) nyz
  -- la arista x–y está en un lado, en algún orden
  obtain ⟨e, he, hj⟩ := List.any_eq_true.mp exy
  have he' : e ∈ g₁.edges ++ g₂.edges := by
    rcases List.mem_append.mp he with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_filter.mp h).1
  -- `z` es vecino de `e.1` en algún lado, y `e.2`–`z` es arista en algún lado
  have nbr_of : ∀ a, a ≠ z → U.hasEdge a z = true →
      z ∈ (Idx.of g₁).nbrs a ++ (Idx.of g₂).nbrs a ∧ ((Idx.of g₁).hasEdge a z || (Idx.of g₂).hasEdge a z) = true := by
    intro a haz he2
    obtain ⟨e', he2', hj'⟩ := List.any_eq_true.mp he2
    rcases List.mem_append.mp he2' with h | h
    · have hE : g₁.hasEdge a z = true := List.any_eq_true.mpr ⟨e', h, hj'⟩
      refine ⟨List.mem_append_left _ ((idx_mem_nbrs g₁ a z).mpr ⟨fun h => haz h.symm, (hea₁ a z (by
        unfold Adj adjb; simp [hE])).2, hE⟩), by simp [idx_hasEdge, hE]⟩
    · have hE : g₂.hasEdge a z = true := List.any_eq_true.mpr ⟨e', (List.mem_filter.mp h).1, hj'⟩
      refine ⟨List.mem_append_right _ ((idx_mem_nbrs g₂ a z).mpr ⟨fun h => haz h.symm, (hea₂ a z (by
        unfold Adj adjb; simp [hE])).2, hE⟩), by simp [idx_hasEdge, hE]⟩
  have hcov : ∃ t ∈ joinForbid g₁ g₂, trioIs x y z t = true := by
    rcases (joins_iff x y e).mp hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨(e.1, e.2, z), ?_, by rw [h1, h2]; exact trioIs_self x y z⟩
      unfold joinForbid
      refine List.mem_flatMap.mpr ⟨e, he', List.mem_map.mpr ⟨z, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩⟩
      · rw [h1]; exact (nbr_of x nxz exz).1
      · rw [h1, h2]
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, idx_sideForbids]
        exact ⟨⟨⟨fun h => nyz h.symm, by rw [← adj_symm] at hyz; exact (nbr_of y nyz eyz).2⟩,
          B_of_sideForbids nxy nxz nyz s1⟩, B_of_sideForbids nxy nxz nyz s2⟩
    · refine ⟨(e.1, e.2, z), ?_, by rw [h1, h2]; exact trioIs_swap12 (trioIs_self y x z)⟩
      unfold joinForbid
      refine List.mem_flatMap.mpr ⟨e, he', List.mem_map.mpr ⟨z, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩⟩
      · rw [h1]; exact (nbr_of y nyz eyz).1
      · rw [h1, h2]
        have tsw : ∀ a b r, TF g₁ b a r → TF g₁ a b r := fun _ _ _ h => tF_swap12 h
        have tsw2 : ∀ a b r, TF g₂ b a r → TF g₂ a b r := fun _ _ _ h => tF_swap12 h
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, idx_sideForbids]
        exact ⟨⟨⟨fun h => nxz h.symm, (nbr_of x nxz exz).2⟩,
          B_of_sideForbids (Ne.symm nxy) nyz nxz (sideForbids_swap12 tsw s1)⟩,
          B_of_sideForbids (Ne.symm nxy) nyz nxz (sideForbids_swap12 tsw2 s2)⟩
  obtain ⟨t, ht, hti⟩ := hcov
  refine ⟨nxy, ?_⟩
  unfold deadTrio
  rw [Bool.and_eq_true]
  refine ⟨by rw [hT]; exact exy, ?_⟩
  rw [htr]
  rcases addTrios_covers u (Idx.of u) _ t ht with h | h
  · obtain ⟨t', ht', hti'⟩ := List.any_eq_true.mp h
    -- `trioIs x y z t` y `trioIs t t'`: `t'` es un orden de `{x, y, z}`
    refine List.any_eq_true.mpr ⟨t', ht', ?_⟩
    obtain ⟨a, b, c⟩ := t
    simp only [trioIs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hti
    rcases hti with (((((⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) |
      ⟨⟨h1, h2⟩, h3⟩) <;> subst h1 <;> subst h2 <;> subst h3 <;>
      (obtain ⟨p, q, w⟩ := t'; simp only [trioIs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hti' ⊢;
       rcases hti' with (((((⟨⟨k1, k2⟩, k3⟩ | ⟨⟨k1, k2⟩, k3⟩) | ⟨⟨k1, k2⟩, k3⟩) | ⟨⟨k1, k2⟩, k3⟩) |
         ⟨⟨k1, k2⟩, k3⟩) | ⟨⟨k1, k2⟩, k3⟩) <;> subst k1 <;> subst k2 <;> subst k3 <;> simp)
  · exfalso
    rw [idx_deadTrio] at h
    unfold deadTrio at h
    simp [u] at h

-- ============================================================
-- Sobrevivir a un pin revisado: la estructura con testigos buenos
-- ============================================================

/-- **Un estado en el punto fijo de la regla vive entero en cualquier estado fijado que lo contenga**: si `s` (entero)
cumple el invariante en `x` y los pins `R`, lo cumple en `pinOn x R`. -/
theorem downInv_pinOn_core {s x : GPathB} {c : Int} {R : List NodeId} (hfix : FixClosed s) (hnd : NoDegT s)
    (hc : c ≤ s.current_step) (h0 : DownInv (LowV s c) (LowR s c) (TF s) c x)
    (hagree : ∀ p ∈ R, SecAgrees (LowV s c) p) :
    DownInv (LowV s c) (LowR s c) (TF s) c (x.pinOn R) := by
  have hTG : TrioGood (LowV s c) (LowR s c) (TF s) c := trioGood_low hfix hnd hc
  have hsymm : ∀ {y w}, LowR s c y w → LowR s c w y :=
    fun hr => ⟨⟨hr.1.2.1, hr.1.1, (adj_symm s _ _).mp hr.1.2.2⟩, hr.2.2, hr.2.1⟩
  have hfold : ∀ (l : List NodeId) (z : GPathB), (∀ p ∈ l, SecAgrees (LowV s c) p) →
      DownInv (LowV s c) (LowR s c) (TF s) c z → DownInv (LowV s c) (LowR s c) (TF s) c (l.foldl filterRequire z) := by
    intro l
    induction l with
    | nil => intro z _ hz; exact hz
    | cons p ps ih =>
      intro z hl hz
      rw [List.foldl_cons]
      exact ih _ (fun p' hp' => hl p' (List.mem_cons_of_mem _ hp')) (downInv_filterRequire hz (hl p List.mem_cons_self))
  have h1 := hfold _ x hagree h0
  have h2 : DownInv (LowV s c) (LowR s c) (TF s) c { R.foldl filterRequire x with dirty := true } :=
    downInv_shrink h1 (shrinks_dirty _ true).1 rfl (sec_dirty h1.sec true) h1.ns
  exact downInv_reviewOn h2 hTG hsymm

/-- **Una estructura de `s` cuyos nodos y parejas son de `A` es una estructura de `A`**: los enlaces pasan por la
completitud de los de `A` y la compatibilidad de los de `s`. -/
theorem secStruct_of_graphSub {s A : GPathB} {V : PathNodeId → Prop} {Rr : PathNodeId → PathNodeId → Prop}
    (hsec : SecStruct s V Rr) (hcs : s.current_step = A.current_step) (h1 : ∀ y, V y → y ∈ A.alive)
    (h2 : ∀ y w, Rr y w → A.Adj y w) (hlis : LinksInv s) (hliA : LinksInv A) : SecStruct A V Rr := by
  -- un padre (o hijo) del documento de `s`, relacionado en la estructura, lo es del documento de `A`
  have par : ∀ {y p : PathNodeId} {n m : PNodeB}, s.node? y = some n → A.node? y = some m → p ∈ n.parents →
      Rr y p → p ∈ m.parents := by
    intro y p n m hn hm hp hR
    have hcomp := (hlis.2.2 n (node?_mem hn)).1 p hp
    rw [node?_id hn] at hcomp
    exact (hliA.2.1 m (node?_mem hm) p (h1 p (hsec.dom hR).2) (by rw [node?_id hm]; exact h2 _ _ hR)).1
      (by rw [node?_id hm]; exact hcomp)
  have son : ∀ {y q : PathNodeId} {n m : PNodeB}, s.node? y = some n → A.node? y = some m → q ∈ n.sons →
      Rr y q → q ∈ m.sons := by
    intro y q n m hn hm hq hR
    have hcomp := (hlis.2.2 n (node?_mem hn)).2 q hq
    rw [node?_id hn] at hcomp
    exact (hliA.2.1 m (node?_mem hm) q (h1 q (hsec.dom hR).2) (by rw [node?_id hm]; exact h2 _ _ hR)).2
      (by rw [node?_id hm]; exact hcomp)
  refine ⟨fun hy => h1 _ hy, hsec.refl, hsec.symm, hsec.dom, fun hr => h2 _ _ hr,
    fun hr l h0 hl => hsec.pair hr l h0 (by rw [hcs]; exact hl), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn, hp, hs⟩ := hsec.node hy
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hliA.1 (h1 y hy))
    refine ⟨m, hm, fun hpar => ?_, fun hson => ?_⟩
    · obtain ⟨p, hpp, hR⟩ := hp hpar
      exact ⟨p, par hn hm hpp hR, hR⟩
    · obtain ⟨q, hq, hR⟩ := hs (by rw [hcs]; exact hson)
      exact ⟨q, son hn hm hq hR, hR⟩
  · intro x w m hR hne hm hst
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hlis.1 (hsec.alive (hsec.dom hR).1))
    obtain ⟨p, hp, hxp, hpw⟩ := hsec.par hR hne hn hst
    exact ⟨p, par hn hm hp hxp, hxp, hpw⟩
  · intro x w m hR hne hm hst
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hlis.1 (hsec.alive (hsec.dom hR).1))
    obtain ⟨q, hq, hxq, hqw⟩ := hsec.son hR hne hn (by rw [hcs]; exact hst)
    exact ⟨q, son hn hm hq hxq, hxq, hqw⟩

-- ============================================================
-- Pieza 2 (demostrada): la unión fijada en el color de un lado es parte de ese lado
-- ============================================================

/-- **La unión fijada en el color `b` de los padres de las cimas del lado `S` es, como grafo, parte de `S`.** `O` es
el otro lado: sus cimas no tienen padre de color `b`, y `J` prohíbe todo triángulo suyo cuya arista no sea de `S` y
cuyo tercer nodo no esté en `O` (`hcut`, que para el join `:on` es `tF_joinOn_of_cut`). -/
theorem sideGraph {J S O : GPathB} {R' : List NodeId} {b : NodeId} (hJ : SInvB J) (hnsJ : NoSelf J)
    (hndJ : NoDegT J) (hc2 : 2 ≤ J.current_step) (hv : (J.pinOn R').isValid = true) (hb : b ∈ R')
    (hbs : b.step = J.current_step - 2)
    (halive : ∀ q ∈ J.alive, q ∈ S.alive ∨ q ∈ O.alive) (hadj : ∀ x w, J.Adj x w → S.Adj x w ∨ O.Adj x w)
    (heS : EdgesAlive S) (heO : EdgesAlive O)
    (hO : ∀ t ∈ O.alive, t.id.step = J.current_step - 1 → t.parent_id ≠ some b)
    (hcut : ∀ {x y z}, J.Adj x y → J.Adj x z → J.Adj y z → x ≠ y → x ≠ z → y ≠ z → ¬ S.Adj x y → z ∉ O.alive →
      TF J x y z) :
    (∀ q ∈ (J.pinOn R').alive, q ∈ S.alive) ∧ (∀ x w, (J.pinOn R').Adj x w → S.Adj x w) := by
  let s := J.pinOn R'
  let c := J.current_step
  have hcss : s.current_step = c := step_pinOn J R'
  have his : SInvB s := sInvB_pinOn hJ R'
  have hbs' : ∀ q ∈ s.alive, q.id.step < c := fun q hq => by
    have := alive_below his.docs his.below hq; rw [hcss] at this; exact this
  have hcl : ClosedState s := closedState_pinOn hJ hv hc2
  have hfix : FixClosed s := fixClosed_reviewOn (g := { R'.foldl filterRequire J with dirty := true }) rfl hv
  have hTG : TrioGood (LowV s c) (LowR s c) (TF s) c :=
    trioGood_low hfix (noDegT_pinOn hnsJ hndJ R') (by rw [hcss]; exact Int.le_refl _)
  have hsub : Sub s J := sub_pinOn J R'
  -- las cimas de `s` son de `S` y no de `O`: su padre tiene el color `b`
  have topfact : ∀ t ∈ s.alive, t.id.step = c - 1 → t ∈ S.alive ∧ t ∉ O.alive := by
    intro t ht hts
    obtain ⟨r, hrs, htr, _⟩ := hcl.pair (hcl.refl ht) (c - 2) (by omega) (by rw [hcss]; omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive his.docs ht)
    have hne : t ≠ r := by intro e; rw [← e, hts] at hrs; omega
    obtain ⟨p, hp, htp, _⟩ := hcl.par htr hne hn (by rw [hts]; omega)
    have hcomp := (his.links.2.2 n (node?_mem hn)).1 p hp
    rw [node?_id hn] at hcomp
    have hpid : p.id = b := pinned_pinOn hJ.docs hv b hb p htp.2.1 (by rw [hbs]; have := hcomp.2.2; omega)
    have hpar : t.parent_id = some b := by rw [hcomp.1, hpid]
    have hnO : t ∉ O.alive := fun h => hO t h hts hpar
    rcases halive t (hsub.alive t ht) with h | h
    · exact ⟨h, hnO⟩
    · exact absurd h hnO
  -- una arista de `s` con un extremo fuera de `O` es de `S`
  have key : ∀ a b', s.Adj a b' → a ∉ O.alive → S.Adj a b' := fun a b' h hn =>
    (hadj a b' (hsub.adj _ _ h)).resolve_right (fun ho => hn (heO a b' ho).1)
  have nodes : ∀ q ∈ s.alive, q ∈ S.alive := by
    intro q hq
    obtain ⟨r, hrs, hqr, _⟩ := hcl.pair (hcl.refl hq) (c - 1) (by omega) (by rw [hcss]; omega)
    obtain ⟨_, hrO⟩ := topfact r hqr.2.1 hrs
    exact (heS r q (key r q ((adj_symm s _ _).mp hqr.2.2) hrO)).2
  refine ⟨nodes, fun x w hxw => ?_⟩
  have hx := (his.edges x w hxw).1
  have hw := (his.edges x w hxw).2
  by_cases hxe : x = w
  · subst hxe; exact adj_refl S x (nodes x hx)
  · obtain ⟨s0, hs0, hxs, hws, hcase⟩ := hTG.edge (a := x) (b := w) ⟨⟨hx, hw, hxw⟩, hbs' x hx, hbs' w hw⟩ hxe
      (c - 1) (by omega) (by omega)
    obtain ⟨_, hs0O⟩ := topfact s0 hxs.1.2.1 hs0
    by_cases h1 : s0 = x
    · rw [h1] at hs0O; exact key x w hxw hs0O
    · by_cases h2 : s0 = w
      · rw [h2] at hs0O; exact (adj_symm S _ _).mp (key w x ((adj_symm s _ _).mp hxw) hs0O)
      · apply Classical.byContradiction
        intro hno
        have hJf : TF J x w s0 := hcut (hsub.adj _ _ hxw) (hsub.adj _ _ hxs.1.2.2) (hsub.adj _ _ hws.1.2.2) hxe
          (Ne.symm h1) (Ne.symm h2) hno hs0O
        have hsf : TF s x w s0 := tF_mono (trios_grow_pinOn J R') hxw hJf
        rcases hcase with e | e | e
        · exact h1 e
        · exact h2 e
        · exact e hsf

-- ============================================================
-- Las dos hipótesis y el teorema
-- ============================================================

/-- **Pieza 1, `TopKeepAt`**: fijar además el color del padre de una cima viva no la mata. Habla solo de `J`. -/
def TopKeepAt (J : GPathB) (R : List NodeId) : Prop :=
  (J.pinOn R).isValid = true → ∀ t ∈ (J.pinOn R).alive, t.id.step = J.current_step - 1 → ∀ b, t.parent_id = some b →
    (J.pinOn (R ++ [b])).isValid = true ∧ t ∈ (J.pinOn (R ++ [b])).alive

/-- **Pieza 3, `TriSideAt`**: un triángulo de `pinOn J R'` prohibido en el lado `S` (sin fijar) está prohibido en
`pinOn J R'`. -/
def TriSideAt (S J : GPathB) (R' : List NodeId) : Prop :=
  (J.pinOn R').isValid = true → ∀ a b r, (J.pinOn R').Adj a b → (J.pinOn R').Adj a r → (J.pinOn R').Adj b r →
    TF S a b r → TF (J.pinOn R') a b r

/-- **Si `pinOn J R'` es parte de `S` como grafo y cumple `TriSideAt`, vive entero en `pinOn S R`** (`R ⊆ R'`). -/
theorem side_of_parts {J S : GPathB} {R R' : List NodeId} (hRR : ∀ p ∈ R, p ∈ R') (hJ : SInvB J) (hnsJ : NoSelf J)
    (hndJ : NoDegT J) (hS : SInvB S) (hnsS : NoSelf S) (hcs : J.current_step = S.current_step)
    (hc2 : 2 ≤ J.current_step) (hv : (J.pinOn R').isValid = true)
    (hg1 : ∀ q ∈ (J.pinOn R').alive, q ∈ S.alive) (hg2 : ∀ x w, (J.pinOn R').Adj x w → S.Adj x w)
    (htri : TriSideAt S J R') :
    ∀ q ∈ (J.pinOn R').alive, (S.pinOn R).isValid = true ∧ q ∈ (S.pinOn R).alive := by
  let s := J.pinOn R'
  let c := J.current_step
  have hcss : s.current_step = c := step_pinOn J R'
  have his : SInvB s := sInvB_pinOn hJ R'
  have hbs' : ∀ q ∈ s.alive, q.id.step < c := fun q hq => by
    have := alive_below his.docs his.below hq; rw [hcss] at this; exact this
  have hcl : ClosedState s := closedState_pinOn hJ hv hc2
  have hfix : FixClosed s := fixClosed_reviewOn (g := { R'.foldl filterRequire J with dirty := true }) rfl hv
  have hsecS : SecStruct S (LowV s c) (LowR s c) :=
    secStruct_of_graphSub (closed_low hcl hbs') (hcss.trans hcs) (fun y hy => hg1 y hy.1)
      (fun y w hr => hg2 y w hr.1.2.2) his.links hS.links
  have h0 : DownInv (LowV s c) (LowR s c) (TF s) c S :=
    ⟨hsecS, hnsS, hcs.symm, fun hab har hbr hf => htri hv _ _ _ hab.1.2.2 har.1.2.2 hbr.1.2.2 hf⟩
  have hX := downInv_pinOn_core (R := R) hfix (noDegT_pinOn hnsJ hndJ R') (by rw [hcss]; exact Int.le_refl _) h0
    (fun p hp q hq hqs => pinned_pinOn hJ.docs hv p (hRR p hp) q hq.1 hqs)
  intro q hq
  exact ⟨isValid_of_sec hX.sec (y := q) ⟨hq, hbs' q hq⟩, hX.sec.alive ⟨hq, hbs' q hq⟩⟩

/-- **`TopSideAt` desde sus piezas.** `bA`, `bB`: los colores de los padres de las cimas de cada lado (los nodos de
mapa de sus remitentes), distintos. Bajo `TopKeepAt` en la unión y `TriSideAt` de cada lado en la unión fijada en su
color, una cima viva de la unión fijada está viva en su lado fijado. -/
theorem topSideAt_of_parts {A B : GPathB} {R : List NodeId} {bA bB : NodeId} (hA : SInvB A) (hB : SInvB B)
    (hnsA : NoSelf A) (hnsB : NoSelf B) (hcs : A.current_step = B.current_step) (hc2 : 2 ≤ A.current_step)
    (hbA : bA.step = A.current_step - 2) (hbB : bB.step = A.current_step - 2) (hne : bA ≠ bB)
    (hfA : TopsFrom A (fun a => a = bA)) (hfB : TopsFrom B (fun a => a = bB))
    (hk : TopKeepAt (joinOn A B) R) (htA : TriSideAt A (joinOn A B) (R ++ [bA]))
    (htB : TriSideAt B (joinOn A B) (R ++ [bB])) : TopSideAt A B R := by
  intro hv t ht hts
  have hcsJ : (joinOn A B).current_step = A.current_step := step_joinOn A B
  have hJ : SInvB (joinOn A B) := sInvB_joinOn hA hB hcs
  have hnsJ : NoSelf (joinOn A B) := noSelf_joinOn hnsA hnsB
  have hndJ : NoDegT (joinOn A B) := noDegT_joinOn hnsA hnsB hA.edges hB.edges
  obtain ⟨T', hT⟩ := joinOn_eq A B
  have halive : ∀ q ∈ (joinOn A B).alive, q ∈ A.alive ∨ q ∈ B.alive := fun q hq => by
    rw [hT] at hq; exact (alive_join A B q).mp hq
  have hadj : ∀ x w, (joinOn A B).Adj x w → A.Adj x w ∨ B.Adj x w := fun x w h => by
    rw [hT] at h; exact adj_join_cases h
  have parA : ∀ q ∈ A.alive, q.id.step = A.current_step - 1 → q.parent_id = some bA := fun q hq hs => by
    obtain ⟨a, rfl, hp⟩ := hfA q hq hs; exact hp
  have parB : ∀ q ∈ B.alive, q.id.step = A.current_step - 1 → q.parent_id = some bB := fun q hq hs => by
    obtain ⟨a, rfl, hp⟩ := hfB q hq (by rw [← hcs]; exact hs); exact hp
  rcases halive t ((sub_pinOn _ R).alive t ht) with htA' | htB'
  · -- la cima es del lado `A`
    obtain ⟨hv', ht'⟩ := hk hv t ht (by rw [hcsJ]; exact hts) bA (parA t htA' hts)
    obtain ⟨g1, g2⟩ := sideGraph (S := A) (O := B) (b := bA) hJ hnsJ hndJ (by rw [hcsJ]; exact hc2) hv'
      (List.mem_append_right _ (List.mem_singleton_self _)) (by rw [hcsJ]; exact hbA) halive hadj hA.edges hB.edges
      (fun q hq hs hp => by
        rw [hcsJ] at hs
        have := parB q hq hs; rw [this] at hp; exact hne (Option.some.inj hp).symm)
      (fun hxy hxz hyz nxy nxz nyz hno hz => tF_joinOn_of_cut hA.edges hB.edges hxy hxz hyz nxy nxz nyz
        (Or.inl fun h => hno h.1) (Or.inl fun h => hz (hB.edges _ _ h.2.1).2))
    exact Or.inl (side_of_parts (R := R) (fun p hp => List.mem_append_left _ hp) hJ hnsJ hndJ hA hnsA hcsJ
      (by rw [hcsJ]; exact hc2) hv' g1 g2 htA t ht')
  · -- la cima es del lado `B`
    obtain ⟨hv', ht'⟩ := hk hv t ht (by rw [hcsJ]; exact hts) bB (parB t htB' hts)
    obtain ⟨g1, g2⟩ := sideGraph (S := B) (O := A) (b := bB) hJ hnsJ hndJ (by rw [hcsJ]; exact hc2) hv'
      (List.mem_append_right _ (List.mem_singleton_self _)) (by rw [hcsJ]; exact hbB)
      (fun q hq => (halive q hq).symm) (fun x w h => (hadj x w h).symm) hB.edges hA.edges
      (fun q hq hs hp => by
        rw [hcsJ] at hs
        have := parA q hq hs; rw [this] at hp; exact hne (Option.some.inj hp))
      (fun hxy hxz hyz nxy nxz nyz hno hz => tF_joinOn_of_cut hA.edges hB.edges hxy hxz hyz nxy nxz nyz
        (Or.inl fun h => hz (hA.edges _ _ h.2.1).2) (Or.inl fun h => hno h.1))
    exact Or.inr (side_of_parts (R := R) (fun p hp => List.mem_append_left _ hp) hJ hnsJ hndJ hB hnsB
      (hcsJ.trans hcs) (by rw [hcsJ]; exact hc2) hv' g1 g2 htB t ht')

-- ============================================================
-- En la máquina: las cimas de una llegada tienen por padre la clave de su remitente
-- ============================================================

theorem trioBlind_topsFrom (A : NodeId → Prop) : TrioBlind (fun g => TopsFrom g A) := fun _ _ h => h

/-- Lo que hace falta de una llegada `:on` válida para aplicar `topSideAt_of_parts`. -/
theorem arrOn_tops {φ : Cnf} {T : Int} (hT : 1 ≤ T) {kv : NodeId × GPathB} (hent : EntOn T kv.1 kv.2)
    (htid : TopDocsId kv.2 kv.1) {d : NodeId} (hs : SendsOn φ kv d) :
    TopsFrom (arrOn φ kv d) (fun a => a = kv.1) ∧ TopDocsId (arrOn φ kv d) d := by
  have hok := hent.1
  let Y := kv.2.filterAllOn (reqOf φ d)
  have hd : d.step = Y.current_step := by
    rw [step_filterAllOn, sonsOfMap_step φ kv.1 d hs.1, hok.key, hok.step]; omega
  have hvY : Y.isValid = true := valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
  have hsh := shrinks_filterAllOn kv.2 (reqOf φ d)
  have hbY : Below Y := below_filterAllOn hok.below _
  have hdY : AliveDocs Y := docs_filterAllOn hok.docs _
  have htY : TopDocsId Y kv.1 := topDocsId_of_shrinks hsh htid
  obtain ⟨T', hT'⟩ := upOn_eq (g := Y) (d := d) (title := "") (forb := isProhibited φ) hvY
  have e : arrOn φ kv d = ((Y.addNode d "" (isProhibited φ)).setT T').reviewOn := hT'
  rw [e]
  constructor
  · apply revPrims_reviewOn (revPrims_topsFrom _) (trioBlind_topsFrom _)
    exact topsFrom_addNode (title := "") (forb := isProhibited φ) hdY hbY hd
      (by rw [step_filterAllOn, hok.step]; omega) htY
  · exact topDocsId_of_shrinks (shrinks_reviewOn _) (topDocsId_addNode (title := "") (forb := isProhibited φ) hbY)

/-- **Las piezas en los joins de la máquina**: `TopKeepAt` en la unión y `TriSideAt` de cada llegada en la unión
fijada en la clave de su remitente, para los pins de `PinsFrom`. -/
def HPartsOn (φ : Cnf) (line : Line) : Prop :=
  ∀ a ∈ line, ∀ b ∈ line, a.1 ≠ b.1 → ∀ d, SendsOn φ a d → SendsOn φ b d → ∀ R, PinsFrom φ d R →
    TopKeepAt (joinOn (arrOn φ a d) (arrOn φ b d)) R ∧
    TriSideAt (arrOn φ a d) (joinOn (arrOn φ a d) (arrOn φ b d)) (R ++ [a.1]) ∧
    TriSideAt (arrOn φ b d) (joinOn (arrOn φ a d) (arrOn φ b d)) (R ++ [b.1])

/-- **Las piezas dan `TopSideAt` en los joins de la línea.** -/
theorem hTopOn_of_parts {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (htid : ∀ kv ∈ line, TopDocsId kv.2 kv.1) (hp : HPartsOn φ line) : HTopOn φ line := by
  intro a ha b hb hab d hsa hsb R hR
  obtain ⟨ea, ia, _, _, _⟩ := arrTop_facts hT h ha hsa
  obtain ⟨eb, ib, _, _, _⟩ := arrTop_facts hT h hb hsb
  obtain ⟨fa, _⟩ := arrOn_tops hT (h.on a ha) (htid a ha) hsa
  obtain ⟨fb, _⟩ := arrOn_tops hT (h.on b hb) (htid b hb) hsb
  obtain ⟨hk, hta, htb⟩ := hp a ha b hb hab d hsa hsb R hR
  exact topSideAt_of_parts ia ib ea.2.1 eb.2.1 (ea.1.step.trans eb.1.step.symm) (by rw [ea.1.step]; omega)
    (by rw [ea.1.step, (h.on a ha).1.key]; omega) (by rw [ea.1.step, (h.on b hb).1.key]; omega) hab fa fb hk hta htb

/-- Las cimas de las entradas de la línea siguiente tienen por id su clave. -/
theorem tid_advance {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (htid : ∀ kv ∈ line, TopDocsId kv.2 kv.1) : ∀ E ∈ advanceM .on φ line, TopDocsId E.2 E.1 := by
  intro E hE
  rcases entry_shapeOn (line_cases h.nodup h.keys) h.nodup hE with ⟨kv, hkv, hs, he⟩ |
    ⟨a, ha, b, hb, _, hsa, hsb, he⟩
  · rw [he]; exact (arrOn_tops hT (h.on kv hkv) (htid kv hkv) hs).2
  · obtain ⟨ea, _⟩ := arrTop_facts hT h ha hsa
    obtain ⟨eb, _⟩ := arrTop_facts hT h hb hsb
    have hjoin : doJoinOn (arrOn φ a E.1) (arrOn φ b E.1) = joinOn (arrOn φ a E.1) (arrOn φ b E.1) := by
      unfold doJoinOn okJoin
      rw [if_pos (by simp [ea.1.step, eb.1.step, ea.1.mp, eb.1.mp, ea.1.valid, eb.1.valid])]
    obtain ⟨T', hT'⟩ := joinOn_eq (arrOn φ a E.1) (arrOn φ b E.1)
    rw [he, hjoin, hT']
    exact topDocsId_join (arrOn_tops hT (h.on a ha) (htid a ha) hsa).2 (arrOn_tops hT (h.on b hb) (htid b hb) hsb).2
      (ea.1.step.trans eb.1.step.symm)

/-- **La hipótesis en piezas**, en cada línea de la máquina `:on`. -/
def HypsPartsOn (φ : Cnf) : Prop := ∀ n : Nat, HPartsOn φ (stepsM .on φ n (initM .on φ))

theorem lInvParts_steps {φ : Cnf} (H : HypsPartsOn φ) :
    ∀ n : Nat, LInvTop φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) ∧
      ∀ kv ∈ stepsM .on φ n (initM .on φ), TopDocsId kv.2 kv.1 := by
  intro n
  induction n with
  | zero =>
    refine ⟨lInvTop_init φ, ?_⟩
    show ∀ kv ∈ initM .on φ, TopDocsId kv.2 kv.1
    rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    obtain ⟨T', hT'⟩ := upOn_eq (g := GPathB.empty) (d := (⟨0, 0⟩ : NodeId)) (title := "")
      (forb := fun _ => false) (by rfl)
    have e : initSeedOn (⟨0, 0⟩ : NodeId) "" = ((GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)).setT T').reviewOn :=
      hT'
    show TopDocsId (initSeedOn (⟨0, 0⟩ : NodeId) "") ⟨0, 0⟩
    rw [e]
    exact topDocsId_of_shrinks (shrinks_reviewOn _)
      (topDocsId_addNode (g := GPathB.empty) (title := "") (forb := fun _ => false)
        (fun n hn => absurd hn List.not_mem_nil))
  | succ n ih =>
    obtain ⟨hl, htid⟩ := ih
    have hT : (1 : Int) ≤ (n : Int) + 1 := by omega
    rw [stepsM_succ]
    have := lInvTop_advance hT hl (hTopOn_of_parts hT hl htid (H n))
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact ⟨this, tid_advance hT hl htid⟩

/-- Las piezas dan la hipótesis de cimas. -/
theorem hypsTopOn_of_parts {φ : Cnf} (H : HypsPartsOn φ) : HypsTopOn φ := fun n =>
  hTopOn_of_parts (by omega) (lInvParts_steps H n).1 (lInvParts_steps H n).2 (H n)

end GPathB

namespace MachineOn

open GPathB Driver

/-- **La espina con la regla activa decide la satisfacibilidad bajo las dos piezas de `TopSideAt`** en los joins de la
máquina: fijar el color del padre de una cima viva de la unión no la mata (`TopKeepAt`), y un triángulo de la unión
fijada en el color de un lado que ese lado prohíbe está prohibido en ella (`TriSideAt`). -/
theorem spineVerdictOn_iff_of_parts {φ : Cnf} (hbd : Bounded φ) (H : HypsPartsOn φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_topOn hbd (hypsTopOn_of_parts H)

end MachineOn

end AbsSatBingo.Model
