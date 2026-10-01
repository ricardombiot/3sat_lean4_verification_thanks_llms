-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnStar.lean
import AbsSatBingo.Model.ForbidOnKeep
import AbsSatBingo.Model.TopNbr

/-!
# «El primero que muere» en la estrella de la cima

`TopSideAt` pide que una cima viva `t` de la unión fijada `u = pinOn (joinOn A B) R` esté viva en su lado fijado
`pinOn A R`. La estructura que se lleva al lado es **la familia de `t` en `u`**:

* nodos: `t` y sus vecinos en `u`;
* parejas: las de `u` entre esos nodos cuyo trío con `t` no está prohibido en `u` (y las de `t`).

Es una estructura cerrada del lado sin fijar (`secStruct_star`): sus aristas son del lado porque el join habría
prohibido el triángulo con `t`, y sus testigos salen del punto fijo de la regla en `u`. Todo lo que contiene a `t`
tiene testigo propio. Lo único que no lo tiene son los triángulos entre vecinos de `t` que no contienen a `t`, y esa es
la hipótesis:

**`StarTriAt`**: un triángulo `(a, b, r)` entre vecinos de `t`, vivo en `u` y con sus tres caras con `t` vivas en `u`,
no está en la lista de tríos de `pinOn A R`.

Con ella, la familia entera sobrevive al review de `pinOn A R` (`downInv_pinOnK`), y en particular `t`
(`topSideAt_of_starTri`). Es una hipótesis de tríos; ya no habla de la supervivencia de nodos ni de aristas.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Driver Machine MachineOn

-- ============================================================
-- Vecinos en pasos consecutivos: padre e hijo
-- ============================================================

/-- **Dos vecinos en pasos consecutivos son compatibles** (el de abajo es padre posible del de arriba): las aristas
entre pasos consecutivos solo las crea la fila nueva, de un nodo a sus padres. -/
def AdjPar (g : GPathB) : Prop := ∀ x s, g.Adj x s → s.id.step + 1 = x.id.step → Compat s x

theorem adjPar_of_sub {h g : GPathB} (hs : Sub h g) (hg : AdjPar g) : AdjPar h :=
  fun x s h1 h2 => hg x s (hs.adj _ _ h1) h2

theorem adjPar_join {e g : GPathB} (he : AdjPar e) (hg : AdjPar g) : AdjPar (join e g) := by
  intro x s h h2
  rcases adj_join_cases h with h | h
  · exact he x s h h2
  · exact hg x s h h2

theorem adjPar_setT {g : GPathB} (hg : AdjPar g) (T : List (PathNodeId × PathNodeId × PathNodeId)) :
    AdjPar (g.setT T) := fun x s h h2 => hg x s h h2

theorem adjPar_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool} (hta : TopsApart g)
    (hd : d.step = g.current_step) (hg : AdjPar g) :
    AdjPar (g.addNode d title forb) := by
  intro x s h h2
  rw [adj_iff] at h
  rcases h with ⟨rfl, _⟩ | ⟨e, he, hj⟩
  · omega
  · rcases List.mem_append.mp he with hold | hnew
    · exact hg x s ((adj_iff g x s).mpr (Or.inr ⟨e, hold, hj⟩)) h2
    · obtain ⟨pid, hpid, he'⟩ := List.mem_flatMap.mp hnew
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp he'
      have hps := newRow_step hd hpid
      have ⟨hw1, hw2⟩ := List.mem_filter.mp hw'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw2
      obtain ⟨hlt, hsup⟩ := hw2
      obtain ⟨p, hp, hpw⟩ := List.any_eq_true.mp hsup
      rcases hj with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have e1 : pid = x := e1
        have e2 : w' = s := e2
        subst e1; subst e2
        obtain ⟨_, _, _, hpst⟩ := step_of_newParents (rowParents_sub hp)
        have hpeq : p = w' := hta p w' hpst (by omega) hpw
        subst hpeq
        exact compat_rowParents hd hp
      · exfalso
        have e1 : pid = s := e1
        have e2 : w' = x := e2
        subst e1; subst e2
        omega

-- ============================================================
-- El cierre simétrico de los tríos
-- ============================================================

theorem sym_perm {F : Trios} {a b r p q w : PathNodeId} (h : Sym F p q w) (hp : (p, q, w) ∈ perms a b r) :
    Sym F a b r := by
  simp only [perms, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ <;> (unfold Sym at h ⊢; rcases h with h | h | h | h | h | h <;> simp [h])

theorem nsym_perm {F : Trios} {a b r p q w : PathNodeId} (h : ¬ Sym F a b r) (hp : (p, q, w) ∈ perms a b r) :
    ¬ Sym F p q w := fun hs => h (sym_perm hs hp)

/-- En un triángulo de la parte baja de `u`, el cierre simétrico de sus tríos es lo mismo que sus tríos. -/
theorem tF_of_sym {u : GPathB} {c : Int} (hTG : TrioGood (LowV u c) (LowR u c) (TF u) c) {a b r : PathNodeId}
    (hab : LowR u c a b) (har : LowR u c a r) (hbr : LowR u c b r) (h : Sym (TF u) a b r) : TF u a b r := by
  have hsymm : ∀ {y w}, LowR u c y w → LowR u c w y :=
    fun hr => ⟨⟨hr.1.2.1, hr.1.1, (adj_symm u _ _).mp hr.1.2.2⟩, hr.2.2, hr.2.1⟩
  unfold Sym at h
  rcases h with h | h | h | h | h | h
  · exact h
  · exact trioGood_perm hTG hsymm hab har hbr (by simp [perms]) h
  · exact trioGood_perm hTG hsymm hab har hbr (by simp [perms]) h
  · exact trioGood_perm hTG hsymm hab har hbr (by simp [perms]) h
  · exact trioGood_perm hTG hsymm hab har hbr (by simp [perms]) h
  · exact trioGood_perm hTG hsymm hab har hbr (by simp [perms]) h

-- ============================================================
-- La familia de la cima es una estructura del lado, con testigos
-- ============================================================

/-- **`StarTriAt`**: en la unión fijada `u = pinOn J Rp`, un triángulo `(a, b, r)` entre vecinos de una cima `t` del
lado `S`, vivo en `u` y con sus tres caras con `t` vivas en `u`, no está en la lista de tríos de `pinOn S Rp`. -/
def StarTriAt (S J : GPathB) (Rp : List NodeId) : Prop :=
  (J.pinOn Rp).isValid = true → ∀ t ∈ (J.pinOn Rp).alive, t.id.step = J.current_step - 1 → t ∈ S.alive →
    ∀ a b r, a ≠ t → b ≠ t → r ≠ t → a ≠ b → a ≠ r → b ≠ r →
      (J.pinOn Rp).Adj t a → (J.pinOn Rp).Adj t b → (J.pinOn Rp).Adj t r →
      (J.pinOn Rp).Adj a b → (J.pinOn Rp).Adj a r → (J.pinOn Rp).Adj b r →
      ¬ Sym (TF (J.pinOn Rp)) a b t → ¬ Sym (TF (J.pinOn Rp)) a r t → ¬ Sym (TF (J.pinOn Rp)) b r t →
      ¬ Sym (TF (J.pinOn Rp)) a b r → ∀ τ ∈ (S.pinOn Rp).trios, trioIs a b r τ = false

/-- **Una cima viva de `pinOn J Rp` que es del lado `S` y no del otro está viva en `pinOn S Rp`**, bajo `StarTriAt`.
`O` es el otro lado; `hcut` dice que `J` prohíbe todo triángulo suyo que `S` corta y que `O` no tiene (para el join
`:on`, `tF_joinOn_of_cut`). -/
theorem star_alive {J S O : GPathB} {Rp : List NodeId} (hJ : SInvB J) (hnsJ : NoSelf J) (hndJ : NoDegT J)
    (hc2 : 2 ≤ J.current_step) (hv : (J.pinOn Rp).isValid = true) (hS : SInvB S) (hnsS : NoSelf S)
    (hndS : NoDegT S) (hcs : J.current_step = S.current_step) (hap : AdjPar S)
    (hadj : ∀ x w, J.Adj x w → S.Adj x w ∨ O.Adj x w) (heO : EdgesAlive O)
    (hcut : ∀ {x y z}, J.Adj x y → J.Adj x z → J.Adj y z → x ≠ y → x ≠ z → y ≠ z → SideForbids S (TF S) x y z →
      ¬ (O.Adj x y ∧ O.Adj x z ∧ O.Adj y z) → TF J x y z)
    {t : PathNodeId} (ht : t ∈ (J.pinOn Rp).alive) (hts : t.id.step = J.current_step - 1) (htS : t ∈ S.alive)
    (htO : t ∉ O.alive) (hstar : StarTriAt S J Rp) :
    (S.pinOn Rp).isValid = true ∧ t ∈ (S.pinOn Rp).alive := by
  let u := J.pinOn Rp
  let c := J.current_step
  have hcsu : u.current_step = c := step_pinOn J Rp
  have hiu : SInvB u := sInvB_pinOn hJ Rp
  have hbs : ∀ q ∈ u.alive, q.id.step < c := fun q hq => by
    have := alive_below hiu.docs hiu.below hq; rw [hcsu] at this; exact this
  have hcl : ClosedState u := closedState_pinOn hJ hv hc2
  have hfix : FixClosed u := fixClosed_reviewOn (g := { Rp.foldl filterRequire J with dirty := true }) rfl hv
  have hTGu : TrioGood (LowV u c) (LowR u c) (TF u) c :=
    trioGood_low hfix (noDegT_pinOn hnsJ hndJ Rp) (by rw [hcsu]; exact Int.le_refl _)
  have hsub : Sub u J := sub_pinOn J Rp
  have low : ∀ {y w}, u.Adj y w → LowR u c y w := fun {y w} h =>
    ⟨⟨(hiu.edges y w h).1, (hiu.edges y w h).2, h⟩, hbs y (hiu.edges y w h).1, hbs w (hiu.edges y w h).2⟩
  have usymm : ∀ {y w}, u.Adj y w → u.Adj w y := fun h => (adj_symm u _ _).mp h
  -- un trío sin prohibir en `u`, en su cierre simétrico
  have nsym : ∀ {a b r}, u.Adj a b → u.Adj a r → u.Adj b r → ¬ TF u a b r → ¬ Sym (TF u) a b r :=
    fun hab har hbr hn hs => hn (tF_of_sym hTGu (low hab) (low har) (low hbr) hs)
  -- una arista de `u` con un extremo fuera de `O` es de `S`
  have key : ∀ a b, u.Adj a b → a ∉ O.alive → S.Adj a b := fun a b h hn =>
    (hadj a b (hsub.adj _ _ h)).resolve_right (fun ho => hn (heO a b ho).1)
  -- la familia
  let V : PathNodeId → Prop := fun y => u.Adj t y
  let Rr : PathNodeId → PathNodeId → Prop := fun y w =>
    u.Adj t y ∧ u.Adj t w ∧ u.Adj y w ∧ (y = w ∨ y = t ∨ w = t ∨ ¬ Sym (TF u) y w t)
  let T : Trios := Sym (TF u)
  let K : Trios := fun a b r => a ≠ t ∧ b ≠ t ∧ r ≠ t ∧ ¬ Sym (TF u) a b r
  have htt : u.Adj t t := adj_refl u t ht
  have rsymm : ∀ {y w}, Rr y w → Rr w y := by
    intro y w ⟨h1, h2, h3, h4⟩
    refine ⟨h2, h1, usymm h3, ?_⟩
    rcases h4 with e | e | e | e
    · exact Or.inl e.symm
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inr (nsym_perm e (by simp [perms]))))
  -- los testigos de las aristas
  have hedge : ∀ {a b}, Rr a b → a ≠ b → ∀ l, 0 ≤ l → l < c →
      ∃ s, s.id.step = l ∧ Rr a s ∧ Rr b s ∧ (s = a ∨ s = b ∨ ¬ T a b s) := by
    intro a b ⟨hta, htb, hab, hc⟩ nab l h0 h1
    by_cases hat : a = t
    · subst hat
      obtain ⟨s, hsl, has, hbs', hw⟩ := hTGu.edge (low hab) nab l h0 h1
      refine ⟨s, hsl, ⟨htt, has.1.2.2, has.1.2.2, Or.inr (Or.inl rfl)⟩, ⟨htb, has.1.2.2, hbs'.1.2.2, ?_⟩, ?_⟩
      · rcases hw with e | e | e
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inl e.symm
        · exact Or.inr (Or.inr (Or.inr (nsym_perm (nsym hab has.1.2.2 hbs'.1.2.2 e) (by simp [perms]))))
      · rcases hw with e | e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (nsym hab has.1.2.2 hbs'.1.2.2 e))
    · by_cases hbt : b = t
      · subst hbt
        obtain ⟨s, hsl, has, hbs', hw⟩ := hTGu.edge (low hab) nab l h0 h1
        refine ⟨s, hsl, ⟨hta, hbs'.1.2.2, has.1.2.2, ?_⟩, ⟨htt, hbs'.1.2.2, hbs'.1.2.2, Or.inr (Or.inl rfl)⟩, ?_⟩
        · rcases hw with e | e | e
          · exact Or.inl e.symm
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inr (Or.inr (nsym_perm (nsym hab has.1.2.2 hbs'.1.2.2 e) (by simp [perms]))))
        · rcases hw with e | e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (nsym hab has.1.2.2 hbs'.1.2.2 e))
      · -- arista entre vecinos: los testigos del triángulo con la cima
        have habt : ¬ Sym (TF u) a b t := by
          rcases hc with e | e | e | e
          · exact absurd e nab
          · exact absurd e hat
          · exact absurd e hbt
          · exact e
        have hat' := usymm hta
        have hbt' := usymm htb
        have hnT : ¬ TF u a b t := fun h => habt (Or.inl h)
        obtain ⟨s, hsl, has, hbs', hts', hw⟩ := hTGu.trio (low hab) (low hat') (low hbt') nab hat hbt hnT l h0 h1
        have hst : u.Adj t s := hts'.1.2.2
        refine ⟨s, hsl, ⟨hta, hst, has.1.2.2, ?_⟩, ⟨htb, hst, hbs'.1.2.2, ?_⟩, ?_⟩
        · rcases hw with e | e | e | ⟨_, e, _⟩
          · exact Or.inl e.symm
          · rw [e]; exact Or.inr (Or.inr (Or.inr habt))
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inr (Or.inr (nsym_perm (nsym hat' has.1.2.2 hst e) (by simp [perms]))))
        · rcases hw with e | e | e | ⟨_, _, e⟩
          · rw [e]; exact Or.inr (Or.inr (Or.inr (nsym_perm habt (by simp [perms]))))
          · exact Or.inl e.symm
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inr (Or.inr (nsym_perm (nsym hbt' hbs'.1.2.2 hst e) (by simp [perms]))))
        · rcases hw with e | e | e | ⟨e, _, _⟩
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · rw [e]; exact Or.inr (Or.inr habt)
          · exact Or.inr (Or.inr (nsym hab has.1.2.2 hbs'.1.2.2 e))
  -- todo nodo de la familia tiene un vecino de la familia en cada paso
  have hstep : ∀ {y}, V y → ∀ l, 0 ≤ l → l < c → ∃ r, r.id.step = l ∧ Rr y r := by
    intro y hy l h0 h1
    by_cases hyt : y = t
    · subst hyt
      obtain ⟨r, hrl, hyr, _⟩ := hcl.pair (hcl.refl ht) l h0 (by rw [hcsu]; exact h1)
      exact ⟨r, hrl, htt, hyr.2.2, hyr.2.2, Or.inr (Or.inl rfl)⟩
    · obtain ⟨s, hsl, _, hys, _⟩ := hedge (a := t) (b := y) ⟨htt, hy, hy, Or.inr (Or.inl rfl)⟩
        (fun e => hyt e.symm) l h0 h1
      exact ⟨s, hsl, hys⟩
  have hValive : ∀ {y}, V y → y ∈ S.alive := fun {y} hy => (hS.edges t y (key t y hy htO)).2
  have hRadj : ∀ {y w}, Rr y w → S.Adj y w := by
    intro y w ⟨h1, h2, h3, h4⟩
    by_cases hyw : y = w
    · subst hyw; exact adj_refl S y (hValive h1)
    by_cases hyt : y = t
    · rw [hyt]; exact key t w h2 htO
    by_cases hwt : w = t
    · rw [hwt]; exact (adj_symm S _ _).mp (key t y h1 htO)
    have hn : ¬ Sym (TF u) y w t := by
      rcases h4 with e | e | e | e
      · exact absurd e hyw
      · exact absurd e hyt
      · exact absurd e hwt
      · exact e
    apply Classical.byContradiction
    intro hno
    have hJf : TF J y w t := hcut (hsub.adj _ _ h3) (hsub.adj _ _ (usymm h1)) (hsub.adj _ _ (usymm h2)) hyw hyt hwt
      (Or.inl fun h => hno h.1) (fun h => htO (heO y t h.2.1).2)
    exact hn (Or.inl (tF_mono (trios_grow_pinOn J Rp) h3 hJf))
  -- los enlaces: un vecino del paso anterior es padre, y uno del paso siguiente es hijo
  have hpar : ∀ {x p : PathNodeId} {n : PNodeB}, S.node? x = some n → Rr x p → p.id.step + 1 = x.id.step →
      p ∈ n.parents := by
    intro x p n hn hR hst
    have hA := hRadj hR
    exact (hS.links.2.1 n (node?_mem hn) p (hValive hR.2.1) (by rw [node?_id hn]; exact hA)).1
      (by rw [node?_id hn]; exact hap x p hA hst)
  have hson : ∀ {x q : PathNodeId} {n : PNodeB}, S.node? x = some n → Rr x q → x.id.step + 1 = q.id.step →
      q ∈ n.sons := by
    intro x q n hn hR hst
    have hA := hRadj hR
    exact (hS.links.2.1 n (node?_mem hn) q (hValive hR.2.1) (by rw [node?_id hn]; exact hA)).2
      (by rw [node?_id hn]; exact hap q x ((adj_symm S _ _).mp hA) hst)
  have hstep0 : ∀ {y}, V y → 0 ≤ y.id.step := by
    intro y hy
    obtain ⟨n, hn, hnid⟩ := hS.docs y (hValive hy)
    have := hS.zero n hn
    rw [hnid] at this; exact this
  have hsec : SecStruct S V Rr := by
    refine ⟨fun hy => hValive hy, fun hy => ⟨hy, hy, adj_refl u _ (hiu.edges _ _ hy).2, Or.inl rfl⟩, rsymm,
      fun hr => ⟨hr.1, hr.2.1⟩, hRadj, ?_, ?_, ?_, ?_⟩
    · intro y w hR l h0 h1
      rw [← hcs] at h1
      by_cases hyw : y = w
      · subst hyw
        obtain ⟨r, hrl, hyr⟩ := hstep hR.1 l h0 h1
        exact ⟨r, hrl, hyr, hyr⟩
      · obtain ⟨s, hsl, h1', h2', _⟩ := hedge hR hyw l h0 h1
        exact ⟨s, hsl, h1', h2'⟩
    · intro y hy
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hS.docs (hValive hy))
      refine ⟨n, hn, fun hp => ?_, fun hs => ?_⟩
      · have h0 := hstep0 hy
        have hne : y.id.step ≠ 0 := by
          intro e
          rw [hS.root y (hValive hy) e] at hp
          simp at hp
        obtain ⟨r, hrl, hyr⟩ := hstep hy (y.id.step - 1) (by omega)
          (by have := hbs y (hiu.edges _ _ hy).2; omega)
        exact ⟨r, hpar hn hyr (by omega), hyr⟩
      · rw [← hcs] at hs
        have hlt := hbs y (hiu.edges _ _ hy).2
        obtain ⟨r, hrl, hyr⟩ := hstep hy (y.id.step + 1) (by have := hstep0 hy; omega) (by omega)
        exact ⟨r, hson hn hyr (by omega), hyr⟩
    · intro x w n hR hne hn hst
      obtain ⟨s, hsl, hxs, hws, _⟩ := hedge hR hne (x.id.step - 1) (by omega)
        (by have := hbs x (hiu.edges _ _ hR.1).2; omega)
      exact ⟨s, hpar hn hxs (by omega), hxs, rsymm hws⟩
    · intro x w n hR hne hn hst
      rw [← hcs] at hst
      obtain ⟨s, hsl, hxs, hws, _⟩ := hedge hR hne (x.id.step + 1) (by have := hstep0 hR.1; omega) (by omega)
      exact ⟨s, hson hn hxs (by omega), hxs, rsymm hws⟩
  -- los triángulos de la familia sin la cima, vivos en `u`, no están en los tríos del lado fijado
  have hndP : NoDegT (S.pinOn Rp) := noDegT_pinOn hnsS hndS Rp
  have hK : KeptOut Rr K (S.pinOn Rp).trios := by
    intro a b r hab har hbr ⟨nat, nbt, nrt, hnT⟩ τ hτ
    cases hti : trioIs a b r τ
    · rfl
    · exfalso
      obtain ⟨nab, nar, nbr⟩ := distinct_of_trioIs hti (hndP τ hτ)
      have f : ∀ {y w}, Rr y w → y ≠ w → y ≠ t → w ≠ t → ¬ Sym (TF u) y w t := by
        intro y w hR h1 h2 h3
        rcases hR.2.2.2 with e | e | e | e
        · exact absurd e h1
        · exact absurd e h2
        · exact absurd e h3
        · exact e
      have := hstar hv t ht hts htS a b r nat nbt nrt nab nar nbr hab.1 hab.2.1 har.2.1 hab.2.2.1 har.2.2.1
        hbr.2.2.1 (f hab nab nat nbt) (f har nar nat nrt) (f hbr nbr nbt nrt) hnT τ hτ
      rw [hti] at this; cases this
  -- el invariante en el lado sin fijar
  have h0 : DownInv V Rr T c S := by
    refine ⟨hsec, hnsS, hcs.symm, ?_⟩
    intro a b r hab har hbr hf
    apply Classical.byContradiction
    intro hnT
    obtain ⟨nab, hd⟩ := hf
    have hd' := hd
    unfold deadTrio at hd'
    rw [Bool.and_eq_true] at hd'
    obtain ⟨τ, hτ, hti⟩ := List.any_eq_true.mp hd'.2
    obtain ⟨_, nar, nbr⟩ := distinct_of_trioIs hti (hndS τ hτ)
    by_cases hno : a ≠ t ∧ b ≠ t ∧ r ≠ t
    · -- sin la cima: la hipótesis
      have := hK a b r hab har hbr ⟨hno.1, hno.2.1, hno.2.2, hnT⟩ τ (trios_grow_pinOn S Rp τ hτ)
      rw [hti] at this; cases this
    · -- con la cima: el otro lado no tiene el triángulo, y el join lo habría prohibido
      have hO : ¬ (O.Adj a b ∧ O.Adj a r ∧ O.Adj b r) := by
        intro ⟨h1, h2, h3⟩
        apply htO
        by_cases e1 : a = t
        · rw [← e1]; exact (heO a b h1).1
        by_cases e2 : b = t
        · rw [← e2]; exact (heO a b h1).2
        by_cases e3 : r = t
        · rw [← e3]; exact (heO a r h2).2
        exact absurd ⟨e1, e2, e3⟩ hno
      have hJf : TF J a b r := hcut (hsub.adj _ _ hab.2.2.1) (hsub.adj _ _ har.2.2.1) (hsub.adj _ _ hbr.2.2.1)
        nab nar nbr (Or.inr ⟨nab, hd⟩) hO
      exact hnT (Or.inl (tF_mono (trios_grow_pinOn J Rp) hab.2.2.1 hJf))
  -- los testigos de los triángulos con la cima
  have hTGK : TrioGoodK V Rr T K c := by
    refine ⟨hedge, ?_, fun _ _ _ h => sym_perm h (by simp [perms]), fun _ _ _ h => sym_perm h (by simp [perms])⟩
    intro a b r hab har hbr nab nar nbr hnT
    by_cases hno : a ≠ t ∧ b ≠ t ∧ r ≠ t
    · exact Or.inl ⟨hno.1, hno.2.1, hno.2.2, hnT⟩
    · right
      intro l h0' h1'
      have htin : t = a ∨ t = b ∨ t = r := by
        by_cases e1 : a = t
        · exact Or.inl e1.symm
        by_cases e2 : b = t
        · exact Or.inr (Or.inl e2.symm)
        by_cases e3 : r = t
        · exact Or.inr (Or.inr e3.symm)
        exact absurd ⟨e1, e2, e3⟩ hno
      have hnT' : ¬ TF u a b r := fun h => hnT (Or.inl h)
      obtain ⟨s, hsl, has, hbs', hrs, hw⟩ := hTGu.trio (low hab.2.2.1) (low har.2.2.1) (low hbr.2.2.1) nab nar nbr
        hnT' l h0' h1'
      have hst : u.Adj t s := by
        rcases htin with e | e | e
        · rw [e]; exact has.1.2.2
        · rw [e]; exact hbs'.1.2.2
        · rw [e]; exact hrs.1.2.2
      -- la condición de la familia para cada nodo del triángulo con el testigo
      have cond : ∀ x, (x = a ∨ x = b ∨ x = r) → (x = s ∨ x = t ∨ s = t ∨ ¬ Sym (TF u) x s t) := by
        intro x hx
        by_cases hxs : x = s
        · exact Or.inl hxs
        by_cases hxt : x = t
        · exact Or.inr (Or.inl hxt)
        by_cases hst' : s = t
        · exact Or.inr (Or.inr (Or.inl hst'))
        refine Or.inr (Or.inr (Or.inr ?_))
        rcases hw with e | e | e | ⟨w1, w2, w3⟩
        · -- el testigo es `a`: {x, s, t} es el triángulo
          subst e
          rcases hx with e1 | e1 | e1 <;> rcases htin with e2 | e2 | e2 <;>
            first
            | exact absurd e1 hxs
            | exact absurd e2.symm hst'
            | exact absurd (e1.trans e2.symm) hxt
            | (subst e1; subst e2; refine nsym_perm hnT ?_; simp [perms]; done)
        · subst e
          rcases hx with e1 | e1 | e1 <;> rcases htin with e2 | e2 | e2 <;>
            first
            | exact absurd e1 hxs
            | exact absurd e2.symm hst'
            | exact absurd (e1.trans e2.symm) hxt
            | (subst e1; subst e2; refine nsym_perm hnT ?_; simp [perms]; done)
        · subst e
          rcases hx with e1 | e1 | e1 <;> rcases htin with e2 | e2 | e2 <;>
            first
            | exact absurd e1 hxs
            | exact absurd e2.symm hst'
            | exact absurd (e1.trans e2.symm) hxt
            | (subst e1; subst e2; refine nsym_perm hnT ?_; simp [perms]; done)
        · have n1 := nsym hab.2.2.1 has.1.2.2 hbs'.1.2.2 w1
          have n2 := nsym har.2.2.1 has.1.2.2 hrs.1.2.2 w2
          have n3 := nsym hbr.2.2.1 hbs'.1.2.2 hrs.1.2.2 w3
          rcases hx with e1 | e1 | e1 <;> rcases htin with e2 | e2 | e2 <;>
            first
            | exact absurd (e1.trans e2.symm) hxt
            | (subst e1; subst e2; refine nsym_perm n1 ?_; simp [perms]; done)
            | (subst e1; subst e2; refine nsym_perm n2 ?_; simp [perms]; done)
            | (subst e1; subst e2; refine nsym_perm n3 ?_; simp [perms]; done)
      refine ⟨s, hsl, ⟨hab.1, hst, has.1.2.2, cond a (Or.inl rfl)⟩, ⟨hab.2.1, hst, hbs'.1.2.2, cond b (Or.inr (Or.inl rfl))⟩,
        ⟨har.2.1, hst, hrs.1.2.2, cond r (Or.inr (Or.inr rfl))⟩, ?_⟩
      rcases hw with e | e | e | ⟨w1, w2, w3⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr ⟨nsym hab.2.2.1 has.1.2.2 hbs'.1.2.2 w1, nsym har.2.2.1 has.1.2.2 hrs.1.2.2 w2,
          nsym hbr.2.2.1 hbs'.1.2.2 hrs.1.2.2 w3⟩))
  have hagree : ∀ p ∈ Rp, SecAgrees V p := fun p hp q hq hqs =>
    pinned_pinOn hJ.docs hv p hp q (hiu.edges _ _ hq).2 hqs
  have hX := downInv_pinOnK hTGK rsymm h0 hagree hK
  exact ⟨isValid_of_sec hX.sec (y := t) htt, hX.sec.alive htt⟩

-- ============================================================
-- `TopSideAt` desde `StarTriAt`
-- ============================================================

/-- **`TopSideAt` bajo `StarTriAt` en los dos lados.** `bA`, `bB`: los colores de los padres de las cimas de cada lado,
distintos (las cimas de un lado no están vivas en el otro). -/
theorem topSideAt_of_starTri {A B : GPathB} {Rp : List NodeId} {bA bB : NodeId} (hA : SInvB A) (hB : SInvB B)
    (hnsA : NoSelf A) (hnsB : NoSelf B) (hndA : NoDegT A) (hndB : NoDegT B)
    (hcs : A.current_step = B.current_step) (hc2 : 2 ≤ A.current_step) (hne : bA ≠ bB)
    (hfA : TopsFrom A (fun a => a = bA)) (hfB : TopsFrom B (fun a => a = bB)) (hapA : AdjPar A) (hapB : AdjPar B)
    (hsA : StarTriAt A (joinOn A B) Rp) (hsB : StarTriAt B (joinOn A B) Rp) : TopSideAt A B Rp := by
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
  have hsep : t ∈ A.alive → t ∈ B.alive → False := fun h1 h2 => by
    have e := parA t h1 hts
    rw [parB t h2 hts] at e
    exact hne (Option.some.inj e).symm
  rcases halive t ((sub_pinOn _ Rp).alive t ht) with htA | htB
  · exact Or.inl (star_alive (S := A) (O := B) hJ hnsJ hndJ (by rw [hcsJ]; exact hc2) hv hA hnsA hndA hcsJ hapA hadj
      hB.edges
      (fun hxy hxz hyz nxy nxz nyz s1 hO => tF_joinOn_of_cut hA.edges hB.edges hxy hxz hyz nxy nxz nyz s1 (Or.inl hO))
      ht (by rw [hcsJ]; exact hts) htA (fun h => hsep htA h) hsA)
  · exact Or.inr (star_alive (S := B) (O := A) hJ hnsJ hndJ (by rw [hcsJ]; exact hc2) hv hB hnsB hndB (hcsJ.trans hcs)
      hapB (fun x w h => (hadj x w h).symm) hA.edges
      (fun hxy hxz hyz nxy nxz nyz s2 hO => tF_joinOn_of_cut hA.edges hB.edges hxy hxz hyz nxy nxz nyz (Or.inl hO) s2)
      ht (by rw [hcsJ]; exact hts) htB (fun h => hsep h htB) hsB)

-- ============================================================
-- En la máquina
-- ============================================================

theorem trioBlind_topsApart : TrioBlind TopsApart := fun _ _ h => h

theorem topsApart_setT {g : GPathB} (h : TopsApart g) (T : List (PathNodeId × PathNodeId × PathNodeId)) :
    TopsApart (g.setT T) := fun y w h1 h2 h3 => h y w h1 h2 h3

/-- La llegada `:on` conserva `AdjPar` y `TopsApart`. -/
theorem arrOn_adjPar {φ : Cnf} {T : Int} {kv : NodeId × GPathB} (hent : EntOn T kv.1 kv.2)
    (hi : SInvB kv.2) (hap : AdjPar kv.2) (hta : TopsApart kv.2) {d : NodeId} (hs : SendsOn φ kv d) :
    AdjPar (arrOn φ kv d) ∧ TopsApart (arrOn φ kv d) := by
  have hok := hent.1
  let Y := kv.2.filterAllOn (reqOf φ d)
  have hd : d.step = Y.current_step := by
    rw [step_filterAllOn, sonsOfMap_step φ kv.1 d hs.1, hok.key, hok.step]; omega
  have hvY : Y.isValid = true := valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
  have hiY : SInvB Y := sInvB_filterAllOn hi _
  have hapY : AdjPar Y := adjPar_of_sub (shrinks_filterAllOn kv.2 (reqOf φ d)).1 hap
  have htaY : TopsApart Y := by
    show TopsApart (kv.2.filterAllOn (reqOf φ d))
    unfold filterAllOn
    exact revPrims_reviewOn revPrims_topsApart trioBlind_topsApart _
      (foldl_filterRequire_pres revPrims_topsApart _ _ hta)
  obtain ⟨T', hT'⟩ := upOn_eq (g := Y) (d := d) (title := "") (forb := isProhibited φ) hvY
  have e : arrOn φ kv d = ((Y.addNode d "" (isProhibited φ)).setT T').reviewOn := hT'
  rw [e]
  constructor
  · exact adjPar_of_sub (shrinks_reviewOn _).1 (adjPar_setT (adjPar_addNode htaY hd hapY) T')
  · apply revPrims_reviewOn revPrims_topsApart trioBlind_topsApart
    exact topsApart_addNode (title := "") (forb := isProhibited φ) hiY.docs hiY.below hiY.edges

/-- **`StarTriAt` en los joins de la máquina**, de cada llegada en la unión, para los pins de `PinsFrom`. -/
def HStarOn (φ : Cnf) (line : Line) : Prop :=
  ∀ a ∈ line, ∀ b ∈ line, a.1 ≠ b.1 → ∀ d, SendsOn φ a d → SendsOn φ b d → ∀ R, PinsFrom φ d R →
    StarTriAt (arrOn φ a d) (joinOn (arrOn φ a d) (arrOn φ b d)) R ∧
    StarTriAt (arrOn φ b d) (joinOn (arrOn φ a d) (arrOn φ b d)) R

/-- La contabilidad extra de la línea: ids de las cimas, vecinos consecutivos, cimas no vecinas. -/
def LineBk (line : Line) : Prop := ∀ kv ∈ line, TopDocsId kv.2 kv.1 ∧ AdjPar kv.2 ∧ TopsApart kv.2

/-- **`StarTriAt` da `TopSideAt` en los joins de la línea.** -/
theorem hTopOn_of_star {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (hbk : LineBk line) (hp : HStarOn φ line) : HTopOn φ line := by
  intro a ha b hb hab d hsa hsb R hR
  obtain ⟨ea, ia, na, _, _⟩ := arrTop_facts hT h ha hsa
  obtain ⟨eb, ib, nb, _, _⟩ := arrTop_facts hT h hb hsb
  obtain ⟨fa, _⟩ := arrOn_tops hT (h.on a ha) (hbk a ha).1 hsa
  obtain ⟨fb, _⟩ := arrOn_tops hT (h.on b hb) (hbk b hb).1 hsb
  obtain ⟨pa, _⟩ := arrOn_adjPar (h.on a ha) (h.inv a ha) (hbk a ha).2.1 (hbk a ha).2.2 hsa
  obtain ⟨pb, _⟩ := arrOn_adjPar (h.on b hb) (h.inv b hb) (hbk b hb).2.1 (hbk b hb).2.2 hsb
  obtain ⟨hsA, hsB⟩ := hp a ha b hb hab d hsa hsb R hR
  exact topSideAt_of_starTri ia ib ea.2.1 eb.2.1 na nb (ea.1.step.trans eb.1.step.symm) (by rw [ea.1.step]; omega)
    hab fa fb pa pb hsA hsB

theorem lineBk_advance {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (hbk : LineBk line) : LineBk (advanceM .on φ line) := by
  intro E hE
  refine ⟨tid_advance hT h (fun kv hkv => (hbk kv hkv).1) E hE, ?_⟩
  rcases entry_shapeOn (line_cases h.nodup h.keys) h.nodup hE with ⟨kv, hkv, hs, he⟩ |
    ⟨a, ha, b, hb, _, hsa, hsb, he⟩
  · rw [he]; exact arrOn_adjPar (h.on kv hkv) (h.inv kv hkv) (hbk kv hkv).2.1 (hbk kv hkv).2.2 hs
  · obtain ⟨ea, _⟩ := arrTop_facts hT h ha hsa
    obtain ⟨eb, _⟩ := arrTop_facts hT h hb hsb
    have hjoin : doJoinOn (arrOn φ a E.1) (arrOn φ b E.1) = joinOn (arrOn φ a E.1) (arrOn φ b E.1) := by
      unfold doJoinOn okJoin
      rw [if_pos (by simp [ea.1.step, eb.1.step, ea.1.mp, eb.1.mp, ea.1.valid, eb.1.valid])]
    obtain ⟨pa, ta⟩ := arrOn_adjPar (h.on a ha) (h.inv a ha) (hbk a ha).2.1 (hbk a ha).2.2 hsa
    obtain ⟨pb, tb⟩ := arrOn_adjPar (h.on b hb) (h.inv b hb) (hbk b hb).2.1 (hbk b hb).2.2 hsb
    obtain ⟨T', hT'⟩ := joinOn_eq (arrOn φ a E.1) (arrOn φ b E.1)
    rw [he, hjoin, hT']
    exact ⟨adjPar_setT (adjPar_join pa pb) T',
      topsApart_setT (topsApart_join ta tb (ea.1.step.trans eb.1.step.symm)) T'⟩

theorem empty_noAdj {x s : PathNodeId} (h : GPathB.empty.Adj x s) : False := by
  unfold Adj adjb isAlive hasEdge at h
  simp [GPathB.empty] at h

/-- **La hipótesis de tríos**, en cada línea de la máquina `:on`. -/
def HypsStarOn (φ : Cnf) : Prop := ∀ n : Nat, HStarOn φ (stepsM .on φ n (initM .on φ))

theorem lInvStar_steps {φ : Cnf} (H : HypsStarOn φ) :
    ∀ n : Nat, LInvTop φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) ∧ LineBk (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨lInvTop_init φ, ?_⟩
    show LineBk (initM .on φ)
    rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    obtain ⟨T', hT'⟩ := upOn_eq (g := GPathB.empty) (d := (⟨0, 0⟩ : NodeId)) (title := "")
      (forb := fun _ => false) (by rfl)
    have e : initSeedOn (⟨0, 0⟩ : NodeId) "" = ((GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)).setT T').reviewOn :=
      hT'
    show TopDocsId (initSeedOn (⟨0, 0⟩ : NodeId) "") ⟨0, 0⟩ ∧ AdjPar (initSeedOn (⟨0, 0⟩ : NodeId) "") ∧
      TopsApart (initSeedOn (⟨0, 0⟩ : NodeId) "")
    rw [e]
    have hta0 : TopsApart GPathB.empty := fun y w _ _ h => (empty_noAdj h).elim
    have hap0 : AdjPar GPathB.empty := fun x s h _ => (empty_noAdj h).elim
    refine ⟨topDocsId_of_shrinks (shrinks_reviewOn _)
      (topDocsId_addNode (g := GPathB.empty) (title := "") (forb := fun _ => false)
        (fun n hn => absurd hn List.not_mem_nil)),
      adjPar_of_sub (shrinks_reviewOn _).1 (adjPar_setT (adjPar_addNode hta0 (by rfl) hap0) T'), ?_⟩
    apply revPrims_reviewOn revPrims_topsApart trioBlind_topsApart
    exact topsApart_addNode (g := GPathB.empty) (title := "") (forb := fun _ => false) sInvB_empty.docs
      sInvB_empty.below sInvB_empty.edges
  | succ n ih =>
    obtain ⟨hl, hbk⟩ := ih
    have hT : (1 : Int) ≤ (n : Int) + 1 := by omega
    rw [stepsM_succ]
    have := lInvTop_advance hT hl (hTopOn_of_star hT hl hbk (H n))
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact ⟨this, lineBk_advance hT hl hbk⟩

theorem hypsTopOn_of_star {φ : Cnf} (H : HypsStarOn φ) : HypsTopOn φ := fun n =>
  hTopOn_of_star (by omega) (lInvStar_steps H n).1 (lInvStar_steps H n).2 (H n)

end GPathB

namespace MachineOn

open GPathB Driver

/-- **La espina con la regla activa decide la satisfacibilidad bajo `StarTriAt` en los joins de la máquina**: en la
unión fijada, un triángulo entre vecinos de una cima, vivo y con sus tres caras con la cima vivas, no está en los tríos
del lado fijado de esa cima. Una hipótesis de tríos; la supervivencia de la cima, de sus vecinos y de sus aristas en el
lado está demostrada («el primero que muere»). -/
theorem spineVerdictOn_iff_of_starTri {φ : Cnf} (hbd : Bounded φ) (H : HypsStarOn φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_topOn hbd (hypsTopOn_of_star H)

end MachineOn

end AbsSatBingo.Model
