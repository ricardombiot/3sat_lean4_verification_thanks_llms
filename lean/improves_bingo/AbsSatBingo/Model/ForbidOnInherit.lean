-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnInherit.lean
import AbsSatBingo.Model.ForbidOnStar

/-!
# La herencia de `PrevCut`

`PrevCut` habla de una **base muerta bajo una cima**: en una llegada, una cima viva con tres vecinos, vecinos entre
sí, con las tres caras con la cima sin prohibir y la base prohibida (`DeadBase`). Aquí se cierra por inducción el caso
en que esa situación **se hereda** de la entrada que envía la llegada:

* **`up_forbid` es completo** (`upOn_face_parent`, `arrOn_face_parent`): una cara `(t, x, y)` de una cima nueva que no
  está prohibida en la llegada tiene un padre de `t` que no cortaba `(p, x, y)` en el remitente. Es el contrapositivo
  de la regla del UP, más que el review solo añade tríos.
* **La base muerta de una unión es la de una llegada** (`deadBase_joinOn`): la cima es de un solo lado, sus caras
  viven en él (el join habría prohibido el triángulo con la cima), y el join guardó la base porque ese lado la cortaba.
* **Herencia** (`prevCut_inherit`): si la entrada `a` ya tenía la base muerta bajo una cima suya y los nodos de la base
  existían una línea más atrás, `PrevCut` del nivel anterior y `lineCut_advance` dan el corte en toda la línea.

Queda **`HPrevNew`**: `PrevCut` solo para las bases que no se heredan así (`hPrevCut_succ`, `hypsPrev4On_of_new`,
`spineVerdictOn_iff_of_new4`). Por `arrOn_face_parent`, en esos casos cada cara de la cima tiene un padre que la
sostiene (`deadBase_arr_parents`), y lo que falla es que la base no estaba prohibida en `a`, que ningún padre sostiene
las tres caras, o que la base tiene un nodo en la cima de la línea anterior.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Driver Machine MachineOn

-- ============================================================
-- Parejas, cortes en Bool y tríos en cualquier orden
-- ============================================================

/-- `pairsOf` tiene toda pareja de nodos distintos de la lista, en algún orden. -/
theorem pairsOf_mem : ∀ {l : List PathNodeId} {a b : PathNodeId}, a ∈ l → b ∈ l → a ≠ b →
    (a, b) ∈ pairsOf l ∨ (b, a) ∈ pairsOf l
  | [], _, _, h, _, _ => absurd h List.not_mem_nil
  | w :: ws, a, b, ha, hb, hne => by
    simp only [pairsOf, List.mem_append, List.mem_map]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact Or.inl (Or.inl ⟨b, hb', rfl⟩)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (Or.inl ⟨a, ha', rfl⟩)
      · rcases pairsOf_mem ha' hb' hne with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

/-- Lo que dice que un lado **no** corte `(p, w, r)`: tiene las tres posesiones y, si los tres nodos son distintos, el
trío no está escrito. -/
theorem of_sideForbidsB_false {g : GPathB} {p w r : PathNodeId} (h : g.sideForbidsB p w r = false) :
    g.Adj p w ∧ g.Adj p r ∧ g.Adj w r ∧ (p ≠ w → p ≠ r → w ≠ r → ∀ τ ∈ g.trios, trioIs p w r τ = false) := by
  unfold sideForbidsB at h
  by_cases ht : (g.adjb p w && g.adjb p r && g.adjb w r) = true
  · rw [if_neg (by simp [ht])] at h
    simp only [Bool.and_eq_true] at ht
    refine ⟨ht.1.1, ht.1.2, ht.2, fun h1 h2 h3 => ?_⟩
    rw [if_neg (by simp [beq_iff_eq, h1, Ne.symm h2, Ne.symm h3])] at h
    have he : g.hasEdge p w = true := hasEdge_of_adj ht.1.1 h1
    unfold deadTrio at h
    rw [he, Bool.true_and] at h
    intro τ hτ
    cases hc : trioIs p w r τ
    · rfl
    · exact absurd hc (List.any_eq_false.mp h τ hτ)
  · rw [if_pos (by revert ht; cases g.adjb p w <;> cases g.adjb p r <;> cases g.adjb w r <;> simp)] at h
    cases h

/-- Un trío escrito, leído en el orden de una arista que existe, está prohibido. -/
theorem tF_of_trioIs {g : GPathB} {a b r : PathNodeId} {σ : PathNodeId × PathNodeId × PathNodeId}
    (hab : g.Adj a b) (nab : a ≠ b) (hσ : σ ∈ g.trios) (hti : trioIs a b r σ = true) : TF g a b r :=
  ⟨nab, by unfold deadTrio; rw [Bool.and_eq_true]
           exact ⟨hasEdge_of_adj hab nab, List.any_eq_true.mpr ⟨σ, hσ, hti⟩⟩⟩

/-- El cierre simétrico sobre una arista que existe es el trío mismo. -/
theorem tF_of_sym_adj {g : GPathB} {a b r : PathNodeId} (hab : g.Adj a b) (nab : a ≠ b) (h : Sym (TF g) a b r) :
    TF g a b r := by
  have get : ∀ {p q w}, TF g p q w → ∃ σ ∈ g.trios, trioIs p q w σ = true := by
    intro p q w hf
    have hd := hf.2
    unfold deadTrio at hd
    rw [Bool.and_eq_true] at hd
    exact List.any_eq_true.mp hd.2
  unfold Sym at h
  rcases h with h | h | h | h | h | h
  · exact h
  · obtain ⟨σ, hσ, hti⟩ := get h
    exact tF_of_trioIs hab nab hσ (trioIs_swap23 hti)
  · obtain ⟨σ, hσ, hti⟩ := get h
    exact tF_of_trioIs hab nab hσ (trioIs_swap12 hti)
  · obtain ⟨σ, hσ, hti⟩ := get h
    exact tF_of_trioIs hab nab hσ (trioIs_swap12 (trioIs_swap23 hti))
  · obtain ⟨σ, hσ, hti⟩ := get h
    exact tF_of_trioIs hab nab hσ (trioIs_swap23 (trioIs_swap12 hti))
  · obtain ⟨σ, hσ, hti⟩ := get h
    exact tF_of_trioIs hab nab hσ (trioIs_swap23 (trioIs_swap12 (trioIs_swap23 hti)))

-- ============================================================
-- `up_forbid` es completo
-- ============================================================

/-- **`up_forbid!` escribe todo lo que debe**: si `(t, x, y)`, con `t` de la fila y `x`, `y` vecinos suyos y entre sí,
no queda escrito, algún padre de `t` no corta `(p, x, y)`, en algún orden de `x`, `y`. -/
theorem upForbidRow_face {a' : GPathB} {ids : List PathNodeId} {t x y : PathNodeId} (ht : t ∈ ids)
    (hxa : x ∈ a'.alive) (hya : y ∈ a'.alive) (htx : a'.Adj t x) (hty : a'.Adj t y) (hxy : a'.Adj x y)
    (nxt : x ≠ t) (nyt : y ≠ t) (nxy : x ≠ y)
    (hn : (a'.upForbidRow ids).trios.any (trioIs t x y) = false) :
    ∃ p ∈ a'.parentsOf t, a'.sideForbidsB p x y = false ∨ a'.sideForbidsB p y x = false := by
  have hxn : x ∈ (Idx.of a').nbrs t := (idx_mem_nbrs a' t x).mpr ⟨nxt, hxa, hasEdge_of_adj htx (Ne.symm nxt)⟩
  have hyn : y ∈ (Idx.of a').nbrs t := (idx_mem_nbrs a' t y).mpr ⟨nyt, hya, hasEdge_of_adj hty (Ne.symm nyt)⟩
  -- una pareja `(w, r)` de la lista que todos los padres cortan queda escrita
  have written : ∀ {w r : PathNodeId}, (w, r) ∈ pairsOf ((Idx.of a').nbrs t) → a'.Adj w r → w ≠ r →
      (a'.parentsOf t).all (fun p => a'.sideForbidsB p w r) = true →
      (a'.upForbidRow ids).trios.any (trioIs t w r) = true := by
    intro w r hp hwr nwr hall
    have hmem : (t, w, r) ∈ ids.flatMap (fun n => upForbidTodo (Idx.of a') n (a'.parentsOf n)) := by
      refine List.mem_flatMap.mpr ⟨t, ht, ?_⟩
      unfold upForbidTodo
      refine List.mem_map.mpr ⟨(w, r), List.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
      simp only [Bool.and_eq_true, idx_hasEdge]
      refine ⟨hasEdge_of_adj hwr nwr, ?_⟩
      rw [List.all_eq_true] at hall ⊢
      intro p hp'
      rw [idx_sideForbids]
      exact hall p hp'
    rcases addTrios_covers a' (Idx.of a') _ (t, w, r) hmem with h | h
    · exact h
    · rw [idx_deadTrio] at h
      unfold deadTrio at h
      rw [Bool.and_eq_true] at h
      obtain ⟨σ, hσ, hti⟩ := List.any_eq_true.mp h.2
      refine List.any_eq_true.mpr ⟨σ, ?_, hti⟩
      unfold upForbidRow addTrios
      exact List.mem_append_left _ hσ
  have pick : ∀ {w r : PathNodeId}, (a'.parentsOf t).all (fun p => a'.sideForbidsB p w r) ≠ true →
      ∃ p ∈ a'.parentsOf t, a'.sideForbidsB p w r = false := by
    intro w r hall
    apply Classical.byContradiction
    intro hno
    apply hall
    rw [List.all_eq_true]
    intro p hp
    cases hc : a'.sideForbidsB p w r
    · exact absurd ⟨p, hp, hc⟩ hno
    · rfl
  rcases pairsOf_mem hxn hyn nxy with hp | hp
  · obtain ⟨p, hp', hf⟩ := pick (w := x) (r := y) (fun hall => by
      have := written hp hxy nxy hall; rw [hn] at this; cases this)
    exact ⟨p, hp', Or.inl hf⟩
  · obtain ⟨p, hp', hf⟩ := pick (w := y) (r := x) (fun hall => by
      have h := written hp ((adj_symm a' x y).mp hxy) (Ne.symm nxy) hall
      obtain ⟨σ, hσ, hti⟩ := List.any_eq_true.mp h
      have : (a'.upForbidRow ids).trios.any (trioIs t x y) = true :=
        List.any_eq_true.mpr ⟨σ, hσ, trioIs_swap23 hti⟩
      rw [hn] at this; cases this)
    exact ⟨p, hp', Or.inr hf⟩

section UpFace

variable {Y : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **`up_forbid` es completo.** En el UP `:on` de un estado válido `Y`, una cara `(t, x, y)` de una cima nueva `t`
(con `x`, `y` nodos viejos, vecinos de `t` y entre sí) que no está prohibida en la llegada tiene un padre `p` de `t`
que no la cortaba en `Y`: `p` es vecino de `x` y de `y` en `Y` y el trío `{p, x, y}` no está escrito en `Y`. -/
theorem upOn_face_parent (hi : SInvB Y) (hd : d.step = Y.current_step) (hv : Y.isValid = true)
    {t x y : PathNodeId} (ht : t ∈ (Y.upOn d title forb).alive) (hts : t.id.step = Y.current_step)
    (hxa : x ∈ (Y.upOn d title forb).alive) (hya : y ∈ (Y.upOn d title forb).alive)
    (hx : x.id.step < Y.current_step) (hy : y.id.step < Y.current_step) (nxy : x ≠ y)
    (htx : (Y.upOn d title forb).Adj t x) (hty : (Y.upOn d title forb).Adj t y)
    (hxy : (Y.upOn d title forb).Adj x y) (hn : ¬ TF (Y.upOn d title forb) t x y) :
    ∃ p ∈ Y.rowParents d t, Y.Adj p x ∧ Y.Adj p y ∧ Y.Adj x y ∧
      (p ≠ x → p ≠ y → ∀ τ ∈ Y.trios, trioIs p x y τ = false) := by
  have nxt : x ≠ t := fun e => by rw [e, hts] at hx; exact Int.lt_irrefl _ hx
  have nyt : y ≠ t := fun e => by rw [e, hts] at hy; exact Int.lt_irrefl _ hy
  have hX : Y.upOn d title forb =
      (((Y.addNode d title forb).setT Y.trios).upForbidRow (Y.newRowIds d forb)).reviewOn := by
    unfold upOn; rw [if_pos hv]
  have hsub := sub_upOn_addNode (d := d) (title := title) (forb := forb) hv
  -- `t` es de la fila nueva
  have htnew : t ∈ Y.newRowIds d forb := by
    rcases alive_addNode_cases (title := title) (forb := forb) hi.docs hi.below hd (hsub.alive t ht) with
      ⟨_, h⟩ | ⟨h, _⟩
    · rw [hts] at h; exact absurd h (Int.lt_irrefl _)
    · exact h
  -- la cara no quedó escrita por `up_forbid!`
  have hnU : (((Y.addNode d title forb).setT Y.trios).upForbidRow (Y.newRowIds d forb)).trios.any
      (trioIs t x y) = false := by
    cases hc : (((Y.addNode d title forb).setT Y.trios).upForbidRow (Y.newRowIds d forb)).trios.any (trioIs t x y)
    · rfl
    · exfalso
      obtain ⟨σ, hσ, hti⟩ := List.any_eq_true.mp hc
      exact hn (tF_of_trioIs htx (Ne.symm nxt) (by rw [hX]; exact trios_grow_reviewOn _ σ hσ) hti)
  obtain ⟨p, hp, hf⟩ := upForbidRow_face (a' := (Y.addNode d title forb).setT Y.trios) htnew
    (hsub.alive x hxa) (hsub.alive y hya) (hsub.adj _ _ htx) (hsub.adj _ _ hty) (hsub.adj _ _ hxy) nxt nyt nxy hnU
  have hpar : ((Y.addNode d title forb).setT Y.trios).parentsOf t = Y.rowParents d t := by
    unfold parentsOf
    rw [show ((Y.addNode d title forb).setT Y.trios).node? t = some (Y.rowNode d title t) from
      node?_addNode_new hi.below hd htnew]
    rfl
  rw [hpar] at hp
  obtain ⟨_, _, _, hps⟩ := step_of_newParents (rowParents_sub hp)
  have hpl : p.id.step < Y.current_step := by omega
  have old : ∀ {u w : PathNodeId}, u.id.step < Y.current_step → w.id.step < Y.current_step →
      ((Y.addNode d title forb).setT Y.trios).Adj u w → Y.Adj u w :=
    fun hu hw h => adj_addNode_old (title := title) (forb := forb) hd hu hw h
  refine ⟨p, hp, ?_⟩
  rcases hf with hf | hf
  · obtain ⟨h1, h2, h3, h4⟩ := of_sideForbidsB_false hf
    exact ⟨old hpl hx h1, old hpl hy h2, old hx hy h3, fun n1 n2 => h4 n1 n2 nxy⟩
  · obtain ⟨h1, h2, h3, h4⟩ := of_sideForbidsB_false hf
    refine ⟨old hpl hx h2, old hpl hy h1, (adj_symm Y y x).mp (old hy hx h3), fun n1 n2 τ hτ => ?_⟩
    cases hc : trioIs p x y τ
    · rfl
    · have := h4 n2 n1 (Ne.symm nxy) τ hτ
      rw [trioIs_swap23 hc] at this; cases this

end UpFace

/-- **Un padre sostiene la cara `(t, x, y)`** en el remitente `E`: una cima viva `p` de `E`, padre posible de `t`,
vecina de `x` y de `y`, con `x`, `y` vecinos y el trío `{p, x, y}` sin escribir. -/
def HoldsFace (E : GPathB) (t x y : PathNodeId) : Prop :=
  ∃ p ∈ E.alive, p.id.step = E.current_step - 1 ∧ Compat p t ∧ E.Adj p x ∧ E.Adj p y ∧ E.Adj x y ∧
    (p ≠ x → p ≠ y → ∀ τ ∈ E.trios, trioIs p x y τ = false)

/-- **`up_forbid` es completo, en la máquina**: una cara `(t, x, y)` de una cima de la llegada `arrOn φ kv d` que no
está prohibida la sostiene un padre de `t` en la entrada `kv` (antes del filtro y del UP). -/
theorem arrOn_face_parent {φ : Cnf} {T : Int} {kv : NodeId × GPathB} (hent : EntOn T kv.1 kv.2) (hi : SInvB kv.2)
    {d : NodeId} (hs : SendsOn φ kv d) {t x y : PathNodeId} (ht : t ∈ (arrOn φ kv d).alive)
    (hts : t.id.step = (arrOn φ kv d).current_step - 1)
    (hxa : x ∈ (arrOn φ kv d).alive) (hya : y ∈ (arrOn φ kv d).alive) (hx : x.id.step < T) (hy : y.id.step < T)
    (nxy : x ≠ y) (htx : (arrOn φ kv d).Adj t x) (hty : (arrOn φ kv d).Adj t y) (hxy : (arrOn φ kv d).Adj x y)
    (hn : ¬ TF (arrOn φ kv d) t x y) : HoldsFace kv.2 t x y := by
  have hok := hent.1
  have hcsY : (kv.2.filterAllOn (reqOf φ d)).current_step = T := by rw [step_filterAllOn]; exact hok.step
  have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by
    rw [hcsY, sonsOfMap_step φ kv.1 d hs.1, hok.key]; omega
  have hvY := valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
  have hiY := sInvB_filterAllOn hi (reqOf φ d)
  have hstep : (arrOn φ kv d).current_step = T + 1 := (entOn_upFilteringOn hent hs.1 hs.2).1.step
  obtain ⟨p, hp, h1, h2, h3, h4⟩ := upOn_face_parent (title := "") (forb := isProhibited φ) hiY hdY hvY ht
    (by rw [hcsY, hts, hstep]; omega) hxa hya (by rw [hcsY]; exact hx) (by rw [hcsY]; exact hy) nxy htx hty hxy hn
  have hsh := (shrinks_filterAllOn kv.2 (reqOf φ d)).1
  obtain ⟨_, _, _, hps⟩ := step_of_newParents (rowParents_sub hp)
  exact ⟨p, hsh.alive p (hiY.edges p x h1).1, by rw [hps, hcsY, hok.step], compat_rowParents hdY hp,
    hsh.adj _ _ h1, hsh.adj _ _ h2, hsh.adj _ _ h3,
    fun n1 n2 τ hτ => h4 n1 n2 τ (trios_grow_filterAllOn kv.2 (reqOf φ d) τ hτ)⟩

-- ============================================================
-- La base muerta bajo una cima
-- ============================================================

/-- **Una base muerta bajo una cima**: `t` es una cima viva de `g`; `x`, `y`, `z` son vecinos suyos distintos, vecinos
entre sí; las tres caras con `t` no están prohibidas y la base `(x, y, z)` sí. Es la premisa de `PrevCut`. -/
def DeadBase (g : GPathB) (t x y z : PathNodeId) : Prop :=
  t ∈ g.alive ∧ t.id.step = g.current_step - 1 ∧ x ≠ t ∧ y ≠ t ∧ z ≠ t ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    g.Adj t x ∧ g.Adj t y ∧ g.Adj t z ∧ g.Adj x y ∧ g.Adj x z ∧ g.Adj y z ∧
    ¬ Sym (TF g) x y t ∧ ¬ Sym (TF g) x z t ∧ ¬ Sym (TF g) y z t ∧ TF g x y z

/-- `PrevCut`, con su premisa escrita como `DeadBase`. -/
theorem hPrevCut_iff {φ : Cnf} {prev : Line} {T : Int} :
    HPrevCut φ prev T ↔ ∀ a ∈ advanceM .on φ prev, ∀ d, SendsOn φ a d → ∀ t x y z,
      DeadBase (arrOn φ a d) t x y z → x.id.step < T → y.id.step < T → z.id.step < T →
      ∀ e ∈ prev, SideForbids e.2 (TF e.2) x y z := by
  constructor
  · intro h a ha d hs t x y z ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    exact h a ha d hs t x y z h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  · intro h a ha d hs t x y z h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
    exact h a ha d hs t x y z ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

/-- **Bajo una base muerta de una llegada, cada cara de la cima la sostiene un padre en el remitente.** -/
theorem deadBase_arr_parents {φ : Cnf} {T : Int} (hT : 1 ≤ T) {kv : NodeId × GPathB} (hent : EntOn T kv.1 kv.2)
    (hi : SInvB kv.2) (hap : AdjPar kv.2) (hta : TopsApart kv.2) {d : NodeId} (hs : SendsOn φ kv d)
    {t x y z : PathNodeId} (h : DeadBase (arrOn φ kv d) t x y z) :
    HoldsFace kv.2 t x y ∧ HoldsFace kv.2 t x z ∧ HoldsFace kv.2 t y z := by
  obtain ⟨ht, hts, nxt, nyt, nzt, nxy, nxz, nyz, htx, hty, htz, hxy, hxz, hyz, f1, f2, f3, _⟩ := h
  have hok := hent.1
  have hd : d.step = kv.2.current_step := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key, hok.step]; omega
  have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by rw [step_filterAllOn]; exact hd
  have ia : SInvB (arrOn φ kv d) :=
    sInvB_upOn (sInvB_filterAllOn hi _) hdY (by rw [hd, hok.step]; omega)
  have hstep : (arrOn φ kv d).current_step = T + 1 := (entOn_upFilteringOn hent hs.1 hs.2).1.step
  obtain ⟨_, ta⟩ := arrOn_adjPar hent hi hap hta hs
  have low : ∀ {q : PathNodeId}, (arrOn φ kv d).Adj t q → q ≠ t → q.id.step < T := by
    intro q hq hne
    have h1 := alive_below ia.docs ia.below (ia.edges t q hq).2
    have h2 : q.id.step ≠ (arrOn φ kv d).current_step - 1 := fun e => hne (ta t q hts e hq).symm
    rw [hstep] at h1 h2
    omega
  have al : ∀ {q : PathNodeId}, (arrOn φ kv d).Adj t q → q ∈ (arrOn φ kv d).alive := fun hq => (ia.edges _ _ hq).2
  have nT : ∀ {u w : PathNodeId}, ¬ Sym (TF (arrOn φ kv d)) u w t → ¬ TF (arrOn φ kv d) t u w :=
    fun hn hf => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf)))))
  exact ⟨arrOn_face_parent hent hi hs ht hts (al htx) (al hty) (low htx nxt) (low hty nyt) nxy htx hty hxy (nT f1),
    arrOn_face_parent hent hi hs ht hts (al htx) (al htz) (low htx nxt) (low htz nzt) nxz htx htz hxz (nT f2),
    arrOn_face_parent hent hi hs ht hts (al hty) (al htz) (low hty nyt) (low htz nzt) nyz hty htz hyz (nT f3)⟩

-- ============================================================
-- La base muerta de una unión es la de una llegada
-- ============================================================

/-- **Los tríos de la unión `:on` los cortan los dos lados** (en el orden en que el join los guardó). -/
theorem tF_joinOn_inv {A B : GPathB} (hnsA : NoSelf A) (hnsB : NoSelf B) (heA : EdgesAlive A) (heB : EdgesAlive B)
    {x y z : PathNodeId} (h : TF (joinOn A B) x y z) :
    ∃ τ : PathNodeId × PathNodeId × PathNodeId, trioIs x y z τ = true ∧
      SideForbids A (TF A) τ.1 τ.2.1 τ.2.2 ∧ SideForbids B (TF B) τ.1 τ.2.1 τ.2.2 := by
  have hd := h.2
  unfold deadTrio at hd
  rw [Bool.and_eq_true] at hd
  obtain ⟨τ, hτ, hti⟩ := List.any_eq_true.mp hd.2
  let u : GPathB := { join A B with trios := [] }
  have hτ' : τ ∈ (u.addTrios (Idx.of u) (joinForbid A B)).1.trios := hτ
  rcases mem_addTrios u (Idx.of u) (joinForbid A B) τ hτ' with h0 | hj
  · exact absurd h0 List.not_mem_nil
  · obtain ⟨⟨d1, d2, d3⟩, _⟩ := joinForbid_facts hnsA hnsB heA heB hj
    obtain ⟨f1, f2⟩ := mem_joinForbid hj
    exact ⟨τ, hti, sideForbids_of_B d1 d2 d3 f1, sideForbids_of_B d1 d2 d3 f2⟩

/-- **Una base muerta de `J` bajo una cima que es de `S` y no de `O` es una base muerta de `S`**: las aristas de la
cima son de `S`; las de la base también, porque `J` habría prohibido su triángulo con la cima; las caras no están
prohibidas en `S` por lo mismo; y la base la corta `S`, que tiene sus tres aristas. -/
theorem deadBase_side {J S O : GPathB} (hndS : NoDegT S) (hcs : J.current_step = S.current_step)
    (hadj : ∀ x w, J.Adj x w → S.Adj x w ∨ O.Adj x w) (heO : EdgesAlive O)
    (hcut2 : ∀ {x y z}, J.Adj x y → J.Adj x z → J.Adj y z → x ≠ y → x ≠ z → y ≠ z → SideForbids S (TF S) x y z →
      SideForbids O (TF O) x y z → TF J x y z)
    (hinv : ∀ {x y z}, TF J x y z → ∃ τ : PathNodeId × PathNodeId × PathNodeId, trioIs x y z τ = true ∧
      SideForbids S (TF S) τ.1 τ.2.1 τ.2.2)
    {t x y z : PathNodeId} (htS : t ∈ S.alive) (htO : t ∉ O.alive) (h : DeadBase J t x y z) :
    DeadBase S t x y z := by
  obtain ⟨_, hts, nxt, nyt, nzt, nxy, nxz, nyz, htx, hty, htz, hxy, hxz, hyz, f1, f2, f3, hf⟩ := h
  have jsymm : ∀ {y w}, J.Adj y w → J.Adj w y := fun h => (adj_symm J _ _).mp h
  have ssymm : ∀ {y w}, S.Adj y w → S.Adj w y := fun h => (adj_symm S _ _).mp h
  have key : ∀ q, J.Adj t q → S.Adj t q := fun q h => (hadj t q h).resolve_right (fun ho => htO (heO t q ho).1)
  -- un triángulo de `J` con la cima, prohibido en `S`, está prohibido en `J`
  have face_up : ∀ {p q w}, J.Adj p q → J.Adj p w → J.Adj q w → (t = p ∨ t = q ∨ t = w) → TF S p q w →
      TF J p q w := by
    intro p q w hpq hpw hqw htin hf'
    have hd := hf'.2
    unfold deadTrio at hd
    rw [Bool.and_eq_true] at hd
    obtain ⟨τ, hτ, hti⟩ := List.any_eq_true.mp hd.2
    obtain ⟨npq, npw, nqw⟩ := distinct_of_trioIs hti (hndS τ hτ)
    refine hcut2 hpq hpw hqw npq npw nqw (Or.inr hf') (Or.inl ?_)
    intro ⟨h1, h2, _⟩
    apply htO
    rcases htin with e | e | e
    · rw [e]; exact (heO p q h1).1
    · rw [e]; exact (heO p q h1).2
    · rw [e]; exact (heO p w h2).2
  have nsymS : ∀ {y w}, J.Adj y w → J.Adj t y → J.Adj t w → ¬ Sym (TF J) y w t → ¬ Sym (TF S) y w t := by
    intro y w hyw hty htw hn hs
    apply hn
    refine sym_mono (fun p q x hp hf' => ?_) hs
    obtain ⟨h1, h2, h3⟩ := tri_of_perms (R := fun y w => J.Adj y w) jsymm hyw (jsymm hty) (jsymm htw) hp
    exact face_up h1 h2 h3 (perms_mem3 hp) hf'
  have sadj : ∀ {y w}, y ≠ w → y ≠ t → w ≠ t → J.Adj y w → J.Adj t y → J.Adj t w → ¬ Sym (TF J) y w t →
      S.Adj y w := by
    intro y w hyw hyt hwt h3 h1 h2 hn
    apply Classical.byContradiction
    intro hno
    exact hn (Or.inl (hcut2 h3 (jsymm h1) (jsymm h2) hyw hyt hwt (Or.inl fun h => hno h.1)
      (Or.inl fun h => htO (heO y t h.2.1).2)))
  have sxy := sadj nxy nxt nyt hxy htx hty f1
  have sxz := sadj nxz nxt nzt hxz htx htz f2
  have syz := sadj nyz nyt nzt hyz hty htz f3
  -- la base: `S` la corta y tiene sus tres aristas
  obtain ⟨τ, hti, hsf⟩ := hinv hf
  have hp : τ ∈ perms x y z := (trioIs_iff_perms x y z τ).mp hti
  obtain ⟨p, q, w⟩ := τ
  obtain ⟨a1, a2, a3⟩ := tri_of_perms (R := fun y w => S.Adj y w) ssymm sxy sxz syz hp
  have hT : TF S p q w := hsf.resolve_left (fun hno => hno ⟨a1, a2, a3⟩)
  have hsym : Sym (TF S) x y z := sym_perm (Or.inl hT) hp
  exact ⟨htS, by rw [← hcs]; exact hts, nxt, nyt, nzt, nxy, nxz, nyz, key x htx, key y hty, key z htz, sxy, sxz,
    syz, nsymS hxy htx hty f1, nsymS hxz htx htz f2, nsymS hyz hty htz f3, tF_of_sym_adj sxy nxy hsym⟩

/-- **La base muerta de una unión es la de uno de sus lados** (el de la cima). `bA`, `bB`: los colores de los padres
de las cimas de cada lado, distintos. -/
theorem deadBase_joinOn {A B : GPathB} {bA bB : NodeId} (hA : SInvB A) (hB : SInvB B) (hnsA : NoSelf A)
    (hnsB : NoSelf B) (hndA : NoDegT A) (hndB : NoDegT B) (hcs : A.current_step = B.current_step) (hne : bA ≠ bB)
    (hfA : TopsFrom A (fun a => a = bA)) (hfB : TopsFrom B (fun a => a = bB)) {t x y z : PathNodeId}
    (h : DeadBase (joinOn A B) t x y z) : DeadBase A t x y z ∨ DeadBase B t x y z := by
  have hcsJ : (joinOn A B).current_step = A.current_step := step_joinOn A B
  obtain ⟨T', hT⟩ := joinOn_eq A B
  have halive : ∀ q ∈ (joinOn A B).alive, q ∈ A.alive ∨ q ∈ B.alive := fun q hq => by
    rw [hT] at hq; exact (alive_join A B q).mp hq
  have hadj : ∀ x w, (joinOn A B).Adj x w → A.Adj x w ∨ B.Adj x w := fun x w h => by
    rw [hT] at h; exact adj_join_cases h
  have hts := h.2.1
  have hsep : t ∈ A.alive → t ∈ B.alive → False := by
    intro h1 h2
    obtain ⟨a, ha, hp⟩ := hfA t h1 (by rw [← hcsJ]; exact hts)
    obtain ⟨b, hb, hp'⟩ := hfB t h2 (by rw [← hcs, ← hcsJ]; exact hts)
    rw [hp, ha, hb] at hp'
    exact hne (Option.some.inj hp')
  rcases halive t h.1 with htA | htB
  · exact Or.inl (deadBase_side hndA hcsJ hadj hB.edges
      (fun hxy hxz hyz nxy nxz nyz s1 s2 => tF_joinOn_of_cut hA.edges hB.edges hxy hxz hyz nxy nxz nyz s1 s2)
      (fun hf => by
        obtain ⟨τ, k1, k2, _⟩ := tF_joinOn_inv hnsA hnsB hA.edges hB.edges hf
        exact ⟨τ, k1, k2⟩) htA (fun hb => hsep htA hb) h)
  · exact Or.inr (deadBase_side hndB (hcsJ.trans hcs) (fun x w h => (hadj x w h).symm) hA.edges
      (fun hxy hxz hyz nxy nxz nyz s2 s1 => tF_joinOn_of_cut hA.edges hB.edges hxy hxz hyz nxy nxz nyz s1 s2)
      (fun hf => by
        obtain ⟨τ, k1, _, k2⟩ := tF_joinOn_inv hnsA hnsB hA.edges hB.edges hf
        exact ⟨τ, k1, k2⟩) htB (fun ha => hsep ha htB) h)

-- ============================================================
-- La herencia: `PrevCut` de un nivel da el del siguiente para las bases que se heredan
-- ============================================================

/-- **Herencia.** Sea `L0` la línea del paso `T`. Si una entrada `a` de dos líneas después ya tiene la base
`(x, y, z)` muerta bajo una cima suya, y los nodos de la base existían en `L0`, entonces `PrevCut` de `L0` da el corte
en todas las entradas de la línea siguiente a `L0`: la entrada es una llegada o la unión de dos, la base muerta es de
una llegada (`deadBase_joinOn`), `PrevCut` la corta en toda `L0` y `lineCut_advance` sube el corte. -/
theorem prevCut_inherit {φ : Cnf} {T : Int} (hT : 1 ≤ T) {L0 : Line} (h0 : LInvTop φ T L0)
    (h1 : LInvTop φ (T + 1) (advanceM .on φ L0)) (hbk1 : LineBk (advanceM .on φ L0)) (hp : HPrevCut φ L0 T)
    {a : NodeId × GPathB} (ha : a ∈ advanceM .on φ (advanceM .on φ L0)) {p x y z : PathNodeId}
    (hdb : DeadBase a.2 p x y z) (hx : x.id.step < T) (hy : y.id.step < T) (hz : z.id.step < T) :
    ∀ e ∈ advanceM .on φ L0, SideForbids e.2 (TF e.2) x y z := by
  have hT' : (1 : Int) ≤ T + 1 := by omega
  have nxy : x ≠ y := hdb.2.2.2.2.2.1
  have nxz : x ≠ z := hdb.2.2.2.2.2.2.1
  have nyz : y ≠ z := hdb.2.2.2.2.2.2.2.1
  have fromArr : ∀ kv ∈ advanceM .on φ L0, SendsOn φ kv a.1 → DeadBase (arrOn φ kv a.1) p x y z →
      ∀ e ∈ advanceM .on φ L0, SideForbids e.2 (TF e.2) x y z := by
    intro kv hkv hs hd
    exact lineCut_advance hT h0 nxy nxz nyz hx hy hz (hPrevCut_iff.mp hp kv hkv a.1 hs p x y z hd hx hy hz)
  rcases entry_shapeOn (line_cases h1.nodup h1.keys) h1.nodup ha with ⟨kv, hkv, hs, he⟩ |
    ⟨k1, hk1, k2, hk2, hne, hs1, hs2, he⟩
  · rw [he] at hdb; exact fromArr kv hkv hs hdb
  · obtain ⟨e1, i1, n1, _, _⟩ := arrTop_facts hT' h1 hk1 hs1
    obtain ⟨e2, i2, n2, _, _⟩ := arrTop_facts hT' h1 hk2 hs2
    have hjoin : doJoinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1) = joinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1) := by
      unfold doJoinOn okJoin
      rw [if_pos (by simp [e1.1.step, e2.1.step, e1.1.mp, e2.1.mp, e1.1.valid, e2.1.valid])]
    obtain ⟨f1, _⟩ := arrOn_tops hT' (h1.on k1 hk1) (hbk1 k1 hk1).1 hs1
    obtain ⟨f2, _⟩ := arrOn_tops hT' (h1.on k2 hk2) (hbk1 k2 hk2).1 hs2
    rw [he, hjoin] at hdb
    rcases deadBase_joinOn i1 i2 e1.2.1 e2.2.1 n1 n2 (e1.1.step.trans e2.1.step.symm) hne f1 f2 hdb with h | h
    · exact fromArr k1 hk1 hs1 h
    · exact fromArr k2 hk2 hs2 h

/-- **`PrevCut` para las bases que no se heredan**: como `PrevCut`, pero solo cuando la entrada `a` que envía la
llegada **no** tenía ya la base muerta bajo una cima suya con los tres nodos de la base una línea más atrás. Son los
casos en que la base no estaba prohibida en `a`, o ningún padre de la cima sostiene las tres caras (cada cara tiene
el suyo, `deadBase_arr_parents`), o la base tiene un nodo en la cima de `prev`. -/
def HPrevNew (φ : Cnf) (prev : Line) (T : Int) : Prop :=
  ∀ a ∈ advanceM .on φ prev, ∀ d, SendsOn φ a d → ∀ t x y z, DeadBase (arrOn φ a d) t x y z →
    x.id.step < T → y.id.step < T → z.id.step < T →
    ¬ (∃ p, DeadBase a.2 p x y z ∧ x.id.step < T - 1 ∧ y.id.step < T - 1 ∧ z.id.step < T - 1) →
    ∀ e ∈ prev, SideForbids e.2 (TF e.2) x y z

/-- **El paso de la inducción**: `PrevCut` de una línea y `HPrevNew` de la siguiente dan `PrevCut` de la siguiente. -/
theorem hPrevCut_succ {φ : Cnf} {T : Int} (hT : 1 ≤ T) {L0 : Line} (h0 : LInvTop φ T L0)
    (h1 : LInvTop φ (T + 1) (advanceM .on φ L0)) (hbk1 : LineBk (advanceM .on φ L0)) (hp : HPrevCut φ L0 T)
    (hn : HPrevNew φ (advanceM .on φ L0) (T + 1)) : HPrevCut φ (advanceM .on φ L0) (T + 1) := by
  rw [hPrevCut_iff]
  intro a ha d hs t x y z hd hx hy hz
  by_cases hin : ∃ p, DeadBase a.2 p x y z ∧ x.id.step < T + 1 - 1 ∧ y.id.step < T + 1 - 1 ∧ z.id.step < T + 1 - 1
  · obtain ⟨p, hdb, k1, k2, k3⟩ := hin
    exact prevCut_inherit hT h0 h1 hbk1 hp ha hdb (by omega) (by omega) (by omega)
  · exact hn a ha d hs t x y z hd hx hy hz hin

/-- **El caso base**: en la primera línea no hay herencia (no hay nodos por debajo del paso 0). -/
theorem hPrevCut_init {φ : Cnf} (h1 : LInvTop φ (1 + 1) (advanceM .on φ (initM .on φ)))
    (hn : HPrevNew φ (initM .on φ) 1) : HPrevCut φ (initM .on φ) 1 := by
  rw [hPrevCut_iff]
  intro a ha d hs t x y z hd hx hy hz
  refine hn a ha d hs t x y z hd hx hy hz ?_
  rintro ⟨p, hdb, k1, _, _⟩
  have hi := h1.inv a ha
  have hxal : x ∈ a.2.alive := (hi.edges p x hdb.2.2.2.2.2.2.2.2.1).2
  obtain ⟨n, hn', hnid⟩ := hi.docs x hxal
  have := hi.zero n hn'
  rw [hnid] at this
  omega

/-- **Las hipótesis con la herencia descontada**: `HPrevNew` de cada línea a la siguiente, y el cierre a nivel cuatro
en cada join. -/
def HypsNew4On (φ : Cnf) : Prop :=
  (∀ n : Nat, HPrevNew φ (stepsM .on φ n (initM .on φ)) ((n : Int) + 1)) ∧
  (∀ n : Nat, HStar4On φ (stepsM .on φ n (initM .on φ)))

/-- La inducción de línea bajo `HypsNew4On`: el invariante, la contabilidad, el corte cruzado contra los remitentes y
`PrevCut` en cada línea. -/
theorem lInvNew_steps {φ : Cnf} (H : HypsNew4On φ) :
    ∀ n : Nat, LInvTop φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) ∧ LineBk (stepsM .on φ n (initM .on φ)) ∧
      HSender4On φ (stepsM .on φ n (initM .on φ)) ∧ HPrevCut φ (stepsM .on φ n (initM .on φ)) ((n : Int) + 1) := by
  intro n
  induction n with
  | zero =>
    have hl := lInvTop_init φ
    have hbk := lineBk_init φ
    have hs : HSender4On φ (initM .on φ) := by
      intro a ha b hb hab
      rw [initM_eq, List.mem_singleton] at ha hb
      exact absurd (by rw [ha, hb]) hab
    have hT : (1 : Int) ≤ 1 := by omega
    have hl' := lInvTop_advance hT hl (hTopOn_of_cross4 hT hl hbk (hCross4On_of_sender hT hl hbk hs))
    exact ⟨hl, hbk, hs, hPrevCut_init hl' (H.1 0)⟩
  | succ n ih =>
    obtain ⟨hl, hbk, hs, hpc⟩ := ih
    have hT : (1 : Int) ≤ (n : Int) + 1 := by omega
    have hl' := lInvTop_advance hT hl (hTopOn_of_cross4 hT hl hbk (hCross4On_of_sender hT hl hbk hs))
    have hbk' := lineBk_advance hT hl hbk
    have h4 := H.2 (n + 1)
    have hnw := H.1 (n + 1)
    have hcast : ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 := by push_cast; omega
    rw [stepsM_succ] at h4 hnw ⊢
    rw [hcast] at hnw ⊢
    refine ⟨hl', hbk', ?_, hPrevCut_succ hT hl hl' hbk' hpc hnw⟩
    intro a ha b hb hab d hsa hsb
    exact ⟨crossCut_of_prevCut hT hl hl' hbk' hpc ha hb hab hsa,
      crossCut_of_prevCut hT hl hl' hbk' hpc hb ha (Ne.symm hab) hsb, h4 a ha b hb hab d hsa hsb⟩

theorem hypsPrev4On_of_new {φ : Cnf} (H : HypsNew4On φ) : HypsPrev4On φ :=
  ⟨fun n => (lInvNew_steps H n).2.2.2, H.2⟩

end GPathB

namespace MachineOn

open GPathB Driver

/-- **El veredicto con la herencia descontada**: la espina `:on` decide la satisfacibilidad si

* **`HPrevNew`**: `PrevCut` para las bases muertas que la llegada no hereda de su remitente (la base no estaba
  prohibida en él, o ningún padre de la cima sostiene las tres caras, o la base toca la cima de la línea anterior);
* **`Star4At`**: la estrella de una cima de la unión fijada cierra a nivel cuatro.

Las bases heredadas las cierra la inducción (`prevCut_inherit`). -/
theorem spineVerdictOn_iff_of_new4 {φ : Cnf} (hbd : Bounded φ) (H : HypsNew4On φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_prev4 hbd (hypsPrev4On_of_new H)

end MachineOn

end AbsSatBingo.Model
