-- lean_project/AbsSat/GraphPath/Model/SegReview.lean
import AbsSat.GraphPath.Model.TopGoodUp
import AbsSat.GraphPath.Model.PinAliveChain

/-!
# `SegGood` a través del review: la pasada de padres, nodo a nodo

`reviewNode x` (con los padres como vecinos) corta la tabla de `x` con la **unión** de las tablas de
sus padres, y no toca la tabla de ningún otro nodo. Un tramo que sobrevive conserva su entrada común:

* si `x` no está en el tramo, las tablas del tramo no cambian;
* si `x` es un miembro que no es el más bajo, su padre en el tramo tiene la entrada común, así que
  está en la unión;
* si `x` es el más bajo, la entrada común del paso de abajo es un padre suyo —(I1): en el paso de
  justo abajo, owner es padre— y un padre es un nodo vivo; con la simetría local el tramo se alarga
  con él, y `SegGood` sobre el tramo largo da una entrada común que está en su tabla, luego en la
  unión.

Las hipótesis sobre el estado intermedio están medidas (`row-degree midinv`, `localsym`): (I1) no
falla nunca en la pasada de padres; la simetría **general** sí falla (32 de 53.646 estados en la
semilla 1), pero la **local** —la entrada común de un tramo, cuando es nodo vivo, tiene al tramo en
su tabla— no, y es la única que la prueba usa.
-/

namespace AbsSat.GraphPath.Model.SegReview

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.TopGoodUp
open AbsSat.GraphPath.Model.PinAliveChain
open AbsSat.GraphPath.Model.AggressiveReview (sharesEveryStep)

-- ============================================================
-- Lo que `reviewNode` hace a las tablas
-- ============================================================

theorem removeNode_ne (g : GPathM) (x y : PathNodeId) (n' : PNodeM)
    (h : (removeNode g x).node? y = some n') : y ≠ x := by
  have hmem : n' ∈ (removeNode g x).nodes := List.mem_of_find?_eq_some h
  rw [removeNode_nodes] at hmem
  obtain ⟨n0, hn0, heq⟩ := List.mem_map.mp hmem
  have hid : n'.id = y := node?_id_eq _ y n' h
  have hne := (List.mem_filter.mp hn0).2
  intro hyx
  rw [← heq] at hid
  have : n0.id = x := by rw [← hyx]; exact hid
  simp [this] at hne

/-- **Las tablas tras `reviewNode x`.** La de un nodo distinto de `x` es la de antes; la de `x`, la de
antes cortada con la unión de las de sus vecinos. -/
theorem reviewNode_owners (g : GPathM) (hnd : NodupIds g) (nb : PNodeM → List PathNodeId)
    (x y : PathNodeId) (n' : PNodeM) (h : (reviewNode g nb x).node? y = some n') :
    ∃ n, g.node? y = some n ∧
      (y ≠ x → n'.owners = n.owners) ∧
      (y = x → n'.owners = intersectOwners n.owners (unionOwnersOf g (nb n))) := by
  unfold reviewNode at h
  cases hd : g.node? x with
  | none =>
    rw [hd] at h
    refine ⟨n', h, fun _ => rfl, fun hyx => ?_⟩
    rw [hyx, hd] at h; cases h
  | some d =>
    rw [hd] at h
    simp only at h
    -- la cadena de inversiones: `updateAt`, luego `unlinkIncompatible`, luego quizá `removeNode`
    have hf : ∀ n : PNodeM,
        ({ n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) } : PNodeM).id = n.id :=
      fun _ => rfl
    have hnd1 := NodupIds_updateAt g x _ hf hnd
    have hnd2 := NodupIds_unlinkIncompatible _ x hnd1
    have fromG2 : ∀ n2, (unlinkIncompatible (updateAt g x (fun n =>
          { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x).node? y =
          some n2 →
        ∃ n, g.node? y = some n ∧
          (y ≠ x → n2.owners = n.owners) ∧
          (y = x → n2.owners = intersectOwners n.owners (unionOwnersOf g (nb n))) := by
      intro n2 hn2
      obtain ⟨n1, hn1, ho1⟩ := unlinkIncompatible_node?_inv _ hnd1 x y n2 hn2
      obtain ⟨n0, hn0, heq⟩ := Reader.updateAt_node?_inv g x _ hf y n1 hn1
      have hn0id : n0.id = y := node?_id_eq g y n0 hn0
      refine ⟨n0, hn0, fun hne => ?_, fun hyx => ?_⟩
      · have hb : (n0.id == x) = false := by rw [hn0id]; exact beq_false_of_ne hne
        rw [ho1, heq, hb]
      · have hb : (n0.id == x) = true := by rw [hn0id, hyx]; exact beq_self_eq_true x
        have hdn : d = n0 := by rw [hyx] at hn0; exact Option.some.inj (hd.symm.trans hn0)
        rw [ho1, heq, hb, hdn]
    split at h
    · split at h
      · exact fromG2 n' h
      · have hne := removeNode_ne _ x y n' h
        obtain ⟨n2, hn2, ho2⟩ := removeNode_node?_inv _ hnd2 x y n' h
        obtain ⟨n, hn, hne', _⟩ := fromG2 n2 hn2
        exact ⟨n, hn, fun _ => by rw [ho2, hne' hne], fun hyx => absurd hyx hne⟩
    · have hne := removeNode_ne _ x y n' h
      obtain ⟨n0, hn0, ho0⟩ := removeNode_node?_inv _ hnd x y n' h
      exact ⟨n0, hn0, fun _ => ho0, fun hyx => absurd hyx hne⟩

/-- info: 'AbsSat.GraphPath.Model.SegReview.reviewNode_owners' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reviewNode_owners

-- ============================================================
-- Alargar un tramo con un padre del más bajo
-- ============================================================

open AbsSat.GraphPath.Model.Extendable (upd upd_self upd_other)

/-- **Un tramo se alarga por abajo con un nodo `r₀` que es padre del más bajo, está en todas las
tablas del tramo y lo tiene entero en la suya.** -/
theorem seg_extend (g : GPathM) (sel : Int → PathNodeId) (lo hi : Int) (hlohi : lo ≤ hi)
    (hs : Seg g sel lo hi) (r0 : PathNodeId) (nr0 : PNodeM) (hnr0 : g.node? r0 = some nr0)
    (hr0s : r0.id.step = lo - 1)
    (hpar : ∀ nl, g.node? (sel lo) = some nl → r0 ∈ nl.parents)
    (hin : ∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r0 ∈ nj.owners)
    (hback : ∀ j, lo ≤ j → j ≤ hi → sel j ∈ nr0.owners) :
    Seg g (upd sel (lo - 1) r0) (lo - 1) hi := by
  obtain ⟨hch, hpw⟩ := hs
  refine ⟨⟨fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_⟩, fun i j hi1 hj1 hi2 hj2 hij nj hnj => ?_⟩
  · rcases int_eq_or_ne i (lo - 1) with he | he
    · subst he; rw [upd_self]; exact ⟨by rw [hnr0]; rfl, hr0s⟩
    · rw [upd_other sel (lo - 1) r0 he]; exact hch.1 i (by omega) hi2
  · rcases int_eq_or_ne i (lo - 1) with he | he
    · subst he
      rw [upd_self, upd_other sel (lo - 1) r0 (by omega), show lo - 1 + 1 = lo from by omega]
      obtain ⟨hls, _⟩ := hch.1 lo (Int.le_refl _) hlohi
      obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp hls
      rw [hnl]
      simp only [Option.map_some, Option.getD_some]
      exact hpar nl hnl
    · rw [upd_other sel (lo - 1) r0 he, upd_other sel (lo - 1) r0 (by omega)]
      exact hch.2 i (by omega) hi2
  · rcases int_eq_or_ne i (lo - 1) with hei | hei
    · subst hei
      rw [upd_self]
      rw [upd_other sel (lo - 1) r0 (fun h => hij h.symm)] at hnj
      exact hin j (by omega) hj2 nj hnj
    · rw [upd_other sel (lo - 1) r0 hei]
      rcases int_eq_or_ne j (lo - 1) with hej | hej
      · subst hej
        rw [upd_self] at hnj
        rw [← Option.some.inj (hnr0.symm.trans hnj)]
        exact hback i (by omega) hi2
      · rw [upd_other sel (lo - 1) r0 hej] at hnj
        exact hpw i j (by omega) (by omega) hi2 hj2 hij nj hnj

-- ============================================================
-- La pasada de padres, nodo a nodo
-- ============================================================

/-- **La simetría local**: la entrada común de un tramo en el paso de justo debajo, cuando es un
nodo vivo, tiene al tramo entero en su tabla. Es la única simetría que la prueba usa; la general
falla en estados intermedios, ésta no (`row-degree localsym`). -/
def LocSym (g : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), lo ≤ hi → Seg g sel lo hi →
    ∀ r0 nr0, g.node? r0 = some nr0 → r0.id.step = lo - 1 →
    (∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r0 ∈ nj.owners) →
    ∀ j, lo ≤ j → j ≤ hi → sel j ∈ nr0.owners

/-- Lo que está en la tabla de un padre queda en la de `x` tras cortarla con la unión. -/
theorem mem_intersect_of_parent (g : GPathM) (n : PNodeM) (r : PathNodeId) (hr : r ∈ n.owners)
    (p : PathNodeId) (hp : p ∈ n.parents) (np : PNodeM) (hnp : g.node? p = some np)
    (hrp : r ∈ np.owners) : r ∈ intersectOwners n.owners (unionOwnersOf g n.parents) := by
  refine List.mem_filter.mpr ⟨hr, ?_⟩
  have hu := mem_unionOwnersOf g n.parents p np r hp hnp hrp
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.elem_iff]
  exact Or.inr hu

/-- **`reviewNode x`, con los padres como vecinos, conserva `SegGood`.** -/
theorem segGood_reviewNode_parents (g : GPathM) (hnd : NodupIds g)
    (hI1 : ∀ y ny, g.node? y = some ny → ∀ w ∈ ny.owners, w.id.step + 1 = y.id.step →
      w ∈ ny.parents)
    (hplive : ∀ y ny, g.node? y = some ny → ∀ p ∈ ny.parents, (g.node? p).isSome)
    (hself : ∀ y ny, g.node? y = some ny → y ∈ ny.owners)
    (hlsym : LocSym g) (hseg : SegGood g) (x : PathNodeId) (hx1 : 1 ≤ x.id.step) :
    SegGood (reviewNode g (·.parents) x) := by
  have hpr := pruned_reviewNode (·.parents) x g
  -- un nodo de después viene de uno de antes
  have lift : ∀ y n', (reviewNode g (·.parents) x).node? y = some n' →
      ∃ n, g.node? y = some n ∧ (∀ q ∈ n'.owners, q ∈ n.owners) ∧
        (∀ p ∈ n'.parents, p ∈ n.parents) ∧ (y ≠ x → n'.owners = n.owners) ∧
        (y = x → n'.owners = intersectOwners n.owners (unionOwnersOf g n.parents)) := by
    intro y n' h
    obtain ⟨n, hn, hne, heq⟩ := reviewNode_owners g hnd (·.parents) x y n' h
    obtain ⟨n0, hn0, hid0, hown0, hpar0⟩ := hpr.nodes_derived n' (List.mem_of_find?_eq_some h)
    have hy : n'.id = y := node?_id_eq _ y n' h
    have hn0' : g.node? y = some n0 := by rw [← hy, hid0]; exact node?_of_mem hnd n0 hn0
    rw [hn] at hn0'; cases hn0'
    exact ⟨n, hn, hown0, hpar0, hne, heq⟩
  intro sel lo hi hlo0 hlohi hhi hch' hpw' i hi0 hic hout
  rw [hpr.step_eq] at hhi hic
  -- el tramo es tramo de antes
  have hsG : Seg g sel lo hi := by
    refine ⟨⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_⟩, fun a b ha1 hb1 ha2 hb2 hab nb hnb => ?_⟩
    · obtain ⟨hs, hjs⟩ := hch'.1 j hj1 hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _⟩ := lift _ m hm
      exact ⟨by rw [hn]; rfl, hjs⟩
    · obtain ⟨hs, _⟩ := hch'.1 (j + 1) (by omega) hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _, hpar, _⟩ := lift _ m hm
      have hl := hch'.2 j hj1 hj2
      rw [hm] at hl
      rw [hn]
      simp only [Option.map_some, Option.getD_some] at hl ⊢
      exact hpar _ hl
    · obtain ⟨hs, _⟩ := hch'.1 b hb1 hb2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, hown, _⟩ := lift _ m hm
      rw [← Option.some.inj (hn.symm.trans hnb)]
      exact hown _ (hpw' a b ha1 hb1 ha2 hb2 hab m hm)
  -- una entrada común de antes queda, salvo en `x`, donde basta que la tenga un padre de `x`
  have keep : ∀ r, (∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r ∈ nj.owners) →
      (∀ j, lo ≤ j → j ≤ hi → sel j = x → ∀ nj, g.node? (sel j) = some nj →
        ∃ p ∈ nj.parents, ∃ np, g.node? p = some np ∧ r ∈ np.owners) →
      ∀ j, lo ≤ j → j ≤ hi → ∀ nj', (reviewNode g (·.parents) x).node? (sel j) = some nj' →
        r ∈ nj'.owners := by
    intro r hr hx j hj1 hj2 nj' hnj'
    obtain ⟨n, hn, _, _, hne, heq⟩ := lift _ nj' hnj'
    if hjx : sel j = x then
      rw [heq hjx]
      obtain ⟨p, hp, np, hnp, hrp⟩ := hx j hj1 hj2 hjx n hn
      exact mem_intersect_of_parent g n r (hr j hj1 hj2 n hn) p hp np hnp hrp
    else
      rw [hne hjx]; exact hr j hj1 hj2 n hn
  obtain ⟨hlsome, hls⟩ := hsG.1.1 lo (Int.le_refl _) hlohi
  obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp hlsome
  if hlx : sel lo = x then
    -- el más bajo es `x`: se alarga el tramo con un padre suyo
    have hlo1 : 1 ≤ lo := by rw [← hls, hlx]; exact hx1
    obtain ⟨r0, hr0s, hr0all⟩ := hseg sel lo hi hlo0 hlohi hhi hsG.1 hsG.2 (lo - 1) (by omega)
      (by omega) (Or.inl (by omega))
    have hr0p : r0 ∈ nl.parents :=
      hI1 _ nl hnl r0 (hr0all lo (Int.le_refl _) hlohi nl hnl) (by rw [hr0s, hls]; omega)
    obtain ⟨nr0, hnr0⟩ := Option.isSome_iff_exists.mp (hplive _ nl hnl r0 hr0p)
    have hback := hlsym sel lo hi hlohi hsG r0 nr0 hnr0 hr0s hr0all
    have hs' := seg_extend g sel lo hi hlohi hsG r0 nr0 hnr0 hr0s
      (fun nl' hnl' => by rw [← Option.some.inj (hnl.symm.trans hnl')]; exact hr0p) hr0all hback
    -- en `x` solo puede estar el paso `lo`
    have hxonly : ∀ j, lo ≤ j → j ≤ hi → sel j = x → j = lo := by
      intro j hj1 hj2 hjx
      have := (hsG.1.1 j hj1 hj2).2
      rw [hjx, ← hlx, hls] at this; omega
    rcases int_eq_or_ne i (lo - 1) with hie | hie
    · refine ⟨r0, by omega, keep r0 hr0all (fun j hj1 hj2 hjx nj hnj => ?_)⟩
      rw [hxonly j hj1 hj2 hjx] at hnj
      rw [← Option.some.inj (hnl.symm.trans hnj)]
      exact ⟨r0, hr0p, nr0, hnr0, hself _ nr0 hnr0⟩
    · obtain ⟨r, hrs, hrall⟩ := hseg _ (lo - 1) hi (by omega) (by omega) hhi hs'.1 hs'.2 i hi0
        hic (by omega)
      have hr : ∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r ∈ nj.owners := by
        intro j hj1 hj2 nj hnj
        have := hrall j (by omega) hj2 nj
        rw [upd_other sel (lo - 1) r0 (by omega)] at this
        exact this hnj
      refine ⟨r, hrs, keep r hr (fun j hj1 hj2 hjx nj hnj => ?_)⟩
      rw [hxonly j hj1 hj2 hjx] at hnj
      rw [← Option.some.inj (hnl.symm.trans hnj)]
      have hrr0 := hrall (lo - 1) (Int.le_refl _) (by omega) nr0
      rw [upd_self] at hrr0
      exact ⟨r0, hr0p, nr0, hnr0, hrr0 hnr0⟩
  else
    -- el más bajo no es `x`: si `x` está en el tramo, su padre en el tramo tiene la entrada
    obtain ⟨r, hrs, hrall⟩ := hseg sel lo hi hlo0 hlohi hhi hsG.1 hsG.2 i hi0 hic hout
    refine ⟨r, hrs, keep r hrall (fun j hj1 hj2 hjx nj hnj => ?_)⟩
    have hjlo : j ≠ lo := fun h => hlx (by rw [← h]; exact hjx)
    obtain ⟨hps, _⟩ := hsG.1.1 (j - 1) (by omega) (by omega)
    obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp hps
    have hl := hsG.1.2 (j - 1) (by omega) (by omega)
    rw [show j - 1 + 1 = j by omega, hnj] at hl
    simp only [Option.map_some, Option.getD_some] at hl
    exact ⟨sel (j - 1), hl, np, hnp, hrall (j - 1) (by omega) (by omega) np hnp⟩

/-- info: 'AbsSat.GraphPath.Model.SegReview.segGood_reviewNode_parents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segGood_reviewNode_parents

-- ============================================================
-- La pasada de hijos, nodo a nodo: el espejo
-- ============================================================

/-- Lo que está en la tabla de un vecino queda en la de `x` tras cortarla con la unión. -/
theorem mem_intersect_of_nb (g : GPathM) (n : PNodeM) (ids : List PathNodeId) (r : PathNodeId)
    (hr : r ∈ n.owners) (p : PathNodeId) (hp : p ∈ ids) (np : PNodeM) (hnp : g.node? p = some np)
    (hrp : r ∈ np.owners) : r ∈ intersectOwners n.owners (unionOwnersOf g ids) := by
  refine List.mem_filter.mpr ⟨hr, ?_⟩
  have hu := mem_unionOwnersOf g ids p np r hp hnp hrp
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.elem_iff]
  exact Or.inr hu

/-- **Un tramo se alarga por arriba** con un nodo `r₀` que tiene al más alto por padre, está en todas
las tablas del tramo y lo tiene entero en la suya. -/
theorem seg_extend_up (g : GPathM) (sel : Int → PathNodeId) (lo hi : Int) (hlohi : lo ≤ hi)
    (hs : Seg g sel lo hi) (r0 : PathNodeId) (nr0 : PNodeM) (hnr0 : g.node? r0 = some nr0)
    (hr0s : r0.id.step = hi + 1) (hpar : sel hi ∈ nr0.parents)
    (hin : ∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r0 ∈ nj.owners)
    (hback : ∀ j, lo ≤ j → j ≤ hi → sel j ∈ nr0.owners) :
    Seg g (upd sel (hi + 1) r0) lo (hi + 1) := by
  obtain ⟨hch, hpw⟩ := hs
  refine ⟨⟨fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_⟩, fun i j hi1 hj1 hi2 hj2 hij nj hnj => ?_⟩
  · rcases int_eq_or_ne i (hi + 1) with he | he
    · subst he; rw [upd_self]; exact ⟨by rw [hnr0]; rfl, hr0s⟩
    · rw [upd_other sel (hi + 1) r0 he]; exact hch.1 i hi1 (by omega)
  · rcases int_eq_or_ne i hi with he | he
    · subst he
      rw [upd_self, upd_other sel (i + 1) r0 (by omega), hnr0]
      simp only [Option.map_some, Option.getD_some]
      exact hpar
    · rw [upd_other sel (hi + 1) r0 (by omega), upd_other sel (hi + 1) r0 (by omega)]
      exact hch.2 i hi1 (by omega)
  · rcases int_eq_or_ne i (hi + 1) with hei | hei
    · subst hei
      rw [upd_self]
      rw [upd_other sel (hi + 1) r0 (fun h => hij h.symm)] at hnj
      exact hin j hj1 (by omega) nj hnj
    · rw [upd_other sel (hi + 1) r0 hei]
      rcases int_eq_or_ne j (hi + 1) with hej | hej
      · subst hej
        rw [upd_self] at hnj
        rw [← Option.some.inj (hnr0.symm.trans hnj)]
        exact hback i hi1 (by omega)
      · rw [upd_other sel (hi + 1) r0 hej] at hnj
        exact hpw i j hi1 hj1 (by omega) (by omega) hij nj hnj

/-- **La simetría local por arriba**: la entrada común de un tramo en el paso de justo encima, cuando
es un nodo vivo, tiene al tramo entero en su tabla (`row-degree localsym`, borde de arriba). -/
def LocSymUp (g : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), lo ≤ hi → Seg g sel lo hi →
    ∀ r0 nr0, g.node? r0 = some nr0 → r0.id.step = hi + 1 →
    (∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r0 ∈ nj.owners) →
    ∀ j, lo ≤ j → j ≤ hi → sel j ∈ nr0.owners

/-- **`reviewNode x`, con los hijos como vecinos, conserva `SegGood`.** El caso difícil es ahora el
más ALTO del tramo: la entrada común de encima es un hijo suyo (I1-hijos), y es por padres que el
tramo se alarga con ella (I1). -/
theorem segGood_reviewNode_sons (g : GPathM) (hnd : NodupIds g)
    (hI1 : ∀ y ny, g.node? y = some ny → ∀ w ∈ ny.owners, w.id.step + 1 = y.id.step →
      w ∈ ny.parents)
    (hI1s : ∀ y ny, g.node? y = some ny → ∀ w ∈ ny.owners, w.id.step = y.id.step + 1 →
      w ∈ ny.sons)
    (hslive : ∀ y ny, g.node? y = some ny → ∀ q ∈ ny.sons, (g.node? q).isSome)
    (hself : ∀ y ny, g.node? y = some ny → y ∈ ny.owners)
    (hlsym : LocSymUp g) (hseg : SegGood g) (x : PathNodeId)
    (hxl : x.id.step ≤ g.current_step - 2) :
    SegGood (reviewNode g (·.sons) x) := by
  have hpr := pruned_reviewNode (·.sons) x g
  have lift : ∀ y n', (reviewNode g (·.sons) x).node? y = some n' →
      ∃ n, g.node? y = some n ∧ (∀ q ∈ n'.owners, q ∈ n.owners) ∧
        (∀ p ∈ n'.parents, p ∈ n.parents) ∧ (y ≠ x → n'.owners = n.owners) ∧
        (y = x → n'.owners = intersectOwners n.owners (unionOwnersOf g n.sons)) := by
    intro y n' h
    obtain ⟨n, hn, hne, heq⟩ := reviewNode_owners g hnd (·.sons) x y n' h
    obtain ⟨n0, hn0, hid0, hown0, hpar0⟩ := hpr.nodes_derived n' (List.mem_of_find?_eq_some h)
    have hy : n'.id = y := node?_id_eq _ y n' h
    have hn0' : g.node? y = some n0 := by rw [← hy, hid0]; exact node?_of_mem hnd n0 hn0
    rw [hn] at hn0'; cases hn0'
    exact ⟨n, hn, hown0, hpar0, hne, heq⟩
  intro sel lo hi hlo0 hlohi hhi hch' hpw' i hi0 hic hout
  rw [hpr.step_eq] at hhi hic
  have hsG : Seg g sel lo hi := by
    refine ⟨⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_⟩, fun a b ha1 hb1 ha2 hb2 hab nb hnb => ?_⟩
    · obtain ⟨hs, hjs⟩ := hch'.1 j hj1 hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _⟩ := lift _ m hm
      exact ⟨by rw [hn]; rfl, hjs⟩
    · obtain ⟨hs, _⟩ := hch'.1 (j + 1) (by omega) hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _, hpar, _⟩ := lift _ m hm
      have hl := hch'.2 j hj1 hj2
      rw [hm] at hl
      rw [hn]
      simp only [Option.map_some, Option.getD_some] at hl ⊢
      exact hpar _ hl
    · obtain ⟨hs, _⟩ := hch'.1 b hb1 hb2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, hown, _⟩ := lift _ m hm
      rw [← Option.some.inj (hn.symm.trans hnb)]
      exact hown _ (hpw' a b ha1 hb1 ha2 hb2 hab m hm)
  have keep : ∀ r, (∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r ∈ nj.owners) →
      (∀ j, lo ≤ j → j ≤ hi → sel j = x → ∀ nj, g.node? (sel j) = some nj →
        ∃ p ∈ nj.sons, ∃ np, g.node? p = some np ∧ r ∈ np.owners) →
      ∀ j, lo ≤ j → j ≤ hi → ∀ nj', (reviewNode g (·.sons) x).node? (sel j) = some nj' →
        r ∈ nj'.owners := by
    intro r hr hx j hj1 hj2 nj' hnj'
    obtain ⟨n, hn, _, _, hne, heq⟩ := lift _ nj' hnj'
    if hjx : sel j = x then
      rw [heq hjx]
      obtain ⟨p, hp, np, hnp, hrp⟩ := hx j hj1 hj2 hjx n hn
      exact mem_intersect_of_nb g n n.sons r (hr j hj1 hj2 n hn) p hp np hnp hrp
    else
      rw [hne hjx]; exact hr j hj1 hj2 n hn
  obtain ⟨hhsome, hhs⟩ := hsG.1.1 hi hlohi (Int.le_refl _)
  obtain ⟨nh, hnh⟩ := Option.isSome_iff_exists.mp hhsome
  if hhx : sel hi = x then
    -- el más alto es `x`: se alarga el tramo con un hijo suyo
    have hhi2 : hi ≤ g.current_step - 2 := by rw [← hhs, hhx]; exact hxl
    obtain ⟨r0, hr0s, hr0all⟩ := hseg sel lo hi hlo0 hlohi hhi hsG.1 hsG.2 (hi + 1) (by omega)
      (by omega) (Or.inr (by omega))
    have hr0son : r0 ∈ nh.sons :=
      hI1s _ nh hnh r0 (hr0all hi hlohi (Int.le_refl _) nh hnh) (by rw [hr0s, hhs])
    obtain ⟨nr0, hnr0⟩ := Option.isSome_iff_exists.mp (hslive _ nh hnh r0 hr0son)
    have hback := hlsym sel lo hi hlohi hsG r0 nr0 hnr0 hr0s hr0all
    have hpar : sel hi ∈ nr0.parents :=
      hI1 _ nr0 hnr0 _ (hback hi hlohi (Int.le_refl _)) (by rw [hhs, hr0s])
    have hs' := seg_extend_up g sel lo hi hlohi hsG r0 nr0 hnr0 hr0s hpar hr0all hback
    have hxonly : ∀ j, lo ≤ j → j ≤ hi → sel j = x → j = hi := by
      intro j hj1 hj2 hjx
      have := (hsG.1.1 j hj1 hj2).2
      rw [hjx, ← hhx, hhs] at this; omega
    rcases int_eq_or_ne i (hi + 1) with hie | hie
    · refine ⟨r0, by omega, keep r0 hr0all (fun j hj1 hj2 hjx nj hnj => ?_)⟩
      rw [hxonly j hj1 hj2 hjx] at hnj
      rw [← Option.some.inj (hnh.symm.trans hnj)]
      exact ⟨r0, hr0son, nr0, hnr0, hself _ nr0 hnr0⟩
    · obtain ⟨r, hrs, hrall⟩ := hseg _ lo (hi + 1) hlo0 (by omega) (by omega) hs'.1 hs'.2 i hi0
        hic (by omega)
      have hr : ∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r ∈ nj.owners := by
        intro j hj1 hj2 nj hnj
        have := hrall j hj1 (by omega) nj
        rw [upd_other sel (hi + 1) r0 (by omega)] at this
        exact this hnj
      refine ⟨r, hrs, keep r hr (fun j hj1 hj2 hjx nj hnj => ?_)⟩
      rw [hxonly j hj1 hj2 hjx] at hnj
      rw [← Option.some.inj (hnh.symm.trans hnj)]
      have hrr0 := hrall (hi + 1) (by omega) (Int.le_refl _) nr0
      rw [upd_self] at hrr0
      exact ⟨r0, hr0son, nr0, hnr0, hrr0 hnr0⟩
  else
    -- el más alto no es `x`: si `x` está en el tramo, su hijo en el tramo tiene la entrada
    obtain ⟨r, hrs, hrall⟩ := hseg sel lo hi hlo0 hlohi hhi hsG.1 hsG.2 i hi0 hic hout
    refine ⟨r, hrs, keep r hrall (fun j hj1 hj2 hjx nj hnj => ?_)⟩
    have hjhi : j ≠ hi := fun h => hhx (by rw [← h]; exact hjx)
    obtain ⟨hss, hs1⟩ := hsG.1.1 (j + 1) (by omega) (by omega)
    obtain ⟨ns, hns⟩ := Option.isSome_iff_exists.mp hss
    have hjs := (hsG.1.1 j hj1 hj2).2
    have hson : sel (j + 1) ∈ nj.sons :=
      hI1s _ nj hnj _ (hsG.2 (j + 1) j (by omega) hj1 (by omega) hj2 (by omega) nj hnj)
        (by rw [hs1, hjs])
    exact ⟨sel (j + 1), hson, ns, hns, hrall (j + 1) (by omega) (by omega) ns hns⟩

/-- info: 'AbsSat.GraphPath.Model.SegReview.segGood_reviewNode_sons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segGood_reviewNode_sons

-- ============================================================
-- El barrido: extender a cadena completa con hipótesis locales
-- ============================================================

/-- **Las hipótesis locales para extender tramos**, en un estado cualquiera (no hace falta que sea
punto fijo): (I1) y (I1-hijos), padres e hijos vivos, cada nodo se posee, y la simetría local por
los dos bordes. -/
structure ExtCtx (g : GPathM) : Prop where
  i1 : ∀ y ny, g.node? y = some ny → ∀ w ∈ ny.owners, w.id.step + 1 = y.id.step → w ∈ ny.parents
  i1s : ∀ y ny, g.node? y = some ny → ∀ w ∈ ny.owners, w.id.step = y.id.step + 1 → w ∈ ny.sons
  plive : ∀ y ny, g.node? y = some ny → ∀ p ∈ ny.parents, (g.node? p).isSome
  slive : ∀ y ny, g.node? y = some ny → ∀ q ∈ ny.sons, (g.node? q).isSome
  self : ∀ y ny, g.node? y = some ny → y ∈ ny.owners
  lsym : LocSym g
  lsymU : LocSymUp g

/-- Bajar un paso con las hipótesis locales. -/
theorem seg_down_loc (g : GPathM) (ec : ExtCtx g) (hseg : SegGood g) (sel : Int → PathNodeId)
    (lo hi : Int) (hpos : 0 < lo) (hlohi : lo ≤ hi) (hhi : hi ≤ g.current_step - 1)
    (hs : Seg g sel lo hi) : ∃ r, Seg g (upd sel (lo - 1) r) (lo - 1) hi := by
  obtain ⟨r0, hr0s, hr0all⟩ := hseg sel lo hi (by omega) hlohi hhi hs.1 hs.2 (lo - 1) (by omega)
    (by omega) (Or.inl (by omega))
  obtain ⟨hls, hlstep⟩ := hs.1.1 lo (Int.le_refl _) hlohi
  obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp hls
  have hr0p : r0 ∈ nl.parents :=
    ec.i1 _ nl hnl r0 (hr0all lo (Int.le_refl _) hlohi nl hnl) (by rw [hr0s, hlstep]; omega)
  obtain ⟨nr0, hnr0⟩ := Option.isSome_iff_exists.mp (ec.plive _ nl hnl r0 hr0p)
  exact ⟨r0, seg_extend g sel lo hi hlohi hs r0 nr0 hnr0 hr0s
    (fun nl' hnl' => by rw [← Option.some.inj (hnl.symm.trans hnl')]; exact hr0p) hr0all
    (ec.lsym sel lo hi hlohi hs r0 nr0 hnr0 hr0s hr0all)⟩

/-- Subir un paso con las hipótesis locales. -/
theorem seg_up_loc (g : GPathM) (ec : ExtCtx g) (hseg : SegGood g) (sel : Int → PathNodeId)
    (lo hi : Int) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi < g.current_step - 1)
    (hs : Seg g sel lo hi) : ∃ r, Seg g (upd sel (hi + 1) r) lo (hi + 1) := by
  obtain ⟨r0, hr0s, hr0all⟩ := hseg sel lo hi hlo hlohi (by omega) hs.1 hs.2 (hi + 1) (by omega)
    (by omega) (Or.inr (by omega))
  obtain ⟨hhs, hhstep⟩ := hs.1.1 hi hlohi (Int.le_refl _)
  obtain ⟨nh, hnh⟩ := Option.isSome_iff_exists.mp hhs
  have hr0son : r0 ∈ nh.sons :=
    ec.i1s _ nh hnh r0 (hr0all hi hlohi (Int.le_refl _) nh hnh) (by rw [hr0s, hhstep])
  obtain ⟨nr0, hnr0⟩ := Option.isSome_iff_exists.mp (ec.slive _ nh hnh r0 hr0son)
  have hback := ec.lsymU sel lo hi hlohi hs r0 nr0 hnr0 hr0s hr0all
  have hpar : sel hi ∈ nr0.parents :=
    ec.i1 _ nr0 hnr0 _ (hback hi hlohi (Int.le_refl _)) (by rw [hhstep, hr0s])
  exact ⟨r0, seg_extend_up g sel lo hi hlohi hs r0 nr0 hnr0 hr0s hpar hr0all hback⟩

/-- **Todo tramo se extiende a una cadena completa**, conservando sus miembros. -/
theorem seg_full (g : GPathM) (ec : ExtCtx g) (hseg : SegGood g) (sel : Int → PathNodeId)
    (lo hi : Int) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ g.current_step - 1)
    (hs : Seg g sel lo hi) :
    ∃ sel', Seg g sel' 0 (g.current_step - 1) ∧ ∀ j, lo ≤ j → j ≤ hi → sel' j = sel j := by
  -- bajar
  have down : ∀ (fuel : Nat) (s : Int → PathNodeId) (l : Int), l.toNat ≤ fuel → 0 ≤ l → l ≤ lo →
      Seg g s l hi → (∀ j, lo ≤ j → j ≤ hi → s j = sel j) →
      ∃ s', Seg g s' 0 hi ∧ ∀ j, lo ≤ j → j ≤ hi → s' j = sel j := by
    intro fuel
    induction fuel with
    | zero =>
      intro s l hm hl0 hll hs' hagree
      have : l = 0 := by omega
      subst this; exact ⟨s, hs', hagree⟩
    | succ fuel ih =>
      intro s l hm hl0 hll hs' hagree
      if hpos : 0 < l then
        obtain ⟨r, hr⟩ := seg_down_loc g ec hseg s l hi hpos (by omega) hhi hs'
        exact ih _ (l - 1) (by omega) (by omega) (by omega) hr
          (fun j hj1 hj2 => by rw [upd_other s (l - 1) r (by omega)]; exact hagree j hj1 hj2)
      else
        have : l = 0 := by omega
        subst this; exact ⟨s, hs', hagree⟩
  obtain ⟨s1, hs1, hag1⟩ := down lo.toNat sel lo (Nat.le_refl _) hlo (Int.le_refl _) hs
    (fun _ _ _ => rfl)
  -- subir
  have up : ∀ (fuel : Nat) (s : Int → PathNodeId) (h : Int),
      (g.current_step - 1 - h).toNat ≤ fuel → hi ≤ h → h ≤ g.current_step - 1 →
      Seg g s 0 h → (∀ j, lo ≤ j → j ≤ hi → s j = sel j) →
      ∃ s', Seg g s' 0 (g.current_step - 1) ∧ ∀ j, lo ≤ j → j ≤ hi → s' j = sel j := by
    intro fuel
    induction fuel with
    | zero =>
      intro s h hm hh1 hh2 hs' hagree
      have : h = g.current_step - 1 := by omega
      subst this; exact ⟨s, hs', hagree⟩
    | succ fuel ih =>
      intro s h hm hh1 hh2 hs' hagree
      if hlt : h < g.current_step - 1 then
        obtain ⟨r, hr⟩ := seg_up_loc g ec hseg s 0 h (Int.le_refl _) (by omega) hlt hs'
        exact ih _ (h + 1) (by omega) (by omega) (by omega) hr
          (fun j hj1 hj2 => by rw [upd_other s (h + 1) r (by omega)]; exact hagree j hj1 hj2)
      else
        have : h = g.current_step - 1 := by omega
        subst this; exact ⟨s, hs', hagree⟩
  exact up (g.current_step - 1 - hi).toNat s1 hi (Nat.le_refl _) (Int.le_refl _) hhi hs1 hag1

/-- **Dos miembros de una cadena completa comparten entrada en cada paso**: la de la cadena. -/
theorem shares_of_full (g : GPathM) (hself : ∀ y ny, g.node? y = some ny → y ∈ ny.owners)
    (s : Int → PathNodeId) (hs : Seg g s 0 (g.current_step - 1)) (a b : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ g.current_step - 1) (hb0 : 0 ≤ b) (hb1 : b ≤ g.current_step - 1)
    (na nb : PNodeM) (hna : g.node? (s a) = some na) (hnb : g.node? (s b) = some nb) :
    sharesEveryStep g.current_step na.owners nb.owners = true := by
  -- la entrada de la cadena en el paso `k` está en la tabla de cualquier miembro
  have inT : ∀ c k, 0 ≤ c → c ≤ g.current_step - 1 → 0 ≤ k → k ≤ g.current_step - 1 →
      ∀ nc, g.node? (s c) = some nc → s k ∈ nc.owners := by
    intro c k hc0 hc1 hk0 hk1 nc hnc
    rcases int_eq_or_ne k c with he | he
    · subst he; exact hself _ nc hnc
    · exact hs.2 k c hk0 hc0 hk1 hc1 he nc hnc
  simp only [sharesEveryStep, List.all_eq_true]
  intro k hk
  have hk0 := mem_intRange_lower hk
  have hk1 := mem_intRange_upper hk
  have hks := (hs.1.1 k hk0 hk1).2
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  right
  exact List.any_eq_true.mpr ⟨s k, List.mem_filter.mpr ⟨inT a k ha0 ha1 hk0 hk1 na hna,
    beq_iff_eq.mpr hks⟩, List.elem_iff.mpr (inT b k hb0 hb1 hk0 hk1 nb hnb)⟩

/-- **Una pérdida «mala»**: el par `(y, q)` que el barrido puede romper —asimétrico o sin cruce—. -/
def BadPair (g : GPathM) (y q : PathNodeId) : Prop :=
  ∃ ny nq, g.node? y = some ny ∧ g.node? q = some nq ∧
    (y ∉ nq.owners ∨ sharesEveryStep g.current_step ny.owners nq.owners = false ∨
      sharesEveryStep g.current_step nq.owners ny.owners = false)

/-- **Si un paso solo quita entradas por pares malos, conserva `SegGood`.** El testigo es el miembro
de una cadena completa que extiende al tramo: tiene al tramo en su tabla y comparte con cada miembro
en cada paso, así que ningún par con él es malo. -/
theorem segGood_of_badDrops (g g' : GPathM) (ec : ExtCtx g) (hseg : SegGood g)
    (hstep : g'.current_step = g.current_step)
    (hnode : ∀ y n', g'.node? y = some n' → ∃ n, g.node? y = some n ∧
      (∀ p ∈ n'.parents, p ∈ n.parents) ∧ (∀ q ∈ n'.owners, q ∈ n.owners) ∧
      (∀ q ∈ n.owners, q ∉ n'.owners → BadPair g y q)) :
    SegGood g' := by
  intro sel lo hi hlo0 hlohi hhi hch' hpw' i hi0 hic hout
  rw [hstep] at hhi hic
  have hsG : Seg g sel lo hi := by
    refine ⟨⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_⟩, fun a b ha1 hb1 ha2 hb2 hab nb hnb => ?_⟩
    · obtain ⟨hs, hjs⟩ := hch'.1 j hj1 hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _⟩ := hnode _ m hm
      exact ⟨by rw [hn]; rfl, hjs⟩
    · obtain ⟨hs, _⟩ := hch'.1 (j + 1) (by omega) hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, hpar, _⟩ := hnode _ m hm
      have hl := hch'.2 j hj1 hj2
      rw [hm] at hl
      rw [hn]
      simp only [Option.map_some, Option.getD_some] at hl ⊢
      exact hpar _ hl
    · obtain ⟨hs, _⟩ := hch'.1 b hb1 hb2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _, hown, _⟩ := hnode _ m hm
      rw [← Option.some.inj (hn.symm.trans hnb)]
      exact hown _ (hpw' a b ha1 hb1 ha2 hb2 hab m hm)
  obtain ⟨s, hsF, hag⟩ := seg_full g ec hseg sel lo hi hlo0 hlohi hhi hsG
  refine ⟨s i, (hsF.1.1 i hi0 hic).2, fun j hj1 hj2 nj' hnj' => ?_⟩
  obtain ⟨nj, hnj, _, _, hdrop⟩ := hnode _ nj' hnj'
  have hjs : s j = sel j := hag j hj1 hj2
  have hij : i ≠ j := by omega
  have hnjs : g.node? (s j) = some nj := by rw [hjs]; exact hnj
  have hin : s i ∈ nj.owners := hsF.2 i j hi0 (by omega) hic (by omega) hij nj hnjs
  if hkeep : s i ∈ nj'.owners then exact hkeep else
  exfalso
  obtain ⟨ny, nq, hny, hnq, hbad⟩ := hdrop _ hin hkeep
  rw [hny] at hnj; cases hnj
  have hback : sel j ∈ nq.owners := by
    rw [← hjs]; exact hsF.2 j i (by omega) hi0 (by omega) hic (fun h => hij h.symm) nq hnq
  have h1 := shares_of_full g ec.self s hsF j i (by omega) (by omega) hi0 hic nj nq hnjs hnq
  have h2 := shares_of_full g ec.self s hsF i j hi0 hic (by omega) (by omega) nq nj hnq hnjs
  rcases hbad with hb | hb | hb
  · exact hb hback
  · rw [h1] at hb; exact Bool.noConfusion hb
  · rw [h2] at hb; exact Bool.noConfusion hb

/-- info: 'AbsSat.GraphPath.Model.SegReview.seg_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seg_full

/-- info: 'AbsSat.GraphPath.Model.SegReview.segGood_of_badDrops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segGood_of_badDrops

-- ============================================================
-- `aggPair` solo hace pérdidas malas
-- ============================================================

open AbsSat.GraphPath.Model.AggressiveReview (aggPair dropList dropOwnerPair)

/-- Cortar con `dropList os w` solo quita `w`. -/
theorem mem_drop_keep (a os : List PathNodeId) (w q : PathNodeId) (hqa : q ∈ a) (hqo : q ∈ os)
    (hne : q ≠ w) : q ∈ intersectOwners a (dropList os w) := by
  refine List.mem_filter.mpr ⟨hqa, ?_⟩
  have hin : q ∈ dropList os w :=
    List.mem_append_left _ (List.mem_filter.mpr ⟨hqo, bne_iff_ne.mpr hne⟩)
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.elem_iff]
  exact Or.inr hin

theorem mem_of_intersect (a b : List PathNodeId) (q : PathNodeId) (h : q ∈ intersectOwners a b) :
    q ∈ a := (List.mem_filter.mp h).1

/-- **Lo que `aggPair` quita es siempre un par malo**, y no toca padres. -/
theorem aggPair_drops (g : GPathM) (x w : PathNodeId) (y : PathNodeId) (n' : PNodeM)
    (h : (aggPair g x w).node? y = some n') :
    ∃ n, g.node? y = some n ∧ (∀ p ∈ n'.parents, p ∈ n.parents) ∧
      (∀ q ∈ n'.owners, q ∈ n.owners) ∧ (∀ q ∈ n.owners, q ∉ n'.owners → BadPair g y q) := by
  have trivialCase : g.node? y = some n' → ∃ n, g.node? y = some n ∧
      (∀ p ∈ n'.parents, p ∈ n.parents) ∧ (∀ q ∈ n'.owners, q ∈ n.owners) ∧
      (∀ q ∈ n.owners, q ∉ n'.owners → BadPair g y q) :=
    fun hy => ⟨n', hy, fun _ hp => hp, fun _ hq => hq, fun _ hq hnq => absurd hq hnq⟩
  have hf : ∀ (B : List PathNodeId) (n : PNodeM), (uniMap B n).id = n.id :=
    fun _ _ => rfl
  unfold aggPair at h
  cases hx : g.node? x with
  | none => rw [hx] at h; exact trivialCase h
  | some nx =>
    cases hw : g.node? w with
    | none => rw [hx, hw] at h; exact trivialCase h
    | some nw =>
      rw [hx, hw] at h
      simp only at h
      split at h
      · next hcond =>
        -- asimétrico: `x` pierde `w`
        have hxw : x ∉ nw.owners := by
          intro hm
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hcond
          have hc : nw.owners.contains x = true := List.elem_iff.mpr hm
          rw [hc] at hcond
          exact Bool.noConfusion hcond.2
        obtain ⟨n, hn, heq⟩ := Reader.updateAt_node?_inv g x _ (hf _) y n' h
        refine ⟨n, hn, ?_, ?_, ?_⟩ <;> cases hb : n.id == x <;> simp only [hb] at heq <;>
          subst heq
        · exact fun _ hp => hp
        · exact fun _ hp => hp
        · exact fun _ hq => hq
        · exact fun q hq => mem_of_intersect _ _ q hq
        · exact fun q hq hnq => absurd hq hnq
        · intro q hq hnq
          have hyx : y = x := by rw [← node?_id_eq g y n hn]; exact eq_of_beq hb
          subst hyx
          rw [hx] at hn; cases hn
          have hqw : q = w := by
            if hqw : q = w then exact hqw else
            exact absurd (mem_drop_keep _ _ w q hq hq hqw) hnq
          subst hqw
          exact ⟨nx, nw, hx, hw, Or.inl hxw⟩
      · split at h
        · next _ hcond =>
          -- sin cruce: `x` pierde `w` y `w` pierde `x`
          have hsh : sharesEveryStep g.current_step nx.owners nw.owners = false := by
            simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hcond
            exact hcond.2
          unfold dropOwnerPair at h
          obtain ⟨n1, hn1, heq2⟩ := Reader.updateAt_node?_inv _ w _ (hf _) y n' h
          obtain ⟨n, hn, heq1⟩ := Reader.updateAt_node?_inv g x _ (hf _) y n1 hn1
          have hid : n.id = y := node?_id_eq g y n hn
          have h1sub : ∀ q ∈ n1.owners, q ∈ n.owners := by
            cases hb : n.id == x <;> simp only [hb] at heq1 <;> subst heq1
            · exact fun _ hq => hq
            · exact fun q hq => mem_of_intersect _ _ q hq
          have h1id : n1.id = n.id := by
            cases hb : n.id == x <;> simp only [hb] at heq1 <;> subst heq1 <;> rfl
          have h2sub : ∀ q ∈ n'.owners, q ∈ n1.owners := by
            cases hb : n1.id == w <;> simp only [hb] at heq2 <;> subst heq2
            · exact fun _ hq => hq
            · exact fun q hq => mem_of_intersect _ _ q hq
          have h2par : n'.parents = n1.parents := by
            cases hb : n1.id == w <;> simp only [hb] at heq2 <;> subst heq2 <;> rfl
          have h1par : n1.parents = n.parents := by
            cases hb : n.id == x <;> simp only [hb] at heq1 <;> subst heq1 <;> rfl
          refine ⟨n, hn, fun p hp => by rw [← h1par, ← h2par]; exact hp,
            fun q hq => h1sub q (h2sub q hq), fun q hq hnq => ?_⟩
          if hq1 : q ∈ n1.owners then
            -- la pérdida es de la segunda mitad: `y = w` y `q = x`
            have hbw : (n1.id == w) = true := by
              cases hb : n1.id == w
              · simp only [hb] at heq2; subst heq2; exact absurd hq1 hnq
              · rfl
            have hyw : y = w := by rw [← hid, ← h1id]; exact eq_of_beq hbw
            subst hyw
            rw [hw] at hn; cases hn
            simp only [hbw] at heq2; subst heq2
            have hqx : q = x := by
              if hqx : q = x then exact hqx else
              exact absurd (mem_drop_keep _ _ x q hq1 hq hqx) hnq
            subst hqx
            exact ⟨nw, nx, hw, hx, Or.inr (Or.inr hsh)⟩
          else
            -- la pérdida es de la primera mitad: `y = x` y `q = w`
            have hbx : (n.id == x) = true := by
              cases hb : n.id == x
              · simp only [hb] at heq1; subst heq1; exact absurd hq hq1
              · rfl
            have hyx : y = x := by rw [← hid]; exact eq_of_beq hbx
            subst hyx
            rw [hx] at hn; cases hn
            simp only [hbx] at heq1; subst heq1
            have hqw : q = w := by
              if hqw : q = w then exact hqw else
              exact absurd (mem_drop_keep _ _ w q hq hq hqw) hq1
            subst hqw
            exact ⟨nx, nw, hx, hw, Or.inr (Or.inl hsh)⟩
        · exact trivialCase h

/-- **Un par del barrido conserva `SegGood`**, con las hipótesis locales de extensión. -/
theorem segGood_aggPair (g : GPathM) (ec : ExtCtx g) (hseg : SegGood g) (x w : PathNodeId) :
    SegGood (aggPair g x w) := by
  have hstep : (aggPair g x w).current_step = g.current_step := by
    unfold aggPair
    split
    · split
      · rfl
      · split
        · rfl
        · rfl
    · rfl
  exact segGood_of_badDrops g _ ec hseg hstep (aggPair_drops g x w)

/-- info: 'AbsSat.GraphPath.Model.SegReview.aggPair_drops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms aggPair_drops

/-- info: 'AbsSat.GraphPath.Model.SegReview.segGood_aggPair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segGood_aggPair

/-- **Borrar un nodo conserva `SegGood`**: no toca ninguna tabla, solo enlaces. -/
theorem segGood_removeNode (g : GPathM) (hnd : NodupIds g) (hseg : SegGood g) (x : PathNodeId) :
    SegGood (removeNode g x) := by
  have back : ∀ y n', (removeNode g x).node? y = some n' → ∃ n, g.node? y = some n ∧
      (∀ p ∈ n'.parents, p ∈ n.parents) ∧ n'.owners = n.owners := by
    intro y n' h
    have hmem : n' ∈ (removeNode g x).nodes := List.mem_of_find?_eq_some h
    rw [removeNode_nodes] at hmem
    obtain ⟨n0, hn0, heq⟩ := List.mem_map.mp hmem
    have hid : n'.id = y := node?_id_eq _ y n' h
    have h0id : n0.id = y := by rw [← hid, ← heq]; rfl
    refine ⟨n0, by rw [← h0id]; exact node?_of_mem hnd n0 (List.mem_filter.mp hn0).1, ?_, ?_⟩
    · intro p hp; rw [← heq] at hp; exact (List.mem_filter.mp hp).1
    · rw [← heq]; rfl
  intro sel lo hi hlo0 hlohi hhi hch' hpw' i hi0 hic hout
  have hcs : (removeNode g x).current_step = g.current_step := rfl
  rw [hcs] at hhi hic
  have hsG : Seg g sel lo hi := by
    refine ⟨⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_⟩, fun a b ha1 hb1 ha2 hb2 hab nb hnb => ?_⟩
    · obtain ⟨hs, hjs⟩ := hch'.1 j hj1 hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _⟩ := back _ m hm
      exact ⟨by rw [hn]; rfl, hjs⟩
    · obtain ⟨hs, _⟩ := hch'.1 (j + 1) (by omega) hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, hpar, _⟩ := back _ m hm
      have hl := hch'.2 j hj1 hj2
      rw [hm] at hl
      rw [hn]
      simp only [Option.map_some, Option.getD_some] at hl ⊢
      exact hpar _ hl
    · obtain ⟨hs, _⟩ := hch'.1 b hb1 hb2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _, hown⟩ := back _ m hm
      rw [← Option.some.inj (hn.symm.trans hnb), ← hown]
      exact hpw' a b ha1 hb1 ha2 hb2 hab m hm
  obtain ⟨r, hrs, hrall⟩ := hseg sel lo hi hlo0 hlohi hhi hsG.1 hsG.2 i hi0 hic hout
  refine ⟨r, hrs, fun j hj1 hj2 nj' hnj' => ?_⟩
  obtain ⟨n, hn, _, hown⟩ := back _ nj' hnj'
  rw [hown]; exact hrall j hj1 hj2 n hn

/-- info: 'AbsSat.GraphPath.Model.SegReview.segGood_removeNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segGood_removeNode

end AbsSat.GraphPath.Model.SegReview
