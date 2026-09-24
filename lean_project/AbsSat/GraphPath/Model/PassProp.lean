-- lean_project/AbsSat/GraphPath/Model/PassProp.lean
import AbsSat.GraphPath.Model.ReadyInv

/-!
# Propagación por la pasada de padres (hacia `PinFirstRound`)

`row-degree doomtrace` enseña que los tramos que la limpieza de un pin deja sin entrada común mueren
cuando la pasada de padres —que sube paso a paso— llega a su miembro más bajo: para entonces las tablas
de sus padres ya no cubren al tramo. Aquí, la parte de esa propagación que no es de tipo Helly:

> **`DownCov`**: tras la pasada de padres, si los padres de `y` tienen alguna entrada en el paso de una
> entrada `r` de la tabla de `y` (por debajo de `y`), entonces **uno** de esos padres tiene a `r`.

El corte de `y` lo establece al procesar `y` (`downCov_self`), y los pasos posteriores no lo rompen
(`downCov_other`): procesan nodos de paso `≥` el de `y`, así que ni la entrada `r` ni el padre que la
cubre —que están por debajo— son el procesado, y el espejo y el desenlace solo le quitan el procesado a
los demás.
-/

namespace AbsSat.GraphPath.Model.PassProp

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Bridge (LinksInOwners)

-- ============================================================
-- Lo que `reviewNode x` hace a los padres de otro nodo
-- ============================================================

/-- Un nodo del grafo tras borrar `x` viene de uno de antes, desenlazado de `x`. -/
theorem removeNode_node?_eq (G : GPathM) (x y : PathNodeId) (n' : PNodeM)
    (h : (removeNode G x).node? y = some n') : ∃ n, G.node? y = some n ∧ n' = unlink x n := by
  cases hG : G.node? y with
  | some n =>
    have hne : y ≠ x := SegReview.removeNode_ne G x y n' h
    rw [removeNode_node? G x y n hG hne] at h
    exact ⟨n, rfl, (Option.some.inj h).symm⟩
  | none =>
    exfalso
    have hm := List.mem_of_find?_eq_some h
    rw [removeNode_nodes] at hm
    obtain ⟨n0, hn0, heq⟩ := List.mem_map.mp hm
    have hid : n0.id = y := by rw [← node?_id_eq _ y n' h, ← heq]; rfl
    have := node?_isSome_of_mem G n0 (List.mem_filter.mp hn0).1
    rw [hid, hG] at this
    exact Bool.noConfusion this

/-- **Los padres de un nodo distinto de `x` solo pueden perder a `x`** en `reviewNode x`. -/
theorem reviewNode_parents_keep (g : GPathM) (nb : PNodeM → List PathNodeId) (x y : PathNodeId)
    (hyx : y ≠ x) (n' : PNodeM) (h : (reviewNode g nb x).node? y = some n') :
    ∃ n, g.node? y = some n ∧ ∀ p ∈ n.parents, p ≠ x → p ∈ n'.parents := by
  unfold reviewNode at h
  cases hd : g.node? x with
  | none => rw [hd] at h; exact ⟨n', h, fun _ hp _ => hp⟩
  | some d =>
    rw [hd] at h
    simp only at h
    let B := unionOwnersOf g (nb d)
    let G1 := updateAt g x (fun n => { n with owners := intersectOwners n.owners B })
    let G2 := mirrorDrop G1 x (cutRemoved d B)
    let c : PNodeM := { d with owners := intersectOwners d.owners B }
    have hdid : d.id = x := node?_id_eq g x d hd
    have hc : G2.node? x = some c := by
      show (mirrorDrop (updateAt g x (fun n => { n with owners := intersectOwners n.owners B }))
        x (cutRemoved d B)).node? x = _
      rw [mirrorDrop_node? _ x _ x c (by
          rw [updateAt_node? g x (fun n => { n with owners := intersectOwners n.owners B })
            (fun _ => rfl) x d hd, show (d.id == x) = true from beq_iff_eq.mpr hdid]),
        SegReview.mirrorMap_self_cut_eq x d B hdid]
    -- the node of `y` in `unlinkIncompatible G2 x`, and its parents
    have mid : ∀ n3, (unlinkIncompatible G2 x).node? y = some n3 →
        ∃ n, g.node? y = some n ∧ ∀ p ∈ n.parents, p ≠ x → p ∈ n3.parents := by
      intro n3 h3
      cases hm : G2.node? y with
      | none =>
        exfalso
        have hmem := List.mem_of_find?_eq_some h3
        have hshape : (unlinkIncompatible G2 x).nodes = G2.nodes.map (unlinkMap c x) := by
          simp only [GPathM.unlinkIncompatible, hc]
        rw [hshape] at hmem
        obtain ⟨m0, hm0, heq⟩ := List.mem_map.mp hmem
        have hid : m0.id = y := by rw [← node?_id_eq _ y n3 h3, ← heq, unlinkMap_id]
        have := node?_isSome_of_mem G2 m0 hm0
        rw [hid, hm] at this
        exact Bool.noConfusion this
      | some m =>
        rw [unlinkIncompatible_node? G2 x c hc y m hm] at h3
        obtain rfl := Option.some.inj h3
        obtain ⟨m1, hm1, hmeq⟩ := mirrorDrop_node?_inv G1 x _ y m hm
        obtain ⟨m0, hm0, hm1eq⟩ := Reader.updateAt_node?_inv g x
          (fun n => { n with owners := intersectOwners n.owners B }) (fun _ => rfl) y m1 hm1
        have hm0id : m0.id = y := node?_id_eq g y m0 hm0
        have hb0 : (m0.id == x) = false := by rw [hm0id]; exact beq_false_of_ne hyx
        rw [hm1eq, hb0] at hmeq
        refine ⟨m0, hm0, fun p hp hpx => ?_⟩
        have hmid : m.id ≠ x := by rw [hmeq, mirrorMap_id, hm0id]; exact hyx
        exact PinAliveChain.parents_unlinkMap_keeps c x m hmid p
          (by rw [hmeq, mirrorMap_parents]; exact hp) hpx
    split at h
    · split at h
      · exact mid n' h
      · obtain ⟨n3, h3, rfl⟩ := removeNode_node?_eq _ x y n' h
        obtain ⟨n, hn, hkeep⟩ := mid n3 h3
        exact ⟨n, hn, fun p hp hpx => List.mem_filter.mpr ⟨hkeep p hp hpx, bne_iff_ne.mpr hpx⟩⟩
    · obtain ⟨n, hn, rfl⟩ := removeNode_node?_eq g x y n' h
      exact ⟨n, hn, fun p hp hpx => List.mem_filter.mpr ⟨hp, bne_iff_ne.mpr hpx⟩⟩

-- ============================================================
-- La cobertura hacia abajo
-- ============================================================

/-- **`y` está cubierto hacia abajo**: si sus padres tienen alguna entrada en el paso de una entrada
`r` de su tabla por debajo de él, uno de ellos tiene a `r`. -/
def DownCov (g : GPathM) (y : PathNodeId) : Prop :=
  ∀ ny, g.node? y = some ny → ∀ r ∈ ny.owners, r.id.step < y.id.step →
    hasStepEntry (unionOwnersOf g ny.parents) r.id.step = true →
    ∃ p ∈ ny.parents, ∃ np, g.node? p = some np ∧ r ∈ np.owners

/-- La unión de tablas solo encoge al estrechar el grafo y la lista. -/
theorem hasStepEntry_union_mono {g g' : GPathM} (hpr : Pruned g g') (hnd : NodupIds g)
    (L L' : List PathNodeId) (hL : ∀ p ∈ L', p ∈ L) (k : Int)
    (h : hasStepEntry (unionOwnersOf g' L') k = true) : hasStepEntry (unionOwnersOf g L) k = true := by
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp h
  obtain ⟨p, hp, np', hnp', hqp⟩ := FabricAdd.exists_owner_of_mem_unionOwnersOf g' L' q hq
  obtain ⟨np, hnp, hsub⟩ := SymInvariant.node_back hpr hnd p np' hnp'
  exact List.any_eq_true.mpr ⟨q, mem_unionOwnersOf g L p np q (hL p hp) hnp (hsub q hqp), hqs⟩

/-- **Los pasos posteriores no rompen la cobertura**: `reviewNode x` con `x` en un paso `≥` el de `y`. -/
theorem downCov_other (g : GPathM) (hnd : NodupIds g) (hpb : Parents.PBelow g)
    (nb : PNodeM → List PathNodeId) (x y : PathNodeId) (hyx : y ≠ x)
    (hstep : y.id.step ≤ x.id.step) (h : DownCov g y) : DownCov (reviewNode g nb x) y := by
  have hpr := pruned_reviewNode nb x g
  intro ny' hny' r hr hrs hent
  obtain ⟨ny, hny, hkeep⟩ := reviewNode_parents_keep g nb x y hyx ny' hny'
  obtain ⟨ny0, hny0, hsub⟩ := SymInvariant.node_back hpr hnd y ny' hny'
  rw [hny] at hny0; cases hny0
  obtain ⟨n0, hn0, hid0, _, hpar0⟩ := hpr.nodes_derived ny' (List.mem_of_find?_eq_some hny')
  have hent0 := hasStepEntry_union_mono hpr hnd ny.parents ny'.parents
    (fun p hp => by
      have := hpar0 p hp
      have hn0' : g.node? y = some n0 := by
        rw [← node?_id_eq _ y ny' hny', hid0]; exact node?_of_mem hnd n0 hn0
      rw [hny] at hn0'; cases hn0'; exact this) _ hent
  obtain ⟨p, hp, np, hnp, hrp⟩ := h ny hny r (hsub r hr) hrs hent0
  have hpstep : p.id.step = y.id.step - 1 := by
    rw [← node?_id_eq g y ny hny]; exact hpb ny (List.mem_of_find?_eq_some hny) p hp
  have hpx : p ≠ x := fun he => by rw [he] at hpstep; omega
  have hrx : r ≠ x := fun he => by rw [he] at hrs; omega
  refine ⟨p, hkeep p hp hpx, ?_⟩
  obtain ⟨np', hnp'⟩ := Option.isSome_iff_exists.mp
    (PassCtx.survives_reviewNode g nb x p (by rw [hnp]; rfl) hpx)
  obtain ⟨n1, hn1, hne1, _⟩ := SegReview.reviewNode_owners g hnd nb x p np' hnp'
  rw [hnp] at hn1; cases hn1
  exact ⟨np', hnp', (hne1 hpx).2.1 r hrp hrx⟩

/-- **El corte de `x` lo cubre**: tras `reviewNode x` con los padres como vecinos, `x` está cubierto
hacia abajo. Pide que los enlaces estén en las tablas y que cada nodo se posea. -/
theorem downCov_self (g : GPathM) (hnd : NodupIds g) (hpb : Parents.PBelow g)
    (hlinks : LinksInOwners g) (hself : PassCtx.SelfL g) (x : PathNodeId) :
    DownCov (reviewNode g (·.parents) x) x := by
  have hpr := pruned_reviewNode (·.parents) x g
  intro nx' hnx' r hr hrs hent
  cases hd : g.node? x with
  | none =>
    have hR : reviewNode g (·.parents) x = g := by unfold reviewNode; rw [hd]
    rw [hR, hd] at hnx'; cases hnx'
  | some d =>
    have hk : ((reviewNode g (·.parents) x).node? x).isSome = true := by rw [hnx']; rfl
    have hform := PassCtx.node_after g (·.parents) x d hd hk x d hd
    rw [if_pos rfl, PinAliveChain.unlinkMap_self
      { d with owners := intersectOwners d.owners (unionOwnersOf g d.parents) } x
      (node?_id_eq g x d hd), hnx'] at hform
    obtain rfl := Option.some.inj hform
    -- the union of the parents' tables, before the cut, has an entry at `r`'s step
    let B := unionOwnersOf g d.parents
    have hentB : hasStepEntry B r.id.step = true :=
      hasStepEntry_union_mono hpr hnd d.parents _ (fun p hp => (List.mem_filter.mp hp).1) _ hent
    have hrB : r ∈ B := by
      have hc := (List.mem_filter.mp hr).2
      rw [hentB, Bool.not_true, Bool.false_or] at hc
      exact List.contains_iff_mem.mp hc
    obtain ⟨p, hp, np, hnp, hrp⟩ := FabricAdd.exists_owner_of_mem_unionOwnersOf g d.parents r hrB
    have hpd : p ∈ d.owners := (hlinks x d hd).1 p hp
    have hpB : p ∈ B := mem_unionOwnersOf g d.parents p np p hp hnp (hself p np hnp)
    have hpcut : p ∈ intersectOwners d.owners B := mem_intersectOwners_of_mem _ _ p hpd hpB
    have hpstep : p.id.step = x.id.step - 1 := by
      rw [← node?_id_eq g x d hd]; exact hpb d (List.mem_of_find?_eq_some hd) p hp
    have hpx : p ≠ x := fun he => by rw [he] at hpstep; omega
    have hrx : r ≠ x := fun he => by rw [he] at hrs; omega
    refine ⟨p, List.mem_filter.mpr ⟨hp, List.contains_iff_mem.mpr hpcut⟩, ?_⟩
    obtain ⟨np', hnp'⟩ := Option.isSome_iff_exists.mp
      (PassCtx.survives_reviewNode g (·.parents) x p (by rw [hnp]; rfl) hpx)
    obtain ⟨n1, hn1, hne1, _⟩ := SegReview.reviewNode_owners g hnd (·.parents) x p np' hnp'
    rw [hnp] at hn1; cases hn1
    exact ⟨np', hnp', (hne1 hpx).2.1 r hrp hrx⟩

/-- info: 'AbsSat.GraphPath.Model.PassProp.downCov_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms downCov_self

-- ============================================================
-- La pasada de padres entera
-- ============================================================

/-- Lo que la pasada arrastra para la cobertura. -/
structure PCtx (g : GPathM) : Prop where
  nd : NodupIds g
  links : LinksInOwners g
  self : PassCtx.SelfL g
  pb : Parents.PBelow g
  sh : SymInvariant.ShapeOk g

theorem PCtx.reviewNode {g : GPathM} (h : PCtx g) (nb : PNodeM → List PathNodeId) (x : PathNodeId) :
    PCtx (reviewNode g nb x) :=
  ⟨List.Nodup.sublist (NodeIds.ids_reviewNode g nb x) h.nd, ReadyInv.links_reviewNode g h.nd h.links nb x,
    PassCtx.selfL_reviewNode g h.nd h.sh.oos h.sh.snn h.sh.below h.self nb x,
    Parents.PBelow_of_pruned (pruned_reviewNode nb x g) h.pb, h.sh.of_pruned (pruned_reviewNode nb x g)⟩

/-- **Una línea de la pasada**: si los nodos de pasos anteriores están cubiertos, tras la línea también
lo están los de su paso. -/
theorem downCov_fold (a : Int) :
    ∀ (R : List PathNodeId) (g : GPathM), PCtx g → (∀ x ∈ R, x.id.step = a) →
      (∀ y, 1 ≤ y.id.step → y.id.step ≤ a → y ∉ R → DownCov g y) →
      PCtx (R.foldl (fun g id => reviewNode g (·.parents) id) g) ∧
        ∀ y, 1 ≤ y.id.step → y.id.step ≤ a →
          DownCov (R.foldl (fun g id => reviewNode g (·.parents) id) g) y := by
  intro R
  induction R with
  | nil => intro g hc _ hJ; exact ⟨hc, fun y h1 h2 => hJ y h1 h2 List.not_mem_nil⟩
  | cons x R ih =>
    intro g hc hR hJ
    have hxa := hR x List.mem_cons_self
    refine ih _ (hc.reviewNode _ x) (fun z hz => hR z (List.mem_cons_of_mem _ hz)) ?_
    intro y h1 h2 hyR
    if hyx : y = x then
      subst hyx
      exact downCov_self g hc.nd hc.pb hc.links hc.self y
    else
      exact downCov_other g hc.nd hc.pb _ x y hyx (by rw [hxa]; exact h2)
        (hJ y h1 h2 (fun hm => by
          rcases List.mem_cons.mp hm with he | he
          · exact hyx he
          · exact hyR he))

theorem downCov_reviewLine (g : GPathM) (a : Int) (hc : PCtx g)
    (hH : ∀ y, 1 ≤ y.id.step → y.id.step < a → DownCov g y) :
    PCtx (reviewLine g (·.parents) a) ∧
      ∀ y, 1 ≤ y.id.step → y.id.step < a + 1 → DownCov (reviewLine g (·.parents) a) y := by
  have hL : ∀ x ∈ (g.line a).map (·.id), x.id.step = a := fun x hx => by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    exact eq_of_beq (List.mem_filter.mp hn).2
  obtain ⟨hc', hcov⟩ := downCov_fold a _ g hc hL (fun y h1 h2 hyR => by
    rcases Int.lt_or_le y.id.step a with hlt | hge
    · exact hH y h1 hlt
    · intro ny hny
      exact absurd (mem_line_of_node? g y ny hny a (by omega)) hyR)
  exact ⟨hc', fun y h1 h2 => hcov y h1 (by omega)⟩

theorem intRange_cons (a b : Int) (h : a ≤ b) : intRange a b = a :: intRange (a + 1) b := by
  unfold intRange
  have hn : (b - a + 1).toNat = (b - (a + 1) + 1).toNat + 1 := by omega
  rw [hn, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Function.comp_def]
  congr 1
  · show a + ((0 : Nat) : Int) = a; simp
  · refine List.map_congr_left (fun i _ => ?_)
    show a + ((i + 1 : Nat) : Int) = a + 1 + (i : Int)
    push_cast; omega

theorem intRange_nil (a b : Int) (h : b < a) : intRange a b = [] := by
  unfold intRange
  have hn : (b - a + 1).toNat = 0 := by omega
  rw [hn]; rfl

/-- **Tras la pasada de padres, todo nodo está cubierto hacia abajo**, si el resultado es válido. -/
theorem downCov_reviewParents (g : GPathM) (hc : PCtx g) (hv : isValid (reviewParents g) = true) :
    ∀ y, 1 ≤ y.id.step → DownCov (reviewParents g) y := by
  have main : ∀ (n : Nat) (a : Int) (g' : GPathM), (g.current_step - 1 - a + 1).toNat = n →
      PCtx g' → g'.current_step = g.current_step →
      (∀ y, 1 ≤ y.id.step → y.id.step < a → DownCov g' y) →
      isValid (reviewSteps g' (·.parents) (intRange a (g.current_step - 1))) = true →
      ∀ y, 1 ≤ y.id.step → DownCov (reviewSteps g' (·.parents) (intRange a (g.current_step - 1))) y := by
    intro n
    induction n with
    | zero =>
      intro a g' hn hc' hcs hH _ y h1
      rw [intRange_nil a _ (by omega)]
      show DownCov g' y
      intro ny hny
      have := hc'.sh.below ny (List.mem_of_find?_eq_some hny)
      rw [node?_id_eq g' y ny hny] at this
      exact hH y h1 (by omega) ny hny
    | succ n ih =>
      intro a g' hn hc' hcs hH hv' y h1
      rw [intRange_cons a _ (by omega)] at hv' ⊢
      unfold reviewSteps at hv' ⊢
      split
      · next hg =>
        rw [if_pos hg] at hv'
        obtain ⟨hcL, hHL⟩ := downCov_reviewLine g' a hc' hH
        exact ih (a + 1) _ (by omega) hcL (by rw [(pruned_reviewLine _ a g').step_eq]; exact hcs)
          hHL hv' y h1
      · next hg =>
        rw [if_neg hg] at hv'
        exact absurd hv' hg
  exact main _ 1 g rfl hc rfl (fun y h1 h2 => absurd h2 (by omega)) hv

/-- info: 'AbsSat.GraphPath.Model.PassProp.downCov_reviewParents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms downCov_reviewParents

-- ============================================================
-- La iteración hacia abajo: cada entrada de abajo, por un camino de padres
-- ============================================================

/-- **`r` se alcanza desde `y` bajando por padres que tienen a `r` en su tabla**, hasta un nodo del
que `r` es padre. -/
inductive Desc (P : GPathM) (r : PathNodeId) : PathNodeId → Prop
  | base (y : PathNodeId) (ny : PNodeM) : P.node? y = some ny → r ∈ ny.parents → Desc P r y
  | step (y : PathNodeId) (ny : PNodeM) (p : PathNodeId) (np : PNodeM) : P.node? y = some ny →
      p ∈ ny.parents → P.node? p = some np → r ∈ np.owners → Desc P r p → Desc P r y

/-- Lo que el estado tras la pasada de padres tiene (medido en la primera vuelta de los pines del
lector, `row-degree doomtrace`: 86 de 86): nodos válidos, `I1`, y la forma. -/
structure AfterPar (P : GPathM) : Prop where
  cov : ∀ y, 1 ≤ y.id.step → DownCov P y
  valid : ∀ n ∈ P.nodes, isValidNode P n = true
  i1 : PassCtx.I1L P
  plive : PassCtx.PLive P
  nr : Parents.NotRoot P
  pb : Parents.PBelow P
  sh : SymInvariant.ShapeOk P
  nd : NodupIds P

/-- **Un paso hacia abajo**: una entrada de la tabla de `y`, por debajo de `y`, está en la tabla de
un padre de `y` (los padres válidos tienen entrada en todo paso, así que `DownCov` se aplica). -/
theorem parent_owning (P : GPathM) (h : AfterPar P) (y : PathNodeId) (ny : PNodeM)
    (hny : P.node? y = some ny) (r : PathNodeId) (hr : r ∈ ny.owners) (hr0 : 0 ≤ r.id.step)
    (hrs : r.id.step < y.id.step) : ∃ p ∈ ny.parents, ∃ np, P.node? p = some np ∧ r ∈ np.owners := by
  have hm := List.mem_of_find?_eq_some hny
  have hid := node?_id_eq P y ny hny
  have hbelow := h.sh.below ny hm
  rw [hid] at hbelow
  have hroot : ny.id.parent_id.isNone = false := by
    cases hp : ny.id.parent_id with
    | none => exact absurd hp (h.nr ny hm (by rw [hid]; omega))
    | some _ => rfl
  obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil _
    (SelfOwn.have_parents_of_isValidNode P ny (h.valid ny hm) hroot)
  obtain ⟨np0, hnp0⟩ := Option.isSome_iff_exists.mp (h.plive y ny hny p0 hp0)
  have hok := owners_ok_of_isValidNode _ _ (h.valid np0 (List.mem_of_find?_eq_some hnp0))
  have hk := List.all_eq_true.mp hok r.id.step (mem_intRange hr0 (by omega))
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp hk
  have hent : hasStepEntry (unionOwnersOf P ny.parents) r.id.step = true :=
    List.any_eq_true.mpr ⟨q, mem_unionOwnersOf P ny.parents p0 np0 q hp0 hnp0 hq, hqs⟩
  exact h.cov y (by omega) ny hny r hr hrs hent

/-- **Toda entrada viva por debajo de `y` se alcanza bajando por padres que la tienen.** -/
theorem desc_of_owner (P : GPathM) (h : AfterPar P) :
    ∀ (n : Nat) (y : PathNodeId) (ny : PNodeM) (r : PathNodeId), (y.id.step - r.id.step).toNat = n + 1 →
      P.node? y = some ny → r ∈ ny.owners → 0 ≤ r.id.step → (P.node? r).isSome → Desc P r y := by
  intro n
  induction n with
  | zero =>
    intro y ny r hn hny hr hr0 hrl
    exact Desc.base y ny hny (h.i1 y ny hny r hr hrl (by omega))
  | succ n ih =>
    intro y ny r hn hny hr hr0 hrl
    obtain ⟨p, hp, np, hnp, hrp⟩ := parent_owning P h y ny hny r hr hr0 (by omega)
    have hps : p.id.step = y.id.step - 1 := by
      rw [← node?_id_eq P y ny hny]; exact h.pb ny (List.mem_of_find?_eq_some hny) p hp
    exact Desc.step y ny p np hny hp hnp hrp (ih p np r (by omega) hnp hrp hr0 hrl)

/-- info: 'AbsSat.GraphPath.Model.PassProp.desc_of_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms desc_of_owner

-- ============================================================
-- El hueco, con nombre: de la unión a un padre común
-- ============================================================

/-- **De la unión a un padre común** (la parte de tipo Helly): si cada miembro de un tramo por encima
de su miembro más bajo está en la tabla de **algún** padre de ese miembro, **un solo** padre los tiene
a todos.

**FALSA en general** (medido con `row-degree doomtrace`, tras la pasada de padres de la primera vuelta
de los pines del lector): 1 fallo en 14.579 tramos (semilla 1, #0: tramo de los pasos 6–13). Es un tramo
**condenado** —sin entrada común en los pasos 2–5 y 14–18— que **sobrevive a la pasada de padres**
porque cada miembro está en la tabla de algún padre del extremo, sin que ninguno los tenga a todos, y
que muere después, en la pasada de hijos. Así que la muerte de los condenados no se puede atribuir a
la pasada de padres sola: el argumento tiene que combinar las dos pasadas. Queda como registro de la
ruta, con su consecuencia local (`seg_down_of_common`). -/
def UnionToCommon (P : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), lo ≤ hi → TopGoodUp.Seg P sel lo hi →
    ∀ nl, P.node? (sel lo) = some nl →
    (∀ j, lo < j → j ≤ hi → ∃ p ∈ nl.parents, ∃ np, P.node? p = some np ∧ sel j ∈ np.owners) →
    ∃ p ∈ nl.parents, ∃ np, P.node? p = some np ∧ ∀ j, lo < j → j ≤ hi → sel j ∈ np.owners

/-- **Con un padre común, el tramo baja un paso**: con la simetría y los enlaces en la tabla, ese
padre alarga el tramo. -/
theorem seg_down_of_common (P : GPathM) (hsym : Threaded.OwnSymmetric P) (hlinks : LinksInOwners P)
    (hpb : Parents.PBelow P)
    (sel : Int → PathNodeId) (lo hi : Int) (hlohi : lo ≤ hi) (hs : TopGoodUp.Seg P sel lo hi)
    (nl : PNodeM) (hnl : P.node? (sel lo) = some nl) (p : PathNodeId) (hp : p ∈ nl.parents)
    (np : PNodeM) (hnp : P.node? p = some np) (hall : ∀ j, lo < j → j ≤ hi → sel j ∈ np.owners) :
    TopGoodUp.Seg P (Extendable.upd sel (lo - 1) p) (lo - 1) hi := by
  have hlos : (sel lo).id.step = lo := (hs.1.1 lo (Int.le_refl _) hlohi).2
  have hps : p.id.step = lo - 1 := by
    rw [← hlos, ← node?_id_eq P _ nl hnl]; exact hpb nl (List.mem_of_find?_eq_some hnl) p hp
  have hpl : p ∈ nl.owners := (hlinks _ nl hnl).1 p hp
  have hback : ∀ j, lo ≤ j → j ≤ hi → sel j ∈ np.owners := by
    intro j hj1 hj2
    rcases Int.lt_or_le lo j with hlt | hle
    · exact hall j hlt hj2
    · have hj : j = lo := by omega
      subst hj
      exact hsym (sel j) nl p np hnl hnp hpl
  refine SegReview.seg_extend P sel lo hi hlohi hs p np hnp hps
    (fun nl' hnl' => by rw [← Option.some.inj (hnl.symm.trans hnl')]; exact hp) ?_ hback
  intro j hj1 hj2 nj hnj
  exact hsym p np (sel j) nj hnp hnj (hback j hj1 hj2)

/-- info: 'AbsSat.GraphPath.Model.PassProp.seg_down_of_common' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seg_down_of_common

end AbsSat.GraphPath.Model.PassProp
