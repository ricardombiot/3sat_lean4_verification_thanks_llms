-- lean/improves_bin/AbsSatBin/GraphPath/Model/SymMachine.lean
import AbsSatBin.GraphPath.Model.PairInactive
import AbsSatBin.GraphPath.Model.PinChainBin

/-!
# Every valid state of the bin machine has symmetric tables, and the reader's two reviews agree

`PairInactive.reviewAgg_eq_review` needs `RevOk` (ids without repeats, the table shape, and
`OwnSymmetric`) on the state the review starts from. This module proves it on every state the bin
machine builds and the reader visits.

* **`CutClosed`**: every table entry at a step the global list covers is a global owner. It holds at
  every valid review fixpoint (`cutClosed_review`: the fixpoint is a fixpoint of the cut), and `addNode`
  and `join` keep it.
* **The join keeps symmetry** (`sym_join`). An entry `q` of a merged table comes from one side; there
  `CutClosed` and `GN` make `q` a live node of that side, symmetry puts the other node in `q`'s table,
  and the merge keeps it.
* **`symInv_reachable`**: a valid reachable state is `OwnSymmetric` and `CutClosed`.
* **The reader**: every valid state it visits is symmetric (`sym_readFirst`), so along the reader the
  aggressive review is the review (`start_agg_eq`, `pin_agg_eq`).
-/

namespace AbsSatBin.GraphPath.Model.SymMachine

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Threaded (OwnSymmetric)
open AbsSatBin.GraphPath.Model.AggressiveReview
open AbsSatBin.GraphPath.Model.PairInactive
open AbsSatBin.GraphPath.Model.Reader (RCtx)

-- ============================================================
-- The cut is closed at the review's fixpoint
-- ============================================================

/-- Every table entry at a step the global list covers is a global owner. -/
def CutClosed (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, ∀ q ∈ n.owners, hasStepEntry g.gowners q.id.step = true → q ∈ g.gowners

/-- **A valid review fixpoint is closed under the cut.** -/
theorem cutClosed_review (X : GPathM) (hv : isValid (review X) = true) : CutClosed (review X) := by
  have hfix := reviewPass_review X hv
  have h₁ := measure_cleanPair_le (review X)
  have h₂ := measure_reviewParents_le (cleanPair (review X))
  have h₃ := measure_reviewSons_le (reviewParents (cleanPair (review X)))
  have hm : measure (reviewPass (review X)) = measure (review X) := by rw [hfix]
  simp only [reviewPass] at hm
  have hcp := cleanPair_eq_self (review X) (by omega)
  have hc := CleanTwoPhase.owners_in_gowners_cleanInvalid₂ (review X)
  rw [hcp.1] at hc
  exact hc

theorem below_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step) (hb : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) :
    ∀ n ∈ (addNode g d title forb).nodes, n.id.id.step < (addNode g d title forb).current_step := by
  intro n hn
  rw [addNode_current]
  rw [addNode_nodes] at hn
  rcases List.mem_append.mp hn with h | h
  · obtain ⟨n0, hn0, rfl⟩ := List.mem_map.mp h
    rw [upMap_id]
    have := hb n0 hn0
    omega
  · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title forb _).mp h
    rw [rowNode_id, mapId_of_mem_newRowIds g d forb pid hpid, hd]
    omega

/-- **`addNode` keeps the cut closed**: old entries sit below the new step, where the global list is
the old one; new entries are row ids, which are global owners. -/
theorem cutClosed_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step) (hownb : SelfOwn.OwnBelow g) (hc : CutClosed g) :
    CutClosed (addNode g d title forb) := by
  intro n hn q hq hs
  rw [addNode_gowners] at hs ⊢
  rw [addNode_nodes] at hn
  rcases List.mem_append.mp hn with h | h
  · obtain ⟨n0, hn0, rfl⟩ := List.mem_map.mp h
    rw [upMap_owners] at hq
    rcases List.mem_append.mp hq with hq0 | hq1
    · have hlt := hownb n0 hn0 q hq0
      have hs0 : hasStepEntry g.gowners q.id.step = true := by
        obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp hs
        rcases List.mem_append.mp hr with hr0 | hr1
        · exact List.any_eq_true.mpr ⟨r, hr0, hrs⟩
        · exfalso
          have hrd := mapId_of_mem_newRowIds g d forb r hr1
          have hrs' : r.id.step = q.id.step := eq_of_beq hrs
          rw [hrd, hd] at hrs'
          omega
      exact List.mem_append_left _ (hc n0 hn0 q hq0 hs0)
    · exact List.mem_append_right _ (List.mem_filter.mp hq1).1
  · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title forb _).mp h
    rw [rowNode_owners] at hq
    unfold rowOwners at hq
    rcases List.mem_append.mp hq with h1 | h1
    · exact List.mem_append_left _ (List.contains_iff_mem.mp (List.mem_filter.mp h1).2)
    · rw [List.mem_singleton.mp h1]
      exact List.mem_append_right _ hpid

-- ============================================================
-- The join
-- ============================================================

theorem okJoin_parts {g₁ g₂ : GPathM} (hok : okJoin g₁ g₂ = true) :
    g₁.current_step = g₂.current_step ∧ isValid g₁ = true ∧ isValid g₂ = true := by
  simp only [okJoin, Bool.and_eq_true] at hok
  exact ⟨eq_of_beq hok.1.1.1, hok.1.2, hok.2⟩

/-- A live node of a valid state lies in `[0, current_step)`. -/
theorem node_bounds (g : GPathM) (c : RCtx g) (x : PathNodeId) (h : (g.node? x).isSome = true) :
    0 ≤ x.id.step ∧ x.id.step < g.current_step := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h
  have hm := List.mem_of_find?_eq_some hn
  have hid : n.id = x := node?_id_eq g x n hn
  rw [← hid]
  exact ⟨c.snn n hm, c.below n hm⟩

/-- **An entry at a covered step is a live node**, in a valid state closed under the cut. -/
theorem live_of_owner (g : GPathM) (hv : isValid g = true) (c : RCtx g) (k : CutClosed g)
    (n : PNodeM) (hn : n ∈ g.nodes) (q : PathNodeId) (hq : q ∈ n.owners)
    (h0 : 0 ≤ q.id.step) (h1 : q.id.step < g.current_step) : ∃ nq, g.node? q = some nq := by
  have hq' := k n hn q hq (hasStepEntry_of_isValid g hv _ h0 h1)
  obtain ⟨m, hm, hmid⟩ := c.gn q hq'
  exact ⟨m, by rw [← hmid]; exact node?_of_mem c.nodup m hm⟩

theorem join_bounds (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (c₁ : RCtx g₁) (c₂ : RCtx g₂)
    (x : PathNodeId) (m : PNodeM) (h : (join g₁ g₂).node? x = some m) :
    0 ≤ x.id.step ∧ x.id.step < g₁.current_step := by
  have hcs := (okJoin_parts hok).1
  rcases join_node?_source g₁ g₂ x m h with h1 | h2
  · exact node_bounds g₁ c₁ x h1
  · rw [hcs]; exact node_bounds g₂ c₂ x h2

/-- **The join keeps symmetry.** -/
theorem sym_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (c₁ : RCtx g₁) (c₂ : RCtx g₂)
    (s₁ : OwnSymmetric g₁) (s₂ : OwnSymmetric g₂) (k₁ : CutClosed g₁) (k₂ : CutClosed g₂) :
    OwnSymmetric (join g₁ g₂) := by
  obtain ⟨hcs, hv₁, hv₂⟩ := okJoin_parts hok
  intro p n q m hp hq hqn
  obtain ⟨hs0, hs1⟩ := join_bounds g₁ g₂ hok c₁ c₂ q m hq
  rcases join_owners_source g₁ g₂ p n hp q hqn with ⟨p₁, hp₁, hq₁⟩ | ⟨p₂, hp₂, hq₂⟩
  · obtain ⟨nq, hnq⟩ := live_of_owner g₁ hv₁ c₁ k₁ p₁ (List.mem_of_find?_eq_some hp₁) q hq₁ hs0 hs1
    have hpq := s₁ p p₁ q nq hp₁ hnq hq₁
    obtain ⟨n', hn', hsub, _, _⟩ := (grown_join_left g₁ g₂).node?_grown q nq hnq
    rw [hq] at hn'
    cases hn'
    exact hsub p hpq
  · obtain ⟨nq, hnq⟩ := live_of_owner g₂ hv₂ c₂ k₂ p₂ (List.mem_of_find?_eq_some hp₂) q hq₂ hs0
      (by rw [← hcs]; exact hs1)
    have hpq := s₂ p p₂ q nq hp₂ hnq hq₂
    obtain ⟨n', hn', hsub, _, _⟩ := (grown_join_right g₁ g₂ hok).node?_grown q nq hnq
    rw [hq] at hn'
    cases hn'
    exact hsub p hpq

/-- **The join keeps the cut closed.** -/
theorem cutClosed_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (c₁ : RCtx g₁) (c₂ : RCtx g₂)
    (k₁ : CutClosed g₁) (k₂ : CutClosed g₂) : CutClosed (join g₁ g₂) := by
  obtain ⟨hcs, hv₁, hv₂⟩ := okJoin_parts hok
  intro n hn q hq hs
  -- the step is covered, so it lies in [0, current_step)
  obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp hs
  have hrq : r.id.step = q.id.step := eq_of_beq hrs
  have hb : 0 ≤ q.id.step ∧ q.id.step < g₁.current_step := by
    rw [← hrq]
    rw [GownersNodes.join_gowners, List.mem_append] at hr
    rcases hr with hr | hr
    · obtain ⟨m, hm, hmid⟩ := c₁.gn r hr
      rw [← hmid]; exact ⟨c₁.snn m hm, c₁.below m hm⟩
    · obtain ⟨m, hm, hmid⟩ := c₂.gn r (List.mem_filter.mp hr).1
      rw [← hmid, hcs]; exact ⟨c₂.snn m hm, c₂.below m hm⟩
  have hnd := Reader.nodup_join g₁ g₂ c₁.nodup c₂.nodup
  have hnx : (join g₁ g₂).node? n.id = some n := node?_of_mem hnd n hn
  rcases join_owners_source g₁ g₂ n.id n hnx q hq with ⟨p₁, hp₁, hq₁⟩ | ⟨p₂, hp₂, hq₂⟩
  · exact (grown_join_left g₁ g₂).gowners_grown q
      (k₁ p₁ (List.mem_of_find?_eq_some hp₁) q hq₁ (hasStepEntry_of_isValid g₁ hv₁ _ hb.1 hb.2))
  · exact (grown_join_right g₁ g₂ hok).gowners_grown q
      (k₂ p₂ (List.mem_of_find?_eq_some hp₂) q hq₂
        (hasStepEntry_of_isValid g₂ hv₂ _ hb.1 (by rw [← hcs]; exact hb.2)))

-- ============================================================
-- Every valid reachable state
-- ============================================================

theorem foldl_filterRequire_nodes :
    ∀ (reqs : List NodeId) (g : GPathM), (reqs.foldl filterRequire g).nodes = g.nodes := by
  intro reqs
  induction reqs with
  | nil => intro g; rfl
  | cons r rs ih => intro g; exact ih (filterRequire g r)

theorem sym_foldl_filterRequire (reqs : List NodeId) (g : GPathM) (h : OwnSymmetric g) :
    OwnSymmetric (reqs.foldl filterRequire g) := by
  have hn : ∀ x, (reqs.foldl filterRequire g).node? x = g.node? x := by
    intro x; simp only [node?, foldl_filterRequire_nodes]
  intro p n q m hp hq hqn
  rw [hn] at hp hq
  exact h p n q m hp hq hqn

/-- **`RevOk` of a filtered state**, from the reader's context and symmetry. -/
theorem revOk_foldl (g : GPathM) (c : RCtx g) (s : OwnSymmetric g) (reqs : List NodeId) :
    RevOk (reqs.foldl filterRequire g) := by
  have cX : RCtx (reqs.foldl filterRequire g) :=
    ReaderAgg.RCtx_of_keeps (ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire reqs g) c
  exact ⟨cX.nodup, ⟨cX.oos, cX.snn, cX.below⟩, sym_foldl_filterRequire reqs g s⟩

section
variable (reqOf : NodeId → List NodeId) (forb : PathNodeId → Bool)

/-- **Every valid state the machine builds has symmetric tables and a closed cut.** -/
theorem symInv_reachable (g : GPathM) (h : Reachable reqOf forb g) :
    isValid g = true → OwnSymmetric g ∧ CutClosed g := by
  induction h with
  | seed d title hstep _ =>
    intro _
    have he : initSeed d title = addNode empty d title noForb := by
      simp only [initSeed, up, skipsWindow_noForb, Bool.false_eq_true, if_false]
      rfl
    rw [he]
    have hd : d.step = empty.current_step := hstep
    refine ⟨Reader.OwnSymmetric_addNode empty d title noForb hd (fun _ h => by cases h)
      (fun _ h => by cases h) (fun _ _ _ _ h => by cases h), ?_⟩
    exact cutClosed_addNode empty d title noForb hd (fun _ h => by cases h) (fun _ h => by cases h)
  | up g d title hstep _ _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    have hnd := Reader.NodupIds_reachable reqOf forb g hr
    have cg := Reader.RCtx_reachable reqOf forb g hnd hr
    show isValid (up (filterAll g (reqOf d)) d title forb) = true →
      OwnSymmetric (up (filterAll g (reqOf d)) d title forb) ∧
        CutClosed (up (filterAll g (reqOf d)) d title forb)
    by_cases hvF : isValid (filterAll g (reqOf d)) = true
    · have hvg : isValid g = true := Certifies.isValid_of_pruned hpr hvF
      obtain ⟨sg, _⟩ := ih hvg
      have hsF : OwnSymmetric (filterAll g (reqOf d)) :=
        OwnSymmetric_review _ (revOk_foldl g cg sg (reqOf d)) hvF
      have ccF : CutClosed (filterAll g (reqOf d)) := cutClosed_review _ hvF
      have cF := Reader.RCtx_filterAll g cg (reqOf d)
      have hdF : d.step = (filterAll g (reqOf d)).current_step := by rw [hpr.step_eq]; exact hstep
      have hsA := Reader.OwnSymmetric_addNode _ d title forb hdF cF.below cF.ownb hsF
      simp only [up, hvF, if_true]
      split
      · intro hv'
        have hmok := MachineOk_of_pruned hpr (Certifies.MachineOk_reachable reqOf forb g hr)
        have rA : RevOk (addNode (filterAll g (reqOf d)) d title forb) :=
          ⟨Reader.nodup_addNode _ d title forb cF.nodup cF.below hdF,
            ⟨SelfOwn.OOS_addNode _ d title forb hdF cF.below cF.gn cF.oos,
             SelfOwn.SNN_addNode _ d title forb hdF hmok cF.snn,
             below_addNode _ d title forb hdF cF.below⟩, hsA⟩
        exact ⟨OwnSymmetric_review _ rA hv', cutClosed_review _ hv'⟩
      · intro _
        exact ⟨hsA, cutClosed_addNode _ d title forb hdF cF.ownb ccF⟩
    · intro hv
      simp only [up, hvF, Bool.false_eq_true, if_false] at hv
  | join g₁ g₂ hok h₁ h₂ ih₁ ih₂ =>
    intro _
    obtain ⟨_, hv₁, hv₂⟩ := okJoin_parts hok
    have c₁ := Reader.RCtx_reachable reqOf forb g₁ (Reader.NodupIds_reachable reqOf forb g₁ h₁) h₁
    have c₂ := Reader.RCtx_reachable reqOf forb g₂ (Reader.NodupIds_reachable reqOf forb g₂ h₂) h₂
    obtain ⟨s₁, k₁⟩ := ih₁ hv₁
    obtain ⟨s₂, k₂⟩ := ih₂ hv₂
    exact ⟨sym_join g₁ g₂ hok c₁ c₂ s₁ s₂ k₁ k₂, cutClosed_join g₁ g₂ hok c₁ c₂ k₁ k₂⟩

end

-- ============================================================
-- Along the reader, the aggressive review is the review
-- ============================================================

open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PinChainBin

variable (φ : Cnf)

theorem machine_ctx (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ) :
    RCtx kv.2 ∧ OwnSymmetric kv.2 := by
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hok := Decision.stateOk_pureRun φ hzero kv hkv
  have hreach := MapReachable.reachable_of_mapReachable φ hbd kv.2 hok.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  exact ⟨Reader.RCtx_reachable (reqOf φ) (isProhibited φ) kv.2 hnd hreach,
    (symInv_reachable (reqOf φ) (isProhibited φ) kv.2 hreach hok.valid).1⟩

/-- **The reader starts from the same state with either review.** -/
theorem start_agg_eq (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ) :
    filterAllAgg kv.2 [] = filterAll kv.2 [] := by
  obtain ⟨c, s⟩ := machine_ctx φ hbd kv hkv
  exact filterAllAgg_eq_filterAll _ _ (revOk_foldl kv.2 c s [])

/-- **Every valid state the reader visits is symmetric.** -/
theorem sym_readFirst (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ) :
    ∀ g, ReadFirst (filterAll kv.2 []) g → isValid g = true → OwnSymmetric g := by
  obtain ⟨c, s⟩ := machine_ctx φ hbd kv hkv
  have b₀ := binCtx_start φ hbd kv hkv
  intro g hF
  induction hF with
  | start => exact fun hv => OwnSymmetric_review _ (revOk_foldl kv.2 c s []) hv
  | pin g k q hF hv _ _ hv' ih =>
    intro _
    have cg := (binCtx_readFirst φ _ b₀ g hF).rctx
    exact OwnSymmetric_review _ (revOk_foldl g cg (ih hv) [q.id]) hv'

/-- **Every pin of the reader gives the same state with either review.** -/
theorem pin_agg_eq (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (g : GPathM) (hF : ReadFirst (filterAll kv.2 []) g) (hv : isValid g = true) (reqs : List NodeId) :
    filterAllAgg g reqs = filterAll g reqs := by
  have b₀ := binCtx_start φ hbd kv hkv
  have cg := (binCtx_readFirst φ _ b₀ g hF).rctx
  exact filterAllAgg_eq_filterAll _ _ (revOk_foldl g cg (sym_readFirst φ hbd kv hkv g hF hv) reqs)

/-- info: 'AbsSatBin.GraphPath.Model.SymMachine.symInv_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms symInv_reachable

/-- info: 'AbsSatBin.GraphPath.Model.SymMachine.pin_agg_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pin_agg_eq

end AbsSatBin.GraphPath.Model.SymMachine
