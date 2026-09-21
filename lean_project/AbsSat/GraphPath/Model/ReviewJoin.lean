-- lean_project/AbsSat/GraphPath/Model/ReviewJoin.lean
import AbsSat.GraphPath.Model.SendDistrib
import AbsSat.GraphPath.Model.DescentUp

/-!
# The two equations reduce to one: the review of a join

`SendDistrib` asks a whole send to distribute over a join. A send is four operations — weak filter,
pins, aggressive review, up — and three of them are no obstacle:

* **the weak filter and the pins commute with the join on the nose** (`filterWeakAll_join`,
  `foldl_filterRequire_join`): they only filter global owners, and the join's global owners are a
  union;
* **up distributes** (`embedded_addNode_join`): the up of a join sits inside the join of the ups —
  both sides add the same new node, keyed by the same map parent.

So everything is carried by the review. One statement is left, about the review alone:

* **`ReviewJoin`** — pinning and reviewing the join of two states of a line gives a state inside the
  join of the reviewed sides that stay valid (and one of them does).

From it: `sendDistrib_of_reviewJoin`, `reviewDistrib_of_reviewJoin`, and the verdict
`sat_of_reviewJoin`.
-/

namespace AbsSat.GraphPath.Model.ReviewJoin

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv MInv_join)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF okJoin_of_stateOkF)
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.BranchRun
open AbsSat.GraphPath.Model.BranchLines
open AbsSat.GraphPath.Model.SendDistrib

variable (φ : Cnf)

-- ============================================================
-- The filters commute with the join
-- ============================================================

theorem filter_union (p : PathNodeId → Bool) (A B : List PathNodeId) :
    (A ++ B.filter (fun q => !A.contains q)).filter p =
      A.filter p ++ (B.filter p).filter (fun q => !(A.filter p).contains q) := by
  rw [List.filter_append, List.filter_filter, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro q _
  cases hq : p q
  · simp
  · have hc : (A.filter p).contains q = A.contains q := by
      simp [List.mem_filter, hq]
    rw [hc]
    simp

theorem filterWeak_join (e h : GPathM) (w : Int × List NodeId) :
    filterWeak (join e h) w = join (filterWeak e w) (filterWeak h w) := by
  simp only [filterWeak, join, node?]
  rw [filter_union]

theorem filterRequire_join (e h : GPathM) (r : NodeId) :
    filterRequire (join e h) r = join (filterRequire e r) (filterRequire h r) := by
  simp only [filterRequire, join, node?]
  rw [filter_union]

theorem filterWeakAll_join (ws : List (Int × List NodeId)) :
    ∀ e h, filterWeakAll (join e h) ws = join (filterWeakAll e ws) (filterWeakAll h ws) := by
  induction ws with
  | nil => intro e h; rfl
  | cons w rest ih =>
    intro e h
    show filterWeakAll (filterWeak (join e h) w) rest = _
    rw [filterWeak_join]
    exact ih _ _

theorem foldl_filterRequire_join (rq : List NodeId) :
    ∀ e h, rq.foldl filterRequire (join e h) = join (rq.foldl filterRequire e) (rq.foldl filterRequire h) := by
  induction rq with
  | nil => intro e h; rfl
  | cons r rest ih =>
    intro e h
    show rest.foldl filterRequire (filterRequire (join e h) r) = _
    rw [filterRequire_join]
    exact ih _ _

-- ============================================================
-- Up distributes over the join
-- ============================================================

theorem isValid_addNode (g : GPathM) (d : NodeId) (t : String) (hv : isValid g = true)
    (hd : d.step = g.current_step) (hgn : GownersNodes.GN g) :
    isValid (addNode g d t) = true := by
  have hv' := hv
  simp only [isValid, List.all_eq_true] at hv ⊢
  intro k hk
  rw [addNode_current] at hk
  have h0 := mem_intRange_lower hk
  have h1 := mem_intRange_upper hk
  rw [addNode_gowners]
  simp only [hasStepEntry, List.any_append]
  by_cases hlt : k < g.current_step
  · have := hv k (mem_intRange h0 (by omega))
    simp only [hasStepEntry] at this
    rw [this, Bool.true_or]
  · -- above the old steps, the row carries the entry: it is non-empty because the
    -- state was valid at its own top step
    rw [Bool.or_eq_true]
    refine Or.inr (List.any_eq_true.mpr ?_)
    by_cases hpos : 0 < g.current_step
    · have hent := hasStepEntry_of_isValid g hv' (g.current_step - 1) (by omega) (by omega)
      simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
      obtain ⟨q, hq, hqs⟩ := hent
      obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp
        ((GownersNodes.hasNode_iff g q).mp (hgn q hq))
      have hqp : q ∈ newParents g := by
        simp only [newParents, if_pos hpos]
        exact mem_line_of_node? g q nq hnq _ hqs
      refine ⟨shiftPid q d, mem_newRowIds_of_mem_newParents g d q hpos hqp, ?_⟩
      show (d.step == k) = true
      exact beq_iff_eq.mpr (by omega)
    · refine ⟨{ id := d, parent_id := none, gparent_id := none },
        by rw [newRowIds_of_zero g d hpos]; exact List.mem_cons_self, ?_⟩
      show (d.step == k) = true
      exact beq_iff_eq.mpr (by omega)

theorem below_join (A B : GPathM) (hcs : A.current_step = B.current_step) (hnd : NodupIds (join A B))
    (hbA : ∀ n ∈ A.nodes, n.id.id.step < A.current_step) (hbB : ∀ n ∈ B.nodes, n.id.id.step < B.current_step) :
    ∀ n ∈ (join A B).nodes, n.id.id.step < (join A B).current_step := by
  intro n hn
  have hJ : (join A B).node? n.id = some n := node?_of_mem hnd n hn
  have hcsJ : (join A B).current_step = A.current_step := rfl
  rw [hcsJ]
  rcases join_node?_source A B n.id n hJ with hA | hB
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hA
    have := hbA m (List.mem_of_find?_eq_some hm)
    rw [node?_id_eq A n.id m hm] at this
    exact this
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hB
    have := hbB m (List.mem_of_find?_eq_some hm)
    rw [node?_id_eq B n.id m hm] at this
    rw [hcs]; exact this

/-- **Up distributes over the join**: the up of a join sits inside the join of the ups.

With the row this needs two things the single new node did not. A row node's
table is what its *parents* own, cut to the global owners — so an entry the
joined state gives it has to be one a side already gave the row node there. It
is, provided each side's owner tables stay inside its own global owners
(`hogA`, `hogB`) and its global owners are nodes (`hgnA`, `hgnB`). Without them
the join could hand a row node an owner neither side's row node has. The side
conditions are exactly what the `∩ gowners` of `create_node_from_parents!`
introduced. -/
theorem embedded_addNode_join (A B : GPathM) (d : NodeId) (t : String)
    (hcs : A.current_step = B.current_step) (_hmp : A.map_parent = B.map_parent)
    (hd : d.step = A.current_step) (hndA : NodupIds A) (hndB : NodupIds B)
    (hbA : ∀ n ∈ A.nodes, n.id.id.step < A.current_step)
    (hbB : ∀ n ∈ B.nodes, n.id.id.step < B.current_step)
    (hpos : 0 < A.current_step)
    (hogA : ∀ p n, A.node? p = some n → ∀ q ∈ n.owners, q ∈ A.gowners)
    (hogB : ∀ p n, B.node? p = some n → ∀ q ∈ n.owners, q ∈ B.gowners)
    (hgnA : GownersNodes.GN A) (hgnB : GownersNodes.GN B) :
    Embedded (addNode (join A B) d t) (join (addNode A d t) (addNode B d t)) := by
  have hposB : 0 < B.current_step := by rw [← hcs]; exact hpos
  have hndJ : NodupIds (join A B) := Reader.nodup_join A B hndA hndB
  have hcsJ : (join A B).current_step = A.current_step := rfl
  have hgL := grown_join_left (addNode A d t) (addNode B d t)
  -- the two sides' top lines make up the join's
  have hparJ : ∀ q ∈ newParents (join A B), q ∈ newParents A ∨ q ∈ newParents B := by
    intro q hq
    unfold newParents at hq ⊢
    rw [hcsJ, if_pos hpos] at hq
    rw [if_pos hpos, if_pos hposB]
    obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hq
    have hxJ : (join A B).node? q = some x := by
      rw [← hxid]; exact node?_of_mem hndJ x (List.mem_filter.mp hx).1
    have hxs : q.id.step = A.current_step - 1 := by
      rw [← hxid]; exact eq_of_beq (List.mem_filter.mp hx).2
    rcases join_node?_source A B q x hxJ with hA | hB
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hA
      exact Or.inl (mem_line_of_node? A q y hy _ hxs)
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hB
      exact Or.inr (mem_line_of_node? B q y hy _ (by rw [hxs, hcs]))
  have hrpJ : ∀ z q, q ∈ rowParents (join A B) d z →
      q ∈ rowParents A d z ∨ q ∈ rowParents B d z := by
    intro z q hq
    rcases hparJ q (rowParents_subset (join A B) d z q hq) with h | h
    · exact Or.inl (List.mem_filter.mpr ⟨h, (List.mem_filter.mp hq).2⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨h, (List.mem_filter.mp hq).2⟩)
  have hrowJ : ∀ z ∈ newRowIds (join A B) d, z ∈ newRowIds A d ∨ z ∈ newRowIds B d := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ :=
      exists_shift_of_mem_newRowIds (join A B) d z (by rw [hcsJ]; exact hpos) hz
    rcases hparJ r hr with h | h
    · exact Or.inl (mem_newRowIds_of_mem_newParents A d r hpos h)
    · exact Or.inr (mem_newRowIds_of_mem_newParents B d r hposB h)
  -- a parent of a row node on one side is one on the other, when it is a node there
  have hstepOf : ∀ (g : GPathM), 0 < g.current_step → ∀ z q, q ∈ rowParents g d z →
      q.id.step = g.current_step - 1 := by
    intro g hg z q hq
    have := rowParents_subset g d z q hq
    unfold newParents at this
    rw [if_pos hg] at this
    obtain ⟨x, hx, hxid⟩ := List.mem_map.mp this
    rw [← hxid]; exact eq_of_beq (List.mem_filter.mp hx).2
  -- the join's row table is covered by the two sides' row tables
  have hrownJ : ∀ z w, w ∈ rowOwners (join A B) d z →
      w ∈ rowOwners A d z ∨ w ∈ rowOwners B d z := by
    intro z w hw
    rcases (mem_rowOwners_iff (join A B) d z w).mp hw with ⟨hin, _⟩ | rfl
    · obtain ⟨r, hr, nr, hnr, hwr⟩ := exists_owner_of_mem_unionOwnersOf (join A B) _ w hin
      have hrs : r.id.step = A.current_step - 1 := hstepOf (join A B) (by rw [hcsJ]; exact hpos) z r hr
      have hshift := shiftPid_of_mem_rowParents (join A B) d z r hr
      rcases join_owners_source A B r nr hnr w hwr with ⟨nA, hnA, hwA⟩ | ⟨nB, hnB, hwB⟩
      · have hrA : r ∈ rowParents A d z := by
          refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hshift⟩
          unfold newParents; rw [if_pos hpos]
          exact mem_line_of_node? A r nA hnA _ hrs
        exact Or.inl ((mem_rowOwners_iff A d z w).mpr
          (Or.inl ⟨mem_unionOwnersOf A _ r nA w hrA hnA hwA, hogA r nA hnA w hwA⟩))
      · have hrB : r ∈ rowParents B d z := by
          refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hshift⟩
          unfold newParents; rw [if_pos hposB]
          exact mem_line_of_node? B r nB hnB _ (by rw [hrs, hcs])
        exact Or.inr ((mem_rowOwners_iff B d z w).mpr
          (Or.inl ⟨mem_unionOwnersOf B _ r nB w hrB hnB hwB, hogB r nB hnB w hwB⟩))
    · exact Or.inl (self_mem_rowOwners A d w)
  -- the target's node at a row identifier
  have hrowNode : ∀ z ∈ newRowIds (join A B) d,
      ∃ n', (join (addNode A d t) (addNode B d t)).node? z = some n' ∧
        (∀ w ∈ rowOwners A d z, w ∈ n'.owners) ∧ (∀ w ∈ rowOwners B d z, w ∈ n'.owners) ∧
        (∀ w ∈ rowParents A d z, w ∈ n'.parents) ∧ (∀ w ∈ rowParents B d z, w ∈ n'.parents) := by
    intro z hz
    by_cases hzA : z ∈ newRowIds A d
    · obtain ⟨n', hn', ho, hpa, _⟩ := hgL.node?_grown z _ (addNode_node?_new A d t hd hbA z hzA)
      refine ⟨n', hn', fun w hw => ho w (by rw [rowNode_owners]; exact hw), ?_,
        fun w hw => hpa w (by rw [rowNode_parents]; exact hw), ?_⟩
      · by_cases hzB : z ∈ newRowIds B d
        · obtain ⟨n'', hn'', ho', _, _⟩ := join_node?_right (addNode A d t) (addNode B d t) z _
            (addNode_node?_new B d t (by rw [← hcs]; exact hd) hbB z hzB)
          rw [Option.some_inj.mp (hn''.symm.trans hn')] at ho'
          exact fun w hw => ho' w (by rw [rowNode_owners]; exact hw)
        · intro w hw
          rw [rowOwners_of_not_mem B d z hposB hzB, List.mem_singleton] at hw
          rw [hw]
          exact ho z (by rw [rowNode_owners]; exact self_mem_rowOwners A d z)
      · by_cases hzB : z ∈ newRowIds B d
        · obtain ⟨n'', hn'', _, hpa', _⟩ := join_node?_right (addNode A d t) (addNode B d t) z _
            (addNode_node?_new B d t (by rw [← hcs]; exact hd) hbB z hzB)
          rw [Option.some_inj.mp (hn''.symm.trans hn')] at hpa'
          exact fun w hw => hpa' w (by rw [rowNode_parents]; exact hw)
        · intro w hw
          rw [rowParents_of_not_mem B d z hposB hzB] at hw
          exact absurd hw List.not_mem_nil
    · have hzB : z ∈ newRowIds B d := (hrowJ z hz).resolve_left hzA
      obtain ⟨n', hn', ho, hpa, _⟩ := join_node?_right (addNode A d t) (addNode B d t) z _
        (addNode_node?_new B d t (by rw [← hcs]; exact hd) hbB z hzB)
      refine ⟨n', hn', ?_, fun w hw => ho w (by rw [rowNode_owners]; exact hw), ?_,
        fun w hw => hpa w (by rw [rowNode_parents]; exact hw)⟩
      · intro w hw
        rw [rowOwners_of_not_mem A d z hpos hzA, List.mem_singleton] at hw
        rw [hw]
        exact ho z (by rw [rowNode_owners]; exact self_mem_rowOwners B d z)
      · intro w hw
        rw [rowParents_of_not_mem A d z hpos hzA] at hw
        exact absurd hw List.not_mem_nil
  -- the target's node at an old identifier, from either side
  have fromA : ∀ p nA, A.node? p = some nA →
      ∃ n', (join (addNode A d t) (addNode B d t)).node? p = some n' ∧
        (∀ q ∈ nA.owners, q ∈ n'.owners) ∧ (∀ q ∈ gainedOwners A d nA, q ∈ n'.owners) ∧
        (∀ q ∈ nA.parents, q ∈ n'.parents) := by
    intro p nA hA
    obtain ⟨n', hn', ho, hpa, _⟩ := hgL.node?_grown p _ (addNode_node?_old A d t p nA hA)
    exact ⟨n', hn', fun q hq => ho q (by rw [upMap_owners]; exact List.mem_append_left _ hq),
      fun q hq => ho q (by rw [upMap_owners]; exact List.mem_append_right _ hq),
      fun q hq => hpa q (by rw [upMap_parents]; exact hq)⟩
  have fromB : ∀ p nB, B.node? p = some nB →
      ∃ n', (join (addNode A d t) (addNode B d t)).node? p = some n' ∧
        (∀ q ∈ nB.owners, q ∈ n'.owners) ∧ (∀ q ∈ gainedOwners B d nB, q ∈ n'.owners) ∧
        (∀ q ∈ nB.parents, q ∈ n'.parents) := by
    intro p nB hB
    obtain ⟨n', hn', ho, hpa, _⟩ := join_node?_right (addNode A d t) (addNode B d t) p _
      (addNode_node?_old B d t p nB hB)
    exact ⟨n', hn', fun q hq => ho q (by rw [upMap_owners]; exact List.mem_append_left _ hq),
      fun q hq => ho q (by rw [upMap_owners]; exact List.mem_append_right _ hq),
      fun q hq => hpa q (by rw [upMap_parents]; exact hq)⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [addNode_current]; rfl
  · intro p hp
    rw [addNode_gowners] at hp
    show p ∈ (addNode A d t).gowners ++ (addNode B d t).gowners.filter
      (fun q => !(addNode A d t).gowners.contains q)
    have hinA : p ∈ (addNode A d t).gowners → p ∈ (addNode A d t).gowners ++
        (addNode B d t).gowners.filter (fun q => !(addNode A d t).gowners.contains q) :=
      fun h => List.mem_append_left _ h
    have hinB : p ∈ (addNode B d t).gowners → p ∈ (addNode A d t).gowners ++
        (addNode B d t).gowners.filter (fun q => !(addNode A d t).gowners.contains q) := by
      intro h
      cases hc : (addNode A d t).gowners.contains p with
      | true => exact List.mem_append_left _ (List.mem_of_elem_eq_true hc)
      | false => exact List.mem_append_right _ (List.mem_filter.mpr ⟨h, by rw [hc]; rfl⟩)
    rcases List.mem_append.mp hp with hp | hp
    · change p ∈ A.gowners ++ B.gowners.filter (fun q => !A.gowners.contains q) at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hinA (by rw [addNode_gowners]; exact List.mem_append_left _ hp)
      · exact hinB (by
          rw [addNode_gowners]
          exact List.mem_append_left _ (List.mem_filter.mp hp).1)
    · rcases hrowJ p hp with h | h
      · exact hinA (by rw [addNode_gowners]; exact List.mem_append_right _ h)
      · exact hinB (by rw [addNode_gowners]; exact List.mem_append_right _ h)
  · intro p m hm
    rcases DescentUp.node_addNode_cases (join A B) d t hndJ hm with ⟨hprow, hmeq⟩ | ⟨n0, hn0, hmeq⟩
    · obtain ⟨n', hn', hoA, hoB, hpaA, hpaB⟩ := hrowNode p hprow
      refine ⟨n', hn', fun q hq _ => ?_, fun q hq _ => ?_⟩
      · rw [hmeq, rowNode_owners] at hq
        rcases hrownJ p q hq with h | h
        · exact hoA q h
        · exact hoB q h
      · rw [hmeq, rowNode_parents] at hq
        rcases hrpJ p q hq with h | h
        · exact hpaA q h
        · exact hpaB q h
    · -- an old node
      have hpstep : p.id.step < A.current_step := by
        have hidp := node?_id_eq (join A B) p n0 hn0
        have := below_join A B hcs hndJ hbA hbB n0 (List.mem_of_find?_eq_some hn0)
        rw [hidp] at this; exact this
      -- the target's node at `p`, and both its old table and the row ids that own it
      have hmain : ∃ n', (join (addNode A d t) (addNode B d t)).node? p = some n' ∧
          (∀ q ∈ n0.owners, q ∈ n'.owners) ∧ (∀ q ∈ n0.parents, q ∈ n'.parents) ∧
          (∀ q, q ∈ newRowIds A d → p ∈ rowOwners A d q → q ∈ n'.owners) ∧
          (∀ q, q ∈ newRowIds B d → p ∈ rowOwners B d q → q ∈ n'.owners) := by
        -- fix the target's node once; everything else is `Option.some_inj`
        have hex : ∃ n', (join (addNode A d t) (addNode B d t)).node? p = some n' := by
          rcases join_node?_source A B p n0 hn0 with hA | hB
          · obtain ⟨nA, hnA⟩ := Option.isSome_iff_exists.mp hA
            obtain ⟨n', hn', _, _, _⟩ := fromA p nA hnA
            exact ⟨n', hn'⟩
          · obtain ⟨nB, hnB⟩ := Option.isSome_iff_exists.mp hB
            obtain ⟨n', hn', _, _, _⟩ := fromB p nB hnB
            exact ⟨n', hn'⟩
        obtain ⟨n', hn'⟩ := hex
        refine ⟨n', hn', fun q hq => ?_, fun q hq => ?_, fun q hqr hqo => ?_, fun q hqr hqo => ?_⟩
        · rcases join_owners_source A B p n0 hn0 q hq with ⟨nA, hA', hqA⟩ | ⟨nB, hB', hqB⟩
          · obtain ⟨n'', hn'', ho, _, _⟩ := fromA p nA hA'
            rw [Option.some_inj.mp (hn''.symm.trans hn')] at ho; exact ho q hqA
          · obtain ⟨n'', hn'', ho, _, _⟩ := fromB p nB hB'
            rw [Option.some_inj.mp (hn''.symm.trans hn')] at ho; exact ho q hqB
        · rcases join_parents_source A B p n0 hn0 q hq with ⟨nA, hA', hqA⟩ | ⟨nB, hB', hqB⟩
          · obtain ⟨n'', hn'', _, _, hpa⟩ := fromA p nA hA'
            rw [Option.some_inj.mp (hn''.symm.trans hn')] at hpa; exact hpa q hqA
          · obtain ⟨n'', hn'', _, _, hpa⟩ := fromB p nB hB'
            rw [Option.some_inj.mp (hn''.symm.trans hn')] at hpa; exact hpa q hqB
        · -- `q` owns `p` on the `A` side, so `p` is a node of `A` and gains `q` there
          have hne : p ≠ q := by
            intro hc
            rw [hc, mapId_of_mem_newRowIds A d q hqr, hd] at hpstep
            omega
          have hpg : p ∈ A.gowners := by
            rcases (mem_rowOwners_iff A d q p).mp hqo with ⟨_, hg⟩ | hc
            · exact hg
            · exact absurd hc hne
          obtain ⟨x, hx, hxid⟩ := hgnA p hpg
          have hnA : A.node? p = some x := by rw [← hxid]; exact node?_of_mem hndA x hx
          obtain ⟨n'', hn'', _, hgain, _⟩ := fromA p x hnA
          rw [Option.some_inj.mp (hn''.symm.trans hn')] at hgain
          refine hgain q (List.mem_filter.mpr ⟨hqr, ?_⟩)
          rw [node?_id_eq A p x hnA]
          exact List.elem_eq_true_of_mem hqo
        · have hne : p ≠ q := by
            intro hc
            rw [hc, mapId_of_mem_newRowIds B d q hqr, hd] at hpstep
            omega
          have hpg : p ∈ B.gowners := by
            rcases (mem_rowOwners_iff B d q p).mp hqo with ⟨_, hg⟩ | hc
            · exact hg
            · exact absurd hc hne
          obtain ⟨x, hx, hxid⟩ := hgnB p hpg
          have hnB : B.node? p = some x := by rw [← hxid]; exact node?_of_mem hndB x hx
          obtain ⟨n'', hn'', _, hgain, _⟩ := fromB p x hnB
          rw [Option.some_inj.mp (hn''.symm.trans hn')] at hgain
          refine hgain q (List.mem_filter.mpr ⟨hqr, ?_⟩)
          rw [node?_id_eq B p x hnB]
          exact List.elem_eq_true_of_mem hqo
      obtain ⟨n', hn', hoOld, hpaOld, hgA, hgB⟩ := hmain
      refine ⟨n', hn', fun q hq _ => ?_, fun q hq _ => hpaOld q (by
        rw [hmeq, upMap_parents] at hq; exact hq)⟩
      rw [hmeq, upMap_owners] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hoOld q hq
      · have hqrow : q ∈ newRowIds (join A B) d := gainedOwners_subset (join A B) d n0 q hq
        have hpown : p ∈ rowOwners (join A B) d q := by
          have := (List.mem_filter.mp hq).2
          rw [node?_id_eq (join A B) p n0 hn0] at this
          simpa using this
        rcases hrownJ q p hpown with h | h
        · have hqA : q ∈ newRowIds A d := by
            by_cases hc : q ∈ newRowIds A d
            · exact hc
            · exfalso
              rw [rowOwners_of_not_mem A d q hpos hc, List.mem_singleton] at h
              rw [h, mapId_of_mem_newRowIds (join A B) d q hqrow, hd] at hpstep
              omega
          exact hgA q hqA h
        · have hqB : q ∈ newRowIds B d := by
            by_cases hc : q ∈ newRowIds B d
            · exact hc
            · exfalso
              rw [rowOwners_of_not_mem B d q hposB hc, List.mem_singleton] at h
              rw [h, mapId_of_mem_newRowIds (join A B) d q hqrow, hd] at hpstep
              omega
          exact hgB q hqB h

-- ============================================================
-- The one statement left
-- ============================================================

/-- The pinned state a send reviews. -/
abbrev pinned (g : GPathM) (ws : List (Int × List NodeId)) (rq : List NodeId) : GPathM :=
  rq.foldl filterRequire (filterWeakAll g ws)

/-- **The review of a join.** Pinning and reviewing the join of two states of a line with the same key
gives a state inside the join of the reviewed sides that stay valid, and one of them does. -/
def ReviewJoin : Prop :=
  ∀ (k : Int) (key : NodeId) (e h : GPathM), StateOkF φ k (key, e) → StateOkF φ k (key, h) →
    MInv φ e → MInv φ h → ∀ (ws : List (Int × List NodeId)) (rq : List NodeId),
    isValid (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) = true →
      (isValid (reviewAgg (pinned e ws rq)) = true ∧ isValid (reviewAgg (pinned h ws rq)) = true ∧
          Embedded (reviewAgg (join (pinned e ws rq) (pinned h ws rq)))
            (join (reviewAgg (pinned e ws rq)) (reviewAgg (pinned h ws rq)))) ∨
      (isValid (reviewAgg (pinned e ws rq)) = true ∧
          Embedded (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) (reviewAgg (pinned e ws rq))) ∨
      (isValid (reviewAgg (pinned h ws rq)) = true ∧
          Embedded (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) (reviewAgg (pinned h ws rq)))

theorem reviewDistrib_of_reviewJoin (hRJ : ReviewJoin φ) : ReviewDistrib φ := by
  intro k key e h hse hsh hme hmh hv
  rcases hRJ k key e h hse hsh hme hmh [] [] hv with ⟨hve, _, _⟩ | ⟨hve, _⟩ | ⟨hvh, _⟩
  · exact Or.inl hve
  · exact Or.inl hve
  · exact Or.inr hvh

/-- The facts the up lemmas need, for a reviewed pinned state of a line state. -/
theorem reviewed_facts (k : Int) (key : NodeId) (g : GPathM) (hs : StateOkF φ k (key, g)) (hm : MInv φ g)
    (ws : List (Int × List NodeId)) (rq : List NodeId) :
    (reviewAgg (pinned g ws rq)).current_step = k + 1 ∧
    (reviewAgg (pinned g ws rq)).map_parent = some key ∧
    NodupIds (reviewAgg (pinned g ws rq)) ∧
    (∀ n ∈ (reviewAgg (pinned g ws rq)).nodes, n.id.id.step < (reviewAgg (pinned g ws rq)).current_step) ∧
    Parents.PBelow (reviewAgg (pinned g ws rq)) ∧
    GownersNodes.GN (reviewAgg (pinned g ws rq)) ∧
    SelfOwn.OwnBelow (reviewAgg (pinned g ws rq)) ∧
    SelfOwn.SNN (reviewAgg (pinned g ws rq)) := by
  have hk : ReaderAgg.Keeps g (filterAllAgg (filterWeakAll g ws) rq) :=
    ReaderAgg.Keeps.trans (ReaderAggRun.keeps_filterWeakAll _ _) (ReaderAggRun.keeps_filterAllAgg _ _)
  have hR : ReadableAgg (filterAllAgg (filterWeakAll g ws) rq) :=
    ⟨filterWeakAll g ws, rq, ReaderAgg.RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx, rfl⟩
  have rc := RCtx_of_readableAgg _ hR
  exact ⟨by rw [show reviewAgg (pinned g ws rq) = filterAllAgg (filterWeakAll g ws) rq from rfl,
      hk.1.step_eq, hs.step],
    by rw [show reviewAgg (pinned g ws rq) = filterAllAgg (filterWeakAll g ws) rq from rfl,
      hk.1.map_parent_eq, hs.par],
    rc.nodup, rc.below, rc.shape.pbelow, rc.gn, rc.ownb, rc.snn⟩

/-- **Owner tables inside the global owners**, for the reviewed states a send
works on. With the row `UP` this is what makes "up distributes over join" go
through: a row node inherits only what its parents own *and* what is still
globally alive, so the joined state can only hand it what a side already had.
Measured everywhere on reviewed states and stated here as the explicit side
condition the route now carries. -/
def OwnGowPinned : Prop :=
  ∀ (g : GPathM) (ws : List (Int × List NodeId)) (rq : List NodeId),
    ∀ p n, (reviewAgg (pinned g ws rq)).node? p = some n →
      ∀ q ∈ n.owners, q ∈ (reviewAgg (pinned g ws rq)).gowners

/-- **`SendDistrib` from the review of a join.** -/
theorem sendDistrib_of_reviewJoin (_hwf : WF φ) (hRJ : ReviewJoin φ)
    (hog : OwnGowPinned) : SendDistrib φ := by
  intro k key e h hse hsh hme hmh d hd hv
  let ws := weakReqOfCnf φ d
  let rq := reqOfCnf φ d
  have hok := okJoin_of_stateOkF φ k key e h hse hsh
  have hmJ := MInv_join φ e h hok hme hmh
  have hsJ : StateOkF φ k (key, join e h) := by
    have hjs := ConservationFilter.stateOkF_doJoin φ k key e h hse hsh
    unfold doJoin at hjs
    rw [if_pos hok] at hjs
    exact hjs
  have hX : filterAllAgg (filterWeakAll (join e h) ws) rq = reviewAgg (join (pinned e ws rq) (pinned h ws rq)) := by
    show reviewAgg (rq.foldl filterRequire (filterWeakAll (join e h) ws)) = _
    rw [filterWeakAll_join, foldl_filterRequire_join]
  have hsentJ : sent φ (join e h) d = up (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) d "" := by
    show up (filterAllAgg (filterWeakAll (join e h) ws) rq) d "" = _
    rw [hX]
  have hsentE : sent φ e d = up (reviewAgg (pinned e ws rq)) d "" := rfl
  have hsentH : sent φ h d = up (reviewAgg (pinned h ws rq)) d "" := rfl
  -- the facts of the three reviewed states
  obtain ⟨cX, mX, ndX, bX, pbX, gnX, obX, _⟩ := reviewed_facts φ k key (join e h) hsJ hmJ ws rq
  obtain ⟨cE, mE, ndE, bE, _, gnE, obE, snnE⟩ := reviewed_facts φ k key e hse hme ws rq
  obtain ⟨cH, mH, ndH, bH, _, gnH, obH, snnH⟩ := reviewed_facts φ k key h hsh hmh ws rq
  have hpJ : pinned (join e h) ws rq = join (pinned e ws rq) (pinned h ws rq) := by
    show rq.foldl filterRequire (filterWeakAll (join e h) ws) = _
    rw [filterWeakAll_join, foldl_filterRequire_join]
  rw [hpJ] at cX mX ndX bX pbX gnX obX
  have hkey : key ∈ mapNodes φ k := hse.onMap
  have hkstep : key.step = k := mapNodes_step φ k key hkey
  have hdstep : d.step = k + 1 := by
    have hmk : (⟨k, key.index⟩ : NodeId) ∈ mapNodes φ k := by
      have : (⟨k, key.index⟩ : NodeId) = key := by
        cases key with
        | mk sp ix => simp only at hkstep ⊢; rw [hkstep]
      rw [this]; exact hkey
    exact mapNodes_step φ (k + 1) d (mapSons_subset φ k key.index hmk d (by rw [← hkstep]; exact hd))
  -- the join's reviewed state is valid
  have hvX : isValid (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) = true := by
    rw [hsentJ] at hv
    by_cases hx : isValid (reviewAgg (join (pinned e ws rq) (pinned h ws rq))) = true
    · exact hx
    · exfalso
      simp only [GPathM.up, hx] at hv
      exact hx hv
  have upv : ∀ g : GPathM, isValid g = true → up g d "" = addNode g d "" := by
    intro g hg; simp only [GPathM.up, hg, if_true]
  rw [hsentJ, hsentE, hsentH]
  rw [upv _ hvX]
  rcases hRJ k key e h hse hsh hme hmh ws rq hvX with ⟨hvE, hvH, hemb⟩ | ⟨hvE, hemb⟩ | ⟨hvH, hemb⟩
  · left
    rw [upv _ hvE, upv _ hvH]
    refine ⟨isValid_addNode _ d "" hvE (by rw [cE]; exact hdstep) gnE,
      isValid_addNode _ d "" hvH (by rw [cH]; exact hdstep) gnH, ?_⟩
    have hndG := Reader.nodup_join _ _ ndE ndH
    have hbG := below_join _ _ (cE.trans cH.symm) hndG bE bH
    have e1 := embedded_addNode _ _ d "" hemb (by rw [mX]; exact mE.symm) (by rw [cX]; exact hdstep)
      bX hbG pbX ndX gnX obX
    exact embedded_trans e1 (embedded_addNode_join _ _ d "" (cE.trans cH.symm) (mE.trans mH.symm)
      (by rw [cE]; exact hdstep) ndE ndH bE bH
      (by
        rw [cE]
        have hk0 : 0 ≤ k := by
          by_cases hk : k < 0
          · exfalso
            unfold mapNodes at hkey
            rw [if_pos hk] at hkey
            exact absurd hkey List.not_mem_nil
          · omega
        omega)
      (hog e ws rq) (hog h ws rq) gnE gnH)
  · right; left
    rw [upv _ hvE]
    refine ⟨isValid_addNode _ d "" hvE (by rw [cE]; exact hdstep) gnE, ?_⟩
    exact embedded_addNode _ _ d "" hemb (by rw [mX, mE]) (by rw [cX]; exact hdstep) bX bE pbX ndX
      gnX obX
  · right; right
    rw [upv _ hvH]
    refine ⟨isValid_addNode _ d "" hvH (by rw [cH]; exact hdstep) gnH, ?_⟩
    exact embedded_addNode _ _ d "" hemb (by rw [mX, mH]) (by rw [cX]; exact hdstep) bX bH pbX ndX
      gnX obX

/-- **The Improves verdict from the review of a join.** -/
theorem sat_of_reviewJoin (hwf : WF φ) (hRJ : ReviewJoin φ) (hog : OwnGowPinned)
    (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_distrib φ hwf (sendDistrib_of_reviewJoin φ hwf hRJ hog)
    (reviewDistrib_of_reviewJoin φ hRJ) kv hkv hv



/-- info: 'AbsSat.GraphPath.Model.ReviewJoin.sat_of_reviewJoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_reviewJoin

end AbsSat.GraphPath.Model.ReviewJoin
