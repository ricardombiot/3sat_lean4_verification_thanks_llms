-- lean_project/AbsSat/GraphPath/Model/RoundInvariant.lean
import AbsSat.GraphPath.Model.SliceInvariant

/-!
# The round invariant: after the base review, every ghost is detectable as a pair

The author's review (v140): pins break partial paths; the base review (clean against the global owners,
coherence with parents, coherence with sons) removes the nodes left without a path; the aggressive
filter has two legs — **symmetry** and **path membership** (two owners share an owner at every step) —
and everything repeats until it converges.

Measured (probe `helly ghosts`, every map pin on every exact state of K4 and parity, 3,02 M ghost
entries — entries no surviving path holds): **every ghost dies in the first pass of the base review or
in the first aggressive sweep**, and **every ghost that reaches the sweep is directly detectable**:
asymmetric, or with a step where the two tables share nothing. No second round is ever needed.

This module turns that into the open statement, and proves that it is enough:

* **`GhostsDetectable B R`** — after the base review `B` of the pinned state, every entry is asymmetric,
  or fails path membership, or lies on a path of the final state `R`.
* **`tablesSound_of_ghosts`** — then every table of `R` is a slice. No reasoning about the order of the
  sweep is needed: the final state is symmetric and shares every step (`aggOk_reviewAgg`), and its
  tables sit inside `B`'s, so a detectable entry of `B` cannot survive into `R`.
* **`filterSlices_of_ghosts`** and **`sat_of_ghosts`** — the slice invariant of the whole run, and the
  verdict, from the round invariant.

## What the verdict actually consumes (2026-09-22)

`tablesSound_of_ghosts` only ever applies the invariant to pairs that are **still an entry of the
final state** `R`, and on those pairs the two legs of the author's filter are *refuted*, not used
(`legs_dead`): `R` is `AggOk`, so the entry is symmetric and shares every step, and both properties
climb back to the larger tables of `B`. Restricting the invariant to those pairs
(`GhostsDetectableR`) therefore loses nothing — and what is left is the goal itself:

* **`ghostsR_iff_tablesSound`** — `GhostsDetectableR B R ↔ TablesSound R`.
* **`ghostsLineR_iff_filterSlices`** — `GhostsLineR φ ↔ FilterSlices φ`.

So the declared hypothesis is **not a weaker foothold than the slice invariant it proves**. Its
surplus over `FilterSlices` is entirely about the entries that *die* in the aggressive review — the
measured "one round is enough" — and the verdict never reads that part.
-/

namespace AbsSat.GraphPath.Model.RoundInvariant

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun (MInv)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes)
open AbsSat.GraphPath.Model.AggFixpoint (AggOk aggOk_reviewAgg)
open AbsSat.GraphPath.Model.SliceInvariant (FilterSlices sat_of_slices)

variable (φ : Cnf)

/-- **The round invariant.** After the base review `B`, every entry between two nodes is asymmetric,
or its two tables share nothing at some step, or it lies on a path of the final state `R`. -/
def GhostsDetectable (B R : GPathM) : Prop :=
  ∀ x v nx nv, B.node? x = some nx → B.node? v = some nv →
    0 ≤ x.id.step → x.id.step < B.current_step → 0 ≤ v.id.step → v.id.step < B.current_step →
    v ∈ nx.owners →
      x ∉ nv.owners ∨ sharesEveryStep B.current_step nx.owners nv.owners = false ∨ Realizes R x v

-- ============================================================
-- Detectable entries do not survive
-- ============================================================

/-- Path membership fails for smaller tables too, as long as the smaller second table still has an
entry at every step. -/
theorem shares_false_of_sub (cs : Int) (xo wo xo' wo' : List PathNodeId)
    (hx : ∀ r ∈ xo', r ∈ xo) (hw : ∀ r ∈ wo', r ∈ wo)
    (hent : ∀ k, 0 ≤ k → k < cs → hasStepEntry wo' k = true)
    (h : sharesEveryStep cs xo wo = false) : sharesEveryStep cs xo' wo' = false := by
  cases hb : sharesEveryStep cs xo' wo' with
  | false => rfl
  | true =>
    -- if the smaller tables shared every step, so would the larger ones
    have hbig : sharesEveryStep cs xo wo = true := by
      unfold sharesEveryStep at hb ⊢
      apply List.all_eq_true.mpr
      intro k hk
      have hk' := List.all_eq_true.mp hb k hk
      have h0 := mem_intRange_lower hk
      have h1 := mem_intRange_upper hk
      rw [hent k h0 (by omega), Bool.not_true, Bool.false_or] at hk'
      obtain ⟨r, hr, hc⟩ := List.any_eq_true.mp hk'
      have hr' : r ∈ ownersAt xo k := by
        simp only [ownersAt, List.mem_filter] at hr ⊢
        exact ⟨hx r hr.1, hr.2⟩
      have hin : r ∈ wo := hw r (List.mem_of_elem_eq_true hc)
      have hany : (ownersAt xo k).any (fun r => wo.contains r) = true :=
        List.any_eq_true.mpr ⟨r, hr', List.elem_eq_true_of_mem hin⟩
      rw [hany, Bool.or_true]
    rw [hbig] at h
    exact absurd h (by decide)

/-- **The round invariant is enough**: if every entry of the base review is detectable or on a path
of the final state, every table of the final state is a slice. -/
theorem tablesSound_of_ghosts (B R : GPathM) (hpr : Pruned B R) (hndB : NodupIds B)
    (hR : ReadableAgg R) (hv : isValid R = true) (hok : AggOk R) (hG : GhostsDetectable B R) :
    TablesSound R := by
  have rc := RCtx_of_readableAgg R hR
  have ctx := Reader.Ctx_of_readable R (readable_of_readableAgg R hR) hv
  have hcs : R.current_step = B.current_step := hpr.step_eq
  -- a node of `R` is a node of `B` with a larger table
  have up : ∀ y m, R.node? y = some m → ∃ n, B.node? y = some n ∧ ∀ q ∈ m.owners, q ∈ n.owners := by
    intro y m hy
    have hmem := List.mem_of_find?_eq_some hy
    obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived m hmem
    have hyid := node?_id_eq R y m hy
    refine ⟨n, ?_, hown⟩
    rw [← hyid, hid]; exact node?_of_mem hndB n hn
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  -- `q` is a node of `R`: an owner in range is a global owner, and global owners are nodes
  obtain ⟨mq, hmq, hmqid⟩ := rc.gn q (ctx.ownGow x n hx q hqn hq0 hq1)
  have hq : R.node? q = some mq := by rw [← hmqid]; exact node?_of_mem rc.nodup mq hmq
  obtain ⟨nx, hnx, hsubx⟩ := up x n hx
  obtain ⟨nq, hnq, hsubq⟩ := up q mq hq
  have hvx := ctx.nodeval x n hx
  have hvq := ctx.nodeval q mq hq
  obtain ⟨hsym, hshare⟩ := hok x n q mq hx hq hx0 hx1 hq0 hq1 hqn hvx hvq
  rcases hG x q nx nq hnx hnq hx0 (by rw [← hcs]; exact hx1) hq0 (by rw [← hcs]; exact hq1)
    (hsubx q hqn) with hasym | hsh | hreal
  · exact absurd (hsubq x hsym) hasym
  · -- path membership fails in `B`, so it fails in `R`
    have hent : ∀ k, 0 ≤ k → k < B.current_step → hasStepEntry mq.owners k = true := by
      intro k h0 h1
      have := owners_ok_of_isValidNode R mq hvq
      simp only [List.all_eq_true] at this
      exact this k (mem_intRange h0 (by rw [hcs]; omega))
    have := shares_false_of_sub B.current_step nx.owners nq.owners n.owners mq.owners hsubx hsubq hent hsh
    rw [← hcs] at this
    rw [hshare] at this
    exact absurd this (by decide)
  · exact hreal

-- ============================================================
-- Only the surviving entries are used
-- ============================================================

/-- **The round invariant, restricted to the entries that survive.** Word for word
`GhostsDetectable`, with one extra hypothesis: the pair is still an entry *of the final state* `R`.

`tablesSound_of_ghosts` only ever applies the invariant to such pairs, so this weaker statement is
enough (`tablesSound_of_ghostsR`). -/
def GhostsDetectableR (B R : GPathM) : Prop :=
  ∀ x v nx nv mx, B.node? x = some nx → B.node? v = some nv → R.node? x = some mx →
    0 ≤ x.id.step → x.id.step < B.current_step → 0 ≤ v.id.step → v.id.step < B.current_step →
    v ∈ nx.owners → v ∈ mx.owners →
      x ∉ nv.owners ∨ sharesEveryStep B.current_step nx.owners nv.owners = false ∨ Realizes R x v

/-- The stated invariant is at least as strong as the restricted one. -/
theorem ghostsR_of_ghosts (B R : GPathM) (hG : GhostsDetectable B R) : GhostsDetectableR B R := by
  intro x v nx nv _ hnx hnv _ hx0 hx1 hv0 hv1 hmem _
  exact hG x v nx nv hnx hnv hx0 hx1 hv0 hv1 hmem

/-- **The two legs of the author's aggressive filter are refuted on the entries that survive.** If
`(x, v)` is still an entry of the final state `R`, then in the base-reviewed state `B` it is
symmetric *and* the two tables share every step: `R` is `AggOk`, its tables sit inside `B`'s, and
sharing only grows when the tables grow.

So in `GhostsDetectableR` the first two disjuncts are always false, and only `Realizes R x v` can
ever hold. -/
theorem legs_dead (B R : GPathM) (hpr : Pruned B R) (hndB : NodupIds B)
    (hR : ReadableAgg R) (hv : isValid R = true) (hok : AggOk R)
    {x v : PathNodeId} {nx nv mx : PNodeM}
    (hnx : B.node? x = some nx) (hnv : B.node? v = some nv) (hmx : R.node? x = some mx)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < B.current_step)
    (hv0 : 0 ≤ v.id.step) (hv1 : v.id.step < B.current_step) (hvm : v ∈ mx.owners) :
    x ∈ nv.owners ∧ sharesEveryStep B.current_step nx.owners nv.owners = true := by
  have rc := RCtx_of_readableAgg R hR
  have ctx := Reader.Ctx_of_readable R (readable_of_readableAgg R hR) hv
  have hcs : R.current_step = B.current_step := hpr.step_eq
  have up : ∀ y m, R.node? y = some m → ∃ n, B.node? y = some n ∧ ∀ q ∈ m.owners, q ∈ n.owners := by
    intro y m hy
    have hmem := List.mem_of_find?_eq_some hy
    obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived m hmem
    have hyid := node?_id_eq R y m hy
    refine ⟨n, ?_, hown⟩
    rw [← hyid, hid]; exact node?_of_mem hndB n hn
  obtain ⟨mv, hmvmem, hmvid⟩ := rc.gn v (ctx.ownGow x mx hmx v hvm hv0 (by rw [hcs]; exact hv1))
  have hmv : R.node? v = some mv := by rw [← hmvid]; exact node?_of_mem rc.nodup mv hmvmem
  obtain ⟨nx', hnx', hsubx⟩ := up x mx hmx
  obtain ⟨nv', hnv', hsubv⟩ := up v mv hmv
  rw [hnx] at hnx'; rw [hnv] at hnv'
  have hnxe : nx' = nx := (Option.some.inj hnx').symm
  have hnve : nv' = nv := (Option.some.inj hnv').symm
  subst hnxe; subst hnve
  obtain ⟨hsym, hshare⟩ := hok x mx v mv hmx hmv hx0 (by rw [hcs]; exact hx1) hv0
    (by rw [hcs]; exact hv1) hvm (ctx.nodeval x mx hmx) (ctx.nodeval v mv hmv)
  refine ⟨hsubv x hsym, ?_⟩
  cases hb : sharesEveryStep B.current_step nx'.owners nv'.owners with
  | true => rfl
  | false =>
    have hent : ∀ k, 0 ≤ k → k < B.current_step → hasStepEntry mv.owners k = true := by
      intro k h0 h1
      have := owners_ok_of_isValidNode R mv (ctx.nodeval v mv hmv)
      simp only [List.all_eq_true] at this
      exact this k (mem_intRange h0 (by rw [hcs]; omega))
    have := shares_false_of_sub B.current_step nx'.owners nv'.owners mx.owners mv.owners
      hsubx hsubv hent hb
    rw [← hcs, hshare] at this
    exact absurd this (by decide)

/-- **The restricted invariant is enough**: `tablesSound_of_ghosts` only ever applies the invariant
to pairs that are entries of `R`, and there `legs_dead` leaves only the third disjunct. -/
theorem tablesSound_of_ghostsR (B R : GPathM) (hpr : Pruned B R) (hndB : NodupIds B)
    (hR : ReadableAgg R) (hv : isValid R = true) (hok : AggOk R) (hG : GhostsDetectableR B R) :
    TablesSound R := by
  have rc := RCtx_of_readableAgg R hR
  have ctx := Reader.Ctx_of_readable R (readable_of_readableAgg R hR) hv
  have hcs : R.current_step = B.current_step := hpr.step_eq
  have up : ∀ y m, R.node? y = some m → ∃ n, B.node? y = some n ∧ ∀ q ∈ m.owners, q ∈ n.owners := by
    intro y m hy
    have hmem := List.mem_of_find?_eq_some hy
    obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived m hmem
    have hyid := node?_id_eq R y m hy
    refine ⟨n, ?_, hown⟩
    rw [← hyid, hid]; exact node?_of_mem hndB n hn
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  obtain ⟨mq, hmq, hmqid⟩ := rc.gn q (ctx.ownGow x n hx q hqn hq0 hq1)
  have hq : R.node? q = some mq := by rw [← hmqid]; exact node?_of_mem rc.nodup mq hmq
  obtain ⟨nx, hnx, _⟩ := up x n hx
  obtain ⟨nq, hnq, _⟩ := up q mq hq
  have hx1' : x.id.step < B.current_step := by rw [← hcs]; exact hx1
  have hq1' : q.id.step < B.current_step := by rw [← hcs]; exact hq1
  obtain ⟨hsym, hshare⟩ := legs_dead B R hpr hndB hR hv hok hnx hnq hx hx0 hx1' hq0 hq1' hqn
  rcases hG x q nx nq n hnx hnq hx hx0 hx1' hq0 hq1' (by
    obtain ⟨n', hn', hsub⟩ := up x n hx
    rw [hnx] at hn'
    have : n' = nx := (Option.some.inj hn').symm
    subst this; exact hsub q hqn) hqn with hasym | hsh | hreal
  · exact absurd hsym hasym
  · rw [hshare] at hsh; exact absurd hsh (by decide)
  · exact hreal

/-- **And the restricted invariant is no more than the goal.** Exact tables in `R` give it outright,
through the third disjunct — the only one `legs_dead` leaves standing. -/
theorem ghostsR_of_tablesSound (B R : GPathM) (hpr : Pruned B R) (ht : TablesSound R) :
    GhostsDetectableR B R := by
  intro x v _ _ mx _ _ hmx hx0 hx1 hv0 hv1 _ hvm
  have hcs : R.current_step = B.current_step := hpr.step_eq
  exact Or.inr (Or.inr (ht x mx hmx hx0 (by rw [hcs]; exact hx1) v hv0 (by rw [hcs]; exact hv1) hvm))

/-- **`GhostsDetectableR B R` *is* `TablesSound R`.** -/
theorem ghostsR_iff_tablesSound (B R : GPathM) (hpr : Pruned B R) (hndB : NodupIds B)
    (hR : ReadableAgg R) (hv : isValid R = true) (hok : AggOk R) :
    GhostsDetectableR B R ↔ TablesSound R :=
  ⟨tablesSound_of_ghostsR B R hpr hndB hR hv hok, ghostsR_of_tablesSound B R hpr⟩

-- ============================================================
-- The base review comes first
-- ============================================================

/-- The final state of the aggressive review is a narrowing of its first base review. -/
theorem pruned_review_reviewAgg (g : GPathM) : Pruned (review g) (reviewAgg g) := by
  unfold reviewAgg
  generalize measure g + 1 = fuel
  cases fuel with
  | zero => exact Pruned.refl _
  | succ n =>
    simp only [reviewAggFuel]
    split
    · split
      · exact Pruned.trans (pruned_aggSweep _) (pruned_reviewAggFuel n _)
      · exact Pruned.refl _
    · exact Pruned.refl _

/-- The pinned state a send reviews. -/
abbrev pinnedW (g : GPathM) (ws : List (Int × List NodeId)) (rq : List NodeId) : GPathM :=
  rq.foldl filterRequire (filterWeakAll g ws)

/-- **The round invariant along the run**: after the base review of every pinned line state, every
ghost is detectable. -/
def GhostsLine : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), StateOkF φ k kv → MInv φ kv.2 → TablesSound kv.2 →
    ∀ (ws : List (Int × List NodeId)) (rq : List NodeId),
      isValid (filterAllAgg (filterWeakAll kv.2 ws) rq) = true →
      GhostsDetectable (review (pinnedW kv.2 ws rq)) (filterAllAgg (filterWeakAll kv.2 ws) rq)

/-- **The slice invariant from the round invariant.** -/
theorem filterSlices_of_ghosts (hG : GhostsLine φ) : FilterSlices φ := by
  intro k kv hkv hm ht ws rq hv
  have hR : ReadableAgg (filterAllAgg (filterWeakAll kv.2 ws) rq) :=
    ⟨filterWeakAll kv.2 ws, rq, RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx, rfl⟩
  have rcP : Reader.RCtx (pinnedW kv.2 ws rq) :=
    RCtx_of_keeps (keeps_foldl _ keeps_filterRequire rq _)
      (RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx)
  have hndB : NodupIds (review (pinnedW kv.2 ws rq)) := (RCtx_review _ rcP).nodup
  exact tablesSound_of_ghosts _ _ (pruned_review_reviewAgg (pinnedW kv.2 ws rq)) hndB hR hv
    (aggOk_reviewAgg _ hv) (hG k kv hkv hm ht ws rq hv)

/-- **The round invariant along the run, restricted to the entries that survive.** -/
def GhostsLineR : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), StateOkF φ k kv → MInv φ kv.2 → TablesSound kv.2 →
    ∀ (ws : List (Int × List NodeId)) (rq : List NodeId),
      isValid (filterAllAgg (filterWeakAll kv.2 ws) rq) = true →
      GhostsDetectableR (review (pinnedW kv.2 ws rq)) (filterAllAgg (filterWeakAll kv.2 ws) rq)

/-- The stated invariant is at least as strong as the restricted one, line by line. -/
theorem ghostsLineR_of_ghostsLine (hG : GhostsLine φ) : GhostsLineR φ := fun k kv hkv hm ht ws rq hv =>
  ghostsR_of_ghosts _ _ (hG k kv hkv hm ht ws rq hv)

/-- **The slice invariant from the restricted round invariant.** -/
theorem filterSlices_of_ghostsR (hG : GhostsLineR φ) : FilterSlices φ := by
  intro k kv hkv hm ht ws rq hv
  have hR : ReadableAgg (filterAllAgg (filterWeakAll kv.2 ws) rq) :=
    ⟨filterWeakAll kv.2 ws, rq, RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx, rfl⟩
  have rcP : Reader.RCtx (pinnedW kv.2 ws rq) :=
    RCtx_of_keeps (keeps_foldl _ keeps_filterRequire rq _)
      (RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx)
  have hndB : NodupIds (review (pinnedW kv.2 ws rq)) := (RCtx_review _ rcP).nodup
  exact tablesSound_of_ghostsR _ _ (pruned_review_reviewAgg (pinnedW kv.2 ws rq)) hndB hR hv
    (aggOk_reviewAgg _ hv) (hG k kv hkv hm ht ws rq hv)

/-- **And the slice invariant gives the restricted round invariant back.** -/
theorem ghostsLineR_of_filterSlices (hF : FilterSlices φ) : GhostsLineR φ := by
  intro k kv hkv hm ht ws rq hv
  exact ghostsR_of_tablesSound _ _ (pruned_review_reviewAgg (pinnedW kv.2 ws rq))
    (hF k kv hkv hm ht ws rq hv)

/-- **The restricted round invariant *is* the slice invariant.** So the part of the declared
hypothesis that the verdict actually consumes is not weaker than what it is used to prove: it is the
same statement. What `GhostsLine` adds on top — that the entries which *die* in the aggressive review
were already detectable after the base review — is the measured "one round is enough", and the
verdict never uses it. -/
theorem ghostsLineR_iff_filterSlices : GhostsLineR φ ↔ FilterSlices φ :=
  ⟨filterSlices_of_ghostsR φ, ghostsLineR_of_filterSlices φ⟩

/-- **The Improves verdict from the round invariant.** -/
theorem sat_of_ghosts (hwf : WF φ) (hG : GhostsLine φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_slices φ hwf (filterSlices_of_ghosts φ hG) kv hkv hv


/-- info: 'AbsSat.GraphPath.Model.RoundInvariant.sat_of_ghosts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_ghosts

/-- info: 'AbsSat.GraphPath.Model.RoundInvariant.legs_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms legs_dead

/-- info: 'AbsSat.GraphPath.Model.RoundInvariant.ghostsR_iff_tablesSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ghostsR_iff_tablesSound

/-- info: 'AbsSat.GraphPath.Model.RoundInvariant.ghostsLineR_iff_filterSlices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ghostsLineR_iff_filterSlices

end AbsSat.GraphPath.Model.RoundInvariant
