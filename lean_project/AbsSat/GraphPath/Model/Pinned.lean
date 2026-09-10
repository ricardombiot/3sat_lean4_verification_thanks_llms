-- lean_project/AbsSat/GraphPath/Model/Pinned.lean
import AbsSat.GraphPath.Model.Bridge
import AbsSat.GraphPath.Model.Candidates
import AbsSat.GraphPath.Model.PathExists
import AbsSat.GraphPath.Model.PickInduction

/-!
**`PairwiseOwned` in a fully pinned state.**

v28 refuted the cheap route (the support clique) and v39's measurement refuted
the next one: ownership is **not transitive**, not even along the parent and
son links the bridge just certified — 15,240 of 420,078 downward triples and
18,919 of 416,403 upward ones fail. So co-ownership does not propagate along a
chain by any local rule.

This module takes the other road. Instead of propagating ownership, it removes
the choice: **when every step is pinned to a single map id, the whole path node
is determined**, and then co-ownership is not something to prove — there is
nothing else the owner could be.

The mechanism is the machine's own. `filterRequire` narrows `gowners` at one
step to a single map id; the review then intersects every node's owners with
`gowners`, and `SelfOwned` forces a surviving node's *own* id into that
intersection. So a surviving node at a pinned step carries the pinned map id.
That fixes half of a `PathNodeId`. The other half, `parent_id`, is fixed by the
step below: `PMP` says `parent_id` names the map id of the node's parents, and
the parents are nodes at the pinned step below.

Two `PathNodeId` fields, two pins. Hence `pid_unique`, hence `PairwiseOwned`.
-/

namespace AbsSat.GraphPath.Model.Pinned

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

-- ============================================================
-- Pinned steps
-- ============================================================

/-- **Step `k` is pinned:** all global owners at `k` carry the same map id.
This is exactly what `filterRequire` leaves behind at the step it constrains. -/
def PinnedAt (h : GPathM) (k : Int) : Prop :=
  ∀ q ∈ ownersAt h.gowners k, ∀ r ∈ ownersAt h.gowners k, q.id = r.id

/-- Every step below `current_step` is pinned — the state the Reader reaches
after choosing one node per step. -/
def FullyPinned (h : GPathM) : Prop :=
  ∀ k, 0 ≤ k → k < h.current_step → PinnedAt h k

/-- The invariants of a valid review fixpoint that the argument consumes,
bundled so the statements stay readable. Every field is a theorem elsewhere;
`ctx_filterAll` assembles them. -/
structure Ctx (h : GPathM) : Prop where
  self    : Ownership.SelfOwned h
  gn      : GownersNodes.GN h
  shape   : Parents.Shape h
  rootz   : Sons.RootAtZero h
  pmp     : ParentId.PMP h
  nodeval : ∀ pid n, h.node? pid = some n → isValidNode h n = true
  ownGow  : ∀ pid n, h.node? pid = some n → ∀ q ∈ n.owners,
              0 ≤ q.id.step → q.id.step < h.current_step → q ∈ h.gowners

-- ============================================================
-- A surviving node is a global owner at its own step
-- ============================================================

/-- A node is its own owner (`SelfOwned`) and its owners are global owners, so
**every surviving node sits in `gowners` at its own step**. -/
theorem mem_ownersAt_gowners (h : GPathM) (ctx : Ctx h)
    (p : PathNodeId) (n : PNodeM) (hn : h.node? p = some n)
    (hlo : 0 ≤ p.id.step) (hhi : p.id.step < h.current_step) :
    p ∈ ownersAt h.gowners p.id.step := by
  refine List.mem_filter.mpr ⟨ctx.ownGow p n hn p (ctx.self p n hn) hlo hhi, ?_⟩
  exact beq_iff_eq.mpr rfl

/-- **At a pinned step there is only one map id, and every node there carries
it.** The first of the two pins. -/
theorem mapId_eq (h : GPathM) (ctx : Ctx h) (k : Int)
    (hpin : PinnedAt h k) (hlo : 0 ≤ k) (hhi : k < h.current_step)
    (p : PathNodeId) (n : PNodeM) (hn : h.node? p = some n) (hps : p.id.step = k)
    (p' : PathNodeId) (n' : PNodeM) (hn' : h.node? p' = some n') (hps' : p'.id.step = k) :
    p.id = p'.id := by
  have h1 : p ∈ ownersAt h.gowners k := by
    have := mem_ownersAt_gowners h ctx p n hn (by rw [hps]; exact hlo) (by rw [hps]; exact hhi)
    rwa [hps] at this
  have h2 : p' ∈ ownersAt h.gowners k := by
    have := mem_ownersAt_gowners h ctx p' n' hn' (by rw [hps']; exact hlo)
      (by rw [hps']; exact hhi)
    rwa [hps'] at this
  exact hpin p h1 p' h2

-- ============================================================
-- The second pin: `parent_id`
-- ============================================================

/-- A non-root node has a parent, and that parent is a node one step below. -/
theorem some_parent (h : GPathM) (ctx : Ctx h)
    (p : PathNodeId) (n : PNodeM) (hn : h.node? p = some n) (hroot : p.parent_id ≠ none) :
    ∃ pp ∈ n.parents, ∃ pn, h.node? pp = some pn ∧ pp.id.step = p.id.step - 1 ∧
      some pp.id = p.parent_id := by
  have hmem : n ∈ h.nodes := List.mem_of_find?_eq_some hn
  have hnid : n.id = p := node?_id_eq h p n hn
  have hne : n.parents ≠ [] :=
    PathExists.parents_ne_nil_of_isValidNode h n (ctx.nodeval p n hn) (by rw [hnid]; exact hroot)
  obtain ⟨pp, hpp⟩ := List.exists_mem_of_ne_nil _ hne
  refine ⟨pp, hpp, ?_⟩
  obtain ⟨pn, hpn⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff h pp).mp (ctx.shape.pn n hmem pp hpp))
  refine ⟨pn, hpn, ?_, ?_⟩
  · have := ctx.shape.pbelow n hmem pp hpp
    rw [hnid] at this; exact this
  · have := ctx.pmp n hmem pp hpp
    rw [hnid] at this; exact this

/-- **The path node at a pinned step is unique.** Its map id is pinned by the
step's own requirement; its `parent_id` is pinned by the map id of the step
below. Nothing is left to choose. -/
theorem pid_unique (h : GPathM) (ctx : Ctx h) (hfp : FullyPinned h) (k : Int)
    (hlo : 0 ≤ k) (hhi : k < h.current_step)
    (p : PathNodeId) (n : PNodeM) (hn : h.node? p = some n) (hps : p.id.step = k)
    (p' : PathNodeId) (n' : PNodeM) (hn' : h.node? p' = some n') (hps' : p'.id.step = k) :
    p = p' := by
  have hid : p.id = p'.id := mapId_eq h ctx k (hfp k hlo hhi) hlo hhi p n hn hps p' n' hn' hps'
  refine ParentId.pathNodeId_ext hid ?_
  have hmem : n ∈ h.nodes := List.mem_of_find?_eq_some hn
  have hmem' : n' ∈ h.nodes := List.mem_of_find?_eq_some hn'
  have hnid : n.id = p := node?_id_eq h p n hn
  have hnid' : n'.id = p' := node?_id_eq h p' n' hn'
  by_cases hz : k = 0
  · have e1 : p.parent_id = none := by
      have := ctx.rootz n hmem (by rw [hnid, hps]; exact hz)
      rwa [hnid] at this
    have e2 : p'.parent_id = none := by
      have := ctx.rootz n' hmem' (by rw [hnid', hps']; exact hz)
      rwa [hnid'] at this
    rw [e1, e2]
  · have hkpos : 0 < k := by omega
    have hroot : p.parent_id ≠ none := by
      have := ctx.shape.notroot n hmem (by rw [hnid, hps]; exact hkpos)
      rwa [hnid] at this
    have hroot' : p'.parent_id ≠ none := by
      have := ctx.shape.notroot n' hmem' (by rw [hnid', hps']; exact hkpos)
      rwa [hnid'] at this
    obtain ⟨pp, _, pn, hpn, hstep, heq⟩ := some_parent h ctx p n hn hroot
    obtain ⟨pp', _, pn', hpn', hstep', heq'⟩ := some_parent h ctx p' n' hn' hroot'
    have hb1 : pp.id.step = k - 1 := by rw [hstep, hps]
    have hb2 : pp'.id.step = k - 1 := by rw [hstep', hps']
    have hlo1 : (0 : Int) ≤ k - 1 := by omega
    have hhi1 : k - 1 < h.current_step := by omega
    have : pp.id = pp'.id :=
      mapId_eq h ctx (k - 1) (hfp (k - 1) hlo1 hhi1) hlo1 hhi1 pp pn hpn hb1 pp' pn' hpn' hb2
    rw [← heq, ← heq', this]

-- ============================================================
-- `PairwiseOwned`
-- ============================================================

/-- **The obligation, discharged in the pinned regime.** Every candidate owner
at step `i` is a node at step `i`, and there is only one of those, so it *is*
the chain's pick. Co-ownership is not propagated — it is forced. -/
theorem pairwiseOwned_of_fullyPinned (h : GPathM) (ctx : Ctx h) (hfp : FullyPinned h)
    (sel : Int → PathNodeId) (hchain : IsChain h sel) : PairwiseOwned h sel := by
  intro i j hi hj hin hjn _
  obtain ⟨hjs, _⟩ := hchain.1 j hj hjn
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hjs
  have hall := owners_ok_of_isValidNode h n (ctx.nodeval (sel j) n hn)
  have hentry : hasStepEntry n.owners i = true :=
    List.all_eq_true.mp hall i (mem_intRange hi (by omega))
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp hentry
  have hqstep : q.id.step = i := eq_of_beq hqs
  have hqgow : q ∈ h.gowners :=
    ctx.ownGow (sel j) n hn q hq (by rw [hqstep]; exact hi) (by rw [hqstep]; exact hin)
  obtain ⟨qn, hqn⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff h q).mp (ctx.gn q hqgow))
  obtain ⟨his, hisstep⟩ := hchain.1 i hi hin
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp his
  have : q = sel i := pid_unique h ctx hfp i hi hin q qn hqn hqstep (sel i) m hm hisstep
  rw [ownersOf, hn]
  exact List.mem_filter.mpr ⟨this ▸ hq, by rw [← this]; exact hqs⟩


-- ============================================================
-- Where the pinned states come from: the machine's own filter
-- ============================================================

/-- Pinning survives any later narrowing: `PinnedAt` is a property of a
sublist of `gowners`. -/
theorem PinnedAt_of_sub {h h' : GPathM} (hsub : ∀ q ∈ h'.gowners, q ∈ h.gowners)
    (k : Int) (hp : PinnedAt h k) : PinnedAt h' k := by
  intro q hq r hr
  exact hp q (List.mem_filter.mpr ⟨hsub q (List.mem_filter.mp hq).1, (List.mem_filter.mp hq).2⟩)
    r (List.mem_filter.mpr ⟨hsub r (List.mem_filter.mp hr).1, (List.mem_filter.mp hr).2⟩)

/-- **One `filterRequire` pins its step.** After it, every global owner at
`req.step` carries the map id `req` — that is all the operation does. -/
theorem pinnedAt_filterRequire (g : GPathM) (req : NodeId) :
    PinnedAt (filterRequire g req) req.step := by
  have key : ∀ q ∈ ownersAt (filterRequire g req).gowners req.step, q.id = req := by
    intro q hq
    have h1 := List.mem_filter.mp hq
    have hstep : q.id.step = req.step := eq_of_beq h1.2
    have h2 := List.mem_filter.mp h1.1
    have := h2.2
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with hne | heq
    · exact absurd hstep hne
    · exact eq_of_beq heq
  intro q hq r hr
  rw [key q hq, key r hr]

theorem gowners_sub_foldl (g : GPathM) :
    ∀ (rs : List NodeId) q, q ∈ (rs.foldl filterRequire g).gowners → q ∈ g.gowners := by
  intro rs
  induction rs generalizing g with
  | nil => intro q hq; exact hq
  | cons a rest ih =>
    intro q hq
    exact (pruned_filterRequire g a).gowners_sub q (ih (filterRequire g a) q hq)

/-- Every requirement in the list pins its step, all the way through the fold
and the review that follows it. -/
theorem pinnedAt_filterAll (g : GPathM) :
    ∀ (rs : List NodeId) (req : NodeId), req ∈ rs →
      PinnedAt (rs.foldl filterRequire g) req.step := by
  intro rs
  induction rs generalizing g with
  | nil => intro _ h; exact absurd h List.not_mem_nil
  | cons a rest ih =>
    intro req hreq
    rcases List.mem_cons.mp hreq with rfl | hrest
    · exact PinnedAt_of_sub (gowners_sub_foldl (filterRequire g req) rest) req.step
        (pinnedAt_filterRequire g req)
    · exact ih (filterRequire g a) req hrest

/-- The list of requirements **covers** the state: one per step. -/
def Covers (reqs : List NodeId) (h : GPathM) : Prop :=
  ∀ k, 0 ≤ k → k < h.current_step → ∃ req ∈ reqs, req.step = k

/-- **A covered `filterAll` is fully pinned.** This is the Reader's endgame
state: one requirement chosen per step, the filter applied, the review run. -/
theorem fullyPinned_filterAll (g : GPathM) (reqs : List NodeId)
    (hcov : Covers reqs (filterAll g reqs)) : FullyPinned (filterAll g reqs) := by
  intro k hlo hhi
  obtain ⟨req, hmem, hstep⟩ := hcov k hlo hhi
  subst hstep
  exact PinnedAt_of_sub (pruned_review (reqs.foldl filterRequire g)).gowners_sub req.step
    (pinnedAt_filterAll g reqs req hmem)

-- ============================================================
-- The context, assembled for the machine's states
-- ============================================================

variable (reqOf : NodeId → List NodeId)

theorem ctx_filterAll (g : GPathM) (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true) : Ctx (filterAll g reqs) where
  self := SelfOwn.SelfOwned_filterAll reqOf g reqs hreach hv
  gn := GownersNodes.GN_filterAll g reqs (GownersNodes.GN_reachable reqOf g hreach)
  shape := Parents.Shape_filterAll reqOf g reqs hreach
  rootz := Sons.RootAtZero_reachable_filterAll reqOf g reqs hreach
  pmp := ParentId.PMP_filterAll reqOf g reqs hreach
  nodeval := fun pid n hn => review_node_valid _ hv pid n hn
  ownGow := fun pid n hn q hq hlo hhi =>
    Candidates.owner_mem_gowners _ hv pid n hn q hq hlo hhi

-- ============================================================
-- The payoff
-- ============================================================

/-- **A covered, valid state is inhabited.** `exists_isChain` builds the path
(v27) and the pinning makes it pairwise-owned, so the state denotes something —
which is exactly what the verdict rests on. -/
theorem inhabited_of_covered (g : GPathM) (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true)
    (hpos : 0 < (filterAll g reqs).current_step)
    (hcov : Covers reqs (filterAll g reqs)) : Inhabited (filterAll g reqs) := by
  obtain ⟨sel, hchain⟩ := PathExists.exists_isChain reqOf g reqs hreach hv hpos
  exact ⟨pathOf sel (filterAll g reqs), sel, hchain,
    pairwiseOwned_of_fullyPinned _ (ctx_filterAll reqOf g reqs hreach hv)
      (fullyPinned_filterAll g reqs hcov) sel hchain, rfl⟩

/-- info: 'AbsSat.GraphPath.Model.Pinned.inhabited_of_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inhabited_of_covered


-- ============================================================
-- This *is* route A′'s base case
-- ============================================================

/-!
v19 left `Inhabited_of_pickValid` with two holes: `PickValid` (the inductive
step) and `hbase` — *a state where propagation has left no choice is
inhabited*. Its hypothesis, `PickInduction.NoChoice`, unfolds to

    ∀ k in range, ∀ q r ∈ ownersAt gowners k, q.id = r.id

which is `FullyPinned` written with `Bool`. So the base case is not a separate
problem: it is the theorem above. **`hbase` is discharged.**
-/

theorem fullyPinned_of_noChoice (h : GPathM) (hnc : PickInduction.NoChoice h) :
    FullyPinned h := by
  intro k hlo hhi q hq r hr
  cases hqr : q.id == r.id with
  | true => exact eq_of_beq hqr
  | false =>
    exfalso
    have hne : q.id ≠ r.id := fun hEq =>
      absurd (beq_iff_eq.mpr hEq) (by rw [hqr]; exact Bool.false_ne_true)
    have hck : PickInduction.choiceAt h k = true :=
      List.any_eq_true.mpr ⟨q, hq, List.any_eq_true.mpr ⟨r, hr, bne_iff_ne.mpr hne⟩⟩
    have hc : PickInduction.hasChoice h = true :=
      List.any_eq_true.mpr ⟨k, mem_intRange hlo (by omega), hck⟩
    rw [hnc] at hc
    exact Bool.false_ne_true hc

theorem noChoice_of_fullyPinned (h : GPathM) (hfp : FullyPinned h) :
    PickInduction.NoChoice h := by
  cases hb : PickInduction.hasChoice h with
  | false => exact hb
  | true =>
    exfalso
    obtain ⟨k, hk, hck⟩ := List.any_eq_true.mp hb
    obtain ⟨hlo, hhi⟩ := PickInduction.intRange_bounds hk
    obtain ⟨q, hq, hqr⟩ := List.any_eq_true.mp hck
    obtain ⟨r, hr, hne⟩ := List.any_eq_true.mp hqr
    exact absurd (hfp k hlo (by omega) q hq r hr) (bne_iff_ne.mp hne)

/-- **Route A′'s base case, discharged.** A state where propagation has left no
choice is inhabited — given a path, which v27 supplies for the machine's
states. -/
theorem inhabited_of_noChoice (h : GPathM) (ctx : Ctx h)
    (hnc : PickInduction.NoChoice h) (hex : ∃ sel, IsChain h sel) : Inhabited h := by
  obtain ⟨sel, hchain⟩ := hex
  exact ⟨pathOf sel h, sel, hchain,
    pairwiseOwned_of_fullyPinned h ctx (fullyPinned_of_noChoice h hnc) sel hchain, rfl⟩

/-- The same on the machine's own states, with the path supplied by v27 — the
form `Inhabited_of_pickValid` asks for. -/
theorem inhabited_of_noChoice_filterAll (g : GPathM) (reqs : List NodeId)
    (hreach : Reachable reqOf g) (hv : isValid (filterAll g reqs) = true)
    (hpos : 0 < (filterAll g reqs).current_step)
    (hnc : PickInduction.NoChoice (filterAll g reqs)) : Inhabited (filterAll g reqs) :=
  inhabited_of_noChoice _ (ctx_filterAll reqOf g reqs hreach hv) hnc
    (PathExists.exists_isChain reqOf g reqs hreach hv hpos)

/-- info: 'AbsSat.GraphPath.Model.Pinned.inhabited_of_noChoice_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inhabited_of_noChoice_filterAll


-- ============================================================
-- The route this replaces
-- ============================================================

/-- Ownership propagated along the links. ⚠ **Refuted by measurement** —
`lake exe extend --randomtrans`, 20 instances: of 420,078 downward triples
(`q` a parent of `n`, `r` an owner of `q` below `q`) **15,240** fail, and of
416,403 upward ones (`q` a son of `n`, `r` an owner of `q` above `q`)
**18,919** fail. Globally it is worse: 2,950,784 of 22,521,728.

This was the natural route once `Bridge.linksInOwners_review` made the
adjacent pairs free: walk down the chain from `sel j`, carrying `sel i`
through the parent link. It does not work — co-ownership does not propagate.
`pairwiseOwned_of_fullyPinned` takes the other road, removing the choice
instead of propagating the relation. -/
def OwnersTransitive (h : GPathM) : Prop :=
  ∀ pid n, h.node? pid = some n → ∀ q ∈ n.owners, ∀ qn, h.node? q = some qn →
    ∀ r ∈ qn.owners, r ∈ n.owners

/-- info: 'AbsSat.GraphPath.Model.Pinned.pairwiseOwned_of_fullyPinned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairwiseOwned_of_fullyPinned

/-- info: 'AbsSat.GraphPath.Model.Pinned.pid_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pid_unique

end AbsSat.GraphPath.Model.Pinned
