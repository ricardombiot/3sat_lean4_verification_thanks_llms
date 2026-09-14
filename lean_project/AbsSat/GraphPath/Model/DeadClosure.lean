-- lean_project/AbsSat/GraphPath/Model/DeadClosure.lean
import AbsSat.GraphPath.Model.NoZombies
import AbsSat.GraphPath.Model.Threaded

/-!
# The removal closure over nodes, owner entries and links

`RemovalClosure.Unsupported` follows only whole nodes. The review also deletes single owner
entries (the intersections with the parents' and the sons' owners) and the parent/son links whose
owner entries went, and those deletions propagate inside a pass. So a node can be removed without
being unsupported: on `SatMachinePure`, the 9-variable formula found by the adversarial search
(`9 -3 -8 / 7 -8 4 / 3 8 -1 / -2 -6 8 / 3 -1 -5 / 2 -4 3 / -6 5 1 / 3 8 2 / -6 -9 7`) has, at the
send from key `(23,2)` to `(24,6)` with pins `x2 = 1, x4 = 0, x3 = 0`, a node `(12,0)` on no full
chain, not unsupported, removed by `reviewSons`, from a state whose 79 nodes all lie on full chains.
`NoZombies.LossInClosure` is false there.

`Dead P` is the closure over four kinds of item:

* `node x` — the node goes;
* `entry x q` — the owner entry `q` of `x` goes;
* `link x p` — the link between `x` and `p` is broken: `p` is dead, or one of the two entries is;
* `carry x p q` — the neighbour `p` does not carry `q` for `x`: the link is broken, or the entry
  `q` of `p` is dead.

An entry dies when its owner is not a global owner, when its owner is dead, or when no parent (no
son) carries it. A node dies when some step has only dead entries, or when every parent (every son)
link is broken.

Proved here:

* `dead_of_unsupported` — the old closure is inside the new one.
* `dead_off_chain` — no node, entry, link or carry along a `ChainSound` chain is dead.
* `dead_gone` — **the review removes everything dead**: dead nodes are not nodes after a valid
  `filterAll`, and dead entries, links and carries are absent from the nodes it keeps.
* `survives_iff_chainS` — under `NoZombieOutsideD` (every node of the pinned state is dead or on a
  full chain), a node survives the filter iff it is on a full chain.

Measured on `SatMachinePure`: the node and entry closure computed by fixpoint iteration equals the
review's removals, node by node and entry by entry, on the three counterexamples to
`LossInClosure`, on `far2`, on two more adversarial formulas and on random seeds 1001 and 7777.
Since it matches the review exactly, `NoZombieOutsideD` says that the review leaves no zombie; what
the closure adds is an order-free inductive form of it.
-/

namespace AbsSat.GraphPath.Model.DeadClosure

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.RemovalClosure
open AbsSat.GraphPath.Model.ChainFabric

/-- What the closure talks about. -/
inductive Item where
  | node (x : PathNodeId)
  | entry (x q : PathNodeId)
  | link (x p : PathNodeId)
  | carry (x p q : PathNodeId)

/-- The removal closure of a pinned state over nodes, owner entries and links. -/
inductive Dead (P : GPathM) : Item → Prop where
  | absent (x q : PathNodeId) (n : PNodeM) (hn : P.node? x = some n) (hq : q ∉ n.owners) :
      Dead P (.entry x q)
  | gowner (x q : PathNodeId) (h0 : 0 ≤ q.id.step) (hk : q.id.step < P.current_step)
      (hq : q ∉ P.gowners) : Dead P (.entry x q)
  | owner (x q : PathNodeId) (h0 : 0 ≤ q.id.step) (hk : q.id.step < P.current_step)
      (h : Dead P (.node q)) : Dead P (.entry x q)
  | parentGap (x q : PathNodeId) (n : PNodeM) (hn : P.node? x = some n) (hstep : 0 < x.id.step)
      (hxk : x.id.step < P.current_step) (h0 : 0 ≤ q.id.step) (hk : q.id.step < P.current_step)
      (h : ∀ p ∈ n.parents, (P.node? p).isSome = true → Dead P (.carry x p q)) :
      Dead P (.entry x q)
  | sonGap (x q : PathNodeId) (hx0 : 0 ≤ x.id.step) (hstep : x.id.step + 1 < P.current_step)
      (h0 : 0 ≤ q.id.step) (hk : q.id.step < P.current_step)
      (h : ∀ c m, P.node? c = some m → x ∈ m.parents → Dead P (.carry x c q)) :
      Dead P (.entry x q)
  | linkNode (x p : PathNodeId) (h : Dead P (.node p)) : Dead P (.link x p)
  | linkFwd (x p : PathNodeId) (h : Dead P (.entry x p)) : Dead P (.link x p)
  | linkBack (x p : PathNodeId) (h : Dead P (.entry p x)) : Dead P (.link x p)
  | carryLink (x p q : PathNodeId) (h : Dead P (.link x p)) : Dead P (.carry x p q)
  | carryEntry (x p q : PathNodeId) (h : Dead P (.entry p q)) : Dead P (.carry x p q)
  | noSupport (x : PathNodeId) (n : PNodeM) (hn : P.node? x = some n) (k : Int)
      (h0 : 0 ≤ k) (hk : k < P.current_step)
      (h : ∀ q ∈ ownersAt n.owners k, Dead P (.entry x q)) : Dead P (.node x)
  | noParent (x : PathNodeId) (n : PNodeM) (hn : P.node? x = some n) (hstep : 0 < x.id.step)
      (h : ∀ p ∈ n.parents, (P.node? p).isSome = true → Dead P (.link x p)) : Dead P (.node x)
  | noSon (x : PathNodeId) (hstep : x.id.step + 1 < P.current_step)
      (h : ∀ c m, P.node? c = some m → x ∈ m.parents → Dead P (.link x c)) : Dead P (.node x)

-- ============================================================
-- The old closure is inside the new one
-- ============================================================

theorem dead_of_unsupported {P : GPathM} {x : PathNodeId} (h : Unsupported P x) :
    Dead P (.node x) := by
  induction h with
  | noSupport x n hn k h0 hk _ ih =>
    refine Dead.noSupport x n hn k h0 hk (fun q hq => ?_)
    have hqs : q.id.step = k := beq_iff_eq.mp (List.mem_filter.mp hq).2
    by_cases hg : q ∈ P.gowners
    · exact Dead.owner x q (by omega) (by omega) (ih q hq hg)
    · exact Dead.gowner x q (by omega) (by omega) hg
  | noParent x n hn hstep _ ih =>
    exact Dead.noParent x n hn hstep (fun p hp hs => Dead.linkNode x p (ih p hp hs))

-- ============================================================
-- Chains never touch the closure
-- ============================================================

/-- What a chain says about each kind of item. -/
def OffChain (P : GPathM) (sel : Int → PathNodeId) : Item → Prop
  | .node x => ∀ i, 0 ≤ i → i < P.current_step → sel i ≠ x
  | .entry x q => ∀ i j, 0 ≤ i → i < P.current_step → 0 ≤ j → j < P.current_step →
      sel i = x → sel j = q → False
  | .link x p => ∀ i j, 0 ≤ i → i < P.current_step → 0 ≤ j → j < P.current_step →
      sel i = x → sel j = p → False
  | .carry x p q => ∀ i j l, 0 ≤ i → i < P.current_step → 0 ≤ j → j < P.current_step →
      0 ≤ l → l < P.current_step → sel i = x → sel j = p → sel l = q → False

/-- **Nothing along a sound chain is dead.** -/
theorem dead_off_chain {P : GPathM} {sel : Int → PathNodeId} (hs : ChainSound P sel)
    {it : Item} (h : Dead P it) : OffChain P sel it := by
  obtain ⟨⟨hnode, hlink⟩, howned, hgow⟩ := hs.chain
  induction h with
  | absent x q n hn hq =>
    intro i j hi0 hi hj0 hj hx hqe
    apply hq
    rw [← hqe]
    rcases int_eq_or_ne j i with hji | hji
    · have hso := hs.self_owned i hi0 hi
      rw [hx] at hso
      simp only [ownersOf, hn] at hso
      rw [hji, hx]
      exact hso
    · have ho := howned j i hj0 hi0 hj hi hji
      rw [hx] at ho
      simp only [ownersOf, hn] at ho
      exact (List.mem_filter.mp ho).1
  | gowner x q h0 hk hq =>
    intro i j _ _ hj0 hj _ hqe
    rw [← hqe] at hq
    exact hq (hgow j hj0 hj)
  | owner x q h0 hk _ ih =>
    intro i j _ _ hj0 hj _ hqe
    exact ih j hj0 hj hqe
  | parentGap x q n hn hstep hxk h0 hk _ ih =>
    intro i j hi0 hi hj0 hj hx hqe
    have hstepi : x.id.step = i := by rw [← hx]; exact (hnode i hi0 hi).2
    have hpar := hlink (i - 1) (by omega) (by omega)
    have hi' : i - 1 + 1 = i := by omega
    rw [hi', hx, hn] at hpar
    have hsome := (hnode (i - 1) (by omega) (by omega)).1
    exact ih (sel (i - 1)) hpar hsome i (i - 1) j hi0 hi (by omega) (by omega) hj0 hj hx rfl hqe
  | sonGap x q hx0 hstep h0 hk _ ih =>
    intro i j hi0 hi hj0 hj hx hqe
    have hstepi : x.id.step = i := by rw [← hx]; exact (hnode i hi0 hi).2
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (hnode (i + 1) (by omega) (by omega)).1
    have hpar := hlink i hi0 (by omega)
    rw [hm, hx] at hpar
    exact ih (sel (i + 1)) m hm hpar i (i + 1) j hi0 hi (by omega) (by omega) hj0 hj hx rfl hqe
  | linkNode x p _ ih =>
    intro i j _ _ hj0 hj _ hpe
    exact ih j hj0 hj hpe
  | linkFwd x p _ ih =>
    intro i j hi0 hi hj0 hj hx hpe
    exact ih i j hi0 hi hj0 hj hx hpe
  | linkBack x p _ ih =>
    intro i j hi0 hi hj0 hj hx hpe
    exact ih j i hj0 hj hi0 hi hpe hx
  | carryLink x p q _ ih =>
    intro i j l hi0 hi hj0 hj _ _ hx hpe _
    exact ih i j hi0 hi hj0 hj hx hpe
  | carryEntry x p q _ ih =>
    intro i j l _ _ hj0 hj hl0 hl _ hpe hqe
    exact ih j l hj0 hj hl0 hl hpe hqe
  | noSupport x n hn k h0 hk _ ih =>
    intro i hi0 hi heq
    have hmem : sel k ∈ ownersAt n.owners k := by
      rcases int_eq_or_ne k i with hki | hki
      · subst hki
        have hso := hs.self_owned k h0 hk
        rw [heq] at hso
        simp only [ownersOf, hn] at hso
        refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr (hnode k h0 hk).2⟩
        rw [heq]
        exact hso
      · have ho := howned k i h0 hi0 hk hi hki
        rw [heq] at ho
        simp only [ownersOf, hn] at ho
        exact ho
    exact ih (sel k) hmem i k hi0 hi h0 hk heq rfl
  | noParent x n hn hstep _ ih =>
    intro i hi0 hi heq
    have hstepi : x.id.step = i := by rw [← heq]; exact (hnode i hi0 hi).2
    have hpar := hlink (i - 1) (by omega) (by omega)
    have hi' : i - 1 + 1 = i := by omega
    rw [hi', heq, hn] at hpar
    have hsome := (hnode (i - 1) (by omega) (by omega)).1
    exact ih (sel (i - 1)) hpar hsome i (i - 1) hi0 hi (by omega) (by omega) heq rfl
  | noSon x hstep _ ih =>
    intro i hi0 hi heq
    have hstepi : x.id.step = i := by rw [← heq]; exact (hnode i hi0 hi).2
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (hnode (i + 1) (by omega) (by omega)).1
    have hpar := hlink i hi0 (by omega)
    rw [hm, heq] at hpar
    exact ih (sel (i + 1)) m hm hpar i (i + 1) hi0 hi (by omega) (by omega) heq rfl

/-- A dead node is on no full chain. -/
theorem dead_not_chainS {P : GPathM} {x : PathNodeId} (h : Dead P (.node x)) : ¬ ChainS P x := by
  intro ⟨sel, hs, i, hi0, hi, heq⟩
  exact dead_off_chain hs h i hi0 hi heq

-- ============================================================
-- The review removes the closure
-- ============================================================

/-- What the filtered state says about each kind of item. -/
def Gone (F : GPathM) : Item → Prop
  | .node x => F.node? x = none
  | .entry x q => ∀ d, F.node? x = some d → q ∉ d.owners
  | .link x p => ∀ d m, F.node? x = some d → F.node? p = some m →
      p ∈ d.owners → x ∈ m.owners → False
  | .carry x p q => ∀ d m, F.node? x = some d → F.node? p = some m →
      p ∈ d.owners → x ∈ m.owners → q ∈ m.owners → False

/-- **The review removes everything dead.** -/
theorem dead_gone (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true) {it : Item}
    (h : Dead (reqs.foldl filterRequire g) it) : Gone (filterAll g reqs) it := by
  have hpr : Pruned (reqs.foldl filterRequire g) (filterAll g reqs) := pruned_review _
  have hs := hpr.step_eq
  have hnd : NodupIds (reqs.foldl filterRequire g) := by
    unfold NodupIds
    rw [foldl_filterRequire_nodes]
    exact Reader.NodupIds_reachable reqOf g hr
  have hgn := GownersNodes.GN_filterAll g reqs (GownersNodes.GN_reachable reqOf g hr)
  have ctx : Threaded.TCtx (filterAll g reqs) := Threaded.tctx_filterAll reqOf g reqs hr hv
  have hsmp : Sons.SMP (filterAll g reqs) := Sons.SMP_reachable_filterAll reqOf g reqs hr
  have hlift : ∀ y d, (filterAll g reqs).node? y = some d →
      ∃ n, (reqs.foldl filterRequire g).node? y = some n ∧ (∀ q ∈ d.owners, q ∈ n.owners) ∧
        (∀ p ∈ d.parents, p ∈ n.parents) := by
    intro y d hd
    obtain ⟨n, hn, hid, ho, hp⟩ := hpr.nodes_derived d (List.mem_of_find?_eq_some hd)
    have hdid : d.id = y := node?_id_eq _ y d hd
    refine ⟨n, ?_, ho, hp⟩
    rw [← hdid, hid]
    exact node?_of_mem hnd n hn
  -- an owner inside the step range of a kept node is a global owner
  have hgown : ∀ x d q, (filterAll g reqs).node? x = some d → q ∈ d.owners →
      0 ≤ q.id.step → q.id.step < (reqs.foldl filterRequire g).current_step →
      q ∈ (filterAll g reqs).gowners := by
    intro x d q hd hq h0 hk
    exact owners_mem_gowners _ d (review_owners_within_gowners (reqs.foldl filterRequire g) hv x d hd)
      q hq (hasStepEntry_of_isValid _ hv _ h0 (by rw [hs]; exact hk))
  -- a kept son of a kept node owns it
  have hsonOwns : ∀ x d p m, (filterAll g reqs).node? x = some d → p ∈ d.parents →
      (filterAll g reqs).node? p = some m → x ∈ m.owners := by
    intro x d p m hd hp hm
    have hxs : d.id ∈ m.sons :=
      hsmp d (List.mem_of_find?_eq_some hd) p hp m (List.mem_of_find?_eq_some hm)
        (node?_id_eq _ p m hm)
    rw [node?_id_eq _ x d hd] at hxs
    exact (ctx.links p m hm).2 x hxs
  induction h with
  | absent x q n hn hq =>
    intro d hd hqd
    obtain ⟨n', hn', ho, _⟩ := hlift x d hd
    have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
    rw [hnn] at ho
    exact hq (ho q hqd)
  | gowner x q h0 hk hq =>
    intro d hd hqd
    exact hq (hpr.gowners_sub q (hgown x d q hd hqd h0 hk))
  | owner x q h0 hk _ ih =>
    intro d hd hqd
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
      ((GownersNodes.hasNode_iff _ q).mp (hgn q (hgown x d q hd hqd h0 hk)))
    have hnone : (filterAll g reqs).node? q = none := ih
    rw [hnone] at hm
    cases hm
  | parentGap x q n hn hstep hxk h0 hk _ ih =>
    intro d hd hqd
    obtain ⟨n', hn', _, hp⟩ := hlift x d hd
    have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
    have hdmem : d ∈ (filterAll g reqs).nodes := List.mem_of_find?_eq_some hd
    have hdid : d.id = x := node?_id_eq _ x d hd
    have hval := ctx.nodeval x d hd
    have hroot : d.id.parent_id ≠ none := ctx.shape.notroot d hdmem (by rw [hdid]; exact hstep)
    have hne := PathExists.parents_ne_nil_of_isValidNode _ d hval hroot
    obtain ⟨p0, rest, hcons⟩ : ∃ p rest, d.parents = p :: rest := by
      cases hl : d.parents with
      | nil => exact absurd hl hne
      | cons a b => exact ⟨a, b, rfl⟩
    have hp0 : p0 ∈ d.parents := by rw [hcons]; exact List.mem_cons_self ..
    obtain ⟨m0, hm0⟩ := Option.isSome_iff_exists.mp
      ((GownersNodes.hasNode_iff _ p0).mp (ctx.shape.pn d hdmem p0 hp0))
    have hk' : q.id.step < (filterAll g reqs).current_step := by rw [hs]; exact hk
    have hent := LocalContradiction.ownersOk_of_isValidNode _ m0 (ctx.nodeval p0 m0 hm0)
      q.id.step h0 hk'
    have hunion := Threaded.hasStepEntry_union _ d.parents p0 m0 hp0 hm0 q.id.step hent
    have hcoh := ctx.cpar x.id.step (mem_intRange (by omega) (by rw [hs]; omega)) x
      (Threaded.mem_line_of_node? _ x d hd) d hd
    have hmemu := Threaded.mem_union_of_coherent _ d d.parents hcoh q hqd hunion
    obtain ⟨p, hpp, m, hm, hqm⟩ := FabricAdd.exists_owner_of_mem_unionOwnersOf _ d.parents q hmemu
    have hpn : p ∈ n.parents := by rw [← hnn]; exact hp p hpp
    obtain ⟨np, hnp, _, _⟩ := hlift p m hm
    have hsomeP : ((reqs.foldl filterRequire g).node? p).isSome = true := by rw [hnp]; rfl
    exact ih p hpn hsomeP d m hd hm ((ctx.links x d hd).1 p hpp) (hsonOwns x d p m hd hpp hm) hqm
  | sonGap x q hx0 hstep h0 hk _ ih =>
    intro d hd hqd
    have hdmem : d ∈ (filterAll g reqs).nodes := List.mem_of_find?_eq_some hd
    have hdid : d.id = x := node?_id_eq _ x d hd
    have hval := ctx.nodeval x d hd
    have hne := Threaded.sons_ne_nil_of_isValidNode _ d hval (by rw [hdid, hs]; omega)
    obtain ⟨c0, rest, hcons⟩ : ∃ c rest, d.sons = c :: rest := by
      cases hl : d.sons with
      | nil => exact absurd hl hne
      | cons a b => exact ⟨a, b, rfl⟩
    have hc0 : c0 ∈ d.sons := by rw [hcons]; exact List.mem_cons_self ..
    obtain ⟨m0, hm0⟩ := Option.isSome_iff_exists.mp
      ((GownersNodes.hasNode_iff _ c0).mp (ctx.sn d hdmem c0 hc0))
    have hk' : q.id.step < (filterAll g reqs).current_step := by rw [hs]; exact hk
    have hent := LocalContradiction.ownersOk_of_isValidNode _ m0 (ctx.nodeval c0 m0 hm0)
      q.id.step h0 hk'
    have hunion := Threaded.hasStepEntry_union _ d.sons c0 m0 hc0 hm0 q.id.step hent
    have hcoh := ctx.cson x.id.step (mem_intRange hx0 (by rw [hs]; omega)) x
      (Threaded.mem_line_of_node? _ x d hd) d hd
    have hmemu := Threaded.mem_union_of_coherent _ d d.sons hcoh q hqd hunion
    obtain ⟨c, hcs, m, hm, hqm⟩ := FabricAdd.exists_owner_of_mem_unionOwnersOf _ d.sons q hmemu
    have hxpar : x ∈ m.parents := by
      have := ctx.pms d hdmem c hcs m (List.mem_of_find?_eq_some hm) (node?_id_eq _ c m hm)
      rw [hdid] at this
      exact this
    obtain ⟨m', hm', _, hparsub⟩ := hlift c m hm
    exact ih c m' hm' (hparsub x hxpar) d m hd hm ((ctx.links x d hd).2 c hcs)
      ((ctx.links c m hm).1 x hxpar) hqm
  | linkNode x p _ ih =>
    intro d m _ hm _ _
    have hnone : (filterAll g reqs).node? p = none := ih
    rw [hnone] at hm
    cases hm
  | linkFwd x p _ ih =>
    intro d m hd _ hpd _
    exact ih d hd hpd
  | linkBack x p _ ih =>
    intro d m _ hm _ hxm
    exact ih m hm hxm
  | carryLink x p q _ ih =>
    intro d m hd hm hpd hxm _
    exact ih d m hd hm hpd hxm
  | carryEntry x p q _ ih =>
    intro d m _ hm _ _ hqm
    exact ih m hm hqm
  | noSupport x n hn k h0 hk _ ih =>
    show (filterAll g reqs).node? x = none
    cases hd : (filterAll g reqs).node? x with
    | none => rfl
    | some d =>
      exfalso
      obtain ⟨n', hn', ho, _⟩ := hlift x d hd
      have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
      have hk' : k < (filterAll g reqs).current_step := by rw [hs]; exact hk
      have hent := LocalContradiction.ownersOk_of_isValidNode _ d (ctx.nodeval x d hd) k h0 hk'
      simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
      obtain ⟨q, hq, hqs⟩ := hent
      have hqn : q ∈ ownersAt n.owners k := by
        refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hqs⟩
        rw [← hnn]
        exact ho q hq
      exact ih q hqn d hd hq
  | noParent x n hn hstep _ ih =>
    show (filterAll g reqs).node? x = none
    cases hd : (filterAll g reqs).node? x with
    | none => rfl
    | some d =>
      exfalso
      obtain ⟨n', hn', _, hp⟩ := hlift x d hd
      have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
      have hdmem : d ∈ (filterAll g reqs).nodes := List.mem_of_find?_eq_some hd
      have hdid : d.id = x := node?_id_eq _ x d hd
      have hroot : d.id.parent_id ≠ none := ctx.shape.notroot d hdmem (by rw [hdid]; exact hstep)
      have hne := PathExists.parents_ne_nil_of_isValidNode _ d (ctx.nodeval x d hd) hroot
      obtain ⟨p, rest, hcons⟩ : ∃ p rest, d.parents = p :: rest := by
        cases hl : d.parents with
        | nil => exact absurd hl hne
        | cons a b => exact ⟨a, b, rfl⟩
      have hpp : p ∈ d.parents := by rw [hcons]; exact List.mem_cons_self ..
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
        ((GownersNodes.hasNode_iff _ p).mp (ctx.shape.pn d hdmem p hpp))
      have hpn : p ∈ n.parents := by rw [← hnn]; exact hp p hpp
      obtain ⟨np, hnp, _, _⟩ := hlift p m hm
      have hsomeP : ((reqs.foldl filterRequire g).node? p).isSome = true := by rw [hnp]; rfl
      exact ih p hpn hsomeP d m hd hm ((ctx.links x d hd).1 p hpp) (hsonOwns x d p m hd hpp hm)
  | noSon x hstep _ ih =>
    show (filterAll g reqs).node? x = none
    cases hd : (filterAll g reqs).node? x with
    | none => rfl
    | some d =>
      exfalso
      have hdmem : d ∈ (filterAll g reqs).nodes := List.mem_of_find?_eq_some hd
      have hdid : d.id = x := node?_id_eq _ x d hd
      have hne := Threaded.sons_ne_nil_of_isValidNode _ d (ctx.nodeval x d hd)
        (by rw [hdid, hs]; omega)
      obtain ⟨c, rest, hcons⟩ : ∃ c rest, d.sons = c :: rest := by
        cases hl : d.sons with
        | nil => exact absurd hl hne
        | cons a b => exact ⟨a, b, rfl⟩
      have hcs : c ∈ d.sons := by rw [hcons]; exact List.mem_cons_self ..
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
        ((GownersNodes.hasNode_iff _ c).mp (ctx.sn d hdmem c hcs))
      have hxpar : x ∈ m.parents := by
        have := ctx.pms d hdmem c hcs m (List.mem_of_find?_eq_some hm) (node?_id_eq _ c m hm)
        rw [hdid] at this
        exact this
      obtain ⟨m', hm', _, hparsub⟩ := hlift c m hm
      exact ih c m' hm' (hparsub x hxpar) d m hd hm ((ctx.links x d hd).2 c hcs)
        ((ctx.links c m hm).1 x hxpar)

-- ============================================================
-- Which nodes the review keeps
-- ============================================================

/-- Every node of the pinned state is dead or on a full chain. -/
def NoZombieOutsideD (P : GPathM) : Prop :=
  ∀ x, (P.node? x).isSome = true → Dead P (.node x) ∨ ChainS P x

/-- **Under `NoZombieOutsideD`, a node survives the filter iff it is on a full chain.** -/
theorem survives_iff_chainS (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true)
    (h : NoZombieOutsideD (reqs.foldl filterRequire g)) (x : PathNodeId)
    (hx : ((reqs.foldl filterRequire g).node? x).isSome = true) :
    ((filterAll g reqs).node? x).isSome = true ↔ ChainS (reqs.foldl filterRequire g) x := by
  constructor
  · intro hs
    rcases h x hx with hd | hc
    · have hnone : (filterAll g reqs).node? x = none := dead_gone reqOf g hr reqs hv hd
      rw [hnone] at hs
      cases hs
    · exact hc
  · intro hc
    exact ReviewNodes.fabric_survives reqOf g hr reqs (Fabric_chains _) hc

/-- The old form implies the new one. -/
theorem noZombieOutsideD_of_noZombieOutside {P : GPathM} (h : NoZombieOutside P) :
    NoZombieOutsideD P :=
  fun x hx => (h x hx).imp dead_of_unsupported id

-- ============================================================
-- No zombies, under the new hypothesis
-- ============================================================

/-- At every valid filter of a reachable state with no zombies, every node of the pinned state is
dead or keeps a full chain. -/
def LossInClosureD (reqOf : NodeId → List NodeId) : Prop :=
  ∀ (g : GPathM) (d : NodeId), Reachable reqOf g → d.step = g.current_step → NoZombies.NoZombie g →
    isValid (filterAll g (reqOf d)) = true → NoZombieOutsideD ((reqOf d).foldl filterRequire g)

/-- The old hypothesis implies the new one. -/
theorem lossInClosureD_of_lossInClosure (reqOf : NodeId → List NodeId)
    (h : NoZombies.LossInClosure reqOf) : LossInClosureD reqOf :=
  fun g d hr hd hnz hv => noZombieOutsideD_of_noZombieOutside (h g d hr hd hnz hv)

/-- **The filter step.** Under `NoZombieOutsideD` for the pinned state, the filtered state has no
zombies. -/
theorem noZombie_filterAll (reqOf : NodeId → List NodeId) (g : GPathM) (hr : Reachable reqOf g)
    (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true)
    (hnz : NoZombieOutsideD (reqs.foldl filterRequire g)) : NoZombies.NoZombie (filterAll g reqs) := by
  intro x hx
  have hpr : Pruned (reqs.foldl filterRequire g) (filterAll g reqs) := pruned_review _
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨m, hm, hid, _, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hn)
  have hnid : n.id = x := node?_id_eq _ x n hn
  have hsomeP : ((reqs.foldl filterRequire g).node? x).isSome = true := by
    have := node?_isSome_of_mem _ m hm
    rw [← hid, hnid] at this
    exact this
  obtain ⟨sel, hs, k, hk0, hk1, hk⟩ := (survives_iff_chainS reqOf g hr reqs hv hnz x hsomeP).mp hx
  have hsf : ChainSound (filterAll g reqs) sel := ChainSound_review _ sel hs
  exact ⟨sel, hsf, k, hk0, by rw [hpr.step_eq]; exact hk1, hk⟩

/-- **Every valid reachable state has no zombies**, under `LossInClosureD`. -/
theorem noZombie_reachable (reqOf : NodeId → List NodeId) (hloss : LossInClosureD reqOf)
    (g : GPathM) (hr : Reachable reqOf g) : isValid g = true → NoZombies.NoZombie g := by
  induction hr with
  | seed d title hstep _ => intro _; exact NoZombies.noZombie_initSeed d title hstep
  | up g d title hstep _ _ hrg ih =>
    intro hv
    have hpr := pruned_filterAll g (reqOf d)
    cases hF : isValid (filterAll g (reqOf d)) with
    | false =>
      simp only [upFiltering, GPathM.up, hF] at hv
      exact absurd hv (by simp [hF])
    | true =>
      have hg : isValid g = true := FabricInduction.isValid_of_pruned hpr hF
      have hFz := noZombie_filterAll reqOf g hrg (reqOf d) hF (hloss g d hrg hstep (ih hg) hF)
      have hshape : upFiltering g (reqOf d) d title = addNode (filterAll g (reqOf d)) d title := by
        simp only [upFiltering, GPathM.up, hF, if_pos]
      rw [hshape]
      have hpos : 0 < (filterAll g (reqOf d)).current_step := by
        rw [hpr.step_eq]; exact NodeInvariant.pos_reachable reqOf g hrg
      have hne : ∃ p, ((filterAll g (reqOf d)).node? p).isSome = true := by
        have hent := hasStepEntry_of_isValid _ hF 0 (Int.le_refl 0) hpos
        simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
        obtain ⟨q, hq, _⟩ := hent
        exact ⟨q, (GownersNodes.hasNode_iff _ q).mp
          (GownersNodes.GN_filterAll g (reqOf d) (GownersNodes.GN_reachable reqOf g hrg) q hq)⟩
      exact NoZombies.noZombie_addNode _ d title hFz (by rw [hpr.step_eq]; exact hstep)
        (Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hrg))
        (MachineOk_of_pruned hpr (SubsetSemantics.MachineOk_reachable reqOf g hrg)) hne
  | join g₁ g₂ hok _ _ ih₁ ih₂ =>
    intro _
    have hok' : okJoin g₁ g₂ = true := hok
    simp only [okJoin, Bool.and_eq_true] at hok
    obtain ⟨⟨_, hv₁⟩, hv₂⟩ := hok
    exact NoZombies.noZombie_join g₁ g₂ hok' (ih₁ hv₁) (ih₂ hv₂)

/-- **At every valid filter, the filter keeps exactly the nodes on full chains through the pins**,
under `LossInClosureD`. -/
theorem filter_keeps_chains (reqOf : NodeId → List NodeId) (hloss : LossInClosureD reqOf)
    (g : GPathM) (hr : Reachable reqOf g) (d : NodeId) (hd : d.step = g.current_step)
    (hv : isValid (filterAll g (reqOf d)) = true) (x : PathNodeId)
    (hx : (((reqOf d).foldl filterRequire g).node? x).isSome = true) :
    ((filterAll g (reqOf d)).node? x).isSome = true ↔ ChainS ((reqOf d).foldl filterRequire g) x :=
  survives_iff_chainS reqOf g hr (reqOf d) hv
    (hloss g d hr hd (noZombie_reachable reqOf hloss g hr
      (FabricInduction.isValid_of_pruned (pruned_filterAll g (reqOf d)) hv)) hv) x hx

/-- info: 'AbsSat.GraphPath.Model.DeadClosure.dead_off_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dead_off_chain

/-- info: 'AbsSat.GraphPath.Model.DeadClosure.dead_gone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dead_gone

/-- info: 'AbsSat.GraphPath.Model.DeadClosure.survives_iff_chainS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms survives_iff_chainS

end AbsSat.GraphPath.Model.DeadClosure
