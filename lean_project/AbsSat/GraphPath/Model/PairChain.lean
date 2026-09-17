-- lean_project/AbsSat/GraphPath/Model/PairChain.lean
import AbsSat.GraphPath.Model.PinExactSome
import AbsSat.GraphPath.Model.NodeInvariant
import AbsSat.GraphPath.Model.JoinSound

/-!
# Every owner pair on a path: the pins are exact

The author's view of the machine: after each UP, the filters and the review with all its phases leave
a well-built graph in which **every node belongs to at least one path**; a node that did not would be
invalid and removed. This module states the pairwise form of that property and proves what it gives
the reader.

* `PairChain g` — every owner pair of a node lies on a full chain of the tables (`ChainSound`): one
  node per step, pairwise owners, global owners, linked parent to son. With `w = x` it contains
  "every node lies on a chain".
* **`pinExact_of_pairChain`** — `PairChain` makes every pin exact: a slice member and its carrier
  lie on a chain; the chain respects the pin, so it survives the pin and the whole aggressive review
  (`ChainSound_filterAllAgg`, the no-solution-lost result), and the member with it.
* **`sat_of_pairChain`** — the soundness of the Improves verdict when `PairChain` holds at every state
  the reader visits.

* `pairChain_join`, `pairChain_addNode` — joins and UP keep `PairChain`.
* `FilterKeepsPairChain` — **the open lemma**: a pin with the whole aggressive review keeps it.
* **`sat_of_pairChain_base`** — the verdict from `PairChain` on the base state and the open lemma.

Measured by the probe `helly chains` (report v123): no owner pair without a chain in any state
measured, over every line of the machine and reader walks.
-/

namespace AbsSat.GraphPath.Model.PairChain

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PinExact
open AbsSat.GraphPath.Model.PinExactBoundary

/-- **Every owner pair of a node lies on a full chain of the tables.** -/
def PairChain (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → ∀ w ∈ n.owners, 0 ≤ w.id.step → w.id.step < g.current_step →
    ∃ sel, ChainSound g sel ∧ sel x.id.step = x ∧ sel w.id.step = w

/-- **`PairChain` makes every pin exact.** -/
theorem pinExact_of_pairChain (g : GPathM) (hnd : NodupIds g) (hsnn : SelfOwn.SNN g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hpc : PairChain g) (mid : NodeId)
    (h0 : 0 ≤ mid.step) (h1 : mid.step < g.current_step) : PinExact g mid := by
  intro n hn ⟨q, hq, hqid⟩
  have hx : g.node? n.id = some n := node?_of_mem hnd n hn
  obtain ⟨sel, hs, hsx, hsq⟩ := hpc n.id n hx q hq (by rw [hqid]; exact h0) (by rw [hqid]; exact h1)
  have hreqs : ∀ req ∈ [mid], 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req := by
    intro req hreq _ _
    rw [List.mem_singleton.mp hreq, ← hqid, hsq]
  have hcs := ChainSound_filterAllAgg g [mid] sel hs hreqs
  have hstep : (filterAllAgg g [mid]).current_step = g.current_step := (pruned_filterAllAgg g [mid]).step_eq
  have hmem := hcs.chain.2.2 n.id.id.step (hsnn n hn) (by rw [hstep]; exact hbelow n hn)
  rwa [hsx] at hmem

/-- **Soundness of the Improves verdict when every reader state has `PairChain`.** -/
theorem sat_of_pairChain (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (hpc : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true → PairChain g) :
    Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  have hR₀ : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
  refine sat_of_pinExactAgg φ hwf kv hkv hv (fun g hF hvg p hp => ?_)
  have hR : ReadableAgg g := readableAgg_of_readFrom _ hR₀ g hF
  have rc := RCtx_of_readableAgg g hR
  obtain ⟨m, hm', hmid⟩ := rc.gn p hp
  have hb0 := rc.snn m hm'
  have hb1 := rc.below m hm'
  rw [hmid] at hb0 hb1
  exact pinExact_of_pairChain g rc.nodup rc.snn rc.below (hpc g hF hvg) p.id hb0 hb1

/-- info: 'AbsSat.GraphPath.Model.PairChain.sat_of_pairChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pairChain

-- ============================================================
-- Growth keeps it
-- ============================================================

/-- **Join keeps `PairChain`**: an owner of a joined node comes from one side, where a chain carries
the pair, and chains of either side are chains of the join. -/
theorem pairChain_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (hnd₁ : NodupIds g₁)
    (hnd₂ : NodupIds g₂) (h₁ : PairChain g₁) (h₂ : PairChain g₂) : PairChain (join g₁ g₂) := by
  intro x n hn w hw h0 h1
  have hmem := List.mem_of_find?_eq_some hn
  have hid := node?_id_eq _ x n hn
  have hcs₁ : (join g₁ g₂).current_step = g₁.current_step := rfl
  have hcs₂ : g₂.current_step = g₁.current_step := SymTriReview.okJoin_step g₁ g₂ hok
  rw [hcs₁] at h1
  rcases ParentOwners.mem_join_nodes' hmem with ⟨a, ha, hida, hown⟩ | hn₂
  · rcases hown w hw with hwa | ⟨b, hb, hbid, hwb⟩
    · have hxa : g₁.node? x = some a := by rw [← hid, hida]; exact node?_of_mem hnd₁ a ha
      obtain ⟨sel, hs, hsx, hsw⟩ := h₁ x a hxa w hwa h0 h1
      exact ⟨sel, ChainSound_join_left g₁ g₂ sel hs, hsx, hsw⟩
    · have hxb : g₂.node? x = some b := by rw [← hid, hida, ← hbid]; exact node?_of_mem hnd₂ b hb
      obtain ⟨sel, hs, hsx, hsw⟩ := h₂ x b hxb w hwb h0 (by rw [hcs₂]; exact h1)
      exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hs, hsx, hsw⟩
  · have hxn : g₂.node? x = some n := by rw [← hid]; exact node?_of_mem hnd₂ n hn₂
    obtain ⟨sel, hs, hsx, hsw⟩ := h₂ x n hxn w hw h0 (by rw [hcs₂]; exact h1)
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hs, hsx, hsw⟩

/-- **UP keeps `PairChain`**: the new node owns every global owner and is owned by every node, and any
chain extends through it (`ChainSound_addNode`). -/
theorem pairChain_addNode (g : GPathM) (d : NodeId) (title : String) (hd : d.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hmok : MachineOk g)
    (hself : Ownership.SelfOwned g) (hgn : GownersNodes.GN g) (hnd : NodupIds g)
    (hsnn : SelfOwn.SNN g) (hinh : ∃ sel, ChainSound g sel)
    (hownb : ∀ n ∈ g.nodes, ∀ w ∈ n.owners, w.id.step < g.current_step)
    (h : PairChain g) : PairChain (addNode g d title) := by
  intro x n hn w hw h0 h1
  have hmem := List.mem_of_find?_eq_some hn
  have hid := node?_id_eq _ x n hn
  rw [addNode_current] at h1
  have hnewstep : (newPid g d).id.step = g.current_step := hd
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · obtain ⟨n₁, hn₁, hEq⟩ := List.mem_map.mp hl
    have hx1 : x = n₁.id := by rw [← hid, ← hEq, upMap_id]
    have hxs : x.id.step < g.current_step := by rw [hx1]; exact hbelow n₁ hn₁
    have hxn : g.node? x = some n₁ := by rw [hx1]; exact node?_of_mem hnd n₁ hn₁
    rw [← hEq, upMap_owners] at hw
    rcases List.mem_append.mp hw with hwo | hwn
    · have hws := hownb n₁ hn₁ w hwo
      obtain ⟨sel, hs, hsx, hsw⟩ := h x n₁ hxn w hwo h0 hws
      exact ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hs,
        by rw [extend_below g d sel _ hxs]; exact hsx, by rw [extend_below g d sel _ hws]; exact hsw⟩
    · have hwnew : w = newPid g d := List.mem_singleton.mp hwn
      obtain ⟨sel, hs, hsx, _⟩ := h x n₁ hxn x (hself x n₁ hxn) (by rw [hx1]; exact hsnn n₁ hn₁) hxs
      refine ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hs,
        by rw [extend_below g d sel _ hxs]; exact hsx, ?_⟩
      rw [hwnew, hnewstep, extend_top]
  · have hnew : n = addOwner (newPid g d) (upNode g d title) := List.mem_singleton.mp hr
    have hxnew : x = newPid g d := by rw [← hid, hnew]; rfl
    have hw' : w ∈ g.gowners ++ [newPid g d] := by rw [hnew] at hw; exact hw
    rcases List.mem_append.mp hw' with hwg | hwn
    · obtain ⟨m, hm, hmid⟩ := hgn w hwg
      have hwm : g.node? w = some m := by rw [← hmid]; exact node?_of_mem hnd m hm
      have hws : w.id.step < g.current_step := by rw [← hmid]; exact hbelow m hm
      obtain ⟨sel, hs, hsw, _⟩ := h w m hwm w (hself w m hwm) h0 hws
      refine ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hs, ?_,
        by rw [extend_below g d sel _ hws]; exact hsw⟩
      rw [hxnew, hnewstep, extend_top]
    · have hwnew : w = newPid g d := List.mem_singleton.mp hwn
      obtain ⟨sel, hs⟩ := hinh
      refine ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hs, ?_, ?_⟩
      · rw [hxnew, hnewstep, extend_top]
      · rw [hwnew, hnewstep, extend_top]

/-- info: 'AbsSat.GraphPath.Model.PairChain.pairChain_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairChain_addNode

-- ============================================================
-- The author's claim, as one lemma
-- ============================================================

/-- **The open lemma**: a pin followed by the whole aggressive review keeps every owner pair on a
chain, whenever it leaves the state valid. (The author: the filter and the review with all its
phases leave every node, and here every owner pair, on some path.) -/
def FilterKeepsPairChain : Prop :=
  ∀ g reqs, ReadableAgg g → PairChain g → isValid (filterAllAgg g reqs) = true →
    PairChain (filterAllAgg g reqs)

/-- **A pin fixes the whole line it pins.** In a valid pinned state every node on the pinned step
carries the pinned map node: a node owns itself, so it is a global owner, and the pin has dropped
every global owner of that step with another map node.

So a chain of the *pinned* state respects the pin by itself: there is nothing to steer. What
`FilterKeepsPairChain` needs is not a chain steered through the pin but a chain of `g` carrying the
pair that **survives** the pin — the no-solution-lost property, one pair at a time. -/
theorem node_id_of_pin (g : GPathM) (reqs : List NodeId) (ctx : Pinned.Ctx (filterAllAgg g reqs))
    (hbelow : ∀ n ∈ (filterAllAgg g reqs).nodes, n.id.id.step < (filterAllAgg g reqs).current_step)
    (hnd : NodupIds (filterAllAgg g reqs)) (req : NodeId) (hreq : req ∈ reqs) (h0 : 0 ≤ req.step)
    (n : PNodeM) (hn : n ∈ (filterAllAgg g reqs).nodes) (hstep : n.id.id.step = req.step) :
    n.id.id = req := by
  have hx : (filterAllAgg g reqs).node? n.id = some n := node?_of_mem hnd n hn
  have hself : n.id ∈ n.owners := ctx.self n.id n hx
  have hgow : n.id ∈ (filterAllAgg g reqs).gowners :=
    ctx.ownGow n.id n hx n.id hself (by rw [hstep]; exact h0) (hbelow n hn)
  have hpre : n.id ∈ (reqs.foldl filterRequire g).gowners :=
    (pruned_reviewAgg (reqs.foldl filterRequire g)).gowners_sub _ hgow
  rcases (LocalContradiction.mem_foldl_filterRequire reqs _ n.id hpre).2 req hreq with h | h
  · exact absurd hstep h
  · exact h

/-- **The open lemma reduces to steering the chain through the pins.** A chain of `g` that
respects the pins survives the filter and the whole aggressive review (`ChainSound_filterAllAgg`,
the no-solution-lost result), so all `FilterKeepsPairChain` needs is that the chain carrying an
owner pair of the *filtered* state can be chosen to pass through the pinned map nodes.

This is where `ParentWitness` bites: below a node with a single parent the chain is not a choice
at all (`ParentWitness.owners_below_unique` — the past of such a node is a unique path, forced by
the map node its identifier names), so the steering is free there. What is left is the merged
nodes, those whose parents come from several grandparent histories. -/
theorem pairChain_of_steered (g : GPathM) (reqs : List NodeId)
    (hsteer : ∀ x n, (filterAllAgg g reqs).node? x = some n → ∀ w ∈ n.owners,
      0 ≤ w.id.step → w.id.step < (filterAllAgg g reqs).current_step →
      ∃ sel, ChainSound g sel ∧ sel x.id.step = x ∧ sel w.id.step = w ∧
        ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req) :
    PairChain (filterAllAgg g reqs) := by
  intro x n hx w hw h0 h1
  obtain ⟨sel, hs, hsx, hsw, hreqs⟩ := hsteer x n hx w hw h0 h1
  exact ⟨sel, ChainSound_filterAllAgg g reqs sel hs hreqs, hsx, hsw⟩

/-- info: 'AbsSat.GraphPath.Model.PairChain.pairChain_of_steered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairChain_of_steered

/-- info: 'AbsSat.GraphPath.Model.PairChain.node_id_of_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms node_id_of_pin

/-- `PairChain` along the reader, from the base state, given the open lemma. -/
theorem pairChain_readFrom (hkeep : FilterKeepsPairChain) (g₀ : GPathM) (hR₀ : ReadableAgg g₀)
    (h₀ : PairChain g₀) : ∀ g, ReadFrom g₀ g → isValid g = true → PairChain g := by
  intro g hF
  induction hF with
  | start => intro _; exact h₀
  | pin g' mid hF' hv' ih =>
    intro hv
    exact hkeep g' [mid] (readableAgg_of_readFrom g₀ hR₀ g' hF') (ih hv') hv

/-- **Soundness of the Improves verdict from `PairChain` on the base state and the open lemma.** -/
theorem sat_of_pairChain_base (hkeep : FilterKeepsPairChain) (φ : Cnf) (hwf : WF φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) (h₀ : PairChain (filterAllAgg kv.2 [])) :
    Satisfiable φ := by
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  exact sat_of_pairChain φ hwf kv hkv hv
    (pairChain_readFrom hkeep _ ⟨kv.2, [], hm.rctx, rfl⟩ h₀)

/-- info: 'AbsSat.GraphPath.Model.PairChain.sat_of_pairChain_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pairChain_base

end AbsSat.GraphPath.Model.PairChain
