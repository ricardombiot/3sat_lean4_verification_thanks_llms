-- lean_project/AbsSat/GraphPath/Model/ParentOwners.lean
import AbsSat.GraphPath.Model.NodeInvariant
import AbsSat.GraphPath.Model.Certifies
import AbsSat.GraphPath.Model.Join

/-!
# What a node's parent id says about its owners

A path node `n` records its parent's map node in `n.id.parent_id`. The owners table agrees with that
record, in every state the machine builds (`ParentInv_reachable`):

* `po` (P1) — an owner one step below `n` has the parent's map node as id;
* `ps` — the parent's map node sits exactly one step below `n`;
* `kp` — the global owners of a state whose key is `p` satisfy `p`'s requirements;
* `pr` (P2) — an owner of `n` at the step of a requirement of its parent's map node is that
  requirement;
* `rp` — a requirement of `n`'s own map node at its parent's step is the parent's map node.

`L1` (`ReqFiltered`) says the same about a node's own map node; `pr` is its version for the parent.
Both come from `addNode`: the new node is handed the global owners, whose top step carries the key
(`TopKey`) and whose requirement steps were pinned by the filter that preceded it.

Measured on `SatMachinePure` (seeds 1001, 7777, 31337, 90210, 9,885 kept and filtered states):
P1 holds in 215,324 checks and P2 in 265,951, with no exception.
-/

namespace AbsSat.GraphPath.Model.ParentOwners

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

-- ============================================================
-- Membership through addNode and join
-- ============================================================

theorem mem_addNode_nodes {F : GPathM} {d : NodeId} {title : String} {n' : PNodeM}
    (hn : n' ∈ (addNode F d title).nodes) :
    (∃ m ∈ F.nodes, n' = upMap F d m) ∨ n' = addOwner (newPid F d) (upNode F d title) := by
  rw [addNode_nodes] at hn
  rcases List.mem_append.mp hn with h | h
  · obtain ⟨m, hm, heq⟩ := List.mem_map.mp h
    exact Or.inl ⟨m, hm, heq.symm⟩
  · exact Or.inr (List.mem_singleton.mp h)

theorem mem_join_nodes' {g₁ g₂ : GPathM} {n : PNodeM} (hn : n ∈ (join g₁ g₂).nodes) :
    (∃ a ∈ g₁.nodes, n.id = a.id ∧
      ∀ q ∈ n.owners, q ∈ a.owners ∨ ∃ b ∈ g₂.nodes, b.id = a.id ∧ q ∈ b.owners) ∨
    n ∈ g₂.nodes := by
  have hj : (join g₁ g₂).nodes =
      g₁.nodes.map (fun n => match g₂.node? n.id with | some m => mergeNode n m | none => n) ++
        g₂.nodes.filter (fun m => (g₁.node? m.id).isNone) := rfl
  rw [hj] at hn
  rcases List.mem_append.mp hn with h | h
  · obtain ⟨a, ha, heq⟩ := List.mem_map.mp h
    refine Or.inl ⟨a, ha, ?_⟩
    cases h2 : g₂.node? a.id with
    | none =>
      rw [h2] at heq
      have hna : n = a := heq.symm
      subst hna
      exact ⟨rfl, fun q hq => Or.inl hq⟩
    | some m =>
      rw [h2] at heq
      have hnm : n = mergeNode a m := heq.symm
      subst hnm
      refine ⟨rfl, fun q hq => ?_⟩
      have hq' : q ∈ a.owners ++ m.owners.filter (fun q => !a.owners.contains q) := hq
      rcases List.mem_append.mp hq' with hqa | hqm
      · exact Or.inl hqa
      · exact Or.inr ⟨m, List.mem_of_find?_eq_some h2, node?_id_eq g₂ a.id m h2,
          (List.mem_filter.mp hqm).1⟩
  · exact Or.inr (List.mem_filter.mp h).1

-- ============================================================
-- The invariant
-- ============================================================

section Inv

variable (reqOf : NodeId → List NodeId)

structure ParentInv (g : GPathM) : Prop where
  po : ∀ n ∈ g.nodes, ∀ q ∈ n.owners, q.id.step + 1 = n.id.id.step → some q.id = n.id.parent_id
  ps : ∀ n ∈ g.nodes, ∀ p, n.id.parent_id = some p → p.step + 1 = n.id.id.step
  kp : ∀ p, g.map_parent = some p → ∀ q ∈ g.gowners, ∀ req ∈ reqOf p,
    q.id.step = req.step → q.id = req
  pr : ∀ n ∈ g.nodes, ∀ p, n.id.parent_id = some p → ∀ req ∈ reqOf p, ∀ q ∈ n.owners,
    q.id.step = req.step → q.id = req
  rp : ∀ n ∈ g.nodes, ∀ p, n.id.parent_id = some p → ∀ req ∈ reqOf n.id.id,
    req.step = p.step → req = p

theorem ParentInv_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : ParentInv reqOf g) :
    ParentInv reqOf g' where
  po := fun n' hn' q hq hs => by
    obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived n' hn'
    rw [hid] at hs ⊢
    exact h.po n hn q (hown q hq) hs
  ps := fun n' hn' p hp => by
    obtain ⟨n, hn, hid, _, _⟩ := hpr.nodes_derived n' hn'
    rw [hid] at hp ⊢
    exact h.ps n hn p hp
  kp := fun p hp q hq req hreq hs => by
    rw [hpr.map_parent_eq] at hp
    exact h.kp p hp q (hpr.gowners_sub q hq) req hreq hs
  pr := fun n' hn' p hp req hreq q hq hs => by
    obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived n' hn'
    rw [hid] at hp
    exact h.pr n hn p hp req hreq q (hown q hq) hs
  rp := fun n' hn' p hp req hreq hs => by
    obtain ⟨n, hn, hid, _, _⟩ := hpr.nodes_derived n' hn'
    rw [hid] at hp hreq
    exact h.rp n hn p hp req hreq hs

theorem ParentInv_addNode (hback : ∀ x, ∀ r ∈ reqOf x, r.step < x.step)
    (F : GPathM) (d : NodeId) (title : String) (h : ParentInv reqOf F)
    (hd : d.step = F.current_step) (hbelow : ∀ n ∈ F.nodes, n.id.id.step < F.current_step)
    (htk : NodeInvariant.TopKey F) (hv : isValid F = true) (hpos : 0 < F.current_step)
    (hpin : ∀ q ∈ F.gowners, ∀ req ∈ reqOf d, q.id.step = req.step → q.id = req) :
    ParentInv reqOf (addNode F d title) := by
  have hkey : ∀ p, F.map_parent = some p → p.step + 1 = F.current_step := by
    intro p hp
    have hent := hasStepEntry_of_isValid F hv (F.current_step - 1) (by omega) (by omega)
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
    obtain ⟨q, hq, hqs⟩ := hent
    have htop := htk.2.2 q hq hqs
    rw [hp] at htop
    have hpq : p = q.id := Option.some.inj htop
    rw [hpq]
    omega
  have hnew : (addOwner (newPid F d) (upNode F d title)).id.id.step = d.step := rfl
  have hnewp : (newPid F d).id.step = d.step := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n' hn' q hq hs
    rcases mem_addNode_nodes hn' with ⟨m, hm, rfl⟩ | rfl
    · rw [upMap_owners] at hq
      rw [upMap_id] at hs ⊢
      rcases List.mem_append.mp hq with hq | hq
      · exact h.po m hm q hq hs
      · rw [List.mem_singleton.mp hq] at hs
        have := hbelow m hm
        omega
    · have hq' : q ∈ F.gowners ++ [newPid F d] := hq
      rcases List.mem_append.mp hq' with hq | hq
      · exact (htk.2.2 q hq (by omega)).symm
      · rw [List.mem_singleton.mp hq] at hs
        omega
  · intro n' hn' p hp
    rcases mem_addNode_nodes hn' with ⟨m, hm, rfl⟩ | rfl
    · rw [upMap_id] at hp ⊢
      exact h.ps m hm p hp
    · have hp' : F.map_parent = some p := hp
      have := hkey p hp'
      omega
  · intro p hp q hq req hreq hs
    have hdp : d = p := Option.some.inj hp
    subst hdp
    have hq' : q ∈ F.gowners ++ [newPid F d] := hq
    rcases List.mem_append.mp hq' with hq | hq
    · exact hpin q hq req hreq hs
    · rw [List.mem_singleton.mp hq] at hs
      have := hback d req hreq
      omega
  · intro n' hn' p hp req hreq q hq hs
    rcases mem_addNode_nodes hn' with ⟨m, hm, rfl⟩ | rfl
    · rw [upMap_id] at hp
      rw [upMap_owners] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact h.pr m hm p hp req hreq q hq hs
      · exfalso
        rw [List.mem_singleton.mp hq] at hs
        have h1 := h.ps m hm p hp
        have h2 := hback p req hreq
        have h3 := hbelow m hm
        omega
    · have hp' : F.map_parent = some p := hp
      have hq' : q ∈ F.gowners ++ [newPid F d] := hq
      rcases List.mem_append.mp hq' with hq | hq
      · exact h.kp p hp' q hq req hreq hs
      · exfalso
        rw [List.mem_singleton.mp hq] at hs
        have h1 := hkey p hp'
        have h2 := hback p req hreq
        omega
  · intro n' hn' p hp req hreq hs
    rcases mem_addNode_nodes hn' with ⟨m, hm, rfl⟩ | rfl
    · rw [upMap_id] at hp hreq
      exact h.rp m hm p hp req hreq hs
    · have hp' : F.map_parent = some p := hp
      have hreq' : req ∈ reqOf d := hreq
      have hent := hasStepEntry_of_isValid F hv (F.current_step - 1) (by omega) (by omega)
      simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
      obtain ⟨q, hq, hqs⟩ := hent
      have htop := htk.2.2 q hq hqs
      rw [hp'] at htop
      have hpq : p = q.id := Option.some.inj htop
      have hqreq : q.id = req := hpin q hq req hreq' (by rw [← hpq]; omega)
      rw [← hqreq, hpq]

theorem ParentInv_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : ParentInv reqOf g₁) (h₂ : ParentInv reqOf g₂) : ParentInv reqOf (join g₁ g₂) := by
  have hmp : g₁.map_parent = g₂.map_parent := by
    simp only [okJoin, Bool.and_eq_true, beq_iff_eq] at hok
    exact hok.1.1.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn q hq hs
    rcases mem_join_nodes' hn with ⟨a, ha, hid, hown⟩ | hn2
    · rw [hid] at hs ⊢
      rcases hown q hq with hqa | ⟨b, hb, hbid, hqb⟩
      · exact h₁.po a ha q hqa hs
      · rw [← hbid] at hs ⊢
        exact h₂.po b hb q hqb hs
    · exact h₂.po n hn2 q hq hs
  · intro n hn p hp
    rcases mem_join_nodes' hn with ⟨a, ha, hid, _⟩ | hn2
    · rw [hid] at hp ⊢
      exact h₁.ps a ha p hp
    · exact h₂.ps n hn2 p hp
  · intro p hp q hq req hreq hs
    have hp1 : g₁.map_parent = some p := hp
    have hq' : q ∈ g₁.gowners ++ g₂.gowners.filter (fun x => !g₁.gowners.contains x) := hq
    rcases List.mem_append.mp hq' with hq1 | hq2
    · exact h₁.kp p hp1 q hq1 req hreq hs
    · exact h₂.kp p (by rw [← hmp]; exact hp1) q (List.mem_filter.mp hq2).1 req hreq hs
  · intro n hn p hp req hreq q hq hs
    rcases mem_join_nodes' hn with ⟨a, ha, hid, hown⟩ | hn2
    · rw [hid] at hp
      rcases hown q hq with hqa | ⟨b, hb, hbid, hqb⟩
      · exact h₁.pr a ha p hp req hreq q hqa hs
      · rw [← hbid] at hp
        exact h₂.pr b hb p hp req hreq q hqb hs
    · exact h₂.pr n hn2 p hp req hreq q hq hs
  · intro n hn p hp req hreq hs
    rcases mem_join_nodes' hn with ⟨a, ha, hid, _⟩ | hn2
    · rw [hid] at hp hreq
      exact h₁.rp a ha p hp req hreq hs
    · exact h₂.rp n hn2 p hp req hreq hs

theorem ParentInv_initSeed (hback : ∀ x, ∀ r ∈ reqOf x, r.step < x.step)
    (d : NodeId) (title : String) (hd : d.step = 0) : ParentInv reqOf (initSeed d title) := by
  have hseed : initSeed d title = addNode empty d title := rfl
  have hnode : ∀ n ∈ (initSeed d title).nodes, n = addOwner (newPid empty d) (upNode empty d title) := by
    intro n hn
    rw [hseed] at hn
    rcases mem_addNode_nodes hn with ⟨m, hm, _⟩ | h
    · exact absurd hm List.not_mem_nil
    · exact h
  have hnewp : (newPid empty d).id.step = d.step := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn q hq hs
    rw [hnode n hn] at hq hs
    have hq' : q ∈ empty.gowners ++ [newPid empty d] := hq
    rcases List.mem_append.mp hq' with hq | hq
    · exact absurd hq List.not_mem_nil
    · rw [List.mem_singleton.mp hq] at hs
      have : (addOwner (newPid empty d) (upNode empty d title)).id.id.step = d.step := rfl
      omega
  · intro n hn p hp
    rw [hnode n hn] at hp
    exact absurd hp (by simp [newPid, empty, addOwner, upNode])
  · intro p hp q hq req hreq hs
    have hdp : d = p := Option.some.inj hp
    subst hdp
    have hq' : q ∈ empty.gowners ++ [newPid empty d] := hq
    rcases List.mem_append.mp hq' with hq | hq
    · exact absurd hq List.not_mem_nil
    · rw [List.mem_singleton.mp hq] at hs
      have := hback d req hreq
      omega
  · intro n hn p hp
    rw [hnode n hn] at hp
    exact absurd hp (by simp [newPid, empty, addOwner, upNode])
  · intro n hn p hp
    rw [hnode n hn] at hp
    exact absurd hp (by simp [newPid, empty, addOwner, upNode])

/-- **The owners table agrees with the parent record in every state the machine builds.** -/
theorem ParentInv_reachable (hback : ∀ x, ∀ r ∈ reqOf x, r.step < x.step)
    (g : GPathM) (h : Reachable reqOf g) : ParentInv reqOf g := by
  induction h with
  | seed d title hstep _ => exact ParentInv_initSeed reqOf hback d title hstep
  | up g d title hstep _ _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    have hF := ParentInv_of_pruned reqOf hpr ih
    dsimp only [GPathM.upFiltering, GPathM.up]
    split
    · next hv =>
      exact ParentInv_addNode reqOf hback _ d title hF (by rw [hpr.step_eq]; exact hstep)
        (Certifies.nodes_below_of_pruned hpr (steps_below_current reqOf hr))
        (NodeInvariant.TopKey_of_pruned hpr (NodeInvariant.TopKey_reachable reqOf g hr))
        hv (by rw [hpr.step_eq]; exact NodeInvariant.pos_reachable reqOf g hr)
        (fun q hq req hreq hs => filterAll_cleans_gowner g (reqOf d) req q hreq hq hs)
    · exact hF
  | join g₁ g₂ hok _ _ ih₁ ih₂ => exact ParentInv_join reqOf g₁ g₂ hok ih₁ ih₂

end Inv

/-- info: 'AbsSat.GraphPath.Model.ParentOwners.ParentInv_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ParentInv_reachable

end AbsSat.GraphPath.Model.ParentOwners
