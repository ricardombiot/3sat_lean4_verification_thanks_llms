-- lean_project/AbsSat/GraphPath/Model/BranchRun.lean
import AbsSat.GraphPath.Model.EmbeddedSupport

/-!
# Branches of the Improves machine, and how a branch sits inside the whole run

The global view (reports v124–v125): the machine builds, line by line, the set of partial paths, and
pinning a node of a final state gives exactly the state built on that node's **branch**.

## Branches

* `restrictLine P k line` — at line `k`, keep only the states whose key agrees with every pin of `P`
  on step `k`.
* `branchSteps`, **`branchRun φ P`** — the Improves driver (`pureAdvanceW`) restricted at every line.
  With no pins it is the machine itself (`branchRun_nil`).

## A branch stays inside the whole construction, state by state

`EmbeddedSupport.Embedded B G`: `B` sits inside `G`. It is kept by every operation one send performs:

* `embedded_of_pruned` — narrowing `B`;
* `embedded_filterRequire`, `embedded_filterWeakAll` — the same filters on both sides;
* **`embedded_filterAllAgg`** — the pins and the whole aggressive review on both sides, as soon as the
  reviewed `B` is valid: its own tables are a support relation inside the filtered `G`
  (`sup_of_embedded`), so they survive `G`'s review, links included (`Sup.link`);
* **`embedded_addNode`**, `embedded_up` — the UP of the same map node on both sides;
* `embedded_of_grown` — a join that adds to the outer state only (`Grown`);
* **`embedded_join`** — joining two inner states inside the join of the outer ones.

The line-level induction (the order of sends and joins inside a line) comes next.
-/

namespace AbsSat.GraphPath.Model.BranchRun

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.AnchoredSurvive
open AbsSat.GraphPath.Model.AggFixpoint
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphMap.CnfMap (stepCount)

-- ============================================================
-- Branches
-- ============================================================

/-- At line `k`, keep the states whose key agrees with every pin of `P` on step `k`. -/
def restrictLine (P : List NodeId) (k : Int) (line : PureLine) : PureLine :=
  line.filter (fun kv => P.all (fun r => r.step != k || kv.1 == r))

/-- The driver, restricted at every line it produces. -/
def branchSteps (φ : Cnf) (P : List NodeId) : Nat → Int → PureLine → PureLine
  | 0, _, line => line
  | n + 1, k, line => branchSteps φ P n (k + 1) (restrictLine P (k + 1) (pureAdvanceW φ line))

/-- **The branch of the pins `P`**: the Improves machine built only on the partial paths that agree
with `P`. -/
def branchRun (φ : Cnf) (P : List NodeId) : PureLine :=
  branchSteps φ P (stepCount φ - 1).toNat 0 (restrictLine P 0 (pureInit φ))

theorem restrictLine_nil (k : Int) (line : PureLine) : restrictLine [] k line = line := by
  simp [restrictLine]

theorem branchSteps_nil (φ : Cnf) : ∀ (n : Nat) (k : Int) (line : PureLine),
    branchSteps φ [] n k line = pureStepsW φ n line := by
  intro n
  induction n with
  | zero => intro k line; rfl
  | succ n ih =>
    intro k line
    simp only [branchSteps, pureStepsW, restrictLine_nil]
    exact ih _ _

/-- With no pins, the branch is the machine. -/
theorem branchRun_nil (φ : Cnf) : branchRun φ [] = pureRunW φ := by
  simp only [branchRun, pureRunW, restrictLine_nil, branchSteps_nil]

-- ============================================================
-- Embedded, operation by operation
-- ============================================================

theorem mem_of_pruned {B B' : GPathM} (hpr : Pruned B B') {p : PathNodeId} (h : Mem B' p) : Mem B p := by
  obtain ⟨m', hm'⟩ := h
  obtain ⟨m, hm, hid, _, _⟩ := hpr.nodes_derived m' (List.mem_of_find?_eq_some hm')
  have hs := node?_isSome_of_mem B m hm
  rw [← hid, node?_id_eq _ p m' hm'] at hs
  exact Option.isSome_iff_exists.mp hs

/-- Narrowing the inner state keeps it inside. -/
theorem embedded_of_pruned {B B' G : GPathM} (hpr : Pruned B B') (hnd : NodupIds B)
    (h : Embedded B G) : Embedded B' G where
  step := hpr.step_eq.trans h.step
  gow p hp := h.gow p (hpr.gowners_sub p hp)
  node p m' hm' := by
    obtain ⟨m, hm, hid, ho, hpa⟩ := hpr.nodes_derived m' (List.mem_of_find?_eq_some hm')
    have hBm : B.node? p = some m := by
      rw [← node?_id_eq _ p m' hm', hid]; exact node?_of_mem hnd m hm
    obtain ⟨n, hn, hno, hnp⟩ := h.node p m hBm
    exact ⟨n, hn, fun q hq hqm => hno q (ho q hq) (mem_of_pruned hpr hqm),
      fun q hq hqm => hnp q (hpa q hq) (mem_of_pruned hpr hqm)⟩

/-- A filter that only rewrites the global owners, applied on both sides. -/
theorem embedded_gowners_filter (B G : GPathM) (f : PathNodeId → Bool) (h : Embedded B G) :
    Embedded { B with gowners := B.gowners.filter f } { G with gowners := G.gowners.filter f } where
  step := h.step
  gow p hp := List.mem_filter.mpr ⟨h.gow p (List.mem_filter.mp hp).1, (List.mem_filter.mp hp).2⟩
  node p m hm := h.node p m hm

theorem embedded_filterRequire (B G : GPathM) (r : NodeId) (h : Embedded B G) :
    Embedded (filterRequire B r) (filterRequire G r) :=
  embedded_gowners_filter B G _ h

theorem embedded_foldl_filterRequire (reqs : List NodeId) :
    ∀ B G, Embedded B G → Embedded (reqs.foldl filterRequire B) (reqs.foldl filterRequire G) := by
  induction reqs with
  | nil => intro B G h; exact h
  | cons r rs ih => intro B G h; exact ih _ _ (embedded_filterRequire B G r h)

theorem embedded_filterWeakAll (ws : List (Int × List NodeId)) :
    ∀ B G, Embedded B G → Embedded (filterWeakAll B ws) (filterWeakAll G ws) := by
  induction ws with
  | nil => intro B G h; exact h
  | cons e es ih =>
    intro B G h
    exact ih (filterWeak B e) (filterWeak G e) (embedded_gowners_filter B G _ h)

/-- **The pins and the whole aggressive review, on both sides.** If the reviewed inner state is a
valid state of the reader's kind, its tables are a support relation inside the filtered outer state,
so they survive its review, with their links. -/
theorem embedded_filterAllAgg (B G : GPathM) (reqs : List NodeId) (h : Embedded B G) (hnd : NodupIds B)
    (hR' : ReadableAgg (filterAllAgg B reqs)) (hv' : isValid (filterAllAgg B reqs) = true)
    (hsmp' : Sons.SMP (filterAllAgg B reqs)) (hpms' : Sons.PMS (filterAllAgg B reqs))
    (hsn' : Sons.SN (filterAllAgg B reqs))
    (hsmpG : Sons.SMP (reqs.foldl filterRequire G)) (hnrG : Parents.NotRoot (reqs.foldl filterRequire G)) :
    Embedded (filterAllAgg B reqs) (filterAllAgg G reqs) := by
  have hfe := embedded_foldl_filterRequire reqs B G h
  have hframe : ∀ (l : List NodeId) (g : GPathM), (l.foldl filterRequire g).nodes = g.nodes := by
    intro l
    induction l with
    | nil => intro g; rfl
    | cons r rs ih => intro g; exact ih (filterRequire g r)
  have hndf : NodupIds (reqs.foldl filterRequire B) := by
    unfold NodupIds at hnd ⊢; rw [hframe reqs B]; exact hnd
  have hin : Embedded (filterAllAgg B reqs) (reqs.foldl filterRequire G) :=
    embedded_of_pruned (pruned_reviewAgg _) hndf hfe
  have a := AdjacentOwners.adj_of_readable _ hR' hv' hpms' hsn'
  have hok : AggOk (filterAllAgg B reqs) := aggOk_reviewAgg _ hv'
  have sup := sup_of_embedded _ _ a hok hsmp' hin
  have hA := AOk_filterAllAgg (reqs.foldl filterRequire G) ⟨sup, hsmpG, hnrG⟩ []
    (fun r hr => absurd hr List.not_mem_nil)
  change AOk (filterAllAgg G reqs) _ _ at hA
  refine ⟨?_, ?_, ?_⟩
  · exact (pruned_filterAllAgg B reqs).step_eq.trans (h.step.trans (pruned_filterAllAgg G reqs).step_eq.symm)
  · intro p hp
    obtain ⟨m, hm, hmid⟩ := a.rc.gn p hp
    exact hA.sup.gow p ⟨m, by rw [← hmid]; exact node?_of_mem a.rc.nodup m hm⟩
  · intro x m hm
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hA.sup.node x ⟨m, hm⟩)
    have hmem := List.mem_of_find?_eq_some hm
    have hid := node?_id_eq _ x m hm
    refine ⟨n, hn, fun q hq hqm => hA.sup.own x q n ⟨m, hm, hq, hqm⟩ hn, fun q hq hqm => ?_⟩
    obtain ⟨mq, hmq⟩ := hqm
    have hxq : x ∈ mq.owners := by
      have hson : m.id ∈ mq.sons :=
        hsmp' m hmem q hq mq (List.mem_of_find?_eq_some hmq) (node?_id_eq _ q mq hmq)
      rw [hid] at hson
      exact (a.links q mq hmq).2 x hson
    have hstep : q.id.step + 1 = x.id.step := by
      have := a.rc.shape.pbelow m hmem q hq
      rw [hid] at this
      omega
    exact hA.sup.link x q n ⟨m, hm, (a.links x m hm).1 q hq, ⟨mq, hmq⟩⟩ ⟨mq, hmq, hxq, ⟨m, hm⟩⟩ hstep hn

/-- A node of the grown state is the new node or a node of the state it grew from. -/
theorem mem_addNode {g : GPathM} {d : NodeId} {title : String} {q : PathNodeId}
    (h : Mem (addNode g d title) q) : q = newPid g d ∨ Mem g q := by
  obtain ⟨m, hm⟩ := h
  have hmem := List.mem_of_find?_eq_some hm
  have hid := node?_id_eq _ q m hm
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hl
    have hnid : n.id = q := by rw [← hid, ← hEq, upMap_id]
    have hs := node?_isSome_of_mem g n hn
    rw [hnid] at hs
    exact Or.inr (Option.isSome_iff_exists.mp hs)
  · left
    rw [← hid, List.mem_singleton.mp hr]; rfl

/-- **UP of the same map node on both sides.** -/
theorem embedded_addNode (B G : GPathM) (d : NodeId) (title : String) (h : Embedded B G)
    (hmp : B.map_parent = G.map_parent) (hd : d.step = B.current_step)
    (hbB : ∀ n ∈ B.nodes, n.id.id.step < B.current_step) (hbG : ∀ n ∈ G.nodes, n.id.id.step < G.current_step)
    (hpbB : Parents.PBelow B) (hndB : NodupIds B) :
    Embedded (addNode B d title) (addNode G d title) := by
  have hnew : newPid B d = newPid G d := by simp only [newPid, hmp]
  have hdG : d.step = G.current_step := hd.trans h.step
  have memB : ∀ q, Mem (addNode B d title) q → q ≠ newPid B d → Mem B q := by
    intro q hq hne
    rcases mem_addNode hq with he | hm
    · exact absurd he hne
    · exact hm
  refine ⟨?_, ?_, ?_⟩
  · simp only [addNode_current, h.step]
  · intro p hp
    rw [addNode_gowners] at hp ⊢
    rcases List.mem_append.mp hp with hp | hp
    · exact List.mem_append_left _ (h.gow p hp)
    · rw [List.mem_singleton.mp hp, hnew]; exact List.mem_append_right _ List.mem_cons_self
  · intro p m hm
    have hmem := List.mem_of_find?_eq_some hm
    have hid := node?_id_eq _ p m hm
    rw [addNode_nodes] at hmem
    rcases List.mem_append.mp hmem with hl | hr
    · -- an old node
      obtain ⟨n₀, hn₀, hEq⟩ := List.mem_map.mp hl
      have hpid : n₀.id = p := by rw [← hid, ← hEq, upMap_id]
      have hBp : B.node? p = some n₀ := by rw [← hpid]; exact node?_of_mem hndB n₀ hn₀
      obtain ⟨nG, hnG, hno, hnp⟩ := h.node p n₀ hBp
      have hGmem := List.mem_of_find?_eq_some hnG
      have hGp : (addNode G d title).node? p = some (upMap G d nG) := by
        have := addNode_node?_old G d title p nG hnG
        exact this
      refine ⟨upMap G d nG, hGp, fun q hq hqm => ?_, fun q hq hqm => ?_⟩
      · rw [← hEq, upMap_owners] at hq
        rw [upMap_owners]
        by_cases hqn : q = newPid B d
        · rw [hqn, hnew]; exact List.mem_append_right _ List.mem_cons_self
        · rcases List.mem_append.mp hq with hq | hq
          · exact List.mem_append_left _ (hno q hq (memB q hqm hqn))
          · exact absurd (List.mem_singleton.mp hq) hqn
      · rw [← hEq, upMap_parents] at hq
        rw [upMap_parents]
        have hqs : q.id.step = p.id.step - 1 := by rw [← hpid]; exact hpbB n₀ hn₀ q hq
        have hps : p.id.step < B.current_step := by rw [← hpid]; exact hbB n₀ hn₀
        have hqn : q ≠ newPid B d := by
          intro he
          have : q.id.step = d.step := by rw [he]; rfl
          omega
        exact hnp q hq (memB q hqm hqn)
    · -- the new node
      have hmeq : m = addOwner (newPid B d) (upNode B d title) := List.mem_singleton.mp hr
      have hpnew : p = newPid B d := by rw [← hid, hmeq]; rfl
      refine ⟨addOwner (newPid G d) (upNode G d title), ?_, fun q hq _ => ?_, fun q hq _ => ?_⟩
      · rw [hpnew, hnew]; exact addNode_node?_new G d title hdG hbG
      · rw [hmeq] at hq
        change q ∈ B.gowners ++ [newPid B d] at hq
        change q ∈ G.gowners ++ [newPid G d]
        rcases List.mem_append.mp hq with hq | hq
        · exact List.mem_append_left _ (h.gow q hq)
        · rw [List.mem_singleton.mp hq, hnew]; exact List.mem_append_right _ List.mem_cons_self
      · rw [hmeq] at hq
        change q ∈ newParents B at hq
        change q ∈ newParents G
        unfold newParents at hq ⊢
        rw [← h.step]
        split
        · next hpos =>
          rw [if_pos hpos] at hq
          obtain ⟨nq, hnq, hnqid⟩ := List.mem_map.mp hq
          have hnqB : B.node? q = some nq := by rw [← hnqid]; exact node?_of_mem hndB nq (List.mem_filter.mp hnq).1
          have hqs : q.id.step = B.current_step - 1 := by
            rw [← hnqid]; exact eq_of_beq (List.mem_filter.mp hnq).2
          obtain ⟨nG, hnG, _, _⟩ := h.node q nq hnqB
          rw [h.step] at hqs ⊢
          exact mem_line_of_node? G q nG hnG _ hqs
        · next hpos =>
          rw [if_neg hpos] at hq
          exact absurd hq List.not_mem_nil

/-- A valid inner state makes the outer one valid: its global owners are the outer's. -/
theorem isValid_of_embedded {B G : GPathM} (h : Embedded B G) (hv : isValid B = true) :
    isValid G = true := by
  simp only [isValid, List.all_eq_true] at hv ⊢
  intro k hk
  rw [← h.step] at hk
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (hv k hk)
  exact List.any_eq_true.mpr ⟨q, h.gow q hq, hqs⟩

/-- **UP on both sides**, when the inner state is valid. -/
theorem embedded_up (B G : GPathM) (d : NodeId) (title : String) (h : Embedded B G)
    (hv : isValid B = true) (hmp : B.map_parent = G.map_parent) (hd : d.step = B.current_step)
    (hbB : ∀ n ∈ B.nodes, n.id.id.step < B.current_step) (hbG : ∀ n ∈ G.nodes, n.id.id.step < G.current_step)
    (hpbB : Parents.PBelow B) (hndB : NodupIds B) :
    Embedded (up B d title) (up G d title) := by
  simp only [GPathM.up, hv, isValid_of_embedded h hv, if_pos]
  exact embedded_addNode B G d title h hmp hd hbB hbG hpbB hndB

/-- info: 'AbsSat.GraphPath.Model.BranchRun.embedded_filterAllAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms embedded_filterAllAgg

/-- info: 'AbsSat.GraphPath.Model.BranchRun.embedded_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms embedded_addNode

-- ============================================================
-- Joins
-- ============================================================

/-- Growing the outer state keeps the inner one inside. -/
theorem embedded_of_grown {B G G' : GPathM} (h : Embedded B G) (hg : Grown G G') : Embedded B G' where
  step := h.step.trans hg.step_eq.symm
  gow p hp := hg.gowners_grown p (h.gow p hp)
  node p m hm := by
    obtain ⟨n, hn, ho, hpa⟩ := h.node p m hm
    obtain ⟨n', hn', ho', hpa', _⟩ := hg.node?_grown p n hn
    exact ⟨n', hn', fun q hq hqm => ho' q (ho q hq hqm), fun q hq hqm => hpa' q (hpa q hq hqm)⟩

/-- Where the owners and the parents of a joined node come from. -/
theorem mem_join_nodes_src {g₁ g₂ : GPathM} {n : PNodeM} (hn : n ∈ (join g₁ g₂).nodes) :
    (∃ a ∈ g₁.nodes, n.id = a.id ∧
      (∀ q ∈ n.owners, q ∈ a.owners ∨ ∃ b ∈ g₂.nodes, b.id = a.id ∧ q ∈ b.owners) ∧
      (∀ q ∈ n.parents, q ∈ a.parents ∨ ∃ b ∈ g₂.nodes, b.id = a.id ∧ q ∈ b.parents)) ∨
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
      exact ⟨rfl, fun q hq => Or.inl hq, fun q hq => Or.inl hq⟩
    | some m =>
      rw [h2] at heq
      have hnm : n = mergeNode a m := heq.symm
      subst hnm
      have hbm := List.mem_of_find?_eq_some h2
      have hbid := node?_id_eq g₂ a.id m h2
      refine ⟨rfl, fun q hq => ?_, fun q hq => ?_⟩
      · have hq' : q ∈ a.owners ++ m.owners.filter (fun q => !a.owners.contains q) := hq
        rcases List.mem_append.mp hq' with hqa | hqm
        · exact Or.inl hqa
        · exact Or.inr ⟨m, hbm, hbid, (List.mem_filter.mp hqm).1⟩
      · have hq' : q ∈ a.parents ++ m.parents.filter (fun p => !a.parents.contains p) := hq
        rcases List.mem_append.mp hq' with hqa | hqm
        · exact Or.inl hqa
        · exact Or.inr ⟨m, hbm, hbid, (List.mem_filter.mp hqm).1⟩
  · exact Or.inr (List.mem_filter.mp h).1

/-- **Joining two inner states inside the join of the outer ones.** Owners and parents of the inner
states are their own nodes. -/
theorem embedded_join (B₁ B₂ G₁ G₂ : GPathM) (h₁ : Embedded B₁ G₁) (h₂ : Embedded B₂ G₂)
    (hokG : okJoin G₁ G₂ = true)
    (hown₁ : ∀ x m, B₁.node? x = some m → ∀ q ∈ m.owners, Mem B₁ q)
    (hown₂ : ∀ x m, B₂.node? x = some m → ∀ q ∈ m.owners, Mem B₂ q)
    (hpn₁ : Parents.PN B₁) (hpn₂ : Parents.PN B₂) (hnd₁ : NodupIds B₁) (hnd₂ : NodupIds B₂) :
    Embedded (join B₁ B₂) (join G₁ G₂) := by
  have gl := grown_join_left G₁ G₂
  have gr := grown_join_right G₁ G₂ hokG
  have memPN : ∀ (B : GPathM), Parents.PN B → NodupIds B → ∀ a ∈ B.nodes, ∀ q ∈ a.parents, Mem B q := by
    intro B hpn hnd a ha q hq
    obtain ⟨mq, hmq, hmqid⟩ := hpn a ha q hq
    exact ⟨mq, by rw [← hmqid]; exact node?_of_mem hnd mq hmq⟩
  refine ⟨h₁.step, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact gl.gowners_grown q (h₁.gow q hq)
    · exact gr.gowners_grown q (h₂.gow q (List.mem_filter.mp hq).1)
  · intro p m hm
    have hmem := List.mem_of_find?_eq_some hm
    have hid := node?_id_eq _ p m hm
    rcases mem_join_nodes_src hmem with ⟨a, ha, hida, ho, hpa⟩ | hb
    · have hB₁ : B₁.node? p = some a := by rw [← hid, hida]; exact node?_of_mem hnd₁ a ha
      obtain ⟨n₁, hn₁, ho₁, hp₁⟩ := h₁.node p a hB₁
      obtain ⟨n', hn', ho', hp', _⟩ := gl.node?_grown p n₁ hn₁
      -- a copy on the other side lands in the same joined node
      have other : ∀ b ∈ B₂.nodes, b.id = a.id →
          (∀ q ∈ b.owners, q ∈ n'.owners) ∧ (∀ q ∈ b.parents, q ∈ n'.parents) := by
        intro b hb hbid
        have hB₂ : B₂.node? p = some b := by rw [← hid, hida, ← hbid]; exact node?_of_mem hnd₂ b hb
        obtain ⟨n₂, hn₂, ho₂, hp₂⟩ := h₂.node p b hB₂
        obtain ⟨n'', hn'', ho'', hp'', _⟩ := gr.node?_grown p n₂ hn₂
        rw [hn'] at hn''
        cases hn''
        exact ⟨fun q hq => ho'' q (ho₂ q hq (hown₂ p b hB₂ q hq)),
          fun q hq => hp'' q (hp₂ q hq (memPN B₂ hpn₂ hnd₂ b hb q hq))⟩
      refine ⟨n', hn', fun q hq _ => ?_, fun q hq _ => ?_⟩
      · rcases ho q hq with hqa | ⟨b, hb, hbid, hqb⟩
        · exact ho' q (ho₁ q hqa (hown₁ p a hB₁ q hqa))
        · exact (other b hb hbid).1 q hqb
      · rcases hpa q hq with hqa | ⟨b, hb, hbid, hqb⟩
        · exact hp' q (hp₁ q hqa (memPN B₁ hpn₁ hnd₁ a ha q hqa))
        · exact (other b hb hbid).2 q hqb
    · have hB₂ : B₂.node? p = some m := by rw [← hid]; exact node?_of_mem hnd₂ m hb
      obtain ⟨n₂, hn₂, ho₂, hp₂⟩ := h₂.node p m hB₂
      obtain ⟨n', hn', ho', hp', _⟩ := gr.node?_grown p n₂ hn₂
      exact ⟨n', hn', fun q hq _ => ho' q (ho₂ q hq (hown₂ p m hB₂ q hq)),
        fun q hq _ => hp' q (hp₂ q hq (memPN B₂ hpn₂ hnd₂ m hb q hq))⟩

/-- info: 'AbsSat.GraphPath.Model.BranchRun.embedded_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms embedded_join

end AbsSat.GraphPath.Model.BranchRun
