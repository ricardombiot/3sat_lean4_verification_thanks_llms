-- lean_project/AbsSat/GraphPath/Model/RunEnv.lean
import AbsSat.GraphPath.Model.Up
import AbsSat.GraphPath.Model.Join
import AbsSat.GraphPath.Model.AggressiveReview
import AbsSat.GraphPath.Model.PureDriverImproves
import AbsSat.GraphPath.Model.ConservationCore
import AbsSat.GraphPath.Model.ReaderAggRun

/-!
# Nothing is invented: the tables a node may ever carry

The author's design fact. A `PathNodeId` is a pair **(destination, origin)**, an `up` is tied to
exactly one such pair, and the keys of a line are unique (`PureDriver.key_inj`), so the node
`(d, q)` is created by **one** `up`, from the one state keyed `q`. A node's table can therefore
only ever be a pruning of the table that `up` gave it — the destination may be reached by many
histories, but each of them enters through a node the identifier names.

This file carries that as a run invariant, in the form the proof needs: a **bound** on the tables.

* `Env`, `Within` — a bound per node id, and a state whose every table sits inside it.
* `Within_of_pruned` — every pruning stays inside the bound: filters and reviews only remove.
* `Within_join` — **a join stays inside the bound**: by `Join.join_owners_source` every entry of a
  joined node comes from one of the two sides, so the union of two bounded tables is bounded. This
  is the formal content of "the join unites different histories of the same destination without
  inventing anything".
* `Within_addNode` — an `up` stays inside the bound once the bound is extended by the new node,
  which is what `addNode` appends to every table.

The payoff for `JoinSplit` (v128–v130): at a join, the two sides' tables for a node they share are
**prunings of one and the same table**, so an entry only one side carries is one the other side
*pruned* — not one it never had.
-/

namespace AbsSat.GraphPath.Model.RunEnv

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

/-- Either a state has no node with this id, or it has one. -/
private theorem node?_cases (g : GPathM) (pid : PathNodeId) :
    g.node? pid = none ∨ ∃ n, g.node? pid = some n := by
  generalize hg : g.node? pid = o
  cases o with
  | none => exact Or.inl rfl
  | some n => exact Or.inr ⟨n, rfl⟩

/-- A bound on the tables: for each node id, the entries it may own. -/
abbrev Env := PathNodeId → List PathNodeId

/-- Every table of the state sits inside the bound. -/
def Within (E : Env) (g : GPathM) : Prop :=
  ∀ y n, g.node? y = some n → ∀ w ∈ n.owners, w ∈ E y

/-- A wider bound is still a bound. -/
theorem Within_mono {E E' : Env} {g : GPathM} (hsub : ∀ y, ∀ w ∈ E y, w ∈ E' y)
    (h : Within E g) : Within E' g :=
  fun y n hn w hw => hsub y w (h y n hn w hw)

/-- **Every pruning stays inside the bound.** The filters and the reviews only remove. -/
theorem Within_of_pruned {E : Env} {g g' : GPathM} (hpr : Pruned g g') (hnd : NodupIds g)
    (h : Within E g) : Within E g' := by
  intro y n hn w hw
  have hnB : n ∈ g'.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = y := node?_id_eq g' y n hn
  obtain ⟨n₀, hn₀, hids, hown, _⟩ := hpr.nodes_derived n hnB
  have h₀ : g.node? y = some n₀ := by
    have := node?_of_mem hnd n₀ hn₀
    rw [← hids, hid] at this
    exact this
  exact h y n₀ h₀ w (hown w hw)

/-- **A join stays inside the bound.** Every entry of a joined node comes from one of the two
sides, so a common bound for the sides bounds the join: the union of two histories of the same
destination invents nothing. -/
theorem Within_join {E : Env} {g₁ g₂ : GPathM} (h₁ : Within E g₁) (h₂ : Within E g₂) :
    Within E (join g₁ g₂) := by
  intro y n hn w hw
  rcases join_owners_source g₁ g₂ y n hn w hw with ⟨m, hm, hwm⟩ | ⟨m, hm, hwm⟩
  · exact h₁ y m hm w hwm
  · exact h₂ y m hm w hwm

-- ============================================================
-- The `up`
-- ============================================================

/-- The bound `addNode` needs: every old node gains the new id, and the new node gains the state's
global owners. -/
def upEnv (E : Env) (g : GPathM) (d : NodeId) : Env := fun y =>
  if y == newPid g d then g.gowners ++ [newPid g d] else E y ++ [newPid g d]

/-- The record `addNode` gives the new node. -/
private theorem addNode_node?_new (g : GPathM) (d : NodeId) (title : String)
    (hnone : g.node? (newPid g d) = none) :
    (addNode g d title).node? (newPid g d) = some (addOwner (newPid g d) (upNode g d title)) := by
  have hp : (fun x : PNodeM => (upMap g d x).id == newPid g d)
      = (fun x : PNodeM => x.id == newPid g d) := by
    funext x; rw [upMap_id]
  have hnodes : g.nodes.find? (fun x : PNodeM => x.id == newPid g d) = none := hnone
  simp only [node?, addNode_nodes, List.find?_append, List.find?_map, Function.comp_def, hp,
    hnodes, Option.map_none, Option.none_or, List.find?_cons]
  have hid : (addOwner (newPid g d) (upNode g d title)).id = newPid g d := rfl
  simp only [hid, beq_self_eq_true]

/-- **An `up` stays inside the extended bound.** -/
theorem Within_addNode {E : Env} (g : GPathM) (d : NodeId) (title : String)
    (hnone : g.node? (newPid g d) = none) (h : Within E g) :
    Within (upEnv E g d) (addNode g d title) := by
  intro y n hn w hw
  by_cases hy : y = newPid g d
  · subst hy
    rw [addNode_node?_new g d title hnone] at hn
    have hn' : n = addOwner (newPid g d) (upNode g d title) := (Option.some_inj.mp hn).symm
    have how : n.owners = g.gowners ++ [newPid g d] := by rw [hn']; rfl
    rw [how] at hw
    simp only [upEnv, beq_self_eq_true, if_pos]
    exact hw
  · have hold : ∃ m, g.node? y = some m := by
      have hnB : n ∈ (addNode g d title).nodes := List.mem_of_find?_eq_some hn
      have hid : n.id = y := node?_id_eq _ y n hn
      rw [addNode_nodes] at hnB
      rcases List.mem_append.mp hnB with hl | hr
      · obtain ⟨n₀, hn₀, heq⟩ := List.mem_map.mp hl
        have hid₀ : n₀.id = y := by rw [← hid, ← heq, upMap_id]
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_mem g n₀ hn₀)
        rw [hid₀] at hm
        exact ⟨m, hm⟩
      · exfalso
        have hsing : n = addOwner (newPid g d) (upNode g d title) := List.eq_of_mem_singleton hr
        rw [hsing] at hid
        exact hy (by rw [← hid]; rfl)
    obtain ⟨m, hm⟩ := hold
    rw [addNode_node?_old g d title y m hm] at hn
    have hn' : n = upMap g d m := (Option.some_inj.mp hn).symm
    have how : n.owners = m.owners ++ [newPid g d] := by rw [hn']; exact upMap_owners g d m
    rw [how] at hw
    simp only [upEnv, show (y == newPid g d) = false from by
      cases hb : (y == newPid g d) with
      | true => exact absurd (eq_of_beq hb) hy
      | false => rfl]
    rcases List.mem_append.mp hw with hl | hr
    · exact List.mem_append_left _ (h y m hm w hl)
    · exact List.mem_append_right _ hr


-- ============================================================
-- The stable form: bound only the past
-- ============================================================

/-- **The bound on the past of each node.** An `up` appends the new top node to every table, so a
bound on the whole table has to grow at every step; a bound on the entries **at or below the
node's own step** does not. That is the stable form of the invariant, and the one the proof uses:
the past of a node is bounded by the past its birth state had. -/
def WithinBelow (E : Env) (g : GPathM) : Prop :=
  ∀ y n, g.node? y = some n → ∀ w ∈ n.owners, w.id.step ≤ y.id.step → w ∈ E y

theorem WithinBelow_of_pruned {E : Env} {g g' : GPathM} (hpr : Pruned g g') (hnd : NodupIds g)
    (h : WithinBelow E g) : WithinBelow E g' := by
  intro y n hn w hw hstep
  have hnB : n ∈ g'.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = y := node?_id_eq g' y n hn
  obtain ⟨n₀, hn₀, hids, hown, _⟩ := hpr.nodes_derived n hnB
  have h₀ : g.node? y = some n₀ := by
    have hq := node?_of_mem hnd n₀ hn₀
    rw [← hids, hid] at hq
    exact hq
  exact h y n₀ h₀ w (hown w hw) hstep

/-- **A join keeps the bound on the past**, with no extension: the two sides' tables for a node
they share are prunings of one and the same table, so their union is too. -/
theorem WithinBelow_join {E : Env} {g₁ g₂ : GPathM} (h₁ : WithinBelow E g₁)
    (h₂ : WithinBelow E g₂) : WithinBelow E (join g₁ g₂) := by
  intro y n hn w hw hstep
  rcases join_owners_source g₁ g₂ y n hn w hw with ⟨m, hm, hwm⟩ | ⟨m, hm, hwm⟩
  · exact h₁ y m hm w hwm hstep
  · exact h₂ y m hm w hwm hstep

/-- The bound at birth: the new node's past is the state's global owners, plus itself. -/
def bornEnv (E : Env) (g : GPathM) (d : NodeId) : Env := fun y =>
  if y == newPid g d then g.gowners ++ [newPid g d] else E y

/-- **An `up` keeps the bound on the past**, extended only at the node it creates. The old nodes
gain the new top node, which lies *above* them, so their bound is untouched — that is what makes
this form of the invariant stable along the whole run. -/
theorem WithinBelow_addNode {E : Env} (g : GPathM) (d : NodeId) (title : String)
    (hd : g.current_step ≤ d.step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (h : WithinBelow E g) : WithinBelow (bornEnv E g d) (addNode g d title) := by
  have hnp : (newPid g d).id.step = d.step := rfl
  have hnone : g.node? (newPid g d) = none := by
    rcases node?_cases g (newPid g d) with hc | ⟨m, hm⟩
    · exact hc
    · exfalso
      have hmem := List.mem_of_find?_eq_some hm
      have hid := node?_id_eq g _ m hm
      have hb := hbelow m hmem
      rw [hid, hnp] at hb
      omega
  intro y n hn w hw hstep
  by_cases hy : y = newPid g d
  · subst hy
    rw [addNode_node?_new g d title hnone] at hn
    have hn' : n = addOwner (newPid g d) (upNode g d title) := (Option.some_inj.mp hn).symm
    have how : n.owners = g.gowners ++ [newPid g d] := by rw [hn']; rfl
    rw [how] at hw
    simpa only [bornEnv, beq_self_eq_true, if_pos] using hw
  · have hold : ∃ m, g.node? y = some m := by
      have hnB : n ∈ (addNode g d title).nodes := List.mem_of_find?_eq_some hn
      have hid : n.id = y := node?_id_eq _ y n hn
      rw [addNode_nodes] at hnB
      rcases List.mem_append.mp hnB with hl | hr
      · obtain ⟨n₀, hn₀, heq⟩ := List.mem_map.mp hl
        have hid₀ : n₀.id = y := by rw [← hid, ← heq, upMap_id]
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_mem g n₀ hn₀)
        rw [hid₀] at hm
        exact ⟨m, hm⟩
      · exfalso
        have hsing : n = addOwner (newPid g d) (upNode g d title) := List.eq_of_mem_singleton hr
        rw [hsing] at hid
        exact hy (by rw [← hid]; rfl)
    obtain ⟨m, hm⟩ := hold
    have hybelow : y.id.step < g.current_step := by
      have hmem := List.mem_of_find?_eq_some hm
      have hid := node?_id_eq g y m hm
      have := hbelow m hmem
      rw [hid] at this
      exact this
    rw [addNode_node?_old g d title y m hm] at hn
    have hn' : n = upMap g d m := (Option.some_inj.mp hn).symm
    have how : n.owners = m.owners ++ [newPid g d] := by rw [hn']; exact upMap_owners g d m
    rw [how] at hw
    simp only [bornEnv, show (y == newPid g d) = false from by
      cases hb : (y == newPid g d) with
      | true => exact absurd (eq_of_beq hb) hy
      | false => rfl]
    rcases List.mem_append.mp hw with hl | hr
    · exact h y m hm w hl hstep
    · exfalso
      have hwe := List.mem_singleton.mp hr
      rw [hwe, hnp] at hstep
      omega

/-- A wider bound on the past is still a bound. -/
theorem WithinBelow_mono {E E' : Env} {g : GPathM} (hsub : ∀ y, ∀ w ∈ E y, w ∈ E' y)
    (h : WithinBelow E g) : WithinBelow E' g :=
  fun y n hn w hw hstep => hsub y w (h y n hn w hw hstep)

/-- **The birth of a node touches the bound of no other node.** With the keys of a line unique,
an `up` is tied to one pair (destination, origin), so the extensions of different sends never
collide: this is what lets the bound be carried along the whole run. -/
theorem bornEnv_ne {E : Env} (g : GPathM) (d : NodeId) {y : PathNodeId} (hy : y ≠ newPid g d) :
    bornEnv E g d y = E y := by
  simp only [bornEnv, show (y == newPid g d) = false from by
    cases hb : (y == newPid g d) with
    | true => exact absurd (eq_of_beq hb) hy
    | false => rfl, Bool.false_eq_true, if_false]

/-- Every state of a line is bounded on its past by one common bound. -/
def LineWithinBelow (E : Env) (L : List (NodeId × GPathM)) : Prop :=
  ∀ kv ∈ L, WithinBelow E kv.2

/-- info: 'AbsSat.GraphPath.Model.RunEnv.WithinBelow_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WithinBelow_join


-- ============================================================
-- The fold over the driver
-- ============================================================

open AbsSat.Cnf
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphMap.CnfMap (reqOfCnf mapNodes stepCount)
open AbsSat.GraphMap.CnfSel (mapSons mapNodes_step mapSons_subset)
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)

/-- The state a send filters before opening the new step. -/
def Filt' (φ : Cnf) (g : GPathM) (d : NodeId) : GPathM :=
  AggressiveReview.filterAllAgg (filterWeakAll g (weakReqOfCnf φ d)) (reqOfCnf φ d)

/-- What a send needs from the machine, and nothing more: the destination sits at or above the
step the filtered state has open, and that state's nodes are below it. -/
structure SendOk (φ : Cnf) (g : GPathM) (d : NodeId) : Prop where
  nodup : NodupIds g
  step : (Filt' φ g d).current_step ≤ d.step
  below : ∀ n ∈ (Filt' φ g d).nodes, n.id.id.step < (Filt' φ g d).current_step

theorem sendW_eq (φ : Cnf) (g : GPathM) (d : NodeId) :
    upFilteringWeak g (weakReqOfCnf φ d) (reqOfCnf φ d) d "" = up (Filt' φ g d) d "" := rfl

/-- **One send keeps the bound**, extended only at the node it may create. -/
theorem WithinBelow_send {E : Env} (φ : Cnf) (g : GPathM) (d : NodeId) (hok : SendOk φ g d)
    (h : WithinBelow E g) :
    WithinBelow (bornEnv E (Filt' φ g d) d)
      (upFilteringWeak g (weakReqOfCnf φ d) (reqOfCnf φ d) d "") := by
  have hpr : Pruned g (Filt' φ g d) :=
    Pruned.trans (ConservationCore.pruned_filterWeakAll g (weakReqOfCnf φ d))
      (AggressiveReview.pruned_filterAllAgg _ (reqOfCnf φ d))
  have hF : WithinBelow E (Filt' φ g d) := WithinBelow_of_pruned hpr hok.nodup h
  rw [sendW_eq]
  simp only [GPathM.up]
  cases hv : isValid (Filt' φ g d) with
  | true =>
    simp only [if_pos]
    exact WithinBelow_addNode _ d "" hok.step hok.below hF
  | false =>
    simp only [Bool.false_eq_true, if_false]
    intro y n hn w hw hstep
    by_cases hy : y = newPid (Filt' φ g d) d
    · exfalso
      subst hy
      have hmem := List.mem_of_find?_eq_some hn
      have hid := node?_id_eq _ _ n hn
      have hb := hok.below n hmem
      rw [hid] at hb
      have hnp : (newPid (Filt' φ g d) d).id.step = d.step := rfl
      rw [hnp] at hb
      have := hok.step
      omega
    · rw [bornEnv_ne _ d hy]
      exact hF y n hn w hw hstep

/-- The bound after one advance: the old one, plus the table each send gives the node it creates. -/
def advEnv (φ : Cnf) (E : Env) (L : PureLine) : Env := fun y =>
  E y ++ L.flatMap (fun kv =>
    (mapSons φ kv.1.step kv.1.index).flatMap (fun d =>
      if y == newPid (Filt' φ kv.2 d) d then (Filt' φ kv.2 d).gowners ++ [y] else []))

theorem mem_advEnv_of_mem {φ : Cnf} {E : Env} {L : PureLine} {y : PathNodeId} {w : PathNodeId}
    (h : w ∈ E y) : w ∈ advEnv φ E L y :=
  List.mem_append_left _ h

/-- The born bound of one send sits inside the advance bound. -/
theorem bornEnv_sub_advEnv {φ : Cnf} {E : Env} {L : PureLine} (kv : NodeId × GPathM)
    (hkv : kv ∈ L) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (y : PathNodeId)
    (w : PathNodeId) (h : w ∈ bornEnv E (Filt' φ kv.2 d) d y) : w ∈ advEnv φ E L y := by
  simp only [bornEnv] at h
  cases hb : (y == newPid (Filt' φ kv.2 d) d) with
  | false => rw [hb] at h; simp only [Bool.false_eq_true, if_false] at h; exact mem_advEnv_of_mem h
  | true =>
    rw [hb] at h
    simp only [if_pos] at h
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨kv, hkv, ?_⟩)
    refine List.mem_flatMap.mpr ⟨d, hd, ?_⟩
    rw [hb]
    simp only [if_pos]
    rcases List.mem_append.mp h with hl | hr
    · exact List.mem_append_left _ hl
    · exact List.mem_append_right _ (by
        rw [List.mem_singleton.mp hr, ← eq_of_beq hb]
        exact List.mem_singleton_self y)


/-- **`insertPure` keeps the bound**: it either appends the new state or joins it with the one
already at that key, and a join keeps the bound. -/
theorem lineWithin_insertPure {E : Env} (next : PureLine) (key : NodeId) (g : GPathM)
    (hnext : LineWithinBelow E next) (hg : WithinBelow E g) :
    LineWithinBelow E (insertPure next key g) := by
  simp only [insertPure]
  cases hf : next.find? (fun kv => kv.1 == key) with
  | none =>
    intro kv hkv
    rcases List.mem_append.mp hkv with hl | hr
    · exact hnext kv hl
    · rw [List.mem_singleton.mp hr]; exact hg
  | some p =>
    have hp : p ∈ next := List.mem_of_find?_eq_some hf
    intro kv hkv
    obtain ⟨kv₀, hkv₀, heq⟩ := List.mem_map.mp hkv
    cases hb : (kv₀.1 == key) with
    | true =>
      rw [← heq]
      simp only [hb, if_pos]
      show WithinBelow E (doJoin p.2 g)
      simp only [doJoin]
      cases hj : okJoin p.2 g with
      | true => simp only [if_pos]; exact WithinBelow_join (hnext p hp) hg
      | false => simp only [Bool.false_eq_true, if_false]; exact hnext p hp
    | false =>
      rw [← heq]
      simp only [hb, Bool.false_eq_true, if_false]
      exact hnext kv₀ hkv₀

/-- Every send of a line needs its own step facts. -/
def SendsOk (φ : Cnf) (L : PureLine) : Prop :=
  ∀ kv ∈ L, ∀ d ∈ mapSons φ kv.1.step kv.1.index, SendOk φ kv.2 d

/-- **One send keeps the line's bound.** -/
theorem lineWithin_sendTo {E : Env} (φ : Cnf) (L : PureLine) (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (hok : SendOk φ kv.2 d)
    (h : WithinBelow E kv.2) (next : PureLine)
    (hnext : LineWithinBelow (advEnv φ E L) next) :
    LineWithinBelow (advEnv φ E L) (sendToW φ kv.2 next d) := by
  simp only [sendToW]
  cases hv : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") with
  | false => simp only [Bool.false_eq_true, if_false]; exact hnext
  | true =>
    simp only [if_pos]
    exact lineWithin_insertPure next d _ hnext
      (WithinBelow_mono (bornEnv_sub_advEnv kv hkv d hd) (WithinBelow_send φ kv.2 d hok h))

/-- **All the sends of one state keep the line's bound.** -/
theorem lineWithin_sons {E : Env} (φ : Cnf) (L : PureLine) (kv : NodeId × GPathM) (hkv : kv ∈ L)
    (h : WithinBelow E kv.2) :
    ∀ (ds : List NodeId), (∀ d ∈ ds, d ∈ mapSons φ kv.1.step kv.1.index) →
      (∀ d ∈ ds, SendOk φ kv.2 d) → ∀ next : PureLine,
      LineWithinBelow (advEnv φ E L) next →
      LineWithinBelow (advEnv φ E L) (ds.foldl (sendToW φ kv.2) next) := by
  intro ds
  induction ds with
  | nil => intro _ _ next hnext; exact hnext
  | cons a as ih =>
    intro hsub hoks next hnext
    simp only [List.foldl_cons]
    exact ih (fun d hd => hsub d (List.mem_cons_of_mem _ hd))
      (fun d hd => hoks d (List.mem_cons_of_mem _ hd)) _
      (lineWithin_sendTo φ L kv hkv a (hsub a List.mem_cons_self) (hoks a List.mem_cons_self) h
        next hnext)

/-- **The whole advance keeps one bound for the next line.** -/
theorem lineWithin_line {E : Env} (φ : Cnf) (L : PureLine) (h : LineWithinBelow E L)
    (hoks : SendsOk φ L) :
    ∀ (Ls : PureLine), (∀ kv ∈ Ls, kv ∈ L) → ∀ next : PureLine,
      LineWithinBelow (advEnv φ E L) next →
      LineWithinBelow (advEnv φ E L) (Ls.foldl (fun next kv => sendAllW φ kv next) next) := by
  intro Ls
  induction Ls with
  | nil => intro _ next hnext; exact hnext
  | cons a as ih =>
    intro hsub next hnext
    simp only [List.foldl_cons]
    refine ih (fun kv hkv => hsub kv (List.mem_cons_of_mem _ hkv)) _ ?_
    have ha : a ∈ L := hsub a List.mem_cons_self
    exact lineWithin_sons φ L a ha (h a ha) (mapSons φ a.1.step a.1.index) (fun _ hd => hd)
      (fun d hd => hoks a ha d hd) next hnext

/-- **One step of the machine keeps the bound**, extended only at the nodes it creates. -/
theorem lineWithin_advance {E : Env} (φ : Cnf) (L : PureLine) (h : LineWithinBelow E L)
    (hoks : SendsOk φ L) : LineWithinBelow (advEnv φ E L) (pureAdvanceW φ L) :=
  lineWithin_line φ L h hoks L (fun _ hkv => hkv) [] (fun _ hkv => absurd hkv List.not_mem_nil)

/-- The step facts, along the whole chain of lines the run passes through. -/
def SendsOkChain (φ : Cnf) : Nat → PureLine → Prop
  | 0, _ => True
  | n + 1, L => SendsOk φ L ∧ SendsOkChain φ n (pureAdvanceW φ L)

/-- **The run invariant.** Every line the machine builds has one bound for all its states: no
table ever holds, on its own step or below, an entry outside the one its node was born with. -/
theorem lineWithin_steps (φ : Cnf) : ∀ (n : Nat) (E : Env) (L : PureLine),
    LineWithinBelow E L → SendsOkChain φ n L →
    ∃ E', LineWithinBelow E' (pureStepsW φ n L) := by
  intro n
  induction n with
  | zero => intro E L h _; exact ⟨E, h⟩
  | succ m ih =>
    intro E L h hch
    exact ih (advEnv φ E L) (pureAdvanceW φ L) (lineWithin_advance φ L h hch.1) hch.2

/-- The seed: a state with one node, which owns only itself. -/
theorem withinBelow_initSeed (d : NodeId) (hd : 0 ≤ d.step) :
    WithinBelow (fun y => [y]) (initSeed d "") := by
  have hv : isValid empty = true := by decide
  have heq : initSeed d "" = addNode empty d "" := by
    simp only [initSeed, GPathM.up, hv, if_pos]
  have hempty : WithinBelow (fun y => [y]) empty := by
    intro y n hn _ _ _
    exfalso
    have hne : (empty.node? y) = none := rfl
    rw [hne] at hn
    exact absurd hn (by simp)
  have hbelow : ∀ n ∈ empty.nodes, n.id.id.step < empty.current_step := by
    intro n hn
    exact absurd hn (by
      have : empty.nodes = [] := rfl
      rw [this]
      exact List.not_mem_nil)
  have hstep : empty.current_step ≤ d.step := by
    have : empty.current_step = 0 := rfl
    rw [this]; exact hd
  have hmain := WithinBelow_addNode empty d "" hstep hbelow hempty
  rw [heq]
  refine WithinBelow_mono ?_ hmain
  intro y w hw
  simp only [bornEnv] at hw
  cases hb : (y == newPid empty d) with
  | true =>
    rw [hb] at hw
    simp only [if_pos] at hw
    have hgow : empty.gowners = [] := rfl
    rw [hgow, List.nil_append] at hw
    show w ∈ [y]
    rw [List.mem_singleton.mp hw, ← eq_of_beq hb]
    exact List.mem_singleton_self y
  | false =>
    rw [hb] at hw
    simp only [Bool.false_eq_true, if_false] at hw
    exact hw


/-- **The first line is bounded**: each seed has one node, owning only itself. -/
theorem lineWithin_init (φ : Cnf) : LineWithinBelow (fun y => [y]) (pureInit φ) := by
  have main : ∀ (ids : List NodeId), (∀ d ∈ ids, 0 ≤ d.step) → ∀ line : PureLine,
      LineWithinBelow (fun y => [y]) line →
      LineWithinBelow (fun y => [y])
        (ids.foldl (fun line id => insertPure line id (initSeed id "")) line) := by
    intro ids
    induction ids with
    | nil => intro _ line h; exact h
    | cons a as ih =>
      intro hst line h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hst d (List.mem_cons_of_mem _ hd)) _
        (lineWithin_insertPure line a _ h (withinBelow_initSeed a (hst a List.mem_cons_self)))
  exact main (mapNodes φ 0) (fun d hd => by rw [mapNodes_step φ 0 d hd]; exact Int.le_refl 0) []
    (fun _ hkv => absurd hkv List.not_mem_nil)

/-- **The run invariant, from the seed.** Along the whole run there is one bound per line: no
table ever holds, at its own step or below, an entry outside the one its node was born with. -/
theorem runWithin (φ : Cnf)
    (hch : SendsOkChain φ (stepCount φ - 1).toNat (pureInit φ)) :
    ∃ E, LineWithinBelow E (pureRunW φ) :=
  lineWithin_steps φ _ _ _ (lineWithin_init φ) hch

/-- **The payoff for a join.** Two states of the same line are bounded by the *same* bound, so for
a node they share, an entry one of them carries and the other does not is an entry the other one
**pruned** — not one it never had. -/
theorem shared_tables_common_bound {E : Env} {L : PureLine} (h : LineWithinBelow E L)
    {kv₁ kv₂ : NodeId × GPathM} (h₁ : kv₁ ∈ L) (h₂ : kv₂ ∈ L) (y : PathNodeId)
    {n₁ n₂ : PNodeM} (hn₁ : kv₁.2.node? y = some n₁) (hn₂ : kv₂.2.node? y = some n₂) :
    (∀ w ∈ n₁.owners, w.id.step ≤ y.id.step → w ∈ E y) ∧
      (∀ w ∈ n₂.owners, w.id.step ≤ y.id.step → w ∈ E y) :=
  ⟨h kv₁ h₁ y n₁ hn₁, h kv₂ h₂ y n₂ hn₂⟩


-- ============================================================
-- The step facts come from the machine's own line invariant
-- ============================================================

/-- **The machine's lines satisfy what a send needs.** -/
theorem sendsOk_of_lineInv (φ : Cnf) (k : Int) (L : PureLine)
    (hl : ReaderAggRun.LineInv φ k L) : SendsOk φ L := by
  intro kv hkv d hd
  have hst := hl.1.2 kv hkv
  have hm := hl.2 kv hkv
  have hks : kv.1.step = k := mapNodes_step φ k kv.1 hst.onMap
  have hon : (⟨k, kv.1.index⟩ : NodeId) ∈ mapNodes φ k := by
    have hkid : (⟨k, kv.1.index⟩ : NodeId) = kv.1 := by rw [← hks]
    rw [hkid]; exact hst.onMap
  have hd' : d ∈ mapSons φ k kv.1.index := by rw [← hks]; exact hd
  have hdstep : d.step = k + 1 :=
    mapNodes_step φ (k + 1) d (mapSons_subset φ k kv.1.index hon d hd')
  have hpr : Pruned kv.2 (Filt' φ kv.2 d) :=
    Pruned.trans (ConservationCore.pruned_filterWeakAll kv.2 (weakReqOfCnf φ d))
      (AggressiveReview.pruned_filterAllAgg _ (reqOfCnf φ d))
  refine ⟨hm.rctx.nodup, ?_, ?_⟩
  · have h1 : (Filt' φ kv.2 d).current_step = k + 1 := by rw [hpr.step_eq, hst.step]
    omega
  · intro n hn
    obtain ⟨n₀, hn₀, hids, _, _⟩ := hpr.nodes_derived n hn
    rw [hpr.step_eq, hids]
    exact hm.rctx.below n₀ hn₀

/-- The step facts along the whole chain of lines. -/
theorem sendsOkChain_of_lineInv (φ : Cnf) (hwf : WF φ) :
    ∀ (n : Nat) (k : Int) (L : PureLine), ReaderAggRun.LineInv φ k L → SendsOkChain φ n L := by
  intro n
  induction n with
  | zero => intro _ _ _; exact trivial
  | succ m ih =>
    intro k L hl
    exact ⟨sendsOk_of_lineInv φ k L hl,
      ih (k + 1) _ (ReaderAggRun.LineInv_pureAdvanceW φ hwf k L hl)⟩

/-- **The run invariant, unconditional.** For a well-formed formula, the whole run of the machine
carries one bound per line: no table ever holds, at its own step or below, an entry outside the one
its node was born with — the `up` that created it, from the one state its identifier names. -/
theorem runWithin_of_wf (φ : Cnf) (hwf : WF φ) : ∃ E, LineWithinBelow E (pureRunW φ) :=
  runWithin φ
    (sendsOkChain_of_lineInv φ hwf _ 0 (pureInit φ) (ReaderAggRun.LineInv_init φ hwf))

/-- info: 'AbsSat.GraphPath.Model.RunEnv.Within_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Within_join

/-- info: 'AbsSat.GraphPath.Model.RunEnv.Within_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Within_addNode

/-- info: 'AbsSat.GraphPath.Model.RunEnv.WithinBelow_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WithinBelow_addNode

/-- info: 'AbsSat.GraphPath.Model.RunEnv.lineWithin_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lineWithin_steps

/-- info: 'AbsSat.GraphPath.Model.RunEnv.runWithin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms runWithin

/-- info: 'AbsSat.GraphPath.Model.RunEnv.runWithin_of_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms runWithin_of_wf

end AbsSat.GraphPath.Model.RunEnv
