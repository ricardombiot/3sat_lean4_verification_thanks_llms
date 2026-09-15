-- lean_project/AbsSat/GraphPath/Model/ConservationPins.lean
import AbsSat.GraphPath.Model.ConservationImproves
import AbsSat.GraphPath.Model.SeparationPins

/-!
# Conservation for the pin prune: the machine with the prune loses no solution

`ConservationImproves` proves the weak-filter machine keeps every solution. The
pin prune (`PureDriverPins`) does more: it removes nodes, links and owners
entries, not only global owners. Two new facts carry the argument over.

* **A solution's chain never contradicts its own pins** (`not_idContradicts_sel`).
  Every value the id of a chain node fixes — through its map node or its
  parent's — is the assignment's value, and so is every value a pin of the next
  selected node names. This needs `WF` only (`reqSat_selOfAssign`), not `Sat`.
  The parent is why the branch invariant now also records that every chain
  node's `parent_id` is a selected node (`SelParent`, from
  `mapParent_alongP`).
* **A sound chain survives the prune when none of its nodes is removed**
  (`ChainSound_pinPrune`). The prune keeps every lookup the chain makes: the
  chain's nodes (`node?_pinPrune`), their parents, sons and owners entries among
  the chain.

The pruned state is still a `Pruned` narrowing (`SeparationPins.pruned_pinPrune`),
so the rest is `ConservationImproves` again: `chainSound_up_of_prunedP` (the up
step, now also tracking parents), and the driver bookkeeping with `ShapeOk`.

Result: `pureRunP_ne_nil` and `pureRunP_full_state`.
-/

namespace AbsSat.GraphPath.Model.ConservationPins

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf weakReqOfCnf_sound)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.IdSeparator (IdContradicts fixes fixesMap varVal)
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit mem_insertPure
  mem_insertPure_of_ne key_inj isValid_of_grown insertPure_keys_some insertPure_keys_none
  isValid_initSeed)
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeakAll)
open AbsSat.GraphPath.Model.PureDriverPins
open AbsSat.GraphPath.Model.ConservationImproves (ShapeOk ShapeOk_of_pruned ShapeOk_initSeed
  ShapeOk_addNode ShapeOk_join pruned_filterWeakAll ChainSound_filterWeakAll stepCount_pos)
open AbsSat.GraphPath.Model.SeparationPins (contradictsB_iff pruned_pinPrune)

variable (φ : Cnf)

-- ============================================================
-- A solution's chain never contradicts its own pins
-- ============================================================

section Semantics

variable (a : Assign)

/-- A literal node the assignment selects stands for the assignment's value. -/
theorem varVal_sel (k : Int) (vv : Int × Int) (h : varVal φ (selOfAssign φ a k) = some vv) :
    vv.2 = bit (a vv.1.toNat) := by
  have hstep : (selOfAssign φ a k).step = k := selOfAssign_step φ a k
  rcases step_cases φ k with hk | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | hk | ⟨j, hj, rfl⟩ | hk
  · have hc : (selOfAssign φ a k).step < 0 ∨ litBlock φ ≤ (selOfAssign φ a k).step :=
      Or.inl (by rw [hstep]; exact hk)
    unfold varVal at h
    rw [if_pos hc] at h
    cases h
  · have hidx : (selOfAssign φ a (varStep v)).index = bit (a v) := by
      rw [selOfAssign_var φ a v hv]
    have hc1 : ¬ ((selOfAssign φ a (varStep v)).step < 0 ∨
        litBlock φ ≤ (selOfAssign φ a (varStep v)).step) := by
      rw [hstep]; simp only [varStep, litBlock]; omega
    have hc2 : (selOfAssign φ a (varStep v)).step % 2 = 0 := by
      rw [hstep]; simp only [varStep]; omega
    unfold varVal at h
    rw [if_neg hc1, if_pos hc2, hstep, hidx] at h
    obtain rfl := Option.some.inj h
    show bit (a v) = bit (a (varStep v / 2).toNat)
    rw [show (varStep v / 2).toNat = v by simp only [varStep]; omega]
  · have hidx : (selOfAssign φ a (negStep v)).index = bit (!(a v)) := by
      rw [selOfAssign_neg φ a v hv]
    have hc1 : ¬ ((selOfAssign φ a (negStep v)).step < 0 ∨
        litBlock φ ≤ (selOfAssign φ a (negStep v)).step) := by
      rw [hstep]; simp only [negStep, litBlock]; omega
    have hc2 : ¬ ((selOfAssign φ a (negStep v)).step % 2 = 0) := by
      rw [hstep]; simp only [negStep]; omega
    have hreq := reqOfCnf_neg φ (selOfAssign φ a (negStep v)) v hv hstep
    unfold varVal at h
    rw [if_neg hc1, if_neg hc2, hreq] at h
    have hv2 : varStep v % 2 = 0 := by simp only [varStep]; omega
    change (if varStep v % 2 = 0 then some (varStep v / 2, 1 - (selOfAssign φ a (negStep v)).index)
      else none) = some vv at h
    rw [if_pos hv2, hidx, one_sub_bit_not] at h
    obtain rfl := Option.some.inj h
    show bit (a v) = bit (a (varStep v / 2).toNat)
    rw [show (varStep v / 2).toNat = v by simp only [varStep]; omega]
  · have hc : (selOfAssign φ a k).step < 0 ∨ litBlock φ ≤ (selOfAssign φ a k).step :=
      Or.inr (by rw [hstep]; omega)
    unfold varVal at h
    rw [if_pos hc] at h
    cases h
  · have hc : (selOfAssign φ a (clauseStep φ j)).step < 0 ∨
        litBlock φ ≤ (selOfAssign φ a (clauseStep φ j)).step :=
      Or.inr (by rw [hstep]; simp only [clauseStep, litBlock]; omega)
    unfold varVal at h
    rw [if_pos hc] at h
    cases h
  · have hc : (selOfAssign φ a k).step < 0 ∨ litBlock φ ≤ (selOfAssign φ a k).step :=
      Or.inr (by rw [hstep]; simp only [fusionTop, litBlock] at hk ⊢; omega)
    unfold varVal at h
    rw [if_pos hc] at h
    cases h

/-- A pin of a selected node names the assignment's value. -/
theorem pinVal_sel (hwf : WF φ) (c : Int) (r : NodeId) (hr : r ∈ reqOfCnf φ (selOfAssign φ a c))
    (pv : Int × Int) (h : varVal φ r = some pv) : pv.2 = bit (a pv.1.toNat) := by
  have hrs := reqSat_selOfAssign φ hwf a c r hr
  rw [← hrs] at h
  exact varVal_sel φ a r.step pv h

/-- Every value a selected map node fixes is the assignment's value. -/
theorem fixesMap_sel (hwf : WF φ) (k : Int) (vv : Int × Int)
    (h : vv ∈ fixesMap φ (selOfAssign φ a k)) : vv.2 = bit (a vv.1.toNat) := by
  unfold fixesMap at h
  split at h
  · cases hvv : varVal φ (selOfAssign φ a k) with
    | none => rw [hvv] at h; exact absurd h List.not_mem_nil
    | some x =>
      rw [hvv] at h
      have hx : vv = x := List.mem_singleton.mp h
      subst hx
      exact varVal_sel φ a k vv hvv
  · split at h
    · exact absurd h List.not_mem_nil
    · obtain ⟨r, hr, hvr⟩ := List.mem_filterMap.mp h
      exact pinVal_sel φ a hwf k r hr vv hvr

/-- A path node's parent is `none` or a node the assignment selects. -/
def SelParent (w : PathNodeId) : Prop :=
  w.parent_id = none ∨ ∃ j, w.parent_id = some (selOfAssign φ a j)

/-- **A chain node of the assignment never contradicts a pin of a selected node.** -/
theorem not_idContradicts_sel (hwf : WF φ) (c : Int) (w : PathNodeId)
    (hid : ∃ k, w.id = selOfAssign φ a k) (hpar : SelParent φ a w) :
    ¬ IdContradicts φ (reqOfCnf φ (selOfAssign φ a c)) w := by
  rintro ⟨vv, hvv, r, hr, pv, hvr, h1, h2⟩
  have hp := pinVal_sel φ a hwf c r hr pv hvr
  have hv : vv.2 = bit (a vv.1.toNat) := by
    obtain ⟨k, hk⟩ := hid
    unfold fixes at hvv
    rcases List.mem_append.mp hvv with h | h
    · rw [hk] at h
      exact fixesMap_sel φ a hwf k vv h
    · rcases hpar with hn | ⟨j, hj⟩
      · rw [hn] at h
        exact absurd h List.not_mem_nil
      · rw [hj] at h
        exact fixesMap_sel φ a hwf j vv h
  exact h2 (by rw [hp, hv, h1])

end Semantics

-- ============================================================
-- A sound chain survives the prune
-- ============================================================

/-- What the prune does to a node it keeps. -/
def pinUpd (d : NodeId) (n : PNodeM) : PNodeM :=
  { n with
    owners := n.owners.filter (fun q => !contradictsB φ (pinValues φ d) q),
    parents := n.parents.filter (fun p => !contradictsB φ (pinValues φ d) p),
    sons := n.sons.filter (fun s => !contradictsB φ (pinValues φ d) s) }

theorem find?_filter_map_id (f : PNodeM → PNodeM) (hf : ∀ n, (f n).id = n.id)
    (p : PNodeM → Bool) (pid : PathNodeId) (hp : ∀ n, n.id = pid → p n = true) :
    ∀ l : List PNodeM,
      ((l.filter p).map f).find? (fun n => n.id == pid) = (l.find? (fun n => n.id == pid)).map f
  | [] => rfl
  | n :: ns => by
    have ih := find?_filter_map_id f hf p pid hp ns
    cases hb : (n.id == pid) with
    | true =>
      have hpn : p n = true := hp n (eq_of_beq hb)
      have hfb : ((f n).id == pid) = true := by rw [hf]; exact hb
      simp only [List.filter_cons, hpn, ↓reduceIte, List.map_cons, List.find?_cons, hfb, hb]
      rfl
    | false =>
      have hfb : ((f n).id == pid) = false := by rw [hf]; exact hb
      cases hpn : p n with
      | true =>
        simp only [List.filter_cons, hpn, ↓reduceIte, List.map_cons, List.find?_cons, hfb, hb]
        exact ih
      | false =>
        simp only [List.filter_cons, hpn, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hb]
        exact ih

theorem node?_pinPrune (d : NodeId) (g : GPathM) (pid : PathNodeId)
    (hgood : contradictsB φ (pinValues φ d) pid = false) :
    (pinPrune φ d g).node? pid = (g.node? pid).map (pinUpd φ d) := by
  show ((g.nodes.filter (fun n => !contradictsB φ (pinValues φ d) n.id)).map (pinUpd φ d)).find?
      (fun n => n.id == pid) = (g.nodes.find? (fun n => n.id == pid)).map (pinUpd φ d)
  exact find?_filter_map_id (pinUpd φ d) (fun _ => rfl) _ pid
    (fun n hn => by show (!contradictsB φ (pinValues φ d) n.id) = true; rw [hn, hgood]; rfl) g.nodes

/-- **A sound chain whose nodes the prune keeps survives the prune.** -/
theorem ChainSound_pinPrune (d : NodeId) (g : GPathM) (sel : Int → PathNodeId)
    (h : ChainSound g sel)
    (hgood : ∀ k, 0 ≤ k → k < g.current_step → contradictsB φ (pinValues φ d) (sel k) = false) :
    ChainSound (pinPrune φ d g) sel := by
  obtain ⟨⟨⟨hnode, hpar⟩, howned, hgow⟩, hself, hson, hroot⟩ := h
  have hN : ∀ k, 0 ≤ k → k < g.current_step →
      (pinPrune φ d g).node? (sel k) = (g.node? (sel k)).map (pinUpd φ d) :=
    fun k h0 h1 => node?_pinPrune φ d g _ (hgood k h0 h1)
  have hkeep : ∀ k, 0 ≤ k → k < g.current_step →
      (!contradictsB φ (pinValues φ d) (sel k)) = true := by
    intro k h0 h1
    rw [hgood k h0 h1]
    rfl
  refine ⟨⟨⟨fun k h0 h1 => ?_, fun k h0 h1 => ?_⟩, fun i j hi hj hi' hj' hne => ?_,
    fun k h0 h1 => ?_⟩, fun k h0 h1 => ?_, fun k h0 h1 => ?_, hroot⟩
  · obtain ⟨hs, hst⟩ := hnode k h0 h1
    refine ⟨?_, hst⟩
    rw [hN k h0 h1]
    cases hg : g.node? (sel k) with
    | none => rw [hg] at hs; exact absurd hs (by decide)
    | some n => rfl
  · have h1' : k + 1 < g.current_step := h1
    have hp := hpar k h0 h1
    rw [hN (k + 1) (by omega) h1]
    cases hg : g.node? (sel (k + 1)) with
    | none => rw [hg] at hp; exact absurd hp List.not_mem_nil
    | some n =>
      rw [hg] at hp
      exact List.mem_filter.mpr ⟨hp, hkeep k h0 (by omega)⟩
  · have ho := howned i j hi hj hi' hj' hne
    unfold ownersOf at ho ⊢
    rw [hN j hj hj']
    cases hg : g.node? (sel j) with
    | none => rw [hg] at ho; exact absurd ho List.not_mem_nil
    | some n =>
      rw [hg] at ho
      have ho' : sel i ∈ n.owners.filter (fun q => q.id.step == i) := ho
      obtain ⟨hm, hs⟩ := List.mem_filter.mp ho'
      exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hm, hkeep i hi hi'⟩, hs⟩
  · exact List.mem_filter.mpr ⟨hgow k h0 h1, hkeep k h0 h1⟩
  · have hs := hself k h0 h1
    unfold ownersOf at hs ⊢
    rw [hN k h0 h1]
    cases hg : g.node? (sel k) with
    | none => rw [hg] at hs; exact absurd hs List.not_mem_nil
    | some n =>
      rw [hg] at hs
      exact List.mem_filter.mpr ⟨hs, hkeep k h0 h1⟩
  · have h1' : k + 1 < g.current_step := h1
    have hs := hson k h0 h1
    unfold sonsOf at hs ⊢
    rw [hN k h0 (by omega)]
    cases hg : g.node? (sel k) with
    | none => rw [hg] at hs; exact absurd hs List.not_mem_nil
    | some n =>
      rw [hg] at hs
      exact List.mem_filter.mpr ⟨hs, hkeep (k + 1) (by omega) h1⟩

theorem ShapeOk_upFilteringPin (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (h : ShapeOk g) : ShapeOk (upFilteringPin φ g d title) := by
  have hpr : Pruned g (filterAll (pinPrune φ d (filterWeakAll g (weakReqOfCnf φ d))) (reqOfCnf φ d)) :=
    Pruned.trans (Pruned.trans (pruned_filterWeakAll g _) (pruned_pinPrune φ d _))
      (pruned_filterAll _ _)
  have hf := ShapeOk_of_pruned hpr h
  simp only [upFilteringPin, GPathM.up]
  split
  · exact ShapeOk_addNode _ d title (by rw [hpr.step_eq]; exact hd) hf
  · exact hf

-- ============================================================
-- The branch of an assignment, through the machine with the prune
-- ============================================================

variable (a : Assign)

inductive AlongAssignP : GPathM → Prop where
  | seed (title : String) :
      AlongAssignP (GPathM.initSeed (selOfAssign φ a 0) title)
  | up (g : GPathM) (title : String) :
      AlongAssignP g →
      AlongAssignP (upFilteringPin φ g (selOfAssign φ a g.current_step) title)
  | joinL (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₂ : ShapeOk g₂) :
      AlongAssignP g₁ → AlongAssignP (GPathM.join g₁ g₂)
  | joinR (g₁ g₂ : GPathM) (hok : GPathM.okJoin g₁ g₂ = true) (h₁ : ShapeOk g₁) :
      AlongAssignP g₂ → AlongAssignP (GPathM.join g₁ g₂)

theorem shapeOk_of_alongP (g : GPathM) (h : AlongAssignP φ a g) : ShapeOk g := by
  induction h with
  | seed title => exact ShapeOk_initSeed _ title (selOfAssign_step φ a 0)
  | up g title _ ih =>
    exact ShapeOk_upFilteringPin φ g _ title (selOfAssign_step φ a g.current_step) ih
  | joinL g₁ g₂ hok h₂ _ ih => exact ShapeOk_join g₁ g₂ hok ih h₂
  | joinR g₁ g₂ hok h₁ _ ih => exact ShapeOk_join g₁ g₂ hok h₁ ih

/-- The map node the last `up` visited is a selected node. -/
theorem mapParent_alongP (g : GPathM) (h : AlongAssignP φ a g) :
    g.map_parent = none ∨ ∃ j, g.map_parent = some (selOfAssign φ a j) := by
  induction h with
  | seed title =>
    unfold GPathM.initSeed GPathM.up
    rw [if_pos (by rfl : isValid empty = true)]
    exact Or.inr ⟨0, rfl⟩
  | up g title _ ih =>
    have hpr : Pruned g (filterAll (pinPrune φ (selOfAssign φ a g.current_step)
        (filterWeakAll g (weakReqOfCnf φ (selOfAssign φ a g.current_step))))
        (reqOfCnf φ (selOfAssign φ a g.current_step))) :=
      Pruned.trans (Pruned.trans (pruned_filterWeakAll g _) (pruned_pinPrune φ _ _))
        (pruned_filterAll _ _)
    simp only [upFilteringPin, GPathM.up]
    split
    · exact Or.inr ⟨g.current_step, rfl⟩
    · rw [hpr.map_parent_eq]
      exact ih
  | joinL g₁ g₂ hok _ _ ih => exact ih
  | joinR g₁ g₂ hok _ _ ih =>
    have hmp : g₁.map_parent = g₂.map_parent := by
      simp only [okJoin, Bool.and_eq_true, beq_iff_eq] at hok
      exact hok.1.1.2
    show g₁.map_parent = none ∨ ∃ j, g₁.map_parent = some (selOfAssign φ a j)
    rw [hmp]
    exact ih

/-- `ConservationImproves.chainSound_up_of_pruned`, also tracking that every chain
node's parent is a selected node. -/
theorem chainSound_up_of_prunedP (hwf : WF φ) (g gw : GPathM) (hpr : Pruned g gw)
    (hshape : ShapeOk g)
    (hmp : g.map_parent = none ∨ ∃ j, g.map_parent = some (selOfAssign φ a j))
    (sel : Int → PathNodeId) (hselw : ChainSound gw sel)
    (hids : ∀ k, 0 ≤ k → k < g.current_step →
      (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k))
    (title : String) :
    ∃ sel', ChainSound (upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
          (selOfAssign φ a g.current_step) title) sel'
      ∧ (upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
          (selOfAssign φ a g.current_step) title).current_step = g.current_step + 1
      ∧ ∀ k, 0 ≤ k → k < g.current_step + 1 →
          (sel' k).id = selOfAssign φ a k ∧ SelParent φ a (sel' k) := by
  have hgs : gw.current_step = g.current_step := hpr.step_eq
  have hreqs : ∀ req ∈ reqOfCnf φ (selOfAssign φ a g.current_step),
      0 ≤ req.step → req.step < gw.current_step → (sel req.step).id = req := by
    intro req hreq hr0 hr1
    rw [(hids req.step hr0 (by omega)).1]
    exact reqSat_selOfAssign φ hwf a g.current_step req hreq
  have hpf := pruned_filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))
  have hfil : ChainSound (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))) sel :=
    ChainSound_filterAll gw _ sel hselw hreqs
  have hvalid : isValid (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))) = true :=
    PickInduction.isValid_of_ChainG _ sel hfil.chain
  have hshf : ShapeOk (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))) :=
    ShapeOk_of_pruned (Pruned.trans hpr hpf) hshape
  have hd : (selOfAssign φ a g.current_step).step
      = (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))).current_step := by
    rw [hpf.step_eq, hgs, selOfAssign_step]
  have hshapeEq : upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
      (selOfAssign φ a g.current_step) title
      = addNode (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
        (selOfAssign φ a g.current_step) title := by
    simp only [upFiltering, GPathM.up, hvalid, if_pos]
  have hcur : (upFiltering gw (reqOfCnf φ (selOfAssign φ a g.current_step))
      (selOfAssign φ a g.current_step) title).current_step = g.current_step + 1 := by
    rw [hshapeEq, addNode_current, hpf.step_eq, hgs]
  refine ⟨extend (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
    (selOfAssign φ a g.current_step) sel, ?_, hcur, ?_⟩
  · exact ChainSound_upFiltering gw _ _ title hvalid hd hshf.1 hshf.2 sel hselw hreqs
  · intro k hk0 hk
    if he : k = g.current_step then
      have hextend : extend (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
          (selOfAssign φ a g.current_step) sel g.current_step
          = newPid (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
            (selOfAssign φ a g.current_step) := by
        simp only [extend, if_pos (hpf.step_eq.trans hgs).symm]
      rw [he, hextend]
      refine ⟨rfl, ?_⟩
      show (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))).map_parent = none ∨
        ∃ j, (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step))).map_parent
          = some (selOfAssign φ a j)
      rw [hpf.map_parent_eq, hpr.map_parent_eq]
      exact hmp
    else
      rw [extend_below (filterAll gw (reqOfCnf φ (selOfAssign φ a g.current_step)))
        (selOfAssign φ a g.current_step) sel k (by rw [hpf.step_eq, hgs]; omega)]
      exact hids k hk0 (by omega)

/-- **The conservation law for the machine with the pin prune.** -/
theorem chainSound_alongP (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignP φ a g) :
    ∃ sel, ChainSound g sel ∧
      ∀ k, 0 ≤ k → k < g.current_step →
        (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k) := by
  induction h with
  | seed title =>
    refine ⟨fun _ => { id := selOfAssign φ a 0, parent_id := none },
      ChainSound_initSeed _ title (selOfAssign_step φ a 0), ?_⟩
    intro k hlo hhi
    rw [initSeed_current] at hhi
    have : k = 0 := by omega
    subst this
    exact ⟨rfl, Or.inl rfl⟩
  | up g title hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    have hweak : ∀ e ∈ weakReqOfCnf φ (selOfAssign φ a g.current_step),
        ∀ k, 0 ≤ k → k < g.current_step → k = e.1 → (sel k).id ∈ e.2 := by
      intro e he k hk0 hk hke
      rw [(hids k hk0 hk).1, hke]
      exact weakReqOfCnf_sound φ a hsat g.current_step e he
    have hw := ChainSound_filterWeakAll _ g sel hsel hweak
    have hwstep := (PureDriverImproves.filterWeakAll_frame
      (weakReqOfCnf φ (selOfAssign φ a g.current_step)) g).2.1
    have hgood : ∀ k, 0 ≤ k →
        k < (filterWeakAll g (weakReqOfCnf φ (selOfAssign φ a g.current_step))).current_step →
        contradictsB φ (pinValues φ (selOfAssign φ a g.current_step)) (sel k) = false := by
      intro k hk0 hk
      rw [hwstep] at hk
      have hnot := not_idContradicts_sel φ a hwf g.current_step (sel k)
        ⟨k, (hids k hk0 hk).1⟩ (hids k hk0 hk).2
      cases hc : contradictsB φ (pinValues φ (selOfAssign φ a g.current_step)) (sel k) with
      | false => rfl
      | true => exact absurd ((contradictsB_iff φ _ _).mp hc) hnot
    have hp := ChainSound_pinPrune φ _ _ sel hw hgood
    obtain ⟨sel', hs', hcur, hids'⟩ :=
      chainSound_up_of_prunedP φ a hwf g _
        (Pruned.trans (pruned_filterWeakAll g _) (pruned_pinPrune φ _ _))
        (shapeOk_of_alongP φ a g hal) (mapParent_alongP φ a g hal) sel hp hids title
    exact ⟨sel', hs', fun k hk0 hk => hids' k hk0 (lt_of_lt_of_eq hk hcur)⟩
  | joinL g₁ g₂ hok h₂ hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_left g₁ g₂).step_eq] at hk; exact hk)⟩
  | joinR g₁ g₂ hok h₁ hal ih =>
    obtain ⟨sel, hsel, hids⟩ := ih
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hsel, fun k hk0 hk => hids k hk0
      (by rw [(grown_join_right g₁ g₂ hok).step_eq] at hk; exact hk)⟩

theorem isValid_alongP (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignP φ a g) :
    isValid g = true := by
  obtain ⟨sel, hsel, _⟩ := chainSound_alongP φ a hwf hsat g h
  exact PickInduction.isValid_of_ChainG g sel hsel.chain

theorem inhabited_alongP (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignP φ a g) :
    AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨sel, hsel, _⟩ := chainSound_alongP φ a hwf hsat g h
  exact ⟨pathOf sel g, sel, hsel.chain.1, hsel.chain.2.1, rfl⟩

-- ============================================================
-- The driver: the line invariant
-- ============================================================

structure StateOkP (φ : Cnf) (k : Int) (kv : NodeId × GPathM) : Prop where
  onMap : kv.1 ∈ mapNodes φ k
  shape : ShapeOk kv.2
  step  : kv.2.current_step = k + 1
  par   : kv.2.map_parent = some kv.1
  valid : isValid kv.2 = true

def LineOkP (φ : Cnf) (k : Int) (line : PureLine) : Prop :=
  (line.map (·.1)).Nodup ∧ ∀ kv ∈ line, StateOkP φ k kv

theorem okJoin_of_stateOkP (k : Int) (key : NodeId) (e g : GPathM)
    (he : StateOkP φ k (key, e)) (hg : StateOkP φ k (key, g)) : okJoin e g = true := by
  simp only [okJoin, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨he.step.trans hg.step.symm, he.par.trans hg.par.symm⟩, he.valid⟩, hg.valid⟩

theorem stateOkP_doJoin (k : Int) (key : NodeId) (e g : GPathM)
    (he : StateOkP φ k (key, e)) (hg : StateOkP φ k (key, g)) :
    StateOkP φ k (key, doJoin e g) := by
  have hok := okJoin_of_stateOkP φ k key e g he hg
  simp only [doJoin, hok, if_pos]
  exact ⟨he.onMap, ShapeOk_join e g hok he.shape hg.shape, he.step, he.par,
    isValid_of_grown (grown_join_left e g) he.valid⟩

theorem LineOkP_insertPure (k : Int) (line : PureLine) (key : NodeId) (g : GPathM)
    (hl : LineOkP φ k line) (hg : StateOkP φ k (key, g)) :
    LineOkP φ k (insertPure line key g) := by
  obtain ⟨hnd, hall⟩ := hl
  cases hf : line.find? (fun x => x.1 == key) with
  | none =>
    have hnotin : ∀ (b : NodeId) (x : GPathM), (b, x) ∈ line → ¬ b = key := by
      intro b x hbx hbk
      have h := List.find?_eq_none.mp hf (b, x) hbx
      exact h (by simp only [hbk]; exact beq_iff_eq.mpr rfl)
    constructor
    · rw [insertPure_keys_none line key g hf]
      rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      simpa using hnotin
    · intro kv hkv
      simp only [insertPure, hf] at hkv
      rcases List.mem_append.mp hkv with h | h
      · exact hall kv h
      · rcases List.mem_singleton.mp h with rfl
        exact hg
  | some e =>
    have hekey : e.1 = key :=
      eq_of_beq (List.find?_some (p := fun x : NodeId × GPathM => x.1 == key) hf)
    have hemem : e ∈ line := List.mem_of_find?_eq_some hf
    have hesok : StateOkP φ k (key, e.2) := by
      have h := hall e hemem
      rwa [← hekey]
    constructor
    · rw [insertPure_keys_some line key g e hf]; exact hnd
    · intro kv hkv
      simp only [insertPure, hf] at hkv
      obtain ⟨x, hx, hEq⟩ := List.mem_map.mp hkv
      cases hb : x.1 == key with
      | true =>
        have : kv = (key, doJoin e.2 g) := by rw [← hEq]; simp only [hb]; rfl
        rw [this]
        exact stateOkP_doJoin φ k key e.2 g hesok hg
      | false =>
        have : kv = x := by rw [← hEq]; simp only [hb]; rfl
        rw [this]
        exact hall x hx

-- ============================================================
-- The branch's entry
-- ============================================================

def CarriesP (k : Int) (line : PureLine) : Prop :=
  ∃ g, (selOfAssign φ a k, g) ∈ line ∧ AlongAssignP φ a g ∧ g.current_step = k + 1

theorem CarriesP_insertPure (k : Int) (line : PureLine)
    (key : NodeId) (g' : GPathM) (hl : LineOkP φ k line) (hg' : StateOkP φ k (key, g'))
    (hc : CarriesP φ a k line) : CarriesP φ a k (insertPure line key g') := by
  obtain ⟨g, hmem, hal, hcs⟩ := hc
  obtain ⟨hnd, hall⟩ := hl
  by_cases hkey : selOfAssign φ a k = key
  · subst hkey
    cases hf : line.find? (fun x => x.1 == selOfAssign φ a k) with
    | none =>
      exact absurd (List.find?_eq_none.mp hf _ hmem) (by simp)
    | some e =>
      have hemem : e ∈ line := List.mem_of_find?_eq_some hf
      have hekey : e.1 = selOfAssign φ a k :=
        eq_of_beq (List.find?_some
          (p := fun x : NodeId × GPathM => x.1 == selOfAssign φ a k) hf)
      have hee : e = (selOfAssign φ a k, g) :=
        key_inj line hnd e hemem (selOfAssign φ a k, g) hmem hekey
      have hesok : StateOkP φ k (selOfAssign φ a k, g) := by
        have h := hall e hemem
        rw [hee] at h
        exact h
      have hok : okJoin g g' = true :=
        okJoin_of_stateOkP φ k (selOfAssign φ a k) g g' hesok hg'
      refine ⟨join g g', ?_, AlongAssignP.joinL g g' hok hg'.shape hal, hcs⟩
      simp only [insertPure, hf, hee, doJoin, hok, if_pos]
      refine List.mem_map.mpr ⟨(selOfAssign φ a k, g), hmem, ?_⟩
      simp
  · exact ⟨g, mem_insertPure_of_ne line key _ g' g hkey hmem, hal, hcs⟩

theorem CarriesP_of_insertPure_at (k : Int) (line : PureLine)
    (g' : GPathM) (hl : LineOkP φ k line) (hg' : StateOkP φ k (selOfAssign φ a k, g'))
    (hal : AlongAssignP φ a g') :
    CarriesP φ a k (insertPure line (selOfAssign φ a k) g') := by
  obtain ⟨h, hmem, hcase⟩ := mem_insertPure line (selOfAssign φ a k) g'
  refine ⟨h, hmem, ?_, ?_⟩
  · rcases hcase with rfl | ⟨e, hem, rfl⟩
    · exact hal
    · have he : StateOkP φ k (selOfAssign φ a k, e) := hl.2 _ hem
      have hok := okJoin_of_stateOkP φ k _ e g' he hg'
      simp only [doJoin, hok, if_pos]
      exact AlongAssignP.joinR e g' hok he.shape hal
  · rcases hcase with rfl | ⟨e, hem, rfl⟩
    · exact hg'.step
    · have he : StateOkP φ k (selOfAssign φ a k, e) := hl.2 _ hem
      have hok := okJoin_of_stateOkP φ k _ e g' he hg'
      simp only [doJoin, hok, if_pos]
      rw [(grown_join_left e g').step_eq]
      exact he.step

-- ============================================================
-- One send
-- ============================================================

theorem isValid_filter_of_sentP (g : GPathM) (d : NodeId)
    (hval : isValid (upFilteringPin φ g d "") = true) :
    isValid (filterAll (pinPrune φ d (filterWeakAll g (weakReqOfCnf φ d))) (reqOfCnf φ d)) = true := by
  by_cases h : isValid (filterAll (pinPrune φ d (filterWeakAll g (weakReqOfCnf φ d))) (reqOfCnf φ d)) = true
  · exact h
  · exfalso
    have he : upFilteringPin φ g d ""
        = filterAll (pinPrune φ d (filterWeakAll g (weakReqOfCnf φ d))) (reqOfCnf φ d) := by
      simp only [upFilteringPin, GPathM.up, if_neg h]
    rw [he] at hval
    exact h hval

theorem StateOkP_sent (k : Int) (kv : NodeId × GPathM) (hkv : StateOkP φ k kv)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringPin φ kv.2 d "") = true) :
    StateOkP φ (k + 1) (d, upFilteringPin φ kv.2 d "") := by
  have hkey : kv.1.step = k := mapNodes_step φ k kv.1 hkv.onMap
  have hmk : (⟨k, kv.1.index⟩ : NodeId) ∈ mapNodes φ k := by
    have : (⟨k, kv.1.index⟩ : NodeId) = kv.1 := by
      cases hkv1 : kv.1 with
      | mk sp ix =>
        rw [hkv1] at hkey
        simp only at hkey ⊢
        rw [hkey]
    rw [this]; exact hkv.onMap
  have hd' : d ∈ mapNodes φ (k + 1) :=
    mapSons_subset φ k kv.1.index hmk d (by rw [← hkey]; exact hd)
  have hdstep : d.step = k + 1 := mapNodes_step φ (k + 1) d hd'
  have hfv := isValid_filter_of_sentP φ kv.2 d hval
  have hpr : Pruned kv.2 (filterAll (pinPrune φ d (filterWeakAll kv.2 (weakReqOfCnf φ d))) (reqOfCnf φ d)) :=
    Pruned.trans (Pruned.trans (pruned_filterWeakAll _ _) (pruned_pinPrune φ d _)) (pruned_filterAll _ _)
  have hshape : upFilteringPin φ kv.2 d ""
      = addNode (filterAll (pinPrune φ d (filterWeakAll kv.2 (weakReqOfCnf φ d))) (reqOfCnf φ d)) d "" := by
    simp only [upFilteringPin, GPathM.up, hfv, if_pos]
  refine ⟨hd', ?_, ?_, ?_, hval⟩
  · exact ShapeOk_upFilteringPin φ kv.2 d "" (by rw [hdstep, hkv.step]) hkv.shape
  · rw [hshape, addNode_current, hpr.step_eq, hkv.step]
  · rw [hshape]; rfl

theorem LineOkP_sendToP (k : Int) (kv : NodeId × GPathM) (hkv : StateOkP φ k kv)
    (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index) (next : PureLine)
    (hn : LineOkP φ (k + 1) next) : LineOkP φ (k + 1) (sendToP φ kv.2 next d) := by
  simp only [sendToP]
  split
  · next hval => exact LineOkP_insertPure φ (k + 1) next d _ hn (StateOkP_sent φ k kv hkv d hd hval)
  · exact hn

theorem LineOkP_sendAllP (k : Int) (kv : NodeId × GPathM) (hkv : StateOkP φ k kv)
    (next : PureLine) (hn : LineOkP φ (k + 1) next) :
    LineOkP φ (k + 1) (sendAllP φ kv next) := by
  simp only [sendAllP]
  have : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc, LineOkP φ (k + 1) acc → LineOkP φ (k + 1) (l.foldl (sendToP φ kv.2) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
        (LineOkP_sendToP φ k kv hkv x (hx x List.mem_cons_self) acc h)
  exact this _ (fun _ hd => hd) next hn

theorem LineOkP_pureAdvanceP (k : Int) (line : PureLine) (hl : LineOkP φ k line) :
    LineOkP φ (k + 1) (pureAdvanceP φ line) := by
  simp only [pureAdvanceP]
  obtain ⟨_, hall⟩ := hl
  have : ∀ (l : PureLine), (∀ kv ∈ l, StateOkP φ k kv) →
      ∀ acc, LineOkP φ (k + 1) acc →
        LineOkP φ (k + 1) (l.foldl (fun next kv => sendAllP φ kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
        (LineOkP_sendAllP φ k x (hx x List.mem_cons_self) acc h)
  exact this line hall [] ⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

-- ============================================================
-- The branch through the two folds
-- ============================================================

theorem advance_targetP (hwf : WF φ) (hsat : Sat a φ)
    (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssignP φ a g) (hcs : g.current_step = k + 1) :
    selOfAssign φ a (k + 1)
        ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index
      ∧ AlongAssignP φ a (upFilteringPin φ g (selOfAssign φ a (k + 1)) "")
      ∧ isValid (upFilteringPin φ g (selOfAssign φ a (k + 1)) "") = true := by
  have hson : selOfAssign φ a (k + 1)
      ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index := by
    rw [selOfAssign_step]
    exact selOfAssign_son φ a hsat k h0 hk
  have hup : AlongAssignP φ a (upFilteringPin φ g (selOfAssign φ a (k + 1)) "") := by
    have := AlongAssignP.up (φ := φ) (a := a) g "" hal
    rwa [hcs] at this
  exact ⟨hson, hup, isValid_alongP φ a hwf hsat _ hup⟩

theorem CarriesP_sendToP (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOkP φ k kv) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (next : PureLine) (hn : LineOkP φ (k + 1) next) (hc : CarriesP φ a (k + 1) next) :
    CarriesP φ a (k + 1) (sendToP φ kv.2 next d) := by
  simp only [sendToP]
  split
  · next hval =>
      exact CarriesP_insertPure φ a (k + 1) next d _ hn (StateOkP_sent φ k kv hkv d hd hval) hc
  · exact hc

theorem sons_fold_monoP (k : Int) (kv : NodeId × GPathM) (hkv : StateOkP φ k kv) :
    ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
      ∀ acc, LineOkP φ (k + 1) acc → CarriesP φ a (k + 1) acc →
        LineOkP φ (k + 1) (l.foldl (sendToP φ kv.2) acc)
          ∧ CarriesP φ a (k + 1) (l.foldl (sendToP φ kv.2) acc) := by
  intro l
  induction l with
  | nil => intro _ acc h hc; exact ⟨h, hc⟩
  | cons x xs ih =>
    intro hx acc h hc
    simp only [List.foldl_cons]
    exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
      (LineOkP_sendToP φ k kv hkv x (hx x List.mem_cons_self) acc h)
      (CarriesP_sendToP φ a k kv hkv x (hx x List.mem_cons_self) acc h hc)

theorem CarriesP_sendAllP (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOkP φ k kv) (next : PureLine) (hn : LineOkP φ (k + 1) next)
    (hc : CarriesP φ a (k + 1) next) : CarriesP φ a (k + 1) (sendAllP φ kv next) := by
  simp only [sendAllP]
  exact (sons_fold_monoP φ a k kv hkv _ (fun _ hd => hd) next hn hc).2

theorem sons_fold_establishP (hwf : WF φ) (hsat : Sat a φ)
    (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (g : GPathM) (hal : AlongAssignP φ a g) (hcs : g.current_step = k + 1)
    (hkv : StateOkP φ k (selOfAssign φ a k, g)) :
    ∀ (l : List NodeId),
      (∀ d ∈ l, d ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index) →
      selOfAssign φ a (k + 1) ∈ l →
      ∀ acc, LineOkP φ (k + 1) acc →
        LineOkP φ (k + 1) (l.foldl (sendToP φ g) acc)
          ∧ CarriesP φ a (k + 1) (l.foldl (sendToP φ g) acc) := by
  obtain ⟨hson, hup, hval⟩ := advance_targetP φ a hwf hsat k h0 hk g hal hcs
  intro l
  induction l with
  | nil => intro _ hd; exact absurd hd List.not_mem_nil
  | cons x xs ih =>
    intro hx hd acc h
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hd with rfl | hd'
    · have hsend : sendToP φ g acc (selOfAssign φ a (k + 1))
          = insertPure acc (selOfAssign φ a (k + 1))
              (upFilteringPin φ g (selOfAssign φ a (k + 1)) "") := by
        simp only [sendToP, hval, if_true]
      have hsok : StateOkP φ (k + 1) (selOfAssign φ a (k + 1),
          upFilteringPin φ g (selOfAssign φ a (k + 1)) "") :=
        StateOkP_sent φ k (selOfAssign φ a k, g) hkv _ hson hval
      have hbase : LineOkP φ (k + 1) (sendToP φ g acc (selOfAssign φ a (k + 1)))
          ∧ CarriesP φ a (k + 1) (sendToP φ g acc (selOfAssign φ a (k + 1))) := by
        rw [hsend]
        exact ⟨LineOkP_insertPure φ (k + 1) acc _ _ h hsok,
          CarriesP_of_insertPure_at φ a (k + 1) acc _ h hsok hup⟩
      exact sons_fold_monoP φ a k (selOfAssign φ a k, g) hkv xs
        (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _ hbase.1 hbase.2
    · exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) hd' _
        (LineOkP_sendToP φ k (selOfAssign φ a k, g) hkv x (hx x List.mem_cons_self) acc h)

theorem outer_fold_monoP (k : Int) :
    ∀ (l : PureLine), (∀ kv ∈ l, StateOkP φ k kv) →
      ∀ acc, LineOkP φ (k + 1) acc → CarriesP φ a (k + 1) acc →
        LineOkP φ (k + 1) (l.foldl (fun next kv => sendAllP φ kv next) acc)
          ∧ CarriesP φ a (k + 1) (l.foldl (fun next kv => sendAllP φ kv next) acc) := by
  intro l
  induction l with
  | nil => intro _ acc h hc; exact ⟨h, hc⟩
  | cons x xs ih =>
    intro hx acc h hc
    simp only [List.foldl_cons]
    exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
      (LineOkP_sendAllP φ k x (hx x List.mem_cons_self) acc h)
      (CarriesP_sendAllP φ a k x (hx x List.mem_cons_self) acc h hc)

/-- **One improved driver step conserves the branch.** -/
theorem CarriesP_pureAdvanceP (hwf : WF φ) (hsat : Sat a φ)
    (k : Int) (h0 : 0 ≤ k) (hk : k + 1 < stepCount φ)
    (line : PureLine) (hl : LineOkP φ k line) (hc : CarriesP φ a k line) :
    CarriesP φ a (k + 1) (pureAdvanceP φ line) := by
  obtain ⟨g, hmem, hal, hcs⟩ := hc
  have hkv : StateOkP φ k (selOfAssign φ a k, g) := hl.2 _ hmem
  simp only [pureAdvanceP]
  have main : ∀ (l : PureLine), (∀ kv ∈ l, StateOkP φ k kv) →
      (selOfAssign φ a k, g) ∈ l →
      ∀ acc, LineOkP φ (k + 1) acc →
        LineOkP φ (k + 1) (l.foldl (fun next kv => sendAllP φ kv next) acc)
          ∧ CarriesP φ a (k + 1) (l.foldl (fun next kv => sendAllP φ kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ hd; exact absurd hd List.not_mem_nil
    | cons x xs ih =>
      intro hx hd acc h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · have hbase : LineOkP φ (k + 1) (sendAllP φ (selOfAssign φ a k, g) acc)
            ∧ CarriesP φ a (k + 1) (sendAllP φ (selOfAssign φ a k, g) acc) := by
          simp only [sendAllP]
          exact sons_fold_establishP φ a hwf hsat k h0 hk g hal hcs hkv _
            (fun _ hdm => hdm)
            (by
              rw [selOfAssign_step]
              exact selOfAssign_son φ a hsat k h0 hk)
            acc h
        exact outer_fold_monoP φ a k xs (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) _
          hbase.1 hbase.2
      · exact ih (fun kv hkv' => hx kv (List.mem_cons_of_mem _ hkv')) hd' _
          (LineOkP_sendAllP φ k x (hx x List.mem_cons_self) acc h)
  exact (main line hl.2 hmem [] ⟨by simp, by intro kv hkv'; exact absurd hkv' List.not_mem_nil⟩).2

-- ============================================================
-- The first line, and the whole run
-- ============================================================

theorem stateOkP_initSeed (d : NodeId) (hd : d ∈ mapNodes φ 0) :
    StateOkP φ 0 (d, GPathM.initSeed d "") := by
  have hstep : d.step = 0 := mapNodes_step φ 0 d hd
  refine ⟨hd, ShapeOk_initSeed d "" hstep, ?_, ?_, isValid_initSeed d "" hstep⟩
  · simp only [initSeed_current]; omega
  · rfl

theorem initP_ok (hsat : Sat a φ) : LineOkP φ 0 (pureInit φ) ∧ CarriesP φ a 0 (pureInit φ) := by
  have hsel : selOfAssign φ a 0 ∈ mapNodes φ 0 :=
    selOfAssign_onMap φ a hsat 0 (by omega) (stepCount_pos φ)
  simp only [pureInit]
  have mono : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) →
      ∀ acc, LineOkP φ 0 acc → CarriesP φ a 0 acc →
        LineOkP φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc)
          ∧ CarriesP φ a 0
            (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h hc; exact ⟨h, hc⟩
    | cons x xs ih =>
      intro hx acc h hc
      simp only [List.foldl_cons]
      exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
        (LineOkP_insertPure φ 0 acc x _ h (stateOkP_initSeed φ x (hx x List.mem_cons_self)))
        (CarriesP_insertPure φ a 0 acc x _ h
          (stateOkP_initSeed φ x (hx x List.mem_cons_self)) hc)
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) → selOfAssign φ a 0 ∈ l →
      ∀ acc, LineOkP φ 0 acc →
        LineOkP φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc)
          ∧ CarriesP φ a 0
            (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ hd; exact absurd hd List.not_mem_nil
    | cons x xs ih =>
      intro hx hd acc h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact mono xs (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
          (LineOkP_insertPure φ 0 acc _ _ h (stateOkP_initSeed φ _ hsel))
          (CarriesP_of_insertPure_at φ a 0 acc _ h (stateOkP_initSeed φ _ hsel)
            (AlongAssignP.seed ""))
      · exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) hd' _
          (LineOkP_insertPure φ 0 acc x _ h (stateOkP_initSeed φ x (hx x List.mem_cons_self)))
  exact main _ (fun _ hdm => hdm) hsel []
    ⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem runP_ok (hwf : WF φ) (hsat : Sat a φ) :
    ∀ (n : Nat) (k : Int), 0 ≤ k → k + (n : Int) < stepCount φ →
      ∀ line, LineOkP φ k line → CarriesP φ a k line →
        LineOkP φ (k + (n : Int)) (pureStepsP φ n line)
          ∧ CarriesP φ a (k + (n : Int)) (pureStepsP φ n line) := by
  intro n
  induction n with
  | zero => intro k _ _ line hl hc; simpa using ⟨hl, hc⟩
  | succ m ih =>
    intro k h0 hk line hl hc
    have heq : k + ((m + 1 : Nat) : Int) = (k + 1) + (m : Int) := by omega
    rw [heq]
    simp only [pureStepsP]
    exact ih (k + 1) (by omega) (by omega) _
      (LineOkP_pureAdvanceP φ k line hl)
      (CarriesP_pureAdvanceP φ a hwf hsat k h0 (by omega) line hl hc)

/-- **The improved driver ends holding the branch.** -/
theorem pureRunP_carries (hwf : WF φ) (hsat : Sat a φ) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRunP φ
      ∧ AlongAssignP φ a g ∧ g.current_step = stepCount φ := by
  have hzero := stepCount_pos φ
  obtain ⟨hl0, hc0⟩ := initP_ok φ a hsat
  have hcast : (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  have h := runP_ok φ a hwf hsat (stepCount φ - 1).toNat 0 (by omega)
    (by omega) (pureInit φ) hl0 hc0
  have h0e : (0 : Int) + (stepCount φ - 1) = stepCount φ - 1 := by omega
  rw [hcast, h0e] at h
  obtain ⟨g, hmem, hal, hcs⟩ := h.2
  exact ⟨g, by simp only [pureRunP]; exact hmem, hal, by omega⟩

/-- **The improved machine loses no solution.** The state parked at a
satisfying assignment's final node spans the whole map, is valid, and denotes
something. -/
theorem pureRunP_full_state (hwf : WF φ) (hsat : Sat a φ) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRunP φ
      ∧ g.current_step = stepCount φ
      ∧ isValid g = true
      ∧ AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨g, hmem, hal, hcs⟩ := pureRunP_carries φ a hwf hsat
  exact ⟨g, hmem, hcs, isValid_alongP φ a hwf hsat g hal, inhabited_alongP φ a hwf hsat g hal⟩

/-- **A satisfiable formula gets a non-empty last line.** -/
theorem pureRunP_ne_nil (hwf : WF φ) (h : Satisfiable φ) : pureRunP φ ≠ [] := by
  obtain ⟨b, hsat⟩ := h
  obtain ⟨g, hmem, _, _⟩ := pureRunP_carries φ b hwf hsat
  intro hnil
  rw [hnil] at hmem
  exact absurd hmem List.not_mem_nil

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.ConservationPins.not_idContradicts_sel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_idContradicts_sel

/-- info: 'AbsSat.GraphPath.Model.ConservationPins.ChainSound_pinPrune' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_pinPrune

/-- info: 'AbsSat.GraphPath.Model.ConservationPins.chainSound_alongP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chainSound_alongP

/-- info: 'AbsSat.GraphPath.Model.ConservationPins.pureRunP_full_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRunP_full_state

/-- info: 'AbsSat.GraphPath.Model.ConservationPins.pureRunP_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRunP_ne_nil

end AbsSat.GraphPath.Model.ConservationPins
