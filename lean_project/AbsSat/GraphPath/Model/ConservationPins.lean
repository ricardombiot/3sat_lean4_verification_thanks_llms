-- lean_project/AbsSat/GraphPath/Model/ConservationPins.lean
import AbsSat.GraphPath.Model.ConservationImproves
import AbsSat.GraphPath.Model.ConservationFilter
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
so the rest is `ConservationImproves` again: `chainSound_up_of_prunedR` (the up
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
open AbsSat.GraphPath.Model.ConservationFilter
open AbsSat.GraphPath.Model.ConservationCore (ShapeOk ShapeOk_of_pruned ShapeOk_initSeed
  ShapeOk_addNode ShapeOk_join pruned_filterWeakAll ChainSound_filterWeakAll stepCount_pos
  SelParent chainSound_up_of_prunedR)
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

-- ============================================================
-- The pin machine as an instance of the generic one
-- ============================================================

/-- The weak filter, then the pin prune: the filter parameter of `ConservationFilter`. -/
def Fpin : NodeId → GPathM → GPathM :=
  fun d g => pinPrune φ d (filterWeakAll g (weakReqOfCnf φ d))

theorem prunes_Fpin : PrunesF (Fpin φ) := fun d g =>
  Pruned.trans (pruned_filterWeakAll g _) (pruned_pinPrune φ d _)

/-- The branch survives both: the weak filter by `weakReqOfCnf_sound`, the prune because a chain
node of the assignment never contradicts a pin of a selected node — which is what the parent half of
the invariant is for. -/
theorem keepsBranch_Fpin (hwf : WF φ) (hsat : Sat a φ) : KeepsBranchF φ a (Fpin φ) := by
  intro d g sel hsel hids hd
  subst hd
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
  exact ChainSound_pinPrune φ _ _ sel hw hgood

-- the driver is the generic one, step by step
theorem sendTo_eqP (g : GPathM) (next : PureLine) (d : NodeId) :
    sendToF φ (Fpin φ) review g next d = sendToP φ g next d := rfl

theorem sendAll_eqP (kv : NodeId × GPathM) (next : PureLine) :
    sendAllF φ (Fpin φ) review kv next = sendAllP φ kv next := by
  unfold sendAllF sendAllP
  have h : sendToF φ (Fpin φ) review kv.2 = sendToP φ kv.2 := by
    funext n d
    exact sendTo_eqP φ kv.2 n d
  rw [h]

theorem advance_eqP (line : PureLine) : pureAdvanceF φ (Fpin φ) review line = pureAdvanceP φ line := by
  unfold pureAdvanceF pureAdvanceP
  have h : (fun next kv => sendAllF φ (Fpin φ) review kv next) = (fun next kv => sendAllP φ kv next) := by
    funext next kv
    exact sendAll_eqP φ kv next
  rw [h]

theorem steps_eqP : ∀ (n : Nat) (line : PureLine),
    pureStepsF φ (Fpin φ) review n line = pureStepsP φ n line
  | 0, _ => rfl
  | n + 1, line => by
    show pureStepsF φ (Fpin φ) review n (pureAdvanceF φ (Fpin φ) review line) = pureStepsP φ n (pureAdvanceP φ line)
    rw [advance_eqP φ line, steps_eqP n]

/-- **The pin run is the generic run with the pin filter.** -/
theorem run_eqP : pureRunF φ (Fpin φ) review = pureRunP φ := steps_eqP φ _ _

theorem alongF_of_alongP (g : GPathM) (h : AlongAssignP φ a g) : AlongAssignF φ a (Fpin φ) review g := by
  induction h with
  | seed title => exact AlongAssignF.seed title
  | up g title _ ih => exact AlongAssignF.up g title ih
  | joinL g₁ g₂ hok h₂ _ ih => exact AlongAssignF.joinL g₁ g₂ hok h₂ ih
  | joinR g₁ g₂ hok h₁ _ ih => exact AlongAssignF.joinR g₁ g₂ hok h₁ ih

theorem alongP_of_alongF (g : GPathM) (h : AlongAssignF φ a (Fpin φ) review g) : AlongAssignP φ a g := by
  induction h with
  | seed title => exact AlongAssignP.seed title
  | up g title _ ih => exact AlongAssignP.up g title ih
  | joinL g₁ g₂ hok h₂ _ ih => exact AlongAssignP.joinL g₁ g₂ hok h₂ ih
  | joinR g₁ g₂ hok h₁ _ ih => exact AlongAssignP.joinR g₁ g₂ hok h₁ ih

-- ============================================================
-- What this module says, now proved generically
-- ============================================================

/-- **The conservation law for the machine with the pin prune.** -/
theorem chainSound_alongP (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignP φ a g) :
    ∃ sel, ChainSound g sel ∧
      ∀ k, 0 ≤ k → k < g.current_step →
        (sel k).id = selOfAssign φ a k ∧ SelParent φ a (sel k) :=
  chainSound_alongF φ a (Fpin φ) review hwf (prunes_Fpin φ) (keepsBranch_Fpin φ a hwf hsat) g
    (alongF_of_alongP φ a g h)

theorem isValid_alongP (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignP φ a g) :
    isValid g = true :=
  isValid_alongF φ a (Fpin φ) review hwf (prunes_Fpin φ) (keepsBranch_Fpin φ a hwf hsat) g
    (alongF_of_alongP φ a g h)

theorem inhabited_alongP (hwf : WF φ) (hsat : Sat a φ) (g : GPathM) (h : AlongAssignP φ a g) :
    AbsSat.GraphPath.Model.Inhabited g :=
  inhabitedM_alongF φ a (Fpin φ) review hwf (prunes_Fpin φ) (keepsBranch_Fpin φ a hwf hsat) g
    (alongF_of_alongP φ a g h)

/-- **The driver with the prune ends holding the branch.** -/
theorem pureRunP_carries (hwf : WF φ) (hsat : Sat a φ) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRunP φ
      ∧ AlongAssignP φ a g ∧ g.current_step = stepCount φ := by
  obtain ⟨g, hmem, hal, hcs⟩ :=
    pureRunF_carries φ a (Fpin φ) review hwf hsat (prunes_Fpin φ) (keepsBranch_Fpin φ a hwf hsat)
  exact ⟨g, run_eqP φ ▸ hmem, alongP_of_alongF φ a g hal, hcs⟩

/-- **The machine with the prune loses no solution.** -/
theorem pureRunP_full_state (hwf : WF φ) (hsat : Sat a φ) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRunP φ
      ∧ g.current_step = stepCount φ
      ∧ isValid g = true
      ∧ AbsSat.GraphPath.Model.Inhabited g := by
  obtain ⟨g, hmem, hcs, hv, hi⟩ :=
    pureRunF_full_state φ a (Fpin φ) review hwf hsat (prunes_Fpin φ) (keepsBranch_Fpin φ a hwf hsat)
  exact ⟨g, run_eqP φ ▸ hmem, hcs, hv, hi⟩

/-- **A satisfiable formula gets a non-empty last line.** -/
theorem pureRunP_ne_nil (hwf : WF φ) (h : Satisfiable φ) : pureRunP φ ≠ [] := by
  have hne := pureRunF_ne_nil φ (Fpin φ) review hwf (prunes_Fpin φ)
    (fun b hb => keepsBranch_Fpin φ b hwf hb) h
  rw [run_eqP φ] at hne
  exact hne

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
