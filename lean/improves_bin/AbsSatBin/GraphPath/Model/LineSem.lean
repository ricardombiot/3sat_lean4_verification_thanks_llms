-- lean/improves_bin/AbsSatBin/GraphPath/Model/LineSem.lean
import AbsSatBin.GraphPath.Model.PrefixDecode

/-!
# Step 2: certificates along the machine's line

The machine keeps one state per map node of the current step (its *line*); a step sends every state to
the sons of its key, filtered by the son's requirement, and joins what lands on the same key. This
module follows `MapCert` along the whole line at once, entry by entry, without building a union state.

* `Owns n r q`: in some state of line `n`, the table of `r` holds `q`. `LClique`, `LWit` are cliques and
  witnesses for that relation, and `SemCert n` says every clique with witnesses in line `n` is passed
  by a partial solution (`PreSat`).
* **Sources** (`source_entry`, `source_node`): every node and table entry of a state of line `n+1` comes
  from `upFiltering` of a state of line `n`.
* **Transfer** (`upF_old`, `upF_new_owner`): an old entry of such an output was an entry before; a node
  that owns a new node `z` owns, before, a parent of `z`, a node of `z`'s grandparent map node, and the
  requirement of `z`.
* **Extension**: a partial solution through the old part extends through `z`.

Everything is proved except the third literal of a clause for cliques with no member at that step: that
is the clause's disjunction, left as the hypothesis `ClauseChoice`.
-/

namespace AbsSatBin.GraphPath.Model.LineSem

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.MapReachable
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.PrefixCarry
open AbsSatBin.GraphPath.Model.AmbTriCore (ACtx)

variable (φ : Cnf)

/-- The filter the machine applies before sending a state to `d`. -/
abbrev upF (g : GPathM) (d : NodeId) : GPathM := upFiltering g (reqOf φ d) d "" (isProhibited φ)

-- ============================================================
-- Context of a filtered machine state
-- ============================================================

/-- **A valid filtered machine state has the reader's context.** -/
theorem filt_ctx (hbd : Bounded φ) (k : Int) (kv : NodeId × GPathM) (hkv : StateOk φ k kv)
    (reqs : List NodeId) (hv : isValid (filterAll kv.2 reqs) = true) : ACtx (filterAll kv.2 reqs) := by
  have hreach := reachable_of_mapReachable φ hbd kv.2 hkv.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  have cm := Reader.RCtx_reachable (reqOf φ) (isProhibited φ) kv.2 hnd hreach
  have sm := (SymMachine.symInv_reachable (reqOf φ) (isProhibited φ) kv.2 hreach hkv.valid).1
  have abm := KernelReader.ownAbove_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  have cX : Reader.RCtx (reqs.foldl filterRequire kv.2) :=
    ReaderAgg.RCtx_of_keeps (ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire reqs kv.2) cm
  have abX : KernelReader.OwnAbove (reqs.foldl filterRequire kv.2) := by
    intro n hn; rw [SymMachine.foldl_filterRequire_nodes] at hn; exact abm n hn
  have hk := KernelReader.kernel_of_review _ cX (SymMachine.sym_foldl_filterRequire reqs kv.2 sm) abX hv
  have rF := Reader.RCtx_filterAll kv.2 cm reqs
  have sa := Sons.SAbove_filterAll kv.2 reqs (KernelSplit.SAbove_reachable (reqOf φ) (isProhibited φ) kv.2 hreach)
  exact ⟨⟨hk, rF.nodup, rF.oos, rF.shape.pbelow, sa, rF.snn, rF.below⟩, rF⟩

-- ============================================================
-- Sources: a step of the line
-- ============================================================

/-- What a state of the next line owes to the previous one. -/
def Src (line : PureLine) (kv' : NodeId × GPathM) : Prop :=
  (∀ r nr, kv'.2.node? r = some nr → ∃ kv ∈ line, kv'.1 ∈ sonsOfMap φ kv.1 ∧
      isValid (upF φ kv.2 kv'.1) = true ∧ ∃ n, (upF φ kv.2 kv'.1).node? r = some n) ∧
  (∀ r nr, kv'.2.node? r = some nr → ∀ q ∈ nr.owners, ∃ kv ∈ line, kv'.1 ∈ sonsOfMap φ kv.1 ∧
      isValid (upF φ kv.2 kv'.1) = true ∧ ∃ n, (upF φ kv.2 kv'.1).node? r = some n ∧ q ∈ n.owners)

theorem src_insertPure (line : PureLine) (acc : PureLine) (hacc : ∀ kv' ∈ acc, Src φ line kv')
    (kv : NodeId × GPathM) (hkv : kv ∈ line) (d : NodeId) (hd : d ∈ sonsOfMap φ kv.1)
    (hv : isValid (upF φ kv.2 d) = true) :
    ∀ kv' ∈ insertPure acc d (upF φ kv.2 d), Src φ line kv' := by
  -- the inserted state is its own source
  have hnew : Src φ line (d, upF φ kv.2 d) :=
    ⟨fun r nr hr => ⟨kv, hkv, hd, hv, nr, hr⟩, fun r nr hr q hq => ⟨kv, hkv, hd, hv, nr, hr, hq⟩⟩
  intro kv' hkv'
  unfold insertPure at hkv'
  cases hf : acc.find? (fun kv => kv.1 == d) with
  | none =>
    rw [hf] at hkv'
    rcases List.mem_append.mp hkv' with h | h
    · exact hacc kv' h
    · rw [List.mem_singleton.mp h]; exact hnew
  | some e =>
    rw [hf] at hkv'
    obtain ⟨kv0, hkv0, hEq⟩ := List.mem_map.mp hkv'
    have he : e ∈ acc := List.mem_of_find?_eq_some hf
    have hekey : e.1 = d := eq_of_beq (List.find?_some (p := fun kv : NodeId × GPathM => kv.1 == d) hf)
    by_cases hk0 : kv0.1 = d
    · have hEq' : kv' = (d, doJoin e.2 (upF φ kv.2 d)) := by
        rw [← hEq]; simp only [beq_iff_eq.mpr hk0, if_true]
      rw [hEq']
      have hes : Src φ line (d, e.2) := by have := hacc e he; rw [← hekey]; exact this
      unfold doJoin
      cases hok : okJoin e.2 (upF φ kv.2 d) with
      | false => exact hes
      | true =>
        refine ⟨fun r nr hr => ?_, fun r nr hr q hq => ?_⟩
        · rcases join_node?_source _ _ r nr hr with h | h
          · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h; exact hes.1 r m hm
          · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h; exact hnew.1 r m hm
        · rcases join_owners_source _ _ r nr hr q hq with ⟨m, hm, hqm⟩ | ⟨m, hm, hqm⟩
          · exact hes.2 r m hm q hqm
          · exact hnew.2 r m hm q hqm
    · have hEq' : kv' = kv0 := by
        rw [← hEq]
        have : (kv0.1 == d) = false := by
          cases h : (kv0.1 == d) with
          | false => rfl
          | true => exact absurd (eq_of_beq h) hk0
        simp only [this]; rfl
      rw [hEq']; exact hacc kv0 hkv0

theorem src_sendAll (line : PureLine) (kv : NodeId × GPathM) (hkv : kv ∈ line) :
    ∀ (ds : List NodeId), (∀ d ∈ ds, d ∈ sonsOfMap φ kv.1) → ∀ acc, (∀ kv' ∈ acc, Src φ line kv') →
      ∀ kv' ∈ ds.foldl (sendTo φ kv.2) acc, Src φ line kv' := by
  intro ds
  induction ds with
  | nil => intro _ acc h; exact h
  | cons d ds ih =>
    intro hds acc hacc
    simp only [List.foldl_cons]
    refine ih (fun d' h => hds d' (List.mem_cons_of_mem _ h)) _ ?_
    unfold sendTo
    split
    · rename_i hv
      exact src_insertPure φ line acc hacc kv hkv d (hds d List.mem_cons_self) hv
    · exact hacc

/-- **Every state of the next line comes from `upFiltering` of states of this one.** -/
theorem src_pureAdvance (line : PureLine) : ∀ kv' ∈ pureAdvance φ line, Src φ line kv' := by
  unfold pureAdvance
  have main : ∀ (l : PureLine), (∀ kv ∈ l, kv ∈ line) → ∀ acc, (∀ kv' ∈ acc, Src φ line kv') →
      ∀ kv' ∈ l.foldl (fun next kv => sendAll φ kv next) acc, Src φ line kv' := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons kv l ih =>
      intro hl acc hacc
      simp only [List.foldl_cons]
      refine ih (fun x h => hl x (List.mem_cons_of_mem _ h)) _ ?_
      unfold sendAll
      exact src_sendAll φ line kv (hl kv List.mem_cons_self) _ (fun d h => h) acc hacc
  exact main line (fun _ h => h) [] (fun _ h => absurd h List.not_mem_nil)

-- ============================================================
-- Transfer through `upFiltering`
-- ============================================================

section
variable (J : GPathM) (d : NodeId) (hd : d.step = J.current_step) (c : ACtx (filterAll J (reqOf φ d)))
  (hv : isValid (upF φ J d) = true)

include hv in
theorem upF_shape : isValid (filterAll J (reqOf φ d)) = true ∧
    (upF φ J d = addNode (filterAll J (reqOf φ d)) d "" (isProhibited φ) ∨
      upF φ J d = review (addNode (filterAll J (reqOf φ d)) d "" (isProhibited φ))) := by
  unfold upF upFiltering up at *
  by_cases hF : isValid (filterAll J (reqOf φ d)) = true
  · refine ⟨hF, ?_⟩
    rw [if_pos hF]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [if_neg hF] at hv; exact absurd hv hF

include hd c hv

/-- A node of the output, seen in `addNode` of the filtered state (the review only shrinks tables). -/
theorem upF_in_add (r : PathNodeId) (n : PNodeM) (hn : (upF φ J d).node? r = some n) :
    ∃ nG, (addNode (filterAll J (reqOf φ d)) d "" (isProhibited φ)).node? r = some nG ∧
      ∀ v ∈ n.owners, v ∈ nG.owners := by
  have hbF := (pruned_filterAll J (reqOf φ d)).step_eq
  have hdF : d.step = (filterAll J (reqOf φ d)).current_step := by have := hbF; omega
  have hndG := Reader.nodup_addNode _ d "" (isProhibited φ) c.pc.nd c.pc.below hdF
  rcases (upF_shape φ J d hv).2 with e | e
  · rw [e] at hn; exact ⟨n, hn, fun v h => h⟩
  · rw [e] at hn
    have hb := KernelIff.below_filterAll_self _ hndG []
    obtain ⟨nG, hnG, ho, _, _⟩ := hb.node r n hn
    exact ⟨nG, hnG, ho⟩

/-- **An old entry of the output was an entry of the filtered state.** -/
theorem upF_old (r : PathNodeId) (n : PNodeM) (hn : (upF φ J d).node? r = some n)
    (hr : r.id.step < J.current_step) :
    ∃ nF, (filterAll J (reqOf φ d)).node? r = some nF ∧
      ∀ v ∈ n.owners, v.id.step < J.current_step → v ∈ nF.owners := by
  have hbF := (pruned_filterAll J (reqOf φ d)).step_eq
  have hdF : d.step = (filterAll J (reqOf φ d)).current_step := by have := hbF; omega
  obtain ⟨nG, hnG, ho⟩ := upF_in_add φ J d hd c hv r n hn
  obtain ⟨nF, hnF, hEq⟩ := addNode_node?_below _ d "" (isProhibited φ) hdF r nG hnG (by have := hbF; omega)
  refine ⟨nF, hnF, fun v hvn hvs => ?_⟩
  have hvG := ho v hvn
  rw [hEq, upMap_owners] at hvG
  rcases List.mem_append.mp hvG with h | h
  · exact h
  · exfalso
    have := mapId_of_mem_newRowIds _ d _ v (List.mem_filter.mp h).1
    have : v.id.step = J.current_step := by rw [this]; exact hd
    omega

/-- **A new node of the output is a row node, and its table is inside its row table.** -/
theorem upF_new (z : PathNodeId) (nz : PNodeM) (hn : (upF φ J d).node? z = some nz)
    (hz : z.id.step = J.current_step) :
    z ∈ newRowIds (filterAll J (reqOf φ d)) d (isProhibited φ) ∧
      ∀ v ∈ nz.owners, v ∈ rowOwners (filterAll J (reqOf φ d)) d z := by
  have hbF := (pruned_filterAll J (reqOf φ d)).step_eq
  have hdF : d.step = (filterAll J (reqOf φ d)).current_step := by have := hbF; omega
  obtain ⟨nG, hnG, ho⟩ := upF_in_add φ J d hd c hv z nz hn
  rcases BranchRel.node_cases _ d "" (isProhibited φ) hdF c.pc.below c.pc.nd z nG hnG with
    ⟨_, _, _, hs⟩ | ⟨hzn, hEq, _⟩
  · have := hbF; omega
  · refine ⟨hzn, fun v hvn => ?_⟩
    have := ho v hvn
    rw [hEq, rowNode_owners] at this; exact this

/-- **An old node that owns a new node is in its row table, before.** -/
theorem upF_owner_new (r : PathNodeId) (n : PNodeM) (hn : (upF φ J d).node? r = some n)
    (hr : r.id.step < J.current_step) (z : PathNodeId) (hzn : z ∈ n.owners) (hz : z.id.step = J.current_step) :
    ∃ nF, (filterAll J (reqOf φ d)).node? r = some nF ∧
      z ∈ newRowIds (filterAll J (reqOf φ d)) d (isProhibited φ) ∧
      r ∈ rowOwners (filterAll J (reqOf φ d)) d z := by
  have hbF := (pruned_filterAll J (reqOf φ d)).step_eq
  have hdF : d.step = (filterAll J (reqOf φ d)).current_step := by have := hbF; omega
  obtain ⟨nG, hnG, ho⟩ := upF_in_add φ J d hd c hv r n hn
  obtain ⟨nF, hnF, hEq⟩ := addNode_node?_below _ d "" (isProhibited φ) hdF r nG hnG (by have := hbF; omega)
  have hzG := ho z hzn
  rw [hEq, upMap_owners] at hzG
  rcases List.mem_append.mp hzG with h | h
  · exfalso; have := c.rc.ownb nF (List.mem_of_find?_eq_some hnF) z h; have := hbF; omega
  · obtain ⟨hznew, hc⟩ := List.mem_filter.mp h
    refine ⟨nF, hnF, hznew, ?_⟩
    have := List.mem_of_elem_eq_true hc
    rw [node?_id_eq _ r nF hnF] at this; exact this
end

section
variable {F : GPathM} (c : ACtx F) (d : NodeId) (hdF : d.step = F.current_step)
include c hdF

/-- **In the filtered state, a node of a row table owns a parent of the row node and a node of its
grandparent map node.** -/
theorem row_owner_window (hs2 : 2 ≤ F.current_step) (z : PathNodeId) (hz : z ∈ newRowIds F d (isProhibited φ))
    (r : PathNodeId) (nF : PNodeM) (hnF : F.node? r = some nF) (hr : r.id.step < F.current_step)
    (hrz : r ∈ rowOwners F d z) :
    (∃ p ∈ nF.owners, some p.id = z.parent_id) ∧ (∃ e ∈ nF.owners, some e.id = z.gparent_id) := by
  have hk := c.pc.ker
  have hpos : 0 < F.current_step := by omega
  rcases (mem_rowOwners_iff F d z r).mp hrz with ⟨hu, _⟩ | he
  · obtain ⟨p, hp, np, hnp, hrp⟩ := KernelReader.mem_unionOwnersOf_inv F _ r hu
    have hps : p.id.step = F.current_step - 1 := (rowParent_node F d hpos hp).2
    have hzp : shiftPid p d = z := eq_of_beq (List.mem_filter.mp hp).2
    have hpr : p ∈ nF.owners := hk.sym p np r nF hnp hnF hrp
    refine ⟨⟨p, hpr, by rw [← hzp]; rfl⟩, ?_⟩
    obtain ⟨e, he, hep, hes⟩ := hk.pair r nF p np hnF hnp hpr (F.current_step - 2) (by omega) (by omega)
    obtain ⟨hepar, _⟩ := KernelSplit.parent_of_owner c.pc p np hnp (by omega) e hep (by rw [hes, hps]; omega)
    have hpm := c.rc.pmp np (List.mem_of_find?_eq_some hnp) e hepar
    rw [node?_id_eq F p np hnp] at hpm
    exact ⟨e, he, by rw [hpm, ← hzp]; rfl⟩
  · exfalso
    have := mapId_of_mem_newRowIds F d _ z hz
    rw [he, this] at hr; omega

omit hdF in
/-- **Every node of the filtered state owns a path node of the requirement.** -/
theorem filt_owns_req (J : GPathM) (hF : F = filterAll J (reqOf φ d)) (r : PathNodeId) (nF : PNodeM)
    (hnF : F.node? r = some nF) (req : NodeId) (hreq : req ∈ reqOf φ d) (h0 : 0 ≤ req.step)
    (h1 : req.step < F.current_step) : ∃ x ∈ nF.owners, x.id = req := by
  have hk := c.pc.ker
  have hl : reqOf φ d = [req] := by
    have hlen := reqOf_length_le_one φ d
    cases hr : reqOf φ d with
    | nil => rw [hr] at hreq; exact absurd hreq List.not_mem_nil
    | cons x xs =>
      rw [hr] at hreq hlen
      cases xs with
      | nil => rw [List.mem_singleton.mp hreq]
      | cons y ys => simp at hlen
  have hv := ((isValidNode_iff F nF).mp (hk.valid r nF hnF)).1
  obtain ⟨e, he, hes⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv req.step (mem_intRange h0 (by omega)))
  have heg := hk.own r nF hnF e he
  rw [hF, hl] at heg
  exact ⟨e, he, ReqFilter.req_id J req e heg (eq_of_beq hes)⟩
end

-- ============================================================
-- Semantics: extending a partial solution by one step
-- ============================================================

/-- Changing an assignment at `v` does not move the selection below `v`'s step. -/
theorem selOfAssign_congr (a a' : Assign) (v : Nat) (hv : v < φ.nVars)
    (hsame : ∀ w, w ≠ v → a' w = a w) (k : Int) (hk : k < varStep v) :
    selOfAssign φ a' k = selOfAssign φ a k := by
  have hkm : k < midFusion φ := by simp only [varStep, midFusion] at hk ⊢; omega
  unfold selOfAssign
  by_cases h0 : k ≤ 0
  · simp only [h0, if_true]
  · have hw : varOfStep k ≠ v := by
      intro e
      unfold varOfStep at e
      simp only [varStep] at hk
      have hnn : 0 ≤ (k - 1) / 2 := by omega
      have := Int.toNat_of_nonneg hnn
      rw [e] at this
      omega
    simp only [h0, if_false, hkm, if_true, hsame _ hw]

theorem pidOfAssign_congr (a a' : Assign) (v : Nat) (hv : v < φ.nVars)
    (hsame : ∀ w, w ≠ v → a' w = a w) (k : Int) (hk : k < varStep v) :
    pidOfAssign φ a' k = pidOfAssign φ a k := by
  unfold pidOfAssign
  rw [selOfAssign_congr φ a a' v hv hsame k hk, selOfAssign_congr φ a a' v hv hsame (k - 1) (by omega),
    selOfAssign_congr φ a a' v hv hsame (k - 2) (by omega)]

/-- The selection at a literal's step reads the literal's value. -/
theorem selOfAssign_binStep (a : Assign) (l : Lit) (hl : l.v < φ.nVars) :
    selOfAssign φ a l.binStep = ⟨l.binStep, bit (litVal a l)⟩ := by
  cases hp : l.pos with
  | true =>
    rw [varStep_eq l hp, selOfAssign_var φ a l.v hl]; simp [litVal, hp]
  | false =>
    rw [negStep_eq l hp, selOfAssign_neg φ a l.v hl]; simp [litVal, hp]

/-- **At a step other than a positive variable, the requirement fixes the selection**: if the
assignment honours `d`'s requirement, it selects `d`. -/
theorem selOfAssign_of_req (hbd : Bounded φ) (a : Assign) (d : NodeId) (k : Int) (hk0 : 0 < k)
    (hon : d ∈ mapNodes φ k) (hnv : ∀ v, v < φ.nVars → k ≠ varStep v)
    (hreq : ∀ req ∈ reqOf φ d, selOfAssign φ a req.step = req) : selOfAssign φ a k = d := by
  have hds : d.step = k := mapNodes_step φ k d hon
  rcases step_cases φ k with h | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | h | ⟨j, p, c, hp, hjlt, hj, rfl⟩ | h
  · omega
  · exact absurd rfl (hnv v hv)
  · rw [mapNodes_two φ _ (by simp only [negStep]; omega) (by simp only [negStep, midFusion]; omega)
      (by simp only [negStep, fusionTop]; omega)] at hon
    have hr := hreq _ (by rw [reqOf_neg φ d v hv hds]; exact List.mem_cons_self)
    rw [selOfAssign_var φ a v hv] at hr
    rw [selOfAssign_neg φ a v hv]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hon
    rcases hon with rfl | rfl <;> cases hav : a v <;> simp_all [bit]
  · rw [mapNodes_fusion φ k (Or.inr (Or.inl h))] at hon
    rw [List.mem_singleton.mp hon]
    subst h
    have e1 : ¬ midFusion φ ≤ 0 := by simp only [midFusion]; omega
    simp [selOfAssign, e1]
  · rw [mapNodes_two φ _ (by simp only [clauseStep]; omega) (by simp only [clauseStep, midFusion]; omega)
      (by simp only [clauseStep, fusionTop]; omega)] at hon
    obtain ⟨h1, h2, h3⟩ := hbd c (List.mem_of_getElem? hj)
    have hv : (litAt c p).v < φ.nVars := by unfold litAt; split <;> assumption
    have hr := hreq _ (by rw [reqOf_clause φ d j p c hp hjlt hj hds]; exact List.mem_cons_self)
    rw [selOfAssign_binStep φ a _ hv] at hr
    rw [selOfAssign_clause φ a j p c hp hjlt hj]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hon
    rcases hon with rfl | rfl <;> simp_all
  · have hks : k < stepCount φ := by
      by_cases hc : stepCount φ ≤ k
      · unfold mapNodes at hon
        rw [if_neg (by omega), if_pos hc] at hon
        exact absurd hon List.not_mem_nil
      · omega
    rw [mapNodes_fusion φ k (Or.inr (Or.inr ⟨h, hks⟩))] at hon
    rw [List.mem_singleton.mp hon]
    have h1 : ¬ k ≤ 0 := by simp only [fusionTop] at h; omega
    have h2 : ¬ k < midFusion φ := by simp only [fusionTop, midFusion] at h ⊢; omega
    have h3 : ¬ k = midFusion φ := by simp only [fusionTop, midFusion] at h ⊢; omega
    simp only [selOfAssign, h1, h2, h3, h, if_false, if_true]

/-- **A chain whose map nodes are an assignment's selection is the assignment's windows.** -/
theorem chain_eq_pid (g : GPathM) (sel : Int → PathNodeId) (a : Assign) (hchain : IsChain g sel)
    (hpmp : ParentId.PMP g) (hgpmp : ParentId.GPMP g) (hroot : (sel 0).parent_id = none)
    (hid : ∀ k, 0 ≤ k → k < g.current_step → (sel k).id = selOfAssign φ a k)
    (k : Int) (h0 : 0 ≤ k) (hkc : k < g.current_step) : sel k = pidOfAssign φ a k := by
  have hg0 : (sel 0).gparent_id = none := by
    obtain ⟨hs, _⟩ := hchain.1 0 (Int.le_refl 0) (by omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
    have hnid : n.id = sel 0 := node?_id_eq g _ n hn
    have := hgpmp.2 n (List.mem_of_find?_eq_some hn) (by rw [hnid]; exact hroot)
    rw [hnid] at this; exact this
  unfold pidOfAssign
  apply ParentId.pathNodeId_ext
  · exact hid k h0 hkc
  · by_cases hk : 0 < k
    · rw [if_pos hk, ← hid (k - 1) (by omega) (by omega)]
      have := ParentId.parentId_coherent g hpmp sel hchain (k - 1) (by omega) (by omega)
      rw [show k - 1 + 1 = k from by omega] at this
      exact this
    · have hk0 : k = 0 := by omega
      rw [if_neg hk, hk0]; exact hroot
  · by_cases hk : 1 < k
    · rw [if_pos hk, ← hid (k - 2) (by omega) (by omega)]
      have h1 := ParentId.gparentId_coherent g hgpmp sel hchain (k - 1) (by omega) (by omega)
      have h2 := ParentId.parentId_coherent g hpmp sel hchain (k - 2) (by omega) (by omega)
      rw [show k - 1 + 1 = k from by omega] at h1
      rw [show k - 2 + 1 = k - 1 from by omega] at h2
      rw [h1, h2]
    · rw [if_neg hk]
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · exact hg0
      · have h1 := ParentId.gparentId_coherent g hgpmp sel hchain 0 (Int.le_refl 0) (by omega)
        rw [show (0 : Int) + 1 = 1 from rfl] at h1
        rw [h1, hroot]

-- ============================================================
-- The line, and ownership along it
-- ============================================================

/-- The machine's line after `n` steps. -/
def line (n : Nat) : PureLine := pureSteps φ n (pureInit φ)

theorem pureSteps_succ' : ∀ (n : Nat) (l : PureLine), pureSteps φ (n + 1) l = pureAdvance φ (pureSteps φ n l) := by
  intro n
  induction n with
  | zero => intro l; rfl
  | succ m ih => intro l; show pureSteps φ (m + 1) (pureAdvance φ l) = _; rw [ih]; rfl

theorem line_succ (n : Nat) : line φ (n + 1) = pureAdvance φ (line φ n) := pureSteps_succ' φ n _

theorem lineOk (n : Nat) : LineOk φ n (line φ n) := by
  have h := Decision.LineOk_pureSteps φ n 0 (pureInit φ) (Decision.LineOk_pureInit φ)
  simp only [Int.zero_add] at h; exact h

/-- In some state of line `n`, `r` is a node. -/
def Node (n : Nat) (r : PathNodeId) : Prop := ∃ kv ∈ line φ n, ∃ nr, kv.2.node? r = some nr
/-- In some state of line `n`, the table of `r` holds `q`. -/
def Owns (n : Nat) (r q : PathNodeId) : Prop := ∃ kv ∈ line φ n, ∃ nr, kv.2.node? r = some nr ∧ q ∈ nr.owners
/-- In some state of line `n`, the table of `r` holds a path node of the map node `m`. -/
def OwnsMap (n : Nat) (r : PathNodeId) (m : NodeId) : Prop :=
  ∃ kv ∈ line φ n, ∃ nr, kv.2.node? r = some nr ∧ ∃ p ∈ nr.owners, p.id = m

def LClique (n : Nat) (Q : List PathNodeId) : Prop := ∀ q ∈ Q, ∀ s ∈ Q, Owns φ n q s
def LWit (n : Nat) (Q : List PathNodeId) (R : List NodeId) : Prop :=
  ∀ l, 0 ≤ l → l ≤ (n : Int) → ∃ r, r.id.step = l ∧ Node φ n r ∧ (∀ q ∈ Q, Owns φ n r q) ∧ ∀ m ∈ R, OwnsMap φ n r m

/-- A partial solution passes the clique and the map nodes. -/
def SemConcl (n : Nat) (Q : List PathNodeId) (R : List NodeId) : Prop :=
  ∃ a, PreSat φ a ((n : Int) + 1) ∧ (∀ q ∈ Q, pidOfAssign φ a q.id.step = q) ∧
    ∀ m ∈ R, 0 ≤ m.step → m.step ≤ (n : Int) → selOfAssign φ a m.step = m

/-- **Every clique with witnesses in line `n` is passed by a partial solution.** -/
def SemCert (n : Nat) : Prop := ∀ Q R, LClique φ n Q → LWit φ n Q R → SemConcl φ n Q R

/-- **The clause**: at the third literal of a clause, a clique of the next line with no member at that
step is passed by a partial solution. -/
def ClauseChoice (n : Nat) : Prop :=
  isL3 φ ((n : Int) + 1) = true → ∀ Q R, LClique φ (n + 1) Q → LWit φ (n + 1) Q R →
    (∀ q ∈ Q, q.id.step ≤ (n : Int)) → SemConcl φ (n + 1) Q R

-- ============================================================
-- A state of the next line, seen from its source
-- ============================================================

section
variable (hbd : Bounded φ) (n : Nat)
include hbd

/-- The context of a source of a state of line `n+1`. -/
theorem src_ctx (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId) (hd : d ∈ sonsOfMap φ kv.1)
    (hv : isValid (upF φ kv.2 d) = true) :
    StateOk φ n kv ∧ d.step = kv.2.current_step ∧ kv.2.current_step = (n : Int) + 1 ∧
      d ∈ mapNodes φ ((n : Int) + 1) ∧ isValid (filterAll kv.2 (reqOf φ d)) = true ∧
      NodupIds kv.2 := by
  have hok : StateOk φ n kv := (lineOk φ n).2 kv hkv
  have hkey : kv.1.step = n := mapNodes_step φ n kv.1 hok.onMap
  have hd' : d ∈ mapNodes φ ((n : Int) + 1) := by
    have := sonsOfMap_subset φ kv.1 (by rw [hkey]; exact hok.onMap) d hd
    rwa [hkey] at this
  have hdstep : d.step = (n : Int) + 1 := mapNodes_step φ _ d hd'
  have hreach := reachable_of_mapReachable φ hbd kv.2 hok.reach
  exact ⟨hok, by rw [hdstep, hok.step], hok.step, hd', (upF_shape φ kv.2 d hv).1,
    Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) kv.2 hreach⟩

/-- **An old entry of the next line was an entry of this one.** -/
theorem owns_old (r q : PathNodeId) (h : Owns φ (n + 1) r q) (hr : r.id.step ≤ (n : Int))
    (hq : q.id.step ≤ (n : Int)) : Owns φ n r q := by
  obtain ⟨kv', hkv', nr, hnr, hqr⟩ := h
  rw [line_succ] at hkv'
  obtain ⟨kv, hkv, hd, hv, n', hn', hqn'⟩ := (src_pureAdvance φ (line φ n) kv' hkv').2 r nr hnr q hqr
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  obtain ⟨nF, hnF, ho⟩ := upF_old φ kv.2 kv'.1 hdst c hv r n' hn' (by omega)
  obtain ⟨nJ, hnJ, hoJ, _, _⟩ := (KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)).node r nF hnF
  exact ⟨kv, hkv, nJ, hnJ, hoJ q (ho q hqn' (by omega))⟩

theorem node_old (r : PathNodeId) (h : Node φ (n + 1) r) (hr : r.id.step ≤ (n : Int)) : Node φ n r := by
  obtain ⟨kv', hkv', nr, hnr⟩ := h
  rw [line_succ] at hkv'
  obtain ⟨kv, hkv, hd, hv, n', hn'⟩ := (src_pureAdvance φ (line φ n) kv' hkv').1 r nr hnr
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  obtain ⟨nF, hnF, _⟩ := upF_old φ kv.2 kv'.1 hdst c hv r n' hn' (by omega)
  obtain ⟨nJ, hnJ, _, _, _⟩ := (KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)).node r nF hnF
  exact ⟨kv, hkv, nJ, hnJ⟩

theorem ownsMap_old (r : PathNodeId) (m : NodeId) (h : OwnsMap φ (n + 1) r m) (hr : r.id.step ≤ (n : Int))
    (hm : m.step ≤ (n : Int)) : OwnsMap φ n r m := by
  obtain ⟨kv', hkv', nr, hnr, p, hp, hpm⟩ := h
  obtain ⟨kv, hkv, nJ, hnJ, hpJ⟩ := owns_old φ hbd n r p ⟨kv', hkv', nr, hnr, hp⟩ hr (by rw [hpm]; exact hm)
  exact ⟨kv, hkv, nJ, hnJ, p, hpJ, hpm⟩

/-- **A top entry of the next line is a row node of its source, and a node that owns it owned, before,
a parent of it, a node of its grandparent map node, and its requirement.** -/
theorem owns_top (r z : PathNodeId) (h : Owns φ (n + 1) r z) (hr : r.id.step ≤ (n : Int))
    (hz : z.id.step = (n : Int) + 1) :
    (∀ a, z.parent_id = some a → OwnsMap φ n r a) ∧ (1 ≤ n → ∀ b, z.gparent_id = some b → OwnsMap φ n r b) ∧
      (∀ req ∈ reqOf φ z.id, 0 ≤ req.step → req.step ≤ (n : Int) → OwnsMap φ n r req) := by
  obtain ⟨kv', hkv', nr, hnr, hzr⟩ := h
  rw [line_succ] at hkv'
  obtain ⟨kv, hkv, hd, hv, n', hn', hzn'⟩ := (src_pureAdvance φ (line φ n) kv' hkv').2 r nr hnr z hzr
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  obtain ⟨nF, hnF, hznew, hrz⟩ := upF_owner_new φ kv.2 kv'.1 hdst c hv r n' hn' (by omega) z hzn' (by omega)
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)
  obtain ⟨nJ, hnJ, hoJ, _, _⟩ := hb.node r nF hnF
  have hFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  have hdF : kv'.1.step = (filterAll kv.2 (reqOf φ kv'.1)).current_step := by rw [hFcs, ← hcs, hdst]
  have hzid : z.id = kv'.1 := mapId_of_mem_newRowIds _ _ _ z hznew
  refine ⟨fun a ha => ?_, fun h1 b hb' => ?_, fun req hreq h0 h1 => ?_⟩
  · -- the parent part of the window does not need two steps
    rcases (mem_rowOwners_iff _ _ z r).mp hrz with ⟨hu, _⟩ | he
    · obtain ⟨p, hp, np, hnp, hrp⟩ := KernelReader.mem_unionOwnersOf_inv _ _ r hu
      have hzp : shiftPid p kv'.1 = z := eq_of_beq (List.mem_filter.mp hp).2
      have hpr : p ∈ nF.owners := c.pc.ker.sym p np r nF hnp hnF hrp
      refine ⟨kv, hkv, nJ, hnJ, p, hoJ p hpr, ?_⟩
      rw [← hzp] at ha
      exact Option.some.inj ha
    · exfalso; rw [he] at hr; omega
  · obtain ⟨_, ⟨e, he, hee⟩⟩ := row_owner_window φ c kv'.1 hdF (by omega) z hznew r nF hnF (by omega) hrz
    exact ⟨kv, hkv, nJ, hnJ, e, hoJ e he, Option.some.inj (hee.trans hb')⟩
  · rw [hzid] at hreq
    obtain ⟨x, hx, hxid⟩ := filt_owns_req φ c kv'.1 kv.2 rfl r nF hnF req hreq h0 (by omega)
    exact ⟨kv, hkv, nJ, hnJ, x, hoJ x hx, hxid⟩

/-- **A top node of the next line owns, at its own step, only itself; it is a row node of its source,
not prohibited, on the map, with the window of one of its parents.** -/
theorem top_node (w : PathNodeId) (hw : Node φ (n + 1) w) (hws : w.id.step = (n : Int) + 1) :
    isProhibited φ w = false ∧ w.id ∈ mapNodes φ ((n : Int) + 1) ∧
      (∃ p : PathNodeId, p.id.step = (n : Int) ∧ w.parent_id = some p.id ∧ w.gparent_id = p.parent_id ∧
        (1 ≤ n → ∃ b, p.parent_id = some b ∧ b.step = (n : Int) - 1) ∧ (n = 0 → p.parent_id = none)) := by
  obtain ⟨kv', hkv', nw, hnw⟩ := hw
  rw [line_succ] at hkv'
  obtain ⟨kv, hkv, hd, hv, n', hn'⟩ := (src_pureAdvance φ (line φ n) kv' hkv').1 w nw hnw
  obtain ⟨hok, hdst, hcs, hdm, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  obtain ⟨hwnew, _⟩ := upF_new φ kv.2 kv'.1 hdst c hv w n' hn' (by omega)
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)
  have hFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  refine ⟨not_forb_of_mem_newRowIds _ _ _ w hwnew, by rw [mapId_of_mem_newRowIds _ _ _ w hwnew]; exact hdm, ?_⟩
  obtain ⟨p, hp⟩ := exists_rowParent _ kv'.1 _ (by omega) hwnew
  obtain ⟨hps1, hps⟩ := rowParent_node _ kv'.1 (by omega) hp
  obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp hps1
  have hzp : shiftPid p kv'.1 = w := eq_of_beq (List.mem_filter.mp hp).2
  have hnpm := List.mem_of_find?_eq_some hnp
  have hnpid : np.id = p := node?_id_eq _ p np hnp
  refine ⟨p, by rw [hps, hFcs]; omega, by rw [← hzp]; rfl, by rw [← hzp]; rfl, fun h1 => ?_, fun h0 => ?_⟩
  · -- a node above step 0 has a parent
    have hnr : np.id.parent_id ≠ none := c.rc.shape.notroot np hnpm (by rw [hnpid, hps, hFcs]; omega)
    obtain ⟨pp, hpp⟩ : ∃ pp, pp ∈ np.parents := by
      rcases ((isValidNode_iff _ np).mp (c.pc.ker.valid p np hnp)).2.1 with h' | h'
      · exact absurd (Option.isNone_iff_eq_none.mp h') hnr
      · exact List.exists_mem_of_ne_nil _ h'
    have hppid := c.rc.pmp np hnpm pp hpp
    have hpps := c.pc.pb np hnpm pp hpp
    rw [hnpid] at hppid hpps
    exact ⟨pp.id, hppid.symm, by rw [hpps, hps, hFcs]; omega⟩
  · have := c.rc.rootz np hnpm (by rw [hnpid, hps, hFcs, h0]; rfl)
    rw [hnpid] at this; exact this

/-- **At its own step, a top node owns only itself.** -/
theorem top_owns_self (w q : PathNodeId) (h : Owns φ (n + 1) w q) (hws : w.id.step = (n : Int) + 1)
    (hq : q.id.step = (n : Int) + 1) : q = w := by
  obtain ⟨kv', hkv', nw, hnw, hqw⟩ := h
  rw [line_succ] at hkv'
  obtain ⟨kv, hkv, hd, hv, n', hn', hqn'⟩ := (src_pureAdvance φ (line φ n) kv' hkv').2 w nw hnw q hqw
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  obtain ⟨_, hrow⟩ := upF_new φ kv.2 kv'.1 hdst c hv w n' hn' (by omega)
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)
  have hFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  rcases (mem_rowOwners_iff _ _ w q).mp (hrow q hqn') with ⟨hu, _⟩ | he
  · exfalso
    obtain ⟨_, _, np', hnp', hqp'⟩ := KernelReader.mem_unionOwnersOf_inv _ _ q hu
    have := c.rc.ownb np' (List.mem_of_find?_eq_some hnp') q hqp'; omega
  · exact he

/-- **A node that owns a path node of a top map node `m` owned, before, a path node of `m`'s
requirement.** -/
theorem ownsMap_top (r : PathNodeId) (m : NodeId) (h : OwnsMap φ (n + 1) r m) (hr : r.id.step ≤ (n : Int))
    (hm : m.step = (n : Int) + 1) :
    ∀ req ∈ reqOf φ m, 0 ≤ req.step → req.step ≤ (n : Int) → OwnsMap φ n r req := by
  obtain ⟨kv', hkv', nr, hnr, p, hp, hpm⟩ := h
  have := (owns_top φ hbd n r p ⟨kv', hkv', nr, hnr, hp⟩ hr (by rw [hpm]; exact hm)).2.2
  rw [hpm] at this; exact this
end

-- ============================================================
-- The induction
-- ============================================================

theorem reqOf_nonneg (hbd : Bounded φ) (d : NodeId) : ∀ req ∈ reqOf φ d, 0 ≤ req.step := by
  intro req hreq
  unfold reqOf at hreq
  split at hreq
  · exact absurd hreq List.not_mem_nil
  · split at hreq
    · split at hreq
      · exact absurd hreq List.not_mem_nil
      · rw [List.mem_singleton.mp hreq]; simp only; omega
    · split at hreq
      · exact absurd hreq List.not_mem_nil
      · split at hreq
        · exact absurd hreq List.not_mem_nil
        · split at hreq
          · exact absurd hreq List.not_mem_nil
          · next c p hc =>
            rw [List.mem_singleton.mp hreq]
            obtain ⟨h1, h2, h3⟩ := hbd c (mem_of_clauseOf φ _ c p hc)
            have hv : (litAt c p).v < φ.nVars := by unfold litAt; split <;> assumption
            have := (lit_step_bounds φ _ hv).1
            simp only; omega

/-- **Extending a partial solution to a top map node.** At a positive variable the value is free; elsewhere
the requirement fixes it. -/
theorem extend_to (hbd : Bounded φ) (n : Nat) (a : Assign) (d : NodeId)
    (hd : d ∈ mapNodes φ ((n : Int) + 1)) (hreq : ∀ req ∈ reqOf φ d, selOfAssign φ a req.step = req) :
    ∃ a', (∀ k, k ≤ (n : Int) → pidOfAssign φ a' k = pidOfAssign φ a k ∧ selOfAssign φ a' k = selOfAssign φ a k) ∧
      selOfAssign φ a' ((n : Int) + 1) = d := by
  rcases step_cases φ ((n : Int) + 1) with h | ⟨v, hv, hvs⟩ | h | h | h | h
  · exfalso; omega
  · refine ⟨fun w => if w = v then (d.index == 1) else a w, fun k hk => ?_, ?_⟩
    · have hsame : ∀ w, w ≠ v → (fun w => if w = v then (d.index == 1) else a w) w = a w := by
        intro w hw; show (if w = v then (d.index == 1) else a w) = a w; rw [if_neg hw]
      exact ⟨pidOfAssign_congr φ a _ v hv hsame k (by omega), selOfAssign_congr φ a _ v hv hsame k (by omega)⟩
    · rw [hvs, selOfAssign_var φ _ v hv]
      have hav : (if v = v then (d.index == 1) else a v) = (d.index == 1) := if_pos rfl
      rw [hav]
      rw [hvs, mapNodes_two φ _ (by simp only [varStep]; omega) (by simp only [varStep, midFusion]; omega)
        (by simp only [varStep, fusionTop]; omega)] at hd
      rcases List.mem_cons.mp hd with e | hd
      · rw [e]; rfl
      · rw [List.mem_singleton.mp hd]; rfl
  all_goals
    refine ⟨a, fun k _ => ⟨rfl, rfl⟩, selOfAssign_of_req φ hbd a d _
      (Int.lt_of_le_of_lt (Int.natCast_nonneg n) (Int.lt_succ _)) hd (fun v hv e => ?_) hreq⟩
  · obtain ⟨v', hv', e'⟩ := h; rw [e'] at e; simp only [negStep, varStep] at e; omega
  · rw [h] at e; simp only [midFusion, varStep] at e; omega
  · obtain ⟨j, p, c, hp, hjlt, _, e'⟩ := h; rw [e'] at e; simp only [clauseStep, varStep] at e; omega
  · simp only [fusionTop, varStep] at h e; omega

theorem line_zero (kv : NodeId × GPathM) (hkv : kv ∈ line φ 0) :
    kv = (⟨0, 0⟩, GPathM.initSeed ⟨0, 0⟩ "") := by
  have hm : mapNodes φ 0 = [⟨0, 0⟩] := mapNodes_fusion φ 0 (Or.inl rfl)
  have : line φ 0 = [(⟨0, 0⟩, GPathM.initSeed ⟨0, 0⟩ "")] := by
    show pureInit φ = _
    unfold pureInit; rw [hm]; rfl
  rw [this] at hkv; exact List.mem_singleton.mp hkv

theorem seed_node (r : PathNodeId) (nr : PNodeM) (h : (GPathM.initSeed (⟨0, 0⟩ : NodeId) "").node? r = some nr) :
    r = { id := ⟨0, 0⟩, parent_id := none } ∧ nr.owners = [{ id := ⟨0, 0⟩, parent_id := none }] := by
  have hm := List.mem_of_find?_eq_some h
  have hid := node?_id_eq _ r nr h
  rw [initSeed_nodes] at hm
  rw [List.mem_singleton.mp hm] at hid ⊢
  exact ⟨hid.symm, rfl⟩

/-- **Base.** -/
theorem semCert_zero : SemCert φ 0 := by
  intro Q R hQ hW
  let root : PathNodeId := { id := ⟨0, 0⟩, parent_id := none }
  have ownsRoot : ∀ r q, Owns φ 0 r q → r = root ∧ q = root := by
    intro r q ⟨kv, hkv, nr, hnr, hq⟩
    rw [line_zero φ kv hkv] at hnr
    obtain ⟨hr, ho⟩ := seed_node r nr hnr
    rw [ho] at hq
    exact ⟨hr, List.mem_singleton.mp hq⟩
  refine ⟨fun _ => false, fun k hk => ?_, fun q hq => ?_, fun m hm h0 h1 => ?_⟩
  · have hs : (pidOfAssign φ (fun _ => false) k).id.step = k := selOfAssign_step φ _ k
    unfold isProhibited isL3; rw [hs]
    have : ¬ midFusion φ < k := by simp only [midFusion]; omega
    simp [this]
  · obtain ⟨hq', _⟩ := ownsRoot q q (hQ q hq q hq)
    rw [hq']
    simp [pidOfAssign, selOfAssign, root]
  · obtain ⟨r, _, _, _, hrR⟩ := hW 0 (Int.le_refl 0) (by omega)
    obtain ⟨kv, hkv, nr, hnr, p, hp, hpm⟩ := hrR m hm
    rw [line_zero φ kv hkv] at hnr
    obtain ⟨_, ho⟩ := seed_node r nr hnr
    rw [ho] at hp
    rw [← hpm, List.mem_singleton.mp hp]
    simp [selOfAssign]

/-- A node of a state of line `n+1` sits at a step `≤ n+1`. -/
theorem owns_step (hbd : Bounded φ) (n : Nat) (r q : PathNodeId) (h : Owns φ n r q) :
    r.id.step ≤ (n : Int) := by
  obtain ⟨kv, hkv, nr, hnr, _⟩ := h
  have hok : StateOk φ n kv := (lineOk φ n).2 kv hkv
  have hreach := reachable_of_mapReachable φ hbd kv.2 hok.reach
  have := steps_below_current (reqOf φ) (isProhibited φ) hreach nr (List.mem_of_find?_eq_some hnr)
  rw [node?_id_eq _ r nr hnr, hok.step] at this; omega

/-- **The step.** -/
theorem semCert_succ (hbd : Bounded φ) (n : Nat) (ih : SemCert φ n)
    (hcl : ClauseChoice φ n) : SemCert φ (n + 1) := by
  intro Q R hQ hW
  let Qo := Q.filter (fun q => decide (q.id.step ≤ (n : Int)))
  let Ro := R.filter (fun m => decide (m.step ≤ (n : Int)))
  have memQo : ∀ q, q ∈ Qo ↔ q ∈ Q ∧ q.id.step ≤ (n : Int) := by
    intro q; rw [List.mem_filter]; exact ⟨fun ⟨a, b⟩ => ⟨a, of_decide_eq_true b⟩, fun ⟨a, b⟩ => ⟨a, decide_eq_true b⟩⟩
  have memRo : ∀ m, m ∈ Ro ↔ m ∈ R ∧ m.step ≤ (n : Int) := by
    intro m; rw [List.mem_filter]; exact ⟨fun ⟨a, b⟩ => ⟨a, of_decide_eq_true b⟩, fun ⟨a, b⟩ => ⟨a, decide_eq_true b⟩⟩
  have qstep : ∀ q ∈ Q, q.id.step ≤ (n : Int) + 1 := fun q hq => by
    have := owns_step φ hbd (n + 1) q q (hQ q hq q hq); push_cast at this; omega
  have hQo : LClique φ n Qo := by
    intro q hq s hs
    obtain ⟨hqQ, hqs⟩ := (memQo q).mp hq
    obtain ⟨hsQ, hss⟩ := (memQo s).mp hs
    exact owns_old φ hbd n q s (hQ q hqQ s hsQ) hqs hss
  -- a witness below the top, with extra map constraints
  have witOld : ∀ (E : List NodeId), (∀ r, r.id.step ≤ (n : Int) → Node φ (n + 1) r → (∀ q ∈ Q, Owns φ (n + 1) r q) →
      (∀ m ∈ R, OwnsMap φ (n + 1) r m) → ∀ m ∈ E, OwnsMap φ n r m) → LWit φ n Qo (Ro ++ E) := by
    intro E hE l h0 hl
    obtain ⟨r, hrs, hrn, hrQ, hrR⟩ := hW l h0 (by push_cast; omega)
    refine ⟨r, hrs, node_old φ hbd n r hrn (by omega), fun q hq => ?_, fun m hm => ?_⟩
    · obtain ⟨hqQ, hqs⟩ := (memQo q).mp hq
      exact owns_old φ hbd n r q (hrQ q hqQ) (by omega) hqs
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨hmR, hms⟩ := (memRo m).mp hm
        exact ownsMap_old φ hbd n r m (hrR m hmR) (by omega) hms
      · exact hE r (by omega) hrn hrQ hrR m hm
  -- the top witness pins every top constraint and every top member
  obtain ⟨w, hws, hwn, hwQ, hwR⟩ := hW ((n : Int) + 1) (by omega) (by push_cast; omega)
  have topR : ∀ m ∈ R, m.step = (n : Int) + 1 → m = w.id := by
    intro m hm hms
    obtain ⟨kv, hkv, nr, hnr, p, hp, hpm⟩ := hwR m hm
    have := top_owns_self φ hbd n w p ⟨kv, hkv, nr, hnr, hp⟩ hws (by rw [hpm]; exact hms)
    rw [← hpm, this]
  have topQ : ∀ q ∈ Q, q.id.step = (n : Int) + 1 → q = w :=
    fun q hq hqs => top_owns_self φ hbd n w q (hwQ q hq) hws hqs
  obtain ⟨hwf, hwm, pw, hpws, hwpar, hwgp, hwb1, hwb0⟩ := top_node φ hbd n w hwn hws
  -- a partial solution with the old part, extended to the top, gives the conclusion
  have finish : ∀ a, PreSat φ a ((n : Int) + 1) → (∀ q ∈ Qo, pidOfAssign φ a q.id.step = q) →
      (∀ m ∈ Ro, 0 ≤ m.step → m.step ≤ (n : Int) → selOfAssign φ a m.step = m) →
      ∀ a', (∀ k, k ≤ (n : Int) → pidOfAssign φ a' k = pidOfAssign φ a k ∧ selOfAssign φ a' k = selOfAssign φ a k) →
      isProhibited φ (pidOfAssign φ a' ((n : Int) + 1)) = false →
      ((∃ q ∈ Q, q.id.step = (n : Int) + 1) → pidOfAssign φ a' ((n : Int) + 1) = w) →
      ((∃ m ∈ R, m.step = (n : Int) + 1) → selOfAssign φ a' ((n : Int) + 1) = w.id) →
      SemConcl φ (n + 1) Q R := by
    intro a hpre hQa hRa a' hloc hf htq htr
    refine ⟨a', fun k hk => ?_, fun q hq => ?_, fun m hm h0 h1 => ?_⟩
    · push_cast at hk
      rcases Int.lt_or_le k ((n : Int) + 1) with h | h
      · rw [(hloc k (by omega)).1]; exact hpre k h
      · rw [show k = (n : Int) + 1 by omega]; exact hf
    · rcases Int.lt_or_le q.id.step ((n : Int) + 1) with h | h
      · rw [(hloc _ (by omega)).1]; exact hQa q ((memQo q).mpr ⟨hq, by omega⟩)
      · have hqs : q.id.step = (n : Int) + 1 := by have := qstep q hq; omega
        rw [hqs, htq ⟨q, hq, hqs⟩, topQ q hq hqs]
    · push_cast at h1
      rcases Int.lt_or_le m.step ((n : Int) + 1) with h | h
      · rw [(hloc _ (by omega)).2]; exact hRa m ((memRo m).mpr ⟨hm, by omega⟩) h0 (by omega)
      · have hms : m.step = (n : Int) + 1 := by omega
        rw [hms, htr ⟨m, hm, hms⟩, topR m hm hms]
  -- the window of `w` is its parent's, and not prohibited
  have pidw : ∀ a a', (∀ k, k ≤ (n : Int) → pidOfAssign φ a' k = pidOfAssign φ a k ∧
      selOfAssign φ a' k = selOfAssign φ a k) → selOfAssign φ a' ((n : Int) + 1) = w.id →
      selOfAssign φ a pw.id.step = pw.id → (∀ b, pw.parent_id = some b → selOfAssign φ a b.step = b) →
      pidOfAssign φ a' ((n : Int) + 1) = w := by
    intro a a' hloc htop hpa hpb
    apply ParentId.pathNodeId_ext
    · show selOfAssign φ a' ((n : Int) + 1) = w.id; exact htop
    · show (if 0 < (n : Int) + 1 then some (selOfAssign φ a' ((n : Int) + 1 - 1)) else none) = w.parent_id
      rw [if_pos (by omega), show (n : Int) + 1 - 1 = n by omega, (hloc n (Int.le_refl _)).2, ← hpws, hpa, hwpar]
    · show (if 1 < (n : Int) + 1 then some (selOfAssign φ a' ((n : Int) + 1 - 2)) else none) = w.gparent_id
      by_cases h1 : 1 ≤ n
      · obtain ⟨b, hb, hbs⟩ := hwb1 h1
        rw [if_pos (by omega), show (n : Int) + 1 - 2 = n - 1 by omega, (hloc (n - 1) (by omega)).2, ← hbs,
          hpb b hb, hwgp, hb]
      · have h0 : n = 0 := by omega
        have hc : ¬ (1 < (n : Int) + 1) := by rw [h0]; decide
        rw [if_neg hc, hwgp, hwb0 h0]
  cases hz : Q.any (fun q => q.id.step == (n : Int) + 1) with
  | true =>
    obtain ⟨z, hzQ, hzs'⟩ := List.any_eq_true.mp hz
    have hzs : z.id.step = (n : Int) + 1 := eq_of_beq hzs'
    have hzw : z = w := topQ z hzQ hzs
    let E : List NodeId := [pw.id] ++ pw.parent_id.toList ++ (reqOf φ w.id).filter (fun r => decide (0 ≤ r.step))
    have hW' : LWit φ n Qo (Ro ++ E) := witOld E (fun r hrs _ hrQ _ m hm => by
      have hrz := hrQ z hzQ
      rw [hzw] at hrz
      obtain ⟨hpar, hgp, hrq⟩ := owns_top φ hbd n r w hrz hrs hws
      rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_append.mp hm with hm | hm
        · rw [List.mem_singleton.mp hm]; exact hpar pw.id hwpar
        · have hb : pw.parent_id = some m := Option.mem_toList.mp hm
          have h1 : 1 ≤ n := by
            by_cases h1 : 1 ≤ n
            · exact h1
            · rw [hwb0 (by omega)] at hb; cases hb
          exact hgp h1 m (by rw [hwgp, hb])
      · obtain ⟨hmr, hm0⟩ := List.mem_filter.mp hm
        exact hrq m hmr (of_decide_eq_true hm0) (by have := reqOf_backward φ hbd w.id m hmr; omega))
    obtain ⟨a, hpre, hQa, hRa⟩ := ih Qo (Ro ++ E) hQo hW'
    have hreq : ∀ req ∈ reqOf φ w.id, selOfAssign φ a req.step = req := by
      intro req hr
      have h0 := reqOf_nonneg φ hbd w.id req hr
      exact hRa req (List.mem_append_right _ (List.mem_append_right _ (List.mem_filter.mpr ⟨hr, decide_eq_true h0⟩)))
        h0 (by have := reqOf_backward φ hbd w.id req hr; omega)
    obtain ⟨a', hloc, htop⟩ := extend_to φ hbd n a w.id hwm hreq
    have hpa : selOfAssign φ a pw.id.step = pw.id :=
      hRa pw.id (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)))
        (by omega) (by omega)
    have hpb : ∀ b, pw.parent_id = some b → selOfAssign φ a b.step = b := by
      intro b hb
      have h1 : 1 ≤ n := by
        by_cases h1 : 1 ≤ n
        · exact h1
        · rw [hwb0 (by omega)] at hb; cases hb
      obtain ⟨b', hb', hbs⟩ := hwb1 h1
      rw [hb] at hb'; cases hb'
      exact hRa b (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ (Option.mem_toList.mpr hb))))
        (by omega) (by omega)
    have hpid := pidw a a' hloc htop hpa hpb
    exact finish a hpre (fun q hq => hQa q hq) (fun m hm => hRa m (List.mem_append_left _ hm)) a' hloc
      (by rw [hpid]; exact hwf) (fun _ => hpid) (fun _ => htop)
  | false =>
    have hnoz : ∀ q ∈ Q, q.id.step ≤ (n : Int) := by
      intro q hq
      have := qstep q hq
      have hne := List.any_eq_false.mp hz q hq
      rcases Int.lt_or_le q.id.step ((n : Int) + 1) with h | h
      · omega
      · exact absurd (beq_iff_eq.mpr (by omega)) hne
    by_cases hL3 : isL3 φ ((n : Int) + 1) = true
    · exact hcl hL3 Q R hQ hW hnoz
    · have notProh : ∀ a', isProhibited φ (pidOfAssign φ a' ((n : Int) + 1)) = false := by
        intro a'
        have hs : (pidOfAssign φ a' ((n : Int) + 1)).id.step = (n : Int) + 1 := selOfAssign_step φ _ _
        unfold isProhibited; rw [hs]
        cases h : isL3 φ ((n : Int) + 1) with
        | true => exact absurd h hL3
        | false => rfl
      have noTopQ : ¬ ∃ q ∈ Q, q.id.step = (n : Int) + 1 := by
        rintro ⟨q, hq, hqs⟩; have := hnoz q hq; omega
      have hQall : ∀ q ∈ Q, q ∈ Qo := fun q hq => (memQo q).mpr ⟨hq, hnoz q hq⟩
      have hQoQ : ∀ q ∈ Qo, q ∈ Q := fun q hq => ((memQo q).mp hq).1
      cases hr : R.any (fun m => m.step == (n : Int) + 1) with
      | false =>
        have noTopR : ¬ ∃ m ∈ R, m.step = (n : Int) + 1 := by
          rintro ⟨m, hm, hms⟩
          exact (List.any_eq_false.mp hr m hm) (beq_iff_eq.mpr hms)
        have hW' := witOld [] (fun _ _ _ _ _ m hm => absurd hm List.not_mem_nil)
        rw [List.append_nil] at hW'
        obtain ⟨a, hpre, hQa, hRa⟩ := ih Qo Ro hQo hW'
        exact finish a hpre hQa hRa a (fun k _ => ⟨rfl, rfl⟩) (notProh a) (fun h => absurd h noTopQ)
          (fun h => absurd h noTopR)
      | true =>
        obtain ⟨m0, hm0R, hm0s'⟩ := List.any_eq_true.mp hr
        have hm0s : m0.step = (n : Int) + 1 := eq_of_beq hm0s'
        have hm0w : m0 = w.id := topR m0 hm0R hm0s
        let E : List NodeId := (reqOf φ w.id).filter (fun r => decide (0 ≤ r.step))
        have hW' : LWit φ n Qo (Ro ++ E) := witOld E (fun r hrs _ _ hrR m hm => by
          obtain ⟨hmr, hm0⟩ := List.mem_filter.mp hm
          have := ownsMap_top φ hbd n r m0 (hrR m0 hm0R) hrs hm0s
          rw [hm0w] at this
          exact this m hmr (of_decide_eq_true hm0) (by have := reqOf_backward φ hbd w.id m hmr; omega))
        obtain ⟨a, hpre, hQa, hRa⟩ := ih Qo (Ro ++ E) hQo hW'
        have hreq : ∀ req ∈ reqOf φ w.id, selOfAssign φ a req.step = req := by
          intro req hrq
          have h0 := reqOf_nonneg φ hbd w.id req hrq
          exact hRa req (List.mem_append_right _ (List.mem_filter.mpr ⟨hrq, decide_eq_true h0⟩)) h0
            (by have := reqOf_backward φ hbd w.id req hrq; omega)
        obtain ⟨a', hloc, htop⟩ := extend_to φ hbd n a w.id hwm hreq
        exact finish a hpre hQa (fun m hm => hRa m (List.mem_append_left _ hm)) a' hloc (notProh a')
          (fun h => absurd h noTopQ) (fun _ => htop)

/-- **A clique with a member at the new step is passed by a partial solution** (no hypothesis). -/
theorem semConcl_of_top (hbd : Bounded φ) (n : Nat) (ih : SemCert φ n) (Q : List PathNodeId) (R : List NodeId)
    (hQ : LClique φ (n + 1) Q) (hW : LWit φ (n + 1) Q R)
    (htop : Q.any (fun q => q.id.step == (n : Int) + 1) = true) : SemConcl φ (n + 1) Q R := by
  let Qo := Q.filter (fun q => decide (q.id.step ≤ (n : Int)))
  let Ro := R.filter (fun m => decide (m.step ≤ (n : Int)))
  have memQo : ∀ q, q ∈ Qo ↔ q ∈ Q ∧ q.id.step ≤ (n : Int) := by
    intro q; rw [List.mem_filter]; exact ⟨fun ⟨a, b⟩ => ⟨a, of_decide_eq_true b⟩, fun ⟨a, b⟩ => ⟨a, decide_eq_true b⟩⟩
  have memRo : ∀ m, m ∈ Ro ↔ m ∈ R ∧ m.step ≤ (n : Int) := by
    intro m; rw [List.mem_filter]; exact ⟨fun ⟨a, b⟩ => ⟨a, of_decide_eq_true b⟩, fun ⟨a, b⟩ => ⟨a, decide_eq_true b⟩⟩
  have qstep : ∀ q ∈ Q, q.id.step ≤ (n : Int) + 1 := fun q hq => by
    have := owns_step φ hbd (n + 1) q q (hQ q hq q hq); push_cast at this; omega
  have hQo : LClique φ n Qo := by
    intro q hq s hs
    obtain ⟨hqQ, hqs⟩ := (memQo q).mp hq
    obtain ⟨hsQ, hss⟩ := (memQo s).mp hs
    exact owns_old φ hbd n q s (hQ q hqQ s hsQ) hqs hss
  -- a witness below the top, with extra map constraints
  have witOld : ∀ (E : List NodeId), (∀ r, r.id.step ≤ (n : Int) → Node φ (n + 1) r → (∀ q ∈ Q, Owns φ (n + 1) r q) →
      (∀ m ∈ R, OwnsMap φ (n + 1) r m) → ∀ m ∈ E, OwnsMap φ n r m) → LWit φ n Qo (Ro ++ E) := by
    intro E hE l h0 hl
    obtain ⟨r, hrs, hrn, hrQ, hrR⟩ := hW l h0 (by push_cast; omega)
    refine ⟨r, hrs, node_old φ hbd n r hrn (by omega), fun q hq => ?_, fun m hm => ?_⟩
    · obtain ⟨hqQ, hqs⟩ := (memQo q).mp hq
      exact owns_old φ hbd n r q (hrQ q hqQ) (by omega) hqs
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨hmR, hms⟩ := (memRo m).mp hm
        exact ownsMap_old φ hbd n r m (hrR m hmR) (by omega) hms
      · exact hE r (by omega) hrn hrQ hrR m hm
  -- the top witness pins every top constraint and every top member
  obtain ⟨w, hws, hwn, hwQ, hwR⟩ := hW ((n : Int) + 1) (by omega) (by push_cast; omega)
  have topR : ∀ m ∈ R, m.step = (n : Int) + 1 → m = w.id := by
    intro m hm hms
    obtain ⟨kv, hkv, nr, hnr, p, hp, hpm⟩ := hwR m hm
    have := top_owns_self φ hbd n w p ⟨kv, hkv, nr, hnr, hp⟩ hws (by rw [hpm]; exact hms)
    rw [← hpm, this]
  have topQ : ∀ q ∈ Q, q.id.step = (n : Int) + 1 → q = w :=
    fun q hq hqs => top_owns_self φ hbd n w q (hwQ q hq) hws hqs
  obtain ⟨hwf, hwm, pw, hpws, hwpar, hwgp, hwb1, hwb0⟩ := top_node φ hbd n w hwn hws
  -- a partial solution with the old part, extended to the top, gives the conclusion
  have finish : ∀ a, PreSat φ a ((n : Int) + 1) → (∀ q ∈ Qo, pidOfAssign φ a q.id.step = q) →
      (∀ m ∈ Ro, 0 ≤ m.step → m.step ≤ (n : Int) → selOfAssign φ a m.step = m) →
      ∀ a', (∀ k, k ≤ (n : Int) → pidOfAssign φ a' k = pidOfAssign φ a k ∧ selOfAssign φ a' k = selOfAssign φ a k) →
      isProhibited φ (pidOfAssign φ a' ((n : Int) + 1)) = false →
      ((∃ q ∈ Q, q.id.step = (n : Int) + 1) → pidOfAssign φ a' ((n : Int) + 1) = w) →
      ((∃ m ∈ R, m.step = (n : Int) + 1) → selOfAssign φ a' ((n : Int) + 1) = w.id) →
      SemConcl φ (n + 1) Q R := by
    intro a hpre hQa hRa a' hloc hf htq htr
    refine ⟨a', fun k hk => ?_, fun q hq => ?_, fun m hm h0 h1 => ?_⟩
    · push_cast at hk
      rcases Int.lt_or_le k ((n : Int) + 1) with h | h
      · rw [(hloc k (by omega)).1]; exact hpre k h
      · rw [show k = (n : Int) + 1 by omega]; exact hf
    · rcases Int.lt_or_le q.id.step ((n : Int) + 1) with h | h
      · rw [(hloc _ (by omega)).1]; exact hQa q ((memQo q).mpr ⟨hq, by omega⟩)
      · have hqs : q.id.step = (n : Int) + 1 := by have := qstep q hq; omega
        rw [hqs, htq ⟨q, hq, hqs⟩, topQ q hq hqs]
    · push_cast at h1
      rcases Int.lt_or_le m.step ((n : Int) + 1) with h | h
      · rw [(hloc _ (by omega)).2]; exact hRa m ((memRo m).mpr ⟨hm, by omega⟩) h0 (by omega)
      · have hms : m.step = (n : Int) + 1 := by omega
        rw [hms, htr ⟨m, hm, hms⟩, topR m hm hms]
  -- the window of `w` is its parent's, and not prohibited
  have pidw : ∀ a a', (∀ k, k ≤ (n : Int) → pidOfAssign φ a' k = pidOfAssign φ a k ∧
      selOfAssign φ a' k = selOfAssign φ a k) → selOfAssign φ a' ((n : Int) + 1) = w.id →
      selOfAssign φ a pw.id.step = pw.id → (∀ b, pw.parent_id = some b → selOfAssign φ a b.step = b) →
      pidOfAssign φ a' ((n : Int) + 1) = w := by
    intro a a' hloc htop hpa hpb
    apply ParentId.pathNodeId_ext
    · show selOfAssign φ a' ((n : Int) + 1) = w.id; exact htop
    · show (if 0 < (n : Int) + 1 then some (selOfAssign φ a' ((n : Int) + 1 - 1)) else none) = w.parent_id
      rw [if_pos (by omega), show (n : Int) + 1 - 1 = n by omega, (hloc n (Int.le_refl _)).2, ← hpws, hpa, hwpar]
    · show (if 1 < (n : Int) + 1 then some (selOfAssign φ a' ((n : Int) + 1 - 2)) else none) = w.gparent_id
      by_cases h1 : 1 ≤ n
      · obtain ⟨b, hb, hbs⟩ := hwb1 h1
        rw [if_pos (by omega), show (n : Int) + 1 - 2 = n - 1 by omega, (hloc (n - 1) (by omega)).2, ← hbs,
          hpb b hb, hwgp, hb]
      · have h0 : n = 0 := by omega
        have hc : ¬ (1 < (n : Int) + 1) := by rw [h0]; decide
        rw [if_neg hc, hwgp, hwb0 h0]
  cases hz : Q.any (fun q => q.id.step == (n : Int) + 1) with
  | true =>
    obtain ⟨z, hzQ, hzs'⟩ := List.any_eq_true.mp hz
    have hzs : z.id.step = (n : Int) + 1 := eq_of_beq hzs'
    have hzw : z = w := topQ z hzQ hzs
    let E : List NodeId := [pw.id] ++ pw.parent_id.toList ++ (reqOf φ w.id).filter (fun r => decide (0 ≤ r.step))
    have hW' : LWit φ n Qo (Ro ++ E) := witOld E (fun r hrs _ hrQ _ m hm => by
      have hrz := hrQ z hzQ
      rw [hzw] at hrz
      obtain ⟨hpar, hgp, hrq⟩ := owns_top φ hbd n r w hrz hrs hws
      rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_append.mp hm with hm | hm
        · rw [List.mem_singleton.mp hm]; exact hpar pw.id hwpar
        · have hb : pw.parent_id = some m := Option.mem_toList.mp hm
          have h1 : 1 ≤ n := by
            by_cases h1 : 1 ≤ n
            · exact h1
            · rw [hwb0 (by omega)] at hb; cases hb
          exact hgp h1 m (by rw [hwgp, hb])
      · obtain ⟨hmr, hm0⟩ := List.mem_filter.mp hm
        exact hrq m hmr (of_decide_eq_true hm0) (by have := reqOf_backward φ hbd w.id m hmr; omega))
    obtain ⟨a, hpre, hQa, hRa⟩ := ih Qo (Ro ++ E) hQo hW'
    have hreq : ∀ req ∈ reqOf φ w.id, selOfAssign φ a req.step = req := by
      intro req hr
      have h0 := reqOf_nonneg φ hbd w.id req hr
      exact hRa req (List.mem_append_right _ (List.mem_append_right _ (List.mem_filter.mpr ⟨hr, decide_eq_true h0⟩)))
        h0 (by have := reqOf_backward φ hbd w.id req hr; omega)
    obtain ⟨a', hloc, htop⟩ := extend_to φ hbd n a w.id hwm hreq
    have hpa : selOfAssign φ a pw.id.step = pw.id :=
      hRa pw.id (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)))
        (by omega) (by omega)
    have hpb : ∀ b, pw.parent_id = some b → selOfAssign φ a b.step = b := by
      intro b hb
      have h1 : 1 ≤ n := by
        by_cases h1 : 1 ≤ n
        · exact h1
        · rw [hwb0 (by omega)] at hb; cases hb
      obtain ⟨b', hb', hbs⟩ := hwb1 h1
      rw [hb] at hb'; cases hb'
      exact hRa b (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ (Option.mem_toList.mpr hb))))
        (by omega) (by omega)
    have hpid := pidw a a' hloc htop hpa hpb
    exact finish a hpre (fun q hq => hQa q hq) (fun m hm => hRa m (List.mem_append_left _ hm)) a' hloc
      (by rw [hpid]; exact hwf) (fun _ => hpid) (fun _ => htop)
  | false => rw [htop] at hz; cases hz

/-- **The clause, on the tables**: at the third literal of a clause, a clique with witnesses and no
member at that step extends by a top node — an allowed window of the clause — keeping its witnesses. -/
def ClauseLocal (n : Nat) : Prop :=
  isL3 φ ((n : Int) + 1) = true → ∀ Q R, LClique φ (n + 1) Q → LWit φ (n + 1) Q R →
    (∀ q ∈ Q, q.id.step ≤ (n : Int)) →
    ∃ z : PathNodeId, z.id.step = (n : Int) + 1 ∧ LClique φ (n + 1) (z :: Q) ∧ LWit φ (n + 1) (z :: Q) R

/-- **`ClauseChoice ⇐ ClauseLocal`**: the extended clique has a member at the new step. -/
theorem clauseChoice_of_local (hbd : Bounded φ) (n : Nat) (ih : SemCert φ n) (h : ClauseLocal φ n) :
    ClauseChoice φ n := by
  intro hL3 Q R hQ hW hlow
  obtain ⟨z, hzs, hQz, hWz⟩ := h hL3 Q R hQ hW hlow
  obtain ⟨a, hpre, hQa, hRa⟩ := semConcl_of_top φ hbd n ih (z :: Q) R hQz hWz
    (List.any_eq_true.mpr ⟨z, List.mem_cons_self, beq_iff_eq.mpr hzs⟩)
  exact ⟨a, hpre, fun q hq => hQa q (List.mem_cons_of_mem _ hq), hRa⟩

-- ============================================================
-- Conclusion: the reader
-- ============================================================

/-- **The top entries of a state of the line name its key.** -/
theorem top_entry_key (hbd : Bounded φ) (n : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n)
    (r : PathNodeId) (nr : PNodeM) (hnr : kv.2.node? r = some nr) (q : PathNodeId) (hq : q ∈ nr.owners)
    (hqs : q.id.step = (n : Int)) : q.id = kv.1 := by
  cases n with
  | zero =>
    rw [line_zero φ kv hkv] at hnr ⊢
    obtain ⟨_, ho⟩ := seed_node r nr hnr
    rw [ho] at hq; rw [List.mem_singleton.mp hq]
  | succ m =>
    have hrs := owns_step φ hbd (m + 1) r q ⟨kv, hkv, nr, hnr, hq⟩
    have hkv' := hkv
    rw [line_succ] at hkv'
    obtain ⟨kv0, hkv0, hd, hv, n', hn', hqn'⟩ := (src_pureAdvance φ (line φ m) kv hkv').2 r nr hnr q hq
    obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd m kv0 hkv0 kv.1 hd hv
    have c := filt_ctx φ hbd m kv0 hok (reqOf φ kv.1) hvF
    rcases Int.lt_or_le r.id.step ((m : Int) + 1) with h | h
    · obtain ⟨_, _, hqnew, _⟩ := upF_owner_new φ kv0.2 kv.1 hdst c hv r n' hn' (by omega) q hqn'
        (by push_cast at hqs; omega)
      exact mapId_of_mem_newRowIds _ _ _ q hqnew
    · have hrs' : r.id.step = kv0.2.current_step := by push_cast at hrs; omega
      obtain ⟨hrnew, hrow⟩ := upF_new φ kv0.2 kv.1 hdst c hv r n' hn' hrs'
      have hb := KernelIff.below_filterAll_self kv0.2 hnd (reqOf φ kv.1)
      rcases (mem_rowOwners_iff _ _ r q).mp (hrow q hqn') with ⟨hu, _⟩ | he
      · exfalso
        obtain ⟨_, _, np', hnp', hqp'⟩ := KernelReader.mem_unionOwnersOf_inv _ _ q hu
        have := c.rc.ownb np' (List.mem_of_find?_eq_some hnp') q hqp'
        rw [← hb.step] at this; push_cast at hqs; omega
      · rw [he]; exact mapId_of_mem_newRowIds _ _ _ r hrnew

/-- **From the line to the reviewed state: certificates with map constraints.** -/
theorem mapCert_start (hbd : Bounded φ) (n : Nat) (hn : (n : Int) < stepCount φ) (hsem : SemCert φ n)
    (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (hv : isValid (filterAll kv.2 []) = true) :
    MapCert.MapCert (filterAll kv.2 []) := by
  have hok : StateOk φ n kv := (lineOk φ n).2 kv hkv
  have hreach := reachable_of_mapReachable φ hbd kv.2 hok.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  have hb := KernelIff.below_filterAll_self kv.2 hnd []
  have hkey : kv.1.step = n := mapNodes_step φ n kv.1 hok.onMap
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  intro Q R hQ hW
  have hQl : LClique φ n Q := by
    intro q hq s hs
    obtain ⟨nq, hnq, hqQ⟩ := hQ q hq
    obtain ⟨nk, hnk, ho, _, _⟩ := hb.node q nq hnq
    exact ⟨kv, hkv, nk, hnk, ho s (hqQ s hs)⟩
  have hWl : LWit φ n Q (kv.1 :: R) := by
    intro l h0 hl
    obtain ⟨r, nr, hnr, hrs, hrQ, hrR⟩ := hW l h0 (by rw [← hb.step, hok.step]; omega)
    obtain ⟨nk, hnk, ho, _, _⟩ := hb.node r nr hnr
    refine ⟨r, hrs, ⟨kv, hkv, nk, hnk⟩, fun q hq => ⟨kv, hkv, nk, hnk, ho q (hrQ q hq)⟩, fun m hm => ?_⟩
    rcases List.mem_cons.mp hm with e | hm
    · -- a valid node owns a top entry, which names the key
      have hvn := ((isValidNode_iff _ nr).mp (review_node_valid kv.2 hv r nr hnr)).1
      have hcs' : (review kv.2).current_step = (n : Int) + 1 := by rw [← hok.step]; exact hb.step.symm
      rw [hcs'] at hvn
      obtain ⟨p, hp, hps⟩ := List.any_eq_true.mp (List.all_eq_true.mp hvn n (mem_intRange (by omega) (by omega)))
      refine ⟨kv, hkv, nk, hnk, p, ho p hp, ?_⟩
      rw [e]; exact top_entry_key φ hbd n kv hkv r nk hnk p (ho p hp) (eq_of_beq hps)
    · obtain ⟨p, hp, hpm⟩ := hrR m hm
      exact ⟨kv, hkv, nk, hnk, p, ho p hp, hpm⟩
  obtain ⟨a, hpre, hQa, hRa⟩ := hsem Q (kv.1 :: R) hQl hWl
  have hsel : selOfAssign φ a n = kv.1 := by
    have := hRa kv.1 List.mem_cons_self (by omega) (by omega); rw [hkey] at this; exact this
  obtain ⟨g, hmem, hgcs, sel, hs, hids⟩ := cert_of_prefix φ a hbd ((n : Int) + 1) hpre hzero n hn (Int.le_refl _)
  have hg : g = kv.2 := by
    have := key_inj (line φ n) (lineOk φ n).1 (selOfAssign φ a n, g) hmem kv hkv hsel
    rw [← this]
  subst hg
  have hpmp := ParentId.PMP_reachable (reqOf φ) (isProhibited φ) _ hreach
  have hgpmp := ParentId.GPMP_reachable (reqOf φ) (isProhibited φ) _ hreach
  have hpid := chain_eq_pid φ _ sel a hs.chain.1 hpmp hgpmp hs.root_shape.1 hids
  refine ⟨sel, ChainSound_filterAll _ [] sel hs (fun _ h => absurd h List.not_mem_nil), fun q hq => ?_,
    fun m hm h0 h1 => ?_⟩
  · obtain ⟨nq, hnq, _⟩ := hQ q hq
    obtain ⟨nk, hnk, _, _, _⟩ := hb.node q nq hnq
    have hqm := List.mem_of_find?_eq_some hnk
    have hq0 := SelfOwn.SNN_reachable (reqOf φ) (isProhibited φ) _ hreach nk hqm
    have hq1 := steps_below_current (reqOf φ) (isProhibited φ) hreach nk hqm
    rw [node?_id_eq _ q nk hnk] at hq0 hq1
    rw [hpid q.id.step hq0 hq1]; exact hQa q hq
  · rw [← hb.step] at h1
    rw [hids m.step h0 h1]
    exact hRa m (List.mem_cons_of_mem _ hm) h0 (by rw [hok.step] at h1; omega)

/-- **Step 2: `SemCert` along the whole run**, given the clause at every third literal. -/
theorem semCert_all (hbd : Bounded φ) (hcl : ∀ n : Nat, (n : Int) + 1 < stepCount φ → ClauseChoice φ n) :
    ∀ n : Nat, (n : Int) < stepCount φ → SemCert φ n := by
  intro n
  induction n with
  | zero => intro _; exact semCert_zero φ
  | succ m ih =>
    intro hm
    push_cast at hm
    exact semCert_succ φ hbd m (ih (by omega)) (hcl m hm)

/-- **The reader decides `φ` when every third literal of a clause satisfies `ClauseChoice`.** -/
theorem readerVerdictW_iff_of_clauseChoice (hbd : Bounded φ)
    (hcl : ∀ n : Nat, (n : Int) + 1 < stepCount φ → ClauseChoice φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine CertFix.readerVerdictW_iff_of_certLink φ hbd (fun kv hkv hv => ?_)
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hN : (((stepCount φ - 1).toNat : Nat) : Int) < stepCount φ := by omega
  have hmap := mapCert_start φ hbd _ hN (semCert_all φ hbd hcl _ hN) kv hkv hv
  have c := AmbTriCore.aCtx_readPins φ hbd kv hkv [] _ OtherBitSem.ReadPins.start hv
  exact CertInvariant.certLink_of_certClique c (MapCert.certClique_of_mapCert hmap)

/-- info: 'AbsSatBin.GraphPath.Model.LineSem.semCert_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms semCert_succ

/-- info: 'AbsSatBin.GraphPath.Model.LineSem.readerVerdictW_iff_of_clauseChoice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_clauseChoice

/-- **The reader decides `φ` when every third literal of a clause satisfies `ClauseLocal`** — a statement
about the tables only. -/
theorem readerVerdictW_iff_of_clauseLocal (hbd : Bounded φ)
    (hloc : ∀ n : Nat, (n : Int) + 1 < stepCount φ → ClauseLocal φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  have hsem : ∀ n : Nat, (n : Int) < stepCount φ → SemCert φ n := by
    intro n
    induction n with
    | zero => intro _; exact semCert_zero φ
    | succ m ih =>
      intro hm
      push_cast at hm
      have ihm := ih (by omega)
      exact semCert_succ φ hbd m ihm (clauseChoice_of_local φ hbd m ihm (hloc m hm))
  refine CertFix.readerVerdictW_iff_of_certLink φ hbd (fun kv hkv hv => ?_)
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hN : (((stepCount φ - 1).toNat : Nat) : Int) < stepCount φ := by omega
  have hmap := mapCert_start φ hbd _ hN (hsem _ hN) kv hkv hv
  have c := AmbTriCore.aCtx_readPins φ hbd kv hkv [] _ OtherBitSem.ReadPins.start hv
  exact CertInvariant.certLink_of_certClique c (MapCert.certClique_of_mapCert hmap)

/-- info: 'AbsSatBin.GraphPath.Model.LineSem.readerVerdictW_iff_of_clauseLocal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_clauseLocal

end AbsSatBin.GraphPath.Model.LineSem
