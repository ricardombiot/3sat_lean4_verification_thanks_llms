-- lean_project/AbsSat/GraphPath/Model/FixAgreeInv.lean
import AbsSat.GraphPath.Model.IdDiesProof

/-!
# Owners agree with every value a node's id fixes

A path node's id fixes the values of some variables (`IdSeparator.fixes`): its map node's, and its
parent's. `FixAgree φ g` says that a node and each of its owners never fix the same variable to
different values — at any step, clause rows included. It is proved for every state the machine
builds (`FixAgree_reachable`).

The only step that creates new owner entries is `addNode`: the new node `pid = (d, key)` becomes an
owner of every node, and is handed the global owners as its own. Every node of the filtered state
agrees with every value `pid` fixes (`new_consistent`), by where that value comes from:

* a pin of `d` — the global owner at the pin's step is the pin, and `Agree` forces the value;
* a requirement of the key — the same, through `ParentInv.kp`;
* the key itself, when it is a value node — `TopKey` makes the owner at the top step the key;
* `d` itself, when it is a value node — no earlier node fixes that variable.

Pruning only removes entries, and a join only unions entries of equal ids.

Measured on `SatMachinePure`: 0 disagreements in 5,196,906 checked pairs (v100).
-/

namespace AbsSat.GraphPath.Model.FixAgreeInv

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.IdSeparator
open AbsSat.GraphPath.Model.ParentOwners
open AbsSat.GraphPath.Model.LitOwners
open AbsSat.GraphPath.Model.IdDiesProof

variable (φ : Cnf)

/-- Two lists of fixed values agree on every common variable. -/
def Consistent (a b : List (Int × Int)) : Prop :=
  ∀ vv ∈ a, ∀ ww ∈ b, vv.1 = ww.1 → vv.2 = ww.2

theorem consistent_symm {a b : List (Int × Int)} (h : Consistent a b) : Consistent b a :=
  fun vv hv ww hw hs => (h ww hw vv hv hs.symm).symm

/-- **A node and each of its owners fix no variable to different values.** -/
def FixAgree (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, ∀ q ∈ n.owners, Consistent (fixes φ n.id) (fixes φ q)

-- ============================================================
-- Where a fixed value comes from
-- ============================================================

/-- A value a map node fixes is a requirement's value, or the node's own value. -/
theorem fixesMap_cases (m : NodeId) (ww : Int × Int) (h : ww ∈ fixesMap φ m) :
    (∃ r ∈ reqOfCnf φ m, varVal φ r = some ww) ∨
      (0 ≤ m.step ∧ m.step < litBlock φ ∧ m.step % 2 = 0 ∧ ww = (m.step / 2, m.index)) := by
  unfold fixesMap at h
  by_cases h1 : m.step < litBlock φ
  · rw [if_pos h1] at h
    cases hvm : varVal φ m with
    | none =>
      rw [hvm] at h
      exact absurd h List.not_mem_nil
    | some vv' =>
      rw [hvm] at h
      have h' : ww ∈ [vv'] := h
      have hve : ww = vv' := List.mem_singleton.mp h'
      subst hve
      obtain ⟨v, b⟩ := ww
      obtain ⟨h0, hlt, hcase⟩ := varVal_spec φ m v b hvm
      rcases hcase with ⟨hs, hi⟩ | ⟨hs, hi⟩
      · exact Or.inr ⟨h0, hlt, by omega,
          Prod.ext (by show v = m.step / 2; omega) (by show b = m.index; omega)⟩
      · left
        have hreq := reqOfCnf_neg φ m h0 hlt (by omega)
        refine ⟨{ step := m.step - 1, index := 1 - m.index },
          by rw [hreq]; exact List.mem_singleton_self _, ?_⟩
        rw [varVal_even φ _ (by show 0 ≤ m.step - 1; omega)
          (by show m.step - 1 < litBlock φ; omega) (by show (m.step - 1) % 2 = 0; omega)]
        show some ((m.step - 1) / 2, 1 - m.index) = some (v, b)
        rw [show (m.step - 1) / 2 = v by omega, show 1 - m.index = b by omega]
  · rw [if_neg h1] at h
    by_cases h2 : m.step = litBlock φ
    · rw [if_pos h2] at h
      exact absurd h List.not_mem_nil
    · rw [if_neg h2] at h
      obtain ⟨l, hl, hvl⟩ := List.mem_filterMap.mp h
      exact Or.inl ⟨l, hl, hvl⟩

/-- In the literal block, a map node fixes only variables at or below its step. -/
theorem fixesMap_var_le (hback : ∀ x, ∀ r ∈ reqOfCnf φ x, r.step < x.step) (m : NodeId)
    (ww : Int × Int) (h : ww ∈ fixesMap φ m) : 2 * ww.1 ≤ m.step := by
  rcases fixesMap_cases φ m ww h with ⟨r, hr, hvr⟩ | ⟨_, _, _, hww⟩
  · obtain ⟨v, b⟩ := ww
    obtain ⟨_, _, hcase⟩ := varVal_spec φ r v b hvr
    have := hback m r hr
    show 2 * v ≤ m.step
    rcases hcase with ⟨hs, _⟩ | ⟨hs, _⟩ <;> omega
  · rw [hww]
    show 2 * (m.step / 2) ≤ m.step
    omega

theorem mem_fixesMap_of_varVal (r : NodeId) (ww : Int × Int) (h : varVal φ r = some ww) :
    ww ∈ fixesMap φ r := by
  obtain ⟨v, b⟩ := ww
  obtain ⟨_, hlt, _⟩ := varVal_spec φ r v b h
  unfold fixesMap
  rw [if_pos hlt, h]
  exact List.mem_singleton_self _

-- ============================================================
-- The facts about a valid filtered state that addNode needs
-- ============================================================

structure UpCtx (F : GPathM) (d : NodeId) : Prop where
  agree : ∀ n ∈ F.nodes, ∀ vv ∈ fixes φ n.id, Agree n vv.1 vv.2
  own : ∀ n ∈ F.nodes, ∀ k, 0 ≤ k → k < F.current_step →
    ∃ u ∈ n.owners, u.id.step = k ∧ u ∈ F.gowners
  pin : ∀ q ∈ F.gowners, ∀ r ∈ reqOfCnf φ d, q.id.step = r.step → q.id = r
  kp : ∀ p, F.map_parent = some p → ∀ q ∈ F.gowners, ∀ r ∈ reqOfCnf φ p,
    q.id.step = r.step → q.id = r
  top : ∀ q ∈ F.gowners, q.id.step = F.current_step - 1 → F.map_parent = some q.id
  gn : ∀ q ∈ F.gowners, ∃ x ∈ F.nodes, x.id = q
  below : ∀ n ∈ F.nodes, n.id.id.step < F.current_step
  step : d.step = F.current_step
  keystep : ∀ p, F.map_parent = some p → p.step + 1 = F.current_step
  ps : ∀ n ∈ F.nodes, ∀ p, n.id.parent_id = some p → p.step + 1 = n.id.id.step
  valid : isValid F = true
  back : ∀ x, ∀ r ∈ reqOfCnf φ x, r.step < x.step
  nonneg : ∀ x, ∀ r ∈ reqOfCnf φ x, 0 ≤ r.step
  /-- The top line carries `map_parent` — what makes every row identifier record
  it in its second component. -/
  tl : ParentId.TL F
  pos : 0 < F.current_step

section Up

variable {φ} {F : GPathM} {d : NodeId} (ctx : UpCtx φ F d)
include ctx

/-- **A row identifier fixes exactly what the old single new node fixed**: its own
map node's values and `map_parent`'s, because the window's second component *is*
`map_parent` on the top line (`ParentId.TL`). -/
theorem fixes_row {z : PathNodeId} (hz : z ∈ newRowIds F d) :
    fixes φ z = fixesMap φ d ++
      (match F.map_parent with | some p => fixesMap φ p | none => []) := by
  obtain ⟨r, hr, rfl⟩ := exists_shift_of_mem_newRowIds F d z ctx.pos hz
  have hrmp : F.map_parent = some r.id := by
    unfold newParents at hr
    rw [if_pos ctx.pos] at hr
    obtain ⟨nr, hnr, hnrid⟩ := List.mem_map.mp hr
    have := ctx.tl nr (List.mem_filter.mp hnr).1 (eq_of_beq (List.mem_filter.mp hnr).2)
    rw [hnrid] at this
    exact this.symm
  show fixesMap φ d ++ (match (some r.id : Option NodeId) with
      | some p => fixesMap φ p | none => []) = _
  rw [hrmp]

/-- A node agrees with every pinned literal: the global owner at the pin's step is the pin. -/
theorem agree_pinned (R : List NodeId)
    (hR : ∀ q ∈ F.gowners, ∀ r ∈ R, q.id.step = r.step → q.id = r)
    (hRb : ∀ r ∈ R, 0 ≤ r.step ∧ r.step < F.current_step)
    {n : PNodeM} (hn : n ∈ F.nodes) {vv : Int × Int} (hvv : vv ∈ fixes φ n.id)
    {r : NodeId} (hr : r ∈ R) {pv : Int × Int} (hpv : varVal φ r = some pv)
    (hsame : pv.1 = vv.1) : pv.2 = vv.2 := by
  have hag := ctx.agree n hn vv hvv
  obtain ⟨u, hu, hus, hug⟩ := ctx.own n hn r.step (hRb r hr).1 (hRb r hr).2
  have hur : u.id = r := hR u hug r hr hus
  obtain ⟨v, b⟩ := pv
  have hsame' : v = vv.1 := hsame
  show b = vv.2
  obtain ⟨_, _, hcase⟩ := varVal_spec φ r v b hpv
  rcases hcase with ⟨hs, hi⟩ | ⟨hs, hi⟩
  · have hidx := hag.1 u hu (by rw [hus, hs, hsame'])
    rw [hur, hi] at hidx
    exact hidx
  · have hidx := hag.2 u hu (by rw [hus, hs, hsame'])
    rw [hur, hi] at hidx
    omega

/-- A node agrees with the key's own value, when the key is a value node. -/
theorem agree_key_value {n : PNodeM} (hn : n ∈ F.nodes) {vv : Int × Int}
    (hvv : vv ∈ fixes φ n.id) {p : NodeId} (hp : F.map_parent = some p) (h0 : 0 ≤ p.step)
    (hev : p.step % 2 = 0) (hsame : p.step / 2 = vv.1) : p.index = vv.2 := by
  have hag := ctx.agree n hn vv hvv
  have hks := ctx.keystep p hp
  obtain ⟨u, hu, hus, hug⟩ := ctx.own n hn p.step h0 (by omega)
  have htop := ctx.top u hug (by omega)
  rw [hp] at htop
  have hup : p = u.id := Option.some.inj htop
  have hidx := hag.1 u hu (by rw [hus]; omega)
  rw [← hup] at hidx
  exact hidx

/-- The values a node of the literal block fixes sit at or below its step. -/
theorem fixes_var_le {n : PNodeM} (hn : n ∈ F.nodes) (vv : Int × Int)
    (h : vv ∈ fixes φ n.id) : 2 * vv.1 ≤ n.id.id.step := by
  unfold fixes at h
  rcases List.mem_append.mp h with h | h
  · exact fixesMap_var_le φ ctx.back _ vv h
  · cases hp : n.id.parent_id with
    | none =>
      rw [hp] at h
      exact absurd h List.not_mem_nil
    | some p =>
      rw [hp] at h
      have hps := ctx.ps n hn p hp
      have := fixesMap_var_le φ ctx.back p vv h
      omega

/-- **Every node of the filtered state agrees with every value the new node fixes.** -/
theorem new_consistent {n : PNodeM} (hn : n ∈ F.nodes) {z : PathNodeId}
    (hz : z ∈ newRowIds F d) : Consistent (fixes φ n.id) (fixes φ z) := by
  intro vv hvv ww hww hsame
  rw [fixes_row ctx hz] at hww
  rcases List.mem_append.mp hww with hw | hw
  · rcases fixesMap_cases φ d ww hw with ⟨r, hr, hvr⟩ | ⟨_, _, _, hwd⟩
    · exact (agree_pinned ctx (reqOfCnf φ d) ctx.pin
        (fun r hr => ⟨ctx.nonneg d r hr, by have := ctx.back d r hr; rw [← ctx.step]; exact this⟩)
        hn hvv hr hvr hsame.symm).symm
    · exfalso
      have hbn := ctx.below n hn
      have hle := fixes_var_le ctx hn vv hvv
      rw [hwd] at hsame
      have hs' : vv.1 = d.step / 2 := hsame
      have hst := ctx.step
      omega
  · cases hp : F.map_parent with
    | none =>
      rw [hp] at hw
      exact absurd hw List.not_mem_nil
    | some p =>
      rw [hp] at hw
      rcases fixesMap_cases φ p ww hw with ⟨r, hr, hvr⟩ | ⟨h0, _, hev, hwp⟩
      · exact (agree_pinned ctx (reqOfCnf φ p) (ctx.kp p hp)
          (fun r hr => ⟨ctx.nonneg p r hr,
            by have := ctx.back p r hr; have := ctx.keystep p hp; omega⟩)
          hn hvv hr hvr hsame.symm).symm
      · rw [hwp] at hsame ⊢
        exact (agree_key_value ctx hn hvv hp h0 hev hsame.symm).symm

/-- A value the new node fixes is fixed by some node of the filtered state, unless it is the new
node's own value as a value node. -/
theorem witness {z : PathNodeId} (hz : z ∈ newRowIds F d)
    (ww : Int × Int) (hw : ww ∈ fixes φ z) :
    (∃ x ∈ F.nodes, ww ∈ fixes φ x.id) ∨
      (0 ≤ d.step ∧ d.step < litBlock φ ∧ d.step % 2 = 0 ∧ ww = (d.step / 2, d.index)) := by
  rw [fixes_row ctx hz] at hw
  -- a pinned literal names a node of the filtered state
  have hlit : ∀ (R : List NodeId), (∀ q ∈ F.gowners, ∀ r ∈ R, q.id.step = r.step → q.id = r) →
      (∀ r ∈ R, 0 ≤ r.step ∧ r.step < F.current_step) →
      ∀ r ∈ R, varVal φ r = some ww → ∃ x ∈ F.nodes, ww ∈ fixes φ x.id := by
    intro R hR hRb r hr hvr
    have hent := hasStepEntry_of_isValid F ctx.valid r.step (hRb r hr).1 (hRb r hr).2
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
    obtain ⟨q, hq, hqs⟩ := hent
    have hqr := hR q hq r hr hqs
    obtain ⟨x, hx, hxid⟩ := ctx.gn q hq
    refine ⟨x, hx, List.mem_append_left _ ?_⟩
    rw [hxid, hqr]
    exact mem_fixesMap_of_varVal φ r ww hvr
  rcases List.mem_append.mp hw with hw | hw
  · rcases fixesMap_cases φ d ww hw with ⟨r, hr, hvr⟩ | hval
    · exact Or.inl (hlit (reqOfCnf φ d) ctx.pin
        (fun r hr => ⟨ctx.nonneg d r hr, by have := ctx.back d r hr; rw [← ctx.step]; exact this⟩)
        r hr hvr)
    · exact Or.inr hval
  · cases hp : F.map_parent with
    | none =>
      rw [hp] at hw
      exact absurd hw List.not_mem_nil
    | some p =>
      rw [hp] at hw
      rcases fixesMap_cases φ p ww hw with ⟨r, hr, hvr⟩ | ⟨h0, hlt, hev, hwp⟩
      · exact Or.inl (hlit (reqOfCnf φ p) (ctx.kp p hp)
          (fun r hr => ⟨ctx.nonneg p r hr,
            by have := ctx.back p r hr; have := ctx.keystep p hp; omega⟩)
          r hr hvr)
      · left
        have hks := ctx.keystep p hp
        have hent := hasStepEntry_of_isValid F ctx.valid p.step h0 (by omega)
        simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
        obtain ⟨q, hq, hqs⟩ := hent
        have htop := ctx.top q hq (by omega)
        rw [hp] at htop
        have hpq : p = q.id := Option.some.inj htop
        obtain ⟨x, hx, hxid⟩ := ctx.gn q hq
        refine ⟨x, hx, List.mem_append_left _ ?_⟩
        rw [hxid, ← hpq]
        apply mem_fixesMap_of_varVal
        rw [varVal_even φ p h0 hlt hev, hwp]

/-- The new node's own fixed values agree with each other. -/
theorem self_consistent {z z' : PathNodeId} (hz : z ∈ newRowIds F d)
    (hz' : z' ∈ newRowIds F d) : Consistent (fixes φ z) (fixes φ z') := by
  intro vv hvv ww hww hsame
  rcases witness ctx hz vv hvv with ⟨x, hx, hvx⟩ | ⟨_, _, _, hvd⟩
  · exact new_consistent ctx hx hz' vv hvx ww hww hsame
  · rcases witness ctx hz' ww hww with ⟨x, hx, hwx⟩ | ⟨_, _, _, hwd⟩
    · exact (new_consistent ctx hx hz ww hwx vv hvv hsame.symm).symm
    · rw [hvd, hwd]

/-- **`addNode` keeps `FixAgree`.** -/
theorem FixAgree_addNode (title : String) (h : FixAgree φ F) : FixAgree φ (addNode F d title) := by
  intro n' hn' q hq
  rcases mem_addNode_nodes hn' with ⟨n, hn, rfl⟩ | ⟨pid, hpid, rfl⟩
  · rw [upMap_owners] at hq
    rw [upMap_id]
    rcases List.mem_append.mp hq with hq | hq
    · exact h n hn q hq
    · exact new_consistent ctx hn (gainedOwners_subset F d n q hq)
  · rw [rowNode_id]
    rw [rowNode_owners] at hq
    rcases rowOwners_mem_gowners_or_self F d pid q hq with hq | rfl
    · obtain ⟨x, hx, hxid⟩ := ctx.gn q hq
      rw [← hxid]
      exact consistent_symm (new_consistent ctx hx hpid)
    · exact self_consistent ctx hpid hpid

end Up

-- ============================================================
-- Seed, pruning, join
-- ============================================================

theorem FixAgree_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : FixAgree φ g) :
    FixAgree φ g' := by
  intro n' hn' q hq
  obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived n' hn'
  rw [hid]
  exact h n hn q (hown q hq)

theorem FixAgree_join (g₁ g₂ : GPathM) (h₁ : FixAgree φ g₁) (h₂ : FixAgree φ g₂) :
    FixAgree φ (join g₁ g₂) := by
  intro n hn q hq
  rcases mem_join_nodes' hn with ⟨a, ha, hid, hown⟩ | hn2
  · rw [hid]
    rcases hown q hq with hqa | ⟨b, hb, hbid, hqb⟩
    · exact h₁ a ha q hqa
    · rw [← hbid]
      exact h₂ b hb q hqb
  · exact h₂ n hn2 q hq

theorem FixAgree_initSeed (hwf : WF φ) (d : NodeId) (title : String) (hd : d.step = 0) :
    FixAgree φ (initSeed d title) := by
  have hseed : initSeed d title = addNode empty d title := rfl
  intro n hn q hq
  rw [hseed] at hn
  rcases mem_addNode_nodes hn with ⟨m, hm, _⟩ | ⟨pid, hpid, rfl⟩
  · exact absurd hm List.not_mem_nil
  · have hrow : newRowIds empty d = [{ id := d, parent_id := none, gparent_id := none }] :=
      newRowIds_of_zero empty d (by show ¬ (0:Int) < 0; omega)
    rw [hrow] at hpid
    rcases List.mem_singleton.mp hpid with rfl
    rw [rowNode_owners] at hq
    have hqz : q = { id := d, parent_id := none, gparent_id := none } := by
      rcases rowOwners_mem_gowners_or_self empty d _ q hq with h | h
      · exact absurd h List.not_mem_nil
      · exact h
    rw [rowNode_id, hqz]
    show Consistent (fixes φ { id := d, parent_id := none, gparent_id := none })
      (fixes φ { id := d, parent_id := none, gparent_id := none })
    have hfix : fixes φ ({ id := d, parent_id := none, gparent_id := none } : PathNodeId)
        = fixesMap φ d ++ [] := rfl
    rw [hfix, List.append_nil]
    -- at step 0 a map node fixes at most its own value
    have hone : ∀ ww ∈ fixesMap φ d, ww = (d.step / 2, d.index) := by
      intro ww hww
      rcases fixesMap_cases φ d ww hww with ⟨r, hr, _⟩ | ⟨_, _, _, hwd⟩
      · have h1 := reqOfCnf_backward φ hwf d r hr
        have h2 := UnitPropagation.reqOfCnf_nonneg φ d r hr
        omega
      · exact hwd
    intro vv hvv ww hww _
    rw [hone vv hvv, hone ww hww]

-- ============================================================
-- Every reachable state
-- ============================================================

/-- **`FixAgree` holds in every state the machine builds.** -/
theorem FixAgree_reachable (hwf : WF φ) (g : GPathM) (hr : Reachable (reqOfCnf φ) g) :
    FixAgree φ g := by
  have hback : ∀ x, ∀ r ∈ reqOfCnf φ x, r.step < x.step :=
    fun x r h => reqOfCnf_backward φ hwf x r h
  have hnonneg : ∀ x, ∀ r ∈ reqOfCnf φ x, 0 ≤ r.step :=
    fun x r h => UnitPropagation.reqOfCnf_nonneg φ x r h
  have hdist : ∀ x, ∀ r₁ ∈ reqOfCnf φ x, ∀ r₂ ∈ reqOfCnf φ x, r₁.step = r₂.step → r₁ = r₂ :=
    fun x r₁ h₁ r₂ h₂ hs => reqOfCnf_functional φ hwf x r₁ h₁ r₂ h₂ hs
  induction hr with
  | seed d title hstep _ => exact FixAgree_initSeed φ hwf d title hstep
  | up g d title hstep _ _ hrg ih =>
    have hpr := pruned_filterAll g (reqOfCnf φ d)
    dsimp only [GPathM.upFiltering, GPathM.up]
    split
    · next hv =>
      have hoos := SelfOwn.OOS_reachable (reqOfCnf φ) g hrg
      have hoc := UnitPropagation.OwnedCompatible_reachable (reqOfCnf φ) hback hnonneg g hrg
      have hrf := L1 (reqOfCnf φ) hrg
      have hpi := ParentInv_reachable (reqOfCnf φ) hback g hrg
      have hli := LitInv_reachable (reqOfCnf φ) hback hnonneg hdist g hrg
      have hpiF := ParentInv_of_pruned (reqOfCnf φ) hpr hpi
      have hnd : NodupIds (filterAll g (reqOfCnf φ d)) :=
        NodeIds.NodupIds_filterAll g (Reader.NodupIds_reachable (reqOfCnf φ) g hrg) (reqOfCnf φ d)
      have htk := NodeInvariant.TopKey_of_pruned hpr (NodeInvariant.TopKey_reachable (reqOfCnf φ) g hrg)
      have ctx : UpCtx φ (filterAll g (reqOfCnf φ d)) d := {
        agree := by
          intro n' hn' vv hvv
          obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived n' hn'
          have hvv' : vv ∈ fixes φ n.id := by rw [← hid]; exact hvv
          have hag := agree_of_fixes φ hoos hoc hrf hpi hli hn hvv'
          exact ⟨fun w hw hs => hag.1 w (hown w hw) hs, fun w hw hs => hag.2 w (hown w hw) hs⟩
        own := by
          intro n hn k h0 hk
          have hnode := node?_of_mem hnd n hn
          have hvalid := review_node_valid ((reqOfCnf φ d).foldl filterRequire g) hv n.id n hnode
          have hfixo := review_owners_within_gowners ((reqOfCnf φ d).foldl filterRequire g) hv n.id n hnode
          exact UnitPropagation.owner_at_step g (reqOfCnf φ d) hv n hvalid hfixo k h0
            (by rw [← hpr.step_eq]; exact hk)
        pin := fun q hq r hr hs => filterAll_cleans_gowner g (reqOfCnf φ d) r q hr hq hs
        kp := fun p hp q hq r hr hs => hpiF.kp p hp q hq r hr hs
        top := fun q hq hqs => htk.2.2 q hq hqs
        gn := by
          intro q hq
          exact GownersNodes.GN_filterAll g (reqOfCnf φ d) (GownersNodes.GN_reachable (reqOfCnf φ) g hrg) q hq
        below := Certifies.nodes_below_of_pruned hpr (steps_below_current (reqOfCnf φ) hrg)
        step := by rw [hpr.step_eq]; exact hstep
        keystep := by
          intro p hp
          have hpos : 0 < (filterAll g (reqOfCnf φ d)).current_step := by
            rw [hpr.step_eq]; exact NodeInvariant.pos_reachable (reqOfCnf φ) g hrg
          have hent := hasStepEntry_of_isValid _ hv ((filterAll g (reqOfCnf φ d)).current_step - 1)
            (by omega) (by omega)
          simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
          obtain ⟨q, hq, hqs⟩ := hent
          have htop := htk.2.2 q hq hqs
          rw [hp] at htop
          have hpq : p = q.id := Option.some.inj htop
          rw [hpq]
          omega
        ps := fun n hn p hp => hpiF.ps n hn p hp
        valid := hv
        back := hback
        nonneg := hnonneg
        tl := ParentId.TL_of_pruned hpr (ParentId.TL_reachable (reqOfCnf φ) g hrg)
        pos := by rw [hpr.step_eq]; exact NodeInvariant.pos_reachable (reqOfCnf φ) g hrg }
      exact FixAgree_addNode ctx title (FixAgree_of_pruned φ hpr ih)
    · exact FixAgree_of_pruned φ hpr ih
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact FixAgree_join φ g₁ g₂ ih₁ ih₂

/-- info: 'AbsSat.GraphPath.Model.FixAgreeInv.FixAgree_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FixAgree_reachable

end AbsSat.GraphPath.Model.FixAgreeInv
