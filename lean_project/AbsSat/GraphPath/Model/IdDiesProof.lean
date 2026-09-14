-- lean_project/AbsSat/GraphPath/Model/IdDiesProof.lean
import AbsSat.GraphPath.Model.IdSeparator
import AbsSat.GraphPath.Model.LitOwners
import AbsSat.GraphPath.Model.FabricAdd

/-!
# S2: a global owner whose id contradicts a pin is in the removal closure

`IdSeparator.IdDies` is proved here for the machine's sends (`d.step = g.current_step`), for every
reachable state of a well-formed formula.

The heart is `Agree n v b`: every owner of `n` at the value step `2v` has index `b`, and every owner
at the negation step `2v + 1` has index `1 − b`. Whenever the id of `n` fixes variable `v` to `b`,
`n` agrees with it (`agree_of_fixes`), by the source of the literal:

* a requirement of the node's own or parent map node — `ReqFiltered` / `ParentInv.pr` at the literal's
  step, `LitInv` at the other step of the variable (`agree_of_req`);
* the node's own map node, a value node — `OOS` at its step, `OwnedCompatible` at the negation step
  (`agree_self_value`);
* the parent's map node, a value node — `ParentInv.po` at its step, `OOS` and `ParentInv.rp` at the
  node's own step (`agree_parent_value`);
* a negation map node fixes its variable through its requirement, which is the first case.

A pin `r` on the same variable with the other value names an owner index `Agree` excludes. The global
owners of the pinned state at the pin's step are `r` itself, so the node has none there: it is
unsupported at that step (`idDies`). With it, no zombies follows from S1 alone
(`noZombie_of_idSeparator_only`).

Measured on `SatMachinePure` (seeds 1001, 7777, 31337, 90210): 39,655 of 39,655 such nodes die in the
first round of the closure.
-/

namespace AbsSat.GraphPath.Model.IdDiesProof

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.RemovalClosure
open AbsSat.GraphPath.Model.IdSeparator
open AbsSat.GraphPath.Model.ParentOwners
open AbsSat.GraphPath.Model.LitOwners

variable (φ : Cnf)

-- ============================================================
-- The literal block of the map
-- ============================================================

theorem litBlock_even : litBlock φ % 2 = 0 := by unfold litBlock; omega

/-- A negation node requires the value node with the opposite index. -/
theorem reqOfCnf_neg (m : NodeId) (h0 : 0 ≤ m.step) (hl : m.step < litBlock φ)
    (hodd : m.step % 2 = 1) :
    reqOfCnf φ m = [{ step := m.step - 1, index := 1 - m.index }] := by
  unfold reqOfCnf
  rw [if_neg (by omega), if_pos hl, if_neg (by omega)]

theorem varVal_even (l : NodeId) (h0 : 0 ≤ l.step) (hl : l.step < litBlock φ)
    (hev : l.step % 2 = 0) : varVal φ l = some (l.step / 2, l.index) := by
  unfold varVal
  rw [if_neg (by omega), if_pos hev]

/-- What `varVal` returns: a value node at `2v` with index `b`, or a negation node at `2v + 1` with
index `1 − b`. -/
theorem varVal_spec (l : NodeId) (v b : Int) (h : varVal φ l = some (v, b)) :
    0 ≤ l.step ∧ l.step < litBlock φ ∧
      ((l.step = 2 * v ∧ l.index = b) ∨ (l.step = 2 * v + 1 ∧ l.index = 1 - b)) := by
  by_cases hr : l.step < 0 ∨ litBlock φ ≤ l.step
  · unfold varVal at h
    rw [if_pos hr] at h
    cases h
  · have h0 : 0 ≤ l.step := by omega
    have hl : l.step < litBlock φ := by omega
    by_cases hev : l.step % 2 = 0
    · rw [varVal_even φ l h0 hl hev] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hv, hb⟩ := h
      exact ⟨h0, hl, Or.inl ⟨by omega, hb⟩⟩
    · unfold varVal at h
      rw [if_neg hr, if_neg hev, reqOfCnf_neg φ l h0 hl (by omega)] at h
      have hcond : (l.step - 1) % 2 = 0 := by omega
      simp only [hcond, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hv, hb⟩ := h
      exact ⟨h0, hl, Or.inr ⟨by omega, by omega⟩⟩

-- ============================================================
-- Agreement of the owners with a fixed value
-- ============================================================

/-- Owners of `n` at the literal steps of variable `v` carry the value `b`. -/
def Agree (n : PNodeM) (v b : Int) : Prop :=
  (∀ w ∈ n.owners, w.id.step = 2 * v → w.id.index = b) ∧
  (∀ w ∈ n.owners, w.id.step = 2 * v + 1 → w.id.index = 1 - b)

theorem agree_of_req {g : GPathM} (hli : LitInv (reqOfCnf φ) g) {n : PNodeM} (hn : n ∈ g.nodes)
    {m : NodeId} (hm : FixMap n m)
    (hexact : ∀ l ∈ reqOfCnf φ m, ∀ w ∈ n.owners, w.id.step = l.step → w.id = l)
    {l : NodeId} (hl : l ∈ reqOfCnf φ m) {v b : Int} (hvv : varVal φ l = some (v, b)) :
    Agree n v b := by
  obtain ⟨h0, hlt, hcase⟩ := varVal_spec φ l v b hvv
  have hev := litBlock_even φ
  rcases hcase with ⟨hs, hi⟩ | ⟨hs, hi⟩
  · refine ⟨fun w hw hws => ?_, fun w hw hws => ?_⟩
    · have hwl := hexact l hl w hw (by omega)
      rw [hwl, hi]
    · have hreq := reqOfCnf_neg φ w.id (by omega) (by omega) (by omega)
      have hmem : ({ step := w.id.step - 1, index := 1 - w.id.index } : NodeId) ∈
          reqOfCnf φ w.id := by
        rw [hreq]; exact List.mem_singleton_self _
      have heq := hli.own n hn m hm l hl w hw _ hmem (by show w.id.step - 1 = l.step; omega)
      have hidx : 1 - w.id.index = l.index := by rw [← heq]
      omega
  · refine ⟨fun w hw hws => ?_, fun w hw hws => ?_⟩
    · have hreq := reqOfCnf_neg φ l h0 hlt (by omega)
      have hmem : ({ step := l.step - 1, index := 1 - l.index } : NodeId) ∈ reqOfCnf φ l := by
        rw [hreq]; exact List.mem_singleton_self _
      have heq := hli.twin n hn m hm l hl _ hmem w hw (by show w.id.step = l.step - 1; omega)
      rw [heq]
      show 1 - l.index = b
      omega
    · have hwl := hexact l hl w hw (by omega)
      rw [hwl, hi]

theorem agree_self_value {g : GPathM} (hoos : SelfOwn.OOS g)
    (hoc : UnitPropagation.OwnedCompatible (reqOfCnf φ) g)
    {n : PNodeM} (hn : n ∈ g.nodes) (h0 : 0 ≤ n.id.id.step) (hlt : n.id.id.step < litBlock φ)
    (hev : n.id.id.step % 2 = 0) : Agree n (n.id.id.step / 2) n.id.id.index := by
  have hlb := litBlock_even φ
  refine ⟨fun w hw hws => ?_, fun w hw hws => ?_⟩
  · have hwn := hoos n hn w hw (by omega)
    rw [hwn]
  · have hreq := reqOfCnf_neg φ w.id (by omega) (by omega) (by omega)
    have hmem : ({ step := w.id.step - 1, index := 1 - w.id.index } : NodeId) ∈
        reqOfCnf φ w.id := by
      rw [hreq]; exact List.mem_singleton_self _
    have heq := hoc n hn w hw _ hmem (by show n.id.id.step = w.id.step - 1; omega)
    have hidx : n.id.id.index = 1 - w.id.index := by rw [heq]
    omega

theorem agree_parent_value {g : GPathM} (hoos : SelfOwn.OOS g) (hpi : ParentInv (reqOfCnf φ) g)
    {n : PNodeM} (hn : n ∈ g.nodes) {p : NodeId} (hp : n.id.parent_id = some p)
    (h0 : 0 ≤ p.step) (hlt : p.step < litBlock φ) (hev : p.step % 2 = 0) :
    Agree n (p.step / 2) p.index := by
  have hlb := litBlock_even φ
  have hps := hpi.ps n hn p hp
  refine ⟨fun w hw hws => ?_, fun w hw hws => ?_⟩
  · have hpo := hpi.po n hn w hw (by omega)
    rw [hp] at hpo
    have hwp : w.id = p := Option.some.inj hpo
    rw [hwp]
  · have hwn := hoos n hn w hw (by omega)
    have hreq := reqOfCnf_neg φ n.id.id (by omega) (by omega) (by omega)
    have hmem : ({ step := n.id.id.step - 1, index := 1 - n.id.id.index } : NodeId) ∈
        reqOfCnf φ n.id.id := by
      rw [hreq]; exact List.mem_singleton_self _
    have heq := hpi.rp n hn p hp _ hmem (by show n.id.id.step - 1 = p.step; omega)
    have hidx : 1 - n.id.id.index = p.index := by rw [← heq]
    rw [hwn]
    omega

theorem agree_of_fixesMap {g : GPathM} (hli : LitInv (reqOfCnf φ) g) {n : PNodeM}
    (hn : n ∈ g.nodes) {m : NodeId} (hm : FixMap n m)
    (hexact : ∀ l ∈ reqOfCnf φ m, ∀ w ∈ n.owners, w.id.step = l.step → w.id = l)
    (heven : 0 ≤ m.step → m.step < litBlock φ → m.step % 2 = 0 → Agree n (m.step / 2) m.index)
    {vv : Int × Int} (hvv : vv ∈ fixesMap φ m) : Agree n vv.1 vv.2 := by
  obtain ⟨v, b⟩ := vv
  show Agree n v b
  unfold fixesMap at hvv
  by_cases h1 : m.step < litBlock φ
  · rw [if_pos h1] at hvv
    cases hvm : varVal φ m with
    | none =>
      rw [hvm] at hvv
      exact absurd hvv List.not_mem_nil
    | some vv' =>
      rw [hvm] at hvv
      have hvv' : (v, b) ∈ [vv'] := hvv
      have hve := List.mem_singleton.mp hvv'
      rw [← hve] at hvm
      obtain ⟨h0, hlt, hcase⟩ := varVal_spec φ m v b hvm
      rcases hcase with ⟨hs, hi⟩ | ⟨hs, hi⟩
      · have hag := heven h0 hlt (by omega)
        have hv : m.step / 2 = v := by omega
        rw [hv, hi] at hag
        exact hag
      · have hreq := reqOfCnf_neg φ m h0 hlt (by omega)
        have hmem : ({ step := m.step - 1, index := 1 - m.index } : NodeId) ∈ reqOfCnf φ m := by
          rw [hreq]; exact List.mem_singleton_self _
        have hvl : varVal φ { step := m.step - 1, index := 1 - m.index } = some (v, b) := by
          rw [varVal_even φ _ (by show 0 ≤ m.step - 1; omega)
            (by show m.step - 1 < litBlock φ; omega) (by show (m.step - 1) % 2 = 0; omega)]
          show some ((m.step - 1) / 2, 1 - m.index) = some (v, b)
          rw [show (m.step - 1) / 2 = v by omega, show 1 - m.index = b by omega]
        exact agree_of_req φ hli hn hm hexact hmem hvl
  · rw [if_neg h1] at hvv
    by_cases h2 : m.step = litBlock φ
    · rw [if_pos h2] at hvv
      exact absurd hvv List.not_mem_nil
    · rw [if_neg h2] at hvv
      obtain ⟨l, hl, hvl⟩ := List.mem_filterMap.mp hvv
      exact agree_of_req φ hli hn hm hexact hl hvl

/-- **A node agrees with every value its id fixes.** -/
theorem agree_of_fixes {g : GPathM} (hoos : SelfOwn.OOS g)
    (hoc : UnitPropagation.OwnedCompatible (reqOfCnf φ) g) (hrf : ReqFiltered (reqOfCnf φ) g)
    (hpi : ParentInv (reqOfCnf φ) g) (hli : LitInv (reqOfCnf φ) g)
    {n : PNodeM} (hn : n ∈ g.nodes) {vv : Int × Int} (hvv : vv ∈ fixes φ n.id) :
    Agree n vv.1 vv.2 := by
  unfold fixes at hvv
  rcases List.mem_append.mp hvv with h | h
  · exact agree_of_fixesMap φ hli hn (Or.inl rfl) (fun l hl w hw hs => hrf n hn l hl w hw hs)
      (fun h0 hlt hev => agree_self_value φ hoos hoc hn h0 hlt hev) h
  · cases hp : n.id.parent_id with
    | none =>
      rw [hp] at h
      exact absurd h List.not_mem_nil
    | some p =>
      rw [hp] at h
      exact agree_of_fixesMap φ hli hn (Or.inr hp)
        (fun l hl w hw hs => hpi.pr n hn p hp l hl w hw hs)
        (fun h0 hlt hev => agree_parent_value φ hoos hpi hn hp h0 hlt hev) h

-- ============================================================
-- S2
-- ============================================================

/-- **S2.** For the machine's sends, a global owner of the pinned state whose id contradicts a pin
is in the removal closure. -/
theorem idDies (hwf : WF φ)
    (g : GPathM) (hr : Reachable (reqOfCnf φ) g) (d : NodeId) (hd : d.step = g.current_step) :
    IdDies φ g d := by
  have hdist : ∀ x, ∀ r₁ ∈ reqOfCnf φ x, ∀ r₂ ∈ reqOfCnf φ x, r₁.step = r₂.step → r₁ = r₂ :=
    fun x r₁ h₁ r₂ h₂ hs => reqOfCnf_functional φ hwf x r₁ h₁ r₂ h₂ hs
  have hback : ∀ x, ∀ r ∈ reqOfCnf φ x, r.step < x.step :=
    fun x r h => reqOfCnf_backward φ hwf x r h
  have hnonneg : ∀ x, ∀ r ∈ reqOfCnf φ x, 0 ≤ r.step :=
    fun x r h => UnitPropagation.reqOfCnf_nonneg φ x r h
  have hoos := SelfOwn.OOS_reachable (reqOfCnf φ) g hr
  have hoc := UnitPropagation.OwnedCompatible_reachable (reqOfCnf φ) hback hnonneg g hr
  have hrf := L1 (reqOfCnf φ) hr
  have hpi := ParentInv_reachable (reqOfCnf φ) hback g hr
  have hli := LitInv_reachable (reqOfCnf φ) hback hnonneg hdist g hr
  have hgn := GownersNodes.GN_reachable (reqOfCnf φ) g hr
  intro q ⟨vv, hvv, r, hrr, pv, hpv, hsame, hne⟩ hq
  have hqg : q ∈ g.gowners := FabricAdd.gowners_foldl_sub (reqOfCnf φ d) g q hq
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g q).mp (hgn q hqg))
  have hnmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hnid : n.id = q := node?_id_eq g q n hn
  have hnP : ((reqOfCnf φ d).foldl filterRequire g).node? q = some n := by
    show ((reqOfCnf φ d).foldl filterRequire g).nodes.find? (fun x => x.id == q) = some n
    rw [foldl_filterRequire_nodes]
    exact hn
  have hag : Agree n vv.1 vv.2 :=
    agree_of_fixes φ hoos hoc hrf hpi hli hnmem (by rw [hnid]; exact hvv)
  obtain ⟨v, b⟩ := pv
  simp only at hsame hne
  obtain ⟨h0, _, hcase⟩ := varVal_spec φ r v b hpv
  have hrlt : r.step < ((reqOfCnf φ d).foldl filterRequire g).current_step := by
    rw [foldl_filterRequire_step]
    have := hback d r hrr
    omega
  refine Unsupported.noSupport q n hnP r.step h0 hrlt (fun w hw hwg => ?_)
  exfalso
  obtain ⟨hwo, hws⟩ := List.mem_filter.mp hw
  have hws' : w.id.step = r.step := beq_iff_eq.mp hws
  have hwr : w.id = r := FabricAdd.gowners_foldl_compat (reqOfCnf φ d) g w hwg r hrr hws'
  rcases hcase with ⟨hs, hi⟩ | ⟨hs, hi⟩
  · have hidx := hag.1 w hwo (by rw [hwr, hs, hsame])
    rw [hwr, hi] at hidx
    exact hne hidx
  · have hidx := hag.2 w hwo (by rw [hwr, hs, hsame])
    rw [hwr, hi] at hidx
    exact hne (by omega)

/-- **No zombies in every valid reachable state of the machine, from S1 alone.** -/
theorem noZombie_of_idSeparator_only (hwf : WF φ)
    (h : ∀ (g : GPathM) (d : NodeId), Reachable (reqOfCnf φ) g → d.step = g.current_step →
      NoZombies.NoZombie g → isValid (filterAll g (reqOfCnf φ d)) = true → IdSeparator φ g d)
    (g : GPathM) (hr : Reachable (reqOfCnf φ) g) (hv : isValid g = true) : NoZombies.NoZombie g :=
  noZombie_of_idSeparator φ
    (fun g d hr hd hnz hv => ⟨h g d hr hd hnz hv, idDies φ hwf g hr d hd⟩) g hr hv

/-- info: 'AbsSat.GraphPath.Model.IdDiesProof.idDies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms idDies

/-- info: 'AbsSat.GraphPath.Model.IdDiesProof.noZombie_of_idSeparator_only' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noZombie_of_idSeparator_only

end AbsSat.GraphPath.Model.IdDiesProof
