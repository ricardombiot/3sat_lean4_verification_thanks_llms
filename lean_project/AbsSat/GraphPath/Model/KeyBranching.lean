-- lean_project/AbsSat/GraphPath/Model/KeyBranching.lean
import AbsSat.GraphPath.Model.DriverPropagation

/-!
# The driver branches by key rows

Traced on a constructed case (seed 1001, clauses `a∨b∨c`, `a∨¬b∨c`, `¬a∨b∨c`,
`¬a∨¬b∨c`): the value `c = false` does not disappear through a deduction inside the
review. Every state still holding it dies at a send where the destination row
requires, for some variable, the opposite of what the state's own **key row**
requires — the pin alone already empties a step. The strength is in the driver
keeping one state per key row, not in the review.

* `KeyPure` — a state of the driver's line keeps, at each literal step its key row
  requires, only the required node among its global owners. It holds for every
  entry of `pureAdvance` (`pureAdvance_keyPure`): the send pins the key's
  requirements and joins only merge states with the same key.
* `sendTo_of_key_conflict` — if the destination row requires the opposite value of
  a variable its source state's key row requires, the send is dropped. The key
  refutes one value, the destination's pin the other, and
  `DriverPropagation.sendTo_of_refuted` closes it.
* `pureAdvance_drops_key_conflict` — the same, for every state of the driver's next
  line in the clause block.
-/

namespace AbsSat.GraphPath.Model.KeyBranching

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.LocalContradiction
open AbsSat.GraphPath.Model.UnitPropagation
open AbsSat.GraphPath.Model.DriverPropagation

/-- At each step its key row requires, a state's global owners carry only the
required node. -/
def KeyPure (φ : Cnf) (kv : NodeId × GPathM) : Prop :=
  ∀ q ∈ kv.2.gowners, ∀ r ∈ reqOfCnf φ kv.1, q.id.step = r.step → q.id = r

theorem keyPure_sent (φ : Cnf) (hwf : WF φ) (g : GPathM) (d : NodeId)
    (hval : isValid (upFiltering g (reqOfCnf φ d) d "") = true) :
    KeyPure φ (d, upFiltering g (reqOfCnf φ d) d "") := by
  have hfv := isValid_filterAll_of_sent φ g d hval
  have hshape : upFiltering g (reqOfCnf φ d) d "" = addNode (filterAll g (reqOfCnf φ d)) d "" := by
    simp only [upFiltering, GPathM.up, hfv, if_pos]
  intro q hq r hr hs
  change q ∈ (upFiltering g (reqOfCnf φ d) d "").gowners at hq
  change r ∈ reqOfCnf φ d at hr
  rw [hshape] at hq
  have hq' : q ∈ (filterAll g (reqOfCnf φ d)).gowners ++ [newPid (filterAll g (reqOfCnf φ d)) d] := hq
  rcases List.mem_append.mp hq' with hq | hq
  · have hq0 := (pruned_review ((reqOfCnf φ d).foldl filterRequire g)).gowners_sub q hq
    rcases (mem_foldl_filterRequire (reqOfCnf φ d) g q hq0).2 r hr with h | h
    · exact absurd hs h
    · exact h
  · rcases List.mem_singleton.mp hq with rfl
    exfalso
    have hback := reqOfCnf_backward φ hwf d r hr
    have hid : (newPid (filterAll g (reqOfCnf φ d)) d).id.step = d.step := rfl
    omega

theorem keyPure_doJoin (φ : Cnf) (key : NodeId) (e g : GPathM)
    (he : KeyPure φ (key, e)) (hg : KeyPure φ (key, g)) : KeyPure φ (key, doJoin e g) := by
  intro q hq r hr hs
  change q ∈ (doJoin e g).gowners at hq
  change r ∈ reqOfCnf φ key at hr
  unfold doJoin at hq
  split at hq
  · rw [GownersNodes.join_gowners] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact he q hq r hr hs
    · exact hg q (List.mem_filter.mp hq).1 r hr hs
  · exact he q hq r hr hs

theorem mem_insertPure_cases (acc : PureLine) (key : NodeId) (g : GPathM)
    (e : NodeId × GPathM) (he : e ∈ insertPure acc key g) :
    e ∈ acc ∨ e = (key, g) ∨ ∃ x ∈ acc, x.1 = key ∧ e = (key, doJoin x.2 g) := by
  cases hf : acc.find? (fun x => x.1 == key) with
  | none =>
    simp only [insertPure, hf] at he
    rcases List.mem_append.mp he with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (List.mem_singleton.mp h))
  | some e0 =>
    have he0 : e0 ∈ acc := List.mem_of_find?_eq_some hf
    have hk0 : e0.1 = key :=
      eq_of_beq (List.find?_some (p := fun x : NodeId × GPathM => x.1 == key) hf)
    simp only [insertPure, hf] at he
    obtain ⟨x, hx, hEq⟩ := List.mem_map.mp he
    cases hb : x.1 == key with
    | true =>
      exact Or.inr (Or.inr ⟨e0, he0, hk0, by rw [← hEq]; simp only [hb]; rfl⟩)
    | false =>
      have hex : e = x := by rw [← hEq]; simp only [hb]; rfl
      rw [hex]
      exact Or.inl hx

theorem keyPure_insertPure (φ : Cnf) (acc : PureLine) (key : NodeId) (g : GPathM)
    (hacc : ∀ x ∈ acc, KeyPure φ x) (hg : KeyPure φ (key, g)) :
    ∀ e ∈ insertPure acc key g, KeyPure φ e := by
  intro e he
  rcases mem_insertPure_cases acc key g e he with h | h | ⟨x, hx, hxk, h⟩
  · exact hacc e h
  · rw [h]; exact hg
  · rw [h]
    have hx' : KeyPure φ (key, x.2) := by
      have hpx := hacc x hx
      rw [← hxk]
      exact hpx
    exact keyPure_doJoin φ key x.2 g hx' hg

theorem keyPure_sendTo (φ : Cnf) (hwf : WF φ) (g : GPathM) (acc : PureLine) (d : NodeId)
    (hacc : ∀ x ∈ acc, KeyPure φ x) : ∀ e ∈ sendTo φ g acc d, KeyPure φ e := by
  intro e he
  simp only [sendTo] at he
  split at he
  · next hval => exact keyPure_insertPure φ acc d _ hacc (keyPure_sent φ hwf g d hval) e he
  · exact hacc e he

theorem keyPure_sendAll (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM) (acc : PureLine)
    (hacc : ∀ x ∈ acc, KeyPure φ x) : ∀ e ∈ sendAll φ kv acc, KeyPure φ e := by
  simp only [sendAll]
  have main : ∀ (l : List NodeId) (acc : PureLine), (∀ x ∈ acc, KeyPure φ x) →
      ∀ e ∈ l.foldl (sendTo φ kv.2) acc, KeyPure φ e := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons x xs ih =>
      intro acc h
      simp only [List.foldl_cons]
      exact ih _ (keyPure_sendTo φ hwf kv.2 acc x h)
  exact main _ acc hacc

/-- **Every state the driver parks carries its key row.** -/
theorem pureAdvance_keyPure (φ : Cnf) (hwf : WF φ) (line : PureLine) :
    ∀ e ∈ pureAdvance φ line, KeyPure φ e := by
  simp only [pureAdvance]
  have main : ∀ (l : PureLine) (acc : PureLine), (∀ x ∈ acc, KeyPure φ x) →
      ∀ e ∈ l.foldl (fun next kv => sendAll φ kv next) acc, KeyPure φ e := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons x xs ih =>
      intro acc h
      simp only [List.foldl_cons]
      exact ih _ (keyPure_sendAll φ hwf x acc h)
  exact main line [] (fun x hx => absurd hx List.not_mem_nil)

/-- The row `x` requires `x_v = b`: directly at the variable's step, or through its
negation step. -/
def ReqValue (φ : Cnf) (x : NodeId) (v : Nat) (b : Int) : Prop :=
  (⟨varStep v, b⟩ : NodeId) ∈ reqOfCnf φ x ∨ (⟨negStep v, 1 - b⟩ : NodeId) ∈ reqOfCnf φ x

/-- The key row refutes the opposite value. -/
theorem refuted_of_key (φ : Cnf) (kv : NodeId × GPathM) (hpure : KeyPure φ kv) (d : NodeId)
    (v : Nat) (hv : v < φ.nVars) (b : Int)
    (hkey : ReqValue φ kv.1 v b) :
    Refuted φ (Present ((reqOfCnf φ d).foldl filterRequire kv.2)) kv.2.current_step v (1 - b) := by
  refine Refuted.base v (1 - b) hv ?_
  rintro ⟨⟨q1, hq1, hq1id⟩, ⟨q2, hq2, hq2id⟩⟩
  have hq1g := (mem_foldl_filterRequire (reqOfCnf φ d) kv.2 q1 hq1).1
  have hq2g := (mem_foldl_filterRequire (reqOfCnf φ d) kv.2 q2 hq2).1
  rcases hkey with h | h
  · have heq := hpure q1 hq1g _ h (by rw [hq1id])
    rw [hq1id] at heq
    have hidx := congrArg NodeId.index heq
    simp only at hidx
    omega
  · have heq := hpure q2 hq2g _ h (by rw [hq2id])
    rw [hq2id] at heq
    have hidx := congrArg NodeId.index heq
    simp only at hidx
    omega

/-- The destination's pin refutes the key's value. -/
theorem refuted_of_dest (φ : Cnf) (g : GPathM) (d : NodeId) (v : Nat) (hv : v < φ.nVars)
    (b : Int) (hdest : ReqValue φ d v (1 - b)) :
    Refuted φ (Present ((reqOfCnf φ d).foldl filterRequire g)) g.current_step v b := by
  refine Refuted.base v b hv ?_
  rintro ⟨⟨q1, hq1, hq1id⟩, ⟨q2, hq2, hq2id⟩⟩
  rcases hdest with h | h
  · exact excluded_of_pin g (reqOfCnf φ d) ⟨varStep v, 1 - b⟩ ⟨varStep v, b⟩ h rfl
      (by intro heq; have hidx := congrArg NodeId.index heq; simp only at hidx; omega)
      q1 hq1 hq1id
  · exact excluded_of_pin g (reqOfCnf φ d) ⟨negStep v, 1 - (1 - b)⟩ ⟨negStep v, 1 - b⟩ h rfl
      (by intro heq; have hidx := congrArg NodeId.index heq; simp only at hidx; omega)
      q2 hq2 hq2id

/-- **A row that contradicts the key is never extended.** If the destination row
requires the opposite value of a variable that the source state's key row requires,
the send leaves the next line unchanged. -/
theorem sendTo_of_key_conflict (φ : Cnf) (hwf : WF φ) (k : Int) (kv : NodeId × GPathM)
    (hkv : StateOk φ k kv) (hk : litBlock φ ≤ k) (hpure : KeyPure φ kv)
    (d : NodeId) (v : Nat) (hv : v < φ.nVars) (b : Int) (hb : b = 0 ∨ b = 1)
    (hkey : ReqValue φ kv.1 v b) (hdest : ReqValue φ d v (1 - b)) (next : PureLine) :
    sendTo φ kv.2 next d = next := by
  apply sendTo_of_refuted φ hwf kv.2 hkv.reach (by rw [hkv.step]; omega) next d
  have r1 := refuted_of_key φ kv hpure d v hv b hkey
  have r0 := refuted_of_dest φ kv.2 d v hv b hdest
  show UPConflict _ _ _
  left
  rcases hb with rfl | rfl
  · exact ⟨v, r0, by simpa using r1⟩
  · exact ⟨v, by simpa using r1, r0⟩

/-- **The driver branches by key rows.** In the clause block, no state of the
driver's next line is extended to a row that contradicts its own key row on some
variable. -/
theorem pureAdvance_drops_key_conflict (φ : Cnf) (hwf : WF φ) (k : Int) (line : PureLine)
    (hl : LineOk φ k line) (hk : litBlock φ ≤ k)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureAdvance φ line)
    (d : NodeId) (v : Nat) (hv : v < φ.nVars) (b : Int) (hb : b = 0 ∨ b = 1)
    (hkey : ReqValue φ kv.1 v b) (hdest : ReqValue φ d v (1 - b)) (next : PureLine) :
    sendTo φ kv.2 next d = next :=
  sendTo_of_key_conflict φ hwf (k + 1) kv ((LineOk_pureAdvance φ k line hl).2 kv hkv) (by omega)
    (pureAdvance_keyPure φ hwf line kv hkv) d v hv b hb hkey hdest next

/-- info: 'AbsSat.GraphPath.Model.KeyBranching.pureAdvance_keyPure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureAdvance_keyPure

/-- info: 'AbsSat.GraphPath.Model.KeyBranching.sendTo_of_key_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sendTo_of_key_conflict

/-- info: 'AbsSat.GraphPath.Model.KeyBranching.pureAdvance_drops_key_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureAdvance_drops_key_conflict

end AbsSat.GraphPath.Model.KeyBranching
