-- lean_project/AbsSat/GraphPath/Model/CertifiedVerdict.lean
import AbsSat.GraphPath.Model.Oracle
import AbsSat.GraphPath.Model.Certificate

/-!
# The certified verdict

The machine answers SAT when its last line has states (`is_satisfiable (run_pure φ)`), and whether
that answer is right is open (`Oracle.answer_matches_oracle_iff`). This module reads the answer off
the represented set instead: SAT when some state of the last line has a selection — one node per
step — that the checker `Certificate.isCert` accepts.

* `certifiedVerdict_sound` — a positive certified verdict means the formula is satisfiable
  (`isCert_sound` and `L7.sat_of_inhabited`);
* `certifiedVerdict_complete` — a satisfiable formula gets a positive certified verdict: the
  assignment's path is represented (`PartialPaths.satisfiable_iff_Phi_nonempty`), its chain is among
  the enumerated selections (`mem_selections`) and the checker accepts it (`isCert_of_chain`);
* `certifiedVerdict_iff_oracle` — **the certified verdict is the brute-force oracle's**, with no
  hypothesis.

The enumeration `L6Search.selections` is the product of the lines, so this verdict costs as much
as the brute force in the worst case. What it shows is that the machine's representation, read
with a checked certificate, decides satisfiability exactly; the cost of the reading is a separate
question (a reader that never backtracks, measured in v101 as the forward-checking construction).
-/

namespace AbsSat.GraphPath.Model.CertifiedVerdict

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PartialPaths
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.Certificate
open L6Search (selections ownersOfB isGoodChain)
open AbsSat.SatMachine.PureSatMachine

/-- **The certified verdict**: some state of the last line has a selection the checker accepts. -/
def certifiedVerdict (φ : Cnf) : Bool :=
  (pureRun φ).any (fun kv => (selections kv.2).any (isCert kv.2))

-- ============================================================
-- The enumeration contains every chain
-- ============================================================

theorem mem_foldl_selections (g : GPathM) (sel : Int → PathNodeId) :
    ∀ (ks : List Int) (acc : List (List PathNodeId)) (pre : List PathNodeId), pre ∈ acc →
      (∀ k ∈ ks, sel k ∈ (g.line k).map (·.id)) →
      pre ++ ks.map sel ∈ ks.foldl
        (fun acc k => acc.flatMap (fun pre => ((g.line k).map (·.id)).map (fun c => pre ++ [c])))
        acc := by
  intro ks
  induction ks with
  | nil => intro acc pre hpre _; simpa using hpre
  | cons k rest ih =>
    intro acc pre hpre hks
    simp only [List.foldl_cons, List.map_cons]
    have h := ih (acc.flatMap (fun pre => ((g.line k).map (·.id)).map (fun c => pre ++ [c])))
      (pre ++ [sel k])
      (List.mem_flatMap.mpr ⟨pre, hpre, List.mem_map.mpr ⟨sel k, hks k List.mem_cons_self, rfl⟩⟩)
      (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
    simpa [List.append_assoc] using h

/-- **Every selection that picks a node of each line is enumerated.** -/
theorem mem_selections (g : GPathM) (sel : Int → PathNodeId)
    (h : ∀ k ∈ intRange 0 (g.current_step - 1), sel k ∈ (g.line k).map (·.id)) :
    (intRange 0 (g.current_step - 1)).map sel ∈ selections g := by
  have hm := mem_foldl_selections g sel _ [[]] [] (List.mem_singleton.mpr rfl) h
  rw [List.nil_append] at hm
  exact hm

-- ============================================================
-- The checker accepts every chain
-- ============================================================

theorem length_chainList (c : Int) (hc : 0 ≤ c) (sel : Int → PathNodeId) :
    ((intRange 0 (c - 1)).map sel).length = c.toNat := by
  simp only [intRange, List.length_map, List.length_range]
  omega

theorem getElem?_chainList (c : Int) (hc : 0 ≤ c) (sel : Int → PathNodeId) (i : Nat)
    (hi : i < c.toNat) : ((intRange 0 (c - 1)).map sel)[i]? = some (sel (i : Int)) := by
  have hi' : i < (c - 1 - 0 + 1).toNat := by omega
  simp only [intRange, List.getElem?_map, List.getElem?_range hi', Option.map_some]
  simp

theorem stepsOk_of_chain (g : GPathM) (sel : Int → PathNodeId) (hcs : 0 ≤ g.current_step)
    (hchain : IsChain g sel) : stepsOk g ((intRange 0 (g.current_step - 1)).map sel) = true := by
  have hlen := length_chainList g.current_step hcs sel
  have hget := getElem?_chainList g.current_step hcs sel
  unfold stepsOk
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < g.current_step.toNat := by rw [← hlen]; exact List.mem_range.mp hi
  rw [hget i hi']
  obtain ⟨hs, hstep⟩ := hchain.1 (i : Int) (by omega) (by omega)
  show ((g.node? (sel (i : Int))).isSome && (sel (i : Int)).id.step == (i : Int)) = true
  rw [hs, hstep, Bool.true_and]
  exact beq_iff_eq.mpr rfl

theorem linksOk_of_chain (g : GPathM) (sel : Int → PathNodeId) (hcs : 0 ≤ g.current_step)
    (hchain : IsChain g sel) : linksOk g ((intRange 0 (g.current_step - 1)).map sel) = true := by
  have hlen := length_chainList g.current_step hcs sel
  have hget := getElem?_chainList g.current_step hcs sel
  unfold linksOk
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < g.current_step.toNat := by rw [← hlen]; exact List.mem_range.mp hi
  split
  · next hlt =>
    have hlt' : i + 1 < g.current_step.toNat := by rw [← hlen]; exact hlt
    rw [hget i hi', hget (i + 1) hlt']
    have hcast : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by omega
    obtain ⟨hs, _⟩ := hchain.1 ((i : Int) + 1) (by omega) (by omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
    have hpar := hchain.2 (i : Int) (by omega) (by omega)
    rw [hn] at hpar
    show (match g.node? (sel ((i + 1 : Nat) : Int)) with
      | some n => n.parents.contains (sel (i : Int))
      | none => false) = true
    rw [hcast, hn]
    exact List.elem_eq_true_of_mem hpar
  · rfl

theorem ownedOk_of_chain (g : GPathM) (sel : Int → PathNodeId) (hcs : 0 ≤ g.current_step)
    (howned : PairwiseOwned g sel) :
    ownedOk g ((intRange 0 (g.current_step - 1)).map sel) = true := by
  have hlen := length_chainList g.current_step hcs sel
  have hget := getElem?_chainList g.current_step hcs sel
  unfold ownedOk
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  have hi' : i < g.current_step.toNat := by rw [← hlen]; exact List.mem_range.mp hi
  have hj' : j < g.current_step.toNat := by rw [← hlen]; exact List.mem_range.mp hj
  split
  · rfl
  · next hne =>
    have hij : i ≠ j := fun e => hne (beq_iff_eq.mpr e)
    rw [hget i hi', hget j hj']
    have ho := howned (i : Int) (j : Int) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hmem : sel (i : Int) ∈ ownersOf g (sel (j : Int)) := (List.mem_filter.mp ho).1
    exact List.elem_eq_true_of_mem hmem

/-- **The checker accepts every chain of the state**, read as a list. -/
theorem isCert_of_chain (g : GPathM) (sel : Int → PathNodeId) (hcs : 0 ≤ g.current_step)
    (hchain : IsChain g sel) (howned : PairwiseOwned g sel) :
    isCert g ((intRange 0 (g.current_step - 1)).map sel) = true := by
  unfold isCert
  rw [Bool.and_eq_true, isGoodChain_eq, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨beq_iff_eq.mpr (length_chainList g.current_step hcs sel),
    ⟨stepsOk_of_chain g sel hcs hchain, linksOk_of_chain g sel hcs hchain⟩,
    ownedOk_of_chain g sel hcs howned⟩

-- ============================================================
-- The verdict
-- ============================================================

/-- **A positive certified verdict means the formula is satisfiable.** -/
theorem certifiedVerdict_sound (φ : Cnf) (hwf : WF φ) (h : certifiedVerdict φ = true) :
    Satisfiable φ := by
  unfold certifiedVerdict at h
  obtain ⟨kv, hkv, hsel⟩ := List.any_eq_true.mp h
  obtain ⟨L, _, hcert⟩ := List.any_eq_true.mp hsel
  have hcount : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hrun : pureRun φ = lineAt φ (stepCount φ - 1).toNat := rfl
  have hcast : (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
  rw [hrun] at hkv
  have hok := (lineAt_ok φ _).2 kv hkv
  have hcs : kv.2.current_step = stepCount φ := by rw [hok.step, hcast]; omega
  exact L7.sat_of_inhabited φ hwf kv.2 hok.reach hcs (Inhabited_of_isCert kv.2 L hcert)

/-- **A satisfiable formula gets a positive certified verdict.** -/
theorem certifiedVerdict_complete (φ : Cnf) (hwf : WF φ) (h : Satisfiable φ) :
    certifiedVerdict φ = true := by
  obtain ⟨p, kv, hkv, sel, hchain, howned, _⟩ := (satisfiable_iff_Phi_nonempty φ hwf).mp h
  have hcount : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hrun : pureRun φ = lineAt φ (stepCount φ - 1).toNat := rfl
  have hkv' : kv ∈ lineAt φ (stepCount φ - 1).toNat := by rw [← hrun]; exact hkv
  have hok := (lineAt_ok φ _).2 kv hkv'
  have hpos : 0 ≤ kv.2.current_step := by rw [hok.step]; omega
  unfold certifiedVerdict
  refine List.any_eq_true.mpr ⟨kv, hkv, List.any_eq_true.mpr ⟨_, mem_selections kv.2 sel ?_,
    isCert_of_chain kv.2 sel hpos hchain howned⟩⟩
  intro k hk
  have h0 := mem_intRange_lower hk
  have h1 := mem_intRange_upper hk
  obtain ⟨hs, hstep⟩ := hchain.1 k h0 (by omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
  exact mem_line_of_node? kv.2 (sel k) n hn k hstep

/-- **The certified verdict is the brute-force oracle's.** -/
theorem certifiedVerdict_iff_oracle (φ : Cnf) (hwf : WF φ) :
    certifiedVerdict φ = true ↔ bruteForceSat φ ≠ [] := by
  rw [bruteForceSat_ne_nil_iff φ hwf]
  exact ⟨certifiedVerdict_sound φ hwf, certifiedVerdict_complete φ hwf⟩

/-- A positive certified verdict implies the machine's own answer is SAT. -/
theorem machine_sat_of_certifiedVerdict (φ : Cnf) (hwf : WF φ) (h : certifiedVerdict φ = true) :
    is_satisfiable (run_pure φ) = true :=
  AbsSat.SatMachine.PureProofs.completeness_pure φ hwf (certifiedVerdict_sound φ hwf h)

/-- **The machine's answer agrees with the certified verdict iff a non-empty last line always
represents some path** — the same open statement as `Oracle.answer_matches_oracle_iff`. -/
theorem machine_matches_certified_iff (φ : Cnf) (hwf : WF φ) :
    (is_satisfiable (run_pure φ) = true → certifiedVerdict φ = true) ↔
      (pureRun φ ≠ [] → ∃ p, Phi (pureRun φ) p) := by
  rw [certifiedVerdict_iff_oracle φ hwf]
  exact Oracle.answer_matches_oracle_iff φ hwf

/-- info: 'AbsSat.GraphPath.Model.CertifiedVerdict.isCert_of_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isCert_of_chain

/-- info: 'AbsSat.GraphPath.Model.CertifiedVerdict.certifiedVerdict_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certifiedVerdict_sound

/-- info: 'AbsSat.GraphPath.Model.CertifiedVerdict.certifiedVerdict_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certifiedVerdict_complete

/-- info: 'AbsSat.GraphPath.Model.CertifiedVerdict.certifiedVerdict_iff_oracle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certifiedVerdict_iff_oracle

/-- info: 'AbsSat.GraphPath.Model.CertifiedVerdict.machine_matches_certified_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms machine_matches_certified_iff

end AbsSat.GraphPath.Model.CertifiedVerdict
