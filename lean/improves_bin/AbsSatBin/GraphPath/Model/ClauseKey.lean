-- lean/improves_bin/AbsSatBin/GraphPath/Model/ClauseKey.lean
import AbsSatBin.GraphPath.Model.LineSem

/-!
# The clause by keys: the witnesses choose a true literal

At the third literal `L3` of a clause (step `n+1`) the machine builds the seven allowed windows and never
the window `000`. It does so with three kinds of pieces, one per way the clause is satisfied:

* key `L3 = 1`: the requirement filter keeps only the variable value that makes the third literal true;
  nothing is skipped;
* key `L3 = 0` from the state with `L2 = 1`: every window `(·, 1, 0)` is allowed, nothing is skipped;
* key `L3 = 0` from the state with `L2 = 0`: the window `000` is skipped and the review keeps only what goes
  through `L1 = 1`, the window `(1, 0, 0)`.

Each piece fixes a **true literal**: every node of it owns a path node of `⟨n+1, 1⟩`, of `⟨n, 1⟩` or of
`⟨n-1, 1⟩` (`trueLits`). A partial solution through any of these map nodes has an allowed window at `L3`
(`notProh_of_true`).

* **`semConcl_low`**: a clique with no member at the new step, with witnesses, is passed by a partial
  solution as soon as every assignment that honours the map constraints has an allowed window. It is the
  step of `LineSem.semCert_succ` without the clause.
* **`ClauseKey`**: at `L3`, a clique with witnesses admits a true literal `t` that the witnesses can own too.
* **`clauseChoice_of_key`**: `ClauseKey ⇒ ClauseChoice`, hence the reader (`readerVerdictW_iff_of_clauseKey`).
-/

namespace AbsSatBin.GraphPath.Model.ClauseKey

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.PrefixCarry
open AbsSatBin.GraphPath.Model.LineSem

variable (φ : Cnf)

/-- The three true literals of the clause whose `L3` is step `n+1`. -/
def trueLits (n : Nat) : List NodeId := [⟨(n : Int) + 1, 1⟩, ⟨(n : Int), 1⟩, ⟨(n : Int) - 1, 1⟩]

theorem trueLits_step (n : Nat) (t : NodeId) (ht : t ∈ trueLits n) :
    (n : Int) - 1 ≤ t.step ∧ t.step ≤ (n : Int) + 1 := by
  simp only [trueLits, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with e | e | e <;> rw [e] <;> constructor <;> simp only <;> omega

/-- **A true literal gives an allowed window.** -/
theorem notProh_of_true (a : Assign) (n : Nat) (hn : 1 ≤ n) (t : NodeId) (ht : t ∈ trueLits n)
    (hsel : selOfAssign φ a t.step = t) : isProhibited φ (pidOfAssign φ a ((n : Int) + 1)) = false := by
  have e1 : (n : Int) + 1 - 1 = n := by omega
  have e2 : (n : Int) + 1 - 2 = n - 1 := by omega
  unfold isProhibited pidOfAssign
  rw [if_pos (by omega), if_pos (by omega), e1, e2]
  simp only [trueLits, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with e | e | e <;> rw [e] at hsel <;> simp only at hsel <;> rw [hsel] <;> simp

-- ============================================================
-- The step without the clause
-- ============================================================

/-- **A clique with no member at the new step is passed by a partial solution when the map constraints
force an allowed window.** -/
theorem semConcl_low (hbd : Bounded φ) (n : Nat) (ih : SemCert φ n) (Q : List PathNodeId) (R : List NodeId)
    (hQ : LClique φ (n + 1) Q) (hW : LWit φ (n + 1) Q R) (hnoz : ∀ q ∈ Q, q.id.step ≤ (n : Int))
    (hok : ∀ a', (∀ m ∈ R, 0 ≤ m.step → m.step ≤ (n : Int) + 1 → selOfAssign φ a' m.step = m) →
      isProhibited φ (pidOfAssign φ a' ((n : Int) + 1)) = false) :
    SemConcl φ (n + 1) Q R := by
  let Ro := R.filter (fun m => decide (m.step ≤ (n : Int)))
  have memRo : ∀ m, m ∈ Ro ↔ m ∈ R ∧ m.step ≤ (n : Int) := by
    intro m; rw [List.mem_filter]; exact ⟨fun ⟨a, b⟩ => ⟨a, of_decide_eq_true b⟩, fun ⟨a, b⟩ => ⟨a, decide_eq_true b⟩⟩
  have hQo : LClique φ n Q := fun q hq s hs => owns_old φ hbd n q s (hQ q hq s hs) (hnoz q hq) (hnoz s hs)
  have witOld : ∀ (E : List NodeId), (∀ r, r.id.step ≤ (n : Int) → (∀ m ∈ R, OwnsMap φ (n + 1) r m) →
      ∀ m ∈ E, OwnsMap φ n r m) → LWit φ n Q (Ro ++ E) := by
    intro E hE l h0 hl
    obtain ⟨r, hrs, hrn, hrQ, hrR⟩ := hW l h0 (by push_cast; omega)
    refine ⟨r, hrs, node_old φ hbd n r hrn (by omega),
      fun q hq => owns_old φ hbd n r q (hrQ q hq) (by omega) (hnoz q hq), fun m hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨hmR, hms⟩ := (memRo m).mp hm
      exact ownsMap_old φ hbd n r m (hrR m hmR) (by omega) hms
    · exact hE r (by omega) hrR m hm
  obtain ⟨w, hws, hwn, _, hwR⟩ := hW ((n : Int) + 1) (by omega) (by push_cast; omega)
  have topR : ∀ m ∈ R, m.step = (n : Int) + 1 → m = w.id := by
    intro m hm hms
    obtain ⟨kv, hkv, nr, hnr, p, hp, hpm⟩ := hwR m hm
    have := top_owns_self φ hbd n w p ⟨kv, hkv, nr, hnr, hp⟩ hws (by rw [hpm]; exact hms)
    rw [← hpm, this]
  have hwm := (top_node φ hbd n w hwn hws).2.1
  have fin : ∀ a, PreSat φ a ((n : Int) + 1) → (∀ q ∈ Q, pidOfAssign φ a q.id.step = q) →
      ∀ a', (∀ k, k ≤ (n : Int) → pidOfAssign φ a' k = pidOfAssign φ a k ∧ selOfAssign φ a' k = selOfAssign φ a k) →
      (∀ m ∈ R, 0 ≤ m.step → m.step ≤ (n : Int) + 1 → selOfAssign φ a' m.step = m) →
      SemConcl φ (n + 1) Q R := by
    intro a hpre hQa a' hloc hR'
    refine ⟨a', fun k hk => ?_, fun q hq => ?_, fun m hm h0 h1 => hR' m hm h0 (by push_cast at h1; exact h1)⟩
    · push_cast at hk
      rcases Int.lt_or_le k ((n : Int) + 1) with h | h
      · rw [(hloc k (by omega)).1]; exact hpre k h
      · rw [show k = (n : Int) + 1 by omega]; exact hok a' hR'
    · rw [(hloc _ (hnoz q hq)).1]; exact hQa q hq
  cases hr : R.any (fun m => m.step == (n : Int) + 1) with
  | false =>
    have hW' := witOld [] (fun _ _ _ m hm => absurd hm List.not_mem_nil)
    rw [List.append_nil] at hW'
    obtain ⟨a, hpre, hQa, hRa⟩ := ih Q Ro hQo hW'
    refine fin a hpre hQa a (fun k _ => ⟨rfl, rfl⟩) (fun m hm h0 h1 => ?_)
    rcases Int.lt_or_le m.step ((n : Int) + 1) with h | h
    · exact hRa m ((memRo m).mpr ⟨hm, by omega⟩) h0 (by omega)
    · exfalso; exact (List.any_eq_false.mp hr m hm) (beq_iff_eq.mpr (by omega))
  | true =>
    obtain ⟨m0, hm0R, hm0s'⟩ := List.any_eq_true.mp hr
    have hm0s : m0.step = (n : Int) + 1 := eq_of_beq hm0s'
    have hm0w : m0 = w.id := topR m0 hm0R hm0s
    let E : List NodeId := (reqOf φ w.id).filter (fun r => decide (0 ≤ r.step))
    have hW' : LWit φ n Q (Ro ++ E) := witOld E (fun r hrs hrR m hm => by
      obtain ⟨hmr, hm0⟩ := List.mem_filter.mp hm
      have := ownsMap_top φ hbd n r m0 (hrR m0 hm0R) hrs hm0s
      rw [hm0w] at this
      exact this m hmr (of_decide_eq_true hm0) (by have := reqOf_backward φ hbd w.id m hmr; omega))
    obtain ⟨a, hpre, hQa, hRa⟩ := ih Q (Ro ++ E) hQo hW'
    have hreq : ∀ req ∈ reqOf φ w.id, selOfAssign φ a req.step = req := by
      intro req hrq
      have h0 := reqOf_nonneg φ hbd w.id req hrq
      exact hRa req (List.mem_append_right _ (List.mem_filter.mpr ⟨hrq, decide_eq_true h0⟩)) h0
        (by have := reqOf_backward φ hbd w.id req hrq; omega)
    obtain ⟨a', hloc, htop⟩ := extend_to φ hbd n a w.id hwm hreq
    refine fin a hpre hQa a' hloc (fun m hm h0 h1 => ?_)
    rcases Int.lt_or_le m.step ((n : Int) + 1) with h | h
    · rw [(hloc _ (by omega)).2]
      exact hRa m (List.mem_append_left _ ((memRo m).mpr ⟨hm, by omega⟩)) h0 (by omega)
    · have hms : m.step = (n : Int) + 1 := by omega
      rw [hms, htop, topR m hm hms]

-- ============================================================
-- The clause by keys
-- ============================================================

/-- **The clause by keys**: at the third literal of a clause, a clique with witnesses and no member at
that step admits a true literal of the clause that the witnesses own as well. -/
def ClauseKey (n : Nat) : Prop :=
  isL3 φ ((n : Int) + 1) = true → ∀ Q R, LClique φ (n + 1) Q → LWit φ (n + 1) Q R →
    (∀ q ∈ Q, q.id.step ≤ (n : Int)) → ∃ t ∈ trueLits n, LWit φ (n + 1) Q (t :: R)

/-- A third literal sits above the first clause step, so `1 ≤ n`. -/
theorem one_le_of_isL3 (n : Nat) (h : isL3 φ ((n : Int) + 1) = true) : 1 ≤ n := by
  simp only [isL3, Bool.and_eq_true, decide_eq_true_eq] at h
  have := h.1.1
  simp only [midFusion] at this
  omega

/-- **`ClauseKey ⇒ ClauseChoice`**: the true literal is one more map constraint, and it forces an allowed
window. -/
theorem clauseChoice_of_key (hbd : Bounded φ) (n : Nat) (ih : SemCert φ n) (h : ClauseKey φ n) :
    ClauseChoice φ n := by
  intro hL3 Q R hQ hW hlow
  obtain ⟨t, ht, hWt⟩ := h hL3 Q R hQ hW hlow
  have hn := one_le_of_isL3 φ n hL3
  have hts := trueLits_step n t ht
  obtain ⟨a, hpre, hQa, hRa⟩ := semConcl_low φ hbd n ih Q (t :: R) hQ hWt hlow
    (fun a' hR' => notProh_of_true φ a' n hn t ht (hR' t List.mem_cons_self (by omega) hts.2))
  exact ⟨a, hpre, hQa, fun m hm => hRa m (List.mem_cons_of_mem _ hm)⟩

/-- **The reader decides `φ` when every third literal of a clause satisfies `ClauseKey`.** -/
theorem readerVerdictW_iff_of_clauseKey (hbd : Bounded φ)
    (hkey : ∀ n : Nat, (n : Int) + 1 < stepCount φ → ClauseKey φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  have hsem : ∀ n : Nat, (n : Int) < stepCount φ → SemCert φ n := by
    intro n
    induction n with
    | zero => intro _; exact semCert_zero φ
    | succ m ih =>
      intro hm
      push_cast at hm
      have ihm := ih (by omega)
      exact semCert_succ φ hbd m ihm (clauseChoice_of_key φ hbd m ihm (hkey m hm))
  refine CertFix.readerVerdictW_iff_of_certLink φ hbd (fun kv hkv hv => ?_)
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hN : (((stepCount φ - 1).toNat : Nat) : Int) < stepCount φ := by omega
  have hmap := mapCert_start φ hbd _ hN (hsem _ hN) kv hkv hv
  have c := AmbTriCore.aCtx_readPins φ hbd kv hkv [] _ OtherBitSem.ReadPins.start hv
  exact CertInvariant.certLink_of_certClique c (MapCert.certClique_of_mapCert hmap)

/-- info: 'AbsSatBin.GraphPath.Model.ClauseKey.semConcl_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms semConcl_low

/-- info: 'AbsSatBin.GraphPath.Model.ClauseKey.readerVerdictW_iff_of_clauseKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_clauseKey

end AbsSatBin.GraphPath.Model.ClauseKey
