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
open AbsSatBin.GraphPath.Model.MapReachable
open AbsSatBin.GraphPath.Model.Kernel

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

/-- Witnesses below the new step that own `Q` and `R` in line `n+1` and the map nodes of `E` in line `n`. -/
def OldWit (n : Nat) (Q : List PathNodeId) (R E : List NodeId) : Prop :=
  ∀ l, 0 ≤ l → l ≤ (n : Int) → ∃ r, r.id.step = l ∧ Node φ (n + 1) r ∧ (∀ q ∈ Q, Owns φ (n + 1) r q) ∧
    (∀ m ∈ R, OwnsMap φ (n + 1) r m) ∧ ∀ m ∈ E, OwnsMap φ n r m

/-- **A clique with no member at the new step is passed by a partial solution when the map constraints
force an allowed window.** The extra constraints `E` sit below the new step and are owned by the
witnesses in line `n`. -/
theorem semConcl_low (hbd : Bounded φ) (n : Nat) (ih : SemCert φ n) (Q : List PathNodeId) (R E : List NodeId)
    (hQ : LClique φ (n + 1) Q) (hW : LWit φ (n + 1) Q R) (hnoz : ∀ q ∈ Q, q.id.step ≤ (n : Int))
    (hEs : ∀ m ∈ E, 0 ≤ m.step ∧ m.step ≤ (n : Int)) (hWE : OldWit φ n Q R E)
    (hok : ∀ a', (∀ m ∈ R, 0 ≤ m.step → m.step ≤ (n : Int) + 1 → selOfAssign φ a' m.step = m) →
      (∀ m ∈ E, selOfAssign φ a' m.step = m) → isProhibited φ (pidOfAssign φ a' ((n : Int) + 1)) = false) :
    SemConcl φ (n + 1) Q R := by
  let Ro := R.filter (fun m => decide (m.step ≤ (n : Int)))
  have memRo : ∀ m, m ∈ Ro ↔ m ∈ R ∧ m.step ≤ (n : Int) := by
    intro m; rw [List.mem_filter]; exact ⟨fun ⟨a, b⟩ => ⟨a, of_decide_eq_true b⟩, fun ⟨a, b⟩ => ⟨a, decide_eq_true b⟩⟩
  have hQo : LClique φ n Q := fun q hq s hs => owns_old φ hbd n q s (hQ q hq s hs) (hnoz q hq) (hnoz s hs)
  have witOld : ∀ (E' : List NodeId), (∀ r, r.id.step ≤ (n : Int) → (∀ m ∈ R, OwnsMap φ (n + 1) r m) →
      ∀ m ∈ E', OwnsMap φ n r m) → LWit φ n Q (Ro ++ E ++ E') := by
    intro E' hE' l h0 hl
    obtain ⟨r, hrs, hrn, hrQ, hrR, hrE⟩ := hWE l h0 hl
    refine ⟨r, hrs, node_old φ hbd n r hrn (by omega),
      fun q hq => owns_old φ hbd n r q (hrQ q hq) (by omega) (hnoz q hq), fun m hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨hmR, hms⟩ := (memRo m).mp hm
        exact ownsMap_old φ hbd n r m (hrR m hmR) (by omega) hms
      · exact hrE m hm
    · exact hE' r (by omega) hrR m hm
  obtain ⟨w, hws, hwn, _, hwR⟩ := hW ((n : Int) + 1) (by omega) (by push_cast; omega)
  have topR : ∀ m ∈ R, m.step = (n : Int) + 1 → m = w.id := by
    intro m hm hms
    obtain ⟨kv, hkv, nr, hnr, p, hp, hpm⟩ := hwR m hm
    have := top_owns_self φ hbd n w p ⟨kv, hkv, nr, hnr, hp⟩ hws (by rw [hpm]; exact hms)
    rw [← hpm, this]
  have hwm := (top_node φ hbd n w hwn hws).2.1
  have fin : ∀ a, PreSat φ a ((n : Int) + 1) → (∀ q ∈ Q, pidOfAssign φ a q.id.step = q) →
      (∀ m ∈ E, selOfAssign φ a m.step = m) →
      ∀ a', (∀ k, k ≤ (n : Int) → pidOfAssign φ a' k = pidOfAssign φ a k ∧ selOfAssign φ a' k = selOfAssign φ a k) →
      (∀ m ∈ R, 0 ≤ m.step → m.step ≤ (n : Int) + 1 → selOfAssign φ a' m.step = m) →
      SemConcl φ (n + 1) Q R := by
    intro a hpre hQa hEa a' hloc hR'
    have hE' : ∀ m ∈ E, selOfAssign φ a' m.step = m := fun m hm => by
      rw [(hloc _ (hEs m hm).2).2]; exact hEa m hm
    refine ⟨a', fun k hk => ?_, fun q hq => ?_, fun m hm h0 h1 => hR' m hm h0 (by push_cast at h1; exact h1)⟩
    · push_cast at hk
      rcases Int.lt_or_le k ((n : Int) + 1) with h | h
      · rw [(hloc k (by omega)).1]; exact hpre k h
      · rw [show k = (n : Int) + 1 by omega]; exact hok a' hR' hE'
    · rw [(hloc _ (hnoz q hq)).1]; exact hQa q hq
  have inE : ∀ (E' : List NodeId) m, m ∈ E → m ∈ Ro ++ E ++ E' :=
    fun E' m hm => List.mem_append_left _ (List.mem_append_right _ hm)
  cases hr : R.any (fun m => m.step == (n : Int) + 1) with
  | false =>
    have hW' := witOld [] (fun _ _ _ m hm => absurd hm List.not_mem_nil)
    obtain ⟨a, hpre, hQa, hRa⟩ := ih Q (Ro ++ E ++ []) hQo hW'
    refine fin a hpre hQa (fun m hm => hRa m (inE [] m hm) (hEs m hm).1 (hEs m hm).2) a
      (fun k _ => ⟨rfl, rfl⟩) (fun m hm h0 h1 => ?_)
    rcases Int.lt_or_le m.step ((n : Int) + 1) with h | h
    · exact hRa m (List.mem_append_left _ (List.mem_append_left _ ((memRo m).mpr ⟨hm, by omega⟩))) h0 (by omega)
    · exfalso; exact (List.any_eq_false.mp hr m hm) (beq_iff_eq.mpr (by omega))
  | true =>
    obtain ⟨m0, hm0R, hm0s'⟩ := List.any_eq_true.mp hr
    have hm0s : m0.step = (n : Int) + 1 := eq_of_beq hm0s'
    have hm0w : m0 = w.id := topR m0 hm0R hm0s
    let E' : List NodeId := (reqOf φ w.id).filter (fun r => decide (0 ≤ r.step))
    have hW' : LWit φ n Q (Ro ++ E ++ E') := witOld E' (fun r hrs hrR m hm => by
      obtain ⟨hmr, hm0⟩ := List.mem_filter.mp hm
      have := ownsMap_top φ hbd n r m0 (hrR m0 hm0R) hrs hm0s
      rw [hm0w] at this
      exact this m hmr (of_decide_eq_true hm0) (by have := reqOf_backward φ hbd w.id m hmr; omega))
    obtain ⟨a, hpre, hQa, hRa⟩ := ih Q (Ro ++ E ++ E') hQo hW'
    have hreq : ∀ req ∈ reqOf φ w.id, selOfAssign φ a req.step = req := by
      intro req hrq
      have h0 := reqOf_nonneg φ hbd w.id req hrq
      exact hRa req (List.mem_append_right _ (List.mem_filter.mpr ⟨hrq, decide_eq_true h0⟩)) h0
        (by have := reqOf_backward φ hbd w.id req hrq; omega)
    obtain ⟨a', hloc, htop⟩ := extend_to φ hbd n a w.id hwm hreq
    refine fin a hpre hQa (fun m hm => hRa m (inE E' m hm) (hEs m hm).1 (hEs m hm).2) a' hloc
      (fun m hm h0 h1 => ?_)
    rcases Int.lt_or_le m.step ((n : Int) + 1) with h | h
    · rw [(hloc _ (by omega)).2]
      exact hRa m (List.mem_append_left _ (List.mem_append_left _ ((memRo m).mpr ⟨hm, by omega⟩))) h0 (by omega)
    · have hms : m.step = (n : Int) + 1 := by omega
      rw [hms, htop, topR m hm hms]

-- ============================================================
-- The clause by keys
-- ============================================================

/-- The three ways a piece of `L3` fixes a true literal, as constraints below `L3`: `L2 = 1`, `L1 = 1`, or
the variable value that makes the third literal true (the requirement of `L3 = 1`). -/
def keyOpts (n : Nat) : List (List NodeId) :=
  [[⟨(n : Int), 1⟩], [⟨(n : Int) - 1, 1⟩], reqOf φ ⟨(n : Int) + 1, 1⟩]

/-- **The clause by keys**: at the third literal of a clause, a clique with witnesses and no member at
that step admits one of the three true literals, owned by witnesses at every step below. -/
def ClauseKey (n : Nat) : Prop :=
  isL3 φ ((n : Int) + 1) = true → ∀ Q R, LClique φ (n + 1) Q → LWit φ (n + 1) Q R →
    (∀ q ∈ Q, q.id.step ≤ (n : Int)) → ∃ E ∈ keyOpts φ n, OldWit φ n Q R E

/-- The facts a third literal step gives. -/
theorem l3_facts (n : Nat) (h : isL3 φ ((n : Int) + 1) = true) :
    1 ≤ n ∧ midFusion φ + 3 ≤ (n : Int) + 1 ∧ (n : Int) + 1 < fusionTop φ := by
  simp only [isL3, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, by omega, h2⟩
  have : (0 : Int) < midFusion φ := by simp only [midFusion]; omega
  omega

theorem one_le_of_isL3 (n : Nat) (h : isL3 φ ((n : Int) + 1) = true) : 1 ≤ n := (l3_facts φ n h).1

theorem mapNodes_l3 (n : Nat) (h : isL3 φ ((n : Int) + 1) = true) :
    mapNodes φ ((n : Int) + 1) = [⟨(n : Int) + 1, 0⟩, ⟨(n : Int) + 1, 1⟩] := by
  obtain ⟨_, h1, h2⟩ := l3_facts φ n h
  exact mapNodes_two φ _ (by omega) (by omega) h2

/-- **Each option forces an allowed window.** -/
theorem notProh_of_opt (hbd : Bounded φ) (a : Assign) (n : Nat) (hL3 : isL3 φ ((n : Int) + 1) = true)
    (E : List NodeId) (hE : E ∈ keyOpts φ n) (hsel : ∀ m ∈ E, selOfAssign φ a m.step = m) :
    isProhibited φ (pidOfAssign φ a ((n : Int) + 1)) = false := by
  have hn := one_le_of_isL3 φ n hL3
  simp only [keyOpts, List.mem_cons, List.not_mem_nil, or_false] at hE
  rcases hE with e | e | e
  · rw [e] at hsel
    exact notProh_of_true φ a n hn _ (by simp [trueLits]) (hsel _ List.mem_cons_self)
  · rw [e] at hsel
    exact notProh_of_true φ a n hn _ (by simp [trueLits]) (hsel _ List.mem_cons_self)
  · rw [e] at hsel
    obtain ⟨_, h1, _⟩ := l3_facts φ n hL3
    have htop : selOfAssign φ a ((n : Int) + 1) = ⟨(n : Int) + 1, 1⟩ :=
      selOfAssign_of_req φ hbd a _ _ (by omega) (by rw [mapNodes_l3 φ n hL3]; simp)
        (fun v hv e => by rw [e] at h1; simp only [midFusion, varStep] at h1; omega) hsel
    exact notProh_of_true φ a n hn ⟨(n : Int) + 1, 1⟩ (by simp [trueLits]) htop

theorem opt_steps (hbd : Bounded φ) (n : Nat) (hL3 : isL3 φ ((n : Int) + 1) = true) (E : List NodeId)
    (hE : E ∈ keyOpts φ n) : ∀ m ∈ E, 0 ≤ m.step ∧ m.step ≤ (n : Int) := by
  have hn := one_le_of_isL3 φ n hL3
  simp only [keyOpts, List.mem_cons, List.not_mem_nil, or_false] at hE
  intro m hm
  rcases hE with e | e | e <;> rw [e] at hm
  · rw [List.mem_singleton.mp hm]; constructor <;> simp only <;> omega
  · rw [List.mem_singleton.mp hm]; constructor <;> simp only <;> omega
  · exact ⟨reqOf_nonneg φ hbd _ m hm, by have := reqOf_backward φ hbd _ m hm; simp only at this; omega⟩

/-- **`ClauseKey ⇒ ClauseChoice`**: the true literal is one more map constraint, and it forces an allowed
window. -/
theorem clauseChoice_of_key (hbd : Bounded φ) (n : Nat) (ih : SemCert φ n) (h : ClauseKey φ n) :
    ClauseChoice φ n := by
  intro hL3 Q R hQ hW hlow
  obtain ⟨E, hE, hWE⟩ := h hL3 Q R hQ hW hlow
  exact semConcl_low φ hbd n ih Q R E hQ hW hlow (opt_steps φ hbd n hL3 E hE) hWE
    (fun a' _ hEa => notProh_of_opt φ hbd a' n hL3 E hE hEa)

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

-- ============================================================
-- A clique with a node at `L2`: its window chooses the literal
-- ============================================================

section mid
variable (hbd : Bounded φ) (n : Nat)
include hbd

/-- **A node that owns a node of `L2` owns its parent's map node** (in the source, the pair rule and the
parent link). -/
theorem owns_parent_map (r q : PathNodeId) (h : Owns φ (n + 1) r q) (hr : r.id.step ≤ (n : Int))
    (hqs : q.id.step = (n : Int)) (hn : 1 ≤ n) (b : NodeId) (hqb : q.parent_id = some b) : OwnsMap φ n r b := by
  obtain ⟨kv', hkv', nr, hnr, hqr⟩ := h
  rw [line_succ] at hkv'
  obtain ⟨kv, hkv, hd, hv, n', hn', hqn'⟩ := (src_pureAdvance φ (line φ n) kv' hkv').2 r nr hnr q hqr
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  have hk := c.pc.ker
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)
  have hFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  obtain ⟨nF, hnF, ho⟩ := upF_old φ kv.2 kv'.1 hdst c hv r n' hn' (by omega)
  have hqF := ho q hqn' (by omega)
  obtain ⟨nq, hnq⟩ := hk.isNode_owner r nF hnF q hqF
  obtain ⟨e, he, heq, hes⟩ := hk.pair r nF q nq hnF hnq hqF ((n : Int) - 1) (by omega) (by omega)
  obtain ⟨hepar, _⟩ := KernelSplit.parent_of_owner c.pc q nq hnq (by omega) e heq (by rw [hes, hqs])
  have hpm := c.rc.pmp nq (List.mem_of_find?_eq_some hnq) e hepar
  rw [node?_id_eq _ q nq hnq, hqb] at hpm
  obtain ⟨nJ, hnJ, hoJ, _, _⟩ := hb.node r nF hnF
  exact ⟨kv, hkv, nJ, hnJ, e, hoJ e he, Option.some.inj hpm⟩

/-- **The skipped window decides the piece.** A node that owns a node of `L2` with window `(L1, L2) = 00`
sits in a piece of key `L3 = 1`: in a piece of key `0` the only child of that node would be `000`, the
`UP` skips it, the review then removes the node, and the cut removes it from every table. So the node
owns the variable value that makes the third literal true. -/
theorem owns_mid00 (hL3 : isL3 φ ((n : Int) + 1) = true) (r q : PathNodeId) (h : Owns φ (n + 1) r q)
    (hr : r.id.step ≤ (n : Int)) (hqs : q.id.step = (n : Int)) (hq1 : ¬ q.id.index = 1)
    (hqp : ¬ q.parent_id = some ⟨(n : Int) - 1, 1⟩) :
    ∀ req ∈ reqOf φ ⟨(n : Int) + 1, 1⟩, OwnsMap φ n r req := by
  obtain ⟨hn, hmid, htop⟩ := l3_facts φ n hL3
  have hm0 : (0 : Int) < midFusion φ := by simp only [midFusion]; omega
  intro req hreq
  obtain ⟨kv', hkv', nr, hnr, hqr⟩ := h
  rw [line_succ] at hkv'
  obtain ⟨kv, hkv, hd, hv, n', hn', hqn'⟩ := (src_pureAdvance φ (line φ n) kv' hkv').2 r nr hnr q hqr
  obtain ⟨hok, hdst, hcs, hdm, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  have hk := c.pc.ker
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)
  have hFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  obtain ⟨nF, hnF, ho⟩ := upF_old φ kv.2 kv'.1 hdst c hv r n' hn' (by omega)
  obtain ⟨nJ, hnJ, hoJ, _, _⟩ := hb.node r nF hnF
  have hdmem : kv'.1 = ⟨(n : Int) + 1, 0⟩ ∨ kv'.1 = ⟨(n : Int) + 1, 1⟩ := by
    rw [mapNodes_l3 φ n hL3] at hdm
    rcases List.mem_cons.mp hdm with e | e
    · exact Or.inl e
    · exact Or.inr (List.mem_singleton.mp e)
  rcases hdmem with e0 | e1
  · -- key `0`: impossible
    exfalso
    have hqF := ho q hqn' (by omega)
    obtain ⟨nq, hnq⟩ := hk.isNode_owner r nF hnF q hqF
    have hmapF : NodesOnMap φ (filterAll kv.2 (reqOf φ kv'.1)) :=
      NodesOnMap_of_pruned φ (pruned_filterAll _ _) (nodesOnMap_of_mapReachable φ kv.2 hok.reach)
    have hqid : q.id = ⟨(n : Int), 0⟩ := by
      have := hmapF nq (List.mem_of_find?_eq_some hnq)
      rw [node?_id_eq _ q nq hnq, hqs, mapNodes_two φ _ (by omega) (by omega) (by omega)] at this
      rcases List.mem_cons.mp this with e | e
      · exact e
      · exact absurd (congrArg NodeId.index (List.mem_singleton.mp e)) hq1
    obtain ⟨e, _, heq, hes⟩ := hk.pair r nF q nq hnF hnq hqF ((n : Int) - 1) (by omega) (by omega)
    obtain ⟨hepar, ne, hne⟩ := KernelSplit.parent_of_owner c.pc q nq hnq (by omega) e heq (by rw [hes, hqs])
    have hpm := c.rc.pmp nq (List.mem_of_find?_eq_some hnq) e hepar
    rw [node?_id_eq _ q nq hnq] at hpm
    have hqpar : q.parent_id = some ⟨(n : Int) - 1, 0⟩ := by
      have := hmapF ne (List.mem_of_find?_eq_some hne)
      rw [node?_id_eq _ e ne hne, hes, mapNodes_two φ _ (by omega) (by omega) (by omega)] at this
      rcases List.mem_cons.mp this with e' | e'
      · rw [← hpm, e']
      · exact absurd (by rw [← hpm, List.mem_singleton.mp e']) hqp
    -- the only child of `q` at key `0` is the window `000`
    have hforb : isProhibited φ (shiftPid q kv'.1) = true := by
      unfold isProhibited shiftPid
      rw [e0, hqid, hqpar, show (n : Int) + 1 - 1 = n by omega, show (n : Int) + 1 - 2 = n - 1 by omega]
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨hL3, beq_iff_eq.mpr rfl⟩, beq_iff_eq.mpr rfl⟩, beq_iff_eq.mpr rfl⟩
    have hskip : skipsWindow (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 (isProhibited φ) = true := by
      unfold skipsWindow
      refine List.any_eq_true.mpr ⟨shiftPid q kv'.1, ?_, hforb⟩
      unfold shiftRowIds
      rw [if_pos (by rw [hFcs]; omega)]
      refine (mem_dedupPids _ _).mpr (List.mem_map_of_mem ?_)
      unfold newParents
      rw [if_pos (by rw [hFcs]; omega)]
      exact mem_line_of_node? _ q nq hnq _ (by rw [hFcs, hqs]; omega)
    have hG : upF φ kv.2 kv'.1 = review (addNode (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 "" (isProhibited φ)) := by
      show up (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 "" (isProhibited φ) = _
      unfold up; rw [if_pos hvF, if_pos hskip]
    have hvG : isValid (review (addNode (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 "" (isProhibited φ))) = true := by
      rw [← hG]; exact hv
    have hcsG : (review (addNode (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 "" (isProhibited φ))).current_step =
        (n : Int) + 2 := by
      have := (pruned_review (addNode (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 "" (isProhibited φ))).step_eq
      rw [addNode_current, hFcs] at this; omega
    have hcc := SymMachine.cutClosed_review _ hvG
    have hn'' := hn'
    rw [hG] at hn''
    have hqg := hcc n' (List.mem_of_find?_eq_some hn'') q hqn'
      (hasStepEntry_of_isValid _ hvG _ (by omega) (by rw [hcsG]; omega))
    -- `q` is a node of the reviewed state, so it owns a node at the new step
    have hreachG : Reachable (reqOf φ) (isProhibited φ) (upF φ kv.2 kv'.1) :=
      reachable_of_mapReachable φ hbd _ (MapReachable.up kv.2 kv'.1 "" hdst
        (by rw [mapNodes_step φ _ _ hdm]; exact hdm) hok.reach)
    rw [hG] at hreachG
    have cr := Reader.RCtx_reachable (reqOf φ) (isProhibited φ) _
      (Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreachG) hreachG
    obtain ⟨m, hm, hmid'⟩ := cr.gn q hqg
    have hnqG : (review (addNode (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 "" (isProhibited φ))).node? q = some m := by
      rw [← hmid']; exact node?_of_mem cr.nodup m hm
    have hval := ((isValidNode_iff _ m).mp (review_node_valid _ hvG q m hnqG)).1
    rw [hcsG] at hval
    obtain ⟨z, hz, hzs'⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp hval ((n : Int) + 1) (mem_intRange (by omega) (by omega)))
    have hzs : z.id.step = (n : Int) + 1 := eq_of_beq hzs'
    rw [← hG] at hnqG
    obtain ⟨nFq, hnFq, hznew, hqrow⟩ :=
      upF_owner_new φ kv.2 kv'.1 hdst c hv q m hnqG (by omega) z hz (by omega)
    rcases (mem_rowOwners_iff _ _ z q).mp hqrow with ⟨hu, _⟩ | he
    · obtain ⟨p, hp, np, hnp, hqp'⟩ := KernelReader.mem_unionOwnersOf_inv _ _ q hu
      have hps := (rowParent_node _ kv'.1 (by omega) hp).2
      rw [hFcs] at hps
      have hpq : p ∈ nFq.owners := hk.sym p np q nFq hnp hnFq hqp'
      obtain ⟨nJq, hnJq, hoJq, _, _⟩ := hb.node q nFq hnFq
      have hown : Owns φ n q p := ⟨kv, hkv, nJq, hnJq, hoJq p hpq⟩
      -- at its own step, a top node of line `n` owns only itself
      have hpeq : p = q := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        push_cast at hqs hps
        exact top_owns_self φ hbd k q p hown hqs (by omega)
      have hzq : shiftPid q kv'.1 = z := by rw [← hpeq]; exact eq_of_beq (List.mem_filter.mp hp).2
      have := not_forb_of_mem_newRowIds _ _ _ z hznew
      rw [← hzq, hforb] at this
      cases this
    · rw [he] at hqs; omega
  · -- key `1`: the requirement filter keeps the true value
    have hreq' : req ∈ reqOf φ kv'.1 := by rw [e1]; exact hreq
    have h0 := reqOf_nonneg φ hbd _ req hreq'
    have h1 : req.step < (filterAll kv.2 (reqOf φ kv'.1)).current_step := by
      have := reqOf_backward φ hbd kv'.1 req hreq'
      rw [hFcs]; rw [e1] at this; simp only at this; omega
    obtain ⟨x, hx, hxid⟩ := filt_owns_req φ c kv'.1 kv.2 rfl r nF hnF req hreq' h0 h1
    exact ⟨kv, hkv, nJ, hnJ, x, hoJ x hx, hxid⟩

/-- **`ClauseKey` for a clique with a node at `L2`**: the node's window chooses the literal. `L2 = 1`, or
`L1 = 1` (its parent), or `00`, and then the skipped window forces key `1`. -/
theorem clauseKey_mid (hL3 : isL3 φ ((n : Int) + 1) = true) (Q : List PathNodeId) (R : List NodeId)
    (hW : LWit φ (n + 1) Q R) (q : PathNodeId) (hqQ : q ∈ Q) (hqs : q.id.step = (n : Int)) :
    ∃ E ∈ keyOpts φ n, OldWit φ n Q R E := by
  have hn := one_le_of_isL3 φ n hL3
  have base : ∀ E, (∀ r, r.id.step ≤ (n : Int) → Owns φ (n + 1) r q → ∀ m ∈ E, OwnsMap φ n r m) →
      OldWit φ n Q R E := by
    intro E hE l h0 hl
    obtain ⟨r, hrs, hrn, hrQ, hrR⟩ := hW l h0 (by push_cast; omega)
    exact ⟨r, hrs, hrn, hrQ, hrR, hE r (by omega) (hrQ q hqQ)⟩
  by_cases h1 : q.id.index = 1
  · refine ⟨[⟨(n : Int), 1⟩], by simp [keyOpts], base _ (fun r hr hrq m hm => ?_)⟩
    rw [List.mem_singleton.mp hm]
    obtain ⟨kv, hkv, nJ, hnJ, hq⟩ := owns_old φ hbd n r q hrq hr (by omega)
    have e : q.id = ⟨(n : Int), 1⟩ := by rw [← hqs, ← h1]
    exact ⟨kv, hkv, nJ, hnJ, q, hq, e⟩
  · by_cases h2 : q.parent_id = some ⟨(n : Int) - 1, 1⟩
    · refine ⟨[⟨(n : Int) - 1, 1⟩], by simp [keyOpts], base _ (fun r hr hrq m hm => ?_)⟩
      rw [List.mem_singleton.mp hm]
      exact owns_parent_map φ hbd n r q hrq hr hqs hn _ h2
    · exact ⟨_, by simp [keyOpts], base _ (fun r hr hrq m hm => owns_mid00 φ hbd n hL3 r q hrq hr hqs h1 h2 m hm)⟩

end mid

/-- info: 'AbsSatBin.GraphPath.Model.ClauseKey.clauseKey_mid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms clauseKey_mid

/-- info: 'AbsSatBin.GraphPath.Model.ClauseKey.semConcl_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms semConcl_low

/-- info: 'AbsSatBin.GraphPath.Model.ClauseKey.readerVerdictW_iff_of_clauseKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_clauseKey

end AbsSatBin.GraphPath.Model.ClauseKey
