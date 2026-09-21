-- lean_project/AbsSat/GraphPath/Model/PinHistory.lean
import AbsSat.GraphPath.Model.ClauseReview

/-!
# Pinning is a requirement the history already applied

A pin at a literal step removes every partial path through the other value. When the run stood on that
step, the variable was the **key**: the branch of the pin (`BranchRun.branchRun`, the run that keeps only
the keys agreeing with the pins) never built the other value at all. So a clause row's three pins are
three requirements, and the branch that applied them when their variables were keys is again a run of the
machine.

* `branchLine φ P m` — the line of the branch of `P` at step `m`; with no pins it is the machine's line
  (`branchLine_nil`). It keeps the machine's invariants (`branchLine_inv`) and sits inside the branch of
  any fewer pins, key by key (`branchLine_emb`).
* **`pinIds_branch`** (no hypothesis) — every node of a branch state at a pinned step *is* the pin, so
  every path of the branch takes the pinned values (`chain_pins`).
* **`PinCommutes`** — the history property: at a send of a branch to a clause row, every entry (towards
  a literal) of the pinned, reviewed state is an entry of the branch that also carries the row's pins,
  under the same key.
* **`branch_sound`** — under it, every state of every branch keeps the invariant, by induction on the step
  for all branches at once; **`sat_of_pinCommutes`** — the verdict.
-/

namespace AbsSat.GraphPath.Model.PinHistory

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit insertPure)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv LineInv_init LineInv_pureAdvanceW)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)
open AbsSat.GraphPath.Model.BranchRun (restrictLine branchSteps restrictLine_nil branchSteps_nil)
open AbsSat.GraphPath.Model.BranchLines (sent sendToW_eq advance_inv insert_src key_unique LineEmb
  lineEmb_advance lineInv_restrict embedded_refl)
open AbsSat.GraphPath.Model.EmbeddedSupport (Mem Rel Embedded)
open AbsSat.GraphPath.Model.Exactness (Realizes)
open AbsSat.GraphPath.Model.RunInhabited (SoundAt LitStep LineSoundAt lineSoundAt_insertPure lineSoundAt_init)
open AbsSat.GraphPath.Model.BranchCompat (pinOneByOne)
open AbsSat.GraphPath.Model.BranchRun (embedded_filterAllAgg embedded_of_pruned isValid_of_embedded)
open AbsSat.GraphPath.Model.SendDistrib (embedded_trans mem_of_embedded)
open AbsSat.GraphPath.Model.AnchoredSurvive (SMP_filterAllAgg)

variable (φ : Cnf)

-- ============================================================
-- The branch lines
-- ============================================================

/-- The line of the branch of `P` at step `m`. -/
def branchLine (P : List NodeId) (m : Nat) : PureLine :=
  branchSteps φ P m 0 (restrictLine P 0 (pureInit φ))

theorem branchSteps_succ (P : List NodeId) : ∀ (n : Nat) (k : Int) (L : PureLine),
    branchSteps φ P (n + 1) k L = restrictLine P (k + (n : Int) + 1) (pureAdvanceW φ (branchSteps φ P n k L)) := by
  intro n
  induction n with
  | zero => intro k L; simp [branchSteps]
  | succ n ih =>
    intro k L
    show branchSteps φ P (n + 1) (k + 1) _ = _
    rw [ih]
    rw [show k + 1 + (n : Int) + 1 = k + ((n + 1 : Nat) : Int) + 1 by omega]
    rfl

theorem branchLine_succ (P : List NodeId) (m : Nat) :
    branchLine φ P (m + 1) = restrictLine P ((m : Int) + 1) (pureAdvanceW φ (branchLine φ P m)) := by
  unfold branchLine; rw [branchSteps_succ]; rw [show (0 : Int) + (m : Int) + 1 = (m : Int) + 1 by omega]

theorem branchLine_nil (m : Nat) : branchLine φ [] m = pureStepsW φ m (pureInit φ) := by
  unfold branchLine; rw [restrictLine_nil, branchSteps_nil]

theorem branchLine_inv (hwf : WF φ) (P : List NodeId) : ∀ m : Nat, LineInv φ m (branchLine φ P m) := by
  intro m
  induction m with
  | zero => exact lineInv_restrict φ P 0 0 _ (LineInv_init φ hwf)
  | succ m ih =>
    rw [branchLine_succ]
    have := LineInv_pureAdvanceW φ hwf m _ ih
    exact lineInv_restrict φ P _ _ _ (by rw [show ((m + 1 : Nat) : Int) = (m : Int) + 1 by omega]; exact this)

theorem mem_restrict {P : List NodeId} {k : Int} {L : PureLine} {kv : NodeId × GPathM}
    (h : kv ∈ restrictLine P k L) : kv ∈ L ∧ ∀ r ∈ P, r.step ≠ k ∨ kv.1 = r := by
  obtain ⟨hL, hall⟩ := List.mem_filter.mp h
  refine ⟨hL, fun r hr => ?_⟩
  have := List.all_eq_true.mp hall r hr
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
  rcases this with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **More pins, a smaller branch**: the branch of `P ++ R` sits inside the branch of `P`, key by key. -/
theorem branchLine_emb (hwf : WF φ) (P R : List NodeId) :
    ∀ m : Nat, LineEmb (branchLine φ (P ++ R) m) (branchLine φ P m) := by
  have pass : ∀ (k : Int) (L : PureLine) (kv : NodeId × GPathM), kv ∈ L →
      (∀ r ∈ P ++ R, r.step ≠ k ∨ kv.1 = r) → kv ∈ restrictLine P k L := by
    intro k L kv hL hk
    refine List.mem_filter.mpr ⟨hL, List.all_eq_true.mpr fun r hr => ?_⟩
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    exact hk r (List.mem_append_left _ hr)
  intro m
  induction m with
  | zero =>
    intro kv hkv
    obtain ⟨hL, hk⟩ := mem_restrict hkv
    exact ⟨kv, pass 0 _ kv hL hk, rfl, embedded_refl kv.2⟩
  | succ m ih =>
    rw [branchLine_succ, branchLine_succ]
    intro kv hkv
    obtain ⟨hL, hk⟩ := mem_restrict hkv
    obtain ⟨kv', hkv', hkey, he⟩ := lineEmb_advance φ hwf m _ _ (branchLine_inv φ hwf _ m)
      (branchLine_inv φ hwf _ m) ih kv hL
    exact ⟨kv', pass _ _ kv' hkv' (by rw [hkey]; exact hk), hkey, he⟩

-- ============================================================
-- A branch state only has the pinned values at the pinned steps
-- ============================================================

/-- At the pinned steps below `s`, every node is the pin. -/
def PinIdsBelow (P : List NodeId) (s : Int) (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, n.id.id.step < s → ∀ r ∈ P, n.id.id.step = r.step → n.id.id = r

/-- A send keeps the pins below its new step: the old nodes keep their ids, the new one sits above. -/
theorem pinIds_sent (P : List NodeId) (k : Int) (kv : NodeId × GPathM)
    (hp : PinIdsBelow P (k + 1) kv.2) (d : NodeId) (hd : d.step = k + 1) (hval : isValid (sent φ kv.2 d) = true) :
    PinIdsBelow P (k + 1) (sent φ kv.2 d) := by
  have hvF := ClauseReview.valid_pinned φ kv.2 d hval
  have heq : sent φ kv.2 d = addNode (ClauseReview.pinnedAt φ kv.2 d) d "" := by
    rw [ClauseReview.sent_eq]; unfold GPathM.up; rw [hvF]; rfl
  have hpr : Pruned kv.2 (ClauseReview.pinnedAt φ kv.2 d) :=
    Pruned.trans (ConservationCore.pruned_filterWeakAll _ _) (pruned_filterAllAgg _ _)
  intro n hn hs r hr hrs
  rw [heq, addNode_nodes] at hn
  rcases List.mem_append.mp hn with h1 | h2
  · obtain ⟨n0, hn0, rfl⟩ := List.mem_map.mp h1
    rw [upMap_id] at hs hrs ⊢
    obtain ⟨n1, hn1, hid, _, _⟩ := hpr.nodes_derived n0 hn0
    rw [hid] at hs hrs ⊢
    exact hp n1 hn1 hs r hr hrs
  · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff _ d "" n).mp h2
    rw [rowNode_id, mapId_of_mem_newRowIds _ d pid hpid, hd] at hs
    omega

theorem pinIds_doJoin (P : List NodeId) (s : Int) (g₁ g₂ : GPathM) (h₁ : PinIdsBelow P s g₁)
    (h₂ : PinIdsBelow P s g₂) : PinIdsBelow P s (doJoin g₁ g₂) := by
  unfold doJoin
  split
  · intro n hn hs r hr hrs
    rcases BranchRun.mem_join_nodes_src hn with ⟨a, ha, hid, _, _⟩ | h
    · rw [hid] at hs hrs ⊢; exact h₁ a ha hs r hr hrs
    · exact h₂ n h hs r hr hrs
  · exact h₁

theorem dstep_of (m : Int) (kv : NodeId × GPathM) (hsok : StateOkF φ m kv) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index) : d.step = m + 1 := by
  have hkey : kv.1.step = m := mapNodes_step φ m kv.1 hsok.onMap
  have hmk : (⟨m, kv.1.index⟩ : NodeId) ∈ mapNodes φ m := by
    have hid : (⟨m, kv.1.index⟩ : NodeId) = kv.1 := by
      cases hkv1 : kv.1 with
      | mk sp ix => rw [hkv1] at hkey; simp only at hkey ⊢; rw [hkey]
    rw [hid]; exact hsok.onMap
  exact mapNodes_step φ (m + 1) d (mapSons_subset φ m kv.1.index hmk d (by rw [← hkey]; exact hd))

/-- The line advance keeps the pins below the new step. -/
theorem pinIds_advance (P : List NodeId) (m : Int) (L : PureLine) (hl : LineInv φ m L)
    (hp : ∀ kv ∈ L, PinIdsBelow P (m + 1) kv.2) :
    ∀ kv ∈ pureAdvanceW φ L, PinIdsBelow P (m + 1) kv.2 := by
  refine advance_inv φ (fun acc => ∀ kv ∈ acc, PinIdsBelow P (m + 1) kv.2) L ?_ (fun _ h => absurd h List.not_mem_nil)
  intro kv hkv d hd acc hacc
  rw [sendToW_eq]
  split
  · next hv =>
    have hs := pinIds_sent φ P m kv (hp kv hkv) d (dstep_of φ m kv (hl.1.2 kv hkv) d hd) hv
    rintro ⟨d', B⟩ hB
    rcases insert_src acc d _ d' B hB with ⟨_, rfl | ⟨e, he, rfl⟩⟩ | ⟨hB', _⟩
    · exact hs
    · exact pinIds_doJoin P _ _ _ (hacc _ he) hs
    · exact hacc _ hB'
  · exact hacc

/-- **The key closes the pins at its own step**: the top nodes carry the key, which agrees with the pins. -/
theorem pinIds_close (P : List NodeId) (k : Int) (kv : NodeId × GPathM) (hsok : StateOkF φ k kv)
    (hm : MInv φ kv.2) (hk : ∀ r ∈ P, r.step ≠ k ∨ kv.1 = r) (hp : PinIdsBelow P k kv.2) :
    PinIdsBelow P (k + 1) kv.2 := by
  intro n hn hs r hr hrs
  by_cases hlt : n.id.id.step < k
  · exact hp n hn hlt r hr hrs
  · have htl := hm.tl n hn (by rw [hsok.step]; omega)
    rw [hsok.par] at htl
    rcases hk r hr with h | h
    · omega
    · rw [← h]; exact Option.some.inj htl

/-- **Every node of a branch state at a pinned step is the pin** (no hypothesis). -/
theorem pinIds_branch (hwf : WF φ) (P : List NodeId) :
    ∀ (m : Nat), ∀ kv ∈ branchLine φ P m, PinIdsBelow P ((m : Int) + 1) kv.2 := by
  intro m
  induction m with
  | zero =>
    intro kv hkv
    have hl := branchLine_inv φ hwf P 0
    have hkv' := hkv
    unfold branchLine at hkv'
    obtain ⟨_, hk⟩ := mem_restrict (show kv ∈ restrictLine P 0 (pureInit φ) from hkv')
    refine pinIds_close φ P 0 kv (hl.1.2 kv hkv) (hl.2 kv hkv) hk ?_
    intro n hn hs
    have := (hl.2 kv hkv).rctx.snn n hn
    omega
  | succ m ih =>
    intro kv hkv
    have hl := branchLine_inv φ hwf P (m + 1)
    have hkv' := hkv
    rw [branchLine_succ] at hkv'
    obtain ⟨hA, hk⟩ := mem_restrict hkv'
    have hadv := pinIds_advance φ P m _ (branchLine_inv φ hwf P m) ih kv hA
    have hsok := hl.1.2 kv hkv
    rw [show ((m + 1 : Nat) : Int) = (m : Int) + 1 by omega] at hsok ⊢
    exact pinIds_close φ P _ kv hsok (hl.2 kv hkv) hk hadv

/-- **Every path of a branch takes the pinned values.** -/
theorem chain_pins (P : List NodeId) (g : GPathM) (hp : PinIdsBelow P g.current_step g)
    (sel : Int → PathNodeId) (hsc : ChainSound g sel) :
    ∀ r ∈ P, 0 ≤ r.step → r.step < g.current_step → (sel r.step).id = r := by
  intro r hr h0 h1
  obtain ⟨hsome, hstep⟩ := hsc.chain.1.1 r.step h0 h1
  obtain ⟨nt, hnt⟩ := Option.isSome_iff_exists.mp hsome
  have hid := node?_id_eq _ _ nt hnt
  rw [← hid] at hstep ⊢
  exact hp nt (List.mem_of_find?_eq_some hnt) (by rw [hstep]; exact h1) r hr hstep

-- ============================================================
-- The history property, and the verdict
-- ============================================================

/-- **Pinning commutes with the history.** At a send of the branch of `P` to a clause row `d`, every entry
towards a literal that survives `d`'s pins and the review is an entry of the branch of `P` and `d`'s pins,
under the same key. -/
def PinCommutes : Prop :=
  ∀ (P : List NodeId) (m : Nat) (kv : NodeId × GPathM), kv ∈ branchLine φ P m → (m : Int) + 2 ≤ stepCount φ →
    ∀ d ∈ mapSons φ kv.1.step kv.1.index, litBlock φ < d.step → reqOfCnf φ d ≠ [] →
      isValid (filterAllAgg kv.2 (reqOfCnf φ d)) = true →
      ∀ x q, Rel (filterAllAgg kv.2 (reqOfCnf φ d)) x q → LitStep φ q.id.step →
        ∃ kv' ∈ branchLine φ (P ++ reqOfCnf φ d) m, kv'.1 = kv.1 ∧ Rel kv'.2 x q

/-- **Every state of every branch keeps the invariant**, under `PinCommutes`: by induction on the step,
for all branches at once. At a clause row the entry lies on a path of the branch with the row's pins
(one step down in the induction), that path sits in the state sent from, and it takes the pins, so it
survives them. -/
theorem branch_sound (hwf : WF φ) (hPC : PinCommutes φ) :
    ∀ (m : Nat) (P : List NodeId), (m : Int) + 1 ≤ stepCount φ → LineSoundAt φ (branchLine φ P m) := by
  intro m
  induction m with
  | zero =>
    intro P _ kv hkv
    unfold branchLine at hkv
    exact lineSoundAt_init φ kv (mem_restrict (show kv ∈ restrictLine P 0 (pureInit φ) from hkv)).1
  | succ m ih =>
    intro P hm kv hkv
    rw [branchLine_succ] at hkv
    refine advance_inv φ (LineSoundAt φ) _ ?_ (fun _ h => absurd h List.not_mem_nil) kv (mem_restrict hkv).1
    intro kv hkv d hd acc hacc
    rw [sendToW_eq]
    split
    · next hval =>
      refine lineSoundAt_insertPure φ acc d _ hacc ?_
      have hl := branchLine_inv φ hwf P m
      have hsok : StateOkF φ m kv := hl.1.2 kv hkv
      have hmkv : MInv φ kv.2 := hl.2 kv hkv
      have ht : SoundAt (LitStep φ) kv.2 := ih P (by omega) kv hkv
      have hdstep := dstep_of φ m kv hsok d hd
      refine RunInhabited.soundAt_sent_of φ m kv hsok hmkv d hd hval (fun hvW => ?_)
      refine WeakNoop.soundAt_weak_send φ hwf m kv hsok hmkv d hd hvW (fun hvA => ?_)
      rcases reqOfCnf_shape φ d with h | h | ⟨c, _, hlb, h⟩
      · rw [h] at hvA ⊢; exact RunInhabited.soundAt_review _ kv.2 hmkv.rctx.nodup ht
      · rw [h] at hvA ⊢
        exact ClausePins.soundAt_pin_top φ m kv hsok hmkv ht _ (by show d.step - 1 = (m : Int); omega) hvA
      · -- the clause row: the entry is an entry of the branch with the row's pins
        have hne : reqOfCnf φ d ≠ [] := by rw [h]; exact List.cons_ne_nil _ _
        have hRA : ReadableAgg (filterAllAgg kv.2 (reqOfCnf φ d)) := ⟨kv.2, _, hmkv.rctx, rfl⟩
        have ctxA := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRA) hvA
        have rcA := RCtx_of_readableAgg _ hRA
        have hprA : Pruned kv.2 (filterAllAgg kv.2 (reqOfCnf φ d)) := pruned_filterAllAgg _ _
        intro x n hx hx0 hx1 q hq0 hq1 hL hqn
        have hqm : Mem (filterAllAgg kv.2 (reqOfCnf φ d)) q := by
          obtain ⟨nq, hnq, hnqid⟩ := ctxA.gn q (ctxA.ownGow x n hx q hqn hq0 hq1)
          exact ⟨nq, by rw [← hnqid]; exact node?_of_mem rcA.nodup nq hnq⟩
        obtain ⟨kv', hkv', hkey, n', hn', hqn', _⟩ :=
          hPC P m kv hkv (by omega) d hd hlb hne hvA x q ⟨n, hx, hqn, hqm⟩ hL
        have hl' := branchLine_inv φ hwf (P ++ reqOfCnf φ d) m
        have hs' : kv'.2.current_step = (m : Int) + 1 := (hl'.1.2 kv' hkv').step
        have hsA : (filterAllAgg kv.2 (reqOfCnf φ d)).current_step = (m : Int) + 1 := by
          rw [hprA.step_eq, hsok.step]
        obtain ⟨sel, hsc, hsx, hsq⟩ := ih (P ++ reqOfCnf φ d) (by omega) kv' hkv' x n' hn' hx0
          (by rw [hs', ← hsA]; exact hx1) q hq0 (by rw [hs', ← hsA]; exact hq1) hL hqn'
        -- the branch state sits inside the state sent from
        obtain ⟨kv'', hkv'', hkey', he⟩ := branchLine_emb φ hwf P (reqOfCnf φ d) m kv' hkv'
        have h1 : (kv.1, kv''.2) ∈ branchLine φ P m := by rw [← hkey, ← hkey']; exact hkv''
        have hkk : kv''.2 = kv.2 := key_unique _ hl.1.1 kv.1 _ _ h1 hkv
        rw [hkk] at he
        have hsc' := SeqPin.chainSound_of_embedded he hmkv.smp sel hsc
        -- and its path takes the row's pins
        have hpins := chain_pins (P ++ reqOfCnf φ d) kv'.2
          (by rw [hs']; exact pinIds_branch φ hwf _ m kv' hkv') sel hsc
        exact ⟨sel, ChainSound_filterAllAgg kv.2 (reqOfCnf φ d) sel hsc' (fun r hr h0 h1 =>
          hpins r (List.mem_append_right _ hr) h0 (by rw [hs', ← hsok.step]; exact h1)), hsx, hsq⟩
    · exact hacc

/-- **The verdict from the history property.** -/
theorem sat_of_pinCommutes (hwf : WF φ) (hPC : PinCommutes φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ := by
  have hpos := ConservationCore.stepCount_pos φ
  have hL := branch_sound φ hwf hPC (stepCount φ - 1).toNat [] (by omega)
  rw [branchLine_nil] at hL
  exact RunInhabited.sat_of_lineSound φ hwf hL kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.PinHistory.sat_of_pinCommutes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pinCommutes

-- ============================================================
-- One pin at a time
-- ============================================================

/-- **The history property, one pin at a time.** Pinning one literal value in a state of a branch, once
every variable is built, gives a state inside the state with the same key of the branch that also carries
that pin. -/
def PinCommutes1 : Prop :=
  ∀ (P : List NodeId) (m : Nat) (kv : NodeId × GPathM), kv ∈ branchLine φ P m →
    litBlock φ < (m : Int) + 1 → ∀ r : NodeId, 0 ≤ r.step → r.step < litBlock φ →
      isValid (filterAllAgg kv.2 [r]) = true →
      ∃ kv' ∈ branchLine φ (P ++ [r]) m, kv'.1 = kv.1 ∧ Embedded (filterAllAgg kv.2 [r]) kv'.2

/-- The facts a state needs to be pinned and reviewed inside another one. -/
structure Good (X : GPathM) : Prop where
  rc : Reader.RCtx X
  smp : Sons.SMP X
  pms : Sons.PMS X
  sn : Sons.SN X

theorem good_of_minv {g : GPathM} (h : MInv φ g) : Good g := ⟨h.rctx, h.smp, h.pms, h.sn⟩

theorem good_filterAllAgg {X : GPathM} (h : Good X) (reqs : List NodeId) : Good (filterAllAgg X reqs) :=
  ⟨RCtx_of_readableAgg _ ⟨X, reqs, h.rc, rfl⟩, SMP_filterAllAgg X h.smp h.rc.shape.notroot reqs,
    AggInvariants.PMS_filterAllAgg X reqs h.pms, AggInvariants.SN_filterAllAgg X reqs h.sn⟩

theorem foldl_filterRequire_nodes' : ∀ (l : List NodeId) (g : GPathM), (l.foldl filterRequire g).nodes = g.nodes := by
  intro l
  induction l with
  | nil => intro g; rfl
  | cons r rs ih => intro g; exact ih (filterRequire g r)

/-- **Pinning is monotone**: a state inside another stays inside after the same pin and review. -/
theorem embedded_pin (X Y : GPathM) (reqs : List NodeId) (e : Embedded X Y) (hX : Good X) (hY : Good Y)
    (hv : isValid (filterAllAgg X reqs) = true) : Embedded (filterAllAgg X reqs) (filterAllAgg Y reqs) := by
  have hg := good_filterAllAgg hX reqs
  refine embedded_filterAllAgg X Y reqs e hX.rc.nodup ⟨X, reqs, hX.rc, rfl⟩ hv hg.smp hg.pms hg.sn ?_ ?_
  · unfold Sons.SMP; rw [foldl_filterRequire_nodes']; exact hY.smp
  · unfold Parents.NotRoot; rw [foldl_filterRequire_nodes']; exact hY.rc.shape.notroot

theorem pruned_pinOneByOne : ∀ (rs : List NodeId) (X : GPathM), Pruned X (pinOneByOne X rs) := by
  intro rs
  induction rs with
  | nil => intro X; exact Pruned.refl X
  | cons r rest ih => intro X; exact Pruned.trans (pruned_filterAllAgg X [r]) (ih _)

/-- **Several pins, one at a time**: a state inside a branch state, pinned one by one, stays inside the
branch that carries all those pins. -/
theorem pinOneByOne_branch (hwf : WF φ) (h1 : PinCommutes1 φ) (m : Nat) (hlb : litBlock φ < (m : Int) + 1) :
    ∀ (rs : List NodeId), (∀ r ∈ rs, 0 ≤ r.step ∧ r.step < litBlock φ) →
      ∀ (P : List NodeId) (X : GPathM) (kv : NodeId × GPathM), kv ∈ branchLine φ P m → Good X →
        Embedded X kv.2 → isValid (pinOneByOne X rs) = true →
        ∃ kv' ∈ branchLine φ (P ++ rs) m, kv'.1 = kv.1 ∧ Embedded (pinOneByOne X rs) kv'.2 := by
  intro rs
  induction rs with
  | nil => intro _ P X kv hkv _ e _; exact ⟨kv, by rw [List.append_nil]; exact hkv, rfl, e⟩
  | cons r rest ih =>
    intro hrs P X kv hkv hX e hv
    have hmk : MInv φ kv.2 := (branchLine_inv φ hwf P m).2 kv hkv
    -- the first pin is valid, since the rest only removes
    have hv1 : isValid (filterAllAgg X [r]) = true := by
      have hg := good_filterAllAgg hX [r]
      exact isValid_of_embedded (embedded_of_pruned (pruned_pinOneByOne rest _) hg.rc.nodup
        (embedded_refl _)) hv
    have e1 := embedded_pin X kv.2 [r] e hX (good_of_minv φ hmk) hv1
    have hvk := isValid_of_embedded e1 hv1
    obtain ⟨kv1, hkv1, hk1, e2⟩ := h1 P m kv hkv hlb r (hrs r List.mem_cons_self).1
      (hrs r List.mem_cons_self).2 hvk
    obtain ⟨kv', hkv', hk', e3⟩ := ih (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr')) (P ++ [r])
      (filterAllAgg X [r]) kv1 hkv1 (good_filterAllAgg hX [r]) (embedded_trans e1 e2) hv
    refine ⟨kv', ?_, by rw [hk', hk1], e3⟩
    rw [show P ++ r :: rest = P ++ [r] ++ rest by simp]; exact hkv'

/-- **One pin at a time is enough**: `PinCommutes1` gives `PinCommutes`. The row's three pins at once
are the three pins one by one (`SeqPin.seq_eq_all`). -/
theorem pinCommutes_of_one (hwf : WF φ) (h1 : PinCommutes1 φ) : PinCommutes φ := by
  intro P m kv hkv hm d hd hlb hne hvA x q hxq _
  have hl := branchLine_inv φ hwf P m
  have hsok : StateOkF φ m kv := hl.1.2 kv hkv
  have hmk : MInv φ kv.2 := hl.2 kv hkv
  have hdstep := dstep_of φ m kv hsok d hd
  obtain ⟨j, hj, hjs⟩ := ClauseReview.clause_of_row φ d hlb hne
  have hreqs := reqOfCnf_clause φ d j φ.clauses[j] hj (List.getElem?_eq_getElem hj) hjs
  have hr : ∀ r ∈ reqOfCnf φ d, 0 ≤ r.step ∧ r.step < litBlock φ := by
    intro r hr
    refine ⟨?_, RunInhabited.reqOfCnf_lit φ hwf d r hr⟩
    rw [hreqs] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (show 0 ≤ Lit.step _; unfold Lit.step; split <;> omega)
  rw [hreqs] at hvA hxq hr ⊢
  obtain ⟨hvS, eAS, _⟩ := SeqPin.seq_eq_all kv.2 hmk.rctx hmk.smp hmk.pms hmk.sn _ _ hvA
  obtain ⟨kv', hkv', hk, e⟩ := pinOneByOne_branch φ hwf h1 m (by rw [← hdstep]; exact hlb) _ hr P kv.2 kv hkv
    (good_of_minv φ hmk) (embedded_refl _) hvS
  have eA := embedded_trans eAS e
  obtain ⟨n, hn, hqn, hqm⟩ := hxq
  obtain ⟨n', hn', hown, _⟩ := eA.node x n hn
  exact ⟨kv', hkv', hk, n', hn', hown q hqn hqm, mem_of_embedded eA hqm⟩

/-- **The verdict from one pin at a time.** -/
theorem sat_of_pinCommutes1 (hwf : WF φ) (h1 : PinCommutes1 φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_pinCommutes φ hwf (pinCommutes_of_one φ hwf h1) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.PinHistory.sat_of_pinCommutes1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pinCommutes1

-- ============================================================
-- One pin, line by line: the history property is one step of the machine
-- ============================================================

/-- **Pinning goes through one advance.** If each pinned state of a branch's line sits inside the state with
the same key of the branch that also carries the pin, the same holds on the next line. -/
def PinAdvance : Prop :=
  ∀ (P : List NodeId) (m : Nat) (r : NodeId), 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
    (∀ kv ∈ branchLine φ P m, isValid (filterAllAgg kv.2 [r]) = true →
      ∃ kv' ∈ branchLine φ (P ++ [r]) m, kv'.1 = kv.1 ∧ Embedded (filterAllAgg kv.2 [r]) kv'.2) →
    ∀ kv ∈ pureAdvanceW φ (branchLine φ P m), isValid (filterAllAgg kv.2 [r]) = true →
      ∃ kv' ∈ pureAdvanceW φ (branchLine φ (P ++ [r]) m), kv'.1 = kv.1 ∧
        Embedded (filterAllAgg kv.2 [r]) kv'.2

/-- **A pin at the top step is the key.** Every node at the top carries the key; a valid pinned state keeps
a global owner there, which is the pin. -/
theorem topPin_key (k : Int) (kv : NodeId × GPathM) (hsok : StateOkF φ k kv) (hm : MInv φ kv.2)
    (r : NodeId) (hr : r.step = k) (hv : isValid (filterAllAgg kv.2 [r]) = true) : r = kv.1 := by
  have hRr : ReadableAgg (filterAllAgg kv.2 [r]) := ⟨kv.2, [r], hm.rctx, rfl⟩
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hv
  have hpr := pruned_filterAllAgg kv.2 [r]
  have hcs : (filterAllAgg kv.2 [r]).current_step = k + 1 := by rw [hpr.step_eq, hsok.step]
  have htl := ParentId.TL_of_pruned hpr hm.tl
  have hk0 : 0 ≤ k := SliceInvariant.nonneg_of_mapNodes φ k kv.1 hsok.onMap
  have hv' := hv
  simp only [isValid, List.all_eq_true] at hv'
  have hent := hv' k (mem_intRange hk0 (by rw [hcs]; omega))
  obtain ⟨z, hz, hzs⟩ := List.any_eq_true.mp hent
  have hzs' : z.id.step = k := eq_of_beq hzs
  have hzid : z.id = r := ReaderComplete.pin_id kv.2 r z hz (by rw [hzs', hr])
  obtain ⟨n, hn, hnid⟩ := ctxR.gn z hz
  have := htl n hn (by rw [hnid, hzs', hcs]; omega)
  rw [hnid, hzid, hpr.map_parent_eq, hsok.par] at this
  exact Option.some.inj this

/-- The branch of `P ++ [r]` at the step of `r` is the branch of `P` restricted to the key `r`. -/
theorem mem_branch_top (P : List NodeId) (m : Nat) (r : NodeId) (hr : r.step = m) (kv : NodeId × GPathM)
    (hkv : kv ∈ branchLine φ P m) (hk : kv.1 = r) : kv ∈ branchLine φ (P ++ [r]) m := by
  have h := SendDistrib.bline_append φ P r m hr m (Nat.le_refl _)
  show kv ∈ SendDistrib.bline φ (P ++ [r]) m
  rw [h]
  refine List.mem_filter.mpr ⟨hkv, ?_⟩
  simp [hk]

/-- **The pin commutes with the history at every line**, from `PinAdvance`: by induction on the line. A
pin at the top step is the key, and the branch keeps that state; below it, `PinAdvance` carries the
previous line's embedding one step up. -/
theorem pinCommutes_all (hwf : WF φ) (hA : PinAdvance φ) (P : List NodeId) :
    ∀ (m : Nat), ∀ kv ∈ branchLine φ P m, ∀ r : NodeId, 0 ≤ r.step → r.step ≤ m → r.step < litBlock φ →
      isValid (filterAllAgg kv.2 [r]) = true →
      ∃ kv' ∈ branchLine φ (P ++ [r]) m, kv'.1 = kv.1 ∧ Embedded (filterAllAgg kv.2 [r]) kv'.2 := by
  have top : ∀ (m : Nat), ∀ kv ∈ branchLine φ P m, ∀ r : NodeId, r.step = m →
      isValid (filterAllAgg kv.2 [r]) = true →
      ∃ kv' ∈ branchLine φ (P ++ [r]) m, kv'.1 = kv.1 ∧ Embedded (filterAllAgg kv.2 [r]) kv'.2 := by
    intro m kv hkv r hr hv
    have hl := branchLine_inv φ hwf P m
    have hmk : MInv φ kv.2 := hl.2 kv hkv
    have hk := topPin_key φ m kv (hl.1.2 kv hkv) hmk r hr hv
    exact ⟨kv, mem_branch_top φ P m r hr kv hkv hk.symm, rfl,
      embedded_of_pruned (pruned_filterAllAgg _ _) hmk.rctx.nodup (embedded_refl _)⟩
  intro m
  induction m with
  | zero => intro kv hkv r h0 h1 _ hv; exact top 0 kv hkv r (by omega) hv
  | succ m ih =>
    intro kv hkv r h0 h1 hlb hv
    by_cases hrt : r.step = ((m + 1 : Nat) : Int)
    · exact top (m + 1) kv hkv r hrt hv
    · have hkv' := hkv
      rw [branchLine_succ] at hkv'
      obtain ⟨hA', hpass⟩ := mem_restrict hkv'
      obtain ⟨kv', hkv'', hk, e⟩ := hA P m r h0 (by omega) hlb
        (fun kv0 hkv0 hv0 => ih kv0 hkv0 r h0 (by omega) hlb hv0) kv hA' hv
      refine ⟨kv', ?_, hk, e⟩
      rw [branchLine_succ]
      refine List.mem_filter.mpr ⟨hkv'', List.all_eq_true.mpr fun r' hr' => ?_⟩
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      rcases List.mem_append.mp hr' with h | h
      · rcases hpass r' h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [hk]; exact h')
      · rw [List.mem_singleton.mp h]; exact Or.inl (by push_cast at hrt ⊢; omega)

/-- **`PinCommutes1` from one step of the machine.** -/
theorem pinCommutes1_of_advance (hwf : WF φ) (hA : PinAdvance φ) : PinCommutes1 φ := by
  intro P m kv hkv hlb r h0 h1 hv
  exact pinCommutes_all φ hwf hA P m kv hkv r h0 (by omega) h1 hv

/-- **The verdict from `PinAdvance`.** -/
theorem sat_of_pinAdvance (hwf : WF φ) (hA : PinAdvance φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  sat_of_pinCommutes1 φ hwf (pinCommutes1_of_advance φ hwf hA) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.PinHistory.sat_of_pinAdvance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_pinAdvance

end AbsSat.GraphPath.Model.PinHistory
