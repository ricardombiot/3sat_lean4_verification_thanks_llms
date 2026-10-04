-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnClosed.lean
import AbsSatBingo.Model.ForbidOnBook
import AbsSatBingo.Model.ReviewClean
import AbsSatBingo.Model.MachineClique

/-!
# El review `:on` deja el estado cerrado (`docs/plans/lean_forbid_on.md`, F3)

Las operaciones del review `:off` no miran los tríos y los dejan como estaban: conmutan con cambiarlos
(`setT`). Si una vuelta `:on` sale sin `dirty`, la regla no cortó ninguna arista y solo escribió tríos, así que
esa vuelta es una vuelta `:off` con otros tríos.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- Cambiar los tríos. -/
abbrev setT (g : GPathB) (T : List (PathNodeId × PathNodeId × PathNodeId)) : GPathB := { g with trios := T }

variable (T : List (PathNodeId × PathNodeId × PathNodeId))

-- Las primitivas

theorem removeEdge_setT (g : GPathB) (x w : PathNodeId) : (g.setT T).removeEdge x w = (g.removeEdge x w).setT T := rfl
theorem killVertex_setT (g : GPathB) (id : PathNodeId) : (g.setT T).killVertex id = (g.killVertex id).setT T := rfl
theorem removeNode_setT (g : GPathB) (id : PathNodeId) : (g.setT T).removeNode id = (g.removeNode id).setT T := rfl
theorem dirty_setT (g : GPathB) (b : Bool) : ({ g.setT T with dirty := b } : GPathB) = ({ g with dirty := b } : GPathB).setT T := rfl

-- La purga

theorem purgeStep_setT (g : GPathB) (id : PathNodeId) : (g.setT T).purgeStep id = (g.purgeStep id).setT T := by
  unfold purgeStep
  show (match g.node? id with
    | none => g.setT T
    | some n => if g.isValidNode n then g.setT T else { (g.setT T).removeNode id with dirty := true }) = _
  cases g.node? id with
  | none => rfl
  | some n =>
    dsimp only
    by_cases h : g.isValidNode n = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; rfl

theorem foldl_setT {α : Type} (f : GPathB → α → GPathB) (hf : ∀ g a, f (g.setT T) a = (f g a).setT T) :
    ∀ (l : List α) (g : GPathB), l.foldl f (g.setT T) = (l.foldl f g).setT T := by
  intro l
  induction l with
  | nil => intro g; rfl
  | cons a as ih => intro g; simp only [List.foldl_cons]; rw [hf, ih]

theorem purgeRound_setT (g : GPathB) : (g.setT T).purgeRound = g.purgeRound.setT T := by
  unfold purgeRound
  exact foldl_setT T _ (fun g id => purgeStep_setT T g id) _ g

theorem purgeFuel_setT : ∀ (n : Nat) (g : GPathB), purgeFuel n (g.setT T) = (purgeFuel n g).setT T := by
  intro n
  induction n with
  | zero => intro g; rfl
  | succ n ih =>
    intro g
    rw [purgeFuel.eq_2, purgeFuel.eq_2]
    show (if g.isValid then
        (if (g.setT T).purgeRound.nodes.length < g.nodes.length then purgeFuel n (g.setT T).purgeRound
          else (g.setT T).purgeRound) else g.setT T) = _
    rw [purgeRound_setT]
    by_cases hv : g.isValid = true
    · simp only [hv, if_true]
      split
      · rw [ih]
      · rfl
    · simp [hv]

theorem clean_setT (g : GPathB) : (g.setT T).clean = g.clean.setT T := purgeFuel_setT T _ g

theorem clean_setT' (g : GPathB) : (g.setT T).clean = g.clean.setT T := clean_setT T g

-- Las parejas

theorem pairSweep_setT (g : GPathB) :
    (g.setT T).pairSweep = ((g.pairSweep).1.setT T, (g.pairSweep).2) := by
  unfold pairSweep
  show ((g.edges.filter (fun e => !g.pairOk e.1 e.2)).foldl (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2)
      (g.setT T), _) = _
  rw [foldl_setT T (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) (fun g e => removeEdge_setT T g e.1 e.2)]
  rfl

theorem pairFuel_setT : ∀ (n : Nat) (g : GPathB), pairFuel n (g.setT T) = (pairFuel n g).setT T := by
  intro n
  induction n with
  | zero => intro g; rfl
  | succ n ih =>
    intro g
    rw [pairFuel.eq_2, pairFuel.eq_2]
    show (if g.isValid then
        (if (g.setT T).pairSweep.2 then pairFuel n (clean { (g.setT T).pairSweep.1 with dirty := true })
          else g.setT T) else g.setT T) = _
    rw [pairSweep_setT]
    by_cases hv : g.isValid = true
    · simp only [hv, if_true]
      split
      · show pairFuel n (clean (({ g.pairSweep.1 with dirty := true } : GPathB).setT T)) =
          (pairFuel n (clean { g.pairSweep.1 with dirty := true })).setT T
        rw [clean_setT, ih]
      · rfl
    · simp [hv]

theorem cleanPair_setT (g : GPathB) : (g.setT T).cleanPair = g.cleanPair.setT T := by
  unfold cleanPair
  show pairFuel ((g.setT T).clean.measure + 1) (g.setT T).clean = _
  rw [clean_setT]
  exact pairFuel_setT T _ _

-- Los enlaces

theorem pruneLinks_setT (g : GPathB) : (g.setT T).pruneLinks = g.pruneLinks.setT T := by
  unfold pruneLinks
  by_cases hv : g.isValid = true
  · show (if g.isValid then _ else _) = _
    rw [if_pos hv, if_pos hv]; rfl
  · show (if g.isValid then _ else _) = _
    rw [if_neg hv, if_neg hv]

-- Las pasadas de padres e hijos

theorem cutSupport_setT (g : GPathB) (x : PathNodeId) (sup : List PathNodeId) :
    (g.setT T).cutSupport x sup = ((g.cutSupport x sup).1.setT T, (g.cutSupport x sup).2) := by
  unfold cutSupport
  show (List.foldl (fun h w => h.removeEdge x w) (g.setT T) _, _) = _
  rw [foldl_setT T (fun h w => h.removeEdge x w) (fun g w => removeEdge_setT T g x w)]
  rfl

theorem cutStep_setT (sel : PNodeB → List PathNodeId) (g : GPathB) (n : PNodeB) :
    cutStep sel (g.setT T) n = (cutStep sel g n).setT T := by
  unfold cutStep
  show (if g.isValidNode n then
      (if ((g.setT T).cutSupport n.id (sel n)).2 then { ((g.setT T).cutSupport n.id (sel n)).1 with dirty := true }
        else ((g.setT T).cutSupport n.id (sel n)).1) else g.setT T) = _
  rw [cutSupport_setT]
  by_cases hv : g.isValidNode n = true
  · rw [if_pos hv, if_pos hv]
    dsimp only
    split <;> rfl
  · rw [if_neg hv, if_neg hv]

theorem reviewNode_setT (sel : PNodeB → List PathNodeId) (g : GPathB) (id : PathNodeId) :
    reviewNode sel (g.setT T) id = (reviewNode sel g id).setT T := by
  unfold reviewNode
  show (match g.node? id with
    | none => g.setT T
    | some n => if (cutStep sel (g.setT T) n).isValidNode n then cutStep sel (g.setT T) n
        else { (cutStep sel (g.setT T) n).removeNode id with dirty := true }) = _
  cases g.node? id with
  | none => rfl
  | some n =>
    dsimp only
    rw [cutStep_setT]
    by_cases hv : (cutStep sel g n).isValidNode n = true
    · have hv' : ((cutStep sel g n).setT T).isValidNode n = true := hv
      rw [if_pos hv', if_pos hv]
    · have hv' : ¬ ((cutStep sel g n).setT T).isValidNode n = true := hv
      rw [if_neg hv', if_neg hv]; rfl

theorem reviewLine_setT (sel : PNodeB → List PathNodeId) (g : GPathB) (k : Int) :
    reviewLine sel (g.setT T) k = (reviewLine sel g k).setT T := by
  unfold reviewLine
  exact foldl_setT T _ (fun g id => reviewNode_setT T sel g id) _ g

theorem reviewSteps_setT (sel : PNodeB → List PathNodeId) :
    ∀ (ks : List Int) (g : GPathB), reviewSteps sel (g.setT T) ks = setT (reviewSteps sel g ks) T := by
  intro ks
  induction ks with
  | nil => intro g; rfl
  | cons k ks ih =>
    intro g
    rw [reviewSteps.eq_2, reviewSteps.eq_2]
    rw [reviewLine_setT]
    by_cases hv : (reviewLine sel g k).isValid = true
    · have hv' : (setT (reviewLine sel g k) T).isValid = true := hv
      rw [if_pos hv', if_pos hv, ih]
    · have hv' : ¬ (setT (reviewLine sel g k) T).isValid = true := hv
      rw [if_neg hv', if_neg hv]

theorem reviewParents_setT (g : GPathB) : (g.setT T).reviewParents = g.reviewParents.setT T := by
  unfold reviewParents
  show (if g.isValid && g.dirty then reviewSteps _ (g.setT T) _ else g.setT T) = _
  split
  · rw [reviewSteps_setT]
  · rfl

theorem reviewSons_setT (g : GPathB) : (g.setT T).reviewSons = g.reviewSons.setT T := by
  unfold reviewSons
  show (if g.isValid && g.dirty then reviewSteps _ (g.setT T) _ else g.setT T) = _
  split
  · rw [reviewSteps_setT]
  · rfl

theorem reviewPass_setT (g : GPathB) : (g.setT T).reviewPass = g.reviewPass.setT T := by
  unfold reviewPass
  rw [cleanPair_setT T g, pruneLinks_setT T g.cleanPair, reviewParents_setT T g.cleanPair.pruneLinks,
    reviewSons_setT T g.cleanPair.pruneLinks.reviewParents, pruneLinks_setT T g.cleanPair.pruneLinks.reviewParents.reviewSons]

theorem forcedParents_setT (g : GPathB) : (g.setT T).forcedParents = g.forcedParents.setT T := by
  unfold forcedParents
  show (if g.isValid then reviewSteps _ (g.setT T) _ else g.setT T) = _
  split
  · rw [reviewSteps_setT]
  · rfl

theorem forcedSons_setT (g : GPathB) : (g.setT T).forcedSons = g.forcedSons.setT T := by
  unfold forcedSons
  show (if g.isValid then reviewSteps _ (g.setT T) _ else g.setT T) = _
  split
  · rw [reviewSteps_setT]
  · rfl

theorem finalPass_setT (g : GPathB) : (g.setT T).finalPass = g.finalPass.setT T := by
  unfold finalPass
  rw [forcedParents_setT T g, forcedSons_setT T g.forcedParents, pruneLinks_setT T g.forcedParents.forcedSons]

-- ============================================================
-- La regla borra o no enciende `dirty`: el combustible basta
-- ============================================================

theorem measure_setT (g : GPathB) : (g.setT T).measure = g.measure := rfl
theorem dirty_setT' (g : GPathB) : (g.setT T).dirty = g.dirty := rfl
theorem isValid_setT (g : GPathB) : (g.setT T).isValid = g.isValid := rfl
theorem step_setT (g : GPathB) : (g.setT T).current_step = g.current_step := rfl
theorem setT_back (g : GPathB) : (g.setT T).setT g.trios = g := rfl

theorem trioBlind_closedState (g : GPathB) (h : ClosedState g) : ClosedState (g.setT T) :=
  ⟨h.alive, h.refl, h.symm, h.dom, h.adj, h.pair, h.node, h.par, h.son⟩

theorem trioBlind_back {P : GPathB → Prop} (hb : TrioBlind P) {g : GPathB} (h : P (g.setT T)) : P g := by
  exact hb (g.setT T) g.trios h

theorem addTrios_eq (g : GPathB) (i : Idx) (ts : List (PathNodeId × PathNodeId × PathNodeId)) :
    ∃ T', (g.addTrios i ts).1 = g.setT T' := ⟨_, rfl⟩

theorem measure_forbidRound_le (g : GPathB) : g.forbidRound.1.measure ≤ g.measure := by
  unfold forbidRound
  simp only
  split
  · obtain ⟨T', hT⟩ := addTrios_eq g (Idx.of g) (g.newTrios (Idx.of g))
    rw [hT]; exact Nat.le_refl _
  · obtain ⟨T', hT⟩ := addTrios_eq g (Idx.of g) (g.newTrios (Idx.of g))
    rw [hT]
    refine Nat.le_trans (shrinks_clean _).2 ?_
    exact measure_foldl_le (fun (h : GPathB) (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2)
      (fun g e => measure_removeEdge_le g e.1 e.2) _ _

theorem strictDirty_forbidRound : StrictDirty (fun g => g.forbidRound.1) := by
  intro g hg hd
  simp only [forbidRound] at hd ⊢
  obtain ⟨T', hT⟩ := addTrios_eq g (Idx.of g) (g.newTrios (Idx.of g))
  rw [hT] at hd ⊢
  generalize hbad : (g.setT T').edges.filter (fun e => !(Idx.of (g.setT T')).edgeAlive e.1 e.2) = bad at hd ⊢
  cases bad with
  | nil => simp only [List.isEmpty_nil, if_true] at hd; exact absurd hd (by simp [hg])
  | cons e rest =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
    have hmem : e ∈ (g.setT T').edges.filter (fun e => !(Idx.of (g.setT T')).edgeAlive e.1 e.2) := by
      rw [hbad]; exact List.mem_cons_self
    have he : e ∈ g.edges := (List.mem_filter.mp hmem).1
    have hj : g.hasEdge e.1 e.2 = true := List.any_eq_true.mpr ⟨e, he, by simp [joins]⟩
    refine Nat.lt_of_le_of_lt (shrinks_clean _).2 ?_
    show (List.foldl (fun (h : GPathB) (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2)
      ((g.setT T').removeEdge e.1 e.2) rest).measure < g.measure
    have h1 := measure_foldl_le (fun (h : GPathB) (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2)
      (fun g e => measure_removeEdge_le g e.1 e.2) rest ((g.setT T').removeEdge e.1 e.2)
    exact Nat.lt_of_le_of_lt h1 (measure_removeEdge_lt (g.setT T') e.1 e.2 hj)

theorem measure_forbidFuel_le : ∀ (n : Nat) (g : GPathB), (forbidFuel n g).measure ≤ g.measure := by
  intro n
  induction n with
  | zero => intro g; exact Nat.le_refl _
  | succ n ih =>
    intro g
    unfold forbidFuel
    split
    · simp only
      split
      · exact Nat.le_trans (ih _) (measure_forbidRound_le g)
      · exact measure_forbidRound_le g
    · exact Nat.le_refl _

theorem keepsDirty_forbidRound : KeepsDirty (fun g => g.forbidRound.1) := by
  intro g hg
  simp only [forbidRound]
  obtain ⟨T', hT⟩ := addTrios_eq g (Idx.of g) (g.newTrios (Idx.of g))
  rw [hT]
  split
  · exact hg
  · exact keepsDirty_clean _ rfl

theorem keepsDirty_forbidFuel : ∀ (n : Nat), KeepsDirty (forbidFuel n) := by
  intro n
  induction n with
  | zero => intro g hg; exact hg
  | succ n ih =>
    intro g hg
    unfold forbidFuel
    split
    · simp only
      split
      · exact ih _ (keepsDirty_forbidRound g hg)
      · exact keepsDirty_forbidRound g hg
    · exact hg

theorem strictDirty_forbidFuel : ∀ (n : Nat), StrictDirty (forbidFuel n) := by
  intro n
  induction n with
  | zero => intro g hg hd; simp only [forbidFuel] at hd; rw [hg] at hd; cases hd
  | succ n ih =>
    intro g hg hd
    unfold forbidFuel at hd ⊢
    split at hd
    · rename_i hv
      simp only [hv, if_true] at hd ⊢
      split at hd
      · rename_i hr
        simp only [hr, if_true]
        cases hd1 : g.forbidRound.1.dirty
        · exact Nat.lt_of_lt_of_le (ih _ hd1 hd) (measure_forbidRound_le g)
        · exact Nat.lt_of_le_of_lt (measure_forbidFuel_le n _) (strictDirty_forbidRound g hg hd1)
      · rename_i hr
        simp only [hr]
        exact strictDirty_forbidRound g hg hd
    · rw [hg] at hd; cases hd

theorem strictDirty_forbidRule : StrictDirty forbidRule := fun g hg hd => strictDirty_forbidFuel _ g hg hd

theorem measure_forbidRule_le (g : GPathB) : g.forbidRule.measure ≤ g.measure := measure_forbidFuel_le _ g

theorem keepsDirty_forbidRule : KeepsDirty forbidRule := fun g hg => keepsDirty_forbidFuel _ g hg

theorem strictDirty_reviewPassOn : StrictDirty reviewPassOn := by
  have c0 := strictDirty_comp strictDirty_cleanPair strictDirty_forbidRule (fun g => (shrinks_cleanPair g).2)
    measure_forbidRule_le
  have s0 : ∀ g : GPathB, g.cleanPair.forbidRule.measure ≤ g.measure :=
    fun g => Nat.le_trans (measure_forbidRule_le _) (shrinks_cleanPair g).2
  have c1 := strictDirty_comp c0 strictDirty_pruneLinks s0 (fun g => (shrinks_pruneLinks g).2)
  have s1 : ∀ g : GPathB, g.cleanPair.forbidRule.pruneLinks.measure ≤ g.measure :=
    fun g => Nat.le_trans (shrinks_pruneLinks _).2 (s0 g)
  have c2 := strictDirty_comp c1 strictDirty_reviewParents s1 (fun g => (shrinks_reviewParents g).2)
  have s2 : ∀ g : GPathB, g.cleanPair.forbidRule.pruneLinks.reviewParents.measure ≤ g.measure :=
    fun g => Nat.le_trans (shrinks_reviewParents _).2 (s1 g)
  have c3 := strictDirty_comp c2 strictDirty_reviewSons s2 (fun g => (shrinks_reviewSons g).2)
  have s3 : ∀ g : GPathB, g.cleanPair.forbidRule.pruneLinks.reviewParents.reviewSons.measure ≤ g.measure :=
    fun g => Nat.le_trans (shrinks_reviewSons _).2 (s2 g)
  have c4 := strictDirty_comp c3 strictDirty_pruneLinks s3 (fun g => (shrinks_pruneLinks g).2)
  intro g hg hd
  exact c4 g hg hd

theorem measure_reviewPassOn_le (g : GPathB) : g.reviewPassOn.measure ≤ g.measure :=
  Nat.le_trans (shrinks_pruneLinks _).2 (Nat.le_trans (shrinks_reviewSons _).2 (Nat.le_trans
    (shrinks_reviewParents _).2 (Nat.le_trans (shrinks_pruneLinks _).2 (Nat.le_trans (measure_forbidRule_le _)
    (shrinks_cleanPair g).2))))

/-- Con más combustible que la medida, el review `:on` que sale válido sale sin `dirty`. -/
theorem reviewFuelOn_exits_clean :
    ∀ (n : Nat) (g : GPathB), g.measure < n → (reviewFuelOn n g).isValid = true → (reviewFuelOn n g).dirty = false := by
  intro n
  induction n with
  | zero => intro g hm; omega
  | succ n ih =>
    intro g hm hv
    have hm0 : ({ g with dirty := false } : GPathB).measure = g.measure := rfl
    unfold reviewFuelOn at hv ⊢
    split at hv
    · rename_i h
      simp only [h, if_true] at hv ⊢
      split at hv
      · rename_i hpd
        simp only [hpd, if_true] at hv ⊢
        have hlt := strictDirty_reviewPassOn { g with dirty := false } rfl hpd
        exact ih _ (by omega) hv
      · rename_i hpd
        simp only [hpd] at hv ⊢
        split at hv
        · rename_i hvp
          simp only [hvp, if_true] at hv ⊢
          split at hv
          · rename_i hfd
            simp only [hfd, if_true] at hv ⊢
            have h1 := strictDirty_finalPass _ (by simpa using hpd) hfd
            have h2 := measure_reviewPassOn_le { g with dirty := false }
            exact ih _ (by omega) hv
          · rename_i hfd
            simp only [hfd]
            simpa using hpd
        · rename_i hvp
          exact absurd hv hvp
    · rename_i h
      simp only [h]
      simp only [hv, Bool.true_and, Bool.not_eq_true] at h
      exact h

theorem reviewOn_exits_clean (g : GPathB) (hv : g.reviewOn.isValid = true) : g.reviewOn.dirty = false :=
  reviewFuelOn_exits_clean _ g (Nat.lt_succ_self _) hv

-- ============================================================
-- AliveDocs
-- ============================================================

theorem aliveDocs_forbidRound {g : GPathB} (h : AliveDocs g) : AliveDocs g.forbidRound.1 := by
  simp only [forbidRound]
  obtain ⟨T', hT⟩ := addTrios_eq g (Idx.of g) (g.newTrios (Idx.of g))
  rw [hT]
  split
  · exact h
  · exact aliveDocs_clean (aliveDocs_dirty (aliveDocs_foldl _ (fun g (e : PathNodeId × PathNodeId) h => aliveDocs_removeEdge h e.1 e.2) _ (g.setT T') (show AliveDocs (g.setT T') from h)) _)

theorem aliveDocs_forbidFuel : ∀ (n : Nat) (g : GPathB), AliveDocs g → AliveDocs (forbidFuel n g) := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    unfold forbidFuel
    split
    · simp only
      split
      · exact ih _ (aliveDocs_forbidRound h)
      · exact aliveDocs_forbidRound h
    · exact h

theorem aliveDocs_reviewPassOn {g : GPathB} (h : AliveDocs g) : AliveDocs g.reviewPassOn := by
  have h1 : AliveDocs g.cleanPair.forbidRule := aliveDocs_forbidFuel _ _ (aliveDocs_pairFuel _ _ (aliveDocs_clean h))
  have h2 := aliveDocs_pruneLinks h1
  have h3 : AliveDocs g.cleanPair.forbidRule.pruneLinks.reviewParents := by
    unfold reviewParents; split
    · exact aliveDocs_reviewSteps _ _ _ h2
    · exact h2
  have h4 : AliveDocs g.cleanPair.forbidRule.pruneLinks.reviewParents.reviewSons := by
    unfold reviewSons; split
    · exact aliveDocs_reviewSteps _ _ _ h3
    · exact h3
  exact aliveDocs_pruneLinks h4

theorem aliveDocs_reviewOn {g : GPathB} (h : AliveDocs g) : AliveDocs g.reviewOn :=
  reviewFuelOn_pres AliveDocs (fun _ hh => aliveDocs_reviewPassOn (aliveDocs_dirty hh _))
    (fun _ hh => aliveDocs_finalPass hh) _ g h

-- ============================================================
-- Una vuelta `:on` sin `dirty` es una vuelta `:off` con otros tríos
-- ============================================================

/-- **La regla que no enciende `dirty` solo escribe tríos.** -/
theorem forbidFuel_quiet : ∀ (n : Nat) (g : GPathB), g.dirty = false → (forbidFuel n g).dirty = false →
    ∃ T', forbidFuel n g = g.setT T' := by
  intro n
  induction n with
  | zero => intro g _ _; exact ⟨g.trios, rfl⟩
  | succ n ih =>
    intro g hg hd
    unfold forbidFuel at hd ⊢
    split at hd
    · rename_i hv
      simp only [hv, if_true] at hd ⊢
      have hr : g.forbidRound.1.dirty = false := by
        cases hr : g.forbidRound.1.dirty
        · rfl
        · exfalso
          split at hd
          · rw [keepsDirty_forbidFuel n _ hr] at hd; cases hd
          · rw [hr] at hd; cases hd
      -- la vuelta no cortó: solo tríos
      have hq : ∃ T₁, g.forbidRound.1 = g.setT T₁ := by
        simp only [forbidRound] at hr ⊢
        obtain ⟨T', hT⟩ := addTrios_eq g (Idx.of g) (g.newTrios (Idx.of g))
        rw [hT] at hr ⊢
        split at hr
        · rename_i hb; simp only [hb, if_true]; exact ⟨T', rfl⟩
        · rename_i hb
          exfalso
          rw [keepsDirty_clean _ rfl] at hr; cases hr
      obtain ⟨T₁, hT₁⟩ := hq
      split at hd
      · rename_i hgrew
        simp only [hgrew, if_true]
        rw [hT₁] at hd ⊢
        obtain ⟨T₂, hT₂⟩ := ih (g.setT T₁) hg hd
        exact ⟨T₂, hT₂⟩
      · rename_i hgrew
        simp only [hgrew]
        exact ⟨T₁, hT₁⟩
    · rename_i hv
      simp only [hv, Bool.false_eq_true, if_false]
      exact ⟨g.trios, rfl⟩

theorem forbidRule_quiet {g : GPathB} (hg : g.dirty = false) (hd : g.forbidRule.dirty = false) :
    ∃ T', g.forbidRule = g.setT T' := forbidFuel_quiet _ g hg hd

/-- **Una vuelta `:on` que sale sin `dirty` es la vuelta `:off` con otros tríos.** -/
theorem reviewPassOn_quiet {g : GPathB} (hp : g.reviewPassOn.dirty = false) :
    ∃ T', g.reviewPassOn = g.reviewPass.setT T' := by
  have k4 := keepsDirty_pruneLinks
  have kf : g.cleanPair.forbidRule.dirty = false := by
    cases h : g.cleanPair.forbidRule.dirty
    · rfl
    · exfalso
      have := k4 _ (keepsDirty_reviewSons _ (keepsDirty_reviewParents _ (keepsDirty_pruneLinks _ h)))
      unfold reviewPassOn at hp; rw [this] at hp; cases hp
  have kc : g.cleanPair.dirty = false := by
    cases h : g.cleanPair.dirty
    · rfl
    · rw [keepsDirty_forbidRule _ h] at kf; cases kf
  obtain ⟨T', hT⟩ := forbidRule_quiet kc kf
  refine ⟨T', ?_⟩
  unfold reviewPassOn reviewPass
  rw [hT, pruneLinks_setT T' g.cleanPair, reviewParents_setT T' g.cleanPair.pruneLinks,
    reviewSons_setT T' g.cleanPair.pruneLinks.reviewParents, pruneLinks_setT T' g.cleanPair.pruneLinks.reviewParents.reviewSons]

-- Una vuelta del review `:on`, caso por caso.

theorem reviewFuelOn_skip {n : Nat} {g : GPathB} (h : ¬ (g.isValid && g.dirty) = true) :
    reviewFuelOn (n + 1) g = g := by
  rw [reviewFuelOn.eq_2, if_neg h]

theorem reviewFuelOn_pass {n : Nat} {g : GPathB} (h : (g.isValid && g.dirty) = true)
    (hp : (reviewPassOn { g with dirty := false }).dirty = true) :
    reviewFuelOn (n + 1) g = reviewFuelOn n (reviewPassOn { g with dirty := false }) := by
  rw [reviewFuelOn.eq_2, if_pos h]; simp only [hp, if_true]

theorem reviewFuelOn_invalid {n : Nat} {g : GPathB} (h : (g.isValid && g.dirty) = true)
    (hp : (reviewPassOn { g with dirty := false }).dirty = false)
    (hv : ¬ (reviewPassOn { g with dirty := false }).isValid = true) :
    reviewFuelOn (n + 1) g = reviewPassOn { g with dirty := false } := by
  rw [reviewFuelOn.eq_2, if_pos h]; simp only [hp, hv, Bool.false_eq_true, if_false]

theorem reviewFuelOn_final {n : Nat} {g : GPathB} (h : (g.isValid && g.dirty) = true)
    (hp : (reviewPassOn { g with dirty := false }).dirty = false)
    (hv : (reviewPassOn { g with dirty := false }).isValid = true)
    (hf : (finalPass (reviewPassOn { g with dirty := false })).dirty = true) :
    reviewFuelOn (n + 1) g = reviewFuelOn n (finalPass (reviewPassOn { g with dirty := false })) := by
  rw [reviewFuelOn.eq_2, if_pos h]; simp only [hp, hv, hf, Bool.false_eq_true, if_false, if_true]

theorem reviewFuelOn_done {n : Nat} {g : GPathB} (h : (g.isValid && g.dirty) = true)
    (hp : (reviewPassOn { g with dirty := false }).dirty = false)
    (hv : (reviewPassOn { g with dirty := false }).isValid = true)
    (hf : (finalPass (reviewPassOn { g with dirty := false })).dirty = false) :
    reviewFuelOn (n + 1) g = reviewPassOn { g with dirty := false } := by
  rw [reviewFuelOn.eq_2, if_pos h]; simp only [hp, hv, hf, Bool.false_eq_true, if_false, if_true]

/-- **El review `:on` que entra con algo que revisar y sale válido y sin `dirty`** devuelve una vuelta limpia cuya
comprobación final no cambió nada. -/
theorem reviewFuelOn_exit :
    ∀ (n : Nat) (g : GPathB), g.dirty = true → (reviewFuelOn n g).isValid = true → (reviewFuelOn n g).dirty = false →
      ∃ g₁ : GPathB, g₁.dirty = false ∧ reviewFuelOn n g = g₁.reviewPassOn ∧ g₁.reviewPassOn.dirty = false ∧
        g₁.reviewPassOn.isValid = true ∧ (finalPass g₁.reviewPassOn).dirty = false := by
  intro n
  induction n with
  | zero => intro g hd _ hc; rw [reviewFuelOn.eq_1, hd] at hc; cases hc
  | succ n ih =>
    intro g hd hv hc
    by_cases h : (g.isValid && g.dirty) = true
    · cases hpd : (reviewPassOn { g with dirty := false }).dirty
      · by_cases hvp : (reviewPassOn { g with dirty := false }).isValid = true
        · cases hfd : (finalPass (reviewPassOn { g with dirty := false })).dirty
          · rw [reviewFuelOn_done h hpd hvp hfd]
            exact ⟨_, rfl, rfl, hpd, hvp, hfd⟩
          · rw [reviewFuelOn_final h hpd hvp hfd] at hv hc ⊢
            exact ih _ hfd hv hc
        · rw [reviewFuelOn_invalid h hpd hvp] at hv; exact absurd hv hvp
      · rw [reviewFuelOn_pass h hpd] at hv hc ⊢
        exact ih _ hpd hv hc
    · rw [reviewFuelOn_skip h] at hc; rw [hd] at hc; cases hc

/-- El paso no cambia. -/
theorem revPrims_step (c : Int) : RevPrims (fun h : GPathB => h.current_step = c) :=
  ⟨fun _ _ h => h, fun _ _ _ h => h, fun _ _ h => h, fun _ _ h => h,
    fun g h => (shrinks_pruneLinks g).1.step.trans h⟩

theorem step_reviewOn (g : GPathB) : g.reviewOn.current_step = g.current_step :=
  revPrims_reviewOn (revPrims_step g.current_step) (fun _ _ h => h) g rfl

/-- **El review `:on` que entra con algo que revisar y sale válido deja el estado cerrado.** -/
theorem closedState_reviewOn {g : GPathB} (hd : g.dirty = true) (hv : g.reviewOn.isValid = true)
    (had : AliveDocs g) (hnd : NodupIds g) (hb : Machine.Below g) (hz : AboveZero g) (hcs : 2 ≤ g.current_step) :
    ClosedState g.reviewOn := by
  have hc := reviewOn_exits_clean g hv
  obtain ⟨g₁, hg₁, he, hpd, hvp, hfd⟩ := reviewFuelOn_exit _ g hd hv hc
  obtain ⟨T', hT⟩ := reviewPassOn_quiet hpd
  have heq : g.reviewOn = g₁.reviewPass.setT T' := he.trans hT
  have hpd' : g₁.reviewPass.dirty = false := by
    have := hpd; rw [hT, dirty_setT'] at this; exact this
  have hvp' : g₁.reviewPass.isValid = true := by
    have := hvp; rw [hT, isValid_setT] at this; exact this
  have hfd' : (finalPass g₁.reviewPass).dirty = false := by
    have := hfd; rw [hT, finalPass_setT, dirty_setT'] at this; exact this
  have had' : AliveDocs g₁.reviewPass := by
    have := aliveDocs_reviewOn had; rw [heq] at this; exact trioBlind_back T' trioBlind_aliveDocs this
  have hnd' : NodupIds g₁.reviewPass := by
    have := revPrims_reviewOn revPrims_nodupIds trioBlind_nodupIds g hnd; rw [heq] at this
    exact trioBlind_back T' trioBlind_nodupIds this
  have hb' : Machine.Below g₁.reviewPass := by
    have := revPrims_reviewOn revPrims_below trioBlind_below g hb; rw [heq] at this
    exact trioBlind_back T' trioBlind_below this
  have hz' : AboveZero g₁.reviewPass := by
    have := revPrims_reviewOn revPrims_aboveZero trioBlind_aboveZero g hz; rw [heq] at this
    exact trioBlind_back T' trioBlind_aboveZero this
  have hcs' : g₁.reviewPass.current_step = g.current_step := by
    have := step_reviewOn g; rw [heq, step_setT] at this; exact this
  have hcl := closedState_of_exit hvp' hpd' hfd' (pairClosed_reviewPass hpd' hvp') (docsAlive_reviewPass hg₁ hpd' hvp')
    had' hnd' hb' hz' (by omega)
  rw [heq]; exact trioBlind_closedState T' _ hcl

end GPathB

end AbsSatBingo.Model
