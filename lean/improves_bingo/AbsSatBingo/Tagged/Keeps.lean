-- lean/improves_bingo/AbsSatBingo/Tagged/Keeps.lean
import AbsSatBingo.Tagged.Carried

/-!
# Las operaciones etiquetadas conservan la camarilla (fase T2 de `docs/plans/lean_row_tags.md`)

`TagCarried` se conserva en el review etiquetado (`tagCarried_reviewT`), en el filtro (`tagCarried_filterAllT`), en la
fila nueva (`tagCarried_addNodeT`: la etiqueta de cada par nuevo sale de la del padre), en el UP, en la marca de la
llegada (`tagCarried_stamp`) y en el join (`tagCarried_doJoinT_left`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace TGPath

open GPathB

variable {S : Int → PathNodeId}

-- ============================================================
-- El review etiquetado
-- ============================================================

theorem step_tagCut (g : GPathB) (T : List TagE) (krows : Int) : (tagCut g T krows).current_step = g.current_step :=
  current_step_foldl_killVertex _ g

/-- **El review etiquetado conserva la camarilla.** -/
theorem tagCarried_reviewTFuel : ∀ (n : Nat) (tg : TGPath), TagCarried tg S → TagCarried (reviewTFuel n tg) S := by
  intro n
  induction n with
  | zero => intro tg h; exact h
  | succ n ih =>
    intro tg h
    have hr := carried_review h.carried
    have hrs : tg.g.review.current_step = tg.g.current_step := step_of_shrinks (shrinks_review tg.g)
    have hrt : CliqueTags tg.g.review.current_step S tg.krows tg.tags := hrs ▸ h.tags
    simp only [reviewTFuel]
    split
    · split
      · split
        · apply ih
          have hsw := cliqueTags_tagSweep hr hrt
          refine ⟨carried_dirty (carried_tagCut hr hsw) true, ?_⟩
          show CliqueTags (tagCut tg.g.review (tagSweep tg.g.review tg.tags) tg.krows).current_step S tg.krows _
          rw [step_tagCut]; exact hsw
        · exact ⟨hr, hrt⟩
      · exact ⟨hr, hrt⟩
    · exact h

theorem tagCarried_reviewT {tg : TGPath} (h : TagCarried tg S) : TagCarried (reviewT tg) S :=
  tagCarried_reviewTFuel _ _ h

/-- **El filtro por requisitos que concuerdan con la camarilla la conserva.** -/
theorem tagCarried_filterAllT {tg : TGPath} (h : TagCarried tg S) (reqs : List NodeId)
    (ha : ∀ r ∈ reqs, Agrees tg.g.current_step S r) : TagCarried (tg.filterAllT reqs) S := by
  unfold filterAllT
  apply tagCarried_reviewT
  obtain ⟨hc, hcs⟩ := carried_foldl (cs := tg.g.current_step) filterRequire reqs
    (fun g' r hr hc hcs => ⟨carried_filterRequire hc (by rw [hcs]; exact ha r hr),
      (step_of_shrinks (shrinks_filterRequire g' r)).trans hcs⟩) tg.g h.carried rfl
  exact ⟨hc, hcs ▸ h.tags⟩

-- ============================================================
-- La marca de la llegada y el join
-- ============================================================

/-- **La marca de la llegada**: la fila nueva de claves es la de la cima del remitente, y su clave es la de la
camarilla en ese paso. -/
theorem tagCarried_stamp {tg : TGPath} (h : TagCarried tg S) {k : NodeId} (hrow : k.step = tg.krows)
    (hkey : (S k.step).id = k) : TagCarried (tg.stamp k) S := by
  refine ⟨h.carried, ?_⟩
  intro ℓ h0 h1 i j hi0 hi1 hj0 hj1
  show hasTag (tagUnion tg.tags _) (S i) (S j) ℓ (S ℓ).id = true
  change ℓ < tg.krows + 1 at h1
  rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp h1) with hl | rfl
  · exact hasTag_tagUnion_left (h.tags ℓ h0 hl i j hi0 hi1 hj0 hj1)
  · rw [← hrow, hkey]
    have hadj := h.carried.adj i j hi0 hi1 hj0 hj1
    rw [adj_iff] at hadj
    rcases hadj with ⟨heq, hal⟩ | ⟨e, he, hj⟩
    · refine hasTag_tagUnion_right (hasTag_append_left (hasTag_iff.mpr ⟨(S i, S i, k.step, k), ?_, ?_⟩))
      · exact List.mem_map.mpr ⟨S i, hal, rfl⟩
      · exact ⟨Or.inl ⟨rfl, heq⟩, rfl, rfl⟩
    · refine hasTag_tagUnion_right
        (hasTag_append_right (hasTag_iff.mpr ⟨(e.1, e.2, k.step, k), List.mem_map.mpr ⟨e, he, rfl⟩, hj, rfl, rfl⟩))

theorem tagCarried_doJoinT_left {a b : TGPath} (h : TagCarried a S) : TagCarried (doJoinT a b) S := by
  unfold doJoinT
  split
  · exact ⟨carried_join_left h.carried, cliqueTags_mono h.tags hasTag_tagUnion_left⟩
  · exact h

theorem tagCarried_doJoinT_right {a b : TGPath} (hok : okJoin a.g b.g = true) (hk : a.krows = b.krows)
    (h : TagCarried b S) : TagCarried (doJoinT a b) S := by
  unfold doJoinT
  rw [if_pos hok]
  have hcs : a.g.current_step = b.g.current_step := by
    unfold okJoin at hok; simp only [Bool.and_eq_true, beq_iff_eq] at hok; exact hok.1.1.1
  refine ⟨carried_join_right hcs h.carried, ?_⟩
  show CliqueTags a.g.current_step S a.krows _
  rw [hcs, hk]
  exact cliqueTags_mono h.tags hasTag_tagUnion_right

-- ============================================================
-- La fila nueva hereda las etiquetas
-- ============================================================

section addNode
variable {g : GPathB} {T : List TagE} {d : NodeId} {forb : PathNodeId → Bool}

/-- Una etiqueta que la fila nueva hereda para `pid`. -/
theorem mem_inherit {pid : PathNodeId} (hnew : pid ∈ g.newRowIds d forb) {e : TagE} (he : e ∈ T) {t : TagE}
    (ht : t ∈ (if e.1 == e.2.1 && (g.rowParents d pid).contains e.1 && g.isAlive e.1 then
        [(pid, pid, e.2.2.1, e.2.2.2), (pid, e.1, e.2.2.1, e.2.2.2)] else []) ++
      (if e.1 != e.2.1 && (g.rowParents d pid).contains e.1 && (g.rowNeighbors d pid).contains e.2.1 &&
          g.adjb e.1 e.2.1 then [(pid, e.2.1, e.2.2.1, e.2.2.2)] else []) ++
      (if e.1 != e.2.1 && (g.rowParents d pid).contains e.2.1 && (g.rowNeighbors d pid).contains e.1 &&
          g.adjb e.1 e.2.1 then [(pid, e.1, e.2.2.1, e.2.2.2)] else [])) :
    t ∈ inheritTags g T d forb :=
  List.mem_flatMap.mpr ⟨pid, hnew, List.mem_flatMap.mpr ⟨e, he, ht⟩⟩

theorem mem_rowNeighbors {pid w p : PathNodeId} (hw : w ∈ g.alive) (hlt : w.id.step < pid.id.step)
    (hp : p ∈ g.rowParents d pid) (hadj : g.Adj p w) : w ∈ g.rowNeighbors d pid := by
  refine List.mem_filter.mpr ⟨hw, ?_⟩
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true hlt, List.any_eq_true.mpr ⟨p, hp, hadj⟩⟩

/-- **El nodo nuevo `S c` hereda la clave de la camarilla**: con su padre `S (c-1)`, con él mismo, y con cada
`S l` anterior. -/
theorem hasTag_inherit {krows : Int} (hc : Carried g S) (ht : CliqueTags g.current_step S krows T)
    (hnew : S g.current_step ∈ g.newRowIds d forb)
    (hpar : 0 < g.current_step → S (g.current_step - 1) ∈ g.rowParents d (S g.current_step))
    (hstep : (S g.current_step).id.step = g.current_step) {ℓ : Int} (h0 : 0 ≤ ℓ) (h1 : ℓ < krows)
    (hpos : 0 < g.current_step) {l : Int} (hl0 : 0 ≤ l) (hl1 : l ≤ g.current_step) :
    hasTag (inheritTags g T d forb) (S g.current_step) (S l) ℓ (S ℓ).id = true := by
  have hp0 : (0 : Int) ≤ g.current_step - 1 := by omega
  have hp1 : g.current_step - 1 < g.current_step := by omega
  have hpp := hpar hpos
  have hpc : (g.rowParents d (S g.current_step)).contains (S (g.current_step - 1)) = true :=
    List.contains_iff_mem.mpr hpp
  have hpal : g.isAlive (S (g.current_step - 1)) = true := List.contains_iff_mem.mpr (hc.alive _ hp0 hp1)
  -- la reflexiva del padre da `S c–S c` y `S c–S (c-1)`
  have hrefl : ∀ {e : TagE}, e ∈ T → e.1 = S (g.current_step - 1) → e.2.1 = S (g.current_step - 1) →
      (S g.current_step, S g.current_step, e.2.2.1, e.2.2.2) ∈ inheritTags g T d forb ∧
      (S g.current_step, e.1, e.2.2.1, e.2.2.2) ∈ inheritTags g T d forb := by
    intro e he he1 he2
    have hcond : (e.1 == e.2.1 && (g.rowParents d (S g.current_step)).contains e.1 && g.isAlive e.1) = true := by
      rw [he1, he2, beq_self_eq_true, hpc, hpal]; rfl
    refine ⟨mem_inherit hnew he ?_, mem_inherit hnew he ?_⟩ <;>
      refine List.mem_append_left _ (List.mem_append_left _ ?_) <;> rw [if_pos hcond]
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  rcases Int.lt_or_eq_of_le hl1 with hl | rfl
  · -- `S l` anterior: por la etiqueta de `p–S l`
    obtain ⟨e, he, hxw, hℓ, ha⟩ := hasTag_iff.mp (ht ℓ h0 h1 (g.current_step - 1) l hp0 hp1 hl0 hl)
    by_cases hlp : l = g.current_step - 1
    · subst hlp
      have hee : e.1 = S (g.current_step - 1) ∧ e.2.1 = S (g.current_step - 1) := by
        rcases hxw with h | h <;> exact ⟨h.1, h.2⟩
      exact hasTag_iff.mpr ⟨_, (hrefl he hee.1 hee.2).2, Or.inl ⟨rfl, hee.1⟩, hℓ, ha⟩
    · have hne : S l ≠ S (g.current_step - 1) := by
        intro heq
        have := congrArg (fun x : PathNodeId => x.id.step) heq
        rw [hc.step l hl0 hl, hc.step _ hp0 hp1] at this
        exact hlp this
      have hwn : S l ∈ g.rowNeighbors d (S g.current_step) :=
        mem_rowNeighbors (hc.alive l hl0 hl) (by rw [hc.step l hl0 hl, hstep]; exact hl) hpp
          (hc.adj _ l hp0 hp1 hl0 hl)
      have hwc : (g.rowNeighbors d (S g.current_step)).contains (S l) = true := List.contains_iff_mem.mpr hwn
      have hadj : g.adjb (S (g.current_step - 1)) (S l) = true := hc.adj _ l hp0 hp1 hl0 hl
      have hadj' : g.adjb (S l) (S (g.current_step - 1)) = true := (adj_symm _ _ _).mp hadj
      have hne1 : (S (g.current_step - 1) != S l) = true := bne_iff_ne.mpr (Ne.symm hne)
      have hne2 : (S l != S (g.current_step - 1)) = true := bne_iff_ne.mpr hne
      rcases hxw with ⟨he1, he2⟩ | ⟨he1, he2⟩
      · refine hasTag_iff.mpr ⟨(S g.current_step, e.2.1, e.2.2.1, e.2.2.2), mem_inherit hnew he ?_,
          Or.inl ⟨rfl, he2⟩, hℓ, ha⟩
        refine List.mem_append_left _ (List.mem_append_right _ ?_)
        have hcond : (e.1 != e.2.1 && (g.rowParents d (S g.current_step)).contains e.1 &&
            (g.rowNeighbors d (S g.current_step)).contains e.2.1 && g.adjb e.1 e.2.1) = true := by
          rw [he1, he2, hne1, hpc, hwc, hadj]; rfl
        rw [if_pos hcond]
        exact List.mem_singleton_self _
      · refine hasTag_iff.mpr ⟨(S g.current_step, e.1, e.2.2.1, e.2.2.2), mem_inherit hnew he ?_,
          Or.inl ⟨rfl, he1⟩, hℓ, ha⟩
        refine List.mem_append_right _ ?_
        have hcond : (e.1 != e.2.1 && (g.rowParents d (S g.current_step)).contains e.2.1 &&
            (g.rowNeighbors d (S g.current_step)).contains e.1 && g.adjb e.1 e.2.1) = true := by
          rw [he1, he2, hne2, hpc, hwc, hadj']; rfl
        rw [if_pos hcond]
        exact List.mem_singleton_self _
  · -- `S c` consigo mismo: por la reflexiva del padre
    obtain ⟨e, he, hxw, hℓ, ha⟩ := hasTag_iff.mp (ht ℓ h0 h1 _ _ hp0 hp1 hp0 hp1)
    have hee : e.1 = S (g.current_step - 1) ∧ e.2.1 = S (g.current_step - 1) := by
      rcases hxw with h | h <;> exact ⟨h.1, h.2⟩
    exact hasTag_iff.mpr ⟨_, (hrefl he hee.1 hee.2).1, Or.inl ⟨rfl, rfl⟩, hℓ, ha⟩

/-- **La fila nueva conserva la camarilla alargada.** -/
theorem tagCarried_addNodeT {tg : TGPath} {title : String} (h : TagCarried tg S)
    (hnew : S tg.g.current_step ∈ tg.g.newRowIds d forb)
    (hpar : 0 < tg.g.current_step → S (tg.g.current_step - 1) ∈ tg.g.rowParents d (S tg.g.current_step))
    (hstep : (S tg.g.current_step).id.step = tg.g.current_step)
    (hbelow : ∀ n ∈ tg.g.nodes, n.id.id.step < tg.g.current_step)
    (hroot : (S 0).parent_id = none) (hkr : tg.krows ≤ tg.g.current_step) :
    TagCarried (tg.addNodeT d title forb) S := by
  refine ⟨carried_addNode h.carried hnew hpar hstep hbelow hroot, ?_⟩
  intro ℓ h0 h1 i j hi0 hi1 hj0 hj1
  show hasTag (tagUnion tg.tags (inheritTags tg.g tg.tags d forb)) (S i) (S j) ℓ (S ℓ).id = true
  change i < tg.g.current_step + 1 at hi1
  change j < tg.g.current_step + 1 at hj1
  change ℓ < tg.krows at h1
  have hpos : 0 < tg.g.current_step := by omega
  rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp hi1) with hi | rfl <;>
    rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp hj1) with hj | rfl
  · exact hasTag_tagUnion_left (h.tags ℓ h0 h1 i j hi0 hi hj0 hj)
  · rw [hasTag_symm]
    exact hasTag_tagUnion_right
      (hasTag_inherit h.carried h.tags hnew hpar hstep h0 h1 hpos hi0 (Int.le_of_lt hi))
  · exact hasTag_tagUnion_right
      (hasTag_inherit h.carried h.tags hnew hpar hstep h0 h1 hpos hj0 (Int.le_of_lt hj))
  · exact hasTag_tagUnion_right
      (hasTag_inherit h.carried h.tags hnew hpar hstep h0 h1 hpos hi0 (Int.le_refl _))

end addNode

end TGPath

end AbsSatBingo.Model
