-- lean/improves_bingo/AbsSatBingo/Model/MachineClique.lean
import AbsSatBingo.Model.EdgeCliqueUp
import AbsSatBingo.Model.Decode

/-!
# `EdgeClique` a lo largo de la máquina y del lector

La cadena entera hacia el veredicto del lector, con `EdgeClique` («todo lo vivo está en una camarilla válida») como
invariante:

* **el review lo conserva** sin hipótesis (`edgeClique_review`): solo borra, y las camarillas sobreviven;
* **el join y el UP** lo conservan (`edgeClique_doJoin`, `edgeClique_up`);
* **la selección** (el filtro por requisitos) lo conserva por **`ReviewExact`**, el único lema de fondo, que aquí
  entra como hipótesis sobre los estados de la máquina (`MachineReviewExact`) y del lector (`ReaderReviewExact`);
* la contabilidad: todo documento vivo (`DocsAlive`, que deja la purga de un review limpio), estado sin `dirty`
  (`review_exits_clean`), y ninguna ventana saltada (`NoSkip`, hipótesis; medido: nunca en el corpus).

Resultado: **`readerVerdict_iff_of_reviewExact`**, el veredicto del lector es la satisfacibilidad bajo
`MachineReviewExact`, `ReaderReviewExact` y `NoSkip`. (`EdgeClique` en un estado válido da `NoZombie`.)
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

-- ============================================================
-- El review conserva EdgeClique
-- ============================================================

/-- **El review conserva `EdgeClique`**: lo que se posee tras el review se poseía antes, y su camarilla sobrevive. -/
theorem edgeClique_review {g : GPathB} (h : EdgeClique g) : EdgeClique g.review := by
  have hs := shrinks_review g
  intro y w hyw
  obtain ⟨S, hc, hy, hw⟩ := h y w (hs.1.adj _ _ hyw)
  exact ⟨S, carried_review hc, by rw [hs.1.step]; exact hy, by rw [hs.1.step]; exact hw⟩

/-- **`EdgeClique` en un estado válido da `NoZombie`**: un vivo cualquiera está en una camarilla. -/
theorem noZombie_of_edgeClique {g : GPathB} (h : EdgeClique g) : NoZombie g := by
  intro hv
  by_cases hpos : 0 < g.current_step
  · unfold isValid at hv
    obtain ⟨q, hq, _⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv 0 (mem_intRange (Int.le_refl 0) (by omega)))
    obtain ⟨S, hc, _⟩ := onClique_self h hq
    exact ⟨S, hc⟩
  · refine ⟨fun _ => ({ id := (⟨0, 0⟩ : NodeId), parent_id := none } : PathNodeId), ⟨fun k _ h1 => absurd h1 (by omega), fun k _ h1 => absurd h1 (by omega),
      fun k _ _ h1 _ _ => absurd h1 (by omega), fun h0 => absurd h0 hpos, fun k _ h1 => absurd h1 (by omega)⟩⟩

-- ============================================================
-- DocsAlive: todo documento está vivo
-- ============================================================

def DocsAlive (g : GPathB) : Prop := ∀ n ∈ g.nodes, n.id ∈ g.alive

theorem ownersOk_of_isValidNode {g : GPathB} {n : PNodeB} (h : g.isValidNode n = true) : g.ownersOk n.id = true := by
  unfold isValidNode at h
  simp only at h
  split at h
  · split at h
    · exact h
    · exact (Bool.and_eq_true_iff.mp h).1
  · split at h
    · exact (Bool.and_eq_true_iff.mp h).1
    · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

theorem alive_of_isValidNode {g : GPathB} {n : PNodeB} (h : g.isValidNode n = true) : n.id ∈ g.alive := by
  have := ownersOk_of_isValidNode h
  unfold ownersOk isAlive at this
  exact List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp this).1

/-- Una vuelta de purga que no enciende `dirty` no quitó nada, y todo lo que miró era válido. -/
theorem purge_foldl_clean :
    ∀ (l : List PathNodeId) (g : GPathB), g.dirty = false → (l.foldl purgeStep g).dirty = false →
      l.foldl purgeStep g = g ∧ ∀ id ∈ l, ∀ n, g.node? id = some n → g.isValidNode n = true := by
  intro l
  induction l with
  | nil => intro g _ _; exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | cons a as ih =>
    intro g hg hd
    simp only [List.foldl_cons] at hd ⊢
    have hstep : g.purgeStep a = g ∧ ∀ n, g.node? a = some n → g.isValidNode n = true := by
      cases hn : g.node? a with
      | none =>
        exact ⟨by unfold purgeStep; rw [hn], fun n h => by cases h⟩
      | some n =>
        by_cases hv : g.isValidNode n = true
        · refine ⟨by unfold purgeStep; rw [hn]; simp [hv], fun m hm => ?_⟩
          cases hm; exact hv
        · exfalso
          have hpd : (g.purgeStep a).dirty = true := by
            unfold purgeStep; rw [hn]; simp [hv]
          have := keepsDirty_foldl purgeStep keepsDirty_purgeStep as _ hpd
          rw [this] at hd; cases hd
    rw [hstep.1] at hd ⊢
    obtain ⟨he, hall⟩ := ih g hg hd
    exact ⟨he, fun id hid n hn => by
      rcases List.mem_cons.mp hid with rfl | hid
      · exact hstep.2 n hn
      · exact hall id hid n hn⟩

theorem docsAlive_of_purgeRound_clean {g : GPathB} (hg : g.dirty = false) (hd : g.purgeRound.dirty = false) :
    g.purgeRound = g ∧ DocsAlive g := by
  obtain ⟨he, hall⟩ := purge_foldl_clean (g.nodes.map (fun n => n.id)) g hg (by unfold purgeRound at hd; exact hd)
  refine ⟨by unfold purgeRound; exact he, fun n hn => ?_⟩
  cases hf : g.node? n.id with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf n hn
    simp at this
  | some m =>
    have hv := hall n.id (List.mem_map.mpr ⟨n, hn, rfl⟩) m hf
    rw [← node?_id hf]
    exact alive_of_isValidNode hv

theorem purgeFuel_docs (m : Nat) {g : GPathB} (hg : g.dirty = false) (hd : (purgeFuel (m + 1) g).dirty = false)
    (hv : (purgeFuel (m + 1) g).isValid = true) : DocsAlive (purgeFuel (m + 1) g) := by
  by_cases hval : g.isValid = true
  · by_cases hlt : g.purgeRound.nodes.length < g.nodes.length
    · exfalso
      have he : purgeFuel (m + 1) g = purgeFuel m g.purgeRound := by simp [purgeFuel, hval, hlt]
      rw [he] at hd
      cases hr : g.purgeRound.dirty
      · have := (docsAlive_of_purgeRound_clean hg hr).1
        rw [this] at hlt; exact Nat.lt_irrefl _ hlt
      · rw [keepsDirty_purgeFuel m _ hr] at hd; cases hd
    · have he : purgeFuel (m + 1) g = g.purgeRound := by simp [purgeFuel, hval, hlt]
      rw [he] at hd ⊢
      obtain ⟨he', hda⟩ := docsAlive_of_purgeRound_clean hg hd
      rw [he']; exact hda
  · have he : purgeFuel (m + 1) g = g := by simp [purgeFuel, hval]
    rw [he] at hv; exact absurd hv hval

/-- **Una purga que termina válida y sin `dirty`** deja todo documento vivo. -/
theorem docsAlive_clean {g : GPathB} (hg : g.dirty = false) (hd : g.clean.dirty = false)
    (hv : g.clean.isValid = true) : DocsAlive g.clean := by
  unfold clean at hd hv ⊢
  exact purgeFuel_docs _ hg hd hv

/-- Los enlaces no cambian los ids de los documentos. -/
theorem pruneLinks_ids (g : GPathB) : ∀ n ∈ g.pruneLinks.nodes, ∃ m ∈ g.nodes, m.id = n.id := by
  intro n hn
  unfold pruneLinks at hn
  split at hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    exact ⟨m, hm, rfl⟩
  · exact ⟨n, hn, rfl⟩

theorem docsAlive_congr {g h : GPathB} (hg : DocsAlive g) (ha : h.alive = g.alive)
    (hids : ∀ n ∈ h.nodes, ∃ m ∈ g.nodes, m.id = n.id) : DocsAlive h := by
  intro n hn
  obtain ⟨m, hm, hid⟩ := hids n hn
  rw [ha, ← hid]; exact hg m hm

/-- **Una vuelta que empieza y termina sin `dirty`, válida**, deja todo documento vivo. -/
theorem docsAlive_reviewPass {g : GPathB} (hg : g.dirty = false) (hd : g.reviewPass.dirty = false)
    (hv : g.reviewPass.isValid = true) : DocsAlive g.reviewPass := by
  obtain ⟨hc, ha, _, hs⟩ := reviewPass_clean hd
  have hvc : g.cleanPair.isValid = true := by rw [← isValid_congr ha hs]; exact hv
  have hcp : g.cleanPair = g.clean := by
    have hc' := hc; have hvc' := hvc
    rw [cleanPair_eq] at hc' hvc' ⊢
    exact (pairFuel_clean _ _ hc' hvc').1
  have hcl : g.clean.dirty = false := by rw [← hcp]; exact hc
  have hvcl : g.clean.isValid = true := by rw [← hcp]; exact hvc
  have hda := docsAlive_clean hg hcl hvcl
  rw [← hcp] at hda
  unfold reviewPass at hd ⊢
  have h3 := not_dirty_of keepsDirty_pruneLinks hd
  have h2 := not_dirty_of keepsDirty_reviewSons h3
  have h1 := not_dirty_of keepsDirty_reviewParents h2
  rw [reviewParents_of_clean h1, reviewSons_of_clean h1]
  have hids : ∀ n ∈ g.cleanPair.pruneLinks.pruneLinks.nodes, ∃ m ∈ g.cleanPair.nodes, m.id = n.id := by
    intro n hn
    obtain ⟨m, hm, hmid⟩ := pruneLinks_ids _ n hn
    obtain ⟨m', hm', hm'id⟩ := pruneLinks_ids _ m hm
    exact ⟨m', hm', hm'id.trans hmid⟩
  have ha' : g.cleanPair.pruneLinks.pruneLinks.alive = g.cleanPair.alive := by
    rw [(pruneLinks_graph _).1, (pruneLinks_graph _).1]
  exact docsAlive_congr hda ha' hids

/-- El review deja la entrada tal cual, o todo documento vivo. -/
theorem reviewFuel_docs :
    ∀ (n : Nat) (g : GPathB), (reviewFuel n g).isValid = true → (reviewFuel n g).dirty = false →
      reviewFuel n g = g ∨ DocsAlive (reviewFuel n g) := by
  intro n
  induction n with
  | zero => intro g _ _; exact Or.inl rfl
  | succ n ih =>
    intro g hv hd
    by_cases h : (g.isValid && g.dirty) = true
    · cases hpd : (reviewPass { g with dirty := false }).dirty
      · by_cases hvp : (reviewPass { g with dirty := false }).isValid = true
        · cases hfd : (finalPass (reviewPass { g with dirty := false })).dirty
          · rw [reviewFuel_done h hpd hvp hfd]
            exact Or.inr (docsAlive_reviewPass rfl hpd hvp)
          · rw [reviewFuel_final h hpd hvp hfd] at hv hd ⊢
            rcases ih _ hv hd with he | hda
            · rw [he, hfd] at hd; cases hd
            · exact Or.inr hda
        · rw [reviewFuel_invalid h hpd hvp] at hv; exact absurd hv hvp
      · rw [reviewFuel_pass h hpd] at hv hd ⊢
        rcases ih _ hv hd with he | hda
        · rw [he, hpd] at hd; cases hd
        · exact Or.inr hda
    · exact Or.inl (reviewFuel_skip h)

/-- **El review válido deja todo documento vivo** si la entrada ya lo cumplía o tenía algo que revisar. -/
theorem docsAlive_review {g : GPathB} (hv : g.review.isValid = true) (h : DocsAlive g ∨ g.dirty = true) :
    DocsAlive g.review := by
  have hr : g.review = reviewFuel (g.measure + 1) g := rfl
  have hc := review_exits_clean g hv
  rw [hr] at hv hc ⊢
  rcases reviewFuel_docs _ g hv hc with he | hda
  · rcases h with hg | hg
    · rw [he]; exact hg
    · rw [he, hg] at hc; cases hc
  · exact hda

theorem keepsDirty_filterRequire (r : NodeId) : KeepsDirty (fun g => g.filterRequire r) := by
  intro g hg
  show (g.filterRequire r).dirty = true
  unfold filterRequire
  by_cases hv : g.isValid = true
  · rw [if_pos hv]
    dsimp only
    rw [keepsDirty_foldl killVertex keepsDirty_killVertex _ g hg]
    rfl
  · rw [if_neg hv]; exact hg

/-- Un `filterRequire` que no enciende `dirty` no mata a nadie. -/
theorem filterRequire_clean {g : GPathB} {r : NodeId} (hd : (g.filterRequire r).dirty = false) :
    (g.filterRequire r).alive = g.alive ∧ (g.filterRequire r).nodes = g.nodes := by
  unfold filterRequire at hd ⊢
  by_cases hv : g.isValid = true
  · rw [if_pos hv] at hd ⊢
    dsimp only at hd ⊢
    generalize (List.filter (fun q => q.id != r) (List.map (fun x => x.id) (g.line r.step))) = victims at hd ⊢
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hd
    rw [hd.2]
    exact ⟨rfl, rfl⟩
  · rw [if_neg hv]; exact ⟨rfl, rfl⟩

theorem filterRequires_clean :
    ∀ (reqs : List NodeId) (g : GPathB), (reqs.foldl filterRequire g).dirty = false →
      (reqs.foldl filterRequire g).alive = g.alive ∧ (reqs.foldl filterRequire g).nodes = g.nodes := by
  intro reqs
  induction reqs with
  | nil => intro g _; exact ⟨rfl, rfl⟩
  | cons r rs ih =>
    intro g hd
    simp only [List.foldl_cons] at hd ⊢
    have h1 : (g.filterRequire r).dirty = false := by
      cases hr : (g.filterRequire r).dirty
      · rfl
      · have := keepsDirty_foldl filterRequire keepsDirty_filterRequire rs _ hr
        rw [this] at hd; cases hd
    obtain ⟨ha, hn⟩ := ih _ hd
    obtain ⟨ha', hn'⟩ := filterRequire_clean h1
    exact ⟨ha.trans ha', hn.trans hn'⟩

/-- **El filtro válido conserva `DocsAlive`** (sobre un estado sin `dirty`). -/
theorem docsAlive_filterAll {g : GPathB} (hda : DocsAlive g) (reqs : List NodeId)
    (hv : (g.filterAll reqs).isValid = true) : DocsAlive (g.filterAll reqs) := by
  unfold filterAll at hv ⊢
  apply docsAlive_review hv
  cases hd : (reqs.foldl filterRequire g).dirty
  · obtain ⟨ha, hn⟩ := filterRequires_clean reqs g hd
    exact Or.inl (fun n hnm => by rw [ha]; rw [hn] at hnm; exact hda n hnm)
  · exact Or.inr rfl

theorem docsAlive_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (h : DocsAlive g) : DocsAlive (g.addNode d title forb) := by
  intro n hn
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    exact List.mem_append_left _ (h m hm)
  · obtain ⟨pid, hpid, rfl⟩ := List.mem_map.mp hn
    exact List.mem_append_right _ hpid

theorem docsAlive_join {g₁ g₂ : GPathB} (h₁ : DocsAlive g₁) (h₂ : DocsAlive g₂) : DocsAlive (join g₁ g₂) := by
  intro n hn
  rw [alive_join]
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    have := h₁ m hm
    exact Or.inl (by split <;> exact this)
  · exact Or.inr (h₂ n (List.mem_filter.mp hn).1)

end GPathB

end AbsSatBingo.Model
