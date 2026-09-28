-- lean/improves_bingo/AbsSatBingo/Tagged/Carried.lean
import AbsSatBingo.Tagged.Defs
import AbsSatBingo.Model.Machine

/-!
# La camarilla de una solución lleva su clave en cada fila (fase T2 de `docs/plans/lean_row_tags.md`)

**`TagCarried tg S`**: la camarilla `S` está viva en `tg.g` (`Carried`), y cada par de la camarilla lleva, en cada fila
de claves `ℓ < krows`, la clave por la que pasa: el nodo del mapa de `S ℓ`.

Aquí, lo local: `S` está en su propia pieza (`padj_onS`), y por eso la regla de la etiqueta no le quita nada
(`tagKeeps_onS`, `tagSweep_keeps`), ni `tagCut` le quita un nodo o una arista (`carried_tagCut`). Es el argumento de
solidez del informe v204 §7.3: los testigos, padres e hijos que la regla pide son los de la propia camarilla.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace TGPath

open GPathB

/-- Los pares de la camarilla llevan, en cada fila `ℓ < krows`, la clave de la camarilla en esa fila. -/
def CliqueTags (cs : Int) (S : Int → PathNodeId) (krows : Int) (T : List TagE) : Prop :=
  ∀ ℓ, 0 ≤ ℓ → ℓ < krows → ∀ k l, 0 ≤ k → k < cs → 0 ≤ l → l < cs → hasTag T (S k) (S l) ℓ (S ℓ).id = true

/-- **La camarilla está viva y en su pieza en cada fila.** -/
structure TagCarried (tg : TGPath) (S : Int → PathNodeId) : Prop where
  carried : Carried tg.g S
  tags    : CliqueTags tg.g.current_step S tg.krows tg.tags

-- ============================================================
-- Etiquetas: monotonía
-- ============================================================

theorem hasTag_append_left {T U : List TagE} {x w : PathNodeId} {ℓ : Int} {a : NodeId}
    (h : hasTag T x w ℓ a = true) : hasTag (T ++ U) x w ℓ a = true := by
  unfold hasTag at *; rw [List.any_append, h]; rfl

theorem hasTag_append_right {T U : List TagE} {x w : PathNodeId} {ℓ : Int} {a : NodeId}
    (h : hasTag U x w ℓ a = true) : hasTag (T ++ U) x w ℓ a = true := by
  unfold hasTag at *; rw [List.any_append, h]; simp

theorem mem_tagStep {T : List TagE} {u e : TagE} :
    e ∈ (if T.contains u then T else T ++ [u]) ↔ e ∈ T ∨ e = u := by
  split
  · rename_i h
    exact ⟨Or.inl, fun h' => h'.elim id (fun he => by subst he; exact List.contains_iff_mem.mp h)⟩
  · simp

theorem mem_tagUnion {e : TagE} : ∀ {T U : List TagE}, e ∈ tagUnion T U ↔ e ∈ T ∨ e ∈ U := by
  intro T U
  induction U generalizing T with
  | nil => simp [tagUnion]
  | cons u us ih =>
    unfold tagUnion at ih ⊢
    rw [List.foldl_cons, ih, mem_tagStep, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem hasTag_tagUnion {T U : List TagE} {x w : PathNodeId} {ℓ : Int} {a : NodeId} :
    hasTag (tagUnion T U) x w ℓ a = true ↔ hasTag T x w ℓ a = true ∨ hasTag U x w ℓ a = true := by
  unfold hasTag
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨e, he, h⟩
    rcases mem_tagUnion.mp he with he | he
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact ⟨e, mem_tagUnion.mpr (Or.inl he), h⟩
    · exact ⟨e, mem_tagUnion.mpr (Or.inr he), h⟩

theorem hasTag_tagUnion_left {T U : List TagE} {x w : PathNodeId} {ℓ : Int} {a : NodeId}
    (h : hasTag T x w ℓ a = true) : hasTag (tagUnion T U) x w ℓ a = true := hasTag_tagUnion.mpr (Or.inl h)

theorem hasTag_tagUnion_right {T U : List TagE} {x w : PathNodeId} {ℓ : Int} {a : NodeId}
    (h : hasTag U x w ℓ a = true) : hasTag (tagUnion T U) x w ℓ a = true := hasTag_tagUnion.mpr (Or.inr h)

theorem cliqueTags_mono {cs : Int} {S : Int → PathNodeId} {krows : Int} {T U : List TagE}
    (h : CliqueTags cs S krows T) (hsub : ∀ {x w ℓ a}, hasTag T x w ℓ a = true → hasTag U x w ℓ a = true) :
    CliqueTags cs S krows U :=
  fun ℓ h0 h1 k l hk0 hk1 hl0 hl1 => hsub (h ℓ h0 h1 k l hk0 hk1 hl0 hl1)

theorem hasTag_symm {T : List TagE} {x w : PathNodeId} {ℓ : Int} {a : NodeId} :
    hasTag T x w ℓ a = hasTag T w x ℓ a := by
  unfold hasTag tagOn
  congr 1; funext e
  cases (e.1 == x) <;> cases (e.2.1 == w) <;> cases (e.1 == w) <;> cases (e.2.1 == x) <;> rfl

-- ============================================================
-- La camarilla está en su propia pieza
-- ============================================================

section onS
variable {g : GPathB} {T : List TagE} {S : Int → PathNodeId} {krows : Int}

theorem padj_onS (hc : Carried g S) (ht : CliqueTags g.current_step S krows T) {ℓ : Int} (h0 : 0 ≤ ℓ)
    (h1 : ℓ < krows) {x w : PathNodeId} (hx : OnS g.current_step S x) (hw : OnS g.current_step S w) :
    padj g T ℓ (S ℓ).id x w = true := by
  obtain ⟨k, hk0, hk1, rfl⟩ := hx
  obtain ⟨l, hl0, hl1, rfl⟩ := hw
  unfold padj
  rw [Bool.and_eq_true]
  exact ⟨hc.adj k l hk0 hk1 hl0 hl1, ht ℓ h0 h1 k l hk0 hk1 hl0 hl1⟩

theorem onS_self (_hc : Carried g S) {k : Int} (h0 : 0 ≤ k) (h1 : k < g.current_step) :
    OnS g.current_step S (S k) := ⟨k, h0, h1, rfl⟩

/-- Un nodo de la camarilla tiene, en cada paso, el testigo de la camarilla en su pieza. -/
theorem witness_onS (hc : Carried g S) (ht : CliqueTags g.current_step S krows T) {ℓ : Int} (h0 : 0 ≤ ℓ)
    (h1 : ℓ < krows) {x w : PathNodeId} (hx : OnS g.current_step S x) (hw : OnS g.current_step S w) :
    (intRange 0 (g.current_step - 1)).all (fun k =>
      g.alive.any (fun r => r.id.step == k && padj g T ℓ (S ℓ).id x r && padj g T ℓ (S ℓ).id w r)) = true := by
  rw [List.all_eq_true]
  intro k hk
  obtain ⟨hk0, hk1⟩ := intRange_bounds hk
  have hk1' : k < g.current_step := by omega
  refine List.any_eq_true.mpr ⟨S k, hc.alive k hk0 hk1', ?_⟩
  have hs := onS_self hc hk0 hk1'
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨hc.step k hk0 hk1', padj_onS hc ht h0 h1 hx hs⟩, padj_onS hc ht h0 h1 hw hs⟩

/-- Los apoyos de un nodo de la camarilla hacia otro, dentro de la pieza: sus vecinos de la camarilla. -/
theorem supportIn_onS (hc : Carried g S) (ht : CliqueTags g.current_step S krows T) {ℓ : Int} (h0 : 0 ≤ ℓ)
    (h1 : ℓ < krows) {u v : PathNodeId} (hu : OnS g.current_step S u) (hv : OnS g.current_step S v) :
    supportIn g T ℓ (S ℓ).id u v = true := by
  obtain ⟨k, hk0, hk1, rfl⟩ := hu
  obtain ⟨n, hn, hpar, hson⟩ := hc.node k hk0 hk1
  unfold supportIn
  rw [hn]
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨?_, ?_⟩
  · by_cases hk : 0 < k
    · refine Or.inr (List.any_eq_true.mpr ⟨S (k - 1), hpar hk, ?_⟩)
      have hs := onS_self hc (k := k - 1) (by omega) (by omega)
      rw [Bool.and_eq_true]
      exact ⟨padj_onS hc ht h0 h1 ⟨k, hk0, hk1, rfl⟩ hs, padj_onS hc ht h0 h1 hs hv⟩
    · have hk' : k = 0 := by omega
      subst hk'
      exact Or.inl (by rw [hc.root (by omega)]; rfl)
  · by_cases hk : k + 1 < g.current_step
    · refine Or.inr (List.any_eq_true.mpr ⟨S (k + 1), hson hk, ?_⟩)
      have hs := onS_self hc (k := k + 1) (by omega) hk
      rw [Bool.and_eq_true]
      exact ⟨padj_onS hc ht h0 h1 ⟨k, hk0, hk1, rfl⟩ hs, padj_onS hc ht h0 h1 hs hv⟩
    · refine Or.inl ?_
      rw [hc.step k hk0 hk1, beq_iff_eq]; omega

theorem nodeKeeps_onS (hc : Carried g S) (ht : CliqueTags g.current_step S krows T) {ℓ : Int} (h0 : 0 ≤ ℓ)
    (h1 : ℓ < krows) {x : PathNodeId} (hx : OnS g.current_step S x) :
    nodeKeeps g T ℓ (S ℓ).id x = true := by
  have hw := witness_onS hc ht h0 h1 hx hx
  unfold nodeKeeps
  simp only [Bool.and_eq_true]
  refine ⟨⟨padj_onS hc ht h0 h1 hx hx, ?_⟩, supportIn_onS hc ht h0 h1 hx hx⟩
  rw [List.all_eq_true] at hw ⊢
  intro k hk
  obtain ⟨r, hr, hr'⟩ := List.any_eq_true.mp (hw k hk)
  simp only [Bool.and_eq_true] at hr'
  exact List.any_eq_true.mpr ⟨r, hr, by rw [Bool.and_eq_true]; exact ⟨hr'.1.1, hr'.1.2⟩⟩

theorem edgeKeeps_onS (hc : Carried g S) (ht : CliqueTags g.current_step S krows T) {ℓ : Int} (h0 : 0 ≤ ℓ)
    (h1 : ℓ < krows) {x w : PathNodeId} (hx : OnS g.current_step S x) (hw : OnS g.current_step S w) :
    edgeKeeps g T ℓ (S ℓ).id x w = true := by
  unfold edgeKeeps
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨padj_onS hc ht h0 h1 hx hx, padj_onS hc ht h0 h1 hw hw⟩, padj_onS hc ht h0 h1 hx hw⟩,
    witness_onS hc ht h0 h1 hx hw⟩, supportIn_onS hc ht h0 h1 hx hw⟩, supportIn_onS hc ht h0 h1 hw hx⟩

/-- **La regla no quita una etiqueta de la camarilla**: la de un par de `S` con la clave de `S` en su fila. -/
theorem tagKeeps_onS (hc : Carried g S) (ht : CliqueTags g.current_step S krows T) {e : TagE}
    (h0 : 0 ≤ e.2.2.1) (h1 : e.2.2.1 < krows) (hkey : e.2.2.2 = (S e.2.2.1).id)
    (hx : OnS g.current_step S e.1) (hw : OnS g.current_step S e.2.1) : tagKeeps g T e = true := by
  unfold tagKeeps
  rw [hkey]
  split
  · exact nodeKeeps_onS hc ht h0 h1 hx
  · exact edgeKeeps_onS hc ht h0 h1 hx hw

end onS

-- ============================================================
-- La pasada de la regla y el corte conservan la camarilla
-- ============================================================

theorem tagOn_iff {x w : PathNodeId} {ℓ : Int} {e : TagE} :
    tagOn x w ℓ e = true ↔ ((e.1 = x ∧ e.2.1 = w) ∨ (e.1 = w ∧ e.2.1 = x)) ∧ e.2.2.1 = ℓ := by
  unfold tagOn; simp [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]

theorem hasTag_iff {T : List TagE} {x w : PathNodeId} {ℓ : Int} {a : NodeId} :
    hasTag T x w ℓ a = true ↔ ∃ e ∈ T, ((e.1 = x ∧ e.2.1 = w) ∨ (e.1 = w ∧ e.2.1 = x)) ∧ e.2.2.1 = ℓ ∧ e.2.2.2 = a := by
  unfold hasTag
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, he, h⟩
    rw [Bool.and_eq_true, tagOn_iff, beq_iff_eq] at h
    exact ⟨e, he, h.1.1, h.1.2, h.2⟩
  · rintro ⟨e, he, h1, h2, h3⟩
    exact ⟨e, he, by rw [Bool.and_eq_true, tagOn_iff, beq_iff_eq]; exact ⟨⟨h1, h2⟩, h3⟩⟩

/-- **La pasada de la regla conserva las etiquetas de la camarilla.** -/
theorem cliqueTags_tagSweep {g : GPathB} {T : List TagE} {S : Int → PathNodeId} {krows : Int}
    (hc : Carried g S) (ht : CliqueTags g.current_step S krows T) :
    CliqueTags g.current_step S krows (tagSweep g T) := by
  intro ℓ h0 h1 k l hk0 hk1 hl0 hl1
  obtain ⟨e, he, hxw, hℓ, ha⟩ := hasTag_iff.mp (ht ℓ h0 h1 k l hk0 hk1 hl0 hl1)
  refine hasTag_iff.mpr ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, hxw, hℓ, ha⟩
  have hsk := onS_self hc hk0 hk1
  have hsl := onS_self hc hl0 hl1
  subst hℓ
  rcases hxw with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact tagKeeps_onS hc ht h0 h1 ha (h1' ▸ hsk) (h2' ▸ hsl)
  · exact tagKeeps_onS hc ht h0 h1 ha (h1' ▸ hsl) (h2' ▸ hsk)

theorem hasRow_of_hasTag {T : List TagE} {x w : PathNodeId} {ℓ : Int} {a : NodeId}
    (h : hasTag T x w ℓ a = true) : hasRow T x w ℓ = true := by
  obtain ⟨e, he, hxw, hℓ, _⟩ := hasTag_iff.mp h
  exact List.any_eq_true.mpr ⟨e, he, tagOn_iff.mpr ⟨hxw, hℓ⟩⟩

/-- Los pares de la camarilla tienen clave en todas las filas. -/
theorem rows_onS {cs : Int} {S : Int → PathNodeId} {krows : Int} {T : List TagE} (ht : CliqueTags cs S krows T)
    {k l : Int} (hk0 : 0 ≤ k) (hk1 : k < cs) (hl0 : 0 ≤ l) (hl1 : l < cs) :
    (intRange 0 (krows - 1)).all (hasRow T (S k) (S l)) = true := by
  rw [List.all_eq_true]
  intro ℓ hℓ
  obtain ⟨h0, h1⟩ := intRange_bounds hℓ
  exact hasRow_of_hasTag (ht ℓ h0 (by omega) k l hk0 hk1 hl0 hl1)

theorem current_step_foldl_killVertex (l : List PathNodeId) :
    ∀ g : GPathB, (l.foldl killVertex g).current_step = g.current_step := by
  induction l with
  | nil => intro g; rfl
  | cons a as ih => intro g; simp only [List.foldl_cons]; rw [ih]; rfl

/-- **El corte de la regla conserva la camarilla**: sus nodos y aristas tienen clave en todas las filas. -/
theorem carried_tagCut {g : GPathB} {T : List TagE} {S : Int → PathNodeId} {krows : Int}
    (hc : Carried g S) (ht : CliqueTags g.current_step S krows T) : Carried (tagCut g T krows) S := by
  unfold tagCut
  simp only
  let dead := g.alive.filter (fun x => !(intRange 0 (krows - 1)).all (hasRow T x x))
  have hnd : ∀ x ∈ dead, ¬ OnS g.current_step S x := by
    rintro x hx ⟨k, hk0, hk1, rfl⟩
    have := (List.mem_filter.mp hx).2
    rw [rows_onS ht hk0 hk1 hk0 hk1] at this
    exact absurd this (by decide)
  have hk := carried_foldl (cs := g.current_step) killVertex dead
    (fun g' a ha hc' hcs => ⟨carried_killVertex hc' (hcs ▸ hnd a ha), hcs⟩) g hc rfl
  obtain ⟨hk1, hk2⟩ := hk
  refine ⟨hk1.step, hk1.alive, ?_, hk1.root, hk1.node⟩
  intro k l h0 h1 h2 h3
  have hadj := hk1.adj k l h0 h1 h2 h3
  rw [adj_iff] at hadj ⊢
  rcases hadj with h | ⟨e, he, hj⟩
  · exact Or.inl h
  · refine Or.inr ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, hj⟩
    have hk1' : k < g.current_step := hk2 ▸ h1
    have hl1' : l < g.current_step := hk2 ▸ h3
    rcases hj with ⟨he1, he2⟩ | ⟨he1, he2⟩
    · rw [he1, he2]; exact rows_onS ht h0 hk1' h2 hl1'
    · rw [he1, he2]; exact rows_onS ht h2 hl1' h0 hk1'

end TGPath

end AbsSatBingo.Model
