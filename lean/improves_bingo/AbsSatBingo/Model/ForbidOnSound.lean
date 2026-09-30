-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnSound.lean
import AbsSatBingo.Model.ForbidOnIdx
import AbsSatBingo.Model.ForbidOnClosed
import AbsSatBingo.Model.ForbidSound
import AbsSatBingo.Model.Grow
import AbsSatBingo.Model.ReaderFinal

/-!
# Los tríos de la máquina `:on` son sólidos (`docs/plans/lean_forbid_on.md`, F3)

**`TF g`**: los tríos que guarda `g`, como relación: `a ≠ b` y `deadTrio g a b r` (Julia `dead_trio`, que solo se
consulta sobre una arista). **`CarriedT g S`**: `g` lleva la rama `S` y `S` no pasa por ningún trío de `TF g`.

Cada operación `:on` conserva `CarriedT`. Una rama que pasa por los tres nodos de un trío es testigo bueno de él en
cada paso, así que la regla no lo prohíbe, y por lo mismo no corta sus aristas. El UP prohíbe `(n, w, r)` solo si todo
padre de `n` corta `(p, w, r)`, pero el padre de la rama no lo corta. El join prohíbe lo que cortan los dos lados, y el
lado de la rama no lo corta.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- **Los tríos de `g`** (Julia `dead_trio`, sobre una arista `a–b` de dos nodos distintos). -/
def TF (g : GPathB) : Trios := fun a b r => a ≠ b ∧ g.deadTrio a b r = true

/-- Ninguna arista une un nodo consigo mismo. -/
def NoSelf (g : GPathB) : Prop := ∀ e ∈ g.edges, e.1 ≠ e.2

variable {S : Int → PathNodeId}

-- ============================================================
-- NoSelf
-- ============================================================

theorem hasEdge_self_false {g : GPathB} (h : NoSelf g) (a : PathNodeId) : g.hasEdge a a = false := by
  cases hc : g.hasEdge a a
  · rfl
  · exfalso
    obtain ⟨e, he, hj⟩ := List.any_eq_true.mp hc
    have := (joins_iff a a e).mp hj
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h e he (h1.trans h2.symm)

theorem revPrims_noSelf : RevPrims NoSelf := by
  refine ⟨?_, ?_, ?_, fun _ _ h => h, ?_⟩
  · intro g id h e he; exact h e (List.mem_filter.mp he).1
  · intro g x w h e he; exact h e (List.mem_filter.mp he).1
  · intro g id h e he; exact h e (List.mem_filter.mp he).1
  · intro g h
    unfold pruneLinks; split
    · exact h
    · exact h

theorem trioBlind_noSelf : TrioBlind NoSelf := fun _ _ h => h

-- ============================================================
-- Tríos: monotonía y escritura
-- ============================================================

/-- En un subestado con los mismos tríos, hay menos tríos prohibidos. -/
theorem tF_sub {h g : GPathB} (hs : Sub h g) (ht : h.trios = g.trios) {a b r : PathNodeId} (hf : TF h a b r) :
    TF g a b r := by
  obtain ⟨hab, hd⟩ := hf
  refine ⟨hab, ?_⟩
  unfold deadTrio at hd ⊢
  rw [Bool.and_eq_true] at hd ⊢
  refine ⟨?_, by rw [← ht]; exact hd.2⟩
  have hadj : h.Adj a b := by unfold Adj adjb; simp [hd.1]
  have := hs.adj a b hadj
  unfold Adj adjb at this
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  rcases this with ⟨h1, _⟩ | h1
  · exact absurd h1 hab
  · exact h1

theorem avoids_sub {h g : GPathB} (hs : Sub h g) (ht : h.trios = g.trios) {T : Int} (hA : Avoids (TF g) T S) :
    Avoids (TF h) T S :=
  fun i j k h0 h1 h2 h3 h4 h5 hf => hA i j k h0 h1 h2 h3 h4 h5 (tF_sub hs ht hf)

/-- Las componentes de un trío `{a, b, r}` son `a`, `b` o `r`. -/
theorem trioIs_mem {a b r : PathNodeId} {t : PathNodeId × PathNodeId × PathNodeId} (h : trioIs a b r t = true) :
    (t.1 = a ∨ t.1 = b ∨ t.1 = r) ∧ (t.2.1 = a ∨ t.2.1 = b ∨ t.2.1 = r) ∧ (t.2.2 = a ∨ t.2.2 = b ∨ t.2.2 = r) := by
  obtain ⟨x, y, z⟩ := t
  simp only [trioIs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (((((⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) |
    ⟨⟨h1, h2⟩, h3⟩) <;> simp [h1, h2, h3]

/-- Lo que escribe `addTrios`: los tríos de antes y algunos de la lista. -/
theorem mem_addTrios (g : GPathB) (i : Idx) (ts : List (PathNodeId × PathNodeId × PathNodeId))
    (t : PathNodeId × PathNodeId × PathNodeId) (ht : t ∈ (g.addTrios i ts).1.trios) : t ∈ g.trios ∨ t ∈ ts := by
  unfold addTrios at ht
  simp only [List.mem_append, List.mem_reverse] at ht
  rcases ht with h | h
  · exact Or.inl h
  · right
    -- el acumulador solo junta elementos de la lista
    have key : ∀ (l : List (PathNodeId × PathNodeId × PathNodeId))
        (acc : List (PathNodeId × PathNodeId × PathNodeId) × Std.HashSet (PathNodeId × PathNodeId × PathNodeId)),
        (∀ x ∈ acc.1, x ∈ ts) → (∀ x ∈ l, x ∈ ts) →
        ∀ x ∈ (l.foldl (fun (acc : List (PathNodeId × PathNodeId × PathNodeId) ×
            Std.HashSet (PathNodeId × PathNodeId × PathNodeId)) t =>
          if acc.2.contains t || i.deadTrio t.1 t.2.1 t.2.2 then acc
          else (t :: acc.1, acc.2.insertMany (perms t.1 t.2.1 t.2.2))) acc).1, x ∈ ts := by
      intro l
      induction l with
      | nil => intro acc hacc _; exact hacc
      | cons y ys ih =>
        intro acc hacc hl
        rw [List.foldl_cons]
        apply ih _ _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        split
        · exact hacc
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hl x List.mem_cons_self
          · exact hacc x hx
    exact key ts ([], {}) (fun _ h => absurd h (List.not_mem_nil)) (fun _ h => h) t h

theorem addTrios_edges (g : GPathB) (i : Idx) (ts : List (PathNodeId × PathNodeId × PathNodeId)) :
    (g.addTrios i ts).1.edges = g.edges := rfl

theorem addTrios_step (g : GPathB) (i : Idx) (ts : List (PathNodeId × PathNodeId × PathNodeId)) :
    (g.addTrios i ts).1.current_step = g.current_step := rfl

/-- **Escribir tríos que la rama no recorre entera conserva que la rama los esquive.** -/
theorem avoids_addTrios {g : GPathB} {T : Int} (hA : Avoids (TF g) T S) (i : Idx)
    (ts : List (PathNodeId × PathNodeId × PathNodeId))
    (hts : ∀ t ∈ ts, ¬ (OnS T S t.1 ∧ OnS T S t.2.1 ∧ OnS T S t.2.2)) :
    Avoids (TF (g.addTrios i ts).1) T S := by
  intro p q r' h0 h1 h2 h3 h4 h5 ⟨hne, hd⟩
  unfold deadTrio at hd
  rw [Bool.and_eq_true] at hd
  have hE : (g.addTrios i ts).1.hasEdge (S p) (S q) = g.hasEdge (S p) (S q) := rfl
  rw [hE] at hd
  obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd.2
  rcases mem_addTrios g i ts t ht with hold | hnew
  · exact hA p q r' h0 h1 h2 h3 h4 h5 ⟨hne, by
      unfold deadTrio; rw [Bool.and_eq_true]; exact ⟨hd.1, List.any_eq_true.mpr ⟨t, hold, hti⟩⟩⟩
  · apply hts t hnew
    obtain ⟨c1, c2, c3⟩ := trioIs_mem hti
    have on : ∀ x, (x = S p ∨ x = S q ∨ x = S r') → OnS T S x := by
      rintro x (rfl | rfl | rfl)
      · exact ⟨p, h0, h1, rfl⟩
      · exact ⟨q, h2, h3, rfl⟩
      · exact ⟨r', h4, h5, rfl⟩
    exact ⟨on _ c1, on _ c2, on _ c3⟩

-- ============================================================
-- La rama es testigo bueno: la regla no prohíbe sus tríos ni corta sus aristas
-- ============================================================

theorem hasEdge_of_adj {g : GPathB} {x w : PathNodeId} (h : g.Adj x w) (hne : x ≠ w) : g.hasEdge x w = true := by
  unfold Adj adjb at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨h1, _⟩ | h1
  · exact absurd h1 hne
  · exact h1

/-- Un trío de nodos de la rama no está guardado. -/
theorem not_dead_of_avoids {g : GPathB} (hA : Avoids (TF g) g.current_step S) (hns : NoSelf g) {x y z : PathNodeId}
    (hx : OnS g.current_step S x) (hy : OnS g.current_step S y) (hz : OnS g.current_step S z) :
    g.deadTrio x y z = false := by
  cases hd : g.deadTrio x y z
  · rfl
  · exfalso
    by_cases hxy : x = y
    · subst hxy
      unfold deadTrio at hd
      rw [hasEdge_self_false hns] at hd; cases hd
    · obtain ⟨i, h0, h1, rfl⟩ := hx
      obtain ⟨j, h2, h3, rfl⟩ := hy
      obtain ⟨k, h4, h5, rfl⟩ := hz
      exact hA i j k h0 h1 h2 h3 h4 h5 ⟨hxy, hd⟩

/-- El nodo de la rama en el paso `l` es vecino de `a` en ese paso (Julia `inc[a][l]`). -/
theorem mem_incAt_of_onS {g : GPathB} (hc : Carried g S) {a : PathNodeId} (ha : OnS g.current_step S a) {l : Int}
    (h0 : 0 ≤ l) (h1 : l < g.current_step) : S l ∈ (Idx.of g).incAt a l := by
  have hSl : OnS g.current_step S (S l) := ⟨l, h0, h1, rfl⟩
  unfold Idx.incAt
  by_cases he : S l = a
  · apply List.mem_append_left
    have hst : a.id.step = l := by rw [← he]; exact hc.step l h0 h1
    have hal : a ∈ g.alive := by rw [← he]; exact hc.alive l h0 h1
    rw [if_pos (by simp [hst, (idx_alive g a).mpr hal])]
    rw [he]; exact List.mem_singleton_self _
  · apply List.mem_append_right
    rw [List.mem_filter, idx_mem_nbrs]
    refine ⟨⟨he, hc.alive l h0 h1, hasEdge_of_adj (hc.adj_on ha hSl) (fun h => he h.symm)⟩, ?_⟩
    simp [hc.step l h0 h1]

/-- **Un triángulo de la rama tiene testigo bueno en cada paso.** -/
theorem trioAlive_of_onS {g : GPathB} (hc : Carried g S) (hA : Avoids (TF g) g.current_step S) (hns : NoSelf g)
    {a b r : PathNodeId} (ha : OnS g.current_step S a) (hb : OnS g.current_step S b) (hr : OnS g.current_step S r) :
    (Idx.of g).trioAlive a b r = true := by
  unfold Idx.trioAlive
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨h0, h1⟩ := intRange_bounds hl
  have hcs : (Idx.of g).cs = g.current_step := rfl
  rw [hcs] at h1
  rw [List.any_eq_true]
  refine ⟨S l, mem_incAt_of_onS hc ha h0 (by omega), ?_⟩
  have hSl : OnS g.current_step S (S l) := ⟨l, h0, by omega, rfl⟩
  unfold Idx.goodWitness
  by_cases hw : (S l == a || S l == b || S l == r) = true
  · simp only [Bool.or_eq_true] at hw ⊢; rcases hw with (h | h) | h <;> simp [h]
  · simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hw
    obtain ⟨⟨hwa, hwb⟩, hwr⟩ := hw
    simp only [Bool.or_eq_true, beq_iff_eq, hwa, hwb, hwr, false_or, Bool.and_eq_true, Bool.not_eq_true',
      idx_hasEdge, idx_deadTrio]
    exact ⟨⟨⟨⟨⟨hasEdge_of_adj (hc.adj_on ha hSl) (fun h => hwa h.symm),
      hasEdge_of_adj (hc.adj_on hb hSl) (fun h => hwb h.symm)⟩,
      hasEdge_of_adj (hc.adj_on hr hSl) (fun h => hwr h.symm)⟩,
      not_dead_of_avoids hA hns ha hb hSl⟩, not_dead_of_avoids hA hns ha hr hSl⟩,
      not_dead_of_avoids hA hns hb hr hSl⟩

/-- **Una arista de la rama tiene testigo bueno en cada paso.** -/
theorem edgeAlive_of_onS {g : GPathB} (hc : Carried g S) (hA : Avoids (TF g) g.current_step S) (hns : NoSelf g)
    {x w : PathNodeId} (hx : OnS g.current_step S x) (hw : OnS g.current_step S w) :
    (Idx.of g).edgeAlive x w = true := by
  unfold Idx.edgeAlive
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨h0, h1⟩ := intRange_bounds hl
  have hcs : (Idx.of g).cs = g.current_step := rfl
  rw [hcs] at h1
  rw [List.any_eq_true]
  refine ⟨S l, mem_incAt_of_onS hc hx h0 (by omega), ?_⟩
  have hSl : OnS g.current_step S (S l) := ⟨l, h0, by omega, rfl⟩
  by_cases hq : (S l == x || S l == w) = true
  · simp only [Bool.or_eq_true] at hq ⊢; rcases hq with h | h <;> simp [h]
  · simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hq
    obtain ⟨hqx, hqw⟩ := hq
    simp only [Bool.or_eq_true, beq_iff_eq, hqx, hqw, false_or, Bool.and_eq_true, Bool.not_eq_true',
      idx_hasEdge, idx_deadTrio]
    exact ⟨hasEdge_of_adj (hc.adj_on hw hSl) (fun h => hqw h.symm), not_dead_of_avoids hA hns hx hw hSl⟩

/-- **La fase 1 no escribe tríos de la rama.** -/
theorem newTrios_notOnS {g : GPathB} (hc : Carried g S) (hA : Avoids (TF g) g.current_step S) (hns : NoSelf g) :
    ∀ t ∈ g.newTrios (Idx.of g),
      ¬ (OnS g.current_step S t.1 ∧ OnS g.current_step S t.2.1 ∧ OnS g.current_step S t.2.2) := by
  intro t ht ⟨h1, h2, h3⟩
  unfold newTrios at ht
  obtain ⟨e, _, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  have hr' := (List.mem_filter.mp hr).2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hr'
  rw [trioAlive_of_onS hc hA hns h1 h2 h3] at hr'
  exact absurd hr'.2 (by simp)

-- ============================================================
-- CT: la rama llevada y sin tríos
-- ============================================================

/-- **`g` lleva `S`, `S` esquiva los tríos de `g`, y no hay aristas de un nodo a sí mismo.** -/
def CT (g : GPathB) (S : Int → PathNodeId) : Prop :=
  Carried g S ∧ Avoids (TF g) g.current_step S ∧ NoSelf g

/-- Una operación que borra, lleva la rama y no toca los tríos conserva `CT`. -/
theorem ct_of_shrink {g h : GPathB} (hct : CT g S) (hc : Carried h S) (hs : Shrinks h g) (ht : h.trios = g.trios)
    (hns : NoSelf h) : CT h S := by
  refine ⟨hc, ?_, hns⟩
  rw [hs.1.step]
  exact avoids_sub hs.1 ht hct.2.1

theorem ct_setT {g : GPathB} (hct : CT g S) (T : List (PathNodeId × PathNodeId × PathNodeId))
    (hA : Avoids (TF (g.setT T)) g.current_step S) : CT (g.setT T) S :=
  ⟨⟨hct.1.step, hct.1.alive, hct.1.adj, hct.1.root, hct.1.node⟩, hA, hct.2.2⟩

-- Las operaciones del review `:off` no tocan los tríos.

theorem setT_self (g : GPathB) : g.setT g.trios = g := rfl


theorem trios_clean (g : GPathB) : g.clean.trios = g.trios := by
  have h := congrArg GPathB.trios (clean_setT g.trios g); rw [setT_self] at h; exact h
theorem trios_cleanPair (g : GPathB) : g.cleanPair.trios = g.trios := by
  have h := congrArg GPathB.trios (cleanPair_setT g.trios g); rw [setT_self] at h; exact h
theorem trios_pruneLinks (g : GPathB) : g.pruneLinks.trios = g.trios := by
  have h := congrArg GPathB.trios (pruneLinks_setT g.trios g); rw [setT_self] at h; exact h
theorem trios_reviewParents (g : GPathB) : g.reviewParents.trios = g.trios := by
  have h := congrArg GPathB.trios (reviewParents_setT g.trios g); rw [setT_self] at h; exact h
theorem trios_reviewSons (g : GPathB) : g.reviewSons.trios = g.trios := by
  have h := congrArg GPathB.trios (reviewSons_setT g.trios g); rw [setT_self] at h; exact h
theorem trios_finalPass (g : GPathB) : g.finalPass.trios = g.trios := by
  have h := congrArg GPathB.trios (finalPass_setT g.trios g); rw [setT_self] at h; exact h

theorem ct_clean {g : GPathB} (h : CT g S) : CT g.clean S :=
  ct_of_shrink h (carried_clean h.1) (shrinks_clean g) (trios_clean g) (revPrims_clean revPrims_noSelf g h.2.2)

theorem ct_cleanPair {g : GPathB} (h : CT g S) : CT g.cleanPair S :=
  ct_of_shrink h (carried_cleanPair h.1) (shrinks_cleanPair g) (trios_cleanPair g)
    (revPrims_cleanPair revPrims_noSelf g h.2.2)

theorem ct_pruneLinks {g : GPathB} (h : CT g S) : CT g.pruneLinks S :=
  ct_of_shrink h (carried_pruneLinks h.1) (shrinks_pruneLinks g) (trios_pruneLinks g)
    (revPrims_noSelf.links g h.2.2)

theorem ct_reviewParents {g : GPathB} (h : CT g S) : CT g.reviewParents S := by
  refine ct_of_shrink h (carried_reviewParents h.1) (shrinks_reviewParents g) (trios_reviewParents g) ?_
  unfold reviewParents; split
  · exact revPrims_reviewSteps revPrims_noSelf _ _ _ h.2.2
  · exact h.2.2

theorem ct_reviewSons {g : GPathB} (h : CT g S) : CT g.reviewSons S := by
  refine ct_of_shrink h (carried_reviewSons h.1) (shrinks_reviewSons g) (trios_reviewSons g) ?_
  unfold reviewSons; split
  · exact revPrims_reviewSteps revPrims_noSelf _ _ _ h.2.2
  · exact h.2.2

theorem ct_finalPass {g : GPathB} (h : CT g S) : CT g.finalPass S :=
  ct_of_shrink h (carried_finalPass h.1) (shrinks_finalPass g) (trios_finalPass g)
    (revPrims_finalPass revPrims_noSelf g h.2.2)

theorem ct_dirty {g : GPathB} (h : CT g S) (b : Bool) : CT { g with dirty := b } S :=
  ⟨carried_dirty h.1 b, h.2.1, h.2.2⟩

-- ============================================================
-- La regla conserva CT
-- ============================================================

theorem ct_forbidRound {g : GPathB} (h : CT g S) : CT g.forbidRound.1 S := by
  obtain ⟨hc, hA, hns⟩ := h
  let i := Idx.of g
  have hA₁ : Avoids (TF (g.addTrios i (g.newTrios i)).1) g.current_step S :=
    avoids_addTrios hA i _ (newTrios_notOnS hc hA hns)
  obtain ⟨T', hT⟩ := addTrios_eq g i (g.newTrios i)
  have h₁ : CT (g.setT T') S := ct_setT ⟨hc, hA, hns⟩ T' (by rw [← hT]; exact hA₁)
  simp only [forbidRound]
  rw [hT]
  split
  · exact h₁
  · rename_i hbad
    -- las aristas malas no unen dos nodos de la rama
    apply ct_clean
    apply ct_dirty
    have key : ∀ (l : List (PathNodeId × PathNodeId)),
        (∀ e ∈ l, ¬ (OnS g.current_step S e.1 ∧ OnS g.current_step S e.2)) →
        ∀ x : GPathB, CT x S → x.current_step = g.current_step → x.trios = T' →
          CT (l.foldl (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) x) S := by
      intro l
      induction l with
      | nil => intro _ x hx _ _; exact hx
      | cons e es ih =>
        intro hl x hx hxs hxt
        rw [List.foldl_cons]
        refine ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) _ ?_ hxs hxt
        exact ct_of_shrink hx (carried_removeEdge hx.1 (by rw [hxs]; exact hl e List.mem_cons_self))
          (shrinks_removeEdge x e.1 e.2) rfl (revPrims_noSelf.rmEdge x e.1 e.2 hx.2.2)
    apply key _ _ (g.setT T') h₁ rfl rfl
    intro e he ⟨hx, hw⟩
    have hbad' := (List.mem_filter.mp he).2
    rw [edgeAlive_of_onS h₁.1 h₁.2.1 h₁.2.2 hx hw] at hbad'
    exact absurd hbad' (by simp)

theorem ct_forbidFuel : ∀ (n : Nat) (g : GPathB), CT g S → CT (forbidFuel n g) S := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    unfold forbidFuel
    split
    · simp only
      split
      · exact ih _ (ct_forbidRound h)
      · exact ct_forbidRound h
    · exact h

theorem ct_forbidRule {g : GPathB} (h : CT g S) : CT g.forbidRule S := ct_forbidFuel _ g h

-- ============================================================
-- El review `:on` conserva CT
-- ============================================================

theorem ct_reviewPassOn {g : GPathB} (h : CT g S) : CT g.reviewPassOn S :=
  ct_pruneLinks (ct_reviewSons (ct_reviewParents (ct_pruneLinks (ct_forbidRule (ct_cleanPair h)))))

theorem ct_reviewOn {g : GPathB} (h : CT g S) : CT g.reviewOn S :=
  reviewFuelOn_pres (fun x => CT x S) (fun _ hh => ct_reviewPassOn (ct_dirty hh false)) (fun _ hh => ct_finalPass hh)
    _ g h

-- ============================================================
-- El filtro `:on`
-- ============================================================

theorem trios_of_comm {f : GPathB → GPathB}
    (hf : ∀ (g : GPathB) (T : List (PathNodeId × PathNodeId × PathNodeId)), f (g.setT T) = (f g).setT T) (g : GPathB) :
    (f g).trios = g.trios := by
  have h := congrArg GPathB.trios (hf g g.trios); rw [setT_self] at h; exact h

theorem filterRequire_setT (T : List (PathNodeId × PathNodeId × PathNodeId)) (g : GPathB) (r : NodeId) :
    (g.setT T).filterRequire r = (g.filterRequire r).setT T := by
  unfold filterRequire
  show (if g.isValid then _ else g.setT T) = _
  by_cases hv : g.isValid = true
  · rw [if_pos hv, if_pos hv]
    dsimp only
    rw [foldl_setT T killVertex (fun g id => killVertex_setT T g id)]
    rfl
  · rw [if_neg hv, if_neg hv]

theorem ct_filterRequire {g : GPathB} (h : CT g S) {r : NodeId} (ha : Agrees g.current_step S r) :
    CT (g.filterRequire r) S :=
  ct_of_shrink h (carried_filterRequire h.1 ha) (shrinks_filterRequire g r)
    (trios_of_comm (f := fun x => x.filterRequire r) (fun x T => filterRequire_setT T x r) g) (Final.revPrims_filterRequire revPrims_noSelf g r h.2.2)

theorem ct_filterAllOn {g : GPathB} (h : CT g S) (reqs : List NodeId)
    (ha : ∀ r ∈ reqs, Agrees g.current_step S r) : CT (g.filterAllOn reqs) S := by
  unfold filterAllOn
  apply ct_reviewOn
  have key : ∀ (l : List NodeId) (x : GPathB), CT x S → x.current_step = g.current_step →
      (∀ r ∈ l, Agrees g.current_step S r) → CT (l.foldl filterRequire x) S := by
    intro l
    induction l with
    | nil => intro x hx _ _; exact hx
    | cons r rs ih =>
      intro x hx hxs hl
      rw [List.foldl_cons]
      exact ih _ (ct_filterRequire hx (by rw [hxs]; exact hl r List.mem_cons_self))
        ((shrinks_filterRequire x r).1.step.trans hxs) (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr'))
  exact key reqs g h rfl ha

-- ============================================================
-- El join `:on`
-- ============================================================

/-- El lado que lleva la rama no corta ningún trío de la rama. -/
theorem sideForbidsB_false {g : GPathB} (h : CT g S) {a b r : PathNodeId} (ha : OnS g.current_step S a)
    (hb : OnS g.current_step S b) (hr : OnS g.current_step S r) : g.sideForbidsB a b r = false := by
  unfold sideForbidsB
  have e1 := h.1.adj_on ha hb
  have e2 := h.1.adj_on ha hr
  have e3 := h.1.adj_on hb hr
  unfold Adj at e1 e2 e3
  rw [e1, e2, e3]
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false]
  split
  · rfl
  · exact not_dead_of_avoids h.2.1 h.2.2 ha hb hr

theorem noSelf_join {g₁ g₂ : GPathB} (h₁ : NoSelf g₁) (h₂ : NoSelf g₂) : NoSelf (join g₁ g₂) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact h₁ e h
  · exact h₂ e (List.mem_filter.mp h).1

/-- Los tríos del join: los cortan los dos lados. -/
theorem mem_joinForbid {g₁ g₂ : GPathB} {t : PathNodeId × PathNodeId × PathNodeId} (ht : t ∈ joinForbid g₁ g₂) :
    g₁.sideForbidsB t.1 t.2.1 t.2.2 = true ∧ g₂.sideForbidsB t.1 t.2.1 t.2.2 = true := by
  unfold joinForbid at ht
  obtain ⟨e, _, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  have := (List.mem_filter.mp hr).2
  simp only [Bool.and_eq_true] at this
  rw [idx_sideForbids, idx_sideForbids] at this
  exact ⟨this.1.2, this.2⟩

theorem ct_joinOn_of {g₁ g₂ : GPathB} (hc : Carried (join g₁ g₂) S) (hside : ∀ a b r,
      OnS g₁.current_step S a → OnS g₁.current_step S b → OnS g₁.current_step S r →
      g₁.sideForbidsB a b r = false ∨ g₂.sideForbidsB a b r = false)
    (hns : NoSelf (join g₁ g₂)) : CT (joinOn g₁ g₂) S := by
  let u : GPathB := { join g₁ g₂ with trios := [] }
  have hA : Avoids (TF u) u.current_step S := by
    intro i j k _ _ _ _ _ _ ⟨_, hd⟩
    unfold deadTrio at hd
    simp [u] at hd
  have hA' := avoids_addTrios hA (Idx.of u) (joinForbid g₁ g₂) (by
    intro t ht ⟨h1, h2, h3⟩
    obtain ⟨f1, f2⟩ := mem_joinForbid ht
    rcases hside _ _ _ h1 h2 h3 with h | h
    · rw [h] at f1; cases f1
    · rw [h] at f2; cases f2)
  obtain ⟨T', hT⟩ := addTrios_eq u (Idx.of u) (joinForbid g₁ g₂)
  unfold joinOn
  show CT (u.addTrios (Idx.of u) (joinForbid g₁ g₂)).1 S
  rw [hT] at hA' ⊢
  exact ⟨⟨hc.step, hc.alive, hc.adj, hc.root, hc.node⟩, hA', hns⟩

theorem ct_joinOn_left {g₁ g₂ : GPathB} (h₁ : CT g₁ S) (hns₂ : NoSelf g₂) : CT (joinOn g₁ g₂) S :=
  ct_joinOn_of (carried_join_left h₁.1) (fun _ _ _ ha hb hr => Or.inl (sideForbidsB_false h₁ ha hb hr))
    (noSelf_join h₁.2.2 hns₂)

theorem ct_joinOn_right {g₁ g₂ : GPathB} (hcs : g₁.current_step = g₂.current_step) (h₂ : CT g₂ S)
    (hns₁ : NoSelf g₁) : CT (joinOn g₁ g₂) S :=
  ct_joinOn_of (carried_join_right hcs h₂.1)
    (fun _ _ _ ha hb hr => Or.inr (sideForbidsB_false h₂ (by rw [← hcs]; exact ha) (by rw [← hcs]; exact hb)
      (by rw [← hcs]; exact hr)))
    (noSelf_join hns₁ h₂.2.2)

theorem ct_doJoinOn_left {g₁ g₂ : GPathB} (h₁ : CT g₁ S) (hns₂ : NoSelf g₂) : CT (doJoinOn g₁ g₂) S := by
  unfold doJoinOn; split
  · exact ct_joinOn_left h₁ hns₂
  · exact h₁

theorem ct_doJoinOn_right {g₁ g₂ : GPathB} (hok : okJoin g₁ g₂ = true) (h₂ : CT g₂ S) (hns₁ : NoSelf g₁) :
    CT (doJoinOn g₁ g₂) S := by
  unfold doJoinOn
  rw [if_pos hok]
  have hcs : g₁.current_step = g₂.current_step := by
    unfold okJoin at hok; simp only [Bool.and_eq_true, beq_iff_eq] at hok; exact hok.1.1.1
  exact ct_joinOn_right hcs h₂ hns₁

-- ============================================================
-- Los tríos nombran nodos por debajo del paso actual
-- ============================================================

def AliveBelow (g : GPathB) : Prop := ∀ q ∈ g.alive, q.id.step < g.current_step

def TBelow (g : GPathB) : Prop :=
  ∀ t ∈ g.trios, t.1.id.step < g.current_step ∧ t.2.1.id.step < g.current_step ∧ t.2.2.id.step < g.current_step

/-- El paquete de estado que conservan las operaciones `:on`. -/
def TB (g : GPathB) : Prop := TBelow g ∧ AliveBelow g ∧ EdgesAlive g

theorem revPrims_aliveBelow : RevPrims AliveBelow := by
  refine ⟨?_, fun _ _ _ h => h, ?_, fun _ _ h => h, ?_⟩
  · intro g id h q hq; exact h q (List.mem_filter.mp hq).1
  · intro g id h q hq; exact h q (List.mem_filter.mp hq).1
  · intro g h q hq
    have hs := shrinks_pruneLinks g
    rw [hs.1.step]; exact h q (hs.1.alive q hq)

theorem tb_of_shrink {g h : GPathB} (hb : TB g) (hs : Shrinks h g) (ht : h.trios = g.trios) (hab : AliveBelow h)
    (hea : EdgesAlive h) : TB h := by
  refine ⟨?_, hab, hea⟩
  intro t htt
  rw [hs.1.step]; rw [ht] at htt; exact hb.1 t htt

theorem tb_revPrims {f : GPathB → GPathB} {g : GPathB} (hb : TB g) (hs : Shrinks (f g) g) (ht : (f g).trios = g.trios)
    (hab : AliveBelow g → AliveBelow (f g)) (hea : EdgesAlive g → EdgesAlive (f g)) : TB (f g) :=
  tb_of_shrink hb hs ht (hab hb.2.1) (hea hb.2.2)

theorem tb_addTrios {g : GPathB} (hb : TB g) (i : Idx) (ts : List (PathNodeId × PathNodeId × PathNodeId))
    (hts : ∀ t ∈ ts, t.1.id.step < g.current_step ∧ t.2.1.id.step < g.current_step ∧ t.2.2.id.step < g.current_step) :
    TB (g.addTrios i ts).1 := by
  obtain ⟨T', hT⟩ := addTrios_eq g i ts
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rcases mem_addTrios g i ts t ht with h | h
    · exact hb.1 t h
    · exact hts t h
  · rw [hT]; exact hb.2.1
  · rw [hT]; exact hb.2.2

theorem alive_of_hasEdge {g : GPathB} (hea : EdgesAlive g) {x w : PathNodeId} (h : g.hasEdge x w = true) :
    x ∈ g.alive ∧ w ∈ g.alive :=
  hea x w (by unfold Adj adjb; simp [h])

theorem tb_forbidRound {g : GPathB} (hb : TB g) : TB g.forbidRound.1 := by
  have h₁ : TB (g.addTrios (Idx.of g) (g.newTrios (Idx.of g))).1 := by
    apply tb_addTrios hb
    intro t ht
    unfold newTrios at ht
    obtain ⟨e, he, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
    have hr' := (List.mem_filter.mp hr).1
    rw [idx_mem_nbrs] at hr'
    have hj : g.hasEdge e.1 e.2 = true := List.any_eq_true.mpr ⟨e, he, by simp [joins]⟩
    obtain ⟨a1, a2⟩ := alive_of_hasEdge hb.2.2 hj
    exact ⟨hb.2.1 _ a1, hb.2.1 _ a2, hb.2.1 _ hr'.2.1⟩
  obtain ⟨T', hT⟩ := addTrios_eq g (Idx.of g) (g.newTrios (Idx.of g))
  rw [hT] at h₁
  simp only [forbidRound]
  rw [hT]
  split
  · exact h₁
  · -- quitar aristas, dirty y limpiar: borra y no toca los tríos
    have hf : ∀ (l : List (PathNodeId × PathNodeId)) (x : GPathB), TB x →
        TB (l.foldl (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) x) := by
      intro l
      induction l with
      | nil => intro x hx; exact hx
      | cons e es ih =>
        intro x hx
        rw [List.foldl_cons]
        exact ih _ (tb_of_shrink hx (shrinks_removeEdge x e.1 e.2) rfl (revPrims_aliveBelow.rmEdge x e.1 e.2 hx.2.1)
          (revPrims_edgesAlive.rmEdge x e.1 e.2 hx.2.2))
    have h₂ := hf ((g.setT T').edges.filter (fun e => !(Idx.of (g.setT T')).edgeAlive e.1 e.2)) _ h₁
    have h₃ : TB { (List.foldl (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) (g.setT T')
        ((g.setT T').edges.filter (fun e => !(Idx.of (g.setT T')).edgeAlive e.1 e.2))) with dirty := true } :=
      ⟨h₂.1, h₂.2.1, h₂.2.2⟩
    exact tb_of_shrink h₃ (shrinks_clean _) (trios_clean _) (revPrims_clean revPrims_aliveBelow _ h₃.2.1)
      (revPrims_clean revPrims_edgesAlive _ h₃.2.2)

theorem tb_forbidFuel : ∀ (n : Nat) (g : GPathB), TB g → TB (forbidFuel n g) := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    unfold forbidFuel
    split
    · simp only
      split
      · exact ih _ (tb_forbidRound h)
      · exact tb_forbidRound h
    · exact h

theorem tb_reviewParents {g : GPathB} (h : TB g) : TB g.reviewParents := by
  refine tb_of_shrink h (shrinks_reviewParents g) (trios_reviewParents g) ?_ ?_
  · unfold reviewParents; split
    · exact revPrims_reviewSteps revPrims_aliveBelow _ _ _ h.2.1
    · exact h.2.1
  · unfold reviewParents; split
    · exact revPrims_reviewSteps revPrims_edgesAlive _ _ _ h.2.2
    · exact h.2.2

theorem tb_reviewSons {g : GPathB} (h : TB g) : TB g.reviewSons := by
  refine tb_of_shrink h (shrinks_reviewSons g) (trios_reviewSons g) ?_ ?_
  · unfold reviewSons; split
    · exact revPrims_reviewSteps revPrims_aliveBelow _ _ _ h.2.1
    · exact h.2.1
  · unfold reviewSons; split
    · exact revPrims_reviewSteps revPrims_edgesAlive _ _ _ h.2.2
    · exact h.2.2

theorem tb_pruneLinks {g : GPathB} (h : TB g) : TB g.pruneLinks :=
  tb_of_shrink h (shrinks_pruneLinks g) (trios_pruneLinks g) (revPrims_aliveBelow.links g h.2.1)
    (revPrims_edgesAlive.links g h.2.2)

theorem tb_cleanPair {g : GPathB} (h : TB g) : TB g.cleanPair :=
  tb_of_shrink h (shrinks_cleanPair g) (trios_cleanPair g) (revPrims_cleanPair revPrims_aliveBelow g h.2.1)
    (revPrims_cleanPair revPrims_edgesAlive g h.2.2)

theorem tb_finalPass {g : GPathB} (h : TB g) : TB g.finalPass :=
  tb_of_shrink h (shrinks_finalPass g) (trios_finalPass g) (revPrims_finalPass revPrims_aliveBelow g h.2.1)
    (revPrims_finalPass revPrims_edgesAlive g h.2.2)

theorem tb_dirty {g : GPathB} (h : TB g) (b : Bool) : TB { g with dirty := b } := ⟨h.1, h.2.1, h.2.2⟩

theorem tb_reviewPassOn {g : GPathB} (h : TB g) : TB g.reviewPassOn :=
  tb_pruneLinks (tb_reviewSons (tb_reviewParents (tb_pruneLinks (tb_forbidFuel _ _ (tb_cleanPair h)))))

theorem tb_reviewOn {g : GPathB} (h : TB g) : TB g.reviewOn :=
  reviewFuelOn_pres TB (fun _ hh => tb_reviewPassOn (tb_dirty hh false)) (fun _ hh => tb_finalPass hh) _ g h

-- ============================================================
-- El UP `:on`
-- ============================================================

/-- Cada nodo de `{a, b, r}` es una componente del trío guardado. -/
theorem trioIs_mem' {a b r : PathNodeId} {t : PathNodeId × PathNodeId × PathNodeId} (h : trioIs a b r t = true) :
    (a = t.1 ∨ a = t.2.1 ∨ a = t.2.2) ∧ (b = t.1 ∨ b = t.2.1 ∨ b = t.2.2) ∧ (r = t.1 ∨ r = t.2.1 ∨ r = t.2.2) := by
  obtain ⟨x, y, z⟩ := t
  simp only [trioIs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (((((⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) |
    ⟨⟨h1, h2⟩, h3⟩) <;> simp [h1, h2, h3]

theorem step_of_comp {t : PathNodeId × PathNodeId × PathNodeId} {c : Int}
    (hb : t.1.id.step < c ∧ t.2.1.id.step < c ∧ t.2.2.id.step < c) {x : PathNodeId}
    (hx : x = t.1 ∨ x = t.2.1 ∨ x = t.2.2) : x.id.step < c := by
  rcases hx with rfl | rfl | rfl
  · exact hb.1
  · exact hb.2.1
  · exact hb.2.2

theorem mem_pairsOf : ∀ {l : List PathNodeId} {wr : PathNodeId × PathNodeId}, wr ∈ pairsOf l → wr.1 ∈ l ∧ wr.2 ∈ l
  | [], _, h => by simp [pairsOf] at h
  | w :: ws, wr, h => by
    simp only [pairsOf, List.mem_append, List.mem_map] at h
    rcases h with ⟨r, hr, rfl⟩ | h
    · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ hr⟩
    · obtain ⟨h1, h2⟩ := mem_pairsOf h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

section Up

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

theorem newRow_id' {q : PathNodeId} (hq : q ∈ g.newRowIds d forb) : q.id = d :=
  Machine.mapId_of_mem_shiftRowIds (List.mem_filter.mp hq).1

/-- Una arista de la fila nueva toca un nodo de la fila. -/
theorem hasEdge_addNode_old {x y : PathNodeId} (hx : x ∉ g.newRowIds d forb) (hy : y ∉ g.newRowIds d forb)
    (h : (g.addNode d title forb).hasEdge x y = true) : g.hasEdge x y = true := by
  obtain ⟨e, he, hj⟩ := List.any_eq_true.mp h
  rcases List.mem_append.mp he with hold | hnew
  · exact List.any_eq_true.mpr ⟨e, hold, hj⟩
  · exfalso
    obtain ⟨pid, hpid, he'⟩ := List.mem_flatMap.mp hnew
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp he'
    rcases (joins_iff x y _).mp hj with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hx (h1 ▸ hpid)
    · exact hy (h1 ▸ hpid)

theorem noSelf_addNode (hns : NoSelf g) : NoSelf (g.addNode d title forb) := by
  intro e he
  rcases List.mem_append.mp he with hold | hnew
  · exact hns e hold
  · obtain ⟨pid, _, he'⟩ := List.mem_flatMap.mp hnew
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he'
    have := (List.mem_filter.mp hw).2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    intro h
    have hlt : w.id.step < pid.id.step := this.1
    simp only at h
    rw [h] at hlt
    exact Int.lt_irrefl _ hlt

/-- **El UP `:on` conserva `CT`**, con las hipótesis de `carried_addNode`. -/
theorem ct_upOn (hct : CT g S) (htb : TB g) (hnew : S g.current_step ∈ g.newRowIds d forb)
    (hpar : 0 < g.current_step → S (g.current_step - 1) ∈ g.rowParents d (S g.current_step))
    (hstep : (S g.current_step).id.step = g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hroot : (S 0).parent_id = none) : CT (g.upOn d title forb) S := by
  have hc₀ := carried_addNode (title := title) hct.1 hnew hpar hstep hbelow hroot
  have hid : ∀ q ∈ g.newRowIds d forb, q.id = d := fun q hq => newRow_id' hq
  have hdS : d.step = g.current_step := by rw [← hid _ hnew]; exact hstep
  -- el estado tras la fila, con los tríos de antes
  let a' := (g.addNode d title forb).setT g.trios
  have hcs : a'.current_step = g.current_step + 1 := rfl
  have hc : Carried a' S := ⟨hc₀.step, hc₀.alive, hc₀.adj, hc₀.root, hc₀.node⟩
  have hidx : ∀ k, 0 ≤ k → k < g.current_step + 1 → (S k).id.step = k := fun k h0 h1 => hc.step k h0 h1
  have notNew : ∀ k, 0 ≤ k → k < g.current_step → S k ∉ g.newRowIds d forb := by
    intro k h0 h1 hk
    have := hidx k h0 (by omega)
    rw [hid _ hk, hdS] at this
    omega
  -- los tríos viejos solo nombran nodos viejos
  have hA : Avoids (TF a') a'.current_step S := by
    intro i j k h0 h1 h2 h3 h4 h5 ⟨hne, hd⟩
    unfold deadTrio at hd
    rw [Bool.and_eq_true] at hd
    obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd.2
    obtain ⟨c1, c2, c3⟩ := trioIs_mem' hti
    have hbt := htb.1 t ht
    have hi : i < g.current_step := by
      have := step_of_comp hbt c1; rw [hidx i h0 h1] at this; exact this
    have hj : j < g.current_step := by
      have := step_of_comp hbt c2; rw [hidx j h2 h3] at this; exact this
    have hk : k < g.current_step := by
      have := step_of_comp hbt c3; rw [hidx k h4 h5] at this; exact this
    have hE : g.hasEdge (S i) (S j) = true :=
      hasEdge_addNode_old (notNew i h0 hi) (notNew j h2 hj) (title := title) hd.1
    exact hct.2.1 i j k h0 hi h2 hj h4 hk ⟨hne, by
      unfold deadTrio; rw [Bool.and_eq_true]; exact ⟨hE, hd.2⟩⟩
  have hct' : CT a' S := ⟨hc, hA, noSelf_addNode (title := title) hct.2.2⟩
  -- los tríos del UP no son de la rama
  have hup : ∀ t ∈ (g.newRowIds d forb).flatMap (fun n => upForbidTodo (Idx.of a') n (a'.parentsOf n)),
      ¬ (OnS a'.current_step S t.1 ∧ OnS a'.current_step S t.2.1 ∧ OnS a'.current_step S t.2.2) := by
    intro t ht ⟨hn, hw, hr⟩
    obtain ⟨n, hnm, ht⟩ := List.mem_flatMap.mp ht
    unfold upForbidTodo at ht
    obtain ⟨wr, hwr, rfl⟩ := List.mem_map.mp ht
    simp only at hn hw hr
    obtain ⟨hwr1, hwr2⟩ := List.mem_filter.mp hwr
    simp only [Bool.and_eq_true, List.all_eq_true] at hwr2
    -- `n` es la cima de la rama
    obtain ⟨kn, hk0, hk1, hkn⟩ := hn
    have hkcs : kn = g.current_step := by
      have := hidx kn hk0 hk1; rw [hkn, hid _ hnm, hdS] at this; omega
    subst hkcs
    -- `w` es de la rama y distinto de `n`: el paso es positivo
    obtain ⟨hw1, _⟩ := mem_pairsOf hwr1
    have hwn : wr.1 ≠ n := ((idx_mem_nbrs a' n wr.1).mp hw1).1
    obtain ⟨j, hj0, hj1, hjw⟩ := hw
    have hjcs : j < g.current_step := by
      rcases Int.lt_or_eq_of_le (show j ≤ g.current_step by omega) with h | h
      · exact h
      · exfalso; apply hwn; rw [← hjw, ← hkn, h]
    have hpos : 0 < g.current_step := by omega
    -- el padre de la rama es padre de `n`, y no corta el trío
    obtain ⟨m, hm, hmp, _⟩ := hc.node g.current_step (by omega) (by omega)
    have hpm : S (g.current_step - 1) ∈ a'.parentsOf n := by
      unfold parentsOf; rw [← hkn, hm]; exact hmp hpos
    have hsf := hwr2.2 _ hpm
    rw [idx_sideForbids, sideForbidsB_false hct' ⟨g.current_step - 1, by omega, by omega, rfl⟩
      ⟨j, hj0, by omega, hjw⟩ hr] at hsf
    cases hsf
  -- el UP y el review
  unfold upOn
  rw [if_pos (isValid_of_carried hct.1)]
  apply ct_reviewOn
  show CT (a'.addTrios (Idx.of a') ((g.newRowIds d forb).flatMap
    (fun n => upForbidTodo (Idx.of a') n (a'.parentsOf n)))).1 S
  have hA' := avoids_addTrios hA (Idx.of a') _ hup
  obtain ⟨T', hT⟩ := addTrios_eq a' (Idx.of a') ((g.newRowIds d forb).flatMap
    (fun n => upForbidTodo (Idx.of a') n (a'.parentsOf n)))
  rw [hT] at hA' ⊢
  exact ⟨⟨hc.step, hc.alive, hc.adj, hc.root, hc.node⟩, hA', hct'.2.2⟩

end Up

end GPathB

end AbsSatBingo.Model
