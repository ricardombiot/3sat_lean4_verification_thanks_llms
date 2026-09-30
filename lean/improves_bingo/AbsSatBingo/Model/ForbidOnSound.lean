-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnSound.lean
import AbsSatBingo.Model.ForbidOnIdx
import AbsSatBingo.Model.ForbidOnClosed
import AbsSatBingo.Model.ForbidSound
import AbsSatBingo.Model.Grow

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

end GPathB

end AbsSatBingo.Model
