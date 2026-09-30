-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnFix.lean
import AbsSatBingo.Model.ForbidOnDown

/-!
# La regla llega a su punto fijo (`docs/plans/lean_forbid_on.md`, F4)

Julia corre `forbid_rule!` mientras cambie algo; Lean, con combustible (`forbidBound`). Aquí se demuestra que el
combustible basta: el potencial `phi` (triángulos abiertos entre los candidatos arista × vivo) más la medida baja en
cada vuelta que sigue (`forbidRound_dec`), y está por debajo del tope. Así el estado que devuelve la regla es un punto
fijo (`FixClosed`): ningún triángulo abierto sin testigo bueno y ninguna arista sin testigo bueno.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

-- ============================================================
-- Listas
-- ============================================================

theorem flatMap_sublist {α β : Type} {l₁ l₂ : List α} {f g : α → List β} (h : l₁.Sublist l₂)
    (hfg : ∀ a, (f a).Sublist (g a)) : (l₁.flatMap f).Sublist (l₂.flatMap g) := by
  induction h with
  | slnil => exact List.Sublist.slnil
  | cons a _ ih => rw [List.flatMap_cons]; exact ih.trans (List.sublist_append_right _ _)
  | cons_cons a _ ih => rw [List.flatMap_cons, List.flatMap_cons]; exact List.Sublist.append (hfg a) ih

theorem countP_lt_of {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, q x = true → p x = true) →
    (∃ x ∈ l, p x = true ∧ q x = false) → l.countP q < l.countP p := by
  intro l
  induction l with
  | nil => intro _ ⟨x, hx, _⟩; exact absurd hx List.not_mem_nil
  | cons a as ih =>
    intro hqp ⟨x, hx, hpx, hqx⟩
    rw [List.countP_cons, List.countP_cons]
    have hle : as.countP q ≤ as.countP p :=
      List.countP_mono_left (fun y hy h => hqp y (List.mem_cons_of_mem _ hy) h)
    have hqa' : q a = true → p a = true := hqp a List.mem_cons_self
    rcases List.mem_cons.mp hx with hxa | hx'
    · subst hxa
      rw [hpx, hqx]; simp; omega
    · have hlt := ih (fun y hy h => hqp y (List.mem_cons_of_mem _ hy) h) ⟨x, hx', hpx, hqx⟩
      cases hq : q a <;> cases hp : p a
      · simp; omega
      · simp; omega
      · exact absurd (hqa' hq) (by rw [hp]; simp)
      · simp; omega

-- ============================================================
-- El potencial
-- ============================================================

/-- Los candidatos de la fase 1: una arista y un vivo. -/
def cand (x : GPathB) : List (PathNodeId × PathNodeId × PathNodeId) :=
  x.edges.flatMap (fun e => x.alive.map (fun r => (e.1, e.2, r)))

/-- Un candidato abierto: triángulo sin prohibir. -/
def openB (x : GPathB) (t : PathNodeId × PathNodeId × PathNodeId) : Bool :=
  t.2.2 != t.1 && t.2.2 != t.2.1 && x.hasEdge t.1 t.2.2 && x.hasEdge t.2.1 t.2.2 && !x.deadTrio t.1 t.2.1 t.2.2

def phi (x : GPathB) : Nat := (cand x).countP (openB x)

theorem length_cand (x : GPathB) : (cand x).length = x.edges.length * x.alive.length := by
  unfold cand
  rw [List.length_flatMap]
  simp only [List.length_map]
  induction x.edges with
  | nil => simp
  | cons e es ih => simp [List.map_cons, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem phi_le (x : GPathB) : phi x ≤ x.edges.length * x.alive.length := by
  rw [← length_cand]; exact List.countP_le_length

/-- `y` está por debajo de `x` en listas: aristas y vivos son sublistas, y los tríos de `x` siguen en `y`. -/
structure SubL (y x : GPathB) : Prop where
  edges : y.edges.Sublist x.edges
  alive : y.alive.Sublist x.alive
  trios : ∀ t ∈ x.trios, t ∈ y.trios

theorem SubL.refl (x : GPathB) : SubL x x := ⟨List.Sublist.refl _, List.Sublist.refl _, fun _ h => h⟩

theorem SubL.trans {a b c : GPathB} (h₁ : SubL a b) (h₂ : SubL b c) : SubL a c :=
  ⟨h₁.edges.trans h₂.edges, h₁.alive.trans h₂.alive, fun t ht => h₁.trios t (h₂.trios t ht)⟩

theorem phi_mono {x y : GPathB} (h : SubL y x) : phi y ≤ phi x := by
  have hc : (cand y).Sublist (cand x) := flatMap_sublist h.edges (fun _ => h.alive.map _)
  refine Nat.le_trans (List.countP_mono_left ?_) (hc.countP_le)
  intro t ht hy
  unfold cand at ht
  obtain ⟨e, he, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp ht
  have hsub : ∀ a b, y.hasEdge a b = true → x.hasEdge a b = true := by
    intro a b hab
    obtain ⟨e', he', hj⟩ := List.any_eq_true.mp hab
    exact List.any_eq_true.mpr ⟨e', h.edges.subset he', hj⟩
  unfold openB at hy ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy ⊢
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hy
  refine ⟨⟨⟨⟨h1, h2⟩, hsub _ _ h3⟩, hsub _ _ h4⟩, ?_⟩
  cases hd : x.deadTrio e.1 e.2 r
  · rfl
  · exfalso
    unfold deadTrio at hd h5
    rw [Bool.and_eq_true] at hd
    obtain ⟨t', ht', hti⟩ := List.any_eq_true.mp hd.2
    have hey : y.hasEdge e.1 e.2 = true := List.any_eq_true.mpr ⟨e, he, by simp [joins]⟩
    rw [hey, Bool.true_and] at h5
    rw [List.any_eq_false] at h5
    exact h5 t' (h.trios t' ht') hti

-- ============================================================
-- Las piezas de la vuelta bajan en listas
-- ============================================================

theorem subL_setT (x : GPathB) {T' : List (PathNodeId × PathNodeId × PathNodeId)} (hT : ∀ t ∈ x.trios, t ∈ T') :
    SubL (x.setT T') x := ⟨List.Sublist.refl _, List.Sublist.refl _, hT⟩

theorem subL_removeEdge (x : GPathB) (a b : PathNodeId) : SubL (x.removeEdge a b) x :=
  ⟨List.filter_sublist, List.Sublist.refl _, fun _ h => h⟩

theorem subL_killVertex (x : GPathB) (id : PathNodeId) : SubL (x.killVertex id) x :=
  ⟨List.filter_sublist, List.filter_sublist, fun _ h => h⟩

theorem subL_removeNode (x : GPathB) (id : PathNodeId) : SubL (x.removeNode id) x :=
  ⟨List.filter_sublist, List.filter_sublist, fun _ h => h⟩

theorem subL_dirty (x : GPathB) (b : Bool) : SubL { x with dirty := b } x :=
  ⟨List.Sublist.refl _, List.Sublist.refl _, fun _ h => h⟩

theorem subL_purgeStep (x : GPathB) (id : PathNodeId) : SubL (x.purgeStep id) x := by
  unfold purgeStep
  split
  · exact SubL.refl x
  · split
    · exact SubL.refl x
    · exact ⟨List.filter_sublist, List.filter_sublist, fun _ h => h⟩

theorem subL_foldl {α : Type} (f : GPathB → α → GPathB) (hf : ∀ x a, SubL (f x a) x) :
    ∀ (l : List α) (x : GPathB), SubL (l.foldl f x) x := by
  intro l
  induction l with
  | nil => intro x; exact SubL.refl x
  | cons a as ih => intro x; rw [List.foldl_cons]; exact (ih _).trans (hf x a)

theorem subL_purgeFuel : ∀ (n : Nat) (x : GPathB), SubL (purgeFuel n x) x := by
  intro n
  induction n with
  | zero => intro x; exact SubL.refl x
  | succ n ih =>
    intro x
    unfold purgeFuel
    split
    · have hr : SubL x.purgeRound x := subL_foldl _ subL_purgeStep _ x
      dsimp only
      split
      · exact (ih _).trans hr
      · exact hr
    · exact SubL.refl x

theorem subL_clean (x : GPathB) : SubL x.clean x := subL_purgeFuel _ x

-- ============================================================
-- Cada vuelta que sigue baja el potencial más la medida
-- ============================================================

/-- Si la fase 1 no tiene candidatos, `addTrios` no escribe nada. -/
theorem addTrios_nil (x : GPathB) (i : Idx) : x.addTrios i [] = ({ x with trios := x.trios ++ [] }, false) := rfl

theorem forbidRound_dec (x : GPathB) (hr : x.forbidRound.2 = true) :
    phi x.forbidRound.1 + x.forbidRound.1.measure < phi x + x.measure := by
  obtain ⟨T', hT⟩ := addTrios_eq x (Idx.of x) (x.newTrios (Idx.of x))
  have hgrow : ∀ t ∈ x.trios, t ∈ T' := by
    intro t ht
    have : t ∈ (x.addTrios (Idx.of x) (x.newTrios (Idx.of x))).1.trios := by
      unfold addTrios; exact List.mem_append_left _ ht
    rw [hT] at this; exact this
  simp only [forbidRound] at hr ⊢
  rw [hT] at hr ⊢
  split at hr
  · -- solo tríos: el potencial baja
    rename_i hbad
    rw [if_pos hbad]
    have hm : (x.setT T').measure = x.measure := rfl
    rw [hm]
    -- hay un candidato de la fase 1, y queda prohibido
    have hne : x.newTrios (Idx.of x) ≠ [] := by
      intro h0
      have : (x.addTrios (Idx.of x) (x.newTrios (Idx.of x))).2 = true := by simpa using hr
      rw [h0, addTrios_nil] at this; cases this
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hne
    have ht0 := ht
    unfold newTrios at ht0
    obtain ⟨e, he, ht0⟩ := List.mem_flatMap.mp ht0
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp ht0
    obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr'
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hr2
    have hnb := (idx_mem_nbrs x e.1 r).mp hr1
    have hin : (e.1, e.2, r) ∈ cand x :=
      List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨r, hnb.2.1, rfl⟩⟩
    have hopen : openB x (e.1, e.2, r) = true := by
      unfold openB
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
      refine ⟨⟨⟨⟨hnb.1, hr2.1.1.1⟩, hnb.2.2⟩, by rw [← idx_hasEdge]; exact hr2.1.1.2⟩, ?_⟩
      rw [← idx_deadTrio]; exact hr2.1.2
    have hclosed : openB (x.setT T') (e.1, e.2, r) = false := by
      rcases addTrios_covers x (Idx.of x) _ (e.1, e.2, r) ht with h | h
      · rw [hT] at h
        unfold openB
        have hd : (x.setT T').deadTrio e.1 e.2 r = true := by
          unfold deadTrio; rw [Bool.and_eq_true]
          exact ⟨List.any_eq_true.mpr ⟨e, he, by simp [joins]⟩, h⟩
        simp [hd]
      · exfalso; rw [h] at hr2; simp at hr2
    have hsub := subL_setT x hgrow
    unfold phi
    have hc : cand (x.setT T') = cand x := rfl
    rw [hc]
    exact countP_lt_of (fun t' ht' hq => by
      have := phi_mono hsub
      unfold openB at hq ⊢
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hq ⊢
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hq
      refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ?_⟩
      cases hd : x.deadTrio t'.1 t'.2.1 t'.2.2
      · rfl
      · exfalso
        unfold deadTrio at hd h5
        rw [Bool.and_eq_true] at hd
        obtain ⟨t'', ht'', hti⟩ := List.any_eq_true.mp hd.2
        have hh : (x.setT T').hasEdge t'.1 t'.2.1 = true := hd.1
        rw [hh, Bool.true_and, List.any_eq_false] at h5
        exact h5 t'' (hgrow t'' ht'') hti) ⟨_, hin, hopen, hclosed⟩ |> Nat.add_lt_add_right <| x.measure
  · -- se cortan aristas: la medida baja y el potencial no sube
    rename_i hbad
    rw [if_neg hbad]
    have hsub : SubL (clean { List.foldl (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) (x.setT T')
        ((x.setT T').edges.filter (fun e => !(Idx.of (x.setT T')).edgeAlive e.1 e.2)) with dirty := true }) x :=
      (subL_clean _).trans ((subL_dirty _ true).trans
        ((subL_foldl _ (fun y (e : PathNodeId × PathNodeId) => subL_removeEdge y e.1 e.2) _ _).trans (subL_setT x hgrow)))
    have hphi := phi_mono hsub
    -- la medida baja: se quita una arista que existe
    have hm : (clean { List.foldl (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) (x.setT T')
        ((x.setT T').edges.filter (fun e => !(Idx.of (x.setT T')).edgeAlive e.1 e.2)) with dirty := true }).measure
        < x.measure := by
      generalize hb : (x.setT T').edges.filter (fun e => !(Idx.of (x.setT T')).edgeAlive e.1 e.2) = bad at hbad ⊢
      cases bad with
      | nil => simp at hbad
      | cons e rest =>
        have hmem : e ∈ (x.setT T').edges.filter (fun e => !(Idx.of (x.setT T')).edgeAlive e.1 e.2) := by
          rw [hb]; exact List.mem_cons_self
        have he : e ∈ x.edges := (List.mem_filter.mp hmem).1
        have hj : x.hasEdge e.1 e.2 = true := List.any_eq_true.mpr ⟨e, he, by simp [joins]⟩
        refine Nat.lt_of_le_of_lt (shrinks_clean _).2 ?_
        show (List.foldl (fun (h : GPathB) (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2)
          ((x.setT T').removeEdge e.1 e.2) rest).measure < x.measure
        have h1 := measure_foldl_le (fun (h : GPathB) (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2)
          (fun g e => measure_removeEdge_le g e.1 e.2) rest ((x.setT T').removeEdge e.1 e.2)
        exact Nat.lt_of_le_of_lt h1 (measure_removeEdge_lt (x.setT T') e.1 e.2 hj)
    exact Nat.add_lt_add_of_le_of_lt hphi hm

-- ============================================================
-- El punto fijo
-- ============================================================

/-- **La regla está en su punto fijo en `z`**: la fase 1 no tiene candidatos y ninguna arista carece de testigo. -/
def FixClosed (z : GPathB) : Prop :=
  z.newTrios (Idx.of z) = [] ∧ z.edges.filter (fun e => !(Idx.of z).edgeAlive e.1 e.2) = []

/-- Si el primero de la lista no está prohibido, `addTrios` escribe algo. -/
theorem addTrios_grew (x : GPathB) (i : Idx) (t : PathNodeId × PathNodeId × PathNodeId)
    (ts : List (PathNodeId × PathNodeId × PathNodeId)) (ht : i.deadTrio t.1 t.2.1 t.2.2 = false) :
    (x.addTrios i (t :: ts)).2 = true := by
  have key : ∀ (l : List (PathNodeId × PathNodeId × PathNodeId))
      (acc : List (PathNodeId × PathNodeId × PathNodeId) × Std.HashSet (PathNodeId × PathNodeId × PathNodeId)),
      acc.1 ≠ [] → (l.foldl (fun (acc : List (PathNodeId × PathNodeId × PathNodeId) ×
        Std.HashSet (PathNodeId × PathNodeId × PathNodeId)) t =>
        if acc.2.contains t || i.deadTrio t.1 t.2.1 t.2.2 then acc
        else (t :: acc.1, acc.2.insertMany (perms t.1 t.2.1 t.2.2))) acc).1 ≠ [] := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons u us ih =>
      intro acc hacc
      rw [List.foldl_cons]
      apply ih
      split
      · exact hacc
      · simp
  unfold addTrios
  simp only [List.foldl_cons]
  have hc : ((∅ : Std.HashSet (PathNodeId × PathNodeId × PathNodeId)).contains t || i.deadTrio t.1 t.2.1 t.2.2)
      = false := by simp [ht]
  rw [if_neg (by rw [hc]; simp)]
  have := key ts ([t], (∅ : Std.HashSet (PathNodeId × PathNodeId × PathNodeId)).insertMany (perms t.1 t.2.1 t.2.2))
    (by simp)
  simpa [List.isEmpty_iff] using this

theorem forbidRound_quiet (x : GPathB) (h : x.forbidRound.2 = false) : x.forbidRound.1 = x ∧ FixClosed x := by
  obtain ⟨T', hT⟩ := addTrios_eq x (Idx.of x) (x.newTrios (Idx.of x))
  have hsnd := h
  simp only [forbidRound] at h ⊢
  rw [hT] at h ⊢
  split at h
  · rename_i hbad
    rw [if_pos hbad]
    have hnil : x.newTrios (Idx.of x) = [] := by
      cases hn : x.newTrios (Idx.of x) with
      | nil => rfl
      | cons t ts =>
        exfalso
        have h2 : (x.addTrios (Idx.of x) (x.newTrios (Idx.of x))).2 = false := by simpa using h
        have ht : t ∈ x.newTrios (Idx.of x) := by rw [hn]; exact List.mem_cons_self
        unfold newTrios at ht
        obtain ⟨e, _, ht⟩ := List.mem_flatMap.mp ht
        obtain ⟨r, hr, hte⟩ := List.mem_map.mp ht
        have hr2 := (List.mem_filter.mp hr).2
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hr2
        have hnd : (Idx.of x).deadTrio t.1 t.2.1 t.2.2 = false := by rw [← hte]; exact hr2.1.2
        rw [hn, addTrios_grew x (Idx.of x) t ts hnd] at h2
        cases h2
    have hTe : x.setT T' = x := by
      rw [← hT, hnil, addTrios_nil]; simp
    refine ⟨hTe, hnil, ?_⟩
    rw [hTe] at hbad
    simpa using hbad
  · simp at h

theorem forbidFuel_closed : ∀ (n : Nat) (x : GPathB), phi x + x.measure < n →
    (forbidFuel n x).isValid = true → FixClosed (forbidFuel n x) := by
  intro n
  induction n with
  | zero => intro x h; omega
  | succ n ih =>
    intro x hlt hv
    unfold forbidFuel at hv ⊢
    split at hv
    · rename_i hvx
      rw [if_pos hvx]
      simp only at hv ⊢
      by_cases hr : x.forbidRound.2 = true
      · rw [if_pos hr] at hv ⊢
        exact ih _ (by have := forbidRound_dec x hr; omega) hv
      · have hr' : x.forbidRound.2 = false := by simpa using hr
        rw [if_neg hr]
        obtain ⟨heq, hc⟩ := forbidRound_quiet x hr'
        rw [heq]; exact hc
    · rename_i hvx; exact absurd hv hvx

/-- **La regla llega a su punto fijo** en un estado válido. -/
theorem forbidRule_closed (x : GPathB) (hv : x.forbidRule.isValid = true) : FixClosed x.forbidRule :=
  forbidFuel_closed _ x (by unfold forbidBound; have := phi_le x; omega) hv

-- ============================================================
-- El review `:on` sale en el punto fijo de la regla
-- ============================================================

/-- El índice solo depende de vivos, aristas, tríos y paso. -/
theorem idx_congr {h z : GPathB} (ha : h.alive = z.alive) (he : h.edges = z.edges) (ht : h.trios = z.trios)
    (hc : h.current_step = z.current_step) : Idx.of h = Idx.of z := by
  unfold Idx.of; rw [ha, he, ht, hc]

theorem fixClosed_congr {h z : GPathB} (ha : h.alive = z.alive) (he : h.edges = z.edges) (ht : h.trios = z.trios)
    (hc : h.current_step = z.current_step) (hz : FixClosed z) : FixClosed h := by
  have hi := idx_congr ha he ht hc
  unfold FixClosed newTrios at hz ⊢
  rw [hi, he]; exact hz

theorem pruneLinks_graphOn (g : GPathB) : g.pruneLinks.alive = g.alive ∧ g.pruneLinks.edges = g.edges ∧
    g.pruneLinks.trios = g.trios ∧ g.pruneLinks.current_step = g.current_step := by
  unfold pruneLinks; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem reviewParents_clean {g : GPathB} (hd : g.dirty = false) : g.reviewParents = g := by
  unfold reviewParents; rw [if_neg (by simp [hd])]

theorem reviewSons_clean {g : GPathB} (hd : g.dirty = false) : g.reviewSons = g := by
  unfold reviewSons; rw [if_neg (by simp [hd])]

/-- **El review con la regla sale en su punto fijo.** -/
theorem fixClosed_reviewOn {g : GPathB} (hd : g.dirty = true) (hv : g.reviewOn.isValid = true) :
    FixClosed g.reviewOn := by
  have hc := reviewOn_exits_clean g hv
  obtain ⟨g₁, _, he, hpd, hvp, _⟩ := reviewFuelOn_exit _ g hd hv hc
  have heq : g.reviewOn = g₁.reviewPassOn := he
  rw [heq]
  have hpd' : g₁.cleanPair.forbidRule.pruneLinks.reviewParents.reviewSons.pruneLinks.dirty = false := by
    unfold reviewPassOn at hpd; exact hpd
  have hvp' : g₁.cleanPair.forbidRule.pruneLinks.reviewParents.reviewSons.pruneLinks.isValid = true := by
    unfold reviewPassOn at hvp; exact hvp
  -- tras la regla nada enciende `dirty`
  have hz1 : g₁.cleanPair.forbidRule.pruneLinks.dirty = false := by
    cases h : g₁.cleanPair.forbidRule.pruneLinks.dirty
    · rfl
    · exfalso
      rw [keepsDirty_pruneLinks _ (keepsDirty_reviewSons _ (keepsDirty_reviewParents _ h))] at hpd'
      cases hpd'
  rw [reviewParents_clean hz1, reviewSons_clean hz1] at hpd' hvp'
  show FixClosed g₁.cleanPair.forbidRule.pruneLinks.reviewParents.reviewSons.pruneLinks
  rw [reviewParents_clean hz1, reviewSons_clean hz1]
  obtain ⟨a1, e1, t1, c1⟩ := pruneLinks_graphOn g₁.cleanPair.forbidRule
  obtain ⟨a2, e2, t2, c2⟩ := pruneLinks_graphOn g₁.cleanPair.forbidRule.pruneLinks
  have hvz : g₁.cleanPair.forbidRule.isValid = true := by
    have : g₁.cleanPair.forbidRule.pruneLinks.pruneLinks.isValid = g₁.cleanPair.forbidRule.isValid := by
      unfold isValid; rw [a2, a1, c2, c1]
    rw [← this]; exact hvp'
  exact fixClosed_congr (a2.trans a1) (e2.trans e1) (t2.trans t1) (c2.trans c1) (forbidRule_closed _ hvz)

-- ============================================================
-- Del punto fijo, los testigos buenos de la parte baja
-- ============================================================

/-- La parte baja de un estado: vivos y posesiones por debajo del paso `c` (lo que baja `secStruct_addNode_down`). -/
def LowV (H : GPathB) (c : Int) : PathNodeId → Prop := fun q => q ∈ H.alive ∧ q.id.step < c
def LowR (H : GPathB) (c : Int) : PathNodeId → PathNodeId → Prop := fun y w =>
  (y ∈ H.alive ∧ w ∈ H.alive ∧ H.Adj y w) ∧ y.id.step < c ∧ w.id.step < c

theorem mem_incAt_iff {x : GPathB} {a s : PathNodeId} {l : Int} (hs : s ∈ (Idx.of x).incAt a l) :
    s.id.step = l ∧ s ∈ x.alive ∧ (s = a ∨ x.hasEdge a s = true) := by
  unfold Idx.incAt at hs
  rcases List.mem_append.mp hs with h | h
  · split at h
    · rename_i hc
      rw [List.mem_singleton] at h; subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨hc.1, (idx_alive x s).mp hc.2, Or.inl rfl⟩
    · exact absurd h List.not_mem_nil
  · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    have := (idx_mem_nbrs x a s).mp h1
    exact ⟨by simpa using h2, this.2.1, Or.inr this.2.2⟩

theorem deadTrio_swap12 {x : GPathB} {a b s : PathNodeId} (h : x.deadTrio a b s = true) : x.deadTrio b a s = true := by
  unfold deadTrio at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp h.2
  refine ⟨?_, List.any_eq_true.mpr ⟨t, ht, trioIs_swap12 hti⟩⟩
  obtain ⟨e, he, hj⟩ := List.any_eq_true.mp h.1
  exact List.any_eq_true.mpr ⟨e, he, by rw [joins_iff] at hj ⊢; rcases hj with h | h; exact Or.inr h; exact Or.inl h⟩

theorem trioIs_swap23 {a b r : PathNodeId} {t : PathNodeId × PathNodeId × PathNodeId} (h : trioIs a r b t = true) :
    trioIs a b r t = true := by
  obtain ⟨x, y, z⟩ := t
  simp only [trioIs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (((((⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) |
    ⟨⟨h1, h2⟩, h3⟩) <;> subst h1 <;> subst h2 <;> subst h3 <;> simp [trioIs]

/-- Una arista de `R` bajo sus dos órdenes. -/
theorem edge_of_hasEdge {x : GPathB} {a b : PathNodeId} (h : x.hasEdge a b = true) :
    ∃ e ∈ x.edges, (e.1 = a ∧ e.2 = b) ∨ (e.1 = b ∧ e.2 = a) := by
  obtain ⟨e, he, hj⟩ := List.any_eq_true.mp h
  exact ⟨e, he, (joins_iff a b e).mp hj⟩

theorem adj_of_hasEdge' {x : GPathB} {a b : PathNodeId} (h : x.hasEdge a b = true) : x.Adj a b := by
  unfold Adj adjb; simp [h]

/-- **Del punto fijo de la regla, la parte baja tiene testigos buenos.** -/
theorem trioGood_low {H : GPathB} {c : Int} (hf : FixClosed H) (hnd : NoDegT H) (hc : c ≤ H.current_step) :
    TrioGood (LowV H c) (LowR H c) (TF H) c := by
  have halive : ∀ e ∈ H.edges, (Idx.of H).edgeAlive e.1 e.2 = true := by
    intro e he
    have := hf.2
    rw [List.filter_eq_nil_iff] at this
    simpa using this e he
  have hrange : ∀ l, 0 ≤ l → l < c → l ∈ intRange 0 ((Idx.of H).cs - 1) := fun l h0 h1 =>
    mem_intRange h0 (by show l ≤ H.current_step - 1; omega)
  have hE : ∀ {a b}, LowR H c a b → a ≠ b → H.hasEdge a b = true := fun h hne => hasEdge_of_adj h.1.2.2 hne
  have symm : ∀ {a b}, LowR H c a b → LowR H c b a :=
    fun h => ⟨⟨h.1.2.1, h.1.1, (adj_symm H _ _).mp h.1.2.2⟩, h.2.2, h.2.1⟩
  have refl : ∀ {a b}, LowR H c a b → LowR H c a a :=
    fun h => ⟨⟨h.1.1, h.1.1, adj_refl _ _ h.1.1⟩, h.2.1, h.2.1⟩
  have mkR : ∀ {a b s}, LowR H c a b → s ∈ H.alive → s.id.step < c → H.hasEdge a s = true → LowR H c a s :=
    fun h hs hsl he => ⟨⟨h.1.1, hs, adj_of_hasEdge' he⟩, h.2.1, hsl⟩
  have nT : ∀ {x y z}, H.deadTrio x y z = false → ¬ TF H x y z := fun hd ⟨_, h⟩ => by rw [hd] at h; cases h
  have nT' : ∀ {x y z}, H.deadTrio y x z = false → ¬ TF H x y z := fun hd ⟨_, h⟩ => by
    rw [deadTrio_swap12 h] at hd; cases hd
  have dF : ∀ {x y z}, x ≠ y → ¬ TF H x y z → H.deadTrio x y z = false := fun hne hn => by
    cases h : H.deadTrio _ _ _
    · rfl
    · exact absurd ⟨hne, h⟩ hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- aristas
    intro a b hab hne l h0 hl
    obtain ⟨e, he, hor⟩ := edge_of_hasEdge (hE hab hne)
    have hEA := halive e he
    unfold Idx.edgeAlive at hEA
    obtain ⟨s, hs, hw⟩ := List.any_eq_true.mp (List.all_eq_true.mp hEA l (hrange l h0 hl))
    obtain ⟨hsl, hsa, hsor⟩ := mem_incAt_iff hs
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true', idx_hasEdge, idx_deadTrio] at hw
    have hsc : s.id.step < c := by rw [hsl]; exact hl
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2] at hw hsor
    · refine ⟨s, hsl, ?_, ?_, ?_⟩
      · rcases hsor with rfl | h
        · exact refl hab
        · exact mkR hab hsa hsc h
      · rcases hw with (rfl | rfl) | ⟨h, _⟩
        · exact symm hab
        · exact refl (symm hab)
        · exact mkR (symm hab) hsa hsc h
      · rcases hw with (h | h) | ⟨_, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (nT h))
    · refine ⟨s, hsl, ?_, ?_, ?_⟩
      · rcases hw with (rfl | rfl) | ⟨h, _⟩
        · exact hab
        · exact refl hab
        · exact mkR hab hsa hsc h
      · rcases hsor with rfl | h
        · exact refl (symm hab)
        · exact mkR (symm hab) hsa hsc h
      · rcases hw with (h | h) | ⟨_, h⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (nT' h))
  · -- triángulos
    intro a b r hab har hbr nab nar nbr hn l h0 hl
    obtain ⟨e, he, hor⟩ := edge_of_hasEdge (hE hab nab)
    have hnil := hf.1
    -- el triángulo tiene testigo bueno en cada paso: si no, sería candidato de la fase 1
    have hTA : ∀ p q, e.1 = p → e.2 = q → p ≠ q → p ≠ r → q ≠ r → H.hasEdge p r = true → H.hasEdge q r = true →
        H.deadTrio p q r = false → r ∈ H.alive → (Idx.of H).trioAlive p q r = true := by
      intro p q hp hq npq npr nqr hpr hqr hd hra
      cases hta : (Idx.of H).trioAlive p q r
      · exfalso
        have hin : (e.1, e.2, r) ∈ H.newTrios (Idx.of H) := by
          unfold newTrios
          refine List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩⟩
          · rw [idx_mem_nbrs, hp]; exact ⟨fun h => npr h.symm, hra, hpr⟩
          · rw [hp, hq]
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', idx_hasEdge, idx_deadTrio]
            exact ⟨⟨⟨fun h => nqr h.symm, hqr⟩, hd⟩, hta⟩
        rw [hnil] at hin; exact absurd hin List.not_mem_nil
      · rfl
    have hra : r ∈ H.alive := har.1.2.1
    have hrc : r.id.step < c := har.2.2
    have wit : ∀ p q, (p = a ∧ q = b) ∨ (p = b ∧ q = a) → (Idx.of H).trioAlive p q r = true →
        ∃ s, s.id.step = l ∧ LowR H c a s ∧ LowR H c b s ∧ LowR H c r s ∧
          (s = a ∨ s = b ∨ s = r ∨ (¬ TF H a b s ∧ ¬ TF H a r s ∧ ¬ TF H b r s)) := by
      intro p q hpq hta
      unfold Idx.trioAlive at hta
      obtain ⟨s, hs, hw⟩ := List.any_eq_true.mp (List.all_eq_true.mp hta l (hrange l h0 hl))
      obtain ⟨hsl, hsa, _⟩ := mem_incAt_iff hs
      have hsc : s.id.step < c := by rw [hsl]; exact hl
      unfold Idx.goodWitness at hw
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true', idx_hasEdge, idx_deadTrio] at hw
      have hrr : LowR H c r r := refl (symm har)
      refine ⟨s, hsl, ?_⟩
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hw with ((rfl | rfl) | rfl) | ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, d1⟩, d2⟩, d3⟩
        · exact ⟨refl hab, symm hab, symm har, Or.inl rfl⟩
        · exact ⟨hab, refl (symm hab), symm hbr, Or.inr (Or.inl rfl)⟩
        · exact ⟨har, hbr, hrr, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨mkR hab hsa hsc e1, mkR (symm hab) hsa hsc e2, mkR hrr hsa hsc e3,
            Or.inr (Or.inr (Or.inr ⟨nT d1, nT d2, nT d3⟩))⟩
      · rcases hw with ((rfl | rfl) | rfl) | ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, d1⟩, d2⟩, d3⟩
        · exact ⟨hab, refl (symm hab), symm hbr, Or.inr (Or.inl rfl)⟩
        · exact ⟨refl hab, symm hab, symm har, Or.inl rfl⟩
        · exact ⟨har, hbr, hrr, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨mkR hab hsa hsc e2, mkR (symm hab) hsa hsc e1, mkR hrr hsa hsc e3,
            Or.inr (Or.inr (Or.inr ⟨nT' d1, nT d3, nT d2⟩))⟩
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply wit a b (Or.inl ⟨rfl, rfl⟩)
      exact hTA a b h1 h2 nab nar nbr (hE har nar) (hE hbr nbr) (dF nab hn) hra
    · apply wit b a (Or.inr ⟨rfl, rfl⟩)
      exact hTA b a h1 h2 (Ne.symm nab) nbr nar (hE hbr nbr) (hE har nar)
        (by cases h : H.deadTrio b a r
            · rfl
            · exact absurd ⟨nab, deadTrio_swap12 h⟩ hn) hra
  · -- T no distingue el orden: 2–3
    intro a b r hab har hbr ⟨hne, hd⟩
    obtain ⟨_, nar, _⟩ := noDeg_TF hnd a b r ⟨hne, hd⟩
    refine ⟨nar, ?_⟩
    unfold deadTrio at hd ⊢
    rw [Bool.and_eq_true] at hd ⊢
    obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd.2
    exact ⟨hE har nar, List.any_eq_true.mpr ⟨t, ht, trioIs_swap23 (a := a) (b := r) (r := b) hti⟩⟩
  · -- 1–2
    intro a b r _ _ _ h
    exact tF_swap12 (a := b) (b := a) h

end GPathB

end AbsSatBingo.Model
