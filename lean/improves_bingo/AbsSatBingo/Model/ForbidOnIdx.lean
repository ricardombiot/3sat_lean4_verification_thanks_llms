-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnIdx.lean
import AbsSatBingo.Model.ForbidOn

/-!
# El índice dice lo mismo que las listas (`docs/plans/lean_forbid_on.md`, F3)

`Idx.of g` guarda en tablas hash lo que `g` guarda en listas. Sus consultas son las de listas: aristas
(`idx_hasEdge`), tríos (`idx_deadTrio`), vivos (`idx_alive`), vecinos (`idx_mem_nbr`), y con ellas la posesión y el
corte de un lado (`idx_adjb`, `idx_sideForbids`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

variable (g : GPathB)

-- ============================================================
-- Aristas
-- ============================================================

theorem joins_iff (a b : PathNodeId) (e : PathNodeId × PathNodeId) :
    joins a b e = true ↔ (e.1 = a ∧ e.2 = b) ∨ (e.1 = b ∧ e.2 = a) := by
  simp [joins]

theorem edges_fold_contains (a b : PathNodeId) : ∀ (l : List (PathNodeId × PathNodeId))
    (h : Std.HashSet (PathNodeId × PathNodeId)),
    (l.foldl (fun h e => (h.insert (e.1, e.2)).insert (e.2, e.1)) h).contains (a, b) = true ↔
      h.contains (a, b) = true ∨ ∃ e ∈ l, joins a b e = true := by
  intro l
  induction l with
  | nil => intro h; simp
  | cons e es ih =>
    intro h
    rw [List.foldl_cons, ih]
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, Prod.mk.injEq, List.mem_cons,
      exists_eq_or_imp, joins_iff]
    constructor
    · rintro ((h1 | h1 | h1) | ⟨x, hx, hj⟩)
      · exact Or.inr (Or.inl (Or.inr ⟨h1.2, h1.1⟩))
      · exact Or.inr (Or.inl (Or.inl h1))
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨x, hx, hj⟩)
    · rintro (h1 | (h1 | h1) | ⟨x, hx, hj⟩)
      · exact Or.inl (Or.inr (Or.inr h1))
      · exact Or.inl (Or.inr (Or.inl h1))
      · exact Or.inl (Or.inl ⟨h1.2, h1.1⟩)
      · exact Or.inr ⟨x, hx, hj⟩

theorem idx_hasEdge (a b : PathNodeId) : (Idx.of g).hasEdge a b = g.hasEdge a b := by
  apply Bool.eq_iff_iff.mpr
  unfold Idx.hasEdge Idx.of hasEdge
  rw [edges_fold_contains]
  simp [List.any_eq_true]

-- ============================================================
-- Vivos
-- ============================================================

theorem alive_fold_contains (a : PathNodeId) : ∀ (l : List PathNodeId) (h : Std.HashSet PathNodeId),
    (l.foldl (fun h x => h.insert x) h).contains a = true ↔ h.contains a = true ∨ a ∈ l := by
  intro l
  induction l with
  | nil => intro h; simp
  | cons x xs ih =>
    intro h
    rw [List.foldl_cons, ih]
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    constructor
    · rintro ((h1 | h1) | h1)
      · exact Or.inr (Or.inl h1.symm)
      · exact Or.inl h1
      · exact Or.inr (Or.inr h1)
    · rintro (h1 | h1 | h1)
      · exact Or.inl (Or.inr h1)
      · exact Or.inl (Or.inl h1.symm)
      · exact Or.inr h1

theorem idx_alive (a : PathNodeId) : (Idx.of g).alive.contains a = true ↔ a ∈ g.alive := by
  unfold Idx.of
  rw [alive_fold_contains]
  simp

-- ============================================================
-- Tríos
-- ============================================================

theorem mem_perms_iff (a b r : PathNodeId) (t : PathNodeId × PathNodeId × PathNodeId) :
    (a, b, r) ∈ perms t.1 t.2.1 t.2.2 ↔ trioIs a b r t = true := by
  obtain ⟨x, y, z⟩ := t
  simp only [perms, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, trioIs, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩) <;> simp
  · rintro (((((⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩) | ⟨⟨rfl, rfl⟩, rfl⟩) | ⟨⟨rfl, rfl⟩, rfl⟩) |
      ⟨⟨rfl, rfl⟩, rfl⟩) | ⟨⟨rfl, rfl⟩, rfl⟩) <;> simp

theorem trios_fold_contains (a b r : PathNodeId) : ∀ (l : List (PathNodeId × PathNodeId × PathNodeId))
    (h : Std.HashSet (PathNodeId × PathNodeId × PathNodeId)),
    (l.foldl (fun h t => h.insertMany (perms t.1 t.2.1 t.2.2)) h).contains (a, b, r) = true ↔
      h.contains (a, b, r) = true ∨ ∃ t ∈ l, trioIs a b r t = true := by
  intro l
  induction l with
  | nil => intro h; simp
  | cons t ts ih =>
    intro h
    rw [List.foldl_cons, ih, Std.HashSet.contains_insertMany_list]
    simp only [Bool.or_eq_true, List.contains_iff_mem, mem_perms_iff, List.mem_cons, exists_eq_or_imp]
    exact or_assoc

theorem idx_trios (a b r : PathNodeId) :
    (Idx.of g).trios.contains (a, b, r) = g.trios.any (trioIs a b r) := by
  apply Bool.eq_iff_iff.mpr
  unfold Idx.of
  rw [trios_fold_contains]
  simp [List.any_eq_true]

theorem idx_deadTrio (a b r : PathNodeId) : (Idx.of g).deadTrio a b r = g.deadTrio a b r := by
  unfold Idx.deadTrio deadTrio
  rw [idx_hasEdge, idx_trios]

theorem idx_adjb (x w : PathNodeId) : (Idx.of g).adjb x w = g.adjb x w := by
  unfold Idx.adjb adjb isAlive
  rw [idx_hasEdge]
  congr 2
  apply Bool.eq_iff_iff.mpr
  rw [idx_alive]; simp

theorem idx_sideForbids (a b r : PathNodeId) : (Idx.of g).sideForbids a b r = g.sideForbidsB a b r := by
  unfold Idx.sideForbids sideForbidsB
  rw [idx_adjb, idx_adjb, idx_adjb, idx_deadTrio]

-- ============================================================
-- Vecinos
-- ============================================================

/-- El paso del pliegue de los vecinos (el de `Idx.of`). -/
abbrev nbrStep (m : Std.HashMap PathNodeId (List PathNodeId)) (e : PathNodeId × PathNodeId) :
    Std.HashMap PathNodeId (List PathNodeId) :=
  (m.insert e.1 (e.2 :: m.getD e.1 [])).insert e.2 (e.1 :: (m.insert e.1 (e.2 :: m.getD e.1 [])).getD e.2 [])

theorem nbrStep_mem (a s : PathNodeId) (m : Std.HashMap PathNodeId (List PathNodeId)) (e : PathNodeId × PathNodeId) :
    s ∈ (nbrStep m e).getD a [] ↔ s ∈ m.getD a [] ∨ joins a s e = true := by
  rw [joins_iff]
  simp only [nbrStep, Std.HashMap.getD_insert, beq_iff_eq]
  obtain ⟨x, y⟩ := e
  dsimp only
  by_cases h2 : y = a <;> by_cases h1 : x = a
  · subst h2; subst h1; simp only [if_true, List.mem_cons]
    constructor <;> intro h <;> rcases h with h | h <;> simp_all [eq_comm] <;> exact Or.comm.mp h
  · subst h2; simp only [if_true, h1, if_false, List.mem_cons]
    constructor <;> intro h <;> rcases h with h | h <;> simp_all [eq_comm]
  · subst h1; simp only [if_true, h2, if_false, List.mem_cons]
    constructor <;> intro h <;> rcases h with h | h <;> simp_all [eq_comm]
  · simp only [h1, h2, if_false]; constructor <;> intro h <;> simp_all

theorem nbr_fold_mem (a s : PathNodeId) : ∀ (l : List (PathNodeId × PathNodeId))
    (m : Std.HashMap PathNodeId (List PathNodeId)),
    s ∈ (l.foldl nbrStep m).getD a [] ↔ s ∈ m.getD a [] ∨ ∃ e ∈ l, joins a s e = true := by
  intro l
  induction l with
  | nil => intro m; simp
  | cons e es ih =>
    intro m
    rw [List.foldl_cons, ih, nbrStep_mem]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_assoc

theorem idx_mem_nbr (a s : PathNodeId) : s ∈ (Idx.of g).nbr.getD a [] ↔ g.hasEdge a s = true := by
  show s ∈ (g.edges.foldl nbrStep {}).getD a [] ↔ _
  rw [nbr_fold_mem]
  simp [hasEdge, List.any_eq_true]

theorem idx_mem_nbrs (a s : PathNodeId) :
    s ∈ (Idx.of g).nbrs a ↔ s ≠ a ∧ s ∈ g.alive ∧ g.hasEdge a s = true := by
  unfold Idx.nbrs
  rw [List.mem_filter, idx_mem_nbr]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, idx_alive]
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩⟩; exact ⟨h2, h3, h1⟩
  · rintro ⟨h2, h3, h1⟩; exact ⟨h1, h2, h3⟩

end GPathB

end AbsSatBingo.Model
