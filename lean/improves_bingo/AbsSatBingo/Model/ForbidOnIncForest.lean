-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnIncForest.lean
import AbsSatBingo.Model.ForbidOnGluePegF

/-!
# El bosque de incidencia (plan del v229, paso 3a)

Una fórmula es **Berge-acíclica** si su grafo de incidencia (variables y cláusulas, arista si la variable está en la
cláusula) es un bosque. Aquí el bosque viene dado con raíz: un padre por vértice y una profundidad que baja hacia la
raíz, y toda incidencia es una arista padre-hijo.

* **`IncForest φ`**: `par`, `dep` y `edge`.
* `parN`, **`Anc`** (antepasado, iterando el padre) y sus propiedades.
* **`Br m v`**: la rama de `v` respecto de `m`: el hijo de `m` que es antepasado de `v`, o «arriba» si `m` no lo es.
* **`br_edge`**: una arista padre-hijo sin `m` no cambia de rama. Por eso ninguna cláusula cruza ramas al quitar `m`
  (`br_clause`).
* **`sep_three`** (paso 3b): en un árbol con raíz, el antepasado común más profundo de alguna pareja de tres bloques
  deja los bloques distintos de él en ramas distintas.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

/-- Un vértice del grafo de incidencia: una variable o una cláusula (por su índice). -/
inductive Vx where
  | var (z : Nat)
  | cls (j : Nat)
  deriving DecidableEq

/-- **El bosque de incidencia con raíz.** -/
structure IncForest (φ : Cnf) where
  par    : Vx → Option Vx
  dep    : Vx → Nat
  dep_lt : ∀ v p, par v = some p → dep p < dep v
  edge   : ∀ (j : Nat) (c : Clause) (z : Nat), φ.clauses[j]? = some c → ClVar c z →
             par (.var z) = some (.cls j) ∨ par (.cls j) = some (.var z)

namespace IncForest

variable {φ : Cnf} (F : IncForest φ)

/-- El antepasado `n` pasos arriba. -/
def parN : Nat → Vx → Option Vx
  | 0, v => some v
  | n + 1, v => match F.par v with
    | none => none
    | some p => parN n p

/-- `a` es antepasado (o igual) de `v`. -/
def Anc (a v : Vx) : Prop := ∃ n, F.parN n v = some a

theorem anc_refl (v : Vx) : F.Anc v v := ⟨0, rfl⟩

theorem anc_par {v p a : Vx} (hp : F.par v = some p) (h : F.Anc a p) : F.Anc a v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by simp only [parN, hp]; exact hn⟩


/-- Un antepasado de `v` distinto de `v` lo es de su padre. -/
theorem anc_of_par {v p a : Vx} (hp : F.par v = some p) (h : F.Anc a v) (hne : a ≠ v) : F.Anc a p := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp only [parN, Option.some.injEq] at hn; exact absurd hn.symm hne
  | succ n => simp only [parN, hp] at hn; exact ⟨n, hn⟩

theorem parN_add (n k : Nat) (v : Vx) : F.parN (n + k) v = (F.parN n v).bind (F.parN k) := by
  induction n generalizing v with
  | zero => simp [parN]
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [parN]
    split
    · rfl
    · exact ih _

theorem anc_trans {a b c : Vx} (h1 : F.Anc a b) (h2 : F.Anc b c) : F.Anc a c := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨n, hn⟩ := h2
  exact ⟨n + k, by rw [F.parN_add, hn]; exact hk⟩

theorem anc_par_trans {a c v : Vx} (h1 : F.par c = some a) (h2 : F.Anc c v) : F.Anc a v :=
  F.anc_trans (F.anc_par h1 (F.anc_refl a)) h2

/-- Los antepasados de `v` están en cadena. -/
theorem anc_total {a b v : Vx} (ha : F.Anc a v) (hb : F.Anc b v) : F.Anc a b ∨ F.Anc b a := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨n', hn'⟩ := hb
  rcases Nat.le_total n n' with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [F.parN_add, hn] at hn'
    exact Or.inr ⟨d, hn'⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [F.parN_add, hn'] at hn
    exact Or.inl ⟨d, hn⟩

theorem dep_le_of_anc {a v : Vx} (h : F.Anc a v) : F.dep a ≤ F.dep v := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing v with
  | zero => simp only [parN, Option.some.injEq] at hn; rw [hn]; exact Nat.le_refl _
  | succ n ih =>
    simp only [parN] at hn
    split at hn
    · cases hn
    · rename_i p hp
      exact Nat.le_trans (ih hn) (Nat.le_of_lt (F.dep_lt v p hp))

theorem dep_lt_of_anc {a v : Vx} (h : F.Anc a v) (hne : a ≠ v) : F.dep a < F.dep v := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp only [parN, Option.some.injEq] at hn; exact absurd hn.symm hne
  | succ n =>
    simp only [parN] at hn
    split at hn
    · cases hn
    · rename_i p hp
      exact Nat.lt_of_le_of_lt (F.dep_le_of_anc ⟨n, hn⟩) (F.dep_lt v p hp)

/-- **La rama de `v` respecto de `m`**: `some c` si `c` es el hijo de `m` antepasado de `v`; `none` si `m` no es
antepasado de `v` («arriba»). -/
def InBr (m : Vx) (v : Vx) (c : Option Vx) : Prop :=
  (c = none ∧ ¬ F.Anc m v) ∨ (∃ c', c = some c' ∧ F.par c' = some m ∧ F.Anc c' v)

/-- La rama existe para todo `v ≠ m`. -/
theorem inBr_exists {m v : Vx} (hne : v ≠ m) : ∃ c, F.InBr m v c := by
  classical
  by_cases h : F.Anc m v
  · obtain ⟨n, hn⟩ := h
    induction n generalizing v with
    | zero => simp only [parN, Option.some.injEq] at hn; exact absurd hn hne
    | succ n ih =>
      simp only [parN] at hn
      split at hn
      · cases hn
      · rename_i p hp
        by_cases hpm : p = m
        · subst hpm
          exact ⟨some v, Or.inr ⟨v, rfl, hp, F.anc_refl v⟩⟩
        · obtain ⟨c, hc⟩ := ih hpm hn
          rcases hc with ⟨_, hno⟩ | ⟨c', rfl, h1, h2⟩
          · exact absurd ⟨n, hn⟩ hno
          · exact ⟨some c', Or.inr ⟨c', rfl, h1, F.anc_par hp h2⟩⟩
  · exact ⟨none, Or.inl ⟨rfl, h⟩⟩

/-- La rama es única. -/
theorem inBr_unique {m v : Vx} {c d : Option Vx} (hc : F.InBr m v c) (hd : F.InBr m v d) : c = d := by
  rcases hc with ⟨rfl, h1⟩ | ⟨c', rfl, h1, h2⟩ <;> rcases hd with ⟨rfl, h3⟩ | ⟨d', rfl, h3, h4⟩
  · rfl
  · exact absurd (F.anc_par_trans h3 h4) h1
  · exact absurd (F.anc_par_trans h1 h2) h3
  · -- dos hijos de `m` antepasados de `v`: están en cadena, y uno propio del otro lo sería de `m`
    have key : ∀ {c d : Vx}, F.par c = some m → F.par d = some m → F.Anc c d → c = d := by
      intro c d hc hd hcd
      by_cases e : c = d
      · exact e
      · have hcm : F.Anc c m := F.anc_of_par hd hcd e
        have l1 := F.dep_le_of_anc hcm
        have l2 := F.dep_lt c m hc
        omega
    rcases F.anc_total h2 h4 with h | h
    · rw [key h1 h3 h]
    · rw [key h3 h1 h]

/-- Subir por una arista sin pasar por `m` no cambia de rama. -/
theorem inBr_par {m v p : Vx} {c : Option Vx} (hp : F.par v = some p) (hvm : v ≠ m) (h : F.InBr m p c) :
    F.InBr m v c := by
  rcases h with ⟨rfl, h1⟩ | ⟨c', rfl, h1, h2⟩
  · exact Or.inl ⟨rfl, fun h => h1 (F.anc_of_par hp h (Ne.symm hvm))⟩
  · exact Or.inr ⟨c', rfl, h1, F.anc_par hp h2⟩

open Classical in
/-- La rama de `v` respecto de `m` (y `none` para `m`). -/
noncomputable def br (m v : Vx) : Option Vx :=
  if h : v ≠ m then Classical.choose (F.inBr_exists h) else none

theorem br_spec {m v : Vx} (h : v ≠ m) : F.InBr m v (F.br m v) := by
  unfold br; rw [dif_pos h]; exact Classical.choose_spec (F.inBr_exists h)

/-- **Una arista padre-hijo sin `m` no cambia de rama.** -/
theorem br_edge {m v p : Vx} (hp : F.par v = some p) (hvm : v ≠ m) (hpm : p ≠ m) : F.br m v = F.br m p :=
  F.inBr_unique (F.br_spec hvm) (F.inBr_par hp hvm (F.br_spec hpm))

/-- **Ninguna cláusula cruza ramas**: si ni la cláusula ni sus variables son `m`, todas sus variables están en la
rama de la cláusula. -/
theorem br_clause {m : Vx} {j : Nat} {c : Clause} (hj : φ.clauses[j]? = some c) {z : Nat} (hz : ClVar c z)
    (hzm : Vx.var z ≠ m) (hjm : Vx.cls j ≠ m) : F.br m (.var z) = F.br m (.cls j) := by
  rcases F.edge j c z hj hz with h | h
  · exact F.br_edge h hzm hjm
  · exact (F.br_edge h hjm hzm).symm

-- ============================================================
-- El vértice que separa tres bloques (paso 3b)
-- ============================================================

/-- Entre los vértices que cumplen `Q`, con profundidad acotada, hay uno de profundidad máxima. -/
theorem exists_deepest (Q : Vx → Prop) (B : Nat) (hB : ∀ a, Q a → F.dep a ≤ B) :
    ∀ a, Q a → ∃ m, Q m ∧ ∀ a', Q a' → F.dep a' ≤ F.dep m := by
  classical
  suffices h : ∀ n a, Q a → B - F.dep a ≤ n → ∃ m, Q m ∧ ∀ a', Q a' → F.dep a' ≤ F.dep m from
    fun a ha => h _ a ha (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro a ha hn
    exact ⟨a, ha, fun a' ha' => Nat.le_trans (hB a' ha') (by omega)⟩
  | succ n ih =>
    intro a ha hn
    by_cases hmax : ∀ a', Q a' → F.dep a' ≤ F.dep a
    · exact ⟨a, ha, hmax⟩
    · obtain ⟨a', ha', hlt⟩ : ∃ a', Q a' ∧ F.dep a < F.dep a' := by
        refine Classical.byContradiction fun hno => hmax fun a' ha' => ?_
        exact Nat.le_of_not_lt fun h => hno ⟨a', ha', h⟩
      exact ih a' ha' (by have := hB a' ha'; omega)

/-- `a` es antepasado común de dos de los tres bloques. -/
def PairAnc (b : Fin 3 → Vx) (a : Vx) : Prop := ∃ i j, i ≠ j ∧ F.Anc a (b i) ∧ F.Anc a (b j)

/-- **El separador de tres bloques**: en un árbol con raíz, el antepasado común más profundo de alguna pareja deja
los bloques distintos de él en ramas distintas. -/
theorem sep_three {r : Vx} (hroot : ∀ v, F.Anc r v) (b : Fin 3 → Vx) :
    ∃ m, F.PairAnc b m ∧ ∀ i j, i ≠ j → b i = m ∨ b j = m ∨ F.br m (b i) ≠ F.br m (b j) := by
  classical
  have hQ : F.PairAnc b r := ⟨0, 1, by decide, hroot _, hroot _⟩
  have hb : ∀ i, F.dep (b i) ≤ F.dep (b 0) + F.dep (b 1) + F.dep (b 2) := by
    intro i
    match i with
    | ⟨0, _⟩ => show F.dep (b 0) ≤ _; omega
    | ⟨1, _⟩ => show F.dep (b 1) ≤ _; omega
    | ⟨2, _⟩ => show F.dep (b 2) ≤ _; omega
  obtain ⟨m, hm, hmax⟩ := F.exists_deepest (F.PairAnc b) _
    (fun a ⟨i, _, _, hi, _⟩ => Nat.le_trans (F.dep_le_of_anc hi) (hb i)) r hQ
  refine ⟨m, hm, fun i j hij => ?_⟩
  by_cases hi : b i = m
  · exact Or.inl hi
  by_cases hj : b j = m
  · exact Or.inr (Or.inl hj)
  refine Or.inr (Or.inr fun heq => ?_)
  have si := F.br_spec hi
  have sj := F.br_spec hj
  rw [← heq] at sj
  rcases si with ⟨e, h1⟩ | ⟨c', e, h1, h2⟩
  · -- arriba: `m` no es antepasado de ninguno de los dos, pero lo es de una pareja, que corta a `{i, j}`
    rw [e] at sj
    rcases sj with ⟨_, h3⟩ | ⟨c'', e', _, _⟩
    · obtain ⟨k, l, hkl, hk, hl⟩ := hm
      have cut : ∀ i j k l : Fin 3, i ≠ j → k ≠ l → k = i ∨ k = j ∨ l = i ∨ l = j := by decide
      rcases cut i j k l hij hkl with e1 | e1 | e1 | e1 <;> subst e1
      · exact h1 hk
      · exact h3 hk
      · exact h1 hl
      · exact h3 hl
    · cases e'
  · -- el mismo hijo `c'` de `m` es antepasado de los dos: una pareja con antepasado más profundo
    rw [e] at sj
    rcases sj with ⟨e', _⟩ | ⟨c'', e', _, h4⟩
    · cases e'
    · cases e'
      have := hmax c' ⟨i, j, hij, h2, h4⟩
      have := F.dep_lt c' m h1
      omega

end IncForest

end AbsSatBingo.Model
