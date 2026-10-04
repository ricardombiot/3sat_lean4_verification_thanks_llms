-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainN.lean
import AbsSatBingo.Model.ForbidOnChain5C

/-!
# Cadenas de `n` bloques: la infraestructura

`ForbidOnChain4` y `ForbidOnChain5` repiten la rama de varias fuentes para cada longitud (`glue4`, `glue5`). Aquí, una
sola vez para cualquier `n`:

* **`ChainN φ n zone`**: una función de zona lo describe todo. Las variables de dentro del bloque `j` tienen zona `j`
  (`0 ≤ j < n`); el separador entre los bloques `i - 1` e `i` tiene zona `n + i` (`1 ≤ i < n`, uno por zona); lo que
  está fuera de la cadena, zona `n` o `≥ 2n`. Así los bloques, la pertenencia y la disjunción se leen de la zona. Los
  bloques de los extremos tienen a lo sumo dos variables de dentro; los de en medio, a lo sumo una. Cada cláusula está
  entera en un bloque (`BlkN`) o entera fuera (`OutN`).
* **`glueN n zone src a0`**: una fuente por bloque: `src j` en el interior del bloque `j` y en el separador de su
  derecha (`OwnN`), `a0` fuera.
* `gN_own`, `gN_blk` (con las fuentes vecinas leyendo igual el separador que comparten, `JoinN`), `gN_out`;
  **`glueN_P0`**, **`glueN_P`** (son de `P` las fuentes de los bloques que contienen a `v`), **`glueN_pid`**,
  **`glueN_tri`**.
* `sepCover_of_chainN`: la cobertura por separadores (T1 del lector por separadores) cuando toda cláusula está en
  un bloque.
* Validación: `chainN_of_chain5Data`: los datos de cinco bloques de `ForbidOnChain5` son una `ChainN φ 5`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- El bloque cerrado `j`: su interior y sus separadores. -/
def BlkN (n : Nat) (zone : Nat → Nat) (j z : Nat) : Prop :=
  zone z = j ∨ (1 ≤ j ∧ zone z = n + j) ∨ (j + 1 < n ∧ zone z = n + j + 1)

/-- Lo que lleva la fuente del bloque `j`: su interior y el separador de su derecha. -/
def OwnN (n : Nat) (zone : Nat → Nat) (j z : Nat) : Prop := zone z = j ∨ (j + 1 < n ∧ zone z = n + j + 1)

/-- Fuera de la cadena. -/
def OutN (n : Nat) (zone : Nat → Nat) (z : Nat) : Prop := zone z = n ∨ 2 * n ≤ zone z

/-- **Una cadena de `n` bloques.** -/
structure ChainN (φ : Cnf) (n : Nat) (zone : Nat → Nat) : Prop where
  two   : 2 ≤ n
  sepv  : ∀ z, n + 1 ≤ zone z → zone z < 2 * n → z < φ.nVars
  sep1  : ∀ i, 1 ≤ i → i < n → Le1 (fun z => zone z = n + i)
  card0 : No3 (fun z => zone z = 0)
  cardL : No3 (fun z => zone z = n - 1)
  cardM : ∀ j, 1 ≤ j → j + 1 < n → Le1 (fun z => zone z = j)
  cl    : ∀ c ∈ φ.clauses, ClIn (OutN n zone) c ∨ ∃ j, j < n ∧ ClIn (BlkN n zone j) c

/-- **Una fuente por bloque.** -/
noncomputable def glueN (n : Nat) (zone : Nat → Nat) (src : Nat → Assign) (a0 : Assign) : Assign := fun z =>
  if zone z < n then src (zone z) z
  else if n + 1 ≤ zone z ∧ zone z < 2 * n then src (zone z - n - 1) z
  else a0 z

/-- Las fuentes vecinas leen igual el separador que comparten. -/
def JoinN (n : Nat) (zone : Nat → Nat) (src : Nat → Assign) : Prop :=
  ∀ i, 1 ≤ i → i < n → ∀ z, zone z = n + i → src (i - 1) z = src i z

section GlueN

variable {n : Nat} {zone : Nat → Nat} {src : Nat → Assign} {a0 : Assign}

theorem gN_own {j z : Nat} (hj : j < n) (h : OwnN n zone j z) : glueN n zone src a0 z = src j z := by
  unfold glueN
  rcases h with h | ⟨h1, h⟩
  · rw [if_pos (by omega), h]
  · rw [if_neg (by omega), if_pos (by omega), h, show n + j + 1 - n - 1 = j by omega]

theorem gN_blk (hJ : JoinN n zone src) {j z : Nat} (hj : j < n) (h : BlkN n zone j z) :
    glueN n zone src a0 z = src j z := by
  rcases h with h | ⟨h1, h⟩ | ⟨h1, h⟩
  · exact gN_own hj (Or.inl h)
  · unfold glueN
    rw [if_neg (by omega), if_pos (by omega), h, show n + j - n - 1 = j - 1 by omega]
    exact hJ j h1 hj z h
  · exact gN_own hj (Or.inr ⟨h1, h⟩)

theorem gN_out {z : Nat} (h : OutN n zone z) : glueN n zone src a0 z = a0 z := by
  unfold glueN
  rcases h with h | h
  · rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_neg (by omega), if_neg (by omega)]

variable {P0 P : Assign → Prop} {σ : Int}

/-- **La rama de `n` fuentes es de `P0`** si las fuentes vecinas leen igual el separador que comparten. -/
theorem glueN_P0 (hl : LocPair φ P0 P σ) (D : ChainN φ n zone) (h0 : P0 a0) (hs : ∀ j, j < n → P0 (src j))
    (hJ : JoinN n zone src) : P0 (glueN n zone src a0) := by
  refine p0_of_sources hl ⟨a0, h0⟩ (fun z => ?_) (fun c hc => ?_)
  · by_cases h1 : zone z < n
    · exact ⟨src (zone z), hs _ h1, gN_own h1 (Or.inl rfl)⟩
    by_cases h2 : n + 1 ≤ zone z ∧ zone z < 2 * n
    · exact ⟨src (zone z - n - 1), hs _ (by omega), gN_own (by omega) (Or.inr ⟨by omega, by omega⟩)⟩
    · exact ⟨a0, h0, gN_out (by unfold OutN; omega)⟩
  · rcases D.cl c hc with ⟨o1, o2, o3⟩ | ⟨j, hj, i1, i2, i3⟩
    · exact ⟨a0, h0, gN_out o1, gN_out o2, gN_out o3⟩
    · exact ⟨src j, hs j hj, gN_blk hJ hj i1, gN_blk hJ hj i2, gN_blk hJ hj i3⟩

/-- Un bloque no es de fuera. -/
theorem not_out_of_blk {j z : Nat} (hj : j < n) (h : BlkN n zone j z) : ¬ OutN n zone z := by
  rintro (h' | h') <;> rcases h with h | ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-- **Y de `P`**, si `v` está en la cadena y son de `P` las fuentes de los bloques que lo contienen. -/
theorem glueN_P (hl : LocPair φ P0 P σ) (D : ChainN φ n zone) {v : Nat} (hv : stepVar φ σ = some v)
    (hvin : ∃ j, j < n ∧ BlkN n zone j v) (h0 : P0 a0) (hs : ∀ j, j < n → P0 (src j)) (hJ : JoinN n zone src)
    (hP : ∀ j, j < n → BlkN n zone j v → P (src j)) : P (glueN n zone src a0) := by
  refine p_of_sources hl (glueN_P0 hl D h0 hs hJ) (fun h => by rw [hv] at h; cases h) (fun z hz => ?_)
  rw [hv] at hz; cases hz
  obtain ⟨jv, hjv, hbv⟩ := hvin
  refine ⟨⟨src jv, hP jv hjv hbv, gN_blk hJ hjv hbv⟩, fun c hc hcv => ?_⟩
  rcases D.cl c hc with ho | ⟨j, hj, hin⟩
  · exact absurd (clIn_var ho hcv) (not_out_of_blk hjv hbv)
  · obtain ⟨i1, i2, i3⟩ := hin
    exact ⟨src j, hP j hj (clIn_var ⟨i1, i2, i3⟩ hcv), gN_blk hJ hj i1, gN_blk hJ hj i2, gN_blk hJ hj i3⟩

/-- **La rama de `n` fuentes pasa por las ventanas de `a0`** si cada fuente coincide con `a0` en lo que lleva. -/
theorem glueN_pid {i j l k : Int} (hk : k = i ∨ k = j ∨ k = l)
    (ha : ∀ b, b < n → Agr φ i j l (OwnN n zone b) (src b) a0) :
    pidOfAssign φ (glueN n zone src a0) k = pidOfAssign φ a0 k := by
  refine pid_of_agree (fun k' z hw hz => ?_)
  have iw : InW φ i j l z := ⟨k, k', hk, hw, hz⟩
  by_cases h1 : zone z < n
  · rw [gN_own h1 (Or.inl rfl)]; exact ha _ h1 z (Or.inl rfl) iw
  by_cases h2 : n + 1 ≤ zone z ∧ zone z < 2 * n
  · have ho : OwnN n zone (zone z - n - 1) z := Or.inr ⟨by omega, by omega⟩
    rw [gN_own (by omega) ho]; exact ha _ (by omega) z ho iw
  · exact gN_out (by unfold OutN; omega)

end GlueN

namespace GPathB

variable {P0 P : Assign → Prop} {Nn σ : Int}

/-- **Cerrar un triángulo con `n` fuentes.** -/
theorem glueN_tri {n : Nat} {zone : Nat → Nat} (hl : LocPair φ P0 P σ) (D : ChainN φ n zone) {v : Nat}
    (hv : stepVar φ σ = some v) (hvin : ∃ j, j < n ∧ BlkN n zone j v) {x u w : PathNodeId} {a0 : Assign}
    {src : Nat → Assign} (h0 : P0 a0) (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) (hs : ∀ j, j < n → P0 (src j)) (hJ : JoinN n zone src)
    (hP : ∀ j, j < n → BlkN n zone j v → P (src j))
    (ha : ∀ b, b < n → Agr φ x.id.step u.id.step w.id.step (OwnN n zone b) (src b) a0) : TriOf φ P x u w :=
  ⟨glueN n zone src a0, glueN_P hl D hv hvin h0 hs hJ hP, (glueN_pid (Or.inl rfl) ha).trans hx0,
    (glueN_pid (Or.inr (Or.inl rfl)) ha).trans hu0, (glueN_pid (Or.inr (Or.inr rfl)) ha).trans hw0⟩

end GPathB

/-! ## La cobertura por separadores -/

section Cover

variable {n : Nat} {zone : Nat → Nat}

/-- Un separador. -/
def SepN (n : Nat) (zone : Nat → Nat) (z : Nat) : Prop := n + 1 ≤ zone z ∧ zone z < 2 * n

/-- En un bloque, lo que no es separador es de su interior. -/
theorem blk_inner {j z : Nat} (hj : j < n) (h : BlkN n zone j z) (hs : ¬ SepN n zone z) : zone z = j := by
  unfold SepN at hs
  rcases h with h | ⟨h1, h⟩ | ⟨h1, h⟩
  · exact h
  · omega
  · omega

/-- La parte de cada variable: el interior de su bloque, o ella sola. -/
def partN (n : Nat) (zone : Nat → Nat) (z : Nat) : Nat := if zone z < n then zone z else z + 2 * n

/-- **La cobertura por separadores de una cadena**, si toda cláusula está en un bloque y la lista `S` son sus
separadores. -/
theorem sepCover_of_chainN (D : ChainN φ n zone) (hb : ∀ c ∈ φ.clauses, ∃ j, j < n ∧ ClIn (BlkN n zone j) c)
    {S : List Nat} (hS : ∀ z, z ∈ S ↔ SepN n zone z) : SepCover φ S (partN n zone) := by
  refine ⟨fun c hc z z' hz hz' hzS hz'S => ?_, fun p y1 y2 y3 n1 n2 n3 h1 h2 h3 d12 d13 d23 => ?_⟩
  · obtain ⟨j, hj, hin⟩ := hb c hc
    have e1 := blk_inner hj (clIn_var hin hz) (fun h => hzS ((hS z).mpr h))
    have e2 := blk_inner hj (clIn_var hin hz') (fun h => hz'S ((hS z').mpr h))
    unfold partN; rw [e1, e2, if_pos hj, if_pos hj]
  · unfold partN at h1 h2 h3
    split at h1 <;> split at h2 <;> split at h3
    · have e1 : zone y1 = p := h1
      have e2 : zone y2 = p := h2
      have e3 : zone y3 = p := h3
      by_cases p0 : p = 0
      · subst p0; exact D.card0 y1 y2 y3 e1 e2 e3 d12 d13 d23
      by_cases pL : p = n - 1
      · subst pL; exact D.cardL y1 y2 y3 e1 e2 e3 d12 d13 d23
      · exact GPathB.no3_of_le1 (D.cardM p (by omega) (by omega)) y1 y2 y3 e1 e2 e3 d12 d13 d23
    all_goals omega

end Cover

/-! ## Validación: los cinco bloques de `ForbidOnChain5` -/

section Five

variable {s1 s2 s3 s4 : Nat} {zone : Nat → Nat}

/-- La zona de `ChainN φ 5` de unos datos de cinco bloques: los separadores, `6 … 9`; lo de fuera, `10`. -/
def zone5N (s1 s2 s3 s4 : Nat) (zone : Nat → Nat) (z : Nat) : Nat :=
  if z = s1 then 6 else if z = s2 then 7 else if z = s3 then 8 else if z = s4 then 9
  else if zone z < 5 then zone z else 10

/-- Los cinco casos de `zone5N`. -/
theorem zone5N_cases (s1 s2 s3 s4 : Nat) (zone : Nat → Nat) (z : Nat) :
    (z = s1 ∧ zone5N s1 s2 s3 s4 zone z = 6) ∨ (z = s2 ∧ zone5N s1 s2 s3 s4 zone z = 7) ∨
    (z = s3 ∧ zone5N s1 s2 s3 s4 zone z = 8) ∨ (z = s4 ∧ zone5N s1 s2 s3 s4 zone z = 9) ∨
    (zone z < 5 ∧ zone5N s1 s2 s3 s4 zone z = zone z) ∨
    (z ≠ s1 ∧ z ≠ s2 ∧ z ≠ s3 ∧ z ≠ s4 ∧ 5 ≤ zone z ∧ zone5N s1 s2 s3 s4 zone z = 10) := by
  unfold zone5N
  by_cases a : z = s1
  · exact Or.inl ⟨a, if_pos a⟩
  rw [if_neg a]
  by_cases b : z = s2
  · exact Or.inr (Or.inl ⟨b, if_pos b⟩)
  rw [if_neg b]
  by_cases c : z = s3
  · exact Or.inr (Or.inr (Or.inl ⟨c, if_pos c⟩))
  rw [if_neg c]
  by_cases d : z = s4
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, if_pos d⟩)))
  rw [if_neg d]
  by_cases e : zone z < 5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, if_pos e⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, c, d, by omega, if_neg e⟩))))

theorem zone5N_inner (D : Chain5Data φ s1 s2 s3 s4 zone) {z : Nat} (h : zone z < 5) :
    zone5N s1 s2 s3 s4 zone z = zone z := by
  have := D.z1; have := D.z2; have := D.z3; have := D.z4
  rcases zone5N_cases s1 s2 s3 s4 zone z with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, e⟩ | ⟨_, _, _, _, _, _⟩ <;> omega

theorem zone5N_eq_inner {z j : Nat} (hj : j < 5)
    (h : zone5N s1 s2 s3 s4 zone z = j) : zone z = j := by
  rcases zone5N_cases s1 s2 s3 s4 zone z with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, _, _, _, _, e⟩ <;> omega

theorem chainN_of_chain5Data (D : Chain5Data φ s1 s2 s3 s4 zone) : ChainN φ 5 (zone5N s1 s2 s3 s4 zone) := by
  have z1 := D.z1; have z2 := D.z2; have z3 := D.z3; have z4 := D.z4
  have n12 := D.n12; have n13 := D.n13; have n14 := D.n14; have n23 := D.n23; have n24 := D.n24
  have n34 := D.n34
  have e1 : zone5N s1 s2 s3 s4 zone s1 = 6 := by unfold zone5N; simp
  have e2 : zone5N s1 s2 s3 s4 zone s2 = 7 := by unfold zone5N; simp [Ne.symm n12]
  have e3 : zone5N s1 s2 s3 s4 zone s3 = 8 := by unfold zone5N; simp [Ne.symm n13, Ne.symm n23]
  have e4 : zone5N s1 s2 s3 s4 zone s4 = 9 := by unfold zone5N; simp [Ne.symm n14, Ne.symm n24, Ne.symm n34]
  -- los separadores, por su zona
  have hsep : ∀ z, 6 ≤ zone5N s1 s2 s3 s4 zone z → zone5N s1 s2 s3 s4 zone z < 10 →
      (z = s1 ∧ zone5N s1 s2 s3 s4 zone z = 6) ∨ (z = s2 ∧ zone5N s1 s2 s3 s4 zone z = 7) ∨
      (z = s3 ∧ zone5N s1 s2 s3 s4 zone z = 8) ∨ (z = s4 ∧ zone5N s1 s2 s3 s4 zone z = 9) := by
    intro z a b
    rcases zone5N_cases s1 s2 s3 s4 zone z with h | h | h | h | ⟨_, e⟩ | ⟨_, _, _, _, _, e⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · omega
    · omega
  have card : ∀ j, j < 5 → ∀ z, zone5N s1 s2 s3 s4 zone z = j → zone z = j :=
    fun j hj z h => zone5N_eq_inner hj h
  refine ⟨by omega, fun z a b => ?_, fun i a b z z' h h' => ?_, fun y1 y2 y3 a b c => ?_,
    fun y1 y2 y3 a b c => ?_, fun j a b z z' h h' => ?_, fun c hc => ?_⟩
  · rcases hsep z (by omega) (by omega) with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact D.s1v
    · exact D.s2v
    · exact D.s3v
    · exact D.s4v
  · rcases hsep z (by omega) (by omega) with ⟨rfl, q⟩ | ⟨rfl, q⟩ | ⟨rfl, q⟩ | ⟨rfl, q⟩ <;>
    rcases hsep z' (by omega) (by omega) with ⟨rfl, q'⟩ | ⟨rfl, q'⟩ | ⟨rfl, q'⟩ | ⟨rfl, q'⟩ <;>
    first | rfl | omega
  · exact D.card0 y1 y2 y3 (card 0 (by omega) _ a) (card 0 (by omega) _ b) (card 0 (by omega) _ c)
  · exact D.card4 y1 y2 y3 (card 4 (by omega) _ a) (card 4 (by omega) _ b) (card 4 (by omega) _ c)
  · have hz := card j (by omega) _ h; have hz' := card j (by omega) _ h'
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl
    · exact D.card1 z z' hz hz'
    · exact D.card2 z z' hz hz'
    · exact D.card3 z z' hz hz'
  · -- cada opción de `Chain5Data.cl`, a su bloque
    have inner : ∀ {z j : Nat}, zone z = j → j < 5 → zone5N s1 s2 s3 s4 zone z = j := by
      intro z j h hj; rw [zone5N_inner D (by omega), h]
    rcases D.cl c hc with hi | hi | hi | hi | hi | hi
    · refine Or.inl (clIn_mono hi (fun z ⟨a, b1, b2, b3, b4⟩ => Or.inr ?_))
      rcases zone5N_cases s1 s2 s3 s4 zone z with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _⟩ | ⟨_, _, _, _, _, e⟩
      · exact absurd h b1
      · exact absurd h b2
      · exact absurd h b3
      · exact absurd h b4
      · omega
      · omega
    · refine Or.inr ⟨0, by omega, clIn_mono hi (fun z h => ?_)⟩
      rcases h with h | rfl
      · exact Or.inl (inner h (by omega))
      · exact Or.inr (Or.inr ⟨by omega, e1⟩)
    · refine Or.inr ⟨1, by omega, clIn_mono hi (fun z h => ?_)⟩
      rcases h with rfl | h | rfl
      · exact Or.inr (Or.inl ⟨by omega, e1⟩)
      · exact Or.inl (inner h (by omega))
      · exact Or.inr (Or.inr ⟨by omega, e2⟩)
    · refine Or.inr ⟨2, by omega, clIn_mono hi (fun z h => ?_)⟩
      rcases h with rfl | h | rfl
      · exact Or.inr (Or.inl ⟨by omega, e2⟩)
      · exact Or.inl (inner h (by omega))
      · exact Or.inr (Or.inr ⟨by omega, e3⟩)
    · refine Or.inr ⟨3, by omega, clIn_mono hi (fun z h => ?_)⟩
      rcases h with rfl | h | rfl
      · exact Or.inr (Or.inl ⟨by omega, e3⟩)
      · exact Or.inl (inner h (by omega))
      · exact Or.inr (Or.inr ⟨by omega, e4⟩)
    · refine Or.inr ⟨4, by omega, clIn_mono hi (fun z h => ?_)⟩
      rcases h with rfl | h
      · exact Or.inr (Or.inl ⟨by omega, e4⟩)
      · exact Or.inl (inner h (by omega))

end Five

end AbsSatBingo.Model
