-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnPathN.lean
import AbsSatBingo.Model.ForbidOnChainPreM

/-!
# Caminos de unidades: la infraestructura para bloques anchos

En una `ChainN` cada bloque de en medio tiene a lo sumo una variable de dentro y los bloques se unen en **una** variable.
Un bloque ancho (`s, z₁ … z_w, s'`, con las cláusulas `(s, z₁, z₂), (z₁, z₂, z₃), …`) no tiene separadores dentro: sus
cortes son **pares** de variables. La forma general es un camino de unidades:

* **`PathN φ n lo hi`**: cada variable de la cadena vive en las unidades `lo z … hi z` (`lo z < n`); las de fuera,
  `lo z ≥ n`. Cada cláusula está entera en una unidad (`InU`) o entera fuera (`OutU`). El **corte** `k` (entre las
  unidades `k` y `k + 1`) son las variables con `lo z ≤ k < hi z`.
* **`glueP n lo src a0`**: una fuente por unidad; cada variable toma el valor de la fuente de su primera unidad.
* **`JoinP`**: las fuentes vecinas coinciden en su corte. Con eso cada variable vale lo de la fuente de **cualquiera** de
  sus unidades (`gP_in`, por inducción a lo largo del tramo).
* **`glueP_P0`**, **`glueP_P`**, **`glueP_pid`**, **`glueP_tri`**: los gemelos de `glueN_*`.
* Validación: **`pathN_of_chainN`**: toda `ChainN` es un camino de unidades (el separador `i` vive en las unidades
  `i - 1` e `i`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- La variable `z` vive en la unidad `j`. -/
def InU (lo hi : Nat → Nat) (j z : Nat) : Prop := lo z ≤ j ∧ j ≤ hi z

/-- Fuera del camino. -/
def OutU (n : Nat) (lo : Nat → Nat) (z : Nat) : Prop := n ≤ lo z

/-- **Un camino de `n` unidades.** -/
structure PathN (φ : Cnf) (n : Nat) (lo hi : Nat → Nat) : Prop where
  one : 1 ≤ n
  ord : ∀ z, lo z < n → lo z ≤ hi z ∧ hi z < n
  cl  : ∀ c ∈ φ.clauses, ClIn (OutU n lo) c ∨ ∃ j, j < n ∧ ClIn (InU lo hi j) c

/-- **Una fuente por unidad**: cada variable, de la fuente de su primera unidad. -/
noncomputable def glueP (n : Nat) (lo : Nat → Nat) (src : Nat → Assign) (a0 : Assign) : Assign := fun z =>
  if lo z < n then src (lo z) z else a0 z

/-- Las fuentes vecinas coinciden en su corte. -/
def JoinP (lo hi : Nat → Nat) (src : Nat → Assign) : Prop :=
  ∀ k z, lo z ≤ k → k + 1 ≤ hi z → src k z = src (k + 1) z

section GlueP

variable {n : Nat} {lo hi : Nat → Nat} {src : Nat → Assign} {a0 : Assign}

/-- A lo largo del tramo de `z`, todas las fuentes coinciden en `z`. -/
theorem join_up (hJ : JoinP lo hi src) {z : Nat} : ∀ d, lo z + d ≤ hi z → src (lo z) z = src (lo z + d) z := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro h
    rw [ih (by omega), hJ (lo z + d) z (by omega) (by omega)]
    rfl

theorem gP_in (hJ : JoinP lo hi src) {j z : Nat} (hj : j < n) (h : InU lo hi j z) :
    glueP n lo src a0 z = src j z := by
  unfold glueP
  rw [if_pos (by unfold InU at h; omega)]
  have e := join_up hJ (z := z) (j - lo z) (by unfold InU at h; omega)
  rw [e, show lo z + (j - lo z) = j by unfold InU at h; omega]

theorem gP_out {z : Nat} (h : OutU n lo z) : glueP n lo src a0 z = a0 z := by
  unfold glueP OutU at *
  rw [if_neg (by omega)]

variable {P0 P : Assign → Prop} {σ : Int}

/-- **La rama de una fuente por unidad es de `P0`.** -/
theorem glueP_P0 (hl : LocPair φ P0 P σ) (D : PathN φ n lo hi) (h0 : P0 a0) (hs : ∀ j, j < n → P0 (src j))
    (hJ : JoinP lo hi src) : P0 (glueP n lo src a0) := by
  refine p0_of_sources hl ⟨a0, h0⟩ (fun z => ?_) (fun c hc => ?_)
  · by_cases h1 : lo z < n
    · exact ⟨src (lo z), hs _ h1, by unfold glueP; rw [if_pos h1]⟩
    · exact ⟨a0, h0, gP_out (by unfold OutU; omega)⟩
  · rcases D.cl c hc with ⟨o1, o2, o3⟩ | ⟨j, hj, i1, i2, i3⟩
    · exact ⟨a0, h0, gP_out o1, gP_out o2, gP_out o3⟩
    · exact ⟨src j, hs j hj, gP_in hJ hj i1, gP_in hJ hj i2, gP_in hJ hj i3⟩

theorem not_out_of_inU {j z : Nat} (hj : j < n) (h : InU lo hi j z) : ¬ OutU n lo z := by
  unfold InU at h; unfold OutU; omega

/-- **Y de `P`**, si son de `P` las fuentes de las unidades donde vive `v`. -/
theorem glueP_P (hl : LocPair φ P0 P σ) (D : PathN φ n lo hi) {v : Nat} (hv : stepVar φ σ = some v)
    (hvin : ∃ j, j < n ∧ InU lo hi j v) (h0 : P0 a0) (hs : ∀ j, j < n → P0 (src j)) (hJ : JoinP lo hi src)
    (hP : ∀ j, j < n → InU lo hi j v → P (src j)) : P (glueP n lo src a0) := by
  refine p_of_sources hl (glueP_P0 hl D h0 hs hJ) (fun h => by rw [hv] at h; cases h) (fun z hz => ?_)
  rw [hv] at hz; cases hz
  obtain ⟨jv, hjv, hbv⟩ := hvin
  refine ⟨⟨src jv, hP jv hjv hbv, gP_in hJ hjv hbv⟩, fun c hc hcv => ?_⟩
  rcases D.cl c hc with ho | ⟨j, hj, hin⟩
  · exact absurd (clIn_var ho hcv) (not_out_of_inU hjv hbv)
  · obtain ⟨i1, i2, i3⟩ := hin
    exact ⟨src j, hP j hj (clIn_var ⟨i1, i2, i3⟩ hcv), gP_in hJ hj i1, gP_in hJ hj i2, gP_in hJ hj i3⟩

/-- **La rama pasa por las ventanas de `a0`** si cada fuente coincide con `a0` en lo leído de las variables que
empiezan en su unidad. -/
theorem glueP_pid {i j l k : Int} (hk : k = i ∨ k = j ∨ k = l)
    (ha : ∀ b, b < n → Agr φ i j l (fun z => lo z = b) (src b) a0) :
    pidOfAssign φ (glueP n lo src a0) k = pidOfAssign φ a0 k := by
  refine pid_of_agree (fun k' z hw hz => ?_)
  have iw : InW φ i j l z := ⟨k, k', hk, hw, hz⟩
  unfold glueP
  by_cases h1 : lo z < n
  · rw [if_pos h1]; exact ha _ h1 z rfl iw
  · rw [if_neg h1]

end GlueP

namespace GPathB

variable {P0 P : Assign → Prop} {σ : Int}

/-- **Cerrar un triángulo con una fuente por unidad.** -/
theorem glueP_tri {n : Nat} {lo hi : Nat → Nat} (hl : LocPair φ P0 P σ) (D : PathN φ n lo hi) {v : Nat}
    (hv : stepVar φ σ = some v) (hvin : ∃ j, j < n ∧ InU lo hi j v) {x u w : PathNodeId} {a0 : Assign}
    {src : Nat → Assign} (h0 : P0 a0) (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) (hs : ∀ j, j < n → P0 (src j)) (hJ : JoinP lo hi src)
    (hP : ∀ j, j < n → InU lo hi j v → P (src j))
    (ha : ∀ b, b < n → Agr φ x.id.step u.id.step w.id.step (fun z => lo z = b) (src b) a0) : TriOf φ P x u w :=
  ⟨glueP n lo src a0, glueP_P hl D hv hvin h0 hs hJ hP, (glueP_pid (Or.inl rfl) ha).trans hx0,
    (glueP_pid (Or.inr (Or.inl rfl)) ha).trans hu0, (glueP_pid (Or.inr (Or.inr rfl)) ha).trans hw0⟩

end GPathB

/-! ## Validación: toda `ChainN` es un camino de unidades -/

section OfChain

variable {n : Nat} {zone : Nat → Nat}

/-- La primera unidad: el bloque de dentro, o el de la izquierda de un separador. -/
def loZ (n : Nat) (zone : Nat → Nat) (z : Nat) : Nat :=
  if zone z < n then zone z else if n + 1 ≤ zone z ∧ zone z < 2 * n then zone z - n - 1 else n

/-- La última: el bloque de dentro, o el de la derecha de un separador. -/
def hiZ (n : Nat) (zone : Nat → Nat) (z : Nat) : Nat :=
  if zone z < n then zone z else if n + 1 ≤ zone z ∧ zone z < 2 * n then zone z - n else n

theorem loZ_hiZ_cases (n : Nat) (zone : Nat → Nat) (z : Nat) :
    (zone z < n ∧ loZ n zone z = zone z ∧ hiZ n zone z = zone z) ∨
    (n + 1 ≤ zone z ∧ zone z < 2 * n ∧ loZ n zone z = zone z - n - 1 ∧ hiZ n zone z = zone z - n) ∨
    (¬ zone z < n ∧ ¬ (n + 1 ≤ zone z ∧ zone z < 2 * n) ∧ loZ n zone z = n ∧ hiZ n zone z = n) := by
  unfold loZ hiZ
  by_cases h1 : zone z < n
  · exact Or.inl ⟨h1, if_pos h1, if_pos h1⟩
  rw [if_neg h1, if_neg h1]
  by_cases h2 : n + 1 ≤ zone z ∧ zone z < 2 * n
  · exact Or.inr (Or.inl ⟨h2.1, h2.2, if_pos h2, if_pos h2⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, if_neg h2, if_neg h2⟩)

/-- En una `ChainN`, vivir en la unidad `j` es estar en el bloque `j`. -/
theorem inU_of_blkN {j z : Nat} (hj : j < n) (h : BlkN n zone j z) : InU (loZ n zone) (hiZ n zone) j z := by
  unfold InU
  rcases loZ_hiZ_cases n zone z with ⟨_, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨a, b, _, _⟩ <;>
    rcases h with h | ⟨h1, h⟩ | ⟨h1, h⟩ <;> omega

theorem outU_of_outN {z : Nat} (h : OutN n zone z) : OutU n (loZ n zone) z := by
  unfold OutU; unfold OutN at h
  rcases loZ_hiZ_cases n zone z with ⟨_, e1, _⟩ | ⟨_, _, e1, _⟩ | ⟨_, _, e1, _⟩ <;> omega

/-- **Toda `ChainN` es un camino de unidades.** -/
theorem pathN_of_chainN (D : ChainN φ n zone) : PathN φ n (loZ n zone) (hiZ n zone) := by
  have two := D.two
  refine ⟨by omega, fun z h => ?_, fun c hc => ?_⟩
  · rcases loZ_hiZ_cases n zone z with ⟨_, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, _⟩ <;> omega
  · rcases D.cl c hc with ⟨o1, o2, o3⟩ | ⟨j, hj, i1, i2, i3⟩
    · exact Or.inl ⟨outU_of_outN o1, outU_of_outN o2, outU_of_outN o3⟩
    · exact Or.inr ⟨j, hj, inU_of_blkN hj i1, inU_of_blkN hj i2, inU_of_blkN hj i3⟩

end OfChain

end AbsSatBingo.Model
