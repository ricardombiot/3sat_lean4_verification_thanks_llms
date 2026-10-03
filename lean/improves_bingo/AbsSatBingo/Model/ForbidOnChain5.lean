-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain5.lean
import AbsSatBingo.Model.ForbidOnSepRead

/-!
# Cinco bloques: la variable fijada en un separador (T2 del lector por separadores)

Bloques `B0 = Z0 ∪ {s1}`, `B1 = {s1} ∪ Z1 ∪ {s2}`, `B2 = {s2} ∪ Z2 ∪ {s3}`, `B3 = {s3} ∪ Z3 ∪ {s4}`, `B4 = {s4} ∪ Z4`,
con `Zk = {z | zone z = k}` (`Chain5Data`): los separadores tienen zona `5`; `Z0`, `Z4` sin tres variables distintas y
`Z1`, `Z2`, `Z3` con a lo sumo una. Las ventanas `W1`, `W2`, `W3` de las cláusulas de los bloques de en medio leen sus
dos separadores. Sin hipótesis sobre la numeración.

Por descenso, con la rama de cinco fuentes `glue5` (una por bloque, `a0` donde no está `v`):

* **`v = s4`** (`phantomFree_chain5_s4`): rango por el primer separador leído de `s3, s2, s1`: testigo de `σ`; del paso
  de `s3`; de la ventana `W2`; de la ventana `W1`.
* **`v = s3`** (`phantomFree_chain5_s3`): los dos lados se pegan en `v`, que todas las ramas de `P` leen igual. Rango
  primero por la derecha (`s4` leído o no) y después por la izquierda (`s2`, `s1`, nada). La derecha sale de la ventana
  `W3`; la izquierda, de `W2` o `W1`; si se lee `s4`, de las dos caras por el nodo que lo lee.

`v = s1` y `v = s2` son los mismos casos leyendo la cadena al revés (otros datos).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- **`Chain5Data`**: cinco bloques en cadena, descritos por la zona de cada variable. -/
structure Chain5Data (φ : Cnf) (s1 s2 s3 s4 : Nat) (zone : Nat → Nat) : Prop where
  s1v : s1 < φ.nVars
  s2v : s2 < φ.nVars
  s3v : s3 < φ.nVars
  s4v : s4 < φ.nVars
  z1 : zone s1 = 5
  z2 : zone s2 = 5
  z3 : zone s3 = 5
  z4 : zone s4 = 5
  n12 : s1 ≠ s2
  n13 : s1 ≠ s3
  n14 : s1 ≠ s4
  n23 : s2 ≠ s3
  n24 : s2 ≠ s4
  n34 : s3 ≠ s4
  card0 : No3 (fun z => zone z = 0)
  card4 : No3 (fun z => zone z = 4)
  card1 : Le1 (fun z => zone z = 1)
  card2 : Le1 (fun z => zone z = 2)
  card3 : Le1 (fun z => zone z = 3)
  cl : ∀ c ∈ φ.clauses,
    ClIn (fun z => 5 ≤ zone z ∧ z ≠ s1 ∧ z ≠ s2 ∧ z ≠ s3 ∧ z ≠ s4) c ∨ ClIn (fun z => zone z = 0 ∨ z = s1) c ∨
    ClIn (fun z => z = s1 ∨ zone z = 1 ∨ z = s2) c ∨ ClIn (fun z => z = s2 ∨ zone z = 2 ∨ z = s3) c ∨
    ClIn (fun z => z = s3 ∨ zone z = 3 ∨ z = s4) c ∨ ClIn (fun z => z = s4 ∨ zone z = 4) c

/-- **Una fuente por bloque**: `d0` en `Z0 ∪ {s1}`, `d1` en `Z1 ∪ {s2}`, `d2` en `Z2 ∪ {s3}`, `d3` en `Z3 ∪ {s4}`,
`d4` en `Z4`, `a0` en lo demás. -/
noncomputable def glue5 (s1 s2 s3 s4 : Nat) (zone : Nat → Nat) (d0 d1 d2 d3 d4 a0 : Assign) : Assign := fun z =>
  if zone z = 0 ∨ z = s1 then d0 z
  else if zone z = 1 ∨ z = s2 then d1 z
  else if zone z = 2 ∨ z = s3 then d2 z
  else if zone z = 3 ∨ z = s4 then d3 z
  else if zone z = 4 then d4 z
  else a0 z

section Glue5

variable {s1 s2 s3 s4 : Nat} {zone : Nat → Nat} {d0 d1 d2 d3 d4 a0 : Assign}

theorem g5_0 {z : Nat} (h : zone z = 0 ∨ z = s1) : glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0 z = d0 z := by
  unfold glue5; rw [if_pos h]

theorem g5_1 (D : Chain5Data φ s1 s2 s3 s4 zone) {z : Nat} (h : zone z = 1 ∨ z = s2) :
    glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0 z = d1 z := by
  have n0 : ¬ (zone z = 0 ∨ z = s1) := by
    rcases h with h | h
    · rintro (h' | h')
      · omega
      · rw [h'] at h; rw [D.z1] at h; omega
    · rintro (h' | h')
      · rw [h, D.z2] at h'; omega
      · exact D.n12 (h'.symm.trans h)
  unfold glue5; rw [if_neg n0, if_pos h]

theorem g5_2 (D : Chain5Data φ s1 s2 s3 s4 zone) {z : Nat} (h : zone z = 2 ∨ z = s3) :
    glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0 z = d2 z := by
  have n0 : ¬ (zone z = 0 ∨ z = s1) := by
    rcases h with h | h
    · rintro (h' | h')
      · omega
      · rw [h'] at h; rw [D.z1] at h; omega
    · rintro (h' | h')
      · rw [h, D.z3] at h'; omega
      · exact D.n13 (h'.symm.trans h)
  have n1 : ¬ (zone z = 1 ∨ z = s2) := by
    rcases h with h | h
    · rintro (h' | h')
      · omega
      · rw [h'] at h; rw [D.z2] at h; omega
    · rintro (h' | h')
      · rw [h, D.z3] at h'; omega
      · exact D.n23 (h'.symm.trans h)
  unfold glue5; rw [if_neg n0, if_neg n1, if_pos h]

theorem g5_3 (D : Chain5Data φ s1 s2 s3 s4 zone) {z : Nat} (h : zone z = 3 ∨ z = s4) :
    glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0 z = d3 z := by
  have n0 : ¬ (zone z = 0 ∨ z = s1) := by
    rcases h with h | h
    · rintro (h' | h')
      · omega
      · rw [h'] at h; rw [D.z1] at h; omega
    · rintro (h' | h')
      · rw [h, D.z4] at h'; omega
      · exact D.n14 (h'.symm.trans h)
  have n1 : ¬ (zone z = 1 ∨ z = s2) := by
    rcases h with h | h
    · rintro (h' | h')
      · omega
      · rw [h'] at h; rw [D.z2] at h; omega
    · rintro (h' | h')
      · rw [h, D.z4] at h'; omega
      · exact D.n24 (h'.symm.trans h)
  have n2 : ¬ (zone z = 2 ∨ z = s3) := by
    rcases h with h | h
    · rintro (h' | h')
      · omega
      · rw [h'] at h; rw [D.z3] at h; omega
    · rintro (h' | h')
      · rw [h, D.z4] at h'; omega
      · exact D.n34 (h'.symm.trans h)
  unfold glue5; rw [if_neg n0, if_neg n1, if_neg n2, if_pos h]

theorem g5_4 (D : Chain5Data φ s1 s2 s3 s4 zone) {z : Nat} (h : zone z = 4) :
    glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0 z = d4 z := by
  have n0 : ¬ (zone z = 0 ∨ z = s1) := by
    rintro (h' | h')
    · omega
    · rw [h'] at h; rw [D.z1] at h; omega
  have n1 : ¬ (zone z = 1 ∨ z = s2) := by
    rintro (h' | h')
    · omega
    · rw [h'] at h; rw [D.z2] at h; omega
  have n2 : ¬ (zone z = 2 ∨ z = s3) := by
    rintro (h' | h')
    · omega
    · rw [h'] at h; rw [D.z3] at h; omega
  have n3 : ¬ (zone z = 3 ∨ z = s4) := by
    rintro (h' | h')
    · omega
    · rw [h'] at h; rw [D.z4] at h; omega
  unfold glue5; rw [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_pos h]

theorem g5_O {z : Nat} (h : 5 ≤ zone z ∧ z ≠ s1 ∧ z ≠ s2 ∧ z ≠ s3 ∧ z ≠ s4) :
    glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0 z = a0 z := by
  obtain ⟨h5, h1, h2, h3, h4⟩ := h
  unfold glue5
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

-- por bloques, con las fuentes vecinas leyendo igual el separador
theorem g5B1 (D : Chain5Data φ s1 s2 s3 s4 zone) (e1 : d0 s1 = d1 s1) {z : Nat} (h : z = s1 ∨ zone z = 1 ∨ z = s2) :
    glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0 z = d1 z := by
  rcases h with rfl | h | h
  · rw [g5_0 (Or.inr rfl)]; exact e1
  · exact g5_1 D (Or.inl h)
  · exact g5_1 D (Or.inr h)

theorem g5B2 (D : Chain5Data φ s1 s2 s3 s4 zone) (e2 : d1 s2 = d2 s2) {z : Nat} (h : z = s2 ∨ zone z = 2 ∨ z = s3) :
    glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0 z = d2 z := by
  rcases h with rfl | h | h
  · rw [g5_1 D (Or.inr rfl)]; exact e2
  · exact g5_2 D (Or.inl h)
  · exact g5_2 D (Or.inr h)

theorem g5B3 (D : Chain5Data φ s1 s2 s3 s4 zone) (e3 : d2 s3 = d3 s3) {z : Nat} (h : z = s3 ∨ zone z = 3 ∨ z = s4) :
    glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0 z = d3 z := by
  rcases h with rfl | h | h
  · rw [g5_2 D (Or.inr rfl)]; exact e3
  · exact g5_3 D (Or.inl h)
  · exact g5_3 D (Or.inr h)

theorem g5B4 (D : Chain5Data φ s1 s2 s3 s4 zone) (e4 : d3 s4 = d4 s4) {z : Nat} (h : z = s4 ∨ zone z = 4) :
    glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0 z = d4 z := by
  rcases h with rfl | h
  · rw [g5_3 D (Or.inr rfl)]; exact e4
  · exact g5_4 D h

variable {P0 P : Assign → Prop} {σ : Int}

/-- **La rama de cinco fuentes es de `P0`** si las fuentes vecinas leen igual el separador que comparten. -/
theorem glue5_P0 (hl : LocPair φ P0 P σ) (D : Chain5Data φ s1 s2 s3 s4 zone) (h0 : P0 a0) (q0 : P0 d0) (q1 : P0 d1)
    (q2 : P0 d2) (q3 : P0 d3) (q4 : P0 d4) (e1 : d0 s1 = d1 s1) (e2 : d1 s2 = d2 s2) (e3 : d2 s3 = d3 s3)
    (e4 : d3 s4 = d4 s4) : P0 (glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0) := by
  refine p0_of_sources hl ⟨a0, h0⟩ (fun z => ?_) (fun c hc => ?_)
  · by_cases h : zone z = 0 ∨ z = s1
    · exact ⟨d0, q0, g5_0 h⟩
    by_cases h' : zone z = 1 ∨ z = s2
    · exact ⟨d1, q1, g5_1 D h'⟩
    by_cases h'' : zone z = 2 ∨ z = s3
    · exact ⟨d2, q2, g5_2 D h''⟩
    by_cases h3 : zone z = 3 ∨ z = s4
    · exact ⟨d3, q3, g5_3 D h3⟩
    by_cases h4 : zone z = 4
    · exact ⟨d4, q4, g5_4 D h4⟩
    exact ⟨a0, h0, g5_O ⟨by omega, by omega, by omega, by omega, by omega⟩⟩
  · rcases D.cl c hc with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩
    · exact ⟨a0, h0, g5_O o1, g5_O o2, g5_O o3⟩
    · exact ⟨d0, q0, g5_0 i1, g5_0 i2, g5_0 i3⟩
    · exact ⟨d1, q1, g5B1 D e1 i1, g5B1 D e1 i2, g5B1 D e1 i3⟩
    · exact ⟨d2, q2, g5B2 D e2 i1, g5B2 D e2 i2, g5B2 D e2 i3⟩
    · exact ⟨d3, q3, g5B3 D e3 i1, g5B3 D e3 i2, g5B3 D e3 i3⟩
    · exact ⟨d4, q4, g5B4 D e4 i1, g5B4 D e4 i2, g5B4 D e4 i3⟩

/-- **Y de `P`**, con `v = s4` (fuentes `d3`, `d4` de `P`) o `v = s3` (fuentes `d2`, `d3` de `P`). -/
theorem glue5_P (hl : LocPair φ P0 P σ) (D : Chain5Data φ s1 s2 s3 s4 zone) {v : Nat} (hv : stepVar φ σ = some v)
    (h0 : P0 a0) (q0 : P0 d0) (q1 : P0 d1) (q2 : P0 d2) (q3 : P0 d3) (q4 : P0 d4) (e1 : d0 s1 = d1 s1)
    (e2 : d1 s2 = d2 s2) (e3 : d2 s3 = d3 s3) (e4 : d3 s4 = d4 s4)
    (hpos : (v = s4 ∧ P d3 ∧ P d4) ∨ (v = s3 ∧ P d2 ∧ P d3)) : P (glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0) := by
  refine p_of_sources hl (glue5_P0 hl D h0 q0 q1 q2 q3 q4 e1 e2 e3 e4) (fun h => by rw [hv] at h; cases h)
    (fun z hz => ?_)
  rw [hv] at hz; cases hz
  have tv : ∀ {Q : Nat → Prop} {cl : Clause}, ClVar cl v → ClIn Q cl → Q v := by
    intro Q cl hcv hin
    obtain ⟨a, b, c⟩ := hin
    rcases hcv with e | e | e
    · rw [e]; exact a
    · rw [e]; exact b
    · rw [e]; exact c
  rcases hpos with ⟨rfl, p3, p4⟩ | ⟨rfl, p2, p3⟩
  · refine ⟨⟨d3, p3, g5_3 D (Or.inr rfl)⟩, fun cl hcl hcv => ?_⟩
    rcases D.cl cl hcl with hi | hi | hi | hi | hi | hi
    · exact absurd rfl (tv hcv hi).2.2.2.2
    · rcases tv hcv hi with h | h
      · rw [D.z4] at h; omega
      · exact absurd h.symm D.n14
    · rcases tv hcv hi with h | h | h
      · exact absurd h.symm D.n14
      · rw [D.z4] at h; omega
      · exact absurd h.symm D.n24
    · rcases tv hcv hi with h | h | h
      · exact absurd h.symm D.n24
      · rw [D.z4] at h; omega
      · exact absurd h.symm D.n34
    · obtain ⟨i1, i2, i3⟩ := hi
      exact ⟨d3, p3, g5B3 D e3 i1, g5B3 D e3 i2, g5B3 D e3 i3⟩
    · obtain ⟨i1, i2, i3⟩ := hi
      exact ⟨d4, p4, g5B4 D e4 i1, g5B4 D e4 i2, g5B4 D e4 i3⟩
  · refine ⟨⟨d2, p2, g5_2 D (Or.inr rfl)⟩, fun cl hcl hcv => ?_⟩
    rcases D.cl cl hcl with hi | hi | hi | hi | hi | hi
    · exact absurd rfl (tv hcv hi).2.2.2.1
    · rcases tv hcv hi with h | h
      · rw [D.z3] at h; omega
      · exact absurd h.symm D.n13
    · rcases tv hcv hi with h | h | h
      · exact absurd h.symm D.n13
      · rw [D.z3] at h; omega
      · exact absurd h.symm D.n23
    · obtain ⟨i1, i2, i3⟩ := hi
      exact ⟨d2, p2, g5B2 D e2 i1, g5B2 D e2 i2, g5B2 D e2 i3⟩
    · obtain ⟨i1, i2, i3⟩ := hi
      exact ⟨d3, p3, g5B3 D e3 i1, g5B3 D e3 i2, g5B3 D e3 i3⟩
    · rcases tv hcv hi with h | h
      · exact absurd h D.n34
      · rw [D.z3] at h; omega

/-- La rama de cinco fuentes pasa por las ventanas de `a0` si cada fuente coincide con `a0` en su parte. -/
theorem glue5_pid {i j l k : Int} (hk : k = i ∨ k = j ∨ k = l)
    (a0' : Agr φ i j l (fun z => zone z = 0 ∨ z = s1) d0 a0) (a1 : Agr φ i j l (fun z => zone z = 1 ∨ z = s2) d1 a0)
    (a2 : Agr φ i j l (fun z => zone z = 2 ∨ z = s3) d2 a0) (a3 : Agr φ i j l (fun z => zone z = 3 ∨ z = s4) d3 a0)
    (a4 : Agr φ i j l (fun z => zone z = 4) d4 a0) :
    pidOfAssign φ (glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0) k = pidOfAssign φ a0 k := by
  refine pid_of_agree (fun k' z hw hz => ?_)
  have iw : InW φ i j l z := ⟨k, k', hk, hw, hz⟩
  unfold glue5
  by_cases h : zone z = 0 ∨ z = s1
  · rw [if_pos h]; exact a0' z h iw
  rw [if_neg h]
  by_cases h' : zone z = 1 ∨ z = s2
  · rw [if_pos h']; exact a1 z h' iw
  rw [if_neg h']
  by_cases h'' : zone z = 2 ∨ z = s3
  · rw [if_pos h'']; exact a2 z h'' iw
  rw [if_neg h'']
  by_cases h3 : zone z = 3 ∨ z = s4
  · rw [if_pos h3]; exact a3 z h3 iw
  rw [if_neg h3]
  by_cases h4 : zone z = 4
  · rw [if_pos h4]; exact a4 z h4 iw
  rw [if_neg h4]

end Glue5

namespace GPathB

variable {P0 P : Assign → Prop} {Nn σ : Int} {R : PathNodeId → PathNodeId → Prop} {Tf : Trios}

section Tools5

variable {s1 s2 s3 s4 : Nat} {zone : Nat → Nat}

/-- **Cerrar un triángulo con cinco fuentes.** -/
theorem glue5_tri (hl : LocPair φ P0 P σ) (D : Chain5Data φ s1 s2 s3 s4 zone) {v : Nat}
    (hv : stepVar φ σ = some v) {x u w : PathNodeId} {a0 d0 d1 d2 d3 d4 : Assign} (h0 : P0 a0)
    (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) (q0 : P0 d0) (q1 : P0 d1) (q2 : P0 d2) (q3 : P0 d3) (q4 : P0 d4)
    (e1 : d0 s1 = d1 s1) (e2 : d1 s2 = d2 s2) (e3 : d2 s3 = d3 s3) (e4 : d3 s4 = d4 s4)
    (hpos : (v = s4 ∧ P d3 ∧ P d4) ∨ (v = s3 ∧ P d2 ∧ P d3))
    (a0' : Agr φ x.id.step u.id.step w.id.step (fun z => zone z = 0 ∨ z = s1) d0 a0)
    (a1 : Agr φ x.id.step u.id.step w.id.step (fun z => zone z = 1 ∨ z = s2) d1 a0)
    (a2 : Agr φ x.id.step u.id.step w.id.step (fun z => zone z = 2 ∨ z = s3) d2 a0)
    (a3 : Agr φ x.id.step u.id.step w.id.step (fun z => zone z = 3 ∨ z = s4) d3 a0)
    (a4 : Agr φ x.id.step u.id.step w.id.step (fun z => zone z = 4) d4 a0) : TriOf φ P x u w :=
  ⟨glue5 s1 s2 s3 s4 zone d0 d1 d2 d3 d4 a0, glue5_P hl D hv h0 q0 q1 q2 q3 q4 e1 e2 e3 e4 hpos,
    (glue5_pid (Or.inl rfl) a0' a1 a2 a3 a4).trans hx0, (glue5_pid (Or.inr (Or.inl rfl)) a0' a1 a2 a3 a4).trans hu0,
    (glue5_pid (Or.inr (Or.inr rfl)) a0' a1 a2 a3 a4).trans hw0⟩

end Tools5

/-- **Las caras del testigo del paso `lam`, con el primer nodo leyendo `s'`**, para un paso cuya ventana lee `s`: las
dos caras por el primer nodo son de `P`, la tercera de `P0`, y las tres pasan por el mismo nodo de `lam`. -/
theorem faces_Pwx (hl : LocPair φ P0 P σ) (hS : PhStruct φ P0 Nn R Tf) {x u w : PathNodeId} (t : Tri R Tf x u w)
    {a0 : Assign} (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) {lam : Int} (h0 : 0 ≤ lam) (hN : lam < Nn) {s s' : Nat}
    (hs : ReadsAt φ lam s) (hno : ¬ InW φ x.id.step u.id.step w.id.step s) (hx : ReadsAt φ x.id.step s')
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s' →
      InW φ x'.id.step u'.id.step w'.id.step s → TriOf φ P x' u' w') :
    ∃ c1 c2 c3, Faces φ (fun c => P0 c ∧ pidOfAssign φ c lam = pidOfAssign φ c1 lam) a0 c1 c2 c3
      x.id.step u.id.step w.id.step ∧ P c1 ∧ P c2 := by
  obtain ⟨n, hns, hn⟩ := t.wit hS h0 hN
  rcases hn with hn | ⟨t1, t2, t3⟩
  · exfalso
    apply hno
    rcases hn with e | e | e
    · exact inW_of_reads (Or.inl rfl) (by rw [← e, hns]; exact hs)
    · exact inW_of_reads (Or.inr (Or.inl rfl)) (by rw [← e, hns]; exact hs)
    · exact inW_of_reads (Or.inr (Or.inr rfl)) (by rw [← e, hns]; exact hs)
  have fr : ∀ {y z : PathNodeId}, InW φ y.id.step z.id.step n.id.step s :=
    inW_of_reads (Or.inr (Or.inr rfl)) (by rw [hns]; exact hs)
  obtain ⟨c1, q1, c1x, c1u, c1n⟩ := hP x u n t1 (inW_of_reads (Or.inl rfl) hx) fr
  obtain ⟨c2, q2, c2x, c2w, c2n⟩ := hP x w n t2 (inW_of_reads (Or.inl rfl) hx) fr
  obtain ⟨c3, q3, c3u, c3w, c3n⟩ := t3.b3 hS
  rw [hns] at c1n c2n c3n
  exact ⟨c1, c2, c3, ⟨⟨hl.sub _ q1, rfl⟩, ⟨hl.sub _ q2, c2n.trans c1n.symm⟩, ⟨q3, c3n.trans c1n.symm⟩,
    c1x.trans hx0.symm, c2x.trans hx0.symm, c1u.trans hu0.symm, c3u.trans hu0.symm, c2w.trans hw0.symm,
    c3w.trans hw0.symm⟩, q1, q2⟩

-- ============================================================
-- `v = s4`
-- ============================================================

section CaseS4

variable {s1 s2 s3 s4 : Nat} {zone : Nat → Nat}

/-- **Cinco bloques, `v = s4`**, con las ventanas `W1` (lee `s1`, `s2`) y `W2` (lee `s2`, `s3`). -/
theorem phantomFree_chain5_s4 (hl : LocPair φ P0 P σ) (D : Chain5Data φ s1 s2 s3 s4 zone)
    (hv : stepVar φ σ = some s4) {k1 k2 : Int} (hk1 : 0 ≤ k1 ∧ k1 < Nn ∧ ReadsAt φ k1 s1 ∧ ReadsAt φ k1 s2)
    (hk2 : 0 ≤ k2 ∧ k2 < Nn ∧ ReadsAt φ k2 s2 ∧ ReadsAt φ k2 s3) (hσ0 : 0 ≤ σ) (hσN : σ < Nn)
    (hN : midFusion φ < Nn) : PhantomFree φ P0 P Nn σ := by
  have rng : ∀ {s : Nat}, s < φ.nVars → 0 ≤ varStep s ∧ varStep s < Nn := by
    intro s hs
    have h1 : 0 ≤ varStep s := by simp only [varStep]; omega
    have h2 : varStep s < midFusion φ := by simp only [varStep, midFusion]; omega
    exact ⟨h1, by omega⟩
  refine phantomFree_of_descent hσ0 hσN
    (fun x u w => rkF (InW φ x.id.step u.id.step w.id.step s3) (InW φ x.id.step u.id.step w.id.step s2)
      (InW φ x.id.step u.id.step w.id.step s1))
    (fun R Tf hS hanch x u w t ih => ?_)
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  by_cases h3 : InW φ x.id.step u.id.step w.id.step s3
  · -- el testigo de `σ`
    rcases faces_sigma hS hanch hσ0 hσN t hP0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
    · exact h
    obtain ⟨d4, q4, ag4⟩ := F.pick D.card4
    obtain ⟨d3, q3, ag3⟩ := F.pick (no3_or D.card3 (le1_eq s3))
    exact glue5_tri hl D hv hP0 hx0 hu0 hw0 hP0 hP0 hP0 (hl.sub _ q3) (hl.sub _ q4) rfl rfl
      (ag3 s3 (Or.inr rfl) h3).symm (hl.sameVar hv q3 q4) (Or.inl ⟨rfl, q3, q4⟩) agr_refl' agr_refl' agr_refl'
      (agr_or (agr_mono ag3 (fun z h => Or.inl h)) (vfix4 hl hv F F.q1 F.q2 q3)) ag4
  by_cases h2 : InW φ x.id.step u.id.step w.id.step s2
  · -- el testigo del paso de `s3`
    obtain ⟨l0, lN⟩ := rng D.s3v
    obtain ⟨c1, c2, c3, F⟩ := faces_P hS t hx0 hu0 hw0 l0 lN (stepVar_var D.s3v) h3
      (fun x' u' w' t' h' => ih x' u' w' t' (by rw [rkF_p h', rkF_1 h3 h2]; omega))
    obtain ⟨d4, ⟨q4, _⟩, ag4⟩ := F.pick D.card4
    obtain ⟨d3, ⟨q3, s3e⟩, ag3⟩ := F.pick (no3_of_le1 D.card3)
    obtain ⟨d2, ⟨q2, s2e⟩, ag2⟩ := F.pick (no3_or D.card2 (le1_eq s2))
    exact glue5_tri hl D hv hP0 hx0 hu0 hw0 hP0 hP0 (hl.sub _ q2) (hl.sub _ q3) (hl.sub _ q4) rfl
      (ag2 s2 (Or.inr rfl) h2).symm (s2e.trans s3e.symm) (hl.sameVar hv q3 q4) (Or.inl ⟨rfl, q3, q4⟩) agr_refl'
      agr_refl' (agr_or (agr_mono ag2 (fun z h => Or.inl h)) (fun iw => absurd iw h3))
      (agr_or ag3 (vfix4 hl hv F F.q1.1 F.q2.1 q3)) ag4
  by_cases h1 : InW φ x.id.step u.id.step w.id.step s1
  · -- el testigo de la ventana `W2`
    obtain ⟨k0, kN, kr2, kr3⟩ := hk2
    obtain ⟨c1, c2, c3, F⟩ := faces_Pw hS t hx0 hu0 hw0 k0 kN kr2 h2
      (fun x' u' w' t' h' => ih x' u' w' t' (rkF_q_lt h' h3 h2))
    obtain ⟨d1, ⟨q1, p1⟩, ag1⟩ := F.pick (no3_or D.card1 (le1_eq s1))
    obtain ⟨d2, ⟨q2, p2⟩, ag2⟩ := F.pick (no3_of_le1 D.card2)
    obtain ⟨d3, ⟨q3, p3⟩, ag3⟩ := F.pick (no3_of_le1 D.card3)
    obtain ⟨d4, ⟨q4, _⟩, ag4⟩ := F.pick D.card4
    exact glue5_tri hl D hv hP0 hx0 hu0 hw0 hP0 (hl.sub _ q1) (hl.sub _ q2) (hl.sub _ q3) (hl.sub _ q4)
      (ag1 s1 (Or.inr rfl) h1).symm (agree_at p1 p2 kr2) (agree_at p2 p3 kr3) (hl.sameVar hv q3 q4)
      (Or.inl ⟨rfl, q3, q4⟩) agr_refl' (agr_or (agr_mono ag1 (fun z h => Or.inl h)) (fun iw => absurd iw h2))
      (agr_or ag2 (fun iw => absurd iw h3)) (agr_or ag3 (vfix4 hl hv F F.q1.1 F.q2.1 q3)) ag4
  · -- nada: el testigo de la ventana `W1`
    obtain ⟨k0, kN, kr1, kr2⟩ := hk1
    obtain ⟨c1, c2, c3, F⟩ := faces_Pw hS t hx0 hu0 hw0 k0 kN kr2 h2
      (fun x' u' w' t' h' => ih x' u' w' t' (rkF_q_lt h' h3 h2))
    obtain ⟨d0, ⟨q0, p0⟩, ag0⟩ := F.pick D.card0
    obtain ⟨d1, ⟨q1, p1⟩, ag1⟩ := F.pick (no3_of_le1 D.card1)
    obtain ⟨d2, ⟨q2, p2⟩, ag2⟩ := F.pick (no3_or D.card2 D.card3)
    obtain ⟨d4, ⟨q4, _⟩, ag4⟩ := F.pick D.card4
    exact glue5_tri hl D hv hP0 hx0 hu0 hw0 (hl.sub _ q0) (hl.sub _ q1) (hl.sub _ q2) (hl.sub _ q2) (hl.sub _ q4)
      (agree_at p0 p1 kr1) (agree_at p1 p2 kr2) rfl (hl.sameVar hv q2 q4) (Or.inl ⟨rfl, q2, q4⟩)
      (agr_or ag0 (fun iw => absurd iw h1)) (agr_or ag1 (fun iw => absurd iw h2))
      (agr_or (agr_mono ag2 (fun z h => Or.inl h)) (fun iw => absurd iw h3))
      (agr_or (agr_mono ag2 (fun z h => Or.inr h)) (vfix4 hl hv F F.q1.1 F.q2.1 q2)) ag4

end CaseS4

-- ============================================================
-- `v = s3`
-- ============================================================

open Classical in
/-- El rango con `v = s3`: primero la derecha (`0` si se lee `s4`, `3` si no), después la izquierda (`0` si se lee
`s2`, `1` si `s1`, `2` si nada). -/
noncomputable def rkS3 (p4 p2 p1 : Prop) : Nat := (if p4 then 0 else 3) + (if p2 then 0 else if p1 then 1 else 2)

theorem rkS3_4 {p4 p2 p1 : Prop} (h : p4) : rkS3 p4 p2 p1 ≤ 2 := by
  unfold rkS3; rw [if_pos h]
  by_cases h2 : p2
  · rw [if_pos h2]; omega
  · rw [if_neg h2]; by_cases h1 : p1 <;> simp [h1]
theorem rkS3_2 {p4 p2 p1 : Prop} (h : p2) : rkS3 p4 p2 p1 ≤ 3 := by
  unfold rkS3; rw [if_pos h]; by_cases h4 : p4 <;> simp [h4]
theorem rkS3_42 {p4 p2 p1 : Prop} (h4 : p4) (h2 : p2) : rkS3 p4 p2 p1 = 0 := by simp [rkS3, h4, h2]
open Classical in
theorem rkS3_val {p4 p2 p1 : Prop} : rkS3 p4 p2 p1 =
    (if p4 then 0 else 3) + (if p2 then 0 else if p1 then 1 else 2) := rfl

section CaseS3

variable {s1 s2 s3 s4 : Nat} {zone : Nat → Nat}

/-- Se lee `s4` (por el primer nodo) y no `s2`: una ventana de la izquierda, con las dos caras por el primer nodo. -/
theorem c5s3_four (hl : LocPair φ P0 P σ) (D : Chain5Data φ s1 s2 s3 s4 zone) (hv : stepVar φ σ = some s3)
    (hS : PhStruct φ P0 Nn R Tf) {k1 k2 : Int} (hk1 : 0 ≤ k1 ∧ k1 < Nn ∧ ReadsAt φ k1 s1 ∧ ReadsAt φ k1 s2)
    (hk2 : 0 ≤ k2 ∧ k2 < Nn ∧ ReadsAt φ k2 s2 ∧ ReadsAt φ k2 s3) {x u w : PathNodeId} (t : Tri R Tf x u w)
    (hx : ReadsAt φ x.id.step s4) (hno2 : ¬ InW φ x.id.step u.id.step w.id.step s2)
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s4 →
      InW φ x'.id.step u'.id.step w'.id.step s2 → TriOf φ P x' u' w') : TriOf φ P x u w := by
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  by_cases h1 : InW φ x.id.step u.id.step w.id.step s1
  · -- la ventana `W2`
    obtain ⟨k0, kN, kr2, _⟩ := hk2
    obtain ⟨c1, c2, c3, F, q1, q2⟩ := faces_Pwx hl hS t hx0 hu0 hw0 k0 kN kr2 hno2 hx hP
    obtain ⟨d1, ⟨r1, p1⟩, ag1⟩ := F.pick (no3_or D.card1 (le1_eq s1))
    obtain ⟨d2, e2P, ⟨_, p2⟩, ag2, _⟩ := pick12 F q1 q2 D.card2
    obtain ⟨d3, e3P, _, ag3, e3x⟩ := pick12 F q1 q2 D.card3
    exact glue5_tri hl D hv hP0 hx0 hu0 hw0 hP0 r1 (hl.sub _ e2P) (hl.sub _ e3P) hP0 (ag1 s1 (Or.inr rfl) h1).symm
      (agree_at p1 p2 kr2) (hl.sameVar hv e2P e3P) (var_of_reads e3x hx) (Or.inr ⟨rfl, e2P, e3P⟩) agr_refl'
      (agr_or (agr_mono ag1 (fun z h => Or.inl h)) (fun iw => absurd iw hno2))
      (agr_or ag2 (vfix4 hl hv F q1 q2 e2P)) (agr_or ag3 (fun _ => var_of_reads e3x hx)) agr_refl'
  · -- la ventana `W1`
    obtain ⟨k0, kN, kr1, kr2⟩ := hk1
    obtain ⟨c1, c2, c3, F, q1, q2⟩ := faces_Pwx hl hS t hx0 hu0 hw0 k0 kN kr2 hno2 hx hP
    obtain ⟨d0, ⟨r0, p0⟩, ag0⟩ := F.pick D.card0
    obtain ⟨d1, ⟨r1, p1⟩, ag1⟩ := F.pick (no3_of_le1 D.card1)
    obtain ⟨d2, e2P, ⟨_, p2⟩, ag2, _⟩ := pick12 F q1 q2 D.card2
    obtain ⟨d3, e3P, _, ag3, e3x⟩ := pick12 F q1 q2 D.card3
    exact glue5_tri hl D hv hP0 hx0 hu0 hw0 r0 r1 (hl.sub _ e2P) (hl.sub _ e3P) hP0 (agree_at p0 p1 kr1)
      (agree_at p1 p2 kr2) (hl.sameVar hv e2P e3P) (var_of_reads e3x hx) (Or.inr ⟨rfl, e2P, e3P⟩)
      (agr_or ag0 (fun iw => absurd iw h1)) (agr_or ag1 (fun iw => absurd iw hno2))
      (agr_or ag2 (vfix4 hl hv F q1 q2 e2P)) (agr_or ag3 (fun _ => var_of_reads e3x hx)) agr_refl'

/-- **Cinco bloques, `v = s3`**, con las ventanas `W1` (lee `s1`, `s2`), `W2` (lee `s2`, `s3`) y `W3` (lee `s3`, `s4`). -/
theorem phantomFree_chain5_s3 (hl : LocPair φ P0 P σ) (D : Chain5Data φ s1 s2 s3 s4 zone)
    (hv : stepVar φ σ = some s3) {k1 k2 k3 : Int} (hk1 : 0 ≤ k1 ∧ k1 < Nn ∧ ReadsAt φ k1 s1 ∧ ReadsAt φ k1 s2)
    (hk2 : 0 ≤ k2 ∧ k2 < Nn ∧ ReadsAt φ k2 s2 ∧ ReadsAt φ k2 s3)
    (hk3 : 0 ≤ k3 ∧ k3 < Nn ∧ ReadsAt φ k3 s3 ∧ ReadsAt φ k3 s4) (hσ0 : 0 ≤ σ) (hσN : σ < Nn) :
    PhantomFree φ P0 P Nn σ := by
  refine phantomFree_of_descent hσ0 hσN
    (fun x u w => rkS3 (InW φ x.id.step u.id.step w.id.step s4) (InW φ x.id.step u.id.step w.id.step s2)
      (InW φ x.id.step u.id.step w.id.step s1))
    (fun R Tf hS hanch x u w t ih => ?_)
  by_cases h4 : InW φ x.id.step u.id.step w.id.step s4
  · by_cases h2 : InW φ x.id.step u.id.step w.id.step s2
    · -- base: el testigo de `σ`
      obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
      rcases faces_sigma hS hanch hσ0 hσN t hP0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
      · exact h
      obtain ⟨d2, q2, ag2⟩ := F.pick (no3_or D.card2 (le1_eq s2))
      obtain ⟨d3, q3, ag3⟩ := F.pick (no3_or D.card3 (le1_eq s4))
      exact glue5_tri hl D hv hP0 hx0 hu0 hw0 hP0 hP0 (hl.sub _ q2) (hl.sub _ q3) hP0 rfl
        (ag2 s2 (Or.inr rfl) h2).symm (hl.sameVar hv q2 q3) (ag3 s4 (Or.inr rfl) h4) (Or.inr ⟨rfl, q2, q3⟩)
        agr_refl' agr_refl' (agr_or (agr_mono ag2 (fun z h => Or.inl h)) (vfix4 hl hv F F.q1 F.q2 q2)) ag3 agr_refl'
    · -- se lee `s4` y no `s2`: el nodo que lee `s4` al primer sitio
      refine of_reads_first hS (H := fun x u w => ¬ InW φ x.id.step u.id.step w.id.step s2)
        (fun _ _ _ h => not_inW_swap12 h) (fun _ _ _ h => not_inW_swap23 h)
        (fun x' u' w' t' h' hx' => c5s3_four hl D hv hS hk1 hk2 t' hx' h' (fun a b c t'' p q => ih a b c t'' (by
          rw [rkS3_42 p q, rkS3_val, if_pos h4, if_neg h2]; split <;> omega))) x u w t h2 h4
  · obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
    -- la derecha: la ventana `W3`, cuyas caras leen `s4`
    obtain ⟨k30, k3N, kr3, kr4⟩ := hk3
    obtain ⟨g1, g2, g3, G⟩ := faces_Pw hS t hx0 hu0 hw0 k30 k3N kr4 h4
      (fun x' u' w' t' h' => ih x' u' w' t' (by
        have := rkS3_4 (p2 := InW φ x'.id.step u'.id.step w'.id.step s2)
          (p1 := InW φ x'.id.step u'.id.step w'.id.step s1) h'
        rw [rkS3_val (p4 := InW φ x.id.step u.id.step w.id.step s4), if_neg h4]; omega))
    obtain ⟨d3, ⟨q3, p3⟩, ag3⟩ := G.pick (no3_of_le1 D.card3)
    obtain ⟨d4, ⟨q4, p4⟩, ag4⟩ := G.pick D.card4
    by_cases h2 : InW φ x.id.step u.id.step w.id.step s2
    · -- la izquierda, de `a0` y una cara de `W3` que coincide con `a0` en `s2`
      obtain ⟨d2, ⟨q2, _⟩, ag2⟩ := G.pick (no3_or D.card2 (le1_eq s2))
      exact glue5_tri hl D hv hP0 hx0 hu0 hw0 hP0 hP0 (hl.sub _ q2) (hl.sub _ q3) (hl.sub _ q4) rfl
        (ag2 s2 (Or.inr rfl) h2).symm (hl.sameVar hv q2 q3) (agree_at p3 p4 kr4) (Or.inr ⟨rfl, q2, q3⟩) agr_refl'
        agr_refl' (agr_or (agr_mono ag2 (fun z h => Or.inl h)) (vfix4 hl hv G G.q1.1 G.q2.1 q2))
        (agr_or ag3 (fun iw => absurd iw h4)) ag4
    · -- la izquierda: la ventana `W2` (si se lee `s1`) o `W1`; sus caras leen `s2`
      have hPl : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s2 → TriOf φ P x' u' w' :=
        fun x' u' w' t' h' => ih x' u' w' t' (by
          have := rkS3_2 (p4 := InW φ x'.id.step u'.id.step w'.id.step s4)
            (p1 := InW φ x'.id.step u'.id.step w'.id.step s1) h'
          rw [rkS3_val (p4 := InW φ x.id.step u.id.step w.id.step s4), if_neg h4, if_neg h2]; split <;> omega)
      by_cases h1 : InW φ x.id.step u.id.step w.id.step s1
      · obtain ⟨k20, k2N, kr2, kr3'⟩ := hk2
        obtain ⟨c1, c2, c3, F⟩ := faces_Pw hS t hx0 hu0 hw0 k20 k2N kr2 h2 hPl
        obtain ⟨d1, ⟨q1, p1⟩, ag1⟩ := F.pick (no3_or D.card1 (le1_eq s1))
        obtain ⟨d2, ⟨q2, p2⟩, ag2⟩ := F.pick (no3_of_le1 D.card2)
        exact glue5_tri hl D hv hP0 hx0 hu0 hw0 hP0 (hl.sub _ q1) (hl.sub _ q2) (hl.sub _ q3) (hl.sub _ q4)
          (ag1 s1 (Or.inr rfl) h1).symm (agree_at p1 p2 kr2) (hl.sameVar hv q2 q3) (agree_at p3 p4 kr4)
          (Or.inr ⟨rfl, q2, q3⟩) agr_refl' (agr_or (agr_mono ag1 (fun z h => Or.inl h)) (fun iw => absurd iw h2))
          (agr_or ag2 (vfix4 hl hv F F.q1.1 F.q2.1 q2)) (agr_or ag3 (fun iw => absurd iw h4)) ag4
      · obtain ⟨k10, k1N, kr1, kr2⟩ := hk1
        obtain ⟨c1, c2, c3, F⟩ := faces_Pw hS t hx0 hu0 hw0 k10 k1N kr2 h2 hPl
        obtain ⟨d0, ⟨q0, p0⟩, ag0⟩ := F.pick D.card0
        obtain ⟨d1, ⟨q1, p1⟩, ag1⟩ := F.pick (no3_of_le1 D.card1)
        obtain ⟨d2, ⟨q2, p2⟩, ag2⟩ := F.pick (no3_of_le1 D.card2)
        exact glue5_tri hl D hv hP0 hx0 hu0 hw0 (hl.sub _ q0) (hl.sub _ q1) (hl.sub _ q2) (hl.sub _ q3)
          (hl.sub _ q4) (agree_at p0 p1 kr1) (agree_at p1 p2 kr2) (hl.sameVar hv q2 q3) (agree_at p3 p4 kr4)
          (Or.inr ⟨rfl, q2, q3⟩) (agr_or ag0 (fun iw => absurd iw h1)) (agr_or ag1 (fun iw => absurd iw h2))
          (agr_or ag2 (vfix4 hl hv F F.q1.1 F.q2.1 q2)) (agr_or ag3 (fun iw => absurd iw h4)) ag4

end CaseS3

end GPathB

end AbsSatBingo.Model

-- ============================================================
-- `chain5_cross`: T2 del lector por separadores
-- ============================================================

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

/-- **`chain5_cross`** (`scripts/cnf/chain5_cross.cnf`, variables desde 0):
`(x0 ∨ x2 ∨ x5) ∧ (¬x5 ∨ x4 ∨ x6) ∧ (¬x6 ∨ x1 ∨ x7) ∧ (¬x7 ∨ x3 ∨ x8) ∧ (¬x8 ∨ x9 ∨ x10)`. -/
def chain5Cross : Cnf :=
  ⟨11, [⟨⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩⟩, ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩, ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩,
    ⟨⟨7, false⟩, ⟨3, true⟩, ⟨8, true⟩⟩, ⟨⟨8, false⟩, ⟨9, true⟩, ⟨10, true⟩⟩]⟩

theorem bounded_chain5Cross : Bounded chain5Cross := by
  intro c hc
  simp only [chain5Cross, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp [Clause.Bounded, chain5Cross]

/-- Las zonas, en el sentido de la cadena: `{x0, x2}`, `{x4}`, `{x1}`, `{x3}`, `{x9, x10}`; separadores `x5 … x8`. -/
def zone5 (z : Nat) : Nat :=
  if z = 0 ∨ z = 2 then 0 else if z = 4 then 1 else if z = 1 then 2 else if z = 3 then 3
  else if z = 9 ∨ z = 10 then 4 else if 5 ≤ z ∧ z ≤ 8 then 5 else z + 10

/-- Las zonas, leyendo la cadena al revés (separadores `x8, x7, x6, x5`). -/
def zone5r (z : Nat) : Nat :=
  if z = 9 ∨ z = 10 then 0 else if z = 3 then 1 else if z = 1 then 2 else if z = 4 then 3
  else if z = 0 ∨ z = 2 then 4 else if 5 ≤ z ∧ z ≤ 8 then 5 else z + 10

theorem zone5_cases {z k : Nat} (h : zone5 z = k) :
    (k = 0 ∧ (z = 0 ∨ z = 2)) ∨ (k = 1 ∧ z = 4) ∨ (k = 2 ∧ z = 1) ∨ (k = 3 ∧ z = 3) ∨ (k = 4 ∧ (z = 9 ∨ z = 10)) ∨
      (k = 5 ∧ 5 ≤ z ∧ z ≤ 8) ∨ k = z + 10 := by
  unfold zone5 at h
  by_cases h1 : z = 0 ∨ z = 2
  · rw [if_pos h1] at h; omega
  rw [if_neg h1] at h
  by_cases h2 : z = 4
  · rw [if_pos h2] at h; omega
  rw [if_neg h2] at h
  by_cases h3 : z = 1
  · rw [if_pos h3] at h; omega
  rw [if_neg h3] at h
  by_cases h4 : z = 3
  · rw [if_pos h4] at h; omega
  rw [if_neg h4] at h
  by_cases h5 : z = 9 ∨ z = 10
  · rw [if_pos h5] at h; omega
  rw [if_neg h5] at h
  by_cases h6 : 5 ≤ z ∧ z ≤ 8
  · rw [if_pos h6] at h; omega
  rw [if_neg h6] at h; omega

theorem zone5r_cases {z k : Nat} (h : zone5r z = k) :
    (k = 0 ∧ (z = 9 ∨ z = 10)) ∨ (k = 1 ∧ z = 3) ∨ (k = 2 ∧ z = 1) ∨ (k = 3 ∧ z = 4) ∨ (k = 4 ∧ (z = 0 ∨ z = 2)) ∨
      (k = 5 ∧ 5 ≤ z ∧ z ≤ 8) ∨ k = z + 10 := by
  unfold zone5r at h
  by_cases h1 : z = 9 ∨ z = 10
  · rw [if_pos h1] at h; omega
  rw [if_neg h1] at h
  by_cases h2 : z = 3
  · rw [if_pos h2] at h; omega
  rw [if_neg h2] at h
  by_cases h3 : z = 1
  · rw [if_pos h3] at h; omega
  rw [if_neg h3] at h
  by_cases h4 : z = 4
  · rw [if_pos h4] at h; omega
  rw [if_neg h4] at h
  by_cases h5 : z = 0 ∨ z = 2
  · rw [if_pos h5] at h; omega
  rw [if_neg h5] at h
  by_cases h6 : 5 ≤ z ∧ z ≤ 8
  · rw [if_pos h6] at h; omega
  rw [if_neg h6] at h; omega

theorem chain5Data_chain5Cross : Chain5Data chain5Cross 5 6 7 8 zone5 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by omega, by omega,
    by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, fun c hc => ?_⟩
  · intro z1 z2 z3 a b c d e f
    rcases zone5_cases a with h | h | h | h | h | h | h <;> rcases zone5_cases b with h' | h' | h' | h' | h' | h' | h' <;>
      rcases zone5_cases c with h'' | h'' | h'' | h'' | h'' | h'' | h'' <;> omega
  · intro z1 z2 z3 a b c d e f
    rcases zone5_cases a with h | h | h | h | h | h | h <;> rcases zone5_cases b with h' | h' | h' | h' | h' | h' | h' <;>
      rcases zone5_cases c with h'' | h'' | h'' | h'' | h'' | h'' | h'' <;> omega
  · intro z1 z2 a b
    rcases zone5_cases a with h | h | h | h | h | h | h <;> rcases zone5_cases b with h' | h' | h' | h' | h' | h' | h' <;>
      omega
  · intro z1 z2 a b
    rcases zone5_cases a with h | h | h | h | h | h | h <;> rcases zone5_cases b with h' | h' | h' | h' | h' | h' | h' <;>
      omega
  · intro z1 z2 a b
    rcases zone5_cases a with h | h | h | h | h | h | h <;> rcases zone5_cases b with h' | h' | h' | h' | h' | h' | h' <;>
      omega
  · simp only [chain5Cross, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl (by simp [ClIn, zone5]))
    · exact Or.inr (Or.inr (Or.inl (by simp [ClIn, zone5])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [ClIn, zone5]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [ClIn, zone5])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [ClIn, zone5])))))

theorem chain5Data_chain5Cross_rev : Chain5Data chain5Cross 8 7 6 5 zone5r := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by omega, by omega,
    by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, fun c hc => ?_⟩
  · intro z1 z2 z3 a b c d e f
    rcases zone5r_cases a with h | h | h | h | h | h | h <;> rcases zone5r_cases b with h' | h' | h' | h' | h' | h' | h' <;>
      rcases zone5r_cases c with h'' | h'' | h'' | h'' | h'' | h'' | h'' <;> omega
  · intro z1 z2 z3 a b c d e f
    rcases zone5r_cases a with h | h | h | h | h | h | h <;> rcases zone5r_cases b with h' | h' | h' | h' | h' | h' | h' <;>
      rcases zone5r_cases c with h'' | h'' | h'' | h'' | h'' | h'' | h'' <;> omega
  · intro z1 z2 a b
    rcases zone5r_cases a with h | h | h | h | h | h | h <;> rcases zone5r_cases b with h' | h' | h' | h' | h' | h' | h' <;>
      omega
  · intro z1 z2 a b
    rcases zone5r_cases a with h | h | h | h | h | h | h <;> rcases zone5r_cases b with h' | h' | h' | h' | h' | h' | h' <;>
      omega
  · intro z1 z2 a b
    rcases zone5r_cases a with h | h | h | h | h | h | h <;> rcases zone5r_cases b with h' | h' | h' | h' | h' | h' | h' <;>
      omega
  · simp only [chain5Cross, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [ClIn, zone5r])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [ClIn, zone5r])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [ClIn, zone5r]))))
    · exact Or.inr (Or.inr (Or.inl (by simp [ClIn, zone5r])))
    · exact Or.inr (Or.inl (by simp [ClIn, zone5r]))

/-- La ventana de la cláusula `j` (de `1` a `3`) lee sus primer y tercer literales. -/
theorem win_chain5Cross {j : Nat} {c : Clause} (hj : chain5Cross.clauses[j]? = some c) :
    ReadsAt chain5Cross (clauseStep chain5Cross j 2) c.l1.v ∧ ReadsAt chain5Cross (clauseStep chain5Cross j 2) c.l3.v :=
  ⟨⟨clauseStep chain5Cross j 0, Or.inr (Or.inr ⟨by simp [clauseStep, chain5Cross]; omega, by simp [clauseStep]⟩),
      stepVar_clause hj 0 (by omega)⟩, ⟨clauseStep chain5Cross j 2, Or.inl rfl, stepVar_clause hj 2 (by omega)⟩⟩

theorem cs_lt {j : Nat} (hj : j < 5) : clauseStep chain5Cross j 2 < stepCount chain5Cross := by
  simp [clauseStep, stepCount, chain5Cross]; omega

namespace MachineOn

open GPathB Driver Machine

/-- **T2 en `chain5_cross`**: fijar un separador, con lo que sea fijado antes, por los lemas de cinco bloques. -/
theorem sepPinFree_chain5Cross : SepPinFree chain5Cross [5, 6, 7, 8] (stepCount chain5Cross) := by
  intro k R0 r s _ hs hrs hr1 hrT
  have hs' : s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by
    have := List.mem_of_getElem? hs
    simpa using this
  have hl := locPair_read (φ := chain5Cross) (stepCount chain5Cross) k R0 r
  have h1 : chain5Cross.clauses[1]? = some ⟨⟨5, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩ := rfl
  have h2 : chain5Cross.clauses[2]? = some ⟨⟨6, false⟩, ⟨1, true⟩, ⟨7, true⟩⟩ := rfl
  have h3 : chain5Cross.clauses[3]? = some ⟨⟨7, false⟩, ⟨3, true⟩, ⟨8, true⟩⟩ := rfl
  have w1 := win_chain5Cross h1
  have w2 := win_chain5Cross h2
  have w3 := win_chain5Cross h3
  have k0 : ∀ j, (0 : Int) ≤ clauseStep chain5Cross j 2 := fun j => by simp [clauseStep]; omega
  have hN : midFusion chain5Cross < stepCount chain5Cross := by unfold stepCount midFusion; omega
  rcases hs' with rfl | rfl | rfl | rfl
  · -- `x5`: el último separador leyendo al revés
    exact phantomFree_chain5_s4 hl chain5Data_chain5Cross_rev hrs ⟨k0 3, cs_lt (by omega), w3.2, w3.1⟩
      ⟨k0 2, cs_lt (by omega), w2.2, w2.1⟩ (by omega) hrT hN
  · -- `x6`: el tercero leyendo al revés
    exact phantomFree_chain5_s3 hl chain5Data_chain5Cross_rev hrs ⟨k0 3, cs_lt (by omega), w3.2, w3.1⟩
      ⟨k0 2, cs_lt (by omega), w2.2, w2.1⟩ ⟨k0 1, cs_lt (by omega), w1.2, w1.1⟩ (by omega) hrT
  · exact phantomFree_chain5_s3 hl chain5Data_chain5Cross hrs ⟨k0 1, cs_lt (by omega), w1.1, w1.2⟩
      ⟨k0 2, cs_lt (by omega), w2.1, w2.2⟩ ⟨k0 3, cs_lt (by omega), w3.1, w3.2⟩ (by omega) hrT
  · exact phantomFree_chain5_s4 hl chain5Data_chain5Cross hrs ⟨k0 1, cs_lt (by omega), w1.1, w1.2⟩
      ⟨k0 2, cs_lt (by omega), w2.1, w2.2⟩ (by omega) hrT hN

theorem sepCover_chain5Cross : SepCover chain5Cross [5, 6, 7, 8] zone5 := by
  refine ⟨fun c hc z z' hz hz' hzS hz'S => ?_, fun p z1 z2 z3 n1 n2 n3 h1 h2 h3 d12 d13 d23 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hzS hz'S
    simp only [chain5Cross, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp only [ClVar] at hz hz' <;>
      rcases hz with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl <;> simp_all [zone5]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at n1 n2 n3
    rcases zone5_cases h1 with h | h | h | h | h | h | h <;> rcases zone5_cases h2 with h' | h' | h' | h' | h' | h' | h' <;>
      rcases zone5_cases h3 with h'' | h'' | h'' | h'' | h'' | h'' | h'' <;> omega

/-- **El lector por separadores no se atasca en `chain5_cross`**, con las líneas como hipótesis (la máquina las cumple:
`probe_exact3.jl` da 0 fuera en todos los estados): toda lectura que empieza por `x5, x6, x7, x8` deja un estado válido
con la rama de una solución que coincide con todas las elecciones. -/
theorem reader_sep_chain5Cross (HA : ∀ T : Int, 1 ≤ T → PhantomAtW chain5Cross T) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on chain5Cross) {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g')
    (hsf : SepFirst chain5Cross [5, 6, 7, 8] R) :
    g'.isValid = true ∧ ∃ a, Sat a chain5Cross ∧ (∀ r ∈ R, selOfAssign chain5Cross a r.step = r) ∧
      CT g' (pidOfAssign chain5Cross a) :=
  reader_sep_on bounded_chain5Cross HA sepCover_chain5Cross sepPinFree_chain5Cross hkv hr hsf

end MachineOn

end AbsSatBingo.Model
