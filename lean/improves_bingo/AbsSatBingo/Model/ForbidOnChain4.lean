-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4.lean
import AbsSatBingo.Model.ForbidOnDescent

/-!
# Cuatro bloques en cadena: la variable fijada en un separador

Bloques `A ∪ {s1}`, `{s1} ∪ M ∪ {s2}`, `{s2} ∪ N ∪ {s3}`, `{s3} ∪ C` (`Chain4Data`), con `A`, `C` sin tres variables
distintas y `M`, `N` con a lo sumo una. Aquí la variable `v` del paso fijado es un separador: `v = s3` o `v = s2` (y
`v = s1` es `v = s3` leyendo la cadena al revés). Sin hipótesis sobre la numeración de las variables.

Por descenso (`ForbidOnDescent`), con el rango por **lectura**: qué separadores lee alguna ventana del triángulo
(`InW`). La rama final es `glue4`, una fuente por bloque; es de `P0` si dos fuentes vecinas leen igual el separador
que comparten (`glue4_P0`), y de `P` si son de `P` las fuentes de los bloques que contienen a `v` (`glue4_P`).

Las fuentes salen de las ramas de las caras de un testigo, y de la propia rama `a0` del triángulo en los bloques que no
contienen a `v`. Dos fuentes vecinas leen igual el separador `s` si vienen del testigo del paso de `s`, si las dos
coinciden con `a0` en `s` porque lo lee una ventana, o, si `s = v`, si las dos son de `P`.

**Lo nuevo: dos testigos a la vez** (`c4s2_none`). Con `v = s2` y un triángulo que no lee `s1` ni `s3`, el lado
izquierdo sale de las caras del testigo del paso de `s1` y el derecho de las del paso de `s3`; se pegan en `v`, que
todas las ramas de `P` leen igual.

* `v = s3` (`phantomFree_chain4_s3`): rangos «lee `s2`» (testigo de `σ`), «lee `s1`» (testigo de `s2`), «nada»
  (testigo de `s1`).
* `v = s2` (`phantomFree_chain4_s2`): «lee `s1` y `s3`» (testigo de `σ`); «solo `s1`» (testigo de `s3`, con las dos
  caras por el nodo que lee `s1`); «solo `s3`» (al revés); «nada» (dos testigos).

Abierto: `v` dentro de un bloque (en `A`, `M`, `N` o `C`). Ahí la variable fijada no separa, las fuentes de testigos
distintos no se pegan, y un triángulo que no lee ningún separador pide una sola cara para tres variables de los
lados (`Faces.pick3` dice qué ventana lee cada una).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

-- ============================================================
-- Lecturas de una ventana
-- ============================================================

/-- La ventana del paso `k` lee la variable `z`. -/
def ReadsAt (φ : Cnf) (k : Int) (z : Nat) : Prop := ∃ k', InWin k k' ∧ stepVar φ k' = some z

theorem inW_of_reads {i j l k : Int} {z : Nat} (hk : k = i ∨ k = j ∨ k = l) (h : ReadsAt φ k z) : InW φ i j l z := by
  obtain ⟨k', hw, hz⟩ := h
  exact ⟨k, k', hk, hw, hz⟩

theorem var_of_reads {a b : Assign} {k : Int} (h : pidOfAssign φ a k = pidOfAssign φ b k) {z : Nat}
    (hr : ReadsAt φ k z) : a z = b z := by
  obtain ⟨k', hw, hz⟩ := hr
  exact var_of_pid_eq h hw hz

theorem reads_self {k : Int} {z : Nat} (h : stepVar φ k = some z) : ReadsAt φ k z := ⟨k, Or.inl rfl, h⟩

theorem inW_swap12 {i j l : Int} {z : Nat} (h : InW φ i j l z) : InW φ j i l z := by
  obtain ⟨k, k', hk, hw, hz⟩ := h
  refine ⟨k, k', ?_, hw, hz⟩
  rcases hk with e | e | e
  · exact Or.inr (Or.inl e)
  · exact Or.inl e
  · exact Or.inr (Or.inr e)

theorem inW_swap23 {i j l : Int} {z : Nat} (h : InW φ i j l z) : InW φ i l j z := by
  obtain ⟨k, k', hk, hw, hz⟩ := h
  refine ⟨k, k', ?_, hw, hz⟩
  rcases hk with e | e | e
  · exact Or.inl e
  · exact Or.inr (Or.inr e)
  · exact Or.inr (Or.inl e)

/-- Sin tres variables distintas. -/
def No3 (M : Nat → Prop) : Prop := ∀ z1 z2 z3, M z1 → M z2 → M z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False

/-- A lo sumo una variable. -/
def Le1 (M : Nat → Prop) : Prop := ∀ z1 z2, M z1 → M z2 → z1 = z2

theorem le1_eq (s : Nat) : Le1 (fun z => z = s) := fun _ _ h1 h2 => h1.trans h2.symm

theorem no3_or {M M' : Nat → Prop} (h1 : Le1 M) (h2 : Le1 M') : No3 (fun z => M z ∨ M' z) := by
  intro y1 y2 y3 b1 b2 b3 e12 e13 e23
  rcases b1 with b1 | b1 <;> rcases b2 with b2 | b2 <;> rcases b3 with b3 | b3
  · exact e12 (h1 _ _ b1 b2)
  · exact e12 (h1 _ _ b1 b2)
  · exact e13 (h1 _ _ b1 b3)
  · exact e23 (h2 _ _ b2 b3)
  · exact e23 (h1 _ _ b2 b3)
  · exact e13 (h2 _ _ b1 b3)
  · exact e12 (h2 _ _ b1 b2)
  · exact e12 (h2 _ _ b1 b2)

section FacesMore

variable {Q : Assign → Prop} {a0 c1 c2 c3 : Assign} {i j l : Int}

/-- **La cuenta, diciendo qué ventana lee cada variable**: o una de las tres ramas coincide con `a0` en las variables
de `M` de las ventanas, o hay tres variables distintas de `M`, una en la ventana que le falta a cada rama (la del
tercer nodo, la del segundo y la del primero). -/
theorem Faces.pick3 (F : Faces φ Q a0 c1 c2 c3 i j l) (M : Nat → Prop) :
    (∃ c, Q c ∧ Agr φ i j l M c a0) ∨
      ∃ z1 z2 z3, M z1 ∧ M z2 ∧ M z3 ∧ z1 ≠ z2 ∧ z1 ≠ z3 ∧ z2 ≠ z3 ∧ ReadsAt φ l z1 ∧ ReadsAt φ j z2 ∧
        ReadsAt φ i z3 := by
  have alt : ∀ c : Assign, Agr φ i j l M c a0 ∨ ∃ z, M z ∧ InW φ i j l z ∧ c z ≠ a0 z := by
    intro c
    by_cases hex : ∃ z, M z ∧ InW φ i j l z ∧ c z ≠ a0 z
    · exact Or.inr hex
    · left
      intro z hm hw
      by_cases he : c z = a0 z
      · exact he
      · exact absurd ⟨z, hm, hw, he⟩ hex
  rcases alt c1 with g | ⟨z1, m1, w1, n1⟩
  · exact Or.inl ⟨c1, F.q1, g⟩
  rcases alt c2 with g | ⟨z2, m2, w2, n2⟩
  · exact Or.inl ⟨c2, F.q2, g⟩
  rcases alt c3 with g | ⟨z3, m3, w3, n3⟩
  · exact Or.inl ⟨c3, F.q3, g⟩
  right
  obtain ⟨k1, k1', hk1, hw1, hz1⟩ := w1
  obtain ⟨k2, k2', hk2, hw2, hz2⟩ := w2
  obtain ⟨k3, k3', hk3, hw3, hz3⟩ := w3
  have r1 : ReadsAt φ l z1 := by
    rcases hk1 with e | e | e
    · exact absurd (var_of_pid_eq F.e1 (by rw [← e]; exact hw1) hz1) n1
    · exact absurd (var_of_pid_eq F.e3 (by rw [← e]; exact hw1) hz1) n1
    · exact ⟨k1', by rw [← e]; exact hw1, hz1⟩
  have r2 : ReadsAt φ j z2 := by
    rcases hk2 with e | e | e
    · exact absurd (var_of_pid_eq F.e2 (by rw [← e]; exact hw2) hz2) n2
    · exact ⟨k2', by rw [← e]; exact hw2, hz2⟩
    · exact absurd (var_of_pid_eq F.e5 (by rw [← e]; exact hw2) hz2) n2
  have r3 : ReadsAt φ i z3 := by
    rcases hk3 with e | e | e
    · exact ⟨k3', by rw [← e]; exact hw3, hz3⟩
    · exact absurd (var_of_pid_eq F.e4 (by rw [← e]; exact hw3) hz3) n3
    · exact absurd (var_of_pid_eq F.e6 (by rw [← e]; exact hw3) hz3) n3
  refine ⟨z1, z2, z3, m1, m2, m3, fun e => n1 ?_, fun e => n1 ?_, fun e => n2 ?_, r1, r2, r3⟩
  · rw [e]; exact var_of_reads F.e3 r2
  · rw [e]; exact var_of_reads F.e1 r3
  · rw [e]; exact var_of_reads F.e2 r3

end FacesMore

-- ============================================================
-- La cadena de cuatro bloques y la rama de cuatro fuentes
-- ============================================================

/-- Las tres variables de una cláusula cumplen `B`. -/
def ClIn (B : Nat → Prop) (c : Clause) : Prop := B c.l1.v ∧ B c.l2.v ∧ B c.l3.v

/-- Una variable de la cadena. -/
def InCh4 (s1 s2 s3 : Nat) (A M N C : Nat → Prop) (z : Nat) : Prop :=
  A z ∨ M z ∨ N z ∨ C z ∨ z = s1 ∨ z = s2 ∨ z = s3

/-- **`Chain4Data φ s1 s2 s3 A M N C`**: cuatro bloques en cadena, `A ∪ {s1}`, `{s1} ∪ M ∪ {s2}`, `{s2} ∪ N ∪ {s3}`
y `{s3} ∪ C`. Cada cláusula está entera fuera o entera en un bloque. -/
structure Chain4Data (φ : Cnf) (s1 s2 s3 : Nat) (A M N C : Nat → Prop) : Prop where
  s1v  : s1 < φ.nVars
  s2v  : s2 < φ.nVars
  s3v  : s3 < φ.nVars
  ne12 : s1 ≠ s2
  ne13 : s1 ≠ s3
  ne23 : s2 ≠ s3
  aS1  : ¬ A s1
  aS2  : ¬ A s2
  aS3  : ¬ A s3
  mS1  : ¬ M s1
  mS2  : ¬ M s2
  mS3  : ¬ M s3
  nS1  : ¬ N s1
  nS2  : ¬ N s2
  nS3  : ¬ N s3
  cS1  : ¬ C s1
  cS2  : ¬ C s2
  cS3  : ¬ C s3
  dAM  : ∀ z, A z → M z → False
  dAN  : ∀ z, A z → N z → False
  dAC  : ∀ z, A z → C z → False
  dMN  : ∀ z, M z → N z → False
  dMC  : ∀ z, M z → C z → False
  dNC  : ∀ z, N z → C z → False
  cardA : No3 A
  cardC : No3 C
  cardM : Le1 M
  cardN : Le1 N
  cl   : ∀ c ∈ φ.clauses, ClIn (fun z => ¬ InCh4 s1 s2 s3 A M N C z) c ∨ ClIn (fun z => A z ∨ z = s1) c ∨
    ClIn (fun z => z = s1 ∨ M z ∨ z = s2) c ∨ ClIn (fun z => z = s2 ∨ N z ∨ z = s3) c ∨ ClIn (fun z => C z ∨ z = s3) c

/-- **Una fuente por bloque**: `d4` en `C`, `d3` en `N ∪ {s3}`, `d2` en `M ∪ {s2}`, `d1` en `A ∪ {s1}`, `a0` en lo
demás. -/
noncomputable def glue4 (s1 s2 s3 : Nat) (A M N C : Nat → Prop) (d4 d3 d2 d1 a0 : Assign) : Assign :=
  patch C d4 (patch (fun z => N z ∨ z = s3) d3 (patch (fun z => M z ∨ z = s2) d2 (patch (fun z => A z ∨ z = s1) d1 a0)))

section Glue4

variable {s1 s2 s3 : Nat} {A M N C : Nat → Prop} {d4 d3 d2 d1 a0 : Assign}

theorem g4C {z : Nat} (h : C z) : glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0 z = d4 z := patch_in h

theorem g4N (D : Chain4Data φ s1 s2 s3 A M N C) {z : Nat} (h : N z ∨ z = s3) :
    glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0 z = d3 z := by
  have nc : ¬ C z := by
    rcases h with h | h
    · exact fun hc => D.dNC z h hc
    · rw [h]; exact D.cS3
  unfold glue4
  rw [patch_out nc]
  exact patch_in (B := fun z => N z ∨ z = s3) h

theorem g4M (D : Chain4Data φ s1 s2 s3 A M N C) {z : Nat} (h : M z ∨ z = s2) :
    glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0 z = d2 z := by
  have nc : ¬ C z := by
    rcases h with h | h
    · exact fun hc => D.dMC z h hc
    · rw [h]; exact D.cS2
  have nn : ¬ (N z ∨ z = s3) := by
    rcases h with h | h
    · rintro (h' | h')
      · exact D.dMN z h h'
      · rw [h'] at h; exact D.mS3 h
    · rintro (h' | h')
      · rw [h] at h'; exact D.nS2 h'
      · exact D.ne23 (h.symm.trans h')
  unfold glue4
  rw [patch_out nc, patch_out (B := fun z => N z ∨ z = s3) nn]
  exact patch_in (B := fun z => M z ∨ z = s2) h

theorem g4A (D : Chain4Data φ s1 s2 s3 A M N C) {z : Nat} (h : A z ∨ z = s1) :
    glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0 z = d1 z := by
  have nc : ¬ C z := by
    rcases h with h | h
    · exact fun hc => D.dAC z h hc
    · rw [h]; exact D.cS1
  have nn : ¬ (N z ∨ z = s3) := by
    rcases h with h | h
    · rintro (h' | h')
      · exact D.dAN z h h'
      · rw [h'] at h; exact D.aS3 h
    · rintro (h' | h')
      · rw [h] at h'; exact D.nS1 h'
      · exact D.ne13 (h.symm.trans h')
  have nm : ¬ (M z ∨ z = s2) := by
    rcases h with h | h
    · rintro (h' | h')
      · exact D.dAM z h h'
      · rw [h'] at h; exact D.aS2 h
    · rintro (h' | h')
      · rw [h] at h'; exact D.mS1 h'
      · exact D.ne12 (h.symm.trans h')
  unfold glue4
  rw [patch_out nc, patch_out (B := fun z => N z ∨ z = s3) nn, patch_out (B := fun z => M z ∨ z = s2) nm]
  exact patch_in (B := fun z => A z ∨ z = s1) h

theorem g4O {z : Nat} (h : ¬ InCh4 s1 s2 s3 A M N C z) : glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0 z = a0 z := by
  unfold glue4
  rw [patch_out (fun hc => h (Or.inr (Or.inr (Or.inr (Or.inl hc))))),
    patch_out (B := fun z => N z ∨ z = s3) (fun hn => hn.elim (fun n => h (Or.inr (Or.inr (Or.inl n))))
      (fun e => h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))))),
    patch_out (B := fun z => M z ∨ z = s2) (fun hm => hm.elim (fun m => h (Or.inr (Or.inl m)))
      (fun e => h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))))))]
  exact patch_out (B := fun z => A z ∨ z = s1) (fun ha => ha.elim (fun a => h (Or.inl a))
    (fun e => h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))))

theorem g4B2 (D : Chain4Data φ s1 s2 s3 A M N C) (e1 : d1 s1 = d2 s1) {z : Nat} (h : z = s1 ∨ M z ∨ z = s2) :
    glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0 z = d2 z := by
  rcases h with h | h | h
  · rw [g4A D (Or.inr h), h]; exact e1
  · exact g4M D (Or.inl h)
  · exact g4M D (Or.inr h)

theorem g4B3 (D : Chain4Data φ s1 s2 s3 A M N C) (e2 : d2 s2 = d3 s2) {z : Nat} (h : z = s2 ∨ N z ∨ z = s3) :
    glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0 z = d3 z := by
  rcases h with h | h | h
  · rw [g4M D (Or.inr h), h]; exact e2
  · exact g4N D (Or.inl h)
  · exact g4N D (Or.inr h)

theorem g4B4 (D : Chain4Data φ s1 s2 s3 A M N C) (e3 : d3 s3 = d4 s3) {z : Nat} (h : C z ∨ z = s3) :
    glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0 z = d4 z := by
  rcases h with h | h
  · exact g4C h
  · rw [g4N D (Or.inr h), h]; exact e3

variable {P0 P : Assign → Prop} {σ : Int}

/-- **La rama de cuatro fuentes es de `P0`** si las fuentes vecinas leen igual el separador que comparten. -/
theorem glue4_P0 (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M N C) (h0 : P0 a0) (h1 : P0 d1) (h2 : P0 d2)
    (h3 : P0 d3) (h4 : P0 d4) (e1 : d1 s1 = d2 s1) (e2 : d2 s2 = d3 s2) (e3 : d3 s3 = d4 s3) :
    P0 (glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0) := by
  refine p0_of_sources hl ⟨a0, h0⟩ (fun z => ?_) (fun cl hcl => ?_)
  · by_cases hc : C z
    · exact ⟨d4, h4, g4C hc⟩
    by_cases hn : N z ∨ z = s3
    · exact ⟨d3, h3, g4N D hn⟩
    by_cases hm : M z ∨ z = s2
    · exact ⟨d2, h2, g4M D hm⟩
    by_cases ha : A z ∨ z = s1
    · exact ⟨d1, h1, g4A D ha⟩
    refine ⟨a0, h0, g4O ?_⟩
    rintro (h | h | h | h | h | h | h)
    · exact ha (Or.inl h)
    · exact hm (Or.inl h)
    · exact hn (Or.inl h)
    · exact hc h
    · exact ha (Or.inr h)
    · exact hm (Or.inr h)
    · exact hn (Or.inr h)
  · rcases D.cl cl hcl with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩
    · exact ⟨a0, h0, g4O o1, g4O o2, g4O o3⟩
    · exact ⟨d1, h1, g4A D i1, g4A D i2, g4A D i3⟩
    · exact ⟨d2, h2, g4B2 D e1 i1, g4B2 D e1 i2, g4B2 D e1 i3⟩
    · exact ⟨d3, h3, g4B3 D e2 i1, g4B3 D e2 i2, g4B3 D e2 i3⟩
    · exact ⟨d4, h4, g4B4 D e3 i1, g4B4 D e3 i2, g4B4 D e3 i3⟩

/-- **Y de `P`** con `v` un separador (`s3` o `s2`), si son de `P` las fuentes de los dos bloques que lo contienen. -/
theorem glue4_P (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M N C) {v : Nat} (hv : stepVar φ σ = some v)
    (h0 : P0 a0) (h1 : P0 d1) (h2 : P0 d2) (h3 : P0 d3) (h4 : P0 d4) (e1 : d1 s1 = d2 s1) (e2 : d2 s2 = d3 s2)
    (e3 : d3 s3 = d4 s3) (hpos : (v = s3 ∧ P d3 ∧ P d4) ∨ (v = s2 ∧ P d2 ∧ P d3)) :
    P (glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0) := by
  refine p_of_sources hl (glue4_P0 hl D h0 h1 h2 h3 h4 e1 e2 e3) (fun h => by rw [hv] at h; cases h)
    (fun z hz => ?_)
  rw [hv] at hz; cases hz
  have tv : ∀ {Q : Nat → Prop} {cl : Clause}, ClVar cl v → ClIn Q cl → Q v := by
    intro Q cl hcv hin
    obtain ⟨a, b, c⟩ := hin
    rcases hcv with e | e | e
    · rw [e]; exact a
    · rw [e]; exact b
    · rw [e]; exact c
  rcases hpos with ⟨hs, q3, q4⟩ | ⟨hs, q2, q3⟩
  · subst hs
    refine ⟨⟨d3, q3, g4N D (Or.inr rfl)⟩, fun cl hcl hcv => ?_⟩
    rcases D.cl cl hcl with hi | hi | hi | hi | hi
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) (tv hcv hi)
    · rcases tv hcv hi with h | h
      · exact absurd h D.aS3
      · exact absurd h.symm D.ne13
    · rcases tv hcv hi with h | h | h
      · exact absurd h.symm D.ne13
      · exact absurd h D.mS3
      · exact absurd h.symm D.ne23
    · obtain ⟨i1, i2, i3⟩ := hi
      exact ⟨d3, q3, g4B3 D e2 i1, g4B3 D e2 i2, g4B3 D e2 i3⟩
    · obtain ⟨i1, i2, i3⟩ := hi
      exact ⟨d4, q4, g4B4 D e3 i1, g4B4 D e3 i2, g4B4 D e3 i3⟩
  · subst hs
    refine ⟨⟨d2, q2, g4M D (Or.inr rfl)⟩, fun cl hcl hcv => ?_⟩
    rcases D.cl cl hcl with hi | hi | hi | hi | hi
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (tv hcv hi)
    · rcases tv hcv hi with h | h
      · exact absurd h D.aS2
      · exact absurd h.symm D.ne12
    · obtain ⟨i1, i2, i3⟩ := hi
      exact ⟨d2, q2, g4B2 D e1 i1, g4B2 D e1 i2, g4B2 D e1 i3⟩
    · obtain ⟨i1, i2, i3⟩ := hi
      exact ⟨d3, q3, g4B3 D e2 i1, g4B3 D e2 i2, g4B3 D e2 i3⟩
    · rcases tv hcv hi with h | h
      · exact absurd h D.cS2
      · exact absurd h D.ne23

/-- La rama de cuatro fuentes pasa por las ventanas de `a0` si cada fuente coincide con `a0` en las variables de su
parte que leen las ventanas. -/
theorem glue4_pid {i j l k : Int} (hk : k = i ∨ k = j ∨ k = l) (h4 : Agr φ i j l C d4 a0)
    (h3 : Agr φ i j l (fun z => N z ∨ z = s3) d3 a0) (h2 : Agr φ i j l (fun z => M z ∨ z = s2) d2 a0)
    (h1 : Agr φ i j l (fun z => A z ∨ z = s1) d1 a0) :
    pidOfAssign φ (glue4 s1 s2 s3 A M N C d4 d3 d2 d1 a0) k = pidOfAssign φ a0 k := by
  refine pid_of_agree (fun k' z hw hz => ?_)
  have iw : InW φ i j l z := ⟨k, k', hk, hw, hz⟩
  unfold glue4
  by_cases hc : C z
  · rw [patch_in hc]; exact h4 z hc iw
  rw [patch_out hc]
  by_cases hn : N z ∨ z = s3
  · rw [patch_in (B := fun z => N z ∨ z = s3) hn]; exact h3 z hn iw
  rw [patch_out (B := fun z => N z ∨ z = s3) hn]
  by_cases hm : M z ∨ z = s2
  · rw [patch_in (B := fun z => M z ∨ z = s2) hm]; exact h2 z hm iw
  rw [patch_out (B := fun z => M z ∨ z = s2) hm]
  by_cases ha : A z ∨ z = s1
  · rw [patch_in (B := fun z => A z ∨ z = s1) ha]; exact h1 z ha iw
  exact patch_out (B := fun z => A z ∨ z = s1) ha

end Glue4

namespace GPathB

variable {P0 P : Assign → Prop} {N σ : Int} {R : PathNodeId → PathNodeId → Prop} {Tf : Trios}

-- ============================================================
-- Herramientas de los pasos
-- ============================================================

section Tools

variable {s1 s2 s3 : Nat} {A M Nn C : Nat → Prop}

/-- **Cerrar un triángulo con cuatro fuentes.** -/
theorem glue4_tri (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M Nn C) {v : Nat}
    (hv : stepVar φ σ = some v) {x u w : PathNodeId} {a0 d1 d2 d3 d4 : Assign} (h0 : P0 a0)
    (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) (p1 : P0 d1) (p2 : P0 d2) (p3 : P0 d3) (p4 : P0 d4)
    (e1 : d1 s1 = d2 s1) (e2 : d2 s2 = d3 s2) (e3 : d3 s3 = d4 s3)
    (hpos : (v = s3 ∧ P d3 ∧ P d4) ∨ (v = s2 ∧ P d2 ∧ P d3))
    (a4 : Agr φ x.id.step u.id.step w.id.step C d4 a0)
    (a3 : Agr φ x.id.step u.id.step w.id.step (fun z => Nn z ∨ z = s3) d3 a0)
    (a2 : Agr φ x.id.step u.id.step w.id.step (fun z => M z ∨ z = s2) d2 a0)
    (a1 : Agr φ x.id.step u.id.step w.id.step (fun z => A z ∨ z = s1) d1 a0) : TriOf φ P x u w :=
  ⟨glue4 s1 s2 s3 A M Nn C d4 d3 d2 d1 a0, glue4_P hl D hv h0 p1 p2 p3 p4 e1 e2 e3 hpos,
    (glue4_pid (Or.inl rfl) a4 a3 a2 a1).trans hx0, (glue4_pid (Or.inr (Or.inl rfl)) a4 a3 a2 a1).trans hu0,
    (glue4_pid (Or.inr (Or.inr rfl)) a4 a3 a2 a1).trans hw0⟩

end Tools

theorem agr_refl' {i j l : Int} {M : Nat → Prop} {a0 : Assign} : Agr φ i j l M a0 a0 := fun _ _ _ => rfl

theorem agr_mono {i j l : Int} {M M' : Nat → Prop} {c a0 : Assign} (h : Agr φ i j l M c a0) (hm : ∀ z, M' z → M z) :
    Agr φ i j l M' c a0 := fun z hz iw => h z (hm z hz) iw

/-- `Agr` en `M ∪ {s}` a partir de `M` y de `s`. -/
theorem agr_or {i j l : Int} {M : Nat → Prop} {s : Nat} {c a0 : Assign} (h : Agr φ i j l M c a0)
    (hs : InW φ i j l s → c s = a0 s) : Agr φ i j l (fun z => M z ∨ z = s) c a0 := by
  intro z hz iw
  rcases hz with hz | hz
  · exact h z hz iw
  · subst hz; exact hs iw

/-- Un testigo en un paso que lee `s`, para un triángulo que no lee `s`: no es ninguno de sus nodos. -/
theorem wit_out (hS : PhStruct φ P0 N R Tf) {x u w : PathNodeId} (t : Tri R Tf x u w) {lam : Int} (h0 : 0 ≤ lam)
    (hN : lam < N) {s : Nat} (hs : stepVar φ lam = some s) (hno : ¬ InW φ x.id.step u.id.step w.id.step s) :
    ∃ n, n.id.step = lam ∧ Tri R Tf x u n ∧ Tri R Tf x w n ∧ Tri R Tf u w n := by
  obtain ⟨n, hns, hn⟩ := t.wit hS h0 hN
  rcases hn with hn | ⟨t1, t2, t3⟩
  · exfalso
    apply hno
    rcases hn with e | e | e
    · exact inW_of_reads (Or.inl rfl) (by rw [← e, hns]; exact reads_self hs)
    · exact inW_of_reads (Or.inr (Or.inl rfl)) (by rw [← e, hns]; exact reads_self hs)
    · exact inW_of_reads (Or.inr (Or.inr rfl)) (by rw [← e, hns]; exact reads_self hs)
  · exact ⟨n, hns, t1, t2, t3⟩

/-- Una cara por el testigo `n` del paso `lam` lee la variable de `lam`. -/
theorem face_reads {y z n : PathNodeId} {lam : Int} {s : Nat} (hns : n.id.step = lam) (hs : stepVar φ lam = some s) :
    InW φ y.id.step z.id.step n.id.step s :=
  inW_of_reads (Or.inr (Or.inr rfl)) (by rw [hns]; exact reads_self hs)

/-- **Las caras de un testigo**, con las tres ramas de `P` y la variable del paso del testigo leída igual. -/
theorem faces_P (hS : PhStruct φ P0 N R Tf) {x u w : PathNodeId} (t : Tri R Tf x u w) {a0 : Assign}
    (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) {lam : Int} (h0 : 0 ≤ lam) (hN : lam < N) {s : Nat}
    (hs : stepVar φ lam = some s) (hno : ¬ InW φ x.id.step u.id.step w.id.step s)
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s → TriOf φ P x' u' w') :
    ∃ c1 c2 c3, Faces φ (fun c => P c ∧ c s = c1 s) a0 c1 c2 c3 x.id.step u.id.step w.id.step := by
  obtain ⟨n, hns, t1, t2, t3⟩ := wit_out hS t h0 hN hs hno
  obtain ⟨c1, q1, c1x, c1u, c1n⟩ := hP x u n t1 (face_reads hns hs)
  obtain ⟨c2, q2, c2x, c2w, c2n⟩ := hP x w n t2 (face_reads hns hs)
  obtain ⟨c3, q3, c3u, c3w, c3n⟩ := hP u w n t3 (face_reads hns hs)
  refine ⟨c1, c2, c3, ⟨⟨q1, rfl⟩, ⟨q2, ?_⟩, ⟨q3, ?_⟩, c1x.trans hx0.symm, c2x.trans hx0.symm, c1u.trans hu0.symm,
    c3u.trans hu0.symm, c2w.trans hw0.symm, c3w.trans hw0.symm⟩⟩
  · exact var_of_reads (c2n.trans c1n.symm) (by rw [hns]; exact reads_self hs)
  · exact var_of_reads (c3n.trans c1n.symm) (by rw [hns]; exact reads_self hs)

/-- **Las caras de un testigo, con el primer nodo leyendo `s'`**: las dos caras por el primer nodo son de `P` (leen
`s'` y la variable `s` del testigo), la tercera solo de `P0`. -/
theorem faces_Px (hl : LocPair φ P0 P σ) (hS : PhStruct φ P0 N R Tf) {x u w : PathNodeId} (t : Tri R Tf x u w) {a0 : Assign}
    (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) {lam : Int} (h0 : 0 ≤ lam) (hN : lam < N) {s s' : Nat}
    (hs : stepVar φ lam = some s) (hno : ¬ InW φ x.id.step u.id.step w.id.step s) (hx : ReadsAt φ x.id.step s')
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s' →
      InW φ x'.id.step u'.id.step w'.id.step s → TriOf φ P x' u' w') :
    ∃ c1 c2 c3, Faces φ (fun c => P0 c ∧ c s = c1 s) a0 c1 c2 c3 x.id.step u.id.step w.id.step ∧ P c1 ∧ P c2 := by
  obtain ⟨n, hns, t1, t2, t3⟩ := wit_out hS t h0 hN hs hno
  obtain ⟨c1, q1, c1x, c1u, c1n⟩ := hP x u n t1 (inW_of_reads (Or.inl rfl) hx) (face_reads hns hs)
  obtain ⟨c2, q2, c2x, c2w, c2n⟩ := hP x w n t2 (inW_of_reads (Or.inl rfl) hx) (face_reads hns hs)
  obtain ⟨c3, q3, c3u, c3w, c3n⟩ := t3.b3 hS
  refine ⟨c1, c2, c3, ⟨⟨hl.sub _ q1, rfl⟩, ⟨hl.sub _ q2, ?_⟩, ⟨q3, ?_⟩, c1x.trans hx0.symm, c2x.trans hx0.symm,
    c1u.trans hu0.symm, c3u.trans hu0.symm, c2w.trans hw0.symm, c3w.trans hw0.symm⟩, q1, q2⟩
  · exact var_of_reads (c2n.trans c1n.symm) (by rw [hns]; exact reads_self hs)
  · exact var_of_reads (c3n.trans c1n.symm) (by rw [hns]; exact reads_self hs)

/-- **Las caras del testigo del paso fijado**: son de `P` (pasan por un nodo de `σ`, el ancla), o el triángulo ya
tiene un nodo en `σ`. -/
theorem faces_sigma (hS : PhStruct φ P0 N R Tf)
    (hanch : ∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a) (hσ0 : 0 ≤ σ) (hσN : σ < N)
    {x u w : PathNodeId} (t : Tri R Tf x u w) {a0 : Assign} (hP0 : P0 a0)
    (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) :
    TriOf φ P x u w ∨ ∃ c1 c2 c3, Faces φ P a0 c1 c2 c3 x.id.step u.id.step w.id.step := by
  obtain ⟨n, hns, hn⟩ := t.wit hS hσ0 hσN
  rcases hn with hn | ⟨t1, t2, t3⟩
  · left
    rcases hn with e | e | e
    · exact ⟨a0, hanch a0 n hP0 (by rw [e]; exact (hS.refl x u t.xu).1) hns (by rw [← hns, e]; exact hx0),
        hx0, hu0, hw0⟩
    · exact ⟨a0, hanch a0 n hP0 (by rw [e]; exact (hS.refl x u t.xu).2) hns (by rw [← hns, e]; exact hu0),
        hx0, hu0, hw0⟩
    · exact ⟨a0, hanch a0 n hP0 (by rw [e]; exact (hS.refl x w t.xw).2) hns (by rw [← hns, e]; exact hw0),
        hx0, hu0, hw0⟩
  · right
    have hRn := (hS.refl x n t1.xw).2
    obtain ⟨c1, q1, c1x, c1u, c1n⟩ := t1.b3 hS
    obtain ⟨c2, q2, c2x, c2w, c2n⟩ := t2.b3 hS
    obtain ⟨c3, q3, c3u, c3w, c3n⟩ := t3.b3 hS
    exact ⟨c1, c2, c3, ⟨hanch c1 n q1 hRn hns (by rw [← hns]; exact c1n), hanch c2 n q2 hRn hns (by rw [← hns]; exact c2n),
      hanch c3 n q3 hRn hns (by rw [← hns]; exact c3n), c1x.trans hx0.symm, c2x.trans hx0.symm, c1u.trans hu0.symm,
      c3u.trans hu0.symm, c2w.trans hw0.symm, c3w.trans hw0.symm⟩⟩

/-- **La variable fijada se lee como en `a0`** en cuanto la lee una ventana, si las dos primeras caras son de `P`. -/
theorem vfix4 (hl : LocPair φ P0 P σ) {v : Nat} (hv : stepVar φ σ = some v) {Q : Assign → Prop}
    {a0 c1 c2 c3 : Assign} {i j l : Int} (F : Faces φ Q a0 c1 c2 c3 i j l) (q1 : P c1) (q2 : P c2) {d : Assign}
    (qd : P d) (h : InW φ i j l v) : d v = a0 v := by
  rcases F.inw h with h | h
  · exact (hl.sameVar hv qd q1).trans h
  · exact (hl.sameVar hv qd q2).trans h

theorem no3_of_le1 {M : Nat → Prop} (h : Le1 M) : No3 M := fun z1 z2 _ a b _ e _ _ => e (h z1 z2 a b)

/-- Elegir entre las dos caras por el primer nodo: la elegida es de `P`, pasa por el primer nodo y coincide con
`a0` en `M`. -/
theorem pick12 {Q : Assign → Prop} {a0 c1 c2 c3 : Assign} {i j l : Int} (F : Faces φ Q a0 c1 c2 c3 i j l)
    (q1 : P c1) (q2 : P c2) {M : Nat → Prop} (hM : Le1 M) :
    ∃ d, P d ∧ Q d ∧ Agr φ i j l M d a0 ∧ pidOfAssign φ d i = pidOfAssign φ a0 i := by
  rcases F.pick2 hM with g | g
  · exact ⟨c1, q1, F.q1, g, F.e1⟩
  · exact ⟨c2, q2, F.q2, g, F.e2⟩

/-- **El primer nodo lee `s`**: un enunciado para esos triángulos vale para todo triángulo que lee `s`, si lo demás
que se pide no cambia al permutar los nodos. -/
theorem of_reads_first (hS : PhStruct φ P0 N R Tf) {H : PathNodeId → PathNodeId → PathNodeId → Prop}
    (h12 : ∀ x u w, H x u w → H u x w) (h23 : ∀ x u w, H x u w → H x w u) {s : Nat}
    (base : ∀ x u w, Tri R Tf x u w → H x u w → ReadsAt φ x.id.step s → TriOf φ P x u w) :
    ∀ x u w, Tri R Tf x u w → H x u w → InW φ x.id.step u.id.step w.id.step s → TriOf φ P x u w := by
  intro x u w t hH hr
  obtain ⟨k, k', hk, hw, hz⟩ := hr
  rcases hk with e | e | e
  · exact base x u w t hH (by rw [← e]; exact ⟨k', hw, hz⟩)
  · exact (base u x w (t.swap12 hS) (h12 _ _ _ hH) (by rw [← e]; exact ⟨k', hw, hz⟩)).swap12
  · exact ((base w x u ((t.swap23 hS).swap12 hS) (h12 _ _ _ (h23 _ _ _ hH))
      (by rw [← e]; exact ⟨k', hw, hz⟩)).swap12).swap23

theorem not_inW_swap12 {i j l : Int} {z : Nat} (h : ¬ InW φ i j l z) : ¬ InW φ j i l z := fun h' => h (inW_swap12 h')
theorem not_inW_swap23 {i j l : Int} {z : Nat} (h : ¬ InW φ i j l z) : ¬ InW φ i l j z := fun h' => h (inW_swap23 h')

-- ============================================================
-- Los rangos
-- ============================================================

open Classical in
/-- Rango de tres valores: `0` si `p`, `1` si `q`, `2` si no. -/
noncomputable def rk3 (p q : Prop) : Nat := if p then 0 else if q then 1 else 2

open Classical in
/-- Rango de cuatro valores: `0` si `p` y `q`, `1` si solo `p`, `2` si solo `q`, `3` si ninguno. -/
noncomputable def rk4 (p q : Prop) : Nat := if p ∧ q then 0 else if p then 1 else if q then 2 else 3

theorem rk3_p {p q : Prop} (h : p) : rk3 p q = 0 := by simp [rk3, h]
theorem rk3_q {p q : Prop} (h : q) : rk3 p q ≤ 1 := by
  unfold rk3; split
  · exact Nat.zero_le _
  · exact Nat.le_refl _
theorem rk3_1 {p q : Prop} (hp : ¬ p) (h : q) : rk3 p q = 1 := by simp [rk3, hp, h]
theorem rk3_2 {p q : Prop} (hp : ¬ p) (h : ¬ q) : rk3 p q = 2 := by simp [rk3, hp, h]

theorem rk4_pq {p q : Prop} (hp : p) (hq : q) : rk4 p q = 0 := by simp [rk4, hp, hq]
theorem rk4_p {p q : Prop} (hp : p) : rk4 p q ≤ 1 := by
  unfold rk4; split
  · exact Nat.zero_le _
  · exact Nat.le_refl _
theorem rk4_q {p q : Prop} (hq : q) : rk4 p q ≤ 2 := by
  unfold rk4; split
  · exact Nat.zero_le _
  · split
    · exact Nat.le_succ _
    · exact Nat.le_refl _
theorem rk4_1 {p q : Prop} (hp : p) (hq : ¬ q) : rk4 p q = 1 := by simp [rk4, hp, hq]
theorem rk4_2 {p q : Prop} (hp : ¬ p) (hq : q) : rk4 p q = 2 := by simp [rk4, hp, hq]
theorem rk4_3 {p q : Prop} (hp : ¬ p) (hq : ¬ q) : rk4 p q = 3 := by simp [rk4, hp, hq]

-- ============================================================
-- `v = s3`
-- ============================================================

section CaseS3

variable {s1 s2 s3 : Nat} {A M Nn C : Nat → Prop}

theorem c4s3_r0 (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M Nn C) (hv : stepVar φ σ = some s3)
    (hS : PhStruct φ P0 N R Tf) (hanch : ∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a)
    (hσ0 : 0 ≤ σ) (hσN : σ < N) {x u w : PathNodeId} (t : Tri R Tf x u w)
    (hr : InW φ x.id.step u.id.step w.id.step s2) : TriOf φ P x u w := by
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  rcases faces_sigma hS hanch hσ0 hσN t hP0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
  · exact h
  obtain ⟨d4, q4, ag4⟩ := F.pick D.cardC
  obtain ⟨d3, q3, ag3⟩ := F.pick (no3_or D.cardN (le1_eq s2))
  refine glue4_tri hl D hv hP0 hx0 hu0 hw0 hP0 hP0 (hl.sub _ q3) (hl.sub _ q4) rfl (ag3 s2 (Or.inr rfl) hr).symm
    (hl.sameVar hv q3 q4) (Or.inl ⟨rfl, q3, q4⟩) ag4
    (agr_or (agr_mono ag3 (fun z h => Or.inl h)) (vfix4 hl hv F F.q1 F.q2 q3)) agr_refl' agr_refl'

theorem c4s3_r1 (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M Nn C) (hv : stepVar φ σ = some s3)
    (hS : PhStruct φ P0 N R Tf) (hN : midFusion φ < N) {x u w : PathNodeId} (t : Tri R Tf x u w)
    (hno : ¬ InW φ x.id.step u.id.step w.id.step s2) (hr : InW φ x.id.step u.id.step w.id.step s1)
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s2 → TriOf φ P x' u' w') :
    TriOf φ P x u w := by
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨c1, c2, c3, F⟩ := faces_P hS t hx0 hu0 hw0 (lam := varStep s2) (by simp only [varStep]; omega)
    (by have := D.s2v; simp only [varStep, midFusion] at hN ⊢; omega) (stepVar_var D.s2v) hno hP
  obtain ⟨d2, ⟨q2, s2e⟩, ag2⟩ := F.pick (no3_or D.cardM (le1_eq s1))
  obtain ⟨d3, ⟨q3, s3e⟩, ag3⟩ := F.pick (no3_of_le1 D.cardN)
  obtain ⟨d4, ⟨q4, _⟩, ag4⟩ := F.pick D.cardC
  refine glue4_tri hl D hv hP0 hx0 hu0 hw0 hP0 (hl.sub _ q2) (hl.sub _ q3) (hl.sub _ q4)
    (ag2 s1 (Or.inr rfl) hr).symm (s2e.trans s3e.symm) (hl.sameVar hv q3 q4) (Or.inl ⟨rfl, q3, q4⟩) ag4
    (agr_or ag3 (vfix4 hl hv F F.q1.1 F.q2.1 q3))
    (agr_or (agr_mono ag2 (fun z h => Or.inl h)) (fun iw => absurd iw hno)) agr_refl'

theorem c4s3_r2 (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M Nn C) (hv : stepVar φ σ = some s3)
    (hS : PhStruct φ P0 N R Tf) (hN : midFusion φ < N) {x u w : PathNodeId} (t : Tri R Tf x u w)
    (hno2 : ¬ InW φ x.id.step u.id.step w.id.step s2) (hno1 : ¬ InW φ x.id.step u.id.step w.id.step s1)
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s1 → TriOf φ P x' u' w') :
    TriOf φ P x u w := by
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨c1, c2, c3, F⟩ := faces_P hS t hx0 hu0 hw0 (lam := varStep s1) (by simp only [varStep]; omega)
    (by have := D.s1v; simp only [varStep, midFusion] at hN ⊢; omega) (stepVar_var D.s1v) hno1 hP
  obtain ⟨d1, ⟨q1, s1e⟩, ag1⟩ := F.pick D.cardA
  obtain ⟨d2, ⟨q2, s2e⟩, ag2⟩ := F.pick (no3_or D.cardM D.cardN)
  obtain ⟨d4, ⟨q4, _⟩, ag4⟩ := F.pick D.cardC
  refine glue4_tri hl D hv hP0 hx0 hu0 hw0 (hl.sub _ q1) (hl.sub _ q2) (hl.sub _ q2) (hl.sub _ q4)
    (s1e.trans s2e.symm) rfl (hl.sameVar hv q2 q4) (Or.inl ⟨rfl, q2, q4⟩) ag4
    (agr_or (agr_mono ag2 (fun z h => Or.inr h)) (vfix4 hl hv F F.q1.1 F.q2.1 q2))
    (agr_or (agr_mono ag2 (fun z h => Or.inl h)) (fun iw => absurd iw hno2))
    (agr_or ag1 (fun iw => absurd iw hno1))

/-- **Cuatro bloques, `v = s3`**: sin familias fantasma, con cualquier numeración. -/
theorem phantomFree_chain4_s3 (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M Nn C)
    (hv : stepVar φ σ = some s3) (hσ0 : 0 ≤ σ) (hσN : σ < N) (hN : midFusion φ < N) : PhantomFree φ P0 P N σ := by
  refine phantomFree_of_descent hσ0 hσN
    (fun x u w => rk3 (InW φ x.id.step u.id.step w.id.step s2) (InW φ x.id.step u.id.step w.id.step s1))
    (fun R Tf hS hanch x u w t ih => ?_)
  by_cases h2 : InW φ x.id.step u.id.step w.id.step s2
  · exact c4s3_r0 hl D hv hS hanch hσ0 hσN t h2
  by_cases h1 : InW φ x.id.step u.id.step w.id.step s1
  · exact c4s3_r1 hl D hv hS hN t h2 h1 (fun x' u' w' t' h' => ih x' u' w' t' (by
      rw [rk3_p h', rk3_1 h2 h1]; omega))
  · exact c4s3_r2 hl D hv hS hN t h2 h1 (fun x' u' w' t' h' => ih x' u' w' t' (by
      have := rk3_q (p := InW φ x'.id.step u'.id.step w'.id.step s2) h'; rw [rk3_2 h2 h1]; omega))

end CaseS3

-- ============================================================
-- `v = s2`
-- ============================================================

section CaseS2

variable {s1 s2 s3 : Nat} {A M Nn C : Nat → Prop}

theorem c4s2_both (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M Nn C) (hv : stepVar φ σ = some s2)
    (hS : PhStruct φ P0 N R Tf) (hanch : ∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a)
    (hσ0 : 0 ≤ σ) (hσN : σ < N) {x u w : PathNodeId} (t : Tri R Tf x u w)
    (h1 : InW φ x.id.step u.id.step w.id.step s1) (h3 : InW φ x.id.step u.id.step w.id.step s3) :
    TriOf φ P x u w := by
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  rcases faces_sigma hS hanch hσ0 hσN t hP0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
  · exact h
  obtain ⟨d2, q2, ag2⟩ := F.pick (no3_or D.cardM (le1_eq s1))
  obtain ⟨d3, q3, ag3⟩ := F.pick (no3_or D.cardN (le1_eq s3))
  refine glue4_tri hl D hv hP0 hx0 hu0 hw0 hP0 (hl.sub _ q2) (hl.sub _ q3) hP0 (ag2 s1 (Or.inr rfl) h1).symm
    (hl.sameVar hv q2 q3) (ag3 s3 (Or.inr rfl) h3) (Or.inr ⟨rfl, q2, q3⟩) agr_refl' ag3
    (agr_or (agr_mono ag2 (fun z h => Or.inl h)) (vfix4 hl hv F F.q1 F.q2 q2)) agr_refl'

/-- Solo se lee `s1`, y lo lee el primer nodo: el testigo del paso de `s3`, con las dos caras por el primer nodo. -/
theorem c4s2_one (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M Nn C) (hv : stepVar φ σ = some s2)
    (hS : PhStruct φ P0 N R Tf) (hN : midFusion φ < N) {x u w : PathNodeId} (t : Tri R Tf x u w)
    (hx : ReadsAt φ x.id.step s1) (hno : ¬ InW φ x.id.step u.id.step w.id.step s3)
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s1 →
      InW φ x'.id.step u'.id.step w'.id.step s3 → TriOf φ P x' u' w') : TriOf φ P x u w := by
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨c1, c2, c3, F, q1, q2⟩ := faces_Px hl hS t hx0 hu0 hw0 (lam := varStep s3) (by simp only [varStep]; omega)
    (by have := D.s3v; simp only [varStep, midFusion] at hN ⊢; omega) (stepVar_var D.s3v) hno hx hP
  obtain ⟨d2, p2, _, ag2, e2x⟩ := pick12 F q1 q2 D.cardM
  obtain ⟨d3, p3, ⟨_, s3e⟩, ag3, _⟩ := pick12 F q1 q2 D.cardN
  obtain ⟨d4, ⟨q4, s4e⟩, ag4⟩ := F.pick D.cardC
  refine glue4_tri hl D hv hP0 hx0 hu0 hw0 hP0 (hl.sub _ p2) (hl.sub _ p3) q4 (var_of_reads e2x hx).symm
    (hl.sameVar hv p2 p3) (s3e.trans s4e.symm) (Or.inr ⟨rfl, p2, p3⟩) ag4
    (agr_or ag3 (fun iw => absurd iw hno)) (agr_or ag2 (vfix4 hl hv F q1 q2 p2)) agr_refl'

/-- Solo se lee `s3`, y lo lee el primer nodo: el testigo del paso de `s1`. -/
theorem c4s2_three (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M Nn C) (hv : stepVar φ σ = some s2)
    (hS : PhStruct φ P0 N R Tf) (hN : midFusion φ < N) {x u w : PathNodeId} (t : Tri R Tf x u w)
    (hx : ReadsAt φ x.id.step s3) (hno : ¬ InW φ x.id.step u.id.step w.id.step s1)
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s3 →
      InW φ x'.id.step u'.id.step w'.id.step s1 → TriOf φ P x' u' w') : TriOf φ P x u w := by
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨c1, c2, c3, F, q1, q2⟩ := faces_Px hl hS t hx0 hu0 hw0 (lam := varStep s1) (by simp only [varStep]; omega)
    (by have := D.s1v; simp only [varStep, midFusion] at hN ⊢; omega) (stepVar_var D.s1v) hno hx hP
  obtain ⟨d2, p2, ⟨_, s2e⟩, ag2, _⟩ := pick12 F q1 q2 D.cardM
  obtain ⟨d3, p3, _, ag3, e3x⟩ := pick12 F q1 q2 D.cardN
  obtain ⟨d1, ⟨q1', s1e⟩, ag1⟩ := F.pick D.cardA
  refine glue4_tri hl D hv hP0 hx0 hu0 hw0 q1' (hl.sub _ p2) (hl.sub _ p3) hP0 (s1e.trans s2e.symm)
    (hl.sameVar hv p2 p3) (var_of_reads e3x hx) (Or.inr ⟨rfl, p2, p3⟩) agr_refl'
    (agr_or ag3 (fun _ => var_of_reads e3x hx)) (agr_or ag2 (vfix4 hl hv F q1 q2 p2))
    (agr_or ag1 (fun iw => absurd iw hno))

/-- **Dos testigos**: no se lee `s1` ni `s3`. El lado izquierdo sale de las caras del testigo del paso de `s1`, el
derecho de las del paso de `s3`, y se pegan en `v = s2`. -/
theorem c4s2_none (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M Nn C) (hv : stepVar φ σ = some s2)
    (hS : PhStruct φ P0 N R Tf) (hN : midFusion φ < N) {x u w : PathNodeId} (t : Tri R Tf x u w)
    (hno1 : ¬ InW φ x.id.step u.id.step w.id.step s1) (hno3 : ¬ InW φ x.id.step u.id.step w.id.step s3)
    (hP1 : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s1 → TriOf φ P x' u' w')
    (hP3 : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s3 → TriOf φ P x' u' w') :
    TriOf φ P x u w := by
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨f1, f2, f3, F⟩ := faces_P hS t hx0 hu0 hw0 (lam := varStep s1) (by simp only [varStep]; omega)
    (by have := D.s1v; simp only [varStep, midFusion] at hN ⊢; omega) (stepVar_var D.s1v) hno1 hP1
  obtain ⟨h1, h2, h3, H⟩ := faces_P hS t hx0 hu0 hw0 (lam := varStep s3) (by simp only [varStep]; omega)
    (by have := D.s3v; simp only [varStep, midFusion] at hN ⊢; omega) (stepVar_var D.s3v) hno3 hP3
  obtain ⟨d1, ⟨q1, s1e⟩, ag1⟩ := F.pick D.cardA
  obtain ⟨d2, ⟨q2, s2e⟩, ag2⟩ := F.pick (no3_of_le1 D.cardM)
  obtain ⟨d3, ⟨q3, s3e⟩, ag3⟩ := H.pick (no3_of_le1 D.cardN)
  obtain ⟨d4, ⟨q4, s4e⟩, ag4⟩ := H.pick D.cardC
  refine glue4_tri hl D hv hP0 hx0 hu0 hw0 (hl.sub _ q1) (hl.sub _ q2) (hl.sub _ q3) (hl.sub _ q4)
    (s1e.trans s2e.symm) (hl.sameVar hv q2 q3) (s3e.trans s4e.symm) (Or.inr ⟨rfl, q2, q3⟩) ag4
    (agr_or ag3 (fun iw => absurd iw hno3)) (agr_or ag2 (vfix4 hl hv F F.q1.1 F.q2.1 q2))
    (agr_or ag1 (fun iw => absurd iw hno1))

/-- **Cuatro bloques, `v = s2`**: sin familias fantasma, con cualquier numeración. -/
theorem phantomFree_chain4_s2 (hl : LocPair φ P0 P σ) (D : Chain4Data φ s1 s2 s3 A M Nn C)
    (hv : stepVar φ σ = some s2) (hσ0 : 0 ≤ σ) (hσN : σ < N) (hN : midFusion φ < N) : PhantomFree φ P0 P N σ := by
  refine phantomFree_of_descent hσ0 hσN
    (fun x u w => rk4 (InW φ x.id.step u.id.step w.id.step s1) (InW φ x.id.step u.id.step w.id.step s3))
    (fun R Tf hS hanch x u w t ih => ?_)
  have r0 : ∀ {x' u' w' : PathNodeId}, InW φ x'.id.step u'.id.step w'.id.step s1 →
      InW φ x'.id.step u'.id.step w'.id.step s3 →
      rk4 (InW φ x'.id.step u'.id.step w'.id.step s1) (InW φ x'.id.step u'.id.step w'.id.step s3) = 0 :=
    fun a b => rk4_pq a b
  by_cases h1 : InW φ x.id.step u.id.step w.id.step s1
  · by_cases h3 : InW φ x.id.step u.id.step w.id.step s3
    · exact c4s2_both hl D hv hS hanch hσ0 hσN t h1 h3
    · -- solo `s1`: el nodo que lo lee al primer sitio
      refine of_reads_first hS (H := fun x u w => ¬ InW φ x.id.step u.id.step w.id.step s3)
        (fun _ _ _ h => not_inW_swap12 h) (fun _ _ _ h => not_inW_swap23 h)
        (fun x' u' w' t' h' hx' => c4s2_one hl D hv hS hN t' hx' h' (fun a b c t'' p q => ih a b c t'' (by
          rw [r0 p q, rk4_1 h1 h3]; omega))) x u w t h3 h1
  · by_cases h3 : InW φ x.id.step u.id.step w.id.step s3
    · refine of_reads_first hS (H := fun x u w => ¬ InW φ x.id.step u.id.step w.id.step s1)
        (fun _ _ _ h => not_inW_swap12 h) (fun _ _ _ h => not_inW_swap23 h)
        (fun x' u' w' t' h' hx' => c4s2_three hl D hv hS hN t' hx' h' (fun a b c t'' p q => ih a b c t'' (by
          rw [r0 q p, rk4_2 h1 h3]; omega))) x u w t h1 h3
    · refine c4s2_none hl D hv hS hN t h1 h3 (fun a b c t'' p => ih a b c t'' ?_) (fun a b c t'' q => ih a b c t'' ?_)
      · have := rk4_p (q := InW φ a.id.step b.id.step c.id.step s3) p
        rw [rk4_3 h1 h3]; omega
      · have := rk4_q (p := InW φ a.id.step b.id.step c.id.step s1) q
        rw [rk4_3 h1 h3]; omega

end CaseS2

end GPathB

end AbsSatBingo.Model
