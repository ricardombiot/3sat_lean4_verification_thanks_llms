-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain.lean
import AbsSatBingo.Model.ForbidOnLocal

/-!
# Tres bloques en cadena

`ForbidOnSep` cierra dos bloques que comparten una variable con un testigo de la regla (el del paso de la variable
compartida). Aquí la cadena tiene tres bloques, `A ∪ {s1}`, `{s1} ∪ M ∪ {s2}` y `{s2} ∪ C`, y hacen falta **dos
testigos encadenados**: el argumento sube por niveles, y en cada nivel los triángulos tienen fijada una variable
compartida más.

Con la variable fijada `v` en el último bloque (o `v = s2`):

1. los triángulos con un nodo que lee `s2` son de ramas de `P` (`tri_lam_any`, o el ancla si `v = s2`);
2. los que tienen un nodo que lee `s1` (`chain_mid`): el testigo en el paso de `s2` da tres ramas del nivel 1; el
   bloque de en medio toma la suya de las dos que pasan por el nodo de `s1`, y el último, de cualquiera;
3. todos (`chain_far`): el testigo en el paso de `s1` da tres ramas del nivel 2. El primer bloque toma una. Para el
   resto, o una sola rama sirve, o las ventanas del triángulo ya fijan `s2`, y entonces el bloque de en medio y el
   último eligen rama por separado.

Con `v` en el bloque de en medio (`chain_both`, `chain_near`, `chain_allmid`) los niveles son: los triángulos con
nodos en los pasos de `s1` y de `s2`; los que tienen uno en el de `s2`; todos.

En todos los niveles la rama final es `glue3` (una fuente por bloque) y es de `P` por `ForbidOnLocal`
(`glue3_P`): basta que dos fuentes vecinas lean igual la variable que comparten.

**`ChainData φ v s1 s2 A M C`** es lo que se pide a la fórmula alrededor de `v`; **`Chain3 φ`**: cada variable tiene
datos de cadena o de separador (`SepData`). Resultado, sin hipótesis sobre la máquina y con cualquier numeración de
las variables:

  `spineVerdictOn_iff_of_chain3`, `machineExact_of_chain3`, `reader_on_chain3`,

y `machineExact_threeChain` para `(x0 ∨ x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ x4) ∧ (¬x4 ∨ x5 ∨ x6)`.

El método se acaba aquí: con cuatro bloques, tras fijar una variable compartida queda a un lado una cadena de dos
bloques con variables fijadas por las tres ventanas, y haría falta un testigo vecino de cuatro nodos.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

-- ============================================================
-- Tres ramas por las caras de un tetraedro
-- ============================================================

/-- `z` es una variable que lee alguna de las tres ventanas. -/
def InW (φ : Cnf) (i j l : Int) (z : Nat) : Prop :=
  ∃ k k', (k = i ∨ k = j ∨ k = l) ∧ InWin k k' ∧ stepVar φ k' = some z

/-- `c` coincide con `a0` en las variables de `M` que leen las tres ventanas. -/
def Agr (φ : Cnf) (i j l : Int) (M : Nat → Prop) (c a0 : Assign) : Prop :=
  ∀ z, M z → InW φ i j l z → c z = a0 z

theorem agr_refl {i j l : Int} {M : Nat → Prop} {a0 : Assign} : Agr φ i j l M a0 a0 := fun _ _ _ => rfl

theorem patch_self (B : Nat → Prop) (a : Assign) : patch B a a = a := by
  funext z
  by_cases h : B z
  · exact patch_in h
  · exact patch_out h

/-- Tres ramas con la propiedad `Q`: `c1` pasa por las ventanas `i`, `j` de `a0`; `c2` por `i`, `l`; `c3` por `j`,
`l`. -/
structure Faces (φ : Cnf) (Q : Assign → Prop) (a0 c1 c2 c3 : Assign) (i j l : Int) : Prop where
  q1 : Q c1
  q2 : Q c2
  q3 : Q c3
  e1 : pidOfAssign φ c1 i = pidOfAssign φ a0 i
  e2 : pidOfAssign φ c2 i = pidOfAssign φ a0 i
  e3 : pidOfAssign φ c1 j = pidOfAssign φ a0 j
  e4 : pidOfAssign φ c3 j = pidOfAssign φ a0 j
  e5 : pidOfAssign φ c2 l = pidOfAssign φ a0 l
  e6 : pidOfAssign φ c3 l = pidOfAssign φ a0 l

section FacesLemmas

variable {Q : Assign → Prop} {a0 c1 c2 c3 : Assign} {i j l : Int}

/-- Una variable de las ventanas la lee como `a0` alguna de las dos primeras ramas. -/
theorem Faces.inw (F : Faces φ Q a0 c1 c2 c3 i j l) {z : Nat} (h : InW φ i j l z) : c1 z = a0 z ∨ c2 z = a0 z := by
  obtain ⟨k, k', hk, hw, hz⟩ := h
  rcases hk with e | e | e
  · exact Or.inl (var_of_pid_eq F.e1 (by rw [← e]; exact hw) hz)
  · exact Or.inl (var_of_pid_eq F.e3 (by rw [← e]; exact hw) hz)
  · exact Or.inr (var_of_pid_eq F.e5 (by rw [← e]; exact hw) hz)

/-- **La cuenta**: o una de las tres ramas coincide con `a0` en todas las variables de `M` de las ventanas, o las
ventanas leen tres variables distintas de `M`. -/
theorem Faces.pick' (F : Faces φ Q a0 c1 c2 c3 i j l) (M : Nat → Prop) :
    (∃ c, Q c ∧ Agr φ i j l M c a0) ∨
      ∃ z1 z2 z3, M z1 ∧ M z2 ∧ M z3 ∧ z1 ≠ z2 ∧ z1 ≠ z3 ∧ z2 ≠ z3 ∧ InW φ i j l z1 ∧ InW φ i j l z2 ∧
        InW φ i j l z3 := by
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
  -- `z2` está en la ventana `j` (donde `c2` no pasa), `z3` en la `i`
  have a12 : c1 z2 = a0 z2 := by
    obtain ⟨k, k', hk, hw, hz⟩ := w2
    rcases hk with e | e | e
    · exact absurd (var_of_pid_eq F.e2 (by rw [← e]; exact hw) hz) n2
    · exact var_of_pid_eq F.e3 (by rw [← e]; exact hw) hz
    · exact absurd (var_of_pid_eq F.e5 (by rw [← e]; exact hw) hz) n2
  have a3 : c1 z3 = a0 z3 ∧ c2 z3 = a0 z3 := by
    obtain ⟨k, k', hk, hw, hz⟩ := w3
    rcases hk with e | e | e
    · exact ⟨var_of_pid_eq F.e1 (by rw [← e]; exact hw) hz, var_of_pid_eq F.e2 (by rw [← e]; exact hw) hz⟩
    · exact absurd (var_of_pid_eq F.e4 (by rw [← e]; exact hw) hz) n3
    · exact absurd (var_of_pid_eq F.e6 (by rw [← e]; exact hw) hz) n3
  exact ⟨z1, z2, z3, m1, m2, m3, fun e => n1 (by rw [e]; exact a12), fun e => n1 (by rw [e]; exact a3.1),
    fun e => n2 (by rw [e]; exact a3.2), w1, w2, w3⟩

theorem Faces.pick (F : Faces φ Q a0 c1 c2 c3 i j l) {M : Nat → Prop}
    (hM : ∀ z1 z2 z3, M z1 → M z2 → M z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False) :
    ∃ c, Q c ∧ Agr φ i j l M c a0 := by
  rcases F.pick' M with h | ⟨z1, z2, z3, m1, m2, m3, d12, d13, d23, _⟩
  · exact h
  · exact absurd (hM z1 z2 z3 m1 m2 m3 d12 d13 d23) (fun h => h)

/-- Con una sola variable en `M`, basta elegir entre las dos ramas que pasan por la ventana `i`. -/
theorem Faces.pick2 (F : Faces φ Q a0 c1 c2 c3 i j l) {M : Nat → Prop} (hM : ∀ z1 z2, M z1 → M z2 → z1 = z2) :
    Agr φ i j l M c1 a0 ∨ Agr φ i j l M c2 a0 := by
  by_cases h1 : ∃ z, M z ∧ InW φ i j l z ∧ c1 z ≠ a0 z
  · by_cases h2 : ∃ z, M z ∧ InW φ i j l z ∧ c2 z ≠ a0 z
    · exfalso
      obtain ⟨z1, m1, _, n1⟩ := h1
      obtain ⟨z2, m2, w2, n2⟩ := h2
      have a12 : c1 z2 = a0 z2 := by
        obtain ⟨k, k', hk, hw, hz⟩ := w2
        rcases hk with e | e | e
        · exact absurd (var_of_pid_eq F.e2 (by rw [← e]; exact hw) hz) n2
        · exact var_of_pid_eq F.e3 (by rw [← e]; exact hw) hz
        · exact absurd (var_of_pid_eq F.e5 (by rw [← e]; exact hw) hz) n2
      exact n1 (by rw [hM z1 z2 m1 m2]; exact a12)
    · right
      intro z hm hw
      by_cases he : c2 z = a0 z
      · exact he
      · exact absurd ⟨z, hm, hw, he⟩ h2
  · left
    intro z hm hw
    by_cases he : c1 z = a0 z
    · exact he
    · exact absurd ⟨z, hm, hw, he⟩ h1

end FacesLemmas

-- ============================================================
-- La cadena de tres bloques y la rama de tres fuentes
-- ============================================================

/-- **Una fuente por bloque**: `d'` en `C`, `d` en `M ∪ {s2}`, `dA` en `A ∪ {s1}` y `a0` en lo demás. -/
noncomputable def glue3 (s1 s2 : Nat) (A M C : Nat → Prop) (d' d dA a0 : Assign) : Assign :=
  patch C d' (patch (fun z => M z ∨ z = s2) d (patch (fun z => A z ∨ z = s1) dA a0))

theorem glue3_self (s1 s2 : Nat) (A M C : Nat → Prop) (d' a0 : Assign) :
    glue3 s1 s2 A M C d' a0 a0 a0 = patch C d' a0 := by
  unfold glue3
  rw [patch_self, patch_self]

theorem glue3_pid {s1 s2 : Nat} {A M C : Nat → Prop} {d' d dA a0 : Assign} {i j l k : Int}
    (hk : k = i ∨ k = j ∨ k = l) (hC : Agr φ i j l C d' a0) (hM : Agr φ i j l (fun z => M z ∨ z = s2) d a0)
    (hA : Agr φ i j l (fun z => A z ∨ z = s1) dA a0) :
    pidOfAssign φ (glue3 s1 s2 A M C d' d dA a0) k = pidOfAssign φ a0 k := by
  refine pid_of_agree (fun k' z hw hz => ?_)
  have iw : InW φ i j l z := ⟨k, k', hk, hw, hz⟩
  unfold glue3
  by_cases h1 : C z
  · rw [patch_in h1]; exact hC z h1 iw
  · rw [patch_out h1]
    by_cases h2 : M z ∨ z = s2
    · rw [patch_in (B := fun z => M z ∨ z = s2) h2]; exact hM z h2 iw
    · rw [patch_out (B := fun z => M z ∨ z = s2) h2]
      by_cases h3 : A z ∨ z = s1
      · rw [patch_in (B := fun z => A z ∨ z = s1) h3]; exact hA z h3 iw
      · exact patch_out (B := fun z => A z ∨ z = s1) h3

/-- **`ChainData φ v s1 s2 A M C`**: alrededor de la variable `v`, tres bloques en cadena: `A ∪ {s1}`,
`{s1} ∪ M ∪ {s2}` y `{s2} ∪ C`. Cada cláusula está entera fuera o entera en un bloque; `A` y `C` no tienen tres
variables distintas y `M` tiene a lo sumo una; `v` está en `C` (y entonces `C` tiene a lo sumo otra), o es `s2`, o
está en `M`. -/
structure ChainData (φ : Cnf) (v s1 s2 : Nat) (A M C : Nat → Prop) : Prop where
  s1v   : s1 < φ.nVars
  s2v   : s2 < φ.nVars
  ne12  : s1 ≠ s2
  nA1   : ¬ A s1
  nA2   : ¬ A s2
  nM1   : ¬ M s1
  nM2   : ¬ M s2
  nC1   : ¬ C s1
  nC2   : ¬ C s2
  dAM   : ∀ z, A z → M z → False
  dAC   : ∀ z, A z → C z → False
  dMC   : ∀ z, M z → C z → False
  cardA : ∀ z1 z2 z3, A z1 → A z2 → A z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False
  cardC : ∀ z1 z2 z3, C z1 → C z2 → C z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False
  cardM : ∀ z1 z2, M z1 → M z2 → z1 = z2
  pos   : (C v ∧ ∀ z1 z2, C z1 → C z2 → z1 ≠ v → z2 ≠ v → z1 = z2) ∨ v = s2 ∨ M v
  cl    : ∀ c ∈ φ.clauses,
    ((¬ (A c.l1.v ∨ M c.l1.v ∨ C c.l1.v ∨ c.l1.v = s1 ∨ c.l1.v = s2)) ∧
      (¬ (A c.l2.v ∨ M c.l2.v ∨ C c.l2.v ∨ c.l2.v = s1 ∨ c.l2.v = s2)) ∧
      (¬ (A c.l3.v ∨ M c.l3.v ∨ C c.l3.v ∨ c.l3.v = s1 ∨ c.l3.v = s2))) ∨
    ((A c.l1.v ∨ c.l1.v = s1) ∧ (A c.l2.v ∨ c.l2.v = s1) ∧ (A c.l3.v ∨ c.l3.v = s1)) ∨
    ((M c.l1.v ∨ c.l1.v = s1 ∨ c.l1.v = s2) ∧ (M c.l2.v ∨ c.l2.v = s1 ∨ c.l2.v = s2) ∧
      (M c.l3.v ∨ c.l3.v = s1 ∨ c.l3.v = s2)) ∨
    ((C c.l1.v ∨ c.l1.v = s2) ∧ (C c.l2.v ∨ c.l2.v = s2) ∧ (C c.l3.v ∨ c.l3.v = s2))

section Glue3

variable {v s1 s2 : Nat} {A M C : Nat → Prop} {d' d dA a0 : Assign}

theorem g3C {z : Nat} (h : C z) : glue3 s1 s2 A M C d' d dA a0 z = d' z := patch_in h

theorem g3M (D : ChainData φ v s1 s2 A M C) {z : Nat} (h : M z ∨ z = s2) :
    glue3 s1 s2 A M C d' d dA a0 z = d z := by
  have nc : ¬ C z := by
    rcases h with h | h
    · exact fun hc => D.dMC z h hc
    · rw [h]; exact D.nC2
  unfold glue3
  rw [patch_out nc]
  exact patch_in (B := fun z => M z ∨ z = s2) h

theorem g3A (D : ChainData φ v s1 s2 A M C) {z : Nat} (h : A z ∨ z = s1) :
    glue3 s1 s2 A M C d' d dA a0 z = dA z := by
  have nc : ¬ C z := by
    rcases h with h | h
    · exact fun hc => D.dAC z h hc
    · rw [h]; exact D.nC1
  have nm : ¬ (M z ∨ z = s2) := by
    rcases h with h | h
    · rintro (hm | hm)
      · exact D.dAM z h hm
      · rw [hm] at h; exact D.nA2 h
    · rintro (hm | hm)
      · rw [h] at hm; exact D.nM1 hm
      · rw [h] at hm; exact D.ne12 hm
  unfold glue3
  rw [patch_out nc, patch_out (B := fun z => M z ∨ z = s2) nm]
  exact patch_in (B := fun z => A z ∨ z = s1) h

theorem g3O {z : Nat} (h : ¬ (A z ∨ M z ∨ C z ∨ z = s1 ∨ z = s2)) : glue3 s1 s2 A M C d' d dA a0 z = a0 z := by
  unfold glue3
  rw [patch_out (fun hc => h (Or.inr (Or.inr (Or.inl hc)))),
    patch_out (B := fun z => M z ∨ z = s2)
      (fun hm => h (hm.elim (fun m => Or.inr (Or.inl m)) (fun e => Or.inr (Or.inr (Or.inr (Or.inr e))))))]
  exact patch_out (B := fun z => A z ∨ z = s1)
    (fun ha => h (ha.elim Or.inl (fun e => Or.inr (Or.inr (Or.inr (Or.inl e))))))

theorem g3TM (D : ChainData φ v s1 s2 A M C) (e1 : dA s1 = d s1) {z : Nat} (h : M z ∨ z = s1 ∨ z = s2) :
    glue3 s1 s2 A M C d' d dA a0 z = d z := by
  rcases h with h | h | h
  · exact g3M D (Or.inl h)
  · rw [g3A D (Or.inr h), h]; exact e1
  · exact g3M D (Or.inr h)

theorem g3TC (D : ChainData φ v s1 s2 A M C) (e2 : d s2 = d' s2) {z : Nat} (h : C z ∨ z = s2) :
    glue3 s1 s2 A M C d' d dA a0 z = d' z := by
  rcases h with h | h
  · exact g3C h
  · rw [g3M D (Or.inr h), h]; exact e2

variable {P0 P : Assign → Prop} {σ : Int}

/-- **La rama de tres fuentes es de `P0`** si dos fuentes vecinas leen igual la variable que comparten. -/
theorem glue3_P0 (hl : LocPair φ P0 P σ) (D : ChainData φ v s1 s2 A M C) (h0 : P0 a0) (hA : P0 dA) (hd : P0 d)
    (hd' : P0 d') (e1 : dA s1 = d s1) (e2 : d s2 = d' s2) : P0 (glue3 s1 s2 A M C d' d dA a0) := by
  refine p0_of_sources hl ⟨a0, h0⟩ (fun z => ?_) (fun cl hcl => ?_)
  · by_cases h1 : C z
    · exact ⟨d', hd', g3C h1⟩
    · by_cases h2 : M z ∨ z = s2
      · exact ⟨d, hd, g3M D h2⟩
      · by_cases h3 : A z ∨ z = s1
        · exact ⟨dA, hA, g3A D h3⟩
        · refine ⟨a0, h0, g3O ?_⟩
          rintro (h | h | h | h | h)
          · exact h3 (Or.inl h)
          · exact h2 (Or.inl h)
          · exact h1 h
          · exact h3 (Or.inr h)
          · exact h2 (Or.inr h)
  · rcases D.cl cl hcl with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩
    · exact ⟨a0, h0, g3O o1, g3O o2, g3O o3⟩
    · exact ⟨dA, hA, g3A D i1, g3A D i2, g3A D i3⟩
    · exact ⟨d, hd, g3TM D e1 i1, g3TM D e1 i2, g3TM D e1 i3⟩
    · exact ⟨d', hd', g3TC D e2 i1, g3TC D e2 i2, g3TC D e2 i3⟩

/-- **Y de `P`**, si la fuente del bloque de `v` (o las dos de los bloques de `s2`, si `v = s2`) es de `P`. -/
theorem glue3_P (hl : LocPair φ P0 P σ) (D : ChainData φ v s1 s2 A M C) (hv : stepVar φ σ = some v) (h0 : P0 a0)
    (hA : P0 dA) (hd : P0 d) (hd' : P0 d') (e1 : dA s1 = d s1) (e2 : d s2 = d' s2) (hpC : C v → P d')
    (hpS : v = s2 → P d ∧ P d') (hpM : M v → P d) : P (glue3 s1 s2 A M C d' d dA a0) := by
  refine p_of_sources hl (glue3_P0 hl D h0 hA hd hd' e1 e2) (fun h => by rw [hv] at h; cases h) (fun z hz => ?_)
  rw [hv] at hz; cases hz
  refine ⟨?_, fun cl hcl hcv => ?_⟩
  · rcases D.pos with ⟨hc, _⟩ | hs | hm
    · exact ⟨d', hpC hc, g3C hc⟩
    · exact ⟨d, (hpS hs).1, g3M D (Or.inr hs)⟩
    · exact ⟨d, hpM hm, g3M D (Or.inl hm)⟩
  · have tv : ∀ {Q : Nat → Prop}, Q cl.l1.v → Q cl.l2.v → Q cl.l3.v → Q v := by
      intro Q a b c
      rcases hcv with e | e | e
      · rw [e]; exact a
      · rw [e]; exact b
      · rw [e]; exact c
    rcases D.cl cl hcl with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩
    · exfalso
      have hno := tv (Q := fun z => ¬ (A z ∨ M z ∨ C z ∨ z = s1 ∨ z = s2)) o1 o2 o3
      rcases D.pos with ⟨hc, _⟩ | hs | hm
      · exact hno (Or.inr (Or.inr (Or.inl hc)))
      · exact hno (Or.inr (Or.inr (Or.inr (Or.inr hs))))
      · exact hno (Or.inr (Or.inl hm))
    · exfalso
      have hta := tv (Q := fun z => A z ∨ z = s1) i1 i2 i3
      rcases D.pos with ⟨hc, _⟩ | hs | hm
      · rcases hta with h | h
        · exact D.dAC v h hc
        · rw [h] at hc; exact D.nC1 hc
      · rcases hta with h | h
        · rw [hs] at h; exact D.nA2 h
        · exact D.ne12 (h.symm.trans hs)
      · rcases hta with h | h
        · exact D.dAM v h hm
        · rw [h] at hm; exact D.nM1 hm
    · have hpd : P d := by
        have htm := tv (Q := fun z => M z ∨ z = s1 ∨ z = s2) i1 i2 i3
        rcases D.pos with ⟨hc, _⟩ | hs | hm
        · exfalso
          rcases htm with h | h | h
          · exact D.dMC v h hc
          · rw [h] at hc; exact D.nC1 hc
          · rw [h] at hc; exact D.nC2 hc
        · exact (hpS hs).1
        · exact hpM hm
      exact ⟨d, hpd, g3TM D e1 i1, g3TM D e1 i2, g3TM D e1 i3⟩
    · have hpd : P d' := by
        have htc := tv (Q := fun z => C z ∨ z = s2) i1 i2 i3
        rcases D.pos with ⟨hc, _⟩ | hs | hm
        · exact hpC hc
        · exact (hpS hs).2
        · exfalso
          rcases htc with h | h
          · exact D.dMC v hm h
          · rw [h] at hm; exact D.nM2 hm
      exact ⟨d', hpd, g3TC D e2 i1, g3TC D e2 i2, g3TC D e2 i3⟩

end Glue3

namespace GPathB

variable {P0 P : Assign → Prop} {N σ : Int} {R : PathNodeId → PathNodeId → Prop} {Tf : Trios}

-- ============================================================
-- Triángulos de una estructura
-- ============================================================

/-- Un triángulo sin prohibir de la estructura. -/
structure Tri (R : PathNodeId → PathNodeId → Prop) (Tf : Trios) (x u w : PathNodeId) : Prop where
  xu  : R x u
  xw  : R x w
  uw  : R u w
  nxu : x ≠ u
  nxw : x ≠ w
  nuw : u ≠ w
  nf  : ¬ Tf x u w

section TriLemmas

variable {x u w : PathNodeId}

theorem Tri.swap12 (hS : PhStruct φ P0 N R Tf) (t : Tri R Tf x u w) : Tri R Tf u x w :=
  ⟨hS.symm _ _ t.xu, t.uw, t.xw, Ne.symm t.nxu, t.nuw, t.nxw,
    fun hf => t.nf (hS.sw12 u x w (hS.symm _ _ t.xu) t.uw t.xw hf)⟩

theorem Tri.swap23 (hS : PhStruct φ P0 N R Tf) (t : Tri R Tf x u w) : Tri R Tf x w u :=
  ⟨t.xw, t.xu, hS.symm _ _ t.uw, t.nxw, t.nxu, Ne.symm t.nuw,
    fun hf => t.nf (hS.sw23 x w u t.xw t.xu (hS.symm _ _ t.uw) hf)⟩

theorem TriOf.swap12 (h : TriOf φ P x u w) : TriOf φ P u x w := by
  obtain ⟨a, ha, h1, h2, h3⟩ := h
  exact ⟨a, ha, h2, h1, h3⟩

theorem TriOf.swap23 (h : TriOf φ P x u w) : TriOf φ P x w u := by
  obtain ⟨a, ha, h1, h2, h3⟩ := h
  exact ⟨a, ha, h1, h3, h2⟩

theorem Tri.b3 (hS : PhStruct φ P0 N R Tf) (t : Tri R Tf x u w) : TriOf φ P0 x u w :=
  hS.b3 x u w t.xu t.xw t.uw t.nxu t.nxw t.nuw t.nf

/-- El testigo del triángulo en un paso: o es uno de sus nodos, o forma tres caras sin prohibir. -/
theorem Tri.wit (hS : PhStruct φ P0 N R Tf) (t : Tri R Tf x u w) {lam : Int} (h0 : 0 ≤ lam) (hN : lam < N) :
    ∃ n, n.id.step = lam ∧ ((n = x ∨ n = u ∨ n = w) ∨ (Tri R Tf x u n ∧ Tri R Tf x w n ∧ Tri R Tf u w n)) := by
  obtain ⟨n, hns, hxn, hun, hwn, hor⟩ := hS.trio x u w t.xu t.xw t.uw t.nxu t.nxw t.nuw t.nf lam h0 hN
  refine ⟨n, hns, ?_⟩
  by_cases hnx : n = x
  · exact Or.inl (Or.inl hnx)
  by_cases hnu : n = u
  · exact Or.inl (Or.inr (Or.inl hnu))
  by_cases hnw : n = w
  · exact Or.inl (Or.inr (Or.inr hnw))
  obtain ⟨m1, m2, m3⟩ : ¬ Tf x u n ∧ ¬ Tf x w n ∧ ¬ Tf u w n := by
    rcases hor with h' | h' | h' | h'
    · exact absurd h' hnx
    · exact absurd h' hnu
    · exact absurd h' hnw
    · exact h'
  exact Or.inr ⟨⟨t.xu, hxn, hun, t.nxu, Ne.symm hnx, Ne.symm hnu, m1⟩,
    ⟨t.xw, hxn, hwn, t.nxw, Ne.symm hnx, Ne.symm hnw, m2⟩, ⟨t.uw, hun, hwn, t.nuw, Ne.symm hnu, Ne.symm hnw, m3⟩⟩

end TriLemmas

/-- Un enunciado para triángulos con su primer nodo en un paso vale con el nodo en cualquiera de los tres sitios. -/
theorem any_of_first (hS : PhStruct φ P0 N R Tf) {lam : Int}
    (base : ∀ x u w, Tri R Tf x u w → x.id.step = lam → TriOf φ P x u w) :
    ∀ x u w, Tri R Tf x u w → (x.id.step = lam ∨ u.id.step = lam ∨ w.id.step = lam) → TriOf φ P x u w := by
  intro x u w t hor
  rcases hor with h | h | h
  · exact base x u w t h
  · exact (base u x w (t.swap12 hS) h).swap12
  · exact ((base w x u ((t.swap23 hS).swap12 hS) h).swap12).swap23

-- ============================================================
-- La variable fijada en el último bloque, o es `s2`
-- ============================================================

section Levels

variable {v s1 s2 : Nat} {A M C : Nat → Prop}

/-- **Nivel 2**: los triángulos con un nodo que lee `s1`, desde los que tienen un nodo que lee `s2`. -/
theorem chain_mid (hl : LocPair φ P0 P σ) (D : ChainData φ v s1 s2 A M C) (hv : stepVar φ σ = some v)
    (hS : PhStruct φ P0 N R Tf) {lam1 lam2 : Int} (h20 : 0 ≤ lam2) (h2N : lam2 < N)
    (hs1 : stepVar φ lam1 = some s1) (hs2 : stepVar φ lam2 = some s2)
    (hA2 : ∀ x u w, Tri R Tf x u w → (x.id.step = lam2 ∨ u.id.step = lam2 ∨ w.id.step = lam2) → TriOf φ P x u w) :
    ∀ x u w, Tri R Tf x u w → x.id.step = lam1 → TriOf φ P x u w := by
  intro x u w t hx
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨n, hns, hn⟩ := t.wit hS h20 h2N
  rcases hn with hn | ⟨t1, t2, t3⟩
  · refine hA2 x u w t ?_
    rcases hn with e | e | e
    · exact Or.inl (by rw [← e]; exact hns)
    · exact Or.inr (Or.inl (by rw [← e]; exact hns))
    · exact Or.inr (Or.inr (by rw [← e]; exact hns))
  obtain ⟨c1, q1, c1x, c1u, c1n⟩ := hA2 x u n t1 (Or.inr (Or.inr hns))
  obtain ⟨c2, q2, c2x, c2w, c2n⟩ := hA2 x w n t2 (Or.inr (Or.inr hns))
  obtain ⟨c3, q3, c3u, c3w, c3n⟩ := hA2 u w n t3 (Or.inr (Or.inr hns))
  have s21 : c2 s2 = c1 s2 := var_of_pid_eq (c2n.trans c1n.symm) (Or.inl rfl) (by rw [hns]; exact hs2)
  have s31 : c3 s2 = c1 s2 := var_of_pid_eq (c3n.trans c1n.symm) (Or.inl rfl) (by rw [hns]; exact hs2)
  have F : Faces φ (fun c => P c ∧ c s2 = c1 s2) a0 c1 c2 c3 x.id.step u.id.step w.id.step :=
    ⟨⟨q1, rfl⟩, ⟨q2, s21⟩, ⟨q3, s31⟩, c1x.trans hx0.symm, c2x.trans hx0.symm, c1u.trans hu0.symm,
      c3u.trans hu0.symm, c2w.trans hw0.symm, c3w.trans hw0.symm⟩
  have fix2 : InW φ x.id.step u.id.step w.id.step s2 → c1 s2 = a0 s2 := by
    intro iw
    rcases F.inw iw with h | h
    · exact h
    · exact s21.symm.trans h
  have hxs1 : stepVar φ x.id.step = some s1 := by rw [hx]; exact hs1
  obtain ⟨cM, qM, sM2, sM1, aM⟩ : ∃ c, P c ∧ c s2 = c1 s2 ∧ c s1 = a0 s1 ∧
      Agr φ x.id.step u.id.step w.id.step M c a0 := by
    rcases F.pick2 D.cardM with g | g
    · exact ⟨c1, q1, rfl, var_of_pid_eq F.e1 (Or.inl rfl) hxs1, g⟩
    · exact ⟨c2, q2, s21, var_of_pid_eq F.e2 (Or.inl rfl) hxs1, g⟩
  obtain ⟨cC, ⟨qC, sC⟩, aC⟩ := F.pick D.cardC
  have hMs : Agr φ x.id.step u.id.step w.id.step (fun z => M z ∨ z = s2) cM a0 := by
    intro z hz iw
    rcases hz with h | h
    · exact aM z h iw
    · rw [h] at iw ⊢; exact sM2.trans (fix2 iw)
  exact ⟨glue3 s1 s2 A M C cC cM a0 a0,
    glue3_P hl D hv hP0 hP0 (hl.sub _ qM) (hl.sub _ qC) sM1.symm (sM2.trans sC.symm) (fun _ => qC)
      (fun _ => ⟨qM, qC⟩) (fun _ => qM),
    (glue3_pid (Or.inl rfl) aC hMs agr_refl).trans hx0, (glue3_pid (Or.inr (Or.inl rfl)) aC hMs agr_refl).trans hu0,
    (glue3_pid (Or.inr (Or.inr rfl)) aC hMs agr_refl).trans hw0⟩

/-- **Nivel 3**: todos los triángulos, desde los que tienen un nodo que lee `s1`. -/
theorem chain_far (hl : LocPair φ P0 P σ) (D : ChainData φ v s1 s2 A M C) (hv : stepVar φ σ = some v)
    (hS : PhStruct φ P0 N R Tf)
    (hc : (C v ∧ ∀ z1 z2, C z1 → C z2 → z1 ≠ v → z2 ≠ v → z1 = z2) ∨ v = s2) {lam1 : Int} (h10 : 0 ≤ lam1)
    (h1N : lam1 < N) (hs1 : stepVar φ lam1 = some s1)
    (hB : ∀ x u w, Tri R Tf x u w → (x.id.step = lam1 ∨ u.id.step = lam1 ∨ w.id.step = lam1) → TriOf φ P x u w) :
    ∀ x u w, Tri R Tf x u w → TriOf φ P x u w := by
  intro x u w t
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨n, hns, hn⟩ := t.wit hS h10 h1N
  rcases hn with hn | ⟨t1, t2, t3⟩
  · refine hB x u w t ?_
    rcases hn with e | e | e
    · exact Or.inl (by rw [← e]; exact hns)
    · exact Or.inr (Or.inl (by rw [← e]; exact hns))
    · exact Or.inr (Or.inr (by rw [← e]; exact hns))
  obtain ⟨d1, q1, d1x, d1u, d1n⟩ := hB x u n t1 (Or.inr (Or.inr hns))
  obtain ⟨d2, q2, d2x, d2w, d2n⟩ := hB x w n t2 (Or.inr (Or.inr hns))
  obtain ⟨d3, q3, d3u, d3w, d3n⟩ := hB u w n t3 (Or.inr (Or.inr hns))
  have s21 : d2 s1 = d1 s1 := var_of_pid_eq (d2n.trans d1n.symm) (Or.inl rfl) (by rw [hns]; exact hs1)
  have s31 : d3 s1 = d1 s1 := var_of_pid_eq (d3n.trans d1n.symm) (Or.inl rfl) (by rw [hns]; exact hs1)
  have F : Faces φ (fun c => P c ∧ c s1 = d1 s1) a0 d1 d2 d3 x.id.step u.id.step w.id.step :=
    ⟨⟨q1, rfl⟩, ⟨q2, s21⟩, ⟨q3, s31⟩, d1x.trans hx0.symm, d2x.trans hx0.symm, d1u.trans hu0.symm,
      d3u.trans hu0.symm, d2w.trans hw0.symm, d3w.trans hw0.symm⟩
  have fix1 : InW φ x.id.step u.id.step w.id.step s1 → d1 s1 = a0 s1 := by
    intro iw
    rcases F.inw iw with h | h
    · exact h
    · exact s21.symm.trans h
  have vfix : InW φ x.id.step u.id.step w.id.step v → ∀ c, P c → c v = a0 v := by
    intro iw c hc'
    rcases F.inw iw with h | h
    · exact (hl.sameVar hv hc' q1).trans h
    · exact (hl.sameVar hv hc' q2).trans h
  obtain ⟨dA, ⟨qA, sA⟩, aA⟩ := F.pick D.cardA
  have hAs : Agr φ x.id.step u.id.step w.id.step (fun z => A z ∨ z = s1) dA a0 := by
    intro z hz iw
    rcases hz with h | h
    · exact aA z h iw
    · rw [h] at iw ⊢; exact sA.trans (fix1 iw)
  -- la rama final, dadas las fuentes
  have fin : ∀ d' d : Assign, P d' → P d → d s1 = d1 s1 → d s2 = d' s2 →
      Agr φ x.id.step u.id.step w.id.step C d' a0 →
      Agr φ x.id.step u.id.step w.id.step (fun z => M z ∨ z = s2) d a0 → TriOf φ P x u w := by
    intro d' d qd' qd sd e2 hC hM
    exact ⟨glue3 s1 s2 A M C d' d dA a0,
      glue3_P hl D hv hP0 (hl.sub _ qA) (hl.sub _ qd) (hl.sub _ qd') (sA.trans sd.symm) e2 (fun _ => qd')
        (fun _ => ⟨qd, qd'⟩) (fun _ => qd),
      (glue3_pid (Or.inl rfl) hC hM hAs).trans hx0, (glue3_pid (Or.inr (Or.inl rfl)) hC hM hAs).trans hu0,
      (glue3_pid (Or.inr (Or.inr rfl)) hC hM hAs).trans hw0⟩
  rcases F.pick' (fun z => (M z ∨ z = s2 ∨ C z) ∧ z ≠ v) with
    ⟨d, ⟨qd, sd⟩, ad⟩ | ⟨z1, z2, z3, m1, m2, m3, d12, d13, d23, w1, w2, w3⟩
  · -- una sola rama para el bloque de en medio y el último
    refine fin d d qd qd sd rfl (fun z hz iw => ?_) (fun z hz iw => ?_)
    · by_cases e : z = v
      · rw [e] at iw ⊢; exact vfix iw d qd
      · exact ad z ⟨Or.inr (Or.inr hz), e⟩ iw
    · by_cases e : z = v
      · rw [e] at iw ⊢; exact vfix iw d qd
      · exact ad z ⟨hz.elim Or.inl (fun h => Or.inr (Or.inl h)), e⟩ iw
  · rcases hc with ⟨_, huniq⟩ | hvs
    · -- las ventanas leen `s2`
      have hs2w : InW φ x.id.step u.id.step w.id.step s2 := by
        by_cases a1 : z1 = s2
        · rw [← a1]; exact w1
        by_cases a2 : z2 = s2
        · rw [← a2]; exact w2
        by_cases a3 : z3 = s2
        · rw [← a3]; exact w3
        exfalso
        have cls : ∀ z, ((M z ∨ z = s2 ∨ C z) ∧ z ≠ v) → z ≠ s2 → M z ∨ (C z ∧ z ≠ v) := by
          rintro z ⟨h | h | h, hne⟩ hs
          · exact Or.inl h
          · exact absurd h hs
          · exact Or.inr ⟨h, hne⟩
        rcases cls z1 m1 a1 with p1 | p1 <;> rcases cls z2 m2 a2 with p2 | p2 <;>
          rcases cls z3 m3 a3 with p3 | p3
        · exact d12 (D.cardM z1 z2 p1 p2)
        · exact d12 (D.cardM z1 z2 p1 p2)
        · exact d13 (D.cardM z1 z3 p1 p3)
        · exact d23 (huniq z2 z3 p2.1 p3.1 p2.2 p3.2)
        · exact d23 (D.cardM z2 z3 p2 p3)
        · exact d13 (huniq z1 z3 p1.1 p3.1 p1.2 p3.2)
        · exact d12 (huniq z1 z2 p1.1 p2.1 p1.2 p2.2)
        · exact d12 (huniq z1 z2 p1.1 p2.1 p1.2 p2.2)
      obtain ⟨d, ⟨qd, sd⟩, ad⟩ := F.pick (M := fun z => M z ∨ z = s2) (by
        intro y1 y2 y3 b1 b2 b3 e12 e13 e23
        rcases b1 with b1 | b1 <;> rcases b2 with b2 | b2 <;> rcases b3 with b3 | b3
        · exact e12 (D.cardM y1 y2 b1 b2)
        · exact e12 (D.cardM y1 y2 b1 b2)
        · exact e13 (D.cardM y1 y3 b1 b3)
        · exact e23 (b2.trans b3.symm)
        · exact e23 (D.cardM y2 y3 b2 b3)
        · exact e13 (b1.trans b3.symm)
        · exact e12 (b1.trans b2.symm)
        · exact e12 (b1.trans b2.symm))
      obtain ⟨d', ⟨qd', _⟩, ad'⟩ := F.pick (M := fun z => (C z ∧ z ≠ v) ∨ z = s2) (by
        intro y1 y2 y3 b1 b2 b3 e12 e13 e23
        rcases b1 with b1 | b1 <;> rcases b2 with b2 | b2 <;> rcases b3 with b3 | b3
        · exact e12 (huniq y1 y2 b1.1 b2.1 b1.2 b2.2)
        · exact e12 (huniq y1 y2 b1.1 b2.1 b1.2 b2.2)
        · exact e13 (huniq y1 y3 b1.1 b3.1 b1.2 b3.2)
        · exact e23 (b2.trans b3.symm)
        · exact e23 (huniq y2 y3 b2.1 b3.1 b2.2 b3.2)
        · exact e13 (b1.trans b3.symm)
        · exact e12 (b1.trans b2.symm)
        · exact e12 (b1.trans b2.symm))
      refine fin d' d qd' qd sd ((ad s2 (Or.inr rfl) hs2w).trans (ad' s2 (Or.inr rfl) hs2w).symm)
        (fun z hz iw => ?_) ad
      by_cases e : z = v
      · rw [e] at iw ⊢; exact vfix iw d' qd'
      · exact ad' z (Or.inl ⟨hz, e⟩) iw
    · -- `v = s2`: todas las ramas de `P` leen `s2` igual
      obtain ⟨d, ⟨qd, sd⟩, ad⟩ := F.pick (M := M) (fun y1 y2 _ b1 b2 _ e12 _ _ => e12 (D.cardM y1 y2 b1 b2))
      obtain ⟨d', ⟨qd', _⟩, ad'⟩ := F.pick D.cardC
      refine fin d' d qd' qd sd (by rw [← hvs]; exact hl.sameVar hv qd qd') ad' (fun z hz iw => ?_)
      rcases hz with h | h
      · exact ad z h iw
      · rw [h, ← hvs] at iw ⊢; exact vfix iw d qd

-- ============================================================
-- La variable fijada en el bloque de en medio
-- ============================================================

/-- **Nivel 1**: los triángulos con un nodo que lee `s2` y otro que lee `s1`. El testigo del paso `σ` da una rama de
`P` por los dos; solo cambia `v`. -/
theorem chain_both (hl : LocPair φ P0 P σ) (D : ChainData φ v s1 s2 A M C) (hv : stepVar φ σ = some v)
    (hS : PhStruct φ P0 N R Tf) (hMv : M v) (hσ0 : 0 ≤ σ) (hσN : σ < N)
    (hanch : ∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a) {lam1 lam2 : Int}
    (hs1 : stepVar φ lam1 = some s1) (hs2 : stepVar φ lam2 = some s2) :
    ∀ x u w, Tri R Tf x u w → x.id.step = lam2 → w.id.step = lam1 → TriOf φ P x u w := by
  intro x u w t hx hw
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨n, hns, hn⟩ := t.wit hS hσ0 hσN
  rcases hn with hn | ⟨t1, t2, _⟩
  · rcases hn with e | e | e
    · exact ⟨a0, hanch a0 n hP0 (by rw [e]; exact (hS.refl x u t.xu).1) hns (by rw [← hns, e]; exact hx0),
        hx0, hu0, hw0⟩
    · exact ⟨a0, hanch a0 n hP0 (by rw [e]; exact (hS.refl x u t.xu).2) hns (by rw [← hns, e]; exact hu0),
        hx0, hu0, hw0⟩
    · exact ⟨a0, hanch a0 n hP0 (by rw [e]; exact (hS.refl x w t.xw).2) hns (by rw [← hns, e]; exact hw0),
        hx0, hu0, hw0⟩
  have hRn := (hS.refl x n t1.xw).2
  obtain ⟨a1, hP1, hx1, hu1, hn1⟩ := t1.b3 hS
  obtain ⟨a2, hP2, hx2, hw2, hn2⟩ := t2.b3 hS
  have q1 : P a1 := hanch a1 n hP1 hRn hns (by rw [← hns]; exact hn1)
  have q2 : P a2 := hanch a2 n hP2 hRn hns (by rw [← hns]; exact hn2)
  have e1u := hu1.trans hu0.symm
  have e2x := hx2.trans hx0.symm
  have e2w := hw2.trans hw0.symm
  have a2s1 : a2 s1 = a0 s1 := var_of_pid_eq e2w (Or.inl rfl) (by rw [hw]; exact hs1)
  have a2s2 : a2 s2 = a0 s2 := var_of_pid_eq e2x (Or.inl rfl) (by rw [hx]; exact hs2)
  have hMs : Agr φ x.id.step u.id.step w.id.step (fun z => M z ∨ z = s2) a2 a0 := by
    intro z hz iw
    obtain ⟨k, k', hk, hwin, hzv⟩ := iw
    rcases hk with e | e | e
    · exact var_of_pid_eq e2x (by rw [← e]; exact hwin) hzv
    · rcases hz with h | h
      · have hzv' : z = v := D.cardM z v h hMv
        rw [hzv'] at hzv ⊢
        exact (hl.sameVar hv q2 q1).trans (var_of_pid_eq e1u (by rw [← e]; exact hwin) hzv)
      · rw [h]; exact a2s2
    · exact var_of_pid_eq e2w (by rw [← e]; exact hwin) hzv
  exact ⟨glue3 s1 s2 A M C a0 a2 a0 a0,
    glue3_P hl D hv hP0 hP0 (hl.sub _ q2) hP0 a2s1.symm a2s2 (fun hc => absurd hc (fun hc => D.dMC v hMv hc))
      (fun hs => absurd hMv (by rw [hs]; exact D.nM2)) (fun _ => q2),
    (glue3_pid (Or.inl rfl) agr_refl hMs agr_refl).trans hx0,
    (glue3_pid (Or.inr (Or.inl rfl)) agr_refl hMs agr_refl).trans hu0,
    (glue3_pid (Or.inr (Or.inr rfl)) agr_refl hMs agr_refl).trans hw0⟩

/-- **Nivel 2**: los triángulos con un nodo que lee `s2`. El testigo en el paso de `s1` da dos caras del nivel 1 y una
tercera que solo es de una rama de `P0`: basta, porque el primer bloque no contiene a `v`. -/
theorem chain_near (hl : LocPair φ P0 P σ) (D : ChainData φ v s1 s2 A M C) (hv : stepVar φ σ = some v)
    (hS : PhStruct φ P0 N R Tf) (hMv : M v) {lam1 lam2 : Int} (h10 : 0 ≤ lam1) (h1N : lam1 < N)
    (hs1 : stepVar φ lam1 = some s1) (hs2 : stepVar φ lam2 = some s2)
    (hA2 : ∀ x u w, Tri R Tf x u w → x.id.step = lam2 → w.id.step = lam1 → TriOf φ P x u w) :
    ∀ x u w, Tri R Tf x u w → x.id.step = lam2 → TriOf φ P x u w := by
  intro x u w t hx
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨n, hns, hn⟩ := t.wit hS h10 h1N
  rcases hn with hn | ⟨t1, t2, t3⟩
  · rcases hn with e | e | e
    · exfalso
      have h12 : lam1 = lam2 := by rw [← hns, e]; exact hx
      rw [h12, hs2] at hs1
      exact D.ne12 (Option.some.inj hs1).symm
    · exact (hA2 x w u (t.swap23 hS) hx (by rw [← e]; exact hns)).swap23
    · exact hA2 x u w t hx (by rw [← e]; exact hns)
  obtain ⟨c1, q1, c1x, c1u, c1n⟩ := hA2 x u n t1 hx hns
  obtain ⟨c2, q2, c2x, c2w, c2n⟩ := hA2 x w n t2 hx hns
  obtain ⟨c3, h3, c3u, c3w, c3n⟩ := t3.b3 hS
  have s21 : c2 s1 = c1 s1 := var_of_pid_eq (c2n.trans c1n.symm) (Or.inl rfl) (by rw [hns]; exact hs1)
  have s31 : c3 s1 = c1 s1 := var_of_pid_eq (c3n.trans c1n.symm) (Or.inl rfl) (by rw [hns]; exact hs1)
  have F : Faces φ (fun c => P0 c ∧ c s1 = c1 s1) a0 c1 c2 c3 x.id.step u.id.step w.id.step :=
    ⟨⟨hl.sub _ q1, rfl⟩, ⟨hl.sub _ q2, s21⟩, ⟨h3, s31⟩, c1x.trans hx0.symm, c2x.trans hx0.symm, c1u.trans hu0.symm,
      c3u.trans hu0.symm, c2w.trans hw0.symm, c3w.trans hw0.symm⟩
  obtain ⟨dA, ⟨hdA, sA⟩, aA⟩ := F.pick D.cardA
  have c1s2 : c1 s2 = a0 s2 := var_of_pid_eq F.e1 (Or.inl rfl) (by rw [hx]; exact hs2)
  have hAs : Agr φ x.id.step u.id.step w.id.step (fun z => A z ∨ z = s1) dA a0 := by
    intro z hz iw
    rcases hz with h | h
    · exact aA z h iw
    · rw [h] at iw ⊢
      rcases F.inw iw with h' | h'
      · exact sA.trans h'
      · exact sA.trans (s21.symm.trans h')
  have hMs : Agr φ x.id.step u.id.step w.id.step (fun z => M z ∨ z = s2) c1 a0 := by
    intro z hz iw
    rcases hz with h | h
    · have hzv : z = v := D.cardM z v h hMv
      rw [hzv] at iw ⊢
      rcases F.inw iw with h' | h'
      · exact h'
      · exact (hl.sameVar hv q1 q2).trans h'
    · rw [h]; exact c1s2
  exact ⟨glue3 s1 s2 A M C a0 c1 dA a0,
    glue3_P hl D hv hP0 hdA (hl.sub _ q1) hP0 sA c1s2 (fun hc => absurd hc (fun hc => D.dMC v hMv hc))
      (fun hs => absurd hMv (by rw [hs]; exact D.nM2)) (fun _ => q1),
    (glue3_pid (Or.inl rfl) agr_refl hMs hAs).trans hx0, (glue3_pid (Or.inr (Or.inl rfl)) agr_refl hMs hAs).trans hu0,
    (glue3_pid (Or.inr (Or.inr rfl)) agr_refl hMs hAs).trans hw0⟩

/-- **Nivel 3**: todos los triángulos, desde los que tienen un nodo que lee `s2`. O una sola rama sirve para el primer
bloque y `s1`, o las ventanas leen `s1`, y el primer bloque se queda como en `a0`. -/
theorem chain_allmid (hl : LocPair φ P0 P σ) (D : ChainData φ v s1 s2 A M C) (hv : stepVar φ σ = some v)
    (hS : PhStruct φ P0 N R Tf) (hMv : M v) {lam2 : Int} (h20 : 0 ≤ lam2) (h2N : lam2 < N)
    (hs2 : stepVar φ lam2 = some s2)
    (hA1 : ∀ x u w, Tri R Tf x u w → (x.id.step = lam2 ∨ u.id.step = lam2 ∨ w.id.step = lam2) → TriOf φ P x u w) :
    ∀ x u w, Tri R Tf x u w → TriOf φ P x u w := by
  intro x u w t
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨n, hns, hn⟩ := t.wit hS h20 h2N
  rcases hn with hn | ⟨t1, t2, t3⟩
  · refine hA1 x u w t ?_
    rcases hn with e | e | e
    · exact Or.inl (by rw [← e]; exact hns)
    · exact Or.inr (Or.inl (by rw [← e]; exact hns))
    · exact Or.inr (Or.inr (by rw [← e]; exact hns))
  obtain ⟨c1, q1, c1x, c1u, c1n⟩ := hA1 x u n t1 (Or.inr (Or.inr hns))
  obtain ⟨c2, q2, c2x, c2w, c2n⟩ := hA1 x w n t2 (Or.inr (Or.inr hns))
  obtain ⟨c3, q3, c3u, c3w, c3n⟩ := hA1 u w n t3 (Or.inr (Or.inr hns))
  have s21 : c2 s2 = c1 s2 := var_of_pid_eq (c2n.trans c1n.symm) (Or.inl rfl) (by rw [hns]; exact hs2)
  have s31 : c3 s2 = c1 s2 := var_of_pid_eq (c3n.trans c1n.symm) (Or.inl rfl) (by rw [hns]; exact hs2)
  have F : Faces φ (fun c => P c ∧ c s2 = c1 s2) a0 c1 c2 c3 x.id.step u.id.step w.id.step :=
    ⟨⟨q1, rfl⟩, ⟨q2, s21⟩, ⟨q3, s31⟩, c1x.trans hx0.symm, c2x.trans hx0.symm, c1u.trans hu0.symm,
      c3u.trans hu0.symm, c2w.trans hw0.symm, c3w.trans hw0.symm⟩
  have fix2 : InW φ x.id.step u.id.step w.id.step s2 → c1 s2 = a0 s2 := by
    intro iw
    rcases F.inw iw with h | h
    · exact h
    · exact s21.symm.trans h
  have vfix : InW φ x.id.step u.id.step w.id.step v → ∀ c, P c → c v = a0 v := by
    intro iw c hc'
    rcases F.inw iw with h | h
    · exact (hl.sameVar hv hc' q1).trans h
    · exact (hl.sameVar hv hc' q2).trans h
  obtain ⟨cC, ⟨qC, sC⟩, aC⟩ := F.pick D.cardC
  have hMof : ∀ d : Assign, P d → d s2 = c1 s2 →
      Agr φ x.id.step u.id.step w.id.step (fun z => M z ∨ z = s2) d a0 := by
    intro d qd sd z hz iw
    rcases hz with h | h
    · have hzv : z = v := D.cardM z v h hMv
      rw [hzv] at iw ⊢; exact vfix iw d qd
    · rw [h] at iw ⊢; exact sd.trans (fix2 iw)
  have fin : ∀ d dA : Assign, P d → d s2 = c1 s2 → P0 dA → dA s1 = d s1 →
      Agr φ x.id.step u.id.step w.id.step (fun z => A z ∨ z = s1) dA a0 → TriOf φ P x u w := by
    intro d dA qd sd hdA e1 hA
    exact ⟨glue3 s1 s2 A M C cC d dA a0,
      glue3_P hl D hv hP0 hdA (hl.sub _ qd) (hl.sub _ qC) e1 (sd.trans sC.symm) (fun _ => qC) (fun _ => ⟨qd, qC⟩)
        (fun _ => qd),
      (glue3_pid (Or.inl rfl) aC (hMof d qd sd) hA).trans hx0,
      (glue3_pid (Or.inr (Or.inl rfl)) aC (hMof d qd sd) hA).trans hu0,
      (glue3_pid (Or.inr (Or.inr rfl)) aC (hMof d qd sd) hA).trans hw0⟩
  rcases F.pick' (fun z => A z ∨ z = s1) with
    ⟨d, ⟨qd, sd⟩, ad⟩ | ⟨z1, z2, z3, m1, m2, m3, d12, d13, d23, w1, w2, w3⟩
  · exact fin d d qd sd (hl.sub _ qd) rfl ad
  · -- las ventanas leen `s1`
    have hs1w : InW φ x.id.step u.id.step w.id.step s1 := by
      rcases m1 with b1 | b1
      · rcases m2 with b2 | b2
        · rcases m3 with b3 | b3
          · exact absurd (D.cardA z1 z2 z3 b1 b2 b3 d12 d13 d23) (fun h => h)
          · rw [← b3]; exact w3
        · rw [← b2]; exact w2
      · rw [← b1]; exact w1
    rcases F.inw hs1w with h | h
    · exact fin c1 a0 q1 rfl hP0 h.symm agr_refl
    · exact fin c2 a0 q2 s21 hP0 h.symm agr_refl

end Levels

-- ============================================================
-- Sin familias fantasma
-- ============================================================

/-- **Sin familias fantasma alrededor de una variable con datos de cadena**, para cualquier par local. -/
theorem phantomFree_chainData {v s1 s2 : Nat} {A M C : Nat → Prop} (hl : LocPair φ P0 P σ)
    (D : ChainData φ v s1 s2 A M C) (hv : stepVar φ σ = some v) (hσ0 : 0 ≤ σ) (hσN : σ < N)
    (hN : midFusion φ < N) : PhantomFree φ P0 P N σ := by
  intro R Tf hrefl hsymm hsw23 hsw12 hsteps hpair htrio hb2 hb3 hanch
  have hS : PhStruct φ P0 N R Tf := ⟨hrefl, hsymm, hsw23, hsw12, hsteps, hpair, htrio, hb2, hb3⟩
  refine ⟨pairs_of_struct hσ0 hσN hS hanch, ?_⟩
  suffices h : ∀ x u w, Tri R Tf x u w → TriOf φ P x u w from
    fun x u w a b c d e f g => h x u w ⟨a, b, c, d, e, f, g⟩
  have rng : ∀ {s : Nat}, s < φ.nVars → 0 ≤ varStep s ∧ varStep s < N := by
    intro s hs
    have h1 : 0 ≤ varStep s := by simp only [varStep]; omega
    have h2 : varStep s < midFusion φ := by simp only [varStep, midFusion]; omega
    exact ⟨h1, by omega⟩
  obtain ⟨h10, h1N⟩ := rng D.s1v
  obtain ⟨h20, h2N⟩ := rng D.s2v
  have hs1 := stepVar_var D.s1v
  have hs2 := stepVar_var D.s2v
  rcases D.pos with ⟨hCv, huniq⟩ | hvs | hMv
  · -- `v` en el último bloque
    have hA2 : ∀ x u w, Tri R Tf x u w →
        (x.id.step = varStep s2 ∨ u.id.step = varStep s2 ∨ w.id.step = varStep s2) → TriOf φ P x u w := by
      intro x u w t hor
      refine tri_lam_any (Rr := C) hσ0 hσN hs2 (fun z1 z2 b1 b2 d => ?_) (fun a0 a' h0 h' hss => ?_) hS hanch x u w t.xu t.xw
        t.uw t.nxu t.nxw t.nuw t.nf hor
      · by_cases e1 : z1 = v
        · exact Or.inl (by rw [e1]; exact hv)
        · by_cases e2 : z2 = v
          · exact Or.inr (by rw [e2]; exact hv)
          · exact absurd (huniq z1 z2 b1 b2 e1 e2) d
      · have := glue3_P hl D hv h0 h0 h0 (hl.sub _ h') rfl hss.symm (fun _ => h')
          (fun e => absurd hCv (by rw [e]; exact D.nC2)) (fun hm => absurd hCv (fun hc => D.dMC v hm hc))
        rwa [glue3_self] at this
    exact chain_far hl D hv hS (Or.inl ⟨hCv, huniq⟩) h10 h1N hs1
      (any_of_first hS (chain_mid hl D hv hS h20 h2N hs1 hs2 hA2))
  · -- `v = s2`: el paso fijado hace de paso de `s2`
    have hs2' : stepVar φ σ = some s2 := by rw [← hvs]; exact hv
    have hA2 : ∀ x u w, Tri R Tf x u w → (x.id.step = σ ∨ u.id.step = σ ∨ w.id.step = σ) → TriOf φ P x u w :=
      fun x u w t hor => tri_anchor hS hanch x u w t.xu t.xw t.uw t.nxu t.nxw t.nuw t.nf hor
    exact chain_far hl D hv hS (Or.inr hvs) h10 h1N hs1
      (any_of_first hS (chain_mid hl D hv hS hσ0 hσN hs1 hs2' hA2))
  · -- `v` en el bloque de en medio
    exact chain_allmid hl D hv hS hMv h20 h2N hs2
      (any_of_first hS (chain_near hl D hv hS hMv h10 h1N hs1 hs2
        (chain_both hl D hv hS hMv hσ0 hσN hanch hs1 hs2)))

end GPathB

/-- **`Chain3 φ`**: cada variable tiene un separador con dos lados pequeños (`SepData`) o está en una cadena de tres
bloques (`ChainData`). -/
def Chain3 (φ : Cnf) : Prop :=
  ∀ v, (∃ s L Rr, SepData φ v s L Rr) ∨ (∃ s1 s2 A M C, ChainData φ v s1 s2 A M C)

theorem chain3_of_sep2 (h : Sep2 φ) : Chain3 φ := fun v => Or.inl (h v)

namespace GPathB

open Driver Machine MachineOn

variable {P0 P : Assign → Prop} {N σ : Int}

theorem phantomFree_of_chain3 (hcl : Chain3 φ) (hl : LocPair φ P0 P σ) (hσ0 : 0 ≤ σ) (hσN : σ < N)
    (hN : midFusion φ < N) : PhantomFree φ P0 P N σ := by
  cases hv : stepVar φ σ with
  | none => exact phantomFree_none hl hv hσ0 hσN
  | some v =>
    rcases hcl v with ⟨s, L, Rr, D⟩ | ⟨s1, s2, A, M, C, D⟩
    · exact phantomFree_sepData hl D hv hσ0 hσN hN
    · exact phantomFree_chainData hl D hv hσ0 hσN hN

/-- **Toda fórmula de cadenas de tres bloques cumple la condición fuerte en todas sus líneas.** -/
theorem phantomAt_of_chain3 (hb : Bounded φ) (hcl : Chain3 φ) (T : Int) (hT : 1 ≤ T) : PhantomAt φ T := by
  by_cases hlow : T + 1 ≤ midFusion φ + 3
  · refine phantomAt_of_hellyAt hb hT (fun k d _ _ => ?_)
    refine ⟨fun r _ => helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_), helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_)⟩
    · exact ⟨⟨validUpTo_pre _ (by omega), by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
    · exact ⟨⟨validUpTo_pre _ hlow, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
  · intro k d hk hd
    have hds : d.step = T := by
      have := sonsOfMap_step φ k d hd
      have hks := mapNodes_step φ (T - 1) k hk
      omega
    refine ⟨fun r hr => ?_, phantomFree_of_chain3 hcl (locPair_up hb T k d) (by omega) (by omega) (by omega)⟩
    obtain ⟨r1, r2⟩ := reqOf_range hb r hr
    rw [hds] at r2
    exact phantomFree_of_chain3 hcl (locPair_filter T k r) (by omega) r2 (by omega)

/-- **La hipótesis de la lectura vale en toda fórmula de cadenas de tres bloques.** -/
theorem hRead_of_chain3 (hcl : Chain3 φ) {T : Int} (hN : midFusion φ < T) (k : NodeId) :
    HRead φ T (SolE φ T k) := by
  intro R r _ hr1 hrT
  exact phantomFree_of_chain3 hcl (locPair_read T k R r) (by omega) hrT hN

end GPathB

-- ============================================================
-- Un caso concreto
-- ============================================================

/-- Tres cláusulas en cadena: `(x0 ∨ x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ x4) ∧ (¬x4 ∨ x5 ∨ x6)`. -/
def threeChain : Cnf :=
  ⟨7, [⟨⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩⟩, ⟨⟨2, false⟩, ⟨3, true⟩, ⟨4, true⟩⟩, ⟨⟨4, false⟩, ⟨5, true⟩, ⟨6, true⟩⟩]⟩

theorem bounded_threeChain : Bounded threeChain := by
  intro c hc
  simp only [threeChain, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp [Clause.Bounded, threeChain]

/-- **La condición no es vacía**: la cadena de tres cláusulas tiene datos de cadena en cada una de sus variables. -/
theorem chain3_threeChain : Chain3 threeChain := by
  intro v
  by_cases hr : v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6
  · refine Or.inr ⟨2, 4, fun z => z = 0 ∨ z = 1, fun z => z = 3, fun z => z = 5 ∨ z = 6,
      ⟨by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        fun z a b => by omega, fun z a b => by omega, fun z a b => by omega,
        fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 a b => by omega,
        ?_, fun c hc => ?_⟩⟩
    · by_cases h56 : v = 5 ∨ v = 6
      · exact Or.inl ⟨h56, fun z1 z2 a b c d => by omega⟩
      · by_cases h4 : v = 4
        · exact Or.inr (Or.inl h4)
        · exact Or.inr (Or.inr (by omega))
    · simp only [threeChain, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact Or.inr (Or.inl (by simp))
      · exact Or.inr (Or.inr (Or.inl (by simp)))
      · exact Or.inr (Or.inr (Or.inr (by simp)))
  · by_cases hl : v = 0 ∨ v = 1 ∨ v = 2
    · refine Or.inr ⟨4, 2, fun z => z = 5 ∨ z = 6, fun z => z = 3, fun z => z = 0 ∨ z = 1,
        ⟨by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          fun z a b => by omega, fun z a b => by omega, fun z a b => by omega,
          fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 a b => by omega,
          ?_, fun c hc => ?_⟩⟩
      · by_cases h01 : v = 0 ∨ v = 1
        · exact Or.inl ⟨h01, fun z1 z2 a b c d => by omega⟩
        · exact Or.inr (Or.inl (by omega))
      · simp only [threeChain, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (by simp)))
        · exact Or.inr (Or.inr (Or.inl (by simp)))
        · exact Or.inr (Or.inl (by simp))
    · refine Or.inl ⟨v, fun _ => False, fun _ => False, ⟨fun h => absurd rfl h, fun h => h, fun _ h _ => h,
        Or.inl rfl, fun _ _ _ h _ _ _ _ _ => h, fun _ _ _ h _ _ _ _ _ => h, fun h => absurd rfl h, fun c hc => ?_⟩⟩
      simp only [threeChain, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩
      · exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩
      · exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩

namespace MachineOn

open GPathB Driver Machine

/-- **La espina `:on` decide toda fórmula de cadenas de tres bloques**, sin hipótesis sobre la máquina. -/
theorem spineVerdictOn_iff_of_chain3 (hbd : Bounded φ) (hcl : Chain3 φ) : SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_phantomFree hbd (phantomAt_of_chain3 hbd hcl)

/-- **La máquina `:on` es exacta en toda fórmula de cadenas de tres bloques.** -/
theorem machineExact_of_chain3 (hbd : Bounded φ) (hcl : Chain3 φ) : MachineExact φ :=
  (machineExact_iff hbd).2 (phantomAt_of_chain3 hbd hcl)

/-- **El lector no se atasca en ninguna fórmula de cadenas de tres bloques.** -/
theorem reader_on_chain3 (hbd : Bounded φ) (hcl : Chain3 φ) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_on hbd (phantomAt_of_chain3 hbd hcl)
    (fun k => hRead_of_chain3 hcl (by unfold stepCount midFusion; omega) k) hkv hr

/-- **Tres cláusulas en cadena, sin ninguna hipótesis**: la máquina `:on` es exacta en
`(x0 ∨ x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ x4) ∧ (¬x4 ∨ x5 ∨ x6)`. -/
theorem machineExact_threeChain : MachineExact threeChain := machineExact_of_chain3 bounded_threeChain chain3_threeChain

end MachineOn

end AbsSatBingo.Model
