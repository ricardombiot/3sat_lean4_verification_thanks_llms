-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnBlock.lean
import AbsSatBingo.Model.ForbidOnReadIff

/-!
# El parche: cláusulas de tres literales distintos, sin hipótesis

`ForbidOnMaj` da la condición de cuatro ramas (`Helly4`) con la mayoría, y por eso solo llega a las fórmulas con forma
2-CNF. Aquí la rama que falta se construye de otra manera: **parcheando**. Dadas la rama `a0` (por los tres nodos) y
las ramas `a1`, `a2`, `a3` (cada una por dos de ellos y por el nodo del paso `σ`), se toma `a0` y se le cambia un
conjunto `B` de variables por los valores de una `aₘ`.

* **`helly4_of_patch`** (sin máquina y sin fórmula concreta): si `B` no tiene tres variables distintas además de la
  que lee el paso `σ`, y parchear en `B` una rama de `P0` con una de `P` da una rama de `P`, vale `Helly4`. La cuenta:
  si ninguno de los tres parches pasa por los tres nodos, cada `aₘ` discrepa de `a0` en una variable de `B` que las
  otras dos ramas leen igual que `a0`; son tres variables distintas, y ninguna es la del paso `σ` porque ahí las tres
  ramas coinciden.
* **`Blocks3 φ E`**: las variables de `φ` se reparten en bloques (`E v z`: `z` está en el bloque de `v`), cada
  cláusula cae entera en un bloque, y el bloque de `v` no tiene tres variables distintas además de `v`. El parche en el
  bloque de la variable del paso `σ` conserva las soluciones de todo prefijo (`not_prohibited_patch`): una ventana
  prohibida es una cláusula entera, y la cláusula está toda dentro o toda fuera del bloque.
* **`ReadOnce φ`**: dos cláusulas distintas no comparten variable. Da `Blocks3` (`blocks3_readOnce`).

Resultado, **sin hipótesis sobre la máquina** y con cláusulas de tres literales distintos:

  `spineVerdictOn_iff_of_blocks`, `machineExact_of_blocks`, `reader_on_blocks` (y las tres `_readOnce`).

`helly4_of_patch` no menciona bloques: sirve para cualquier `B` que cumpla sus dos hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

-- ============================================================
-- El parche
-- ============================================================

open Classical in
/-- **El parche**: `a'` en las variables de `B`, `a0` en las demás. -/
noncomputable def patch (B : Nat → Prop) (a' a0 : Assign) : Assign := fun z => if B z then a' z else a0 z

open Classical in
theorem patch_in {B : Nat → Prop} {a' a0 : Assign} {z : Nat} (h : B z) : patch B a' a0 z = a' z := if_pos h

open Classical in
theorem patch_out {B : Nat → Prop} {a' a0 : Assign} {z : Nat} (h : ¬ B z) : patch B a' a0 z = a0 z := if_neg h

theorem patch_eq {B : Nat → Prop} {a' a0 : Assign} {z : Nat} (h : a' z = a0 z) : patch B a' a0 z = a0 z := by
  by_cases hb : B z
  · rw [patch_in hb, h]
  · exact patch_out hb

/-- Los pasos que lee la ventana del paso `k`. -/
def InWin (k k' : Int) : Prop := k' = k ∨ (0 < k ∧ k' = k - 1) ∨ (1 < k ∧ k' = k - 2)

variable {φ : Cnf}

/-- Dos ramas con la misma ventana coinciden en las variables que la ventana lee. -/
theorem var_of_pid_eq {a b : Assign} {k k' : Int} (h : pidOfAssign φ a k = pidOfAssign φ b k) (hw : InWin k k')
    {z : Nat} (hz : stepVar φ k' = some z) : a z = b z := by
  obtain ⟨h0, h1, h2⟩ := sels_of_pid_eq h
  rcases hw with e | ⟨hk, e⟩ | ⟨hk, e⟩
  · subst e; exact var_eq_of_sel h0 z hz
  · subst e; exact var_eq_of_sel (h1 hk) z hz
  · subst e; exact var_eq_of_sel (h2 hk) z hz

/-- Si `a'` pasa por la ventana de `a0`, el parche también. -/
theorem pid_patch_of_pass (B : Nat → Prop) {a' a0 : Assign} {k : Int}
    (h : pidOfAssign φ a' k = pidOfAssign φ a0 k) : pidOfAssign φ (patch B a' a0) k = pidOfAssign φ a0 k := by
  obtain ⟨h0, h1, h2⟩ := sels_of_pid_eq h
  exact pid_eq_of_sels (sel_eq_of_var fun z hz => patch_eq (var_eq_of_sel h0 z hz))
    (fun hk => sel_eq_of_var fun z hz => patch_eq (var_eq_of_sel (h1 hk) z hz))
    (fun hk => sel_eq_of_var fun z hz => patch_eq (var_eq_of_sel (h2 hk) z hz))

/-- El parche pasa por la ventana de `a0`, o la ventana lee una variable de `B` donde `a'` y `a0` discrepan. -/
theorem pid_patch_or (B : Nat → Prop) (a' a0 : Assign) (k : Int) :
    pidOfAssign φ (patch B a' a0) k = pidOfAssign φ a0 k ∨
      ∃ k' z, InWin k k' ∧ stepVar φ k' = some z ∧ B z ∧ a' z ≠ a0 z := by
  by_cases hex : ∃ k' z, InWin k k' ∧ stepVar φ k' = some z ∧ B z ∧ a' z ≠ a0 z
  · exact Or.inr hex
  · left
    have key : ∀ k', InWin k k' → selOfAssign φ (patch B a' a0) k' = selOfAssign φ a0 k' := by
      intro k' hw
      refine sel_eq_of_var (fun z hz => ?_)
      by_cases hb : B z
      · by_cases he : a' z = a0 z
        · exact patch_eq he
        · exact absurd ⟨k', z, hw, hz, hb, he⟩ hex
      · exact patch_out hb
    exact pid_eq_of_sels (key k (Or.inl rfl)) (fun hk => key _ (Or.inr (Or.inl ⟨hk, rfl⟩)))
      (fun hk => key _ (Or.inr (Or.inr ⟨hk, rfl⟩)))

/-- **La condición de cuatro ramas, por parche.** Si `B` no tiene tres variables distintas además de la del paso
`σ`, y parchear en `B` una rama de `P0` con una de `P` da una rama de `P`, alguno de los tres parches pasa por los
tres nodos. -/
theorem helly4_of_patch {P0 P : Assign → Prop} {N σ : Int} (B : Nat → Prop)
    (hcard : ∀ z1 z2 z3, B z1 → B z2 → B z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 →
      stepVar φ σ = some z1 ∨ stepVar φ σ = some z2 ∨ stepVar φ σ = some z3)
    (hP : ∀ a0 a', P0 a0 → P a' → P (patch B a' a0)) : Helly4 φ P0 P N σ := by
  intro a0 a1 a2 a3 i j l _ _ _ _ _ _ h0 h1 h2 h3 e1 e2 e3 e4 e5 e6 s2 s3
  rcases pid_patch_or (φ := φ) B a1 a0 l with g1 | ⟨k1, z1, w1, v1, b1, n1⟩
  · exact ⟨_, hP a0 a1 h0 h1, pid_patch_of_pass B e1, pid_patch_of_pass B e3, g1⟩
  rcases pid_patch_or (φ := φ) B a2 a0 j with g2 | ⟨k2, z2, w2, v2, b2, n2⟩
  · exact ⟨_, hP a0 a2 h0 h2, pid_patch_of_pass B e2, g2, pid_patch_of_pass B e5⟩
  rcases pid_patch_or (φ := φ) B a3 a0 i with g3 | ⟨k3, z3, w3, v3, b3, n3⟩
  · exact ⟨_, hP a0 a3 h0 h3, g3, pid_patch_of_pass B e4, pid_patch_of_pass B e6⟩
  exfalso
  have p21 : a2 z1 = a0 z1 := var_of_pid_eq e5 w1 v1
  have p12 : a1 z2 = a0 z2 := var_of_pid_eq e3 w2 v2
  have p13 : a1 z3 = a0 z3 := var_of_pid_eq e1 w3 v3
  have p23 : a2 z3 = a0 z3 := var_of_pid_eq e2 w3 v3
  have d12 : z1 ≠ z2 := fun e => n1 (by rw [e]; exact p12)
  have d13 : z1 ≠ z3 := fun e => n1 (by rw [e]; exact p13)
  have d23 : z2 ≠ z3 := fun e => n2 (by rw [e]; exact p23)
  rcases hcard z1 z2 z3 b1 b2 b3 d12 d13 d23 with hz | hz | hz
  · exact n1 ((var_of_pid_eq s2 (Or.inl rfl) hz).symm.trans p21)
  · exact n2 ((var_of_pid_eq s2 (Or.inl rfl) hz).trans p12)
  · exact n3 ((var_of_pid_eq s3 (Or.inl rfl) hz).trans p13)

-- ============================================================
-- Bloques de a lo sumo tres variables
-- ============================================================

/-- **`Blocks3 φ E`**: `E v z` dice que `z` está en el bloque de `v`. Cada cláusula cae entera dentro o entera fuera
del bloque de cada variable, y un bloque no tiene tres variables distintas además de la suya. -/
structure Blocks3 (φ : Cnf) (E : Nat → Nat → Prop) : Prop where
  refl : ∀ v, E v v
  cl   : ∀ c ∈ φ.clauses, ∀ v, (E v c.l1.v ∨ E v c.l2.v ∨ E v c.l3.v) → (E v c.l1.v ∧ E v c.l2.v ∧ E v c.l3.v)
  card : ∀ v z1 z2 z3, E v z1 → E v z2 → E v z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → z1 = v ∨ z2 = v ∨ z3 = v

/-- El bloque de la variable que lee el paso `σ` (vacío si no lee ninguna). -/
def BlkAt (φ : Cnf) (E : Nat → Nat → Prop) (σ : Int) (z : Nat) : Prop := ∃ v, stepVar φ σ = some v ∧ E v z

variable {E : Nat → Nat → Prop}

theorem blkAt_card (hb : Blocks3 φ E) (σ : Int) : ∀ z1 z2 z3, BlkAt φ E σ z1 → BlkAt φ E σ z2 → BlkAt φ E σ z3 →
    z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → stepVar φ σ = some z1 ∨ stepVar φ σ = some z2 ∨ stepVar φ σ = some z3 := by
  rintro z1 z2 z3 ⟨v, hv, e1⟩ ⟨v', hv', e2⟩ ⟨v'', hv'', e3⟩ d12 d13 d23
  rw [hv] at hv' hv''
  cases hv'; cases hv''
  rcases hb.card v z1 z2 z3 e1 e2 e3 d12 d13 d23 with h | h | h
  · exact Or.inl (by rw [h]; exact hv)
  · exact Or.inr (Or.inl (by rw [h]; exact hv))
  · exact Or.inr (Or.inr (by rw [h]; exact hv))

/-- En el paso `σ` el parche elige lo que elige `a'`. -/
theorem sel_patch_at (hb : Blocks3 φ E) (σ : Int) (a' a0 : Assign) :
    selOfAssign φ (patch (BlkAt φ E σ) a' a0) σ = selOfAssign φ a' σ :=
  sel_eq_of_var (fun z hz => patch_in ⟨z, hz, hb.refl z⟩)

/-- Donde `a'` y `a0` eligen lo mismo, el parche también. -/
theorem sel_patch_both (B : Nat → Prop) {a' a0 : Assign} {k : Int} {x : NodeId} (h' : selOfAssign φ a' k = x)
    (h0 : selOfAssign φ a0 k = x) : selOfAssign φ (patch B a' a0) k = x := by
  rw [← h0]
  exact sel_eq_of_var (fun z hz => patch_eq (var_eq_of_sel (h'.trans h0.symm) z hz))

theorem stepVar_clause {j : Nat} {c : Clause} (hj : φ.clauses[j]? = some c) (p : Nat) (hp : p < 3) :
    stepVar φ (clauseStep φ j p) = some (litAt c p).v := by
  have hjlt : j < φ.clauses.length := by
    by_cases hc : j < φ.clauses.length
    · exact hc
    · rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  have h0 : ¬ clauseStep φ j p ≤ 0 := by simp only [clauseStep]; omega
  have h1 : ¬ clauseStep φ j p < midFusion φ := by simp only [clauseStep, midFusion]; omega
  have h2 : ¬ clauseStep φ j p = midFusion φ := by simp only [clauseStep, midFusion]; omega
  have h3 : ¬ fusionTop φ ≤ clauseStep φ j p := by simp only [clauseStep, fusionTop]; omega
  simp only [stepVar, if_neg h0, if_neg h1, if_neg h2, if_neg h3, clauseOf_clauseStep φ j p c hp hj]

/-- **El parche no pisa ventanas prohibidas**: una ventana prohibida es una cláusula entera, y la cláusula está toda
dentro del bloque (la lee `a'`) o toda fuera (la lee `a0`). En el paso `σ` no hace falta nada de `a0`. -/
theorem not_prohibited_patch (hb : Blocks3 φ E) {σ k : Int} {a' a0 : Assign}
    (h' : isProhibited φ (pidOfAssign φ a' k) = false)
    (h0 : isProhibited φ (pidOfAssign φ a0 k) = false ∨ k = σ) :
    isProhibited φ (pidOfAssign φ (patch (BlkAt φ E σ) a' a0) k) = false := by
  cases hp : isProhibited φ (pidOfAssign φ (patch (BlkAt φ E σ) a' a0) k) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨j, c, hj, e, m1, m2, m3⟩ := prohibited_clause hp
    have hc := List.mem_of_getElem? hj
    by_cases hin : BlkAt φ E σ c.l1.v
    · obtain ⟨v, hv, hbv⟩ := hin
      obtain ⟨i1, i2, i3⟩ := hb.cl c hc v (Or.inl hbv)
      have x1 : litVal a' c.l1 = false := (litVal_congr (patch_in ⟨v, hv, i1⟩).symm).trans m1
      have x2 : litVal a' c.l2 = false := (litVal_congr (patch_in ⟨v, hv, i2⟩).symm).trans m2
      have x3 : litVal a' c.l3 = false := (litVal_congr (patch_in ⟨v, hv, i3⟩).symm).trans m3
      have pr := prohibited_of_false (a := a') hj x1 x2 x3
      rw [← e, h'] at pr; cases pr
    · have o2 : ¬ BlkAt φ E σ c.l2.v := fun ⟨v, hv, hbv⟩ => hin ⟨v, hv, (hb.cl c hc v (Or.inr (Or.inl hbv))).1⟩
      have o3 : ¬ BlkAt φ E σ c.l3.v := fun ⟨v, hv, hbv⟩ => hin ⟨v, hv, (hb.cl c hc v (Or.inr (Or.inr hbv))).1⟩
      have x1 : litVal a0 c.l1 = false := (litVal_congr (patch_out hin).symm).trans m1
      have x2 : litVal a0 c.l2 = false := (litVal_congr (patch_out o2).symm).trans m2
      have x3 : litVal a0 c.l3 = false := (litVal_congr (patch_out o3).symm).trans m3
      have pr := prohibited_of_false (a := a0) hj x1 x2 x3
      rw [← e] at pr
      rcases h0 with h0 | h0
      · rw [h0] at pr; cases pr
      · have hs : stepVar φ σ = some c.l3.v := by rw [← h0, e]; exact stepVar_clause hj 2 (by omega)
        exact o3 ⟨_, hs, hb.refl _⟩

/-- El parche de dos soluciones de un prefijo es una solución del prefijo. -/
theorem validUpTo_patch (hb : Blocks3 φ E) (σ : Int) {T : Int} {a' a0 : Assign} (h' : ValidUpTo φ a' T)
    (h0 : ValidUpTo φ a0 T) : ValidUpTo φ (patch (BlkAt φ E σ) a' a0) T :=
  fun s hs => not_prohibited_patch hb (h' s hs) (Or.inl (h0 s hs))

namespace GPathB

/-- **La condición de cuatro ramas vale en toda fórmula de bloques**, en todas las líneas. -/
theorem hellyAt_of_blocks (hb : Blocks3 φ E) (T : Int) : HellyAt φ T := by
  intro k d _ _
  refine ⟨fun r _ => helly4_of_patch (BlkAt φ E r.step) (blkAt_card hb _) (fun a0 a' h0 h' => ?_),
    helly4_of_patch (BlkAt φ E T) (blkAt_card hb _) (fun a0 a' h0 h' => ?_)⟩
  · exact ⟨⟨validUpTo_patch hb _ h'.1.1 h0.1, sel_patch_both _ h'.1.2 h0.2⟩, (sel_patch_at hb _ a' a0).trans h'.2⟩
  · have hd : selOfAssign φ a' T = d := by
      have := h'.1.2
      rwa [Int.add_sub_cancel] at this
    refine ⟨⟨fun s hs => not_prohibited_patch hb (h'.1.1 s hs) ?_, ?_⟩, sel_patch_both _ h'.2 h0.1.2⟩
    · by_cases hsT : s = T
      · exact Or.inr hsT
      · exact Or.inl (h0.1.1 s (by omega))
    · show selOfAssign φ _ (T + 1 - 1) = d
      rw [Int.add_sub_cancel]
      exact (sel_patch_at hb _ a' a0).trans hd

/-- **La hipótesis de la lectura vale en toda fórmula de bloques.** -/
theorem hRead_of_blocks (hb : Blocks3 φ E) (T : Int) (k : NodeId) : HRead φ T (SolE φ T k) := by
  intro R r _ hr1 hrT
  refine phantomFree_of_helly4 (by omega) hrT
    (helly4_of_patch (BlkAt φ E r.step) (blkAt_card hb _) (fun a0 a' h0 h' => ?_))
  exact ⟨⟨⟨validUpTo_patch hb _ h'.1.1.1 h0.1.1, sel_patch_both _ h'.1.1.2 h0.1.2⟩,
      fun x hx => sel_patch_both _ (h'.1.2 x hx) (h0.2 x hx)⟩, (sel_patch_at hb _ a' a0).trans h'.2⟩

end GPathB

-- ============================================================
-- Cláusulas que no comparten variables
-- ============================================================

/-- `z` es una variable de la cláusula. -/
def ClVar (c : Clause) (z : Nat) : Prop := z = c.l1.v ∨ z = c.l2.v ∨ z = c.l3.v

/-- **`ReadOnce φ`**: dos cláusulas distintas no comparten variable. -/
def ReadOnce (φ : Cnf) : Prop := ∀ c ∈ φ.clauses, ∀ c' ∈ φ.clauses, ∀ z, ClVar c z → ClVar c' z → c = c'

/-- Sin variables compartidas, el bloque de `v` son las variables de su cláusula. -/
theorem blocks3_readOnce (h : ReadOnce φ) :
    Blocks3 φ (fun v z => z = v ∨ ∃ c ∈ φ.clauses, ClVar c v ∧ ClVar c z) := by
  refine ⟨fun v => Or.inl rfl, fun c hc v hor => ?_, fun v z1 z2 z3 e1 e2 e3 d12 d13 d23 => ?_⟩
  · have hv : ClVar c v := by
      have aux : ∀ z, ClVar c z → (z = v ∨ ∃ c0 ∈ φ.clauses, ClVar c0 v ∧ ClVar c0 z) → ClVar c v := by
        intro z hz hE
        rcases hE with e | ⟨c0, hc0, hv0, hz0⟩
        · rw [← e]; exact hz
        · rw [h c hc c0 hc0 z hz hz0]; exact hv0
      rcases hor with hE | hE | hE
      · exact aux _ (Or.inl rfl) hE
      · exact aux _ (Or.inr (Or.inl rfl)) hE
      · exact aux _ (Or.inr (Or.inr rfl)) hE
    exact ⟨Or.inr ⟨c, hc, hv, Or.inl rfl⟩, Or.inr ⟨c, hc, hv, Or.inr (Or.inl rfl)⟩,
      Or.inr ⟨c, hc, hv, Or.inr (Or.inr rfl)⟩⟩
  · rcases e1 with e1 | ⟨c1, hc1, v1, w1⟩
    · exact Or.inl e1
    rcases e2 with e2 | ⟨c2, hc2, v2, w2⟩
    · exact Or.inr (Or.inl e2)
    rcases e3 with e3 | ⟨c3, hc3, v3, w3⟩
    · exact Or.inr (Or.inr e3)
    have q2 := h c2 hc2 c1 hc1 v v2 v1
    have q3 := h c3 hc3 c1 hc1 v v3 v1
    subst q2 q3
    unfold ClVar at v1 w1 w2 w3
    omega

namespace MachineOn

open GPathB Driver Machine

/-- **La espina `:on` decide toda fórmula de bloques**, sin hipótesis sobre la máquina. -/
theorem spineVerdictOn_iff_of_blocks (hbd : Bounded φ) (hb : Blocks3 φ E) : SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_helly hbd (fun T _ => hellyAt_of_blocks hb T)

/-- **La máquina `:on` es exacta en toda fórmula de bloques.** -/
theorem machineExact_of_blocks (hbd : Bounded φ) (hb : Blocks3 φ E) : MachineExact φ :=
  (machineExact_iff hbd).2 (fun T hT => phantomAt_of_hellyAt hbd hT (hellyAt_of_blocks hb T))

/-- **El lector no se atasca en ninguna fórmula de bloques**: cualquier lectura de un estado final deja un estado
válido con la rama de una asignación que satisface `φ` y coincide con todas las elecciones. -/
theorem reader_on_blocks (hbd : Bounded φ) (hb : Blocks3 φ E) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_on hbd (fun T hT => phantomAt_of_hellyAt hbd hT (hellyAt_of_blocks hb T))
    (fun k => hRead_of_blocks hb _ k) hkv hr

/-- **La espina `:on` decide las fórmulas cuyas cláusulas no comparten variables**, sin hipótesis. -/
theorem spineVerdictOn_iff_of_readOnce (hbd : Bounded φ) (h : ReadOnce φ) : SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_blocks hbd (blocks3_readOnce h)

/-- **La máquina `:on` es exacta en las fórmulas cuyas cláusulas no comparten variables.** -/
theorem machineExact_of_readOnce (hbd : Bounded φ) (h : ReadOnce φ) : MachineExact φ :=
  machineExact_of_blocks hbd (blocks3_readOnce h)

/-- **El lector no se atasca en las fórmulas cuyas cláusulas no comparten variables.** -/
theorem reader_on_readOnce (hbd : Bounded φ) (h : ReadOnce φ) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_on_blocks hbd (blocks3_readOnce h) hkv hr

end MachineOn

end AbsSatBingo.Model
