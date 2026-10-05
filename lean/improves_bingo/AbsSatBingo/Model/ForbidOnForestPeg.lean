-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnForestPeg.lean
import AbsSatBingo.Model.ForbidOnIncForest

/-!
# H2′ en los árboles de cláusulas (plan del v229, paso 4)

Una fórmula con un bosque de incidencia de raíz común (`IncForest`, Berge-acíclica) y **lecturas locales**: lo que la
ventana de cada paso lee fuera de las variables libres cae en un bloque (una variable o una cláusula).

Para un trío Helly-fallido, `sep_three` da el vértice `m` que separa sus tres bloques. El paso de corte `λ₀` lee lo
que hace falta de `m`: el paso de su variable, o el tercer paso de su cláusula (si `m` no es de la fórmula, cualquiera).
Las regiones son las ramas respecto de `m` (`regOf`). Entonces vale `PegF` en `λ₀`: ninguna cláusula cruza ramas sin
pasar por el corte (`br_clause`) y cada región toca a lo sumo un nodo del trío (`sep_three`).

* Si `λ₀` no es paso del trío, es el `λ` de H2′.
* Si lo es, el nodo `y` del trío en `λ₀` es alcanzable desde los tres (las ramas de sus parejas pasan por él) y el
  pegado da una rama de `P` por los tres: el trío no era Helly-fallido. Esto cierra el hueco del §6.2 del v229 (todos
  los casos de ocupación) sin subcasos.

* **`pegF_forest`**, **`twoWitnessF_of_forest`**, **`reader_winNode_of_forest`**.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- La variable `z` está en el bloque `B` (la variable misma o una cláusula que la contiene). -/
def InBlk (φ : Cnf) (B : Vx) (z : Nat) : Prop :=
  B = .var z ∨ ∃ j c, B = .cls j ∧ φ.clauses[j]? = some c ∧ ClVar c z

/-- **Lecturas locales**: lo que lee la ventana de cada paso, fuera de las libres, cae en un bloque. -/
def LocalBlocks (φ : Cnf) (Fr : Nat → Prop) : Prop := ∀ k : Int, ∃ B : Vx, ∀ z, WR φ k z → ¬ Fr z → InBlk φ B z

/-- Un número por rama (inyectivo). -/
def codeBr : Option Vx → Nat
  | none => 0
  | some (.var z) => 2 * z + 1
  | some (.cls j) => 2 * j + 2

theorem codeBr_inj {a b : Option Vx} (h : codeBr a = codeBr b) : a = b := by
  rcases a with _ | (z | j) <;> rcases b with _ | (z' | j') <;> simp only [codeBr] at h <;>
    first | rfl | omega | (congr 2; omega)

/-- El paso de corte para el separador `m`. -/
def cutStep (φ : Cnf) : Vx → Int
  | .var v => if v < φ.nVars then varStep v else 0
  | .cls j => if j < φ.clauses.length then clauseStep φ j 2 else 0

theorem cutStep_bounds (m : Vx) : 0 ≤ cutStep φ m ∧ cutStep φ m < stepCount φ := by
  cases m with
  | var v =>
    simp only [cutStep]; split
    · simp only [varStep, stepCount]; omega
    · simp only [stepCount]; omega
  | cls j =>
    simp only [cutStep]; split
    · simp only [clauseStep, stepCount]; omega
    · simp only [stepCount]; omega

/-- El corte lee lo que hace falta de `m`: su variable, o las tres de su cláusula. -/
theorem cutStep_var {v : Nat} (hv : v < φ.nVars) : WR φ (cutStep φ (.var v)) v := by
  simp only [cutStep, if_pos hv]
  exact ⟨varStep v, Or.inl rfl, stepVar_var hv⟩

theorem cutStep_cls {j : Nat} {c : Clause} (hj : φ.clauses[j]? = some c) {z : Nat} (hz : ClVar c z) :
    WR φ (cutStep φ (.cls j)) z := by
  have hjl : j < φ.clauses.length := (List.getElem?_eq_some_iff.mp hj).1
  simp only [cutStep, if_pos hjl]
  have k1 : clauseStep φ j 2 - 1 = clauseStep φ j 1 := by simp only [clauseStep]; omega
  have k2 : clauseStep φ j 2 - 2 = clauseStep φ j 0 := by simp only [clauseStep]; omega
  have p0 : (0 : Int) < clauseStep φ j 2 := by simp only [clauseStep]; omega
  have p1 : (1 : Int) < clauseStep φ j 2 := by simp only [clauseStep]; omega
  rcases hz with rfl | rfl | rfl
  · exact ⟨_, Or.inr (Or.inr ⟨p1, rfl⟩), by rw [k2]; exact stepVar_clause hj 0 (by omega)⟩
  · exact ⟨_, Or.inr (Or.inl ⟨p0, rfl⟩), by rw [k1]; exact stepVar_clause hj 1 (by omega)⟩
  · exact ⟨_, Or.inl rfl, stepVar_clause hj 2 (by omega)⟩

/-- Una variable fuera del corte de `m` no es `m`. -/
theorem var_ne_of_cut (hbd : Bounded φ) {m : Vx} {Kc : Nat → Prop} (hK : ∀ z, WR φ (cutStep φ m) z → Kc z)
    {j : Nat} {c : Clause} (hj : φ.clauses[j]? = some c) {z : Nat} (hz : ClVar c z) (hn : ¬ Kc z) :
    Vx.var z ≠ m ∧ Vx.cls j ≠ m := by
  have hzn : z < φ.nVars := by
    have := hbd c (List.mem_of_getElem? hj)
    rcases hz with rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  refine ⟨fun e => ?_, fun e => ?_⟩
  · subst e; exact hn (hK z (cutStep_var hzn))
  · subst e; exact hn (hK z (cutStep_cls hj hz))

namespace IncForest

variable (F : IncForest φ)

/-- La región de una variable: su rama respecto de `m`. -/
noncomputable def regOf (m : Vx) (z : Nat) : Nat := codeBr (F.br m (.var z))

/-- Una variable leída por un nodo, fuera del corte, está en la rama de su bloque, y el bloque no es `m`. -/
theorem touch_reg (hbd : Bounded φ) {m B : Vx} {Kc : Nat → Prop} (hK : ∀ z, WR φ (cutStep φ m) z → Kc z)
    {z : Nat} (hzn : z < φ.nVars) (hn : ¬ Kc z) (hb : InBlk φ B z) :
    B ≠ m ∧ F.br m (.var z) = F.br m B := by
  have hvz : Vx.var z ≠ m := fun e => by subst e; exact hn (hK z (cutStep_var hzn))
  rcases hb with rfl | ⟨j, c, rfl, hj, hz⟩
  · exact ⟨hvz, rfl⟩
  · obtain ⟨_, hjm⟩ := var_ne_of_cut hbd hK hj hz hn
    exact ⟨hjm, F.br_clause hj hz hvz hjm⟩

end IncForest

/-- Una variable que lee un paso es de la fórmula. -/
theorem wr_lt {k : Int} {z : Nat} (hbd : Bounded φ) (h : WR φ k z) : z < φ.nVars := by
  obtain ⟨k', _, hk⟩ := h
  unfold stepVar at hk
  by_cases h0 : k' ≤ 0
  · rw [if_pos h0] at hk; cases hk
  rw [if_neg h0] at hk
  by_cases h1 : k' < midFusion φ
  · rw [if_pos h1] at hk
    cases hk
    simp only [varOfStep]
    simp only [midFusion] at h1
    omega
  rw [if_neg h1] at hk
  by_cases h2 : k' = midFusion φ
  · rw [if_pos h2] at hk; cases hk
  rw [if_neg h2] at hk
  by_cases h3 : fusionTop φ ≤ k'
  · rw [if_pos h3] at hk; cases hk
  rw [if_neg h3] at hk
  cases hc : clauseOf φ k' with
  | none => rw [hc] at hk; cases hk
  | some cp =>
    obtain ⟨c, p⟩ := cp
    rw [hc] at hk
    cases hk
    have := hbd c (mem_of_clauseOf φ k' c p hc)
    unfold litAt
    split
    · exact this.1
    · exact this.2.1
    · exact this.2.2

/-- **`PegF` en el corte de la mediana**: con lecturas locales y el separador `m` de los tres bloques, en el paso
`cutStep m` y con las ramas respecto de `m` como regiones. -/
theorem pegF_forest (hbd : Bounded φ) (F : IncForest φ) {KF Fr : Nat → Prop} {m : Vx} {b : Fin 3 → Vx}
    (hsep : ∀ i j, i ≠ j → b i = m ∨ b j = m ∨ F.br m (b i) ≠ F.br m (b j))
    {x u w : PathNodeId} (bx : ∀ z, WR φ x.id.step z → ¬ Fr z → InBlk φ (b 0) z)
    (bu : ∀ z, WR φ u.id.step z → ¬ Fr z → InBlk φ (b 1) z)
    (bw : ∀ z, WR φ w.id.step z → ¬ Fr z → InBlk φ (b 2) z) :
    PegF φ KF Fr (cutStep φ m) (F.regOf m) x u w := by
  let Kc : Nat → Prop := fun z => KF z ∨ WR φ (cutStep φ m) z ∨ Fr z
  have hK : ∀ z, WR φ (cutStep φ m) z → Kc z := fun z h => Or.inr (Or.inl h)
  -- tocar una región es estar en la rama del bloque
  have touch : ∀ {q : Nat} {y : PathNodeId} {B : Vx}, (∀ z, WR φ y.id.step z → ¬ Fr z → InBlk φ B z) →
      Touch φ Kc (F.regOf m) q y → B ≠ m ∧ q = codeBr (F.br m B) := by
    intro q y B hB ⟨z, hn, hq, hr⟩
    have hnf : ¬ Fr z := fun h => hn (Or.inr (Or.inr h))
    obtain ⟨hBm, e⟩ := F.touch_reg hbd hK (wr_lt hbd hr) hn (hB z hr hnf)
    exact ⟨hBm, by rw [← hq]; unfold IncForest.regOf; rw [e]⟩
  -- dos nodos distintos del trío no tocan la misma región
  have two_no : ∀ {q : Nat} {i j : Fin 3} {y z : PathNodeId}, i ≠ j →
      (∀ t, WR φ y.id.step t → ¬ Fr t → InBlk φ (b i) t) → (∀ t, WR φ z.id.step t → ¬ Fr t → InBlk φ (b j) t) →
      Touch φ Kc (F.regOf m) q y → Touch φ Kc (F.regOf m) q z → False := by
    intro q i j y z hij hy hz ty tz
    obtain ⟨n1, e1⟩ := touch hy ty
    obtain ⟨n2, e2⟩ := touch hz tz
    rcases hsep i j hij with h | h | h
    · exact n1 h
    · exact n2 h
    · exact h (codeBr_inj (e1.symm.trans e2))
  refine ⟨fun c hc z z' hz hz' hn hn' => ?_, fun q ⟨t1, t2, _⟩ => two_no (by decide) bx bu t1 t2,
    fun q y z hyz ty tz => ?_⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    obtain ⟨n1, j1⟩ := var_ne_of_cut hbd hK hj hz hn
    obtain ⟨n2, _⟩ := var_ne_of_cut hbd hK hj hz' hn'
    unfold IncForest.regOf
    rw [F.br_clause hj hz n1 j1, F.br_clause hj hz' n2 j1]
  · exfalso
    rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact two_no (by decide) bx bu ty tz
    · exact two_no (by decide) bx bw ty tz
    · exact two_no (by decide) bu bw ty tz

/-- **H2′ en los árboles de cláusulas**: con un bosque de incidencia de raíz común, variables libres en cláusulas de
una variable y lecturas locales. -/
theorem twoWitnessF_of_forest (hbd : Bounded φ) (F : IncForest φ) {r : Vx} (hroot : ∀ v, F.Anc r v)
    {Fr : Nat → Prop} (hFr : FreeOK φ Fr) (hlb : LocalBlocks φ Fr) {P0 P : Assign → Prop}
    (hloc : ∀ g, (∀ q, ∃ a, P a ∧ LAgree φ q g a) → P g) : TwoWitnessF φ P0 P (stepCount φ) := by
  classical
  intro x u w nxu nxw nuw _ pxu pxw puw hno
  obtain ⟨Bx, hBx⟩ := hlb x.id.step
  obtain ⟨Bu, hBu⟩ := hlb u.id.step
  obtain ⟨Bw, hBw⟩ := hlb w.id.step
  let b : Fin 3 → Vx := fun i => if i = 0 then Bx else if i = 1 then Bu else Bw
  obtain ⟨m, _, hsep⟩ := F.sep_three hroot b
  have peg : PegF φ (ConstIn P) Fr (cutStep φ m) (F.regOf m) x u w :=
    pegF_forest hbd F hsep (fun z h hf => hBx z h hf) (fun z h hf => hBu z h hf) (fun z h hf => hBw z h hf)
  have hfix : ∀ a b, P a → P b → ∀ z, ConstIn P z → a z = b z := fun a b ha hb z hz => hz a b ha hb
  obtain ⟨l0, l1⟩ := cutStep_bounds (φ := φ) m
  obtain ⟨a1, h1, x1, u1⟩ := pxu
  obtain ⟨a2, h2, x2, w2⟩ := pxw
  obtain ⟨a3, h3, u3, w3⟩ := puw
  -- si el corte cae en un nodo del trío, ese nodo es alcanzable desde los tres y el trío no era Helly-fallido
  by_cases ex : cutStep φ m = x.id.step
  · exact absurd (glue_pegF (s := x) hloc hfix hFr peg h1 h1 h2 x1 u1 w2 (by rw [ex]; exact x1) (by rw [ex]; exact x1)
      (by rw [ex]; exact x2) ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩ ⟨a3, h3, u3, w3⟩) hno
  by_cases eu : cutStep φ m = u.id.step
  · exact absurd (glue_pegF (s := u) hloc hfix hFr peg h1 h1 h3 x1 u1 w3 (by rw [eu]; exact u1) (by rw [eu]; exact u1)
      (by rw [eu]; exact u3) ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩ ⟨a3, h3, u3, w3⟩) hno
  by_cases ew : cutStep φ m = w.id.step
  · exact absurd (glue_pegF (s := w) hloc hfix hFr peg h2 h3 h2 x2 u3 w2 (by rw [ew]; exact w2) (by rw [ew]; exact w3)
      (by rw [ew]; exact w2) ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩ ⟨a3, h3, u3, w3⟩) hno
  refine ⟨cutStep φ m, l0, l1, ex, eu, ew, fun s _ hx hu hw => ?_⟩
  exact absurd ⟨hx, hu, hw⟩ (noCommon_of_pegF hloc hfix hFr peg ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩
    ⟨a3, h3, u3, w3⟩ hno s)

namespace MachineOn

open GPathB Driver Machine

/-- **El lector por nodos de ventana no se atasca en los árboles de cláusulas** con lecturas locales, dadas las
líneas. -/
theorem reader_winNode_of_forest (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T) (F : IncForest φ)
    {r : Vx} (hroot : ∀ v, F.Anc r v) {Fr : Nat → Prop} (hFr : FreeOK φ Fr) (hlb : LocalBlocks φ Fr)
    {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ) {W : List (List NodeId)} {g' : GPathB}
    (hr : WinReading φ kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ W.flatten, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_winNode_of_twoWitnessF hbd HA (fun _ _ _ _ _ _ _ _ _ _ _ =>
    twoWitnessF_of_forest hbd F hroot hFr hlb loc_window) hkv hr

end MachineOn

end AbsSatBingo.Model
