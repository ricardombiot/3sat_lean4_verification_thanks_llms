-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnBagTree.lean
import AbsSatBingo.Model.ForbidOnPadLines

/-!
# Descomposición en árbol: H2′ y el lector con bolsas

Generaliza el bosque de incidencia (`IncForest`, fórmulas Berge-acíclicas) a una **descomposición en árbol** de la
fórmula: un árbol con raíz de bolsas de variables (`BagDec`) tal que

* toda cláusula cabe en una bolsa (`cover`, fuera de las variables libres);
* las bolsas que contienen una variable forman un subárbol (`conn`: suben hasta su cima `top z`);
* toda bolsa la lee la ventana de un paso (`cut`, `read`): las bolsas tienen a lo sumo tres variables no libres;
* lo que lee la ventana de cada paso, fuera de las libres, cabe en una bolsa (`loc`).

El árbol de bolsas es un `IncForest` de la fórmula vacía (sus aristas no piden nada): así `br`, `br_edge` y `sep_three`
se heredan sin repetirlos.

Para un trío Helly-fallido, `sep_three` da la bolsa `m` que separa sus tres bloques; el corte es la ventana de
`cut m`, que lee toda la bolsa. Una variable fuera de `m` tiene su subárbol entero en una rama de `m` (`br_top`), así
que las regiones son las ramas de la cima de cada variable y vale `PegF` (`pegF_bags`).

* **`twoWitnessF_of_bags`**, **`reader_winNode_of_bags`**: H2′ y el lector sin atasco, dadas las líneas.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- La fórmula vacía: un bosque de incidencia suyo es un árbol cualquiera sobre `Vx`. -/
def emptyCnf : Cnf := ⟨0, []⟩

/-- **Descomposición en árbol** de `φ` con bolsas leídas por una ventana. -/
structure BagDec (φ : Cnf) (Fr : Nat → Prop) where
  T      : IncForest emptyCnf
  root   : Vx
  hroot  : ∀ v, T.Anc root v
  bag    : Vx → Nat → Prop
  top    : Nat → Vx
  conn   : ∀ z t, bag t z → t = top z ∨ ∃ p, T.par t = some p ∧ bag p z
  cover  : ∀ c ∈ φ.clauses, ∃ t, ∀ z, ClVar c z → ¬ Fr z → bag t z
  cut    : Vx → Int
  cut_lo : ∀ t, 0 ≤ cut t
  cut_hi : ∀ t, cut t < stepCount φ
  read   : ∀ t z, bag t z → WR φ (cut t) z ∨ Fr z
  loc    : ∀ k : Int, ∃ t, ∀ z, WR φ k z → ¬ Fr z → bag t z

namespace BagDec

variable {Fr : Nat → Prop} (D : BagDec φ Fr)

/-- Subiendo por las bolsas de `z` se llega a su cima, sin cambiar de rama respecto de una bolsa sin `z`. -/
theorem up {z : Nat} : ∀ (n : Nat) (t : Vx), D.T.dep t ≤ n → D.bag t z →
    D.bag (D.top z) z ∧ ∀ m, ¬ D.bag m z → D.T.br m t = D.T.br m (D.top z) := by
  intro n
  induction n with
  | zero =>
    intro t ht hb
    rcases D.conn z t hb with e | ⟨p, hp, _⟩
    · subst e; exact ⟨hb, fun _ _ => rfl⟩
    · have := D.T.dep_lt t p hp; omega
  | succ n ih =>
    intro t ht hb
    rcases D.conn z t hb with e | ⟨p, hp, hpz⟩
    · subst e; exact ⟨hb, fun _ _ => rfl⟩
    · have := D.T.dep_lt t p hp
      obtain ⟨h1, h2⟩ := ih p (by omega) hpz
      refine ⟨h1, fun m hm => ?_⟩
      have htm : t ≠ m := fun e => hm (e ▸ hb)
      have hpm : p ≠ m := fun e => hm (e ▸ hpz)
      rw [D.T.br_edge hp htm hpm]
      exact h2 m hm

/-- **El subárbol de una variable está en una sola rama** de toda bolsa que no la contiene. -/
theorem br_top {z : Nat} {t m : Vx} (hb : D.bag t z) (hm : ¬ D.bag m z) : D.T.br m t = D.T.br m (D.top z) :=
  (D.up _ t (Nat.le_refl _) hb).2 m hm

/-- La región de una variable respecto de la bolsa `m`: la rama de su cima. -/
noncomputable def reg (m : Vx) (z : Nat) : Nat := codeBr (D.T.br m (D.top z))

/-- **`PegF` en el corte de la bolsa separadora.** -/
theorem pegF_bags {KF : Nat → Prop} {m : Vx} {b : Fin 3 → Vx}
    (hsep : ∀ i j, i ≠ j → b i = m ∨ b j = m ∨ D.T.br m (b i) ≠ D.T.br m (b j))
    {x u w : PathNodeId} (bx : ∀ z, WR φ x.id.step z → ¬ Fr z → D.bag (b 0) z)
    (bu : ∀ z, WR φ u.id.step z → ¬ Fr z → D.bag (b 1) z)
    (bw : ∀ z, WR φ w.id.step z → ¬ Fr z → D.bag (b 2) z) :
    PegF φ KF Fr (D.cut m) (D.reg m) x u w := by
  let Kc : Nat → Prop := fun z => KF z ∨ WR φ (D.cut m) z ∨ Fr z
  -- fuera del corte no se está en la bolsa separadora
  have notm : ∀ z, ¬ Kc z → ¬ D.bag m z := fun z hn hb => by
    rcases D.read m z hb with h | h
    · exact hn (Or.inr (Or.inl h))
    · exact hn (Or.inr (Or.inr h))
  -- tocar una región es estar en la rama del bloque
  have touch : ∀ {q : Nat} {y : PathNodeId} {B : Vx}, (∀ z, WR φ y.id.step z → ¬ Fr z → D.bag B z) →
      Touch φ Kc (D.reg m) q y → B ≠ m ∧ q = codeBr (D.T.br m B) := by
    intro q y B hB ⟨z, hn, hq, hr⟩
    have hbz := hB z hr (fun h => hn (Or.inr (Or.inr h)))
    have hm := notm z hn
    refine ⟨fun e => hm (e ▸ hbz), ?_⟩
    rw [← hq]
    unfold BagDec.reg
    rw [D.br_top hbz hm]
  -- dos nodos distintos del trío no tocan la misma región
  have two_no : ∀ {q : Nat} {i j : Fin 3} {y z : PathNodeId}, i ≠ j →
      (∀ t, WR φ y.id.step t → ¬ Fr t → D.bag (b i) t) → (∀ t, WR φ z.id.step t → ¬ Fr t → D.bag (b j) t) →
      Touch φ Kc (D.reg m) q y → Touch φ Kc (D.reg m) q z → False := by
    intro q i j y z hij hy hz ty tz
    obtain ⟨n1, e1⟩ := touch hy ty
    obtain ⟨n2, e2⟩ := touch hz tz
    rcases hsep i j hij with h | h | h
    · exact n1 h
    · exact n2 h
    · exact h (codeBr_inj (e1.symm.trans e2))
  refine ⟨fun c hc z z' hz hz' hn hn' => ?_, fun q ⟨t1, t2, _⟩ => two_no (by decide) bx bu t1 t2,
    fun q y z hyz ty tz => ?_⟩
  · obtain ⟨t, ht⟩ := D.cover c hc
    have f : ¬ Fr z := fun h => hn (Or.inr (Or.inr h))
    have f' : ¬ Fr z' := fun h => hn' (Or.inr (Or.inr h))
    unfold BagDec.reg
    rw [← D.br_top (ht z hz f) (notm z hn), ← D.br_top (ht z' hz' f') (notm z' hn')]
  · exfalso
    rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact two_no (by decide) bx bu ty tz
    · exact two_no (by decide) bx bw ty tz
    · exact two_no (by decide) bu bw ty tz

/-- **El testigo de H2′ con bolsas**: para un trío Helly-fallido con bloques `Bx`, `Bu`, `Bw`, el corte de la bolsa
separadora es el `λ` de H2′, si cae bajo `N` para las bolsas antepasadas de algún bloque. -/
theorem witness_bags (hFr : FreeOK φ Fr) {P0 P : Assign → Prop}
    (hloc : ∀ g, (∀ q, ∃ a, P a ∧ LAgree φ q g a) → P g) {N : Int} {x u w : PathNodeId} {Bx Bu Bw : Vx}
    (hBx : ∀ z, WR φ x.id.step z → ¬ Fr z → D.bag Bx z) (hBu : ∀ z, WR φ u.id.step z → ¬ Fr z → D.bag Bu z)
    (hBw : ∀ z, WR φ w.id.step z → ¬ Fr z → D.bag Bw z)
    (hcut : ∀ m, (D.T.Anc m Bx ∨ D.T.Anc m Bu ∨ D.T.Anc m Bw) → D.cut m < N)
    (pxu : ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u)
    (pxw : ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a w.id.step = w)
    (puw : ∃ a, P a ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w)
    (hno : ¬ (∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧
      pidOfAssign φ a w.id.step = w)) :
    ∃ lam, 0 ≤ lam ∧ lam < N ∧ lam ≠ x.id.step ∧ lam ≠ u.id.step ∧ lam ≠ w.id.step ∧
      ∀ s, s.id.step = lam → NodeProj φ P x lam s → NodeProj φ P u lam s → NodeProj φ P w lam s →
        ¬ Tri0 φ P0 x u s ∨ ¬ Tri0 φ P0 x w s ∨ ¬ Tri0 φ P0 u w s := by
  classical
  let b : Fin 3 → Vx := fun i => if i = 0 then Bx else if i = 1 then Bu else Bw
  obtain ⟨m, hpa, hsep⟩ := D.T.sep_three D.hroot b
  have hmN : D.cut m < N := by
    obtain ⟨i, _, _, hi, _⟩ := hpa
    apply hcut
    by_cases h0 : i = 0
    · simp only [b, h0, if_true] at hi; exact Or.inl hi
    · by_cases h1 : i = 1
      · simp only [b, h1, if_true] at hi; exact Or.inr (Or.inl hi)
      · simp only [b, h0, h1, if_false] at hi; exact Or.inr (Or.inr hi)
  have peg : PegF φ (ConstIn P) Fr (D.cut m) (D.reg m) x u w :=
    D.pegF_bags hsep (fun z h hf => hBx z h hf) (fun z h hf => hBu z h hf) (fun z h hf => hBw z h hf)
  have hfix : ∀ a b, P a → P b → ∀ z, ConstIn P z → a z = b z := fun a b ha hb z hz => hz a b ha hb
  obtain ⟨a1, h1, x1, u1⟩ := pxu
  obtain ⟨a2, h2, x2, w2⟩ := pxw
  obtain ⟨a3, h3, u3, w3⟩ := puw
  -- si el corte cae en un nodo del trío, ese nodo es alcanzable desde los tres y el trío no era Helly-fallido
  by_cases ex : D.cut m = x.id.step
  · exact absurd (glue_pegF (s := x) hloc hfix hFr peg h1 h1 h2 x1 u1 w2 (by rw [ex]; exact x1)
      (by rw [ex]; exact x1) (by rw [ex]; exact x2) ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩ ⟨a3, h3, u3, w3⟩) hno
  by_cases eu : D.cut m = u.id.step
  · exact absurd (glue_pegF (s := u) hloc hfix hFr peg h1 h1 h3 x1 u1 w3 (by rw [eu]; exact u1)
      (by rw [eu]; exact u1) (by rw [eu]; exact u3) ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩ ⟨a3, h3, u3, w3⟩) hno
  by_cases ew : D.cut m = w.id.step
  · exact absurd (glue_pegF (s := w) hloc hfix hFr peg h2 h3 h2 x2 u3 w2 (by rw [ew]; exact w2)
      (by rw [ew]; exact w3) (by rw [ew]; exact w2) ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩ ⟨a3, h3, u3, w3⟩) hno
  refine ⟨D.cut m, D.cut_lo m, hmN, ex, eu, ew, fun s _ hx hu hw => ?_⟩
  exact absurd ⟨hx, hu, hw⟩ (noCommon_of_pegF hloc hfix hFr peg ⟨a1, h1, x1, u1⟩ ⟨a2, h2, x2, w2⟩
    ⟨a3, h3, u3, w3⟩ hno s)

include D in
/-- **H2′ con una descomposición en árbol** de bolsas leídas por una ventana. -/
theorem twoWitnessF_of_bags (hFr : FreeOK φ Fr) {P0 P : Assign → Prop}
    (hloc : ∀ g, (∀ q, ∃ a, P a ∧ LAgree φ q g a) → P g) : TwoWitnessF φ P0 P (stepCount φ) := by
  intro x u w nxu nxw nuw _ pxu pxw puw hno
  obtain ⟨Bx, hBx⟩ := D.loc x.id.step
  obtain ⟨Bu, hBu⟩ := D.loc u.id.step
  obtain ⟨Bw, hBw⟩ := D.loc w.id.step
  obtain ⟨lam, l0, l1, lx, lu, lw, hl⟩ :=
    D.witness_bags hFr hloc hBx hBu hBw (fun m _ => D.cut_hi m) pxu pxw puw hno
  exact ⟨lam, l0, l1, lx, lu, lw, hl⟩

end BagDec

namespace MachineOn

open GPathB Driver Machine

/-- **El lector por nodos de ventana no se atasca con una descomposición en árbol** de bolsas leídas por una
ventana, dadas las líneas. -/
theorem reader_winNode_of_bags (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T) {Fr : Nat → Prop}
    (D : BagDec φ Fr) (hFr : FreeOK φ Fr) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {W : List (List NodeId)} {g' : GPathB} (hr : WinReading φ kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ W.flatten, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_winNode_of_twoWitnessF hbd HA (fun _ _ _ _ _ _ _ _ _ _ _ =>
    D.twoWitnessF_of_bags hFr loc_window) hkv hr

end MachineOn

end AbsSatBingo.Model
