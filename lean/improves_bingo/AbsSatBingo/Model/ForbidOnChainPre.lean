-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainPre.lean
import AbsSatBingo.Model.ForbidOnChainOrdI

/-!
# El preproceso de renumeración

`test_3sat/preprocess_chain.jl` reescribe una cadena en la clase `ChainOrdN`: las cláusulas en el orden de la cadena,
las variables numeradas en ese orden y la de dentro de cada bloque de en medio como literal de en medio. Es un
**renombrado** de variables (y una permutación de literales y de cláusulas), así que no cambia la satisfacibilidad.

* **`Renaming φ φ'`**: `f` lleva las variables de `φ` a las de `φ'` y `g` las devuelve (`g ∘ f = id` en las variables
  usadas); cada cláusula de `φ'` es la imagen, literal a literal, de una de `φ`, y al revés.
* **`satisfiable_iff_of_renaming`**: `Satisfiable φ ↔ Satisfiable φ'` (con `a ∘ g` en un sentido y `a ∘ f` en el otro).
* **`spineVerdictOn_iff_of_pre`**: si la fórmula preprocesada está en `ChainOrdN`, **la espina sobre ella decide la
  original**.
* La instancia: `chain6_cross` (`chain6X`), su preprocesada (`chain6P`, que es `chain6_order`) en la clase, y
  **`spineVerdictOn_pre_chain6X`**.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

/-- Los tres literales de una cláusula. -/
def clLits (c : Clause) : List Lit := [c.l1, c.l2, c.l3]

/-- `l'` es la imagen de `l` por `f`. -/
def LitRen (f : Nat → Nat) (l l' : Lit) : Prop := l'.v = f l.v ∧ l'.pos = l.pos

instance (f : Nat → Nat) (l l' : Lit) : Decidable (LitRen f l l') :=
  inferInstanceAs (Decidable (l'.v = f l.v ∧ l'.pos = l.pos))

/-- **Un renombrado** de `φ` en `φ'`. -/
structure Renaming (φ φ' : Cnf) (f g : Nat → Nat) : Prop where
  gf  : ∀ c ∈ φ.clauses, ∀ l ∈ clLits c, g (f l.v) = l.v
  fwd : ∀ c ∈ φ.clauses, ∃ c' ∈ φ'.clauses, ∀ l' ∈ clLits c', ∃ l ∈ clLits c, LitRen f l l'
  bwd : ∀ c' ∈ φ'.clauses, ∃ c ∈ φ.clauses, ∀ l ∈ clLits c, ∃ l' ∈ clLits c', LitRen f l l'

theorem satClause_iff (a : Assign) (c : Clause) : SatClause a c ↔ ∃ l ∈ clLits c, litVal a l = true := by
  unfold SatClause clLits
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | h | h)
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr (Or.inl rfl), h⟩
    · exact ⟨_, Or.inr (Or.inr rfl), h⟩
  · rintro ⟨l, hl | hl | hl, h⟩ <;> subst hl
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- **Renombrar no cambia la satisfacibilidad.** -/
theorem satisfiable_iff_of_renaming {φ φ' : Cnf} {f g : Nat → Nat} (h : Renaming φ φ' f g) :
    Satisfiable φ ↔ Satisfiable φ' := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun w => a (g w), fun c' hc' => ?_⟩
    obtain ⟨c, hc, hsub⟩ := h.bwd c' hc'
    obtain ⟨l, hl, hv⟩ := (satClause_iff a c).mp (ha c hc)
    obtain ⟨l', hl', e1, e2⟩ := hsub l hl
    refine (satClause_iff _ c').mpr ⟨l', hl', ?_⟩
    unfold litVal at hv ⊢
    simp only
    rw [e1, e2, h.gf c hc l hl]; exact hv
  · rintro ⟨a', ha'⟩
    refine ⟨fun v => a' (f v), fun c hc => ?_⟩
    obtain ⟨c', hc', hsub⟩ := h.fwd c hc
    obtain ⟨l', hl', hv⟩ := (satClause_iff a' c').mp (ha' c' hc')
    obtain ⟨l, hl, e1, e2⟩ := hsub l' hl'
    refine (satClause_iff _ c).mpr ⟨l, hl, ?_⟩
    unfold litVal at hv ⊢
    simp only
    rw [e1, e2] at hv; exact hv

namespace MachineOn

open GPathB Driver Machine

/-- **La espina sobre la fórmula preprocesada decide la original.** -/
theorem spineVerdictOn_iff_of_pre {φ φ' : Cnf} {f g : Nat → Nat} (hR : Renaming φ φ' f g) (hb : Bounded φ')
    {n : Nat} {zone sv : Nat → Nat} (C : ChainOrdN φ' n zone sv) : SpineVerdictOn φ' ↔ Satisfiable φ :=
  (spineVerdictOn_iff_of_chainOrd hb C).trans (satisfiable_iff_of_renaming hR).symm

end MachineOn

/-! ## La instancia: `chain6_cross` -/

/-- **`chain6_cross`** (`scripts/cnf/chain6_cross.cnf`, variables desde 0):
`(x0 ∨ x2 ∨ x6) ∧ (¬x6 ∨ x4 ∨ x7) ∧ (¬x7 ∨ x5 ∨ x8) ∧ (¬x8 ∨ x1 ∨ x9) ∧ (¬x9 ∨ x3 ∨ x10) ∧ (¬x10 ∨ x11 ∨ x12)`. -/
def chain6X : Cnf :=
  ⟨13, [⟨⟨0, true⟩, ⟨2, true⟩, ⟨6, true⟩⟩, ⟨⟨6, false⟩, ⟨4, true⟩, ⟨7, true⟩⟩, ⟨⟨7, false⟩, ⟨5, true⟩, ⟨8, true⟩⟩,
    ⟨⟨8, false⟩, ⟨1, true⟩, ⟨9, true⟩⟩, ⟨⟨9, false⟩, ⟨3, true⟩, ⟨10, true⟩⟩, ⟨⟨10, false⟩, ⟨11, true⟩, ⟨12, true⟩⟩]⟩

/-- **Su preprocesada** (`scripts/cnf/pre/chain6_cross_pre.cnf`, que es `chain6_order`). -/
def chain6P : Cnf :=
  ⟨13, [⟨⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩⟩, ⟨⟨2, false⟩, ⟨3, true⟩, ⟨4, true⟩⟩, ⟨⟨4, false⟩, ⟨5, true⟩, ⟨6, true⟩⟩,
    ⟨⟨6, false⟩, ⟨7, true⟩, ⟨8, true⟩⟩, ⟨⟨8, false⟩, ⟨9, true⟩, ⟨10, true⟩⟩, ⟨⟨10, false⟩, ⟨11, true⟩, ⟨12, true⟩⟩]⟩

/-- El renombrado (las líneas `c map` del preproceso) y su inverso. -/
def f6 (v : Nat) : Nat := [0, 7, 1, 9, 3, 5, 2, 4, 6, 8, 10, 11, 12].getD v v
def g6 (w : Nat) : Nat := [0, 2, 6, 4, 7, 5, 8, 1, 9, 3, 10, 11, 12].getD w w

theorem renaming_chain6 : Renaming chain6X chain6P f6 g6 := ⟨by decide, by decide, by decide⟩

theorem bounded_chain6P : Bounded chain6P := by
  unfold Bounded Clause.Bounded
  decide

namespace GPathB

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 20000

def vals6P : List Nat := [0, 0, 7, 1, 8, 2, 9, 3, 10, 4, 11, 5, 5]

theorem chainOrd_chain6P : ChainOrdN chain6P 6 (zoneV 6 vals6P) sv12 := by
  refine ⟨chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    fun k h1 h2 => ?_, rfl, fun j c hj => ?_, fun z p h1 h2 hz => ?_, fun j c hj z p h1 h2 hz hcv => ?_⟩
  · have h : ∀ k, k < 6 → 1 ≤ k → zoneV 6 vals6P (sv12 k) = 6 + k := by decide
    exact h k h2 h1
  · have hjl : j < 6 := by
      by_cases h : j < 6
      · exact h
      · rw [List.getElem?_eq_none (by simp [chain6P]; omega)] at hj; cases hj
    have all : ∀ j, j < 6 → ∀ c, chain6P.clauses[j]? = some c → ClIn (BlkN 6 (zoneV 6 vals6P) j) c := by decide
    exact all j hjl c hj
  · have hzl : z < vals6P.length := zoneV_small hz (by omega)
    have h : ∀ z, z < vals6P.length → ∀ p, p < 6 → 1 ≤ p → p + 1 < 6 → zoneV 6 vals6P z = p →
        1 ≤ z ∧ z + 1 < 13 ∧ (z - 1 = sv12 p ∨ z - 1 = sv12 (p + 1)) ∧ (z + 1 = sv12 p ∨ z + 1 = sv12 (p + 1)) := by
      decide
    exact h z hzl p (by omega) h1 h2 hz
  · have hc : c ∈ chain6P.clauses := List.mem_of_getElem? hj
    have h : ∀ c ∈ chain6P.clauses, ∀ p, p < 6 → 1 ≤ p → p + 1 < 6 →
        (zoneV 6 vals6P c.l1.v = p → c.l2.v = c.l1.v ∧ (c.l1.v = sv12 p ∨ c.l1.v = sv12 (p + 1)) ∧
          (c.l3.v = sv12 p ∨ c.l3.v = sv12 (p + 1))) ∧
        (zoneV 6 vals6P c.l2.v = p → c.l2.v = c.l2.v ∧ (c.l1.v = sv12 p ∨ c.l1.v = sv12 (p + 1)) ∧
          (c.l3.v = sv12 p ∨ c.l3.v = sv12 (p + 1))) ∧
        (zoneV 6 vals6P c.l3.v = p → c.l2.v = c.l3.v ∧ (c.l1.v = sv12 p ∨ c.l1.v = sv12 (p + 1)) ∧
          (c.l3.v = sv12 p ∨ c.l3.v = sv12 (p + 1))) := by
      decide
    obtain ⟨a1, a2, a3⟩ := h c hc p (by omega) h1 h2
    rcases hcv with rfl | rfl | rfl
    · exact a1 hz
    · exact a2 hz
    · exact a3 hz

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **`chain6_cross` se decide con la máquina sobre su preprocesada**, sin hipótesis (la máquina sobre `chain6_cross`
tal cual no es exacta en la condición fuerte: 8 triángulos de más en las llegadas, v223). -/
theorem spineVerdictOn_pre_chain6X : SpineVerdictOn chain6P ↔ Satisfiable chain6X :=
  spineVerdictOn_iff_of_pre renaming_chain6 bounded_chain6P chainOrd_chain6P

end MachineOn

end AbsSatBingo.Model
