-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainOrdI.lean
import AbsSatBingo.Model.ForbidOnChainOrd

/-!
# Una cadena en orden de doce bloques: `chain12_order`

`scripts/cnf/long/chain12_order.cnf` (variables desde 0): `p = x0, q = x1`, separadores `s_i = x(2i)` (`1 ≤ i ≤ 11`),
de dentro `r_i = x(2i+1)` (`1 ≤ i ≤ 10`), `y = x23, w = x24`;
`(p ∨ q ∨ s1) ∧ ⋀_{i=1}^{10} (¬s_i ∨ r_i ∨ s_{i+1}) ∧ (¬s11 ∨ y ∨ w)`.

Está en la clase `ChainOrdN` (comprobado con `decide`): **`machineExact_chain12O`** y **`reader_sep_chain12O`**, sin
hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

/-- Las cláusulas de en medio. -/
def c12mid (i : Nat) : Clause := ⟨⟨2 * i, false⟩, ⟨2 * i + 1, true⟩, ⟨2 * i + 2, true⟩⟩

/-- **`chain12_order`.** -/
def chain12O : Cnf :=
  ⟨25, [⟨⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩⟩] ++ (List.range' 1 10).map c12mid ++ [⟨⟨22, false⟩, ⟨23, true⟩, ⟨24, true⟩⟩]⟩

/-- Las zonas: bloques `0 … 11`, separadores `12 + i`. -/
def vals12 : List Nat := [0, 0, 13, 1, 14, 2, 15, 3, 16, 4, 17, 5, 18, 6, 19, 7, 20, 8, 21, 9, 22, 10, 23, 11, 11]

def sv12 (k : Nat) : Nat := 2 * k

theorem bounded_chain12O : Bounded chain12O := by
  unfold Bounded Clause.Bounded
  decide

namespace GPathB

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 20000

theorem chainOrd_chain12O : ChainOrdN chain12O 12 (zoneV 12 vals12) sv12 := by
  refine ⟨chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    fun k h1 h2 => ?_, rfl, fun j c hj => ?_, fun z p h1 h2 hz => ?_, fun j c hj z p h1 h2 hz hcv => ?_⟩
  · have h : ∀ k, k < 12 → 1 ≤ k → zoneV 12 vals12 (sv12 k) = 12 + k := by decide
    exact h k h2 h1
  · have hm : ∀ c ∈ chain12O.clauses, ∃ j, j < 12 ∧ chain12O.clauses[j]? = some c ∧ ClIn (BlkN 12 (zoneV 12 vals12) j) c := by
      decide
    have hjl : j < 12 := by
      by_cases h : j < 12
      · exact h
      · rw [List.getElem?_eq_none (by simp [chain12O]; omega)] at hj; cases hj
    have all : ∀ j, j < 12 → ∀ c, chain12O.clauses[j]? = some c → ClIn (BlkN 12 (zoneV 12 vals12) j) c := by decide
    exact all j hjl c hj
  · have hzl : z < vals12.length := zoneV_small hz (by omega)
    have h : ∀ z, z < vals12.length → ∀ p, p < 12 → 1 ≤ p → p + 1 < 12 → zoneV 12 vals12 z = p →
        1 ≤ z ∧ z + 1 < 25 ∧ (z - 1 = sv12 p ∨ z - 1 = sv12 (p + 1)) ∧ (z + 1 = sv12 p ∨ z + 1 = sv12 (p + 1)) := by
      decide
    exact h z hzl p (by omega) h1 h2 hz
  · have hc : c ∈ chain12O.clauses := List.mem_of_getElem? hj
    have h : ∀ c ∈ chain12O.clauses, ∀ p, p < 12 → 1 ≤ p → p + 1 < 12 →
        (zoneV 12 vals12 c.l1.v = p → c.l2.v = c.l1.v ∧ (c.l1.v = sv12 p ∨ c.l1.v = sv12 (p + 1)) ∧
          (c.l3.v = sv12 p ∨ c.l3.v = sv12 (p + 1))) ∧
        (zoneV 12 vals12 c.l2.v = p → c.l2.v = c.l2.v ∧ (c.l1.v = sv12 p ∨ c.l1.v = sv12 (p + 1)) ∧
          (c.l3.v = sv12 p ∨ c.l3.v = sv12 (p + 1))) ∧
        (zoneV 12 vals12 c.l3.v = p → c.l2.v = c.l3.v ∧ (c.l1.v = sv12 p ∨ c.l1.v = sv12 (p + 1)) ∧
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

/-- **La máquina `:on` es exacta en `chain12_order`.** -/
theorem machineExact_chain12O : MachineExact chain12O :=
  machineExact_of_chainOrd bounded_chain12O chainOrd_chain12O

/-- **El lector por separadores no se atasca en `chain12_order`**, en cualquier orden de los separadores. -/
theorem reader_sep_chain12O {ord : List Nat} (hord : ∀ q ∈ ord, 1 ≤ q ∧ q < 12)
    (hall : ∀ q, 1 ≤ q → q < 12 → q ∈ ord) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on chain12O)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') (hsf : SepFirst chain12O (ord.map sv12) R) :
    g'.isValid = true ∧ ∃ a, Sat a chain12O ∧ (∀ r ∈ R, selOfAssign chain12O a r.step = r) ∧
      CT g' (pidOfAssign chain12O a) :=
  reader_sep_of_chainOrd bounded_chain12O chainOrd_chain12O hord hall hkv hr hsf

end MachineOn

end AbsSatBingo.Model
