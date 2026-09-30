-- lean/improves_bingo/AbsSatBingo/Model/PreClause.lean
import AbsSatBingo.Model.LiveDriver
import AbsSatBingo.Model.CliqueSplit
import AbsSatBingo.Model.EdgeCliqueUp

/-!
# Antes de las cláusulas

Hasta la fusión central el mapa no tiene ventanas prohibidas y los únicos requisitos son los de negación (la cima del
propio remitente). Allí una selección válida es exactamente la rama de una asignación (`validSel_pid`,
`pid_of_validSel`), y un nodo solo depende de las variables de su ventana (`pid_agree`, `vars_of_pid_eq`). Con eso,
**parcheo** (`patch`): asignaciones que concuerdan dos a dos en las variables que cada una fija se juntan en una sola.
Es Helly para asignaciones parciales, y es lo que hace que tres nodos compatibles dos a dos estén en una misma rama.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (shiftPid)

namespace PreClause

open GPathB Driver Machine CliqueSplit

variable {φ : Cnf}

-- ============================================================
-- Selecciones y asignaciones
-- ============================================================

/-- La asignación de una selección: el valor de cada variable en su paso. -/
def aOf (S : Int → PathNodeId) : Assign := fun v => (S (varStep v)).id.index == 1

theorem shift_pid (a : Assign) {j : Int} (hj : 1 ≤ j) :
    shiftPid (pidOfAssign φ a (j - 1)) (selOfAssign φ a j) = pidOfAssign φ a j := by
  simp only [shiftPid, pidOfAssign]
  congr 1
  · rw [if_pos (by omega)]
  · by_cases h : 0 < j - 1
    · rw [if_pos h, if_pos (by omega), show j - 1 - 1 = j - 2 by omega]
    · rw [if_neg h, if_neg (by omega)]

theorem mid_lt_stepCount (φ : Cnf) : midFusion φ < stepCount φ := by
  unfold midFusion stepCount; omega

/-- **Toda asignación da una selección válida** hasta la fusión central (no hay ventanas prohibidas). -/
theorem validSel_pid (hbd : Bounded φ) (a : Assign) {t : Int} (ht : t ≤ midFusion φ) :
    ValidSel φ t (pidOfAssign φ a) := by
  have hsc := mid_lt_stepCount φ
  refine ⟨fun j _ _ => selOfAssign_step φ a j, ?_, fun j h1 _ => shift_pid a h1, ?_, ?_, ?_⟩
  · simp [pidOfAssign, selOfAssign, root]
  · intro j h1 h2
    have := selOfAssign_son φ a (j - 1) (by omega) (by omega)
    rw [show j - 1 + 1 = j by omega] at this
    exact this
  · intro j _ _ r hr _ _
    exact reqSat_selOfAssign φ hbd a j r hr
  · intro j _ h2
    have hs : (pidOfAssign φ a j).id.step = j := selOfAssign_step φ a j
    unfold isProhibited isL3
    rw [hs, decide_eq_false (show ¬ midFusion φ < j by omega)]
    rfl

theorem bit_index {i : Int} (h : i = 0 ∨ i = 1) : bit (i == 1) = i := by
  rcases h with rfl | rfl <;> rfl

/-- **Toda selección válida es la rama de su asignación**, hasta la fusión central. -/
theorem pid_of_validSel {t : Int} {S : Int → PathNodeId} (hv : ValidSel φ t S) (ht : t ≤ midFusion φ) :
    ∀ k, 0 ≤ k → k ≤ t → S k = pidOfAssign φ (aOf S) k := by
  have key : ∀ n : Nat, (n : Int) ≤ t → S n = pidOfAssign φ (aOf S) n := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [show ((0 : Nat) : Int) = 0 by rfl, hv.root]
      simp [pidOfAssign, selOfAssign, root]
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hj1 : (1 : Int) ≤ ((n + 1 : Nat) : Int) := by omega
      have hsh := hv.shift _ hj1 hn
      have hson := hv.son _ hj1 hn
      rw [show ((n + 1 : Nat) : Int) - 1 = (n : Int) by push_cast; omega] at hsh hson
      rw [ih'] at hsh hson
      -- el id del paso n + 1
      suffices hid : (S ((n + 1 : Nat) : Int)).id = selOfAssign φ (aOf S) ((n + 1 : Nat) : Int) by
        rw [← hsh, hid, show (n : Int) = ((n + 1 : Nat) : Int) - 1 by push_cast; omega]
        exact shift_pid _ hj1
      have hstep : (S ((n + 1 : Nat) : Int)).id.step = ((n + 1 : Nat) : Int) := hv.step _ (by omega) hn
      have hsn : (pidOfAssign φ (aOf S) (n : Int)).id.step = n := selOfAssign_step φ _ _
      unfold sonsOfMap at hson
      have hm : ((n + 1 : Nat) : Int) ≤ midFusion φ := by omega
      by_cases hodd : 0 < (n : Int) ∧ (n : Int) < midFusion φ ∧ (n : Int) % 2 = 1
      · -- paso de negación: el hijo del valor de la variable
        rw [hsn, if_pos hodd, List.mem_singleton] at hson
        rw [hson]
        have hlt : ((n + 1 : Nat) : Int) < midFusion φ := by unfold midFusion at hm ⊢; omega
        unfold selOfAssign
        rw [if_neg (by omega), if_pos hlt, if_neg (by omega)]
        have hn' : (pidOfAssign φ (aOf S) (n : Int)).id = ⟨n, bit (aOf S (varOfStep n))⟩ := by
          show selOfAssign φ (aOf S) (n : Int) = _
          unfold selOfAssign; rw [if_neg (by omega), if_pos hodd.2.1, if_pos hodd.2.2]
        rw [hn', bit_not]
        simp only [NodeId.mk.injEq]
        refine ⟨by push_cast; omega, ?_⟩
        congr 3
        unfold varOfStep; omega
      · rw [hsn, if_neg hodd] at hson
        by_cases hmid : ((n + 1 : Nat) : Int) = midFusion φ
        · -- la fusión central
          rw [show (n : Int) + 1 = midFusion φ by push_cast at hmid; omega,
            mapNodes_fusion φ _ (Or.inr (Or.inl rfl)), List.mem_singleton] at hson
          rw [hson]
          unfold selOfAssign
          rw [if_neg (by omega), if_neg (by omega), if_pos hmid, hmid]
        · -- paso de variable: los dos valores
          have hlt : ((n + 1 : Nat) : Int) < midFusion φ := by omega
          have hodd' : ((n + 1 : Nat) : Int) % 2 = 1 := by
            have : ¬ ((0 : Int) < n ∧ (n : Int) < midFusion φ ∧ (n : Int) % 2 = 1) := hodd
            unfold midFusion at hlt this; omega
          rw [mapNodes_two φ _ (by omega) (by push_cast at hmid; omega) (by unfold midFusion at hlt; unfold fusionTop; omega)]
            at hson
          have hidx : (S ((n + 1 : Nat) : Int)).id.index = 0 ∨ (S ((n + 1 : Nat) : Int)).id.index = 1 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hson
            rcases hson with h | h <;> rw [h] <;> simp
          unfold selOfAssign
          rw [if_neg (by omega), if_pos hlt, if_pos hodd']
          have hv' : varStep (varOfStep ((n + 1 : Nat) : Int)) = ((n + 1 : Nat) : Int) := by
            unfold varStep varOfStep; omega
          show _ = NodeId.mk ((n + 1 : Nat) : Int)
            (bit ((S (varStep (varOfStep ((n + 1 : Nat) : Int)))).id.index == 1))
          rw [hv', bit_index hidx]
          exact nodeId_eq hstep rfl
  intro k hk0 hkt
  have := key k.toNat (by omega)
  rwa [Int.toNat_of_nonneg hk0] at this

-- ============================================================
-- Un nodo solo depende de las variables de su ventana
-- ============================================================

/-- `v` es una variable de la ventana del paso `k`: la de `k`, `k - 1` o `k - 2` (entre la raíz y la fusión). -/
def VarsAt (φ : Cnf) (k : Int) (v : Nat) : Prop :=
  ∃ i, (i = k ∨ i = k - 1 ∨ i = k - 2) ∧ 0 < i ∧ i < midFusion φ ∧ v = varOfStep i

theorem sel_local {a a' : Assign} {i : Int} (hi : i ≤ midFusion φ)
    (h : 0 < i → i < midFusion φ → a (varOfStep i) = a' (varOfStep i)) : selOfAssign φ a i = selOfAssign φ a' i := by
  unfold selOfAssign
  by_cases h0 : i ≤ 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases hm : i < midFusion φ
    · rw [if_pos hm, if_pos hm, h (by omega) hm]
    · rw [if_neg hm, if_neg hm, if_pos (by omega), if_pos (by omega)]

theorem sel_inj {a a' : Assign} {i : Int} (h0 : 0 < i) (hm : i < midFusion φ)
    (h : selOfAssign φ a i = selOfAssign φ a' i) : a (varOfStep i) = a' (varOfStep i) := by
  unfold selOfAssign at h
  rw [if_neg (show ¬ i ≤ 0 by omega), if_neg (show ¬ i ≤ 0 by omega), if_pos hm, if_pos hm] at h
  split at h
  · simp only [NodeId.mk.injEq, true_and] at h
    cases hb : a (varOfStep i) <;> cases hb' : a' (varOfStep i) <;> simp_all [bit]
  · simp only [NodeId.mk.injEq, true_and] at h
    cases hb : a (varOfStep i) <;> cases hb' : a' (varOfStep i) <;> simp_all [bit]

/-- **Un nodo de la rama solo depende de las variables de su ventana.** -/
theorem pid_agree {a a' : Assign} {k : Int} (hk : k ≤ midFusion φ) (h : ∀ v, VarsAt φ k v → a v = a' v) :
    pidOfAssign φ a k = pidOfAssign φ a' k := by
  have hs : ∀ i, (i = k ∨ i = k - 1 ∨ i = k - 2) → selOfAssign φ a i = selOfAssign φ a' i := by
    intro i hi
    exact sel_local (by omega) (fun h0 hm => h _ ⟨i, hi, h0, hm, rfl⟩)
  unfold pidOfAssign
  rw [hs k (Or.inl rfl), hs (k - 1) (Or.inr (Or.inl rfl)), hs (k - 2) (Or.inr (Or.inr rfl))]

/-- **Y las determina**: dos ramas con el mismo nodo en `k` coinciden en las variables de su ventana. -/
theorem vars_of_pid_eq {a a' : Assign} {k : Int} (h : pidOfAssign φ a k = pidOfAssign φ a' k) {v : Nat}
    (hv : VarsAt φ k v) : a v = a' v := by
  obtain ⟨i, hi, h0, hm, rfl⟩ := hv
  apply sel_inj h0 hm
  unfold pidOfAssign at h
  simp only [PathNodeId.mk.injEq] at h
  obtain ⟨e0, e1, e2⟩ := h
  rcases hi with rfl | rfl | rfl
  · exact e0
  · rw [if_pos (by omega), if_pos (by omega)] at e1; exact Option.some.inj e1
  · rw [if_pos (by omega), if_pos (by omega)] at e2; exact Option.some.inj e2

-- ============================================================
-- Parcheo
-- ============================================================

/-- **Parcheo** (Helly para asignaciones parciales): asignaciones que concuerdan dos a dos en las variables que cada
una fija se juntan en una sola que concuerda con todas. -/
theorem patch {ι : Type} (l : List ι) (A : ι → Assign) (V : ι → Nat → Prop)
    (h : ∀ i ∈ l, ∀ j ∈ l, ∀ v, V i v → V j v → A i v = A j v) :
    ∃ a : Assign, ∀ i ∈ l, ∀ v, V i v → a v = A i v := by
  classical
  refine ⟨fun v => if hv : ∃ i ∈ l, V i v then A hv.choose v else false, ?_⟩
  intro i hi v hvi
  have hex : ∃ i ∈ l, V i v := ⟨i, hi, hvi⟩
  simp only [dif_pos hex]
  exact h _ hex.choose_spec.1 i hi v hex.choose_spec.2 hvi

end PreClause

end AbsSatBingo.Model
