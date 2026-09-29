-- lean/improves_bingo/AbsSatBingo/Model/PinKeeps.lean
import AbsSatBingo.Model.ReaderStuck
import AbsSatBingo.Model.LineInduction

/-!
# `PinKeeps`: qué pide exactamente y dónde está

`ReaderStuck.lean` redujo la completitud del lector a `PinKeeps` (ningún pin válido pierde todas las soluciones de
un estado que las tiene). Aquí:

* **Las camarillas suben** (`carried_of_sub`): una camarilla de un estado por debajo lo es del de arriba (con ids
  únicos arriba). Con eso, las camarillas del pin de `q` son **exactamente** las camarillas de `h` que pasan por el
  nodo de mapa de `q` (`carried_pin_iff`).
* **La pérdida, en términos del estado de antes** (`pinLoss_iff`): un pin pierde todas las soluciones si y solo si
  `h` lleva una camarilla, el review deja el pin válido, y **ninguna camarilla de `h` pasa por el nodo de mapa de
  `q`**. Es decir, `PinKeeps h` es **`MapExact h`**: el review, al fijar un nodo de mapa, lo invalida si ninguna
  solución pasa por él (`pinKeeps_iff_mapExact`). Es la exactitud del review restringida a un solo pin y a la
  existencia (no a cada arista, como `KernelExact`).
* **Dónde está** (`Machine.pinKeeps_of_hypsPin`): bajo `PinFree`, la hipótesis del teorema principal
  (`readerVerdict_iff_of_pinFree`), todo estado del lector cumple `PinKeeps`. Así que `PinKeeps` queda entre el
  veredicto y `PinFree`, y del lado del lector no queda contenido: lo que falta es de la máquina.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

open Driver

-- ============================================================
-- Las camarillas suben
-- ============================================================

/-- **Una camarilla de un estado por debajo lo es del de arriba** (con ids únicos arriba). -/
theorem carried_of_sub {h g : GPathB} {S : Int → PathNodeId} (hs : Sub h g) (hnd : NodupIds g)
    (hc : Carried h S) : Carried g S := by
  refine ⟨fun k h0 h1 => hc.step k h0 (by rw [hs.step]; exact h1),
    fun k h0 h1 => hs.alive _ (hc.alive k h0 (by rw [hs.step]; exact h1)),
    fun k l h0 h1 h2 h3 => hs.adj _ _ (hc.adj k l h0 (by rw [hs.step]; exact h1) h2 (by rw [hs.step]; exact h3)),
    fun h0 => hc.root (by rw [hs.step]; exact h0), ?_⟩
  intro k h0 h1
  obtain ⟨n, hn, hp, hsn⟩ := hc.node k h0 (by rw [hs.step]; exact h1)
  obtain ⟨m, hm, hpm, hsm⟩ := up_doc hs hnd hn
  exact ⟨m, hm, fun hk => hpm _ (hp hk), fun hk => hsm _ (hsn (by rw [hs.step]; exact hk))⟩

/-- **Las camarillas del pin de `b` son las de `g` que pasan por `b`.** -/
theorem carried_pin_iff {g : GPathB} {S : Int → PathNodeId} (hd : AliveDocs g) (hnd : NodupIds g) {b : NodeId}
    (h0 : 0 ≤ b.step) (h1 : b.step < g.current_step) :
    Carried (g.filterAll [b]) S ↔ Carried g S ∧ (S b.step).id = b := by
  constructor
  · intro hc
    have hsub := (shrinks_filterAll g [b]).1
    have hcs : b.step < (g.filterAll [b]).current_step := by rw [hsub.step]; exact h1
    refine ⟨carried_of_sub hsub hnd hc, ?_⟩
    exact pinned_filterAll_list hd [b] (isValid_of_carried hc) b (List.mem_singleton_self b) (S b.step)
      (hc.alive _ h0 hcs) (hc.step _ h0 hcs)
  · rintro ⟨hc, hb⟩
    exact carried_filterAll hc [b] (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      intro _ _
      exact hb)

-- ============================================================
-- La pérdida, en términos del estado de antes
-- ============================================================

/-- **El review es exacto para un pin**: si fijar el nodo de mapa de un vivo deja el estado válido, alguna camarilla
pasa por ese nodo de mapa. -/
def MapExact (h : GPathB) : Prop :=
  (∃ S, Carried h S) → ∀ q ∈ h.alive, (h.filterAll [q.id]).isValid = true →
    ∃ S, Carried h S ∧ (S q.id.step).id = q.id

/-- Los vivos tienen su paso en rango (con documentos y `Below`/`AboveZero`). -/
theorem step_range_of_alive {h : GPathB} (hd : AliveDocs h) (hb : Machine.Below h) (hz : AboveZero h)
    {q : PathNodeId} (hq : q ∈ h.alive) : 0 ≤ q.id.step ∧ q.id.step < h.current_step := by
  obtain ⟨n, hn, hid⟩ := hd q hq
  have := hb n hn
  have := hz n hn
  rw [hid] at *
  exact ⟨by assumption, by assumption⟩

/-- **Un pin pierde todas las soluciones si y solo si ninguna camarilla pasa por su nodo de mapa y el review no lo
nota.** -/
theorem pinLoss_iff {h : GPathB} (hd : AliveDocs h) (hnd : NodupIds h) {q : PathNodeId} (h0 : 0 ≤ q.id.step)
    (h1 : q.id.step < h.current_step) :
    PinLoss h q ↔ (∃ S, Carried h S) ∧ (h.filterAll [q.id]).isValid = true ∧
      ¬ ∃ S, Carried h S ∧ (S q.id.step).id = q.id := by
  unfold PinLoss
  constructor
  · rintro ⟨hc, hv, hno⟩
    refine ⟨hc, hv, fun ⟨S, hS⟩ => hno ⟨S, (carried_pin_iff hd hnd h0 h1).mpr hS⟩⟩
  · rintro ⟨hc, hv, hno⟩
    refine ⟨hc, hv, fun ⟨S, hS⟩ => hno ⟨S, (carried_pin_iff hd hnd h0 h1).mp hS⟩⟩

/-- **`PinKeeps` es `MapExact`.** -/
theorem pinKeeps_iff_mapExact {h : GPathB} (hd : AliveDocs h) (hnd : NodupIds h) (hb : Machine.Below h)
    (hz : AboveZero h) : PinKeeps h ↔ MapExact h := by
  constructor
  · intro hpk hc q hq hv
    obtain ⟨h0, h1⟩ := step_range_of_alive hd hb hz hq
    obtain ⟨S, hS⟩ := hpk hc q hq hv
    exact ⟨S, (carried_pin_iff hd hnd h0 h1).mp hS⟩
  · intro hme hc q hq hv
    obtain ⟨h0, h1⟩ := step_range_of_alive hd hb hz hq
    obtain ⟨S, hS⟩ := hme hc q hq hv
    exact ⟨S, (carried_pin_iff hd hnd h0 h1).mpr hS⟩

end GPathB

-- ============================================================
-- Dónde está: bajo PinFree
-- ============================================================

namespace Machine

open GPathB Driver

/-- Bajo `PinFree`, ningún estado que visita el lector es un zombi (el cuerpo de `readerVerdict_iff_of_pinFree`). -/
theorem noZombie_visited_of_hypsPin {φ : Cnf} (H : HypsPin φ) :
    ∀ kv ∈ run φ, ∀ h, Visited kv.2 h → NoZombie h := by
  intro kv hkv h hvis
  have hpos := stepCount_pos φ
  have hinv := lineInv_steps H (stepCount φ - 1).toNat
  have hrun : run φ = steps φ (stepCount φ - 1).toNat (init φ) := rfl
  rw [← hrun, show ((stepCount φ - 1).toNat : Int) + 1 = stepCount φ by rw [Int.toNat_of_nonneg (by omega)]; omega]
    at hinv
  obtain ⟨hl, hent, _, _⟩ := hinv
  have hok := hl kv hkv
  obtain ⟨⟨hbk, _⟩, htop⟩ := hent kv hkv
  have hv := vInv_visited_top htop hbk.1 hbk.2.1 hok.docs h hvis
  have hcs : 2 ≤ kv.2.current_step := by rw [hok.step]; unfold stepCount; omega
  have hc := Final.cInv_visited hok.docs hbk.1 hok.below hbk.2.2.2 hcs h hvis
  exact fun hval => noZombie_of_topExact hv.1 (hc.2.2.2.2.2 hval) (by have := hc.2.2.2.2.1; omega) hval

/-- **`PinFree` ⟹ `PinKeeps`** en todo estado del lector: el pin de un estado visitado es visitado, y no es un
zombi. -/
theorem pinKeeps_of_hypsPin {φ : Cnf} (H : HypsPin φ) :
    ∀ kv ∈ run φ, ∀ h, Visited kv.2 h → PinKeeps h := by
  intro kv hkv h hvis _ q _ hv
  exact noZombie_visited_of_hypsPin H kv hkv _ (Visited.pin q hvis) hv

end Machine

end AbsSatBingo.Model
