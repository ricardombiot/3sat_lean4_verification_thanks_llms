-- lean/improves_bingo/AbsSatBingo/Model/ReaderStuck.lean
import AbsSatBingo.Model.Machine

/-!
# El lector atascado: la reducción por contrapositivo

`Reader.lean` demuestra la dirección directa: sin zombis, el lector termina (`readG_isSome_of_noZombie`). Aquí va el
contrapositivo, en dos formas, y la hipótesis de un paso que sale de él.

* **El atasco es un zombi** (`not_carried_of_stuck`, `exists_zombie_of_readG_none`). Si el lector se para, lo hace
  en un estado **válido** (solo visita estados válidos) en el que ningún pin del primer paso con elección queda
  válido. Ese estado no lleva ninguna camarilla: si llevara una, fijar su nodo del paso la conservaría
  (`carried_filterAll`). *Atasco ⟹ estado válido sin soluciones.*
* **La primera pérdida** (`exists_pinLoss_of_readG_none`). Si el estado de partida lleva una camarilla y el lector se
  atasca, en algún punto de su recorrido hay un estado con camarilla y un pin **válido** que deja un estado sin
  ninguna (`PinLoss`). Es el mínimo contraejemplo: el primer paso en el que se pierden todas las soluciones.
* **La hipótesis de un paso** (`PinKeeps`). Su negación: desde un estado con camarilla, todo pin de un vivo que el
  review deja válido conserva alguna. Es más débil que `NoZombie` (solo mira estados con camarilla y un pin), y
  basta (`readG_isSome_of_pinKeeps`, `readerVerdict_of_sat_pinKeeps`).

A nivel de la máquina (`Machine.pinLoss_of_sat_of_readerFalse`, `Machine.zombie_of_sat_of_readerFalse`): si `φ` es
satisfacible y el lector dice UNSAT, el estado de la línea final que lleva la solución arranca al lector con una
camarilla, y el lector la pierde en un pin válido y se para en un zombi.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

open Driver

-- ============================================================
-- Definiciones
-- ============================================================

/-- **El lector se atasca en `h`**: hay un primer paso con elección y ningún pin en él deja el estado válido. -/
def Stuck (h : GPathB) : Prop := ∃ k, firstChoice h = some k ∧ tryPins h k = none

/-- **Un pin que pierde todas las soluciones**: `h` lleva una camarilla, fijar `q` deja el estado válido, y el
resultado no lleva ninguna. -/
def PinLoss (h : GPathB) (q : PathNodeId) : Prop :=
  (∃ S, Carried h S) ∧ (h.filterAll [q.id]).isValid = true ∧ ¬ ∃ S', Carried (h.filterAll [q.id]) S'

/-- **Ningún pin válido pierde todas las soluciones** desde `h`. -/
def PinKeeps (h : GPathB) : Prop :=
  (∃ S, Carried h S) → ∀ q ∈ h.alive, (h.filterAll [q.id]).isValid = true → ∃ S', Carried (h.filterAll [q.id]) S'

theorem pinKeeps_of_noZombie {h : GPathB} (hnz : ∀ q ∈ h.alive, NoZombie (h.filterAll [q.id])) : PinKeeps h :=
  fun _ q hq hv => hnz q hq hv

-- ============================================================
-- Un paso del lector
-- ============================================================

theorem firstChoice_spec {h : GPathB} {k : Int} (hk : firstChoice h = some k) :
    choiceAt h k = true ∧ 0 ≤ k ∧ k < h.current_step := by
  have hr := intRange_bounds (List.mem_of_find?_eq_some hk)
  exact ⟨List.find?_some hk, hr.1, by omega⟩

/-- Fijar el nodo de una camarilla en su paso la conserva. -/
theorem carried_pin {h : GPathB} {S : Int → PathNodeId} (hS : Carried h S) {k : Int} (h0 : 0 ≤ k)
    (hk : k < h.current_step) : Carried (h.filterAll [(S k).id]) S :=
  carried_filterAll hS [(S k).id] (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    intro _ _
    rw [hS.step k h0 hk])

/-- Con una camarilla, algún pin del paso `k` queda válido: el de su nodo. -/
theorem tryPins_isSome_of_carried {h : GPathB} {S : Int → PathNodeId} (hS : Carried h S) {k : Int} (h0 : 0 ≤ k)
    (hk : k < h.current_step) : (tryPins h k).isSome = true := by
  unfold tryPins
  apply List.findSome?_isSome_iff.mpr
  refine ⟨S k, List.mem_filter.mpr ⟨hS.alive k h0 hk, by simp [hS.step k h0 hk]⟩, ?_⟩
  simp [isValid_of_carried (carried_pin hS h0 hk)]

/-- Lo que devuelve `tryPins`: el pin válido de un vivo del paso. -/
theorem tryPins_spec {h h' : GPathB} {k : Int} (hh : tryPins h k = some h') :
    ∃ q, q ∈ h.alive ∧ q.id.step = k ∧ h' = h.filterAll [q.id] ∧ h'.isValid = true := by
  unfold tryPins at hh
  obtain ⟨q, hq, hqf⟩ := List.exists_of_findSome?_eq_some hh
  have hqk := List.mem_filter.mp hq
  dsimp only at hqf
  split at hqf
  · rename_i hvq
    cases hqf
    exact ⟨q, hqk.1, by simpa using hqk.2, rfl, hvq⟩
  · exact absurd hqf (by simp)

/-- El pin en un paso con elección baja la medida: otro vivo del paso es de otro nodo de mapa. -/
theorem measure_pin_lt {h : GPathB} (hv : h.isValid = true) (hdocs : AliveDocs h) {k : Int}
    (hck : choiceAt h k = true) {q : PathNodeId} (hqs : q.id.step = k) :
    (h.filterAll [q.id]).measure < h.measure := by
  obtain ⟨a, b, ha, hb, has, hbs, hab⟩ := choiceAt_spec hck
  have hlt : (h.filterRequire q.id).measure < h.measure := by
    by_cases haq : a.id = q.id
    · exact measure_filterRequire_lt hv hdocs hb (by rw [hbs, hqs]) (fun hbq => hab (haq.trans hbq.symm))
    · exact measure_filterRequire_lt hv hdocs ha (by rw [has, hqs]) haq
  have hrev := (shrinks_review (h.filterRequire q.id)).2
  show (review ([q.id].foldl filterRequire h)).measure < h.measure
  simp only [List.foldl_cons, List.foldl_nil]
  omega

-- ============================================================
-- El atasco es un zombi
-- ============================================================

/-- **Un estado atascado no lleva ninguna camarilla.** -/
theorem not_carried_of_stuck {h : GPathB} (hs : Stuck h) : ¬ ∃ S, Carried h S := by
  rintro ⟨S, hS⟩
  obtain ⟨k, hk, hnone⟩ := hs
  obtain ⟨_, h0, hlt⟩ := firstChoice_spec hk
  have := tryPins_isSome_of_carried hS h0 hlt
  rw [hnone] at this
  exact absurd this (by simp)

/-- Si el bucle falla desde un estado válido, falla en un estado visitado, válido y atascado (el combustible no se
agota: la medida lo acota). -/
theorem readLoop_none_stuck (g₀ : GPathB) :
    ∀ (n : Nat) (h : GPathB), Visited g₀ h → h.isValid = true → AliveDocs h → h.measure ≤ n →
      readLoop n h = none → ∃ h', Visited g₀ h' ∧ h'.isValid = true ∧ Stuck h' := by
  intro n
  induction n with
  | zero =>
    intro h _ _ _ hm hnone
    simp only [readLoop] at hnone
    cases hch : hasChoice h
    · rw [hch] at hnone
      exact absurd hnone (by simp)
    · exfalso
      unfold hasChoice at hch
      obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hch
      obtain ⟨q, _, hq, _⟩ := choiceAt_spec hk
      have := measure_pos_of_mem hq
      omega
  | succ n ih =>
    intro h hvis hv hdocs hm hnone
    simp only [readLoop] at hnone
    cases hfc : firstChoice h with
    | none =>
      rw [hfc] at hnone
      exact absurd hnone (by simp)
    | some k =>
      rw [hfc] at hnone
      cases htp : tryPins h k with
      | none => exact ⟨h, hvis, hv, k, hfc, htp⟩
      | some h' =>
        simp only [htp] at hnone
        obtain ⟨hck, _, _⟩ := firstChoice_spec hfc
        obtain ⟨q, _, hqs, rfl, hvq⟩ := tryPins_spec htp
        have := measure_pin_lt hv hdocs hck hqs
        exact ih _ (Visited.pin q hvis) hvq (aliveDocs_filterAll hdocs _) (by omega) hnone

/-- **Atasco ⟹ estado válido sin soluciones.** Si el estado de partida revisado es válido y el lector falla, hay un
estado que visita, válido, que no lleva ninguna camarilla. -/
theorem exists_zombie_of_readG_none (g₀ : GPathB) (hv : (reviewAll g₀).isValid = true) (hdocs : AliveDocs g₀)
    (hnone : readG g₀ = none) : ∃ h, Visited g₀ h ∧ h.isValid = true ∧ ¬ ∃ S, Carried h S := by
  unfold readG at hnone
  simp only [hv, if_true] at hnone
  obtain ⟨h, hvis, hvh, hs⟩ := readLoop_none_stuck g₀ _ _ Visited.start hv
    (aliveDocs_review (aliveDocs_dirty hdocs _)) (Nat.le_refl _) hnone
  exact ⟨h, hvis, hvh, not_carried_of_stuck hs⟩

-- ============================================================
-- La primera pérdida
-- ============================================================

/-- **El lector termina si arranca con una camarilla y ningún pin válido la pierde entera.** -/
theorem readLoop_isSome_of_pinKeeps (g₀ : GPathB) (hpk : ∀ h, Visited g₀ h → PinKeeps h) :
    ∀ (n : Nat) (h : GPathB), Visited g₀ h → (∃ S, Carried h S) → AliveDocs h → h.measure ≤ n →
      (readLoop n h).isSome = true := by
  intro n
  induction n with
  | zero =>
    intro h _ _ _ hm
    simp only [readLoop]
    cases hch : hasChoice h
    · rfl
    · exfalso
      unfold hasChoice at hch
      obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hch
      obtain ⟨q, _, hq, _⟩ := choiceAt_spec hk
      have := measure_pos_of_mem hq
      omega
  | succ n ih =>
    intro h hvis hc hdocs hm
    obtain ⟨S, hS⟩ := hc
    simp only [readLoop]
    cases hfc : firstChoice h with
    | none => rfl
    | some k =>
      obtain ⟨hck, h0, hlt⟩ := firstChoice_spec hfc
      obtain ⟨h', hh'⟩ := Option.isSome_iff_exists.mp (tryPins_isSome_of_carried hS h0 hlt)
      simp only [hh']
      obtain ⟨q, hq, hqs, rfl, hvq⟩ := tryPins_spec hh'
      have := measure_pin_lt (isValid_of_carried hS) hdocs hck hqs
      exact ih _ (Visited.pin q hvis) (hpk h hvis ⟨S, hS⟩ q hq hvq) (aliveDocs_filterAll hdocs _) (by omega)

/-- **La completitud del lector, reducida a `PinKeeps`.** -/
theorem readG_isSome_of_pinKeeps (g₀ : GPathB) (hc : ∃ S, Carried (reviewAll g₀) S) (hdocs : AliveDocs g₀)
    (hpk : ∀ h, Visited g₀ h → PinKeeps h) : (readG g₀).isSome = true := by
  obtain ⟨S, hS⟩ := hc
  unfold readG
  simp only [isValid_of_carried hS, if_true]
  exact readLoop_isSome_of_pinKeeps g₀ hpk _ _ Visited.start ⟨S, hS⟩
    (aliveDocs_review (aliveDocs_dirty hdocs _)) (Nat.le_refl _)

/-- **La primera pérdida.** Si el lector arranca con una camarilla y falla, en su recorrido hay un estado con
camarilla y un vivo cuyo pin queda válido y sin ninguna. -/
theorem exists_pinLoss_of_readG_none (g₀ : GPathB) (hc : ∃ S, Carried (reviewAll g₀) S) (hdocs : AliveDocs g₀)
    (hnone : readG g₀ = none) : ∃ h q, Visited g₀ h ∧ q ∈ h.alive ∧ PinLoss h q := by
  refine Classical.byContradiction fun hno => ?_
  have hpk : ∀ h, Visited g₀ h → PinKeeps h := by
    intro h hvis hch q hq hv
    exact Classical.byContradiction fun hz => hno ⟨h, q, hvis, hq, hch, hv, hz⟩
  have := readG_isSome_of_pinKeeps g₀ hc hdocs hpk
  rw [hnone] at this
  exact absurd this (by simp)

end GPathB

-- ============================================================
-- A nivel de la máquina
-- ============================================================

namespace Machine

open GPathB Driver

/-- El estado de la línea final que lleva una solución arranca al lector con una camarilla. -/
theorem start_of_sat (φ : Cnf) (hb : Bounded φ) (hs : Satisfiable φ) :
    ∃ kv ∈ run φ, (∃ S, Carried (reviewAll kv.2) S) ∧ AliveDocs kv.2 := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨g, hf, hc, hok⟩ := run_carries φ hb a ha
  exact ⟨_, List.mem_of_find?_eq_some hf, ⟨_, carried_review (carried_dirty hc _)⟩, hok.docs⟩

theorem readG_none_of_readerFalse {φ : Cnf} (hr : readerVerdict φ = false) : ∀ kv ∈ run φ, readG kv.2 = none := by
  intro kv hkv
  unfold readerVerdict at hr
  have := List.any_eq_false.mp hr kv hkv
  cases h : readG kv.2 with
  | none => rfl
  | some _ => rw [h] at this; exact absurd rfl this

/-- **El lector decide las fórmulas satisfacibles bajo `PinKeeps`.** -/
theorem readerVerdict_of_sat_pinKeeps (φ : Cnf) (hb : Bounded φ) (hs : Satisfiable φ)
    (hpk : ∀ kv ∈ run φ, ∀ h, Visited kv.2 h → PinKeeps h) : readerVerdict φ = true := by
  obtain ⟨kv, hkv, hc, hdocs⟩ := start_of_sat φ hb hs
  unfold readerVerdict
  exact List.any_eq_true.mpr ⟨kv, hkv, readG_isSome_of_pinKeeps kv.2 hc hdocs (hpk kv hkv)⟩

/-- **Contrapositivo, primera pérdida.** Si `φ` es satisfacible y el lector dice UNSAT, algún pin válido del lector
pierde todas las soluciones de un estado que las tenía. -/
theorem pinLoss_of_sat_of_readerFalse (φ : Cnf) (hb : Bounded φ) (hs : Satisfiable φ)
    (hr : readerVerdict φ = false) :
    ∃ kv ∈ run φ, ∃ h q, Visited kv.2 h ∧ q ∈ h.alive ∧ PinLoss h q := by
  obtain ⟨kv, hkv, hc, hdocs⟩ := start_of_sat φ hb hs
  exact ⟨kv, hkv, exists_pinLoss_of_readG_none kv.2 hc hdocs (readG_none_of_readerFalse hr kv hkv)⟩

/-- **Contrapositivo, el atasco.** Si `φ` es satisfacible y el lector dice UNSAT, el lector se para en un estado
válido sin ninguna camarilla. -/
theorem zombie_of_sat_of_readerFalse (φ : Cnf) (hb : Bounded φ) (hs : Satisfiable φ)
    (hr : readerVerdict φ = false) :
    ∃ kv ∈ run φ, ∃ h, Visited kv.2 h ∧ h.isValid = true ∧ ¬ ∃ S, Carried h S := by
  obtain ⟨kv, hkv, ⟨S, hS⟩, hdocs⟩ := start_of_sat φ hb hs
  exact ⟨kv, hkv, exists_zombie_of_readG_none kv.2 (isValid_of_carried hS) hdocs
    (readG_none_of_readerFalse hr kv hkv)⟩

end Machine

end AbsSatBingo.Model
