-- lean_project/AbsSat/GraphPath/Model/ReaderTop.lean
import AbsSat.GraphPath.Model.ReaderExec

/-!
# El lector de arriba abajo

`ReaderExec` pincha el **primer** paso con elección. Este módulo es el mismo lector pinchando el
**último**: de arriba abajo.

El motivo es `Descent.extend_below_pinned`. Un pin deja fijado el id de mapa de su paso
(`ReaderComplete.pin_id`), y con los tres pasos de la ventana fijados el `PathNodeId` queda escrito
entero (`Descent.pid_of_three_pins`). Así que pinchando de arriba abajo el lector va dejando detrás
una **zona pinchada** creciente, y por debajo de ella el descenso se extiende **sin hipótesis
ninguna** — ni `SingleParents`, ni `TwoParents`, ni `PairMeet`, ni `AllParentsOwn`.

Pinchando de abajo arriba la zona no se forma: los pasos fijados quedan por debajo del pick, que es
donde la ventana no dice nada.

Todo lo que no depende del orden se reutiliza de `ReaderExec` (`tryPins`, `findSome_valid`,
`findSome_isSome`, `measure_lt_of_choiceAt`), así que este módulo es el mismo programa con otra
regla de elección, y su corrección es la misma prueba.
-/

namespace AbsSat.GraphPath.Model.ReaderTop

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PickInduction (choiceAt hasChoice)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderExec (tryPins findSome_valid findSome_isSome)

-- ============================================================
-- El programa
-- ============================================================

/-- **El último paso que todavía tiene elección.** La misma lista que `ReaderExec.firstChoice`,
recorrida al revés. -/
def lastChoice (g : GPathM) : Option Int :=
  (intRange 0 (g.current_step - 1)).reverse.find? (choiceAt g)

/-- El bucle de lectura de arriba abajo. Tampoco deshace un pin. -/
def readLoopTop : Nat → GPathM → Option GPathM
  | 0, g => if hasChoice g then none else some g
  | n + 1, g =>
    match lastChoice g with
    | none => some g
    | some k =>
      match tryPins g k with
      | none => none
      | some h => readLoopTop n h

def readAggTop (g : GPathM) : Option GPathM :=
  if isValid g then readLoopTop (measure g) g else none

/-- **El veredicto del lector de arriba abajo.** -/
def readerVerdictWTop (φ : Cnf) : Bool :=
  (pureRunW φ).any (fun kv => (readAggTop (filterAllAgg kv.2 [])).isSome)

-- ============================================================
-- Las piezas: las mismas, sobre la lista al revés
-- ============================================================

theorem noChoice_of_lastChoice_none (g : GPathM) (h : lastChoice g = none) :
    hasChoice g = false := by
  unfold lastChoice at h
  unfold hasChoice
  rw [List.find?_eq_none] at h
  exact List.any_eq_false.mpr (fun k hk => by
    simpa using h k (List.mem_reverse.mpr hk))

theorem choiceAt_of_lastChoice (g : GPathM) (k : Int) (h : lastChoice g = some k) :
    choiceAt g k = true := List.find?_some h

theorem mem_of_lastChoice (g : GPathM) (k : Int) (h : lastChoice g = some k) :
    k ∈ intRange 0 (g.current_step - 1) :=
  List.mem_reverse.mp (List.mem_of_find?_eq_some h)

theorem lastChoice_of_hasChoice (g : GPathM) (h : hasChoice g = true) :
    ∃ k, lastChoice g = some k := by
  cases hf : lastChoice g with
  | none => rw [noChoice_of_lastChoice_none g hf] at h; cases h
  | some k => exact ⟨k, rfl⟩

-- ============================================================
-- Corrección: sin hipótesis, y es la misma prueba
-- ============================================================

/-- **Lo que el lector de arriba abajo termina denota un camino.** -/
theorem readLoopTop_sound : ∀ (n : Nat) (g h : GPathM), ReadableAgg g → isValid g = true →
    readLoopTop n g = some h → Inhabited g := by
  intro n
  induction n with
  | zero =>
    intro g h hR hv hs
    simp only [readLoopTop] at hs
    by_cases hc : hasChoice g = true
    · rw [if_pos hc] at hs; cases hs
    · have hc' : hasChoice g = false := by simpa using hc
      exact Reader.inhabited_of_noChoice_readable g (readable_of_readableAgg g hR) hv hc'
  | succ n ih =>
    intro g h hR hv hs
    simp only [readLoopTop] at hs
    cases hf : lastChoice g with
    | none =>
      exact Reader.inhabited_of_noChoice_readable g (readable_of_readableAgg g hR) hv
        (noChoice_of_lastChoice_none g hf)
    | some k =>
      cases ht : tryPins g k with
      | none => simp only [hf, ht] at hs; cases hs
      | some h' =>
        simp only [hf, ht] at hs
        obtain ⟨q, _, e, hv'⟩ := findSome_valid g _ h' ht
        subst e
        obtain ⟨p, hp⟩ := ih _ h (ReadableAgg_filterAllAgg g hR [q.id]) hv' hs
        exact ⟨p, denot_of_pruned (pruned_filterAllAgg g [q.id]) (RCtx_of_readableAgg g hR).nodup p hp⟩

/-- **Un veredicto positivo del lector de arriba abajo siempre acierta.** Sin hipótesis, igual que
`ReaderExec.readerVerdictW_sound`: el orden de los pines no entra en la corrección. -/
theorem readerVerdictWTop_sound (φ : Cnf) (hwf : WF φ) (h : readerVerdictWTop φ = true) :
    Satisfiable φ := by
  unfold readerVerdictWTop at h
  obtain ⟨kv, hkv, hs⟩ := List.any_eq_true.mp h
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  unfold readAggTop at hs
  by_cases hv : isValid (filterAllAgg kv.2 []) = true
  · rw [if_pos hv] at hs
    obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨p, hp⟩ := readLoopTop_sound _ _ res ⟨kv.2, [], hm.rctx, rfl⟩ hv hres
    exact ReaderAggRun.sat_of_denot_final φ hwf kv hkv p
      (denot_of_pruned (pruned_filterAllAgg kv.2 []) hm.rctx.nodup p hp)
  · rw [if_neg hv] at hs; cases hs

-- ============================================================
-- Completitud: la misma frase, sobre la elección de arriba
-- ============================================================

/-- **El lector de arriba abajo no se atasca.** -/
def ProgressTop (g₀ : GPathM) : Prop :=
  ∀ g, ReadFrom g₀ g → isValid g = true → ∀ k, lastChoice g = some k →
    ∃ q ∈ ownersAt g.gowners k, isValid (filterAllAgg g [q.id]) = true

theorem readLoopTop_complete (g₀ : GPathM) (hP : ProgressTop g₀) :
    ∀ (n : Nat) (g : GPathM), measure g ≤ n → ReadFrom g₀ g → isValid g = true →
      (readLoopTop n g).isSome = true := by
  intro n
  induction n with
  | zero =>
    intro g hm hF hv
    simp only [readLoopTop]
    by_cases hc : hasChoice g = true
    · obtain ⟨k, hk⟩ := lastChoice_of_hasChoice g hc
      obtain ⟨q, hq, _⟩ := hP g hF hv k hk
      have := measure_lt_of_choiceAt g k (choiceAt_of_lastChoice g k hk) q hq
      omega
    · rw [if_neg hc]; rfl
  | succ n ih =>
    intro g hm hF hv
    simp only [readLoopTop]
    cases hf : lastChoice g with
    | none => rfl
    | some k =>
      obtain ⟨q₀, hq₀, hv₀⟩ := hP g hF hv k hf
      have hsome := findSome_isSome g (ownersAt g.gowners k) ⟨q₀, hq₀, hv₀⟩
      obtain ⟨h', ht⟩ := Option.isSome_iff_exists.mp hsome
      have ht' : tryPins g k = some h' := ht
      simp only [ht']
      obtain ⟨q, hq, e, hv'⟩ := findSome_valid g _ h' ht
      subst e
      have hlt := measure_lt_of_choiceAt g k (choiceAt_of_lastChoice g k hf) q hq
      exact ih _ (by omega) (ReadFrom.pin g q.id hF hv) hv'

theorem readAggTop_complete (g₀ : GPathM) (hv : isValid g₀ = true) (hP : ProgressTop g₀) :
    (readAggTop g₀).isSome = true := by
  unfold readAggTop
  rw [if_pos hv]
  exact readLoopTop_complete g₀ hP _ g₀ (Nat.le_refl _) ReadFrom.start hv

theorem readerVerdictWTop_complete (φ : Cnf) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) (hP : ProgressTop (filterAllAgg kv.2 [])) :
    readerVerdictWTop φ = true :=
  List.any_eq_true.mpr ⟨kv, hkv, readAggTop_complete _ hv hP⟩

/-- **Y una cadena da el pin, igual que abajo**: si todo estado válido que el lector alcanza lleva
cadena, el lector de arriba abajo termina. -/
theorem progressTop_of_chains (g₀ : GPathM)
    (hC : ∀ g, ReadFrom g₀ g → isValid g = true → ∃ sel, ChainSound g sel) : ProgressTop g₀ := by
  intro g hF hv k hk
  have hmem := mem_of_lastChoice g k hk
  obtain ⟨sel, hsc⟩ := hC g hF hv
  have h0 : 0 ≤ k := mem_intRange_lower hmem
  have h1 : k < g.current_step := by have := mem_intRange_upper hmem; omega
  obtain ⟨_, hstep⟩ := hsc.chain.1.1 k h0 h1
  refine ⟨sel k, List.mem_filter.mpr ⟨hsc.chain.2.2 k h0 h1, beq_iff_eq.mpr hstep⟩, ?_⟩
  refine PickInduction.isValid_of_ChainG _ sel (ChainSound_filterAllAgg g [(sel k).id] sel hsc ?_).chain
  intro req hreq _ _
  rw [List.mem_singleton.mp hreq, hstep]

/-- info: 'AbsSat.GraphPath.Model.ReaderTop.readerVerdictWTop_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictWTop_sound

/-- info: 'AbsSat.GraphPath.Model.ReaderTop.readerVerdictWTop_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictWTop_complete

/-- info: 'AbsSat.GraphPath.Model.ReaderTop.progressTop_of_chains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms progressTop_of_chains

end AbsSat.GraphPath.Model.ReaderTop
