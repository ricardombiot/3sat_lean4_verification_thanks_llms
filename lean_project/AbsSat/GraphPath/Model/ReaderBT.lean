-- lean_project/AbsSat/GraphPath/Model/ReaderBT.lean
import AbsSat.GraphPath.Model.ReaderExec
import AbsSat.GraphPath.Model.ConservationImproves

/-!
# El lector con retroceso, y el veredicto sin hipótesis

`ReaderExec` no deshace un pin, y eso hizo su corrección trivial y su completitud imposible: para
que un lector que nunca retrocede acierte siempre hace falta que **ningún** pin válido lleve a un
estado sin camino, o sea que no haya fantasmas — que es el objetivo entero
(`Reader.PickSome_of_Inhabited` y su recíproco).

**Eso le pide al algoritmo más de lo que necesita para ser correcto.** La máquina vuelve a revisar
después de cada pin precisamente porque *no* sabe la cadena de antemano; exigirle que no se
equivoque nunca es exigirle que la supiera.

El lector de aquí retrocede. Y entonces la completitud sale de lo que ya está demostrado, sin
ninguna hipótesis abierta:

* `ConservationImproves.pureRunW_full_chain` — sobre una fórmula satisfacible, la línea final tiene
  un estado con una cadena `ChainSound` (la conservación ya la construye; `pureRunW_full_state` la
  tiraba para quedarse con `Inhabited`);
* `AggressiveReview.ChainSound_filterAllAgg` — pinchar el nodo que **la propia cadena** elige la
  conserva;
* y `measure` decrece con cada pin, así que la búsqueda termina.

Resultado: **`readerVerdictBT φ = true ↔ Satisfiable φ`**, sin hipótesis.

El precio es el coste del retroceso, que en el peor caso es exponencial en la fase de lectura (la
construcción del grafo sigue siendo polinómica). Medido: el retroceso **no dispara nunca** en
ninguno de los barridos — `row-degree traj` da 100% de estados donde el descenso baja hasta el
paso 0. Lo que este módulo cambia no es el comportamiento sino lo que se puede demostrar de él.
-/

namespace AbsSat.GraphPath.Model.ReaderBT

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel (selOfAssign)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PickInduction (choiceAt hasChoice)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderExec (firstChoice noChoice_of_firstChoice_none
  choiceAt_of_firstChoice firstChoice_of_hasChoice)

-- ============================================================
-- Dos lemas sobre `findSome?`
-- ============================================================

theorem exists_of_findSome? {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (h : β), l.findSome? f = some h → ∃ q ∈ l, f q = some h := by
  intro l
  induction l with
  | nil => intro h hs; simp at hs
  | cons a rest ih =>
    intro h hs
    simp only [List.findSome?_cons] at hs
    cases hfa : f a with
    | none => rw [hfa] at hs; obtain ⟨q, hq, e⟩ := ih h hs; exact ⟨q, List.mem_cons_of_mem _ hq, e⟩
    | some b => rw [hfa] at hs; cases hs; exact ⟨a, List.mem_cons_self, hfa⟩

theorem findSome?_isSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∃ q ∈ l, (f q).isSome = true) → (l.findSome? f).isSome = true := by
  intro l
  induction l with
  | nil => intro ⟨q, hq, _⟩; cases hq
  | cons a rest ih =>
    intro ⟨q, hq, hv⟩
    simp only [List.findSome?_cons]
    cases hfa : f a with
    | some b => rfl
    | none =>
      rcases List.mem_cons.mp hq with rfl | hq'
      · rw [hfa] at hv; cases hv
      · exact ih ⟨q, hq', hv⟩

-- ============================================================
-- El programa
-- ============================================================

/-- **El lector con retroceso.** En el primer paso con elección prueba cada nodo: pincha, revisa, y
si la rama no llega al final **deshace y prueba el siguiente**. -/
def readBT : Nat → GPathM → Option GPathM
  | 0, g => if hasChoice g then none else some g
  | n + 1, g =>
    match firstChoice g with
    | none => some g
    | some k =>
      (ownersAt g.gowners k).findSome? (fun q =>
        if isValid (filterAllAgg g [q.id]) then readBT n (filterAllAgg g [q.id]) else none)

def readAggBT (g : GPathM) : Option GPathM := if isValid g then readBT (measure g) g else none

/-- **El veredicto del lector con retroceso.** -/
def readerVerdictBT (φ : Cnf) : Bool :=
  (pureRunW φ).any (fun kv => (readAggBT (filterAllAgg kv.2 [])).isSome)

-- ============================================================
-- Corrección: sin hipótesis, como la del lector sin retroceso
-- ============================================================

theorem readBT_sound : ∀ (n : Nat) (g h : GPathM), ReadableAgg g → isValid g = true →
    readBT n g = some h → Inhabited g := by
  intro n
  induction n with
  | zero =>
    intro g h hR hv hs
    simp only [readBT] at hs
    by_cases hc : hasChoice g = true
    · rw [if_pos hc] at hs; cases hs
    · have hc' : hasChoice g = false := by simpa using hc
      exact Reader.inhabited_of_noChoice_readable g (readable_of_readableAgg g hR) hv hc'
  | succ n ih =>
    intro g h hR hv hs
    simp only [readBT] at hs
    cases hf : firstChoice g with
    | none =>
      exact Reader.inhabited_of_noChoice_readable g (readable_of_readableAgg g hR) hv
        (noChoice_of_firstChoice_none g hf)
    | some k =>
      rw [hf] at hs
      obtain ⟨q, _, hq⟩ := exists_of_findSome? _ _ h hs
      by_cases hvq : isValid (filterAllAgg g [q.id]) = true
      · rw [if_pos hvq] at hq
        obtain ⟨p, hp⟩ := ih _ h (ReadableAgg_filterAllAgg g hR [q.id]) hvq hq
        exact ⟨p, denot_of_pruned (pruned_filterAllAgg g [q.id]) (RCtx_of_readableAgg g hR).nodup p hp⟩
      · rw [if_neg hvq] at hq; cases hq

/-- **Un veredicto positivo siempre acierta.** Sin hipótesis. -/
theorem readerVerdictBT_sound (φ : Cnf) (hwf : WF φ) (h : readerVerdictBT φ = true) :
    Satisfiable φ := by
  unfold readerVerdictBT at h
  obtain ⟨kv, hkv, hs⟩ := List.any_eq_true.mp h
  obtain ⟨hm, _, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  unfold readAggBT at hs
  by_cases hv : isValid (filterAllAgg kv.2 []) = true
  · rw [if_pos hv] at hs
    obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨p, hp⟩ := readBT_sound _ _ res ⟨kv.2, [], hm.rctx, rfl⟩ hv hres
    exact ReaderAggRun.sat_of_denot_final φ hwf kv hkv p
      (denot_of_pruned (pruned_filterAllAgg kv.2 []) hm.rctx.nodup p hp)
  · rw [if_neg hv] at hs; cases hs

-- ============================================================
-- Completitud: **sin hipótesis**, que es lo que el retroceso compra
-- ============================================================

/-- El pin que la cadena elige en un paso: está en la tabla del paso, deja el estado válido, y
conserva la cadena. Tres consecuencias de `ChainSound_filterAllAgg`. -/
theorem pin_of_chain (g : GPathM) (sel : Int → PathNodeId) (hsc : ChainSound g sel)
    (k : Int) (hk0 : 0 ≤ k) (hk1 : k < g.current_step) :
    sel k ∈ ownersAt g.gowners k ∧ isValid (filterAllAgg g [(sel k).id]) = true ∧
      ChainSound (filterAllAgg g [(sel k).id]) sel := by
  obtain ⟨_, hstep⟩ := hsc.chain.1.1 k hk0 hk1
  have hkeep : ChainSound (filterAllAgg g [(sel k).id]) sel := by
    refine ChainSound_filterAllAgg g [(sel k).id] sel hsc ?_
    intro req hreq _ _
    rw [List.mem_singleton.mp hreq, hstep]
  exact ⟨List.mem_filter.mpr ⟨hsc.chain.2.2 k hk0 hk1, beq_iff_eq.mpr hstep⟩,
    PickInduction.isValid_of_ChainG _ sel hkeep.chain, hkeep⟩

/-- **El lector con retroceso termina siempre que hay camino.** Ninguna hipótesis: la cadena da el
pin, el pin la conserva, y `measure` decrece. Que otros pines lleven a estados sin camino da igual
— el retroceso los deshace. -/
theorem readBT_complete : ∀ (n : Nat) (g : GPathM), measure g ≤ n →
    (∃ sel, ChainSound g sel) → (readBT n g).isSome = true := by
  intro n
  induction n with
  | zero =>
    intro g hm ⟨sel, hsc⟩
    simp only [readBT]
    by_cases hc : hasChoice g = true
    · obtain ⟨k, hk⟩ := firstChoice_of_hasChoice g hc
      have hmem := List.mem_of_find?_eq_some hk
      have h0 : 0 ≤ k := mem_intRange_lower hmem
      have h1 : k < g.current_step := by have := mem_intRange_upper hmem; omega
      obtain ⟨hq, _, _⟩ := pin_of_chain g sel hsc k h0 h1
      have := measure_lt_of_choiceAt g k (choiceAt_of_firstChoice g k hk) (sel k) hq
      omega
    · rw [if_neg hc]; rfl
  | succ n ih =>
    intro g hm hch
    obtain ⟨sel, hsc⟩ := hch
    simp only [readBT]
    cases hf : firstChoice g with
    | none => rfl
    | some k =>
      have hmem := List.mem_of_find?_eq_some hf
      have h0 : 0 ≤ k := mem_intRange_lower hmem
      have h1 : k < g.current_step := by have := mem_intRange_upper hmem; omega
      obtain ⟨hq, hvq, hkeep⟩ := pin_of_chain g sel hsc k h0 h1
      have hlt := measure_lt_of_choiceAt g k (choiceAt_of_firstChoice g k hf) (sel k) hq
      refine findSome?_isSome _ _ ⟨sel k, hq, ?_⟩
      rw [if_pos hvq]
      exact ih (filterAllAgg g [(sel k).id]) (by omega) ⟨sel, hkeep⟩

/-- **El veredicto del lector con retroceso es completo. Sin hipótesis.**

Sobre una fórmula satisfacible la conservación aparca en la línea final un estado con cadena
(`pureRunW_full_chain`), la cadena sobrevive al review del lector, y `readBT_complete` termina. -/
theorem readerVerdictBT_complete (φ : Cnf) (hwf : WF φ) (h : Satisfiable φ) :
    readerVerdictBT φ = true := by
  obtain ⟨a, hsat⟩ := h
  obtain ⟨g, hmem, _, _, sel, hsel⟩ := ConservationImproves.pureRunW_full_chain φ a hwf hsat
  have hsel0 : ChainSound (filterAllAgg g []) sel :=
    ChainSound_filterAllAgg g [] sel hsel (fun _ hreq => absurd hreq List.not_mem_nil)
  have hv : isValid (filterAllAgg g []) = true :=
    PickInduction.isValid_of_ChainG _ sel hsel0.chain
  refine List.any_eq_true.mpr ⟨(selOfAssign φ a (stepCount φ - 1), g), hmem, ?_⟩
  simp only [readAggBT]
  rw [if_pos hv]
  exact readBT_complete _ _ (Nat.le_refl _) ⟨sel, hsel0⟩

/-- **El retroceso no cambia el algoritmo: lo cubre.** Si el lector sin retroceso termina, el de
aquí también — prueba los mismos pines en el mismo orden y solo sigue probando donde el otro se
habría rendido.

Así que el retroceso **no se paga cuando no hace falta**, y medido no hace falta nunca
(`row-degree traj`: 100% de los estados llegan al paso 0). Lo que cuesta es exactamente lo que el
lector sin retroceso contestaría `unknown`. -/
theorem readBT_isSome_of_readLoop : ∀ (n : Nat) (g h : GPathM),
    ReaderExec.readLoop n g = some h → (readBT n g).isSome = true := by
  intro n
  induction n with
  | zero =>
    intro g h hs
    simp only [ReaderExec.readLoop] at hs
    simp only [readBT]
    by_cases hc : hasChoice g = true
    · rw [if_pos hc] at hs; cases hs
    · rw [if_neg hc]; rfl
  | succ n ih =>
    intro g h hs
    simp only [ReaderExec.readLoop] at hs
    simp only [readBT]
    cases hf : firstChoice g with
    | none => rfl
    | some k =>
      simp only [hf] at hs
      cases ht : ReaderExec.tryPins g k with
      | none => simp only [ht] at hs; cases hs
      | some h' =>
        simp only [ht] at hs
        obtain ⟨q, hq, e, hvq⟩ := ReaderExec.findSome_valid g _ h' ht
        subst e
        exact findSome?_isSome _ _ ⟨q, hq, by rw [if_pos hvq]; exact ih _ h hs⟩

/-- **El veredicto barato implica el caro.** -/
theorem readerVerdictBT_of_readerVerdictW (φ : Cnf) (h : ReaderExec.readerVerdictW φ = true) :
    readerVerdictBT φ = true := by
  unfold ReaderExec.readerVerdictW at h
  obtain ⟨kv, hkv, hs⟩ := List.any_eq_true.mp h
  refine List.any_eq_true.mpr ⟨kv, hkv, ?_⟩
  unfold ReaderExec.readAgg at hs
  unfold readAggBT
  by_cases hv : isValid (filterAllAgg kv.2 []) = true
  · rw [if_pos hv] at hs ⊢
    obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp hs
    exact readBT_isSome_of_readLoop _ _ res hres
  · rw [if_neg hv] at hs; cases hs

/-- **La máquina decide 3-SAT, sin ninguna hipótesis abierta.** -/
theorem readerVerdictBT_iff (φ : Cnf) (hwf : WF φ) : readerVerdictBT φ = true ↔ Satisfiable φ :=
  ⟨readerVerdictBT_sound φ hwf, readerVerdictBT_complete φ hwf⟩

/-- info: 'AbsSat.GraphPath.Model.ReaderBT.readerVerdictBT_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictBT_sound

/-- info: 'AbsSat.GraphPath.Model.ReaderBT.readerVerdictBT_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictBT_complete

/-- info: 'AbsSat.GraphPath.Model.ReaderBT.readerVerdictBT_of_readerVerdictW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictBT_of_readerVerdictW

/-- info: 'AbsSat.GraphPath.Model.ReaderBT.readerVerdictBT_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictBT_iff

end AbsSat.GraphPath.Model.ReaderBT
