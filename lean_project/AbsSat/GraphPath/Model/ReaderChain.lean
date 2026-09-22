-- lean_project/AbsSat/GraphPath/Model/ReaderChain.lean
import AbsSat.GraphPath.Model.ReaderExec
import AbsSat.GraphPath.Model.PinExact
import AbsSat.GraphPath.Model.AncestorOwned

/-!
# El residuo del lector sin retroceso, con su tamaño correcto

Toda esta sesión ha ido apuntando a `Descent.SupportedS` —*todo nodo de todo estado está en una
cadena*— como el enunciado que hay que cerrar. Es más de lo que hace falta.

`ReaderExec.progressAgg_of_chains` pide exactamente esto y nada más:

    ∀ g, ReadFrom g₀ g → isValid g = true → ∃ sel, ChainSound g sel

**Una** cadena por estado, no una por nodo. Este módulo escribe esa diferencia y la explota.

* **`HasChain`** — el estado tiene una cadena. Lo único que el lector necesita.
* **`PinKeepsChain`** — **el residuo, del tamaño correcto**: si un estado con cadena sobrevive a un
  pin, el estado pinchado tiene cadena. Habla de **un estado y un pin**, no de todos los nodos de
  todos los estados alcanzables.
* **`hasChain_readFrom`**, **`progressAgg_of_pinKeepsChain`**, **`readerVerdictW_of_pinKeepsChain`**
  — la escalera entera hasta el veredicto, por inducción sobre `ReadFrom`.
* **`pinKeepsChain_of_pinReachable`** — y `PinKeepsChain` sale de algo aún más estrecho: que un pin
  que deja el estado válido sea un pin **por el que pasa alguna cadena de antes**
  (`PinReachable`). El review ya no estorba: `ChainSound_filterAllAgg` lleva esa cadena al otro
  lado entera.

Comparado con lo que había:

| enunciado | cuantifica sobre |
|---|---|
| `Descent.SupportedS` | todo nodo de todo estado |
| `SupportedRun.ChainPairwise` | toda cadena enlazada dentro de una tabla |
| `AncestorOwned.AncOwned` | todo par (nodo, ancestro) — **medido falso tras `doJoin`** |
| **`PinReachable`** | **un estado, un pin** |

Y `PinReachable` es la frase que el autor viene diciendo desde el principio: *el review agresivo
deja solo nodos con camino, así que cualquier elección válida tiene camino*. La sonda `row-degree
bt` la mide indirectamente y no encuentra un solo estado donde el retroceso haga falta.
-/

namespace AbsSat.GraphPath.Model.ReaderChain

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderExec

/-- **El estado tiene una cadena.** Lo único que `progressAgg_of_chains` pide de cada estado. -/
def HasChain (g : GPathM) : Prop := ∃ sel, ChainSound g sel

/-- **El residuo, del tamaño correcto.** Un estado con cadena que sobrevive a un pin sigue
teniendo cadena. Una frase sobre **un estado y un pin**. -/
def PinKeepsChain : Prop :=
  ∀ (g : GPathM) (mid : NodeId), ReadableAgg g → HasChain g →
    isValid (filterAllAgg g [mid]) = true → HasChain (filterAllAgg g [mid])

/-- **Y de ahí, cadena en todo estado que el lector alcanza**, por inducción sobre `ReadFrom`. -/
theorem hasChain_readFrom (hkeep : PinKeepsChain) (g₀ : GPathM) (hR₀ : ReadableAgg g₀)
    (h₀ : HasChain g₀) : ∀ g, ReadFrom g₀ g → isValid g = true → HasChain g := by
  intro g hF
  induction hF with
  | start => intro _; exact h₀
  | pin g' mid hF' hv' ih =>
    intro hv
    exact hkeep g' mid (PinExact.readableAgg_of_readFrom g₀ hR₀ g' hF') (ih hv') hv

/-- **El lector no se atasca.** -/
theorem progressAgg_of_pinKeepsChain (hkeep : PinKeepsChain) (g₀ : GPathM)
    (hR₀ : ReadableAgg g₀) (h₀ : HasChain g₀) : ProgressAgg g₀ :=
  progressAgg_of_chains g₀ (hasChain_readFrom hkeep g₀ hR₀ h₀)

/-- **Y el veredicto del lector sin retroceso es positivo.** -/
theorem readerVerdictW_of_pinKeepsChain (hkeep : PinKeepsChain) (φ : Cnf)
    (kv : NodeId × GPathM) (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hR₀ : ReadableAgg (filterAllAgg kv.2 []))
    (hv : isValid (filterAllAgg kv.2 []) = true) (h₀ : HasChain (filterAllAgg kv.2 [])) :
    readerVerdictW φ = true :=
  readerVerdictW_complete φ kv hkv hv (progressAgg_of_pinKeepsChain hkeep _ hR₀ h₀)

-- ============================================================
-- Y el residuo, una vuelta de tuerca más estrecho
-- ============================================================

/-- **Un pin válido es un pin por el que pasa una cadena.** La frase del autor, escrita sobre un
solo estado: el review agresivo deja solo nodos con camino, así que si pinchar `mid` no invalida el
grafo es porque alguna cadena pasa por `mid`. -/
def PinReachable : Prop :=
  ∀ (g : GPathM) (mid : NodeId), ReadableAgg g → HasChain g →
    isValid (filterAllAgg g [mid]) = true →
    ∃ sel, ChainSound g sel ∧
      (0 ≤ mid.step → mid.step < g.current_step → (sel mid.step).id = mid)

/-- **Y basta**: el review no estorba. `ChainSound_filterAllAgg` lleva la cadena al estado
pinchado entera, sin pedir nada más. -/
theorem pinKeepsChain_of_pinReachable (h : PinReachable) : PinKeepsChain := by
  intro g mid hR hc hv
  obtain ⟨sel, hsc, hpin⟩ := h g mid hR hc hv
  refine ⟨sel, ChainSound_filterAllAgg g [mid] sel hsc ?_⟩
  intro req hreq h0 h1
  rw [List.mem_singleton.mp hreq] at h0 h1 ⊢
  exact hpin h0 h1

/-- **El veredicto, desde la frase estrecha.** -/
theorem readerVerdictW_of_pinReachable (h : PinReachable) (φ : Cnf)
    (kv : NodeId × GPathM) (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hR₀ : ReadableAgg (filterAllAgg kv.2 []))
    (hv : isValid (filterAllAgg kv.2 []) = true) (h₀ : HasChain (filterAllAgg kv.2 [])) :
    readerVerdictW φ = true :=
  readerVerdictW_of_pinKeepsChain (pinKeepsChain_of_pinReachable h) φ kv hkv hR₀ hv h₀

-- ============================================================
-- Lo que las rutas anteriores dan, dicho en estos términos
-- ============================================================

/-- **`SupportedS` es más que suficiente**, y esto lo dice: un estado con nodos tiene cadena. Se
escribe para dejar constancia de cuánto sobraba — `SupportedS` da una cadena **por nodo**, y aquí
solo se usa una. -/
theorem hasChain_of_supportedS (g : GPathM) (hpos : 0 < g.current_step) (hv : isValid g = true)
    (hgn : GownersNodes.GN g) (hsup : Descent.SupportedS g) : HasChain g := by
  -- la validez da un owner global en el paso 0, y `GN` lo hace nodo
  have hent := hasStepEntry_of_isValid g hv 0 (Int.le_refl 0) hpos
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
  obtain ⟨q, hq, _⟩ := hent
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g q).mp (hgn q hq))
  obtain ⟨sel, hsc, _⟩ := hsup q n hn
  exact ⟨sel, hsc⟩

-- ============================================================
-- La mitad que YA está demostrada: los pines en pasos literales
-- ============================================================

/-- **Un pin en un paso literal conserva la cadena, desde el invariante de entradas.**

No es una hipótesis nueva: `SupportedRun.supportedS_pin_of_soundAt` ya lo demuestra, y aquí se lee
en los términos que el lector necesita. `SoundAt (LitStep φ)` es el invariante de **entradas**
—toda entrada de toda tabla hacia un paso literal es realizable—, medido sobre 825.612 entradas sin
una sola excepción, y su único residuo abierto es `RunSteps.PinPairSoundAt`.

Así que las dos rutas de esta sesión se tocan aquí: lo que quedaba de la ruta del pin cubre
exactamente los pines del lector en el bloque literal. -/
theorem hasChain_pin_of_soundAt (φ : Cnf) (g : GPathM) (hR : ReadableAgg g)
    (hv : isValid g = true) (ht : RunInhabited.SoundAt (RunInhabited.LitStep φ) g)
    (mid : NodeId) (hlit : RunInhabited.LitStep φ mid.step)
    (h0 : 0 ≤ mid.step) (h1 : mid.step < g.current_step)
    (hvr : isValid (filterAllAgg g [mid]) = true) :
    HasChain (filterAllAgg g [mid]) := by
  have hcs : (filterAllAgg g [mid]).current_step = g.current_step :=
    (pruned_filterAllAgg g [mid]).step_eq
  have hRp : ReadableAgg (filterAllAgg g [mid]) :=
    PinExact.readableAgg_of_readFrom g hR _ (ReadFrom.pin g mid ReadFrom.start hv)
  have rc := RCtx_of_readableAgg _ hRp
  have hb : ∀ x n, (filterAllAgg g [mid]).node? x = some n →
      0 ≤ x.id.step ∧ x.id.step < (filterAllAgg g [mid]).current_step := by
    intro x n hx
    have hmem := List.mem_of_find?_eq_some hx
    have hid : n.id = x := node?_id_eq _ x n hx
    exact ⟨by have := rc.snn n hmem; rwa [hid] at this,
           by have := rc.below n hmem; rwa [hid] at this⟩
  exact hasChain_of_supportedS _ (by rw [hcs]; omega) hvr rc.gn
    (SupportedRun.supportedS_pin_of_soundAt φ g hR ht mid hlit h0 hvr (by rw [hcs]; exact h1) hb)

/-- **Un pin fuera de rango no pide nada.** El requisito de `ChainSound_filterAllAgg` está
condicionado a que el paso esté en rango, así que la cadena pasa entera. -/
theorem hasChain_out_of_range (g : GPathM) (mid : NodeId) (h : HasChain g)
    (hout : ¬ (0 ≤ mid.step ∧ mid.step < g.current_step)) : HasChain (filterAllAgg g [mid]) := by
  obtain ⟨sel, hsc⟩ := h
  refine ⟨sel, ChainSound_filterAllAgg g [mid] sel hsc (fun req hreq hr0 hr1 => ?_)⟩
  rw [List.mem_singleton.mp hreq] at hr0 hr1
  exact absurd ⟨hr0, hr1⟩ hout

/-- **Y entonces el residuo se queda solo con los pasos de cláusula.**

`PinKeepsChain` restringido: si el invariante de entradas viaja con el lector, los pines del bloque
literal están cubiertos por el teorema de arriba, y lo único que queda abierto es qué pasa cuando
el lector pincha un paso de cláusula. -/
def PinKeepsChainClause (φ : Cnf) : Prop :=
  ∀ (g : GPathM) (mid : NodeId), ReadableAgg g → HasChain g →
    ¬ RunInhabited.LitStep φ mid.step →
    isValid (filterAllAgg g [mid]) = true → HasChain (filterAllAgg g [mid])

/-- **Las dos mitades, juntas.** Con el invariante de entradas a lo largo de la lectura, el residuo
del lector sin retroceso se reduce a los pines en pasos de cláusula. -/
theorem pinKeepsChain_of_soundAt (φ : Cnf) (g₀ : GPathM)
    (hsound : ∀ g, ReadFrom g₀ g → isValid g = true →
      RunInhabited.SoundAt (RunInhabited.LitStep φ) g)
    (hcl : PinKeepsChainClause φ) (hR₀ : ReadableAgg g₀) (h₀ : HasChain g₀) :
    ∀ g, ReadFrom g₀ g → isValid g = true → HasChain g := by
  intro g hF
  induction hF with
  | start => intro _; exact h₀
  | pin g' mid hF' hv' ih =>
    intro hv
    have hR' : ReadableAgg g' := PinExact.readableAgg_of_readFrom g₀ hR₀ g' hF'
    -- un pin fuera de rango no pide nada a la cadena: el requisito es vacío
    if hin : 0 ≤ mid.step ∧ mid.step < g'.current_step then
      -- el corte es decidible sin `Classical`: es una comparación de enteros
      if hc : mid.step < litBlock φ then
        exact hasChain_pin_of_soundAt φ g' hR' hv' (hsound g' hF' hv') mid (Or.inl hc)
          hin.1 hin.2 hv
      else
        rcases int_eq_or_ne mid.step 0 with hz | hz
        · exact hasChain_pin_of_soundAt φ g' hR' hv' (hsound g' hF' hv') mid (Or.inr hz)
            hin.1 hin.2 hv
        · refine hcl g' mid hR' (ih hv') (fun hl => ?_) hv
          rcases hl with h | h
          · exact hc h
          · exact hz h
    else
      exact hasChain_out_of_range g' mid (ih hv') hin

-- ============================================================
-- Y sin residuo: el invariante de entradas para TODOS los pasos
-- ============================================================

/-- **El pin, en cualquier paso.** `RunSteps.realizes_pin` usaba `LitStep` en un solo sitio: para
alimentar el predicado de `SoundAt`. Generalizado (`realizes_pin_gen`), con `TablesSound` —toda
entrada de toda tabla es realizable, sin restringir el paso— el pin no necesita estar en el bloque
literal.

`TablesSound` es **el otro de los dos invariantes que esta sesión mide al 100%**: 825.612 entradas,
cero fantasmas. -/
theorem hasChain_pin_of_tablesSound (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true)
    (ht : Exactness.TablesSound g) (mid : NodeId)
    (h0 : 0 ≤ mid.step) (h1 : mid.step < g.current_step)
    (hvr : isValid (filterAllAgg g [mid]) = true) : HasChain (filterAllAgg g [mid]) := by
  have hcs : (filterAllAgg g [mid]).current_step = g.current_step :=
    (pruned_filterAllAgg g [mid]).step_eq
  have hRp : ReadableAgg (filterAllAgg g [mid]) :=
    PinExact.readableAgg_of_readFrom g hR _ (ReadFrom.pin g mid ReadFrom.start hv)
  have rc := RCtx_of_readableAgg _ hRp
  have hpos : 0 < (filterAllAgg g [mid]).current_step := by rw [hcs]; omega
  -- un nodo del paso 0 del estado pinchado, que la validez garantiza
  have hent := hasStepEntry_of_isValid _ hvr 0 (Int.le_refl 0) hpos
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
  obtain ⟨q, hq, _⟩ := hent
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff _ q).mp (rc.gn q hq))
  have hmem := List.mem_of_find?_eq_some hn
  have hid : n.id = q := node?_id_eq _ q n hn
  obtain ⟨_, _, _, sel, hsc, _, _⟩ :=
    RunSteps.realizes_pin_gen (fun _ => True) g hR (RunInhabited.soundAt_of_tablesSound ht)
      mid trivial h0 hvr (by rw [hcs]; exact h1) q n hn
      (by have := rc.snn n hmem; rwa [hid] at this)
      (by have := rc.below n hmem; rwa [hid] at this)
  exact ⟨sel, hsc⟩

/-- **`PinKeepsChain`, sin residuo.** Con `TablesSound` a lo largo de la lectura, todo pin conserva
la cadena: en rango por el teorema de arriba, fuera de rango porque no pide nada. -/
theorem pinKeepsChain_of_tablesSound (g₀ : GPathM) (hR₀ : ReadableAgg g₀) (h₀ : HasChain g₀)
    (hts : ∀ g, ReadFrom g₀ g → isValid g = true → Exactness.TablesSound g) :
    ∀ g, ReadFrom g₀ g → isValid g = true → HasChain g := by
  intro g hF
  induction hF with
  | start => intro _; exact h₀
  | pin g' mid hF' hv' ih =>
    intro hv
    have hR' : ReadableAgg g' := PinExact.readableAgg_of_readFrom g₀ hR₀ g' hF'
    if hin : 0 ≤ mid.step ∧ mid.step < g'.current_step then
      exact hasChain_pin_of_tablesSound g' hR' hv' (hts g' hF' hv') mid hin.1 hin.2 hv
    else
      exact hasChain_out_of_range g' mid (ih hv') hin

/-- **El lector sin retroceso no se atasca**, bajo el invariante de entradas. -/
theorem progressAgg_of_tablesSound (g₀ : GPathM) (hR₀ : ReadableAgg g₀) (h₀ : HasChain g₀)
    (hts : ∀ g, ReadFrom g₀ g → isValid g = true → Exactness.TablesSound g) : ProgressAgg g₀ :=
  progressAgg_of_chains g₀ (pinKeepsChain_of_tablesSound g₀ hR₀ h₀ hts)

/-- **Y su veredicto es positivo.** Sin hipótesis sobre pines, sin `SupportedS`, sin cuantificar
sobre nodos: solo el invariante de **entradas** viajando con el lector. -/
theorem readerVerdictW_of_tablesSound (φ : Cnf) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hR₀ : ReadableAgg (filterAllAgg kv.2 []))
    (hv : isValid (filterAllAgg kv.2 []) = true) (h₀ : HasChain (filterAllAgg kv.2 []))
    (hts : ∀ g, ReadFrom (filterAllAgg kv.2 []) g → isValid g = true →
      Exactness.TablesSound g) :
    readerVerdictW φ = true :=
  readerVerdictW_complete φ kv hkv hv (progressAgg_of_tablesSound _ hR₀ h₀ hts)

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.readerVerdictW_of_tablesSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_of_tablesSound

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.hasChain_pin_of_tablesSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasChain_pin_of_tablesSound

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.readerVerdictW_of_pinReachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_of_pinReachable

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.pinKeepsChain_of_pinReachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinKeepsChain_of_pinReachable

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.hasChain_readFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasChain_readFrom

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.hasChain_pin_of_soundAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasChain_pin_of_soundAt

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.pinKeepsChain_of_soundAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinKeepsChain_of_soundAt

end AbsSat.GraphPath.Model.ReaderChain
