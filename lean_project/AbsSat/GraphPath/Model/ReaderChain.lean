-- lean_project/AbsSat/GraphPath/Model/ReaderChain.lean
import AbsSat.GraphPath.Model.ReaderExec
import AbsSat.GraphPath.Model.PinExact
import AbsSat.GraphPath.Model.AncestorOwned
import AbsSat.GraphPath.Model.ReaderBT

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
open AbsSat.GraphPath.Model.Exactness (Realizes)

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

-- ============================================================
-- La propagación: qué le hace un pin al invariante de entradas
-- ============================================================

/-- **El residuo del pin, sin restringir el paso.**

Es `RunSteps.PinPairSoundAt` quitándole el bloque literal, y nótese lo que se gana: **no menciona
φ**. Es una frase sobre un estado de la máquina y un pin — si tras pinchar `r` un nodo `x` sigue
vivo y conserva una entrada `q` hacia un paso **distinto** del pinchado, entonces hay una cadena
del estado pinchado por `x` y por `q`.

El paso pinchado no aparece porque es gratis (`tablesSound_pin_of_pairs`, abajo). -/
def PinPairSound : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → Exactness.TablesSound g →
    ∀ r : NodeId, isValid (filterAllAgg g [r]) = true →
      ∀ x n, (filterAllAgg g [r]).node? x = some n → 0 ≤ x.id.step →
        x.id.step < (filterAllAgg g [r]).current_step →
        ∀ q, 0 ≤ q.id.step → q.id.step < (filterAllAgg g [r]).current_step →
          q.id.step ≠ r.step → q ∈ n.owners → Realizes (filterAllAgg g [r]) x q

/-- **El paso pinchado es gratis, y el resto es el residuo.**

Una entrada al paso pinchado lleva el pin (`ReaderComplete.pin_id`), la entrada estaba en un camino
antes de pinchar, y ese camino pasa por el pin — luego sobrevive. Es la misma prueba que
`RunSteps.pinStep_of_pairs`, sin la restricción al bloque literal. -/
theorem tablesSound_pin_of_pairs (h : PinPairSound) (g : GPathM) (hR : ReadableAgg g)
    (hv : isValid g = true) (ht : Exactness.TablesSound g) (r : NodeId)
    (hvr : isValid (filterAllAgg g [r]) = true) :
    Exactness.TablesSound (filterAllAgg g [r]) := by
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  rcases int_eq_or_ne q.id.step r.step with hqr | hqr
  · have hRr := ReadableAgg_filterAllAgg g hR [r]
    have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
    have rcg := RCtx_of_readableAgg g hR
    have hpr := pruned_filterAllAgg g [r]
    have hcs := hpr.step_eq
    obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
    have hxid := node?_id_eq _ x n hx
    have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
    have hqg := ctxR.ownGow x n hx q hqn hq0 hq1
    have hqid : q.id = r := ReaderComplete.pin_id g r q hqg hqr
    obtain ⟨sel, hsc, hsx, hsq⟩ := ht x n₀ hx₀ hx0 (by rw [← hcs]; exact hx1) q hq0
      (by rw [← hcs]; exact hq1) (hown q hqn)
    refine ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => ?_), hsx, hsq⟩
    rw [List.mem_singleton.mp hreq, ← hqr, hsq, hqid]
  · exact h g hR hv ht r hvr x n hx hx0 hx1 q hq0 hq1 hqr hqn

/-- **Y entonces el invariante viaja con el lector**, por inducción sobre `ReadFrom`. -/
theorem tablesSound_readFrom (h : PinPairSound) (g₀ : GPathM) (hR₀ : ReadableAgg g₀)
    (ht₀ : Exactness.TablesSound g₀) :
    ∀ g, ReadFrom g₀ g → isValid g = true → Exactness.TablesSound g := by
  intro g hF
  induction hF with
  | start => intro _; exact ht₀
  | pin g' mid hF' hv' ih =>
    intro hv
    exact tablesSound_pin_of_pairs h g' (PinExact.readableAgg_of_readFrom g₀ hR₀ g' hF') hv'
      (ih hv') mid hv

/-- **El lector sin retroceso, completo desde UNA sola frase abierta.**

`PinPairSound` es lo único que queda, y es la misma frase de la que cuelga la corrida de la
máquina (`RunSteps.PinPairSoundAt`, su versión restringida al bloque literal). Las dos rutas de esta
sesión terminan en el mismo sitio.

Lo demás son condiciones sobre la **semilla**: que tenga una cadena y que sus tablas sean sanas —
los dos invariantes de la corrida, no del lector. -/
theorem readerVerdictW_of_pinPair (h : PinPairSound) (φ : Cnf) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hR₀ : ReadableAgg (filterAllAgg kv.2 []))
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (h₀ : HasChain (filterAllAgg kv.2 []))
    (ht₀ : Exactness.TablesSound (filterAllAgg kv.2 [])) :
    readerVerdictW φ = true :=
  readerVerdictW_of_tablesSound φ kv hkv hR₀ hv h₀ (tablesSound_readFrom h _ hR₀ ht₀)

-- ============================================================
-- Más estrecho todavía: solo la tabla de la raíz
-- ============================================================

/-- **El invariante que el lector consume de verdad.**

No las entradas de **todas** las tablas, sino las de la tabla del nodo del paso 0: todo lo que la
raíz posee está en un camino completo.

Es la frase del autor dicha desde la raíz — *el review deja solo nodos con camino* — y es
literalmente eso, porque toda cadena pasa por el paso 0. -/
def RootSound (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → x.id.step = 0 →
    ∀ w, w ∈ n.owners → 0 ≤ w.id.step → w.id.step < g.current_step → Realizes g x w

theorem rootSound_of_tablesSound (g : GPathM) (_hpos : 0 < g.current_step)
    (h : Exactness.TablesSound g) : RootSound g :=
  fun x n hx hx0 w hwn hw0 hw1 => h x n hx (by omega) (by omega) w hw0 hw1 hwn

/-- **Y basta para que el pin conserve la cadena.** `realizes_pin_at` solo mira las entradas del
nodo que se le pasa, y aquí ese nodo es el del paso 0. -/
theorem hasChain_pin_of_rootSound (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true)
    (ht : RootSound g) (mid : NodeId) (h0 : 0 ≤ mid.step) (h1 : mid.step < g.current_step)
    (hvr : isValid (filterAllAgg g [mid]) = true) : HasChain (filterAllAgg g [mid]) := by
  have hcs : (filterAllAgg g [mid]).current_step = g.current_step :=
    (pruned_filterAllAgg g [mid]).step_eq
  have hRp : ReadableAgg (filterAllAgg g [mid]) :=
    PinExact.readableAgg_of_readFrom g hR _ (ReadFrom.pin g mid ReadFrom.start hv)
  have rc := RCtx_of_readableAgg _ hRp
  have hpos : 0 < (filterAllAgg g [mid]).current_step := by rw [hcs]; omega
  have hent := hasStepEntry_of_isValid _ hvr 0 (Int.le_refl 0) hpos
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
  obtain ⟨q, hq, hqs⟩ := hent
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff _ q).mp (rc.gn q hq))
  obtain ⟨_, _, _, sel, hsc, _, _⟩ :=
    RunSteps.realizes_pin_at g hR mid h0 hvr (by rw [hcs]; exact h1) q n hn (by omega) (by omega)
      (fun n₀ hx₀ w hwr hwn =>
        ht q n₀ hx₀ hqs w hwn (by rw [hwr]; exact h0) (by rw [hwr]; exact h1))
  exact ⟨sel, hsc⟩

/-- **El residuo, ahora solo sobre la tabla de la raíz.**

Lo mismo que `PinPairSound` pero con `x` obligado al paso 0. Es la forma más estrecha a la que ha
bajado el frente en esta sesión. -/
def RootPairSound : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → RootSound g →
    ∀ r : NodeId, isValid (filterAllAgg g [r]) = true →
      ∀ x n, (filterAllAgg g [r]).node? x = some n → x.id.step = 0 →
        ∀ w, w ∈ n.owners → 0 ≤ w.id.step → w.id.step < (filterAllAgg g [r]).current_step →
          w.id.step ≠ r.step → Realizes (filterAllAgg g [r]) x w

/-- **El paso pinchado sigue siendo gratis**, también desde la raíz. -/
theorem rootSound_pin_of_pairs (h : RootPairSound) (g : GPathM) (hR : ReadableAgg g)
    (hv : isValid g = true) (ht : RootSound g) (r : NodeId)
    (hvr : isValid (filterAllAgg g [r]) = true) : RootSound (filterAllAgg g [r]) := by
  intro x n hx hx0 w hwn hw0 hw1
  rcases int_eq_or_ne w.id.step r.step with hwr | hwr
  · have hRr := ReadableAgg_filterAllAgg g hR [r]
    have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
    have rcg := RCtx_of_readableAgg g hR
    have hpr := pruned_filterAllAgg g [r]
    have hcs := hpr.step_eq
    obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
    have hxid := node?_id_eq _ x n hx
    have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
    have hwg := ctxR.ownGow x n hx w hwn hw0 hw1
    have hwid : w.id = r := ReaderComplete.pin_id g r w hwg hwr
    obtain ⟨sel, hsc, hsx, hsw⟩ :=
      ht x n₀ hx₀ hx0 w (hown w hwn) hw0 (by rw [← hcs]; exact hw1)
    refine ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => ?_), hsx, hsw⟩
    rw [List.mem_singleton.mp hreq, ← hwr, hsw, hwid]
  · exact h g hR hv ht r hvr x n hx hx0 w hwn hw0 hw1 hwr

theorem rootSound_readFrom (h : RootPairSound) (g₀ : GPathM) (hR₀ : ReadableAgg g₀)
    (ht₀ : RootSound g₀) : ∀ g, ReadFrom g₀ g → isValid g = true → RootSound g := by
  intro g hF
  induction hF with
  | start => intro _; exact ht₀
  | pin g' mid hF' hv' ih =>
    intro hv
    exact rootSound_pin_of_pairs h g' (PinExact.readableAgg_of_readFrom g₀ hR₀ g' hF') hv'
      (ih hv') mid hv

theorem pinKeepsChain_of_rootSound (g₀ : GPathM) (hR₀ : ReadableAgg g₀) (h₀ : HasChain g₀)
    (hrs : ∀ g, ReadFrom g₀ g → isValid g = true → RootSound g) :
    ∀ g, ReadFrom g₀ g → isValid g = true → HasChain g := by
  intro g hF
  induction hF with
  | start => intro _; exact h₀
  | pin g' mid hF' hv' ih =>
    intro hv
    have hR' : ReadableAgg g' := PinExact.readableAgg_of_readFrom g₀ hR₀ g' hF'
    if hin : 0 ≤ mid.step ∧ mid.step < g'.current_step then
      exact hasChain_pin_of_rootSound g' hR' hv' (hrs g' hF' hv') mid hin.1 hin.2 hv
    else
      exact hasChain_out_of_range g' mid (ih hv') hin

/-- **El lector sin retroceso, completo desde la frase más estrecha de la sesión.**

`RootPairSound` habla de **un estado, un pin, y la tabla de la raíz**. No menciona φ, no cuantifica
sobre nodos, y no pide nada de las tablas de los demás. -/
theorem readerVerdictW_of_rootPair (h : RootPairSound) (φ : Cnf) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hR₀ : ReadableAgg (filterAllAgg kv.2 []))
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (h₀ : HasChain (filterAllAgg kv.2 []))
    (ht₀ : RootSound (filterAllAgg kv.2 [])) :
    readerVerdictW φ = true :=
  readerVerdictW_complete φ kv hkv hv
    (progressAgg_of_chains _ (pinKeepsChain_of_rootSound _ hR₀ h₀
      (rootSound_readFrom h _ hR₀ ht₀)))

-- ============================================================
-- Y el trío se deshace: un PAR, no tres cosas
-- ============================================================

/-- **La frase del autor, literal.**

*Al aplicar el review sobre todo el grafo dejamos únicamente nodos con caminos válidos* — dicho de
la tabla de la raíz: **todo lo que el nodo del paso 0 posee está en una cadena completa.**

Nótese lo que **no** dice, comparado con `RootSound`: no pide que la cadena pase también por la
raíz. Es un enunciado sobre **un** nodo, no sobre un par. Y es todo lo que el lector consume, porque
`RunSteps.chain_pin_at` tira la pata de la raíz.

Que la raíz no sea única (medido: dos nodos en el paso 0 en un 20–36% de los estados) deja de
importar por lo mismo. -/
def RootChained (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → x.id.step = 0 →
    ∀ w, w ∈ n.owners → 0 ≤ w.id.step → w.id.step < g.current_step →
      ∃ sel, ChainSound g sel ∧ sel w.id.step = w

theorem rootChained_of_rootSound (g : GPathM) (h : RootSound g) : RootChained g := by
  intro x n hx hx0 w hwn hw0 hw1
  obtain ⟨sel, hsc, _, hsw⟩ := h x n hx hx0 w hwn hw0 hw1
  exact ⟨sel, hsc, hsw⟩

/-- **Y basta para que el pin conserve la cadena.** -/
theorem hasChain_pin_of_rootChained (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true)
    (ht : RootChained g) (mid : NodeId) (h0 : 0 ≤ mid.step) (h1 : mid.step < g.current_step)
    (hvr : isValid (filterAllAgg g [mid]) = true) : HasChain (filterAllAgg g [mid]) := by
  have hcs : (filterAllAgg g [mid]).current_step = g.current_step :=
    (pruned_filterAllAgg g [mid]).step_eq
  have hRp : ReadableAgg (filterAllAgg g [mid]) :=
    PinExact.readableAgg_of_readFrom g hR _ (ReadFrom.pin g mid ReadFrom.start hv)
  have rc := RCtx_of_readableAgg _ hRp
  have hpos : 0 < (filterAllAgg g [mid]).current_step := by rw [hcs]; omega
  have hent := hasStepEntry_of_isValid _ hvr 0 (Int.le_refl 0) hpos
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
  obtain ⟨q, hq, hqs⟩ := hent
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff _ q).mp (rc.gn q hq))
  exact RunSteps.chain_pin_at g hR mid h0 hvr (by rw [hcs]; exact h1) q n hn (by omega) (by omega)
    (fun n₀ hx₀ w hwr hwn =>
      ht q n₀ hx₀ hqs w hwn (by rw [hwr]; exact h0) (by rw [hwr]; exact h1))

/-- **El residuo, ahora un PAR y no un trío.**

Todo owner de la raíz que sobrevive al pin está en una cadena **que pasa por el pin**. Dos cosas:
el owner y el pin. Antes (`RootPairSound`) eran tres: la raíz, el owner y el pin.

Y dos es el lado de la frontera donde la máquina es exacta: esta sesión midió que la criba alcanza
la consistencia de caminos completa (`Descent.path_consistent_witness`) y falla solo de tres en
adelante. -/
def RootPinChained : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → RootChained g →
    ∀ r : NodeId, isValid (filterAllAgg g [r]) = true →
      ∀ x n, (filterAllAgg g [r]).node? x = some n → x.id.step = 0 →
        ∀ w, w ∈ n.owners → 0 ≤ w.id.step → w.id.step < (filterAllAgg g [r]).current_step →
          w.id.step ≠ r.step →
          ∃ sel, ChainSound (filterAllAgg g [r]) sel ∧ sel w.id.step = w

/-- **El paso pinchado, gratis otra vez.** Un owner de la raíz en el paso del pin **es** el pin
(`ReaderComplete.pin_id`), su cadena ya existía, y esa cadena pasa por el pin — luego sobrevive. -/
theorem rootChained_pin_of_pairs (h : RootPinChained) (g : GPathM) (hR : ReadableAgg g)
    (hv : isValid g = true) (ht : RootChained g) (r : NodeId)
    (hvr : isValid (filterAllAgg g [r]) = true) : RootChained (filterAllAgg g [r]) := by
  intro x n hx hx0 w hwn hw0 hw1
  rcases int_eq_or_ne w.id.step r.step with hwr | hwr
  · have hRr := ReadableAgg_filterAllAgg g hR [r]
    have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
    have rcg := RCtx_of_readableAgg g hR
    have hpr := pruned_filterAllAgg g [r]
    have hcs := hpr.step_eq
    obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
    have hxid := node?_id_eq _ x n hx
    have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
    have hwid : w.id = r :=
      ReaderComplete.pin_id g r w (ctxR.ownGow x n hx w hwn hw0 hw1) hwr
    obtain ⟨sel, hsc, hsw⟩ := ht x n₀ hx₀ hx0 w (hown w hwn) hw0 (by rw [← hcs]; exact hw1)
    exact ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => by
      rw [List.mem_singleton.mp hreq, ← hwr, hsw, hwid]), hsw⟩
  · exact h g hR hv ht r hvr x n hx hx0 w hwn hw0 hw1 hwr

theorem rootChained_readFrom (h : RootPinChained) (g₀ : GPathM) (hR₀ : ReadableAgg g₀)
    (ht₀ : RootChained g₀) : ∀ g, ReadFrom g₀ g → isValid g = true → RootChained g := by
  intro g hF
  induction hF with
  | start => intro _; exact ht₀
  | pin g' mid hF' hv' ih =>
    intro hv
    exact rootChained_pin_of_pairs h g' (PinExact.readableAgg_of_readFrom g₀ hR₀ g' hF') hv'
      (ih hv') mid hv

theorem pinKeepsChain_of_rootChained (g₀ : GPathM) (hR₀ : ReadableAgg g₀) (h₀ : HasChain g₀)
    (hrc : ∀ g, ReadFrom g₀ g → isValid g = true → RootChained g) :
    ∀ g, ReadFrom g₀ g → isValid g = true → HasChain g := by
  intro g hF
  induction hF with
  | start => intro _; exact h₀
  | pin g' mid hF' hv' ih =>
    intro hv
    have hR' : ReadableAgg g' := PinExact.readableAgg_of_readFrom g₀ hR₀ g' hF'
    if hin : 0 ≤ mid.step ∧ mid.step < g'.current_step then
      exact hasChain_pin_of_rootChained g' hR' hv' (hrc g' hF' hv') mid hin.1 hin.2 hv
    else
      exact hasChain_out_of_range g' mid (ih hv') hin

/-- **El lector sin retroceso, completo, desde un enunciado sobre dos nodos.**

`RootPinChained`: un estado, un pin, la tabla de la raíz, y **dos** cosas —el owner y el pin—.
No menciona φ, no cuantifica sobre nodos, no habla de tríos. -/
theorem readerVerdictW_of_rootPinChained (h : RootPinChained) (φ : Cnf) (kv : NodeId × GPathM)
    (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hR₀ : ReadableAgg (filterAllAgg kv.2 []))
    (hv : isValid (filterAllAgg kv.2 []) = true)
    (h₀ : HasChain (filterAllAgg kv.2 []))
    (ht₀ : RootChained (filterAllAgg kv.2 [])) :
    readerVerdictW φ = true :=
  readerVerdictW_complete φ kv hkv hv
    (progressAgg_of_chains _ (pinKeepsChain_of_rootChained _ hR₀ h₀
      (rootChained_readFrom h _ hR₀ ht₀)))

/-- **Y el residuo se cierra con PARES: el pin se cae solo.**

La supervivencia al pin da un testigo `z` en el paso pinchado que la raíz y `w` **comparten**
(`SupportedRun.shared_pin_witness`, vía `AggOk` del estado pinchado). `TablesSound` del estado de
antes da una cadena por `w` **y por `z`** —un par, no un trío—, y esa cadena pasa por el pin porque
`z` lleva el pin. Luego sobrevive a la criba.

**No se pega nada.** Es lo que `ChainMerge` no podía hacer y aquí no hace falta, porque la pata de
la raíz se tiró antes.

Y con eso queda dicha la estructura entera del problema:

* el lector necesita **singles** — que haya una cadena (`HasChain`);
* propagar `RootChained` (singles) por un pin pide **pares** — `TablesSound`, medido al 100% sobre
  150.124 entradas de estados de lectura sin una sola excepción;
* propagar `TablesSound` (pares) por un pin pide **tríos** — `PinPairSound`, y ahí está el muro,
  que es la frontera 2-vs-3 que esta sesión ha visto caer cinco hipótesis.

El lector, por tanto, **no añade nada** al problema abierto de la máquina. -/
theorem rootChained_pin_of_tablesSound (g : GPathM) (hR : ReadableAgg g)
    (ht : Exactness.TablesSound g) (r : NodeId) (hr0 : 0 ≤ r.step)
    (hvr : isValid (filterAllAgg g [r]) = true)
    (hrs : r.step < (filterAllAgg g [r]).current_step)
    (hpms : Sons.PMS (filterAllAgg g [r])) (hsn : Sons.SN (filterAllAgg g [r])) :
    RootChained (filterAllAgg g [r]) := by
  intro x n hx hx0 w hwn hw0 hw1
  have hpr := pruned_filterAllAgg g [r]
  have hcs := hpr.step_eq
  have hRr := ReadableAgg_filterAllAgg g hR [r]
  have rcr := RCtx_of_readableAgg _ hRr
  have rcg := RCtx_of_readableAgg g hR
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
  -- `w` es nodo del estado pinchado
  have hwg := ctxR.ownGow x n hx w hwn hw0 hw1
  obtain ⟨mw, hmw⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff _ w).mp (rcr.gn w hwg))
  -- el testigo compartido en el paso del pin
  obtain ⟨z, hzid, _, hzw⟩ :=
    SupportedRun.shared_pin_witness g hR r hvr hr0 hrs hpms hsn x w n mw hx hmw
      (by omega) (by omega) hw0 hw1 hwn
  -- y el par `(w, z)` en el estado de antes
  obtain ⟨mw₀, hmw₀, hid, hown, _⟩ := hpr.nodes_derived mw (List.mem_of_find?_eq_some hmw)
  have hwid := node?_id_eq _ w mw hmw
  have hw₀ : g.node? w = some mw₀ := by rw [← hwid, hid]; exact node?_of_mem rcg.nodup mw₀ hmw₀
  have hzs : z.id.step = r.step := by rw [hzid]
  obtain ⟨sel, hsc, hsw, hsz⟩ :=
    ht w mw₀ hw₀ hw0 (by rw [← hcs]; exact hw1) z (by rw [hzs]; exact hr0)
      (by rw [hzs, ← hcs]; exact hrs) (hown z hzw)
  exact ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => by
    rw [List.mem_singleton.mp hreq, ← hzs, hsz, hzid]), hsw⟩

-- ============================================================
-- El muro, atacado con `AggOk`: la semilla es gratis, el paso no
-- ============================================================

/-- **La semilla del descenso por pares, gratis.**

Para demostrar `PinPairSound` lo natural es descender construyendo la cadena y manteniendo que
**todo pick posee a `x` y a `q`**. La semilla de ese descenso sale sola de `AggOk`: si `q` está en
la tabla de `x`, la criba obliga a que compartan un owner en **todos** los pasos, y en el de arriba
ese owner común, por la simetría de `AggOk`, los posee a los dos.

Medido (`row-degree pairdesc`): **34.124 de 34.124 pares, el 100%.** -/
theorem pair_seed (g : GPathM) (a : AdjacentOwners.Adj g) (hok : AggFixpoint.AggOk g) (hpos : 0 < g.current_step)
    (x q : PathNodeId) (nx nq : PNodeM) (hx : g.node? x = some nx) (hq : g.node? q = some nq)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < g.current_step)
    (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < g.current_step) (hqn : q ∈ nx.owners) :
    ∃ t nt, g.node? t = some nt ∧ t.id.step = g.current_step - 1 ∧
      x ∈ nt.owners ∧ q ∈ nt.owners := by
  obtain ⟨z, hzx, hzq, hzs⟩ :=
    ParentWitness.shared_owner a hok hx hq hx0 hx1 hq0 hq1 hqn (g.current_step - 1)
      (by omega) (by omega)
  have hzg : z ∈ g.gowners := a.ctx.ownGow x nx hx z hzx (by omega) (by omega)
  obtain ⟨nz, hnz⟩ :=
    Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g z).mp (a.rc.gn z hzg))
  exact ⟨z, nz, hnz, hzs,
    (hok x nx z nz hx hnz hx0 hx1 (by omega) (by omega) hzx
      (a.ctx.nodeval x nx hx) (a.ctx.nodeval z nz hnz)).1,
    (hok q nq z nz hq hnz hq0 hq1 (by omega) (by omega) hzq
      (a.ctx.nodeval q nq hq) (a.ctx.nodeval z nz hnz)).1⟩

/-- **El paso del descenso por pares, sobre el grafo EN CRUDO.**

Dado un nodo `d` que posee a `x` y a `q`, ¿hay un **padre** de `d` que también los posea a los dos?
Eso es `Descent.PairMeet` restringido al par que se desciende — y **es falso**:

> medido, 140 fallos sobre 871.843 celdas `(par, nodo que posee a los dos)`; el descenso con
> retroceso llega al paso 0 en los 34.124 pares, y sin retroceso en el 99,8%.

**Aviso sobre qué mide eso, porque me equivoqué al leerlo la primera vez.** Este descenso camina
enlaces padre-hijo **sin revisar**, y eso **no es lo que hace el lector**: el lector pincha y
después aplica `filterAllAgg` sobre todo el grafo, que borra las ramas sin continuación antes de
volver a elegir. Los fallos de arriba son ramas que la revisión habría quitado, no elecciones que el
algoritmo pueda tomar.

Con la revisión dentro del bucle —`row-degree pairdesc`, columna «como lo hace el lector»— el
descenso ávido, sin retroceso nunca, llega arriba en **1.016 de 1.016 pares** sobre
`dos_de_tres.cnf`, que es justo la fórmula del contraejemplo al pegado puro.

Así que esta definición se deja escrita para lo que de verdad dice: **la regla local sobre el grafo
en crudo es falsa**, y toda prueba que intente descender por enlaces sin revisar va a chocar con
esos 140 casos. La prueba tiene que descender sobre el estado **revisado**. -/
def PairDescends : Prop :=
  ∀ (g : GPathM) (x q : PathNodeId) (nx : PNodeM), g.node? x = some nx → q ∈ nx.owners →
    ∀ d nd, g.node? d = some nd → 0 < d.id.step → x ∈ nd.owners → q ∈ nd.owners →
      ∃ c ∈ nd.parents, ∀ mc, g.node? c = some mc → x ∈ mc.owners ∧ q ∈ mc.owners

-- ============================================================
-- El descenso CON revisión, que es el que el algoritmo hace
-- ============================================================

/-- **El compañero está en la rebanada del pin.**

Si `q` está en la tabla de `x`, la simetría de `AggOk` pone a `x` en la de `q` — o sea, `q` está en
la **rebanada** de `x.id` (`PinExact.InSlice`: tiene un owner que lleva el pin).

Y eso conecta el descenso por pares con `PinExact`, la conjetura más antigua del repo y una de las
medidas sin excepción: **`PinExact` basta para que `q` sobreviva a pinchar `x`.** El primer paso del
descenso con revisión sale gratis. -/
theorem partner_inSlice (P : GPathM) (hok : AggFixpoint.AggOk P) (ctx : Pinned.Ctx P)
    (x q : PathNodeId) (nx nq : PNodeM) (hx : P.node? x = some nx) (hq : P.node? q = some nq)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < P.current_step)
    (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < P.current_step) (hqn : q ∈ nx.owners) :
    PinExact.InSlice nq x.id :=
  ⟨x, (hok x nx q nq hx hq hx0 hx1 hq0 hq1 hqn (ctx.nodeval x nx hx) (ctx.nodeval q nq hq)).1, rfl⟩

/-- **Y entonces `q` sobrevive a pinchar `x`.** -/
theorem partner_survives_pin (P : GPathM) (hok : AggFixpoint.AggOk P) (ctx : Pinned.Ctx P)
    (x q : PathNodeId) (nx nq : PNodeM) (hx : P.node? x = some nx) (hq : P.node? q = some nq)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < P.current_step)
    (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < P.current_step) (hqn : q ∈ nx.owners)
    (hpe : PinExact.PinExact P x.id) :
    q ∈ (filterAllAgg P [x.id]).gowners := by
  have h := hpe nq (List.mem_of_find?_eq_some hq)
    (partner_inSlice P hok ctx x q nx nq hx hq hx0 hx1 hq0 hq1 hqn)
  rwa [node?_id_eq P q nq hq] at h

/-- **Lo que queda del descenso con revisión, en una frase.**

El algoritmo no desciende por enlaces: pincha, **revisa todo el grafo**, y vuelve a elegir. Montado
así, el paso del descenso por pares es este — y `partner_survives_pin` ya da la mitad (que `q`
sobrevive), con `PinExact` como única entrada.

Lo que falta es la otra mitad: que tras la revisión `q` **siga estando en la tabla de `x`**. La
criba solo puede quitarlo si deja de compartir owner con `x` en algún paso, y eso es lo que el
diseño dice que no puede pasar: pinchar `x` no puede volver incompatible con `x` a algo que ya era
compatible con `x`.

Medido (`row-degree pairdesc`, columna «como lo hace el lector», con revisión en cada paso, sin
retroceso nunca): **1.016 de 1.016 pares sobre `dos_de_tres.cnf`**, que es la fórmula del
contraejemplo al pegado puro. -/
def PinKeepsPartner : Prop :=
  ∀ P : GPathM, ReadableAgg P → isValid P = true →
    ∀ x q : PathNodeId, ∀ nx : PNodeM, P.node? x = some nx → q ∈ nx.owners →
      0 ≤ x.id.step → x.id.step < P.current_step →
      0 ≤ q.id.step → q.id.step < P.current_step → q.id.step ≠ x.id.step →
      isValid (filterAllAgg P [x.id]) = true →
      ∃ nx', (filterAllAgg P [x.id]).node? x = some nx' ∧ q ∈ nx'.owners

/-- **El pin no quita nada: solo la revisión puede.**

`filterRequire` reescribe únicamente `gowners` — no toca ninguna tabla —, así que tras pinchar y
**antes** de revisar, `q` sigue en la de `x`, sin hipótesis ninguna. Toda la obligación de
`PinKeepsPartner` cae por tanto sobre `reviewAgg`, y eso vale la pena dejarlo escrito porque
localiza el problema en una sola operación. -/
theorem partner_after_filterRequire (P : GPathM) (req : NodeId) (x q : PathNodeId) (nx : PNodeM)
    (hx : P.node? x = some nx) (hqn : q ∈ nx.owners) :
    (filterRequire P req).node? x = some nx ∧ q ∈ nx.owners := ⟨hx, hqn⟩

/-- **La forma fuerte, y la que el diseño hace evidente: una tabla sobrevive a su propio pin.**

Todo lo que está en la tabla de `x` es compatible con `x` — es lo que la tabla *significa* —, así
que pinchar `x` no debería poder quitárselo. Ni a `x` mismo.

Medido (`row-degree owntable`, sobre los estados que el lector recorre):

| corpus | nodos | entradas | perdidas |
|---|---|---|---|
| `dos_de_tres.cnf` | 73 | 1.016 | **0** |
| 12 fórmulas aleatorias (semilla 1) | 1.012 | 78.552 | **0** |
| 12 fórmulas aleatorias (semilla 7) | 1.176 | 125.523 | **0** |
| **total** | **2.261** | **205.091** | **0** |

Y el nodo nunca desaparece: pinchar el propio nodo deja el grafo válido en los 2.261 casos.

Con ella `PinKeepsPartner` es inmediato, y con `partner_survives_pin` cierra el descenso con
revisión por pares. -/
def PinKeepsOwnTable : Prop :=
  ∀ P : GPathM, ReadableAgg P → isValid P = true →
    ∀ x nx, P.node? x = some nx → isValid (filterAllAgg P [x.id]) = true →
      ∃ nx', (filterAllAgg P [x.id]).node? x = some nx' ∧
        ∀ u ∈ nx.owners, u.id.step ≠ x.id.step → u ∈ nx'.owners

theorem pinKeepsPartner_of_ownTable (h : PinKeepsOwnTable) : PinKeepsPartner := by
  intro P hR hv x q nx hx hqn _ _ _ _ hne hvr
  obtain ⟨nx', hnx', hkeep⟩ := h P hR hv x nx hx hvr
  exact ⟨nx', hnx', hkeep q hqn hne⟩

/-- **Y la vuelta: `TablesSound` da `PinKeepsOwnTable`.**

Si toda entrada de la tabla de `x` está en una cadena, esa cadena pasa por `x`, luego **pasa el
pin** `x.id` por construcción, luego sobrevive entera a la revisión
(`ChainSound_filterAllAgg`) — y en el estado pinchado sus picks se siguen poseyendo, así que la
entrada sigue ahí.

Lo escribo porque es el dato que cierra el círculo, y conviene que quede constancia: **la única
garantía de conservación que la criba ofrece es «estar en una cadena»**. Por eso toda reformulación
de `TablesSound` —`PinPairSound`, `RootPinChained`, `PinKeepsPartner`, `PinKeepsOwnTable`— termina
pidiendo `TablesSound` otra vez. No es mala suerte: es que el punto fijo de la criba no sabe
conservar nada más.

**Consecuencia para el ataque**: la prueba de `TablesSound` no puede salir del punto fijo. Tiene que
salir de la **construcción** de la máquina —`up`, `doJoin`, filtro, revisión—, que es donde
`ConservationImproves.pureRunW_full_chain` vive y donde `readerVerdictBT_iff` se cerró sin
hipótesis. Y de esos cuatro, tres están: la revisión es `RunInhabited.soundAt_review`, y el que
falta es el **filtro**, que es exactamente `RunSteps.FilterSoundAt`. -/
theorem ownTable_of_tablesSound (P : GPathM) (ht : Exactness.TablesSound P)
    (x : PathNodeId) (nx : PNodeM) (hx : P.node? x = some nx)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < P.current_step) (hself : x ∈ nx.owners) :
    ∃ nx', (filterAllAgg P [x.id]).node? x = some nx' ∧
      ∀ u ∈ nx.owners, u.id.step ≠ x.id.step → 0 ≤ u.id.step → u.id.step < P.current_step →
        u ∈ nx'.owners := by
  have hcs : (filterAllAgg P [x.id]).current_step = P.current_step :=
    (pruned_filterAllAgg P [x.id]).step_eq
  -- la cadena por `x` consigo mismo sobrevive al pin, así que `x` sigue siendo nodo
  have hkeep : ∀ (v : PathNodeId) (sel : Int → PathNodeId), ChainSound P sel →
      sel x.id.step = x → ChainSound (filterAllAgg P [x.id]) sel := by
    intro _ sel hsc hsx
    exact ChainSound_filterAllAgg P [x.id] sel hsc (fun req hreq _ _ => by
      rw [List.mem_singleton.mp hreq, hsx])
  obtain ⟨sel₀, hsc₀, hsx₀, _⟩ := ht x nx hx hx0 hx1 x hx0 hx1 hself
  have hsc₀' := hkeep x sel₀ hsc₀ hsx₀
  obtain ⟨hsome, _⟩ := hsc₀'.chain.1.1 x.id.step hx0 (by rw [hcs]; exact hx1)
  rw [hsx₀] at hsome
  obtain ⟨nx', hnx'⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨nx', hnx', ?_⟩
  intro u hu hne hu0 hu1
  -- la cadena por `x` y por `u`, que también pasa el pin
  obtain ⟨sel, hsc, hsx, hsu⟩ := ht x nx hx hx0 hx1 u hu0 hu1 hu
  have hsc' := hkeep u sel hsc hsx
  -- y la posesión por pares del estado pinchado devuelve la entrada
  have hmem := hsc'.chain.2.1 u.id.step x.id.step hu0 hx0
    (by rw [hcs]; exact hu1) (by rw [hcs]; exact hx1) hne
  rw [hsu, hsx] at hmem
  simp only [ownersAt, List.mem_filter, ownersOf, hnx'] at hmem
  exact hmem.1

-- ============================================================
-- «Si el nodo sigue presente es porque tiene camino»
-- ============================================================

/-- **La frase del autor, y sale de menos de lo que parecía.**

> *si el nodo `x` sigue presente es porque tiene un camino de compatibles que lo lleva a configurar
> una solución*

Para que un superviviente tenga cadena **no hace falta la sanidad de todas sus entradas**: basta la
de las entradas **en el paso del pin**. `RunSteps.realizes_pin_at` hace el resto — el nodo vivo
tiene un owner en el paso pinchado, ese owner lleva el pin (`ReaderComplete.pin_id`), la cadena que
lo realizaba antes del pin pasa por él, y por tanto sobrevive al filtro.

Es un recorte real de la hipótesis: `SupportedS` del estado pinchado —*todo nodo tiene camino*—
cuelga solo de los pares `(x, owner de x en el paso del pin)`, no de todos los pares. Y de esos,
los que no tienen elección ya están cerrados
(`TablesSoundBuild.realizes_pin_of_singleId`, el 65–90 % medido). -/
theorem supportedS_pin_of_pinStepSound (g : GPathM) (hR : ReadableAgg g) (r : NodeId)
    (hr0 : 0 ≤ r.step) (hvr : isValid (filterAllAgg g [r]) = true)
    (hrs : r.step < (filterAllAgg g [r]).current_step)
    (ht : ∀ x n₀, g.node? x = some n₀ → ∀ w, w.id.step = r.step → w ∈ n₀.owners →
      Exactness.Realizes g x w) :
    SupportedS (filterAllAgg g [r]) := by
  have hRp : ReadableAgg (filterAllAgg g [r]) := ReadableAgg_filterAllAgg g hR [r]
  have rc := RCtx_of_readableAgg _ hRp
  intro x n hx
  have hmem := List.mem_of_find?_eq_some hx
  have hid : n.id = x := node?_id_eq _ x n hx
  have hx0 : 0 ≤ x.id.step := by have := rc.snn n hmem; rwa [hid] at this
  have hx1 : x.id.step < (filterAllAgg g [r]).current_step := by
    have := rc.below n hmem; rwa [hid] at this
  obtain ⟨_, _, _, sel, hsc, hsx, _⟩ :=
    RunSteps.realizes_pin_at g hR r hr0 hvr hrs x n hx hx0 hx1
      (fun n₀ h₀ w hwr hwn => ht x n₀ h₀ w hwr hwn)
  exact ⟨sel, hsc, hsx⟩

/-- **Y con la frase del autor, el lector tiene su cadena.** `SupportedS` da una cadena por cada
nodo, y basta una: la del nodo del paso 0 que la validez garantiza. -/
theorem hasChain_of_pinStepSound (g : GPathM) (hR : ReadableAgg g) (r : NodeId)
    (hr0 : 0 ≤ r.step) (hr1 : r.step < g.current_step)
    (hvr : isValid (filterAllAgg g [r]) = true)
    (ht : ∀ x n₀, g.node? x = some n₀ → ∀ w, w.id.step = r.step → w ∈ n₀.owners →
      Exactness.Realizes g x w) :
    HasChain (filterAllAgg g [r]) := by
  have hcs : (filterAllAgg g [r]).current_step = g.current_step :=
    (pruned_filterAllAgg g [r]).step_eq
  have hRp : ReadableAgg (filterAllAgg g [r]) := ReadableAgg_filterAllAgg g hR [r]
  have rc := RCtx_of_readableAgg _ hRp
  exact hasChain_of_supportedS _ (by rw [hcs]; omega) hvr rc.gn
    (supportedS_pin_of_pinStepSound g hR r hr0 hvr (by rw [hcs]; exact hr1) ht)

/-- **Y todavía menos: basta que la cadena elija el ID DE MAPA del pin, no un nodo concreto.**

`supportedS_pin_of_pinStepSound` pedía `Realizes g x w` — una cadena por **dos** `PathNodeId`. Pero
lo único que el filtro comprueba es el **id de mapa** del pick: `ChainSound_filterAllAgg` pide
`(sel r.step).id = r` y nada más.

Y eso es mucho menos. En un paso literal el mapa tiene **dos** nodos, así que fijar el id de mapa es
una condición binaria; fijar el `PathNodeId` es mucho más fuerte, porque varios nodos del grafo
comparten id de mapa y difieren en su historia.

Así que el residuo pasa de «un par de nodos» a «**un nodo y una elección binaria**». -/
def PinCompatChain (g : GPathM) (r : NodeId) : Prop :=
  ∀ x n₀, g.node? x = some n₀ → ((filterAllAgg g [r]).node? x).isSome = true →
    ∃ sel, ChainSound g sel ∧ sel x.id.step = x ∧ (sel r.step).id = r

theorem supportedS_pin_of_compatChain (g : GPathM) (hR : ReadableAgg g) (r : NodeId)
    (h : PinCompatChain g r) : SupportedS (filterAllAgg g [r]) := by
  intro x n hx
  have hpr := pruned_filterAllAgg g [r]
  have rcg := RCtx_of_readableAgg g hR
  obtain ⟨n₀, hn₀, hid, _, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
  have hxid := node?_id_eq _ x n hx
  have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
  obtain ⟨sel, hsc, hsx, hsr⟩ := h x n₀ hx₀ (by rw [hx]; rfl)
  exact ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => by
    rw [List.mem_singleton.mp hreq]; exact hsr), hsx⟩

/-- **Y donde el paso ya no tiene elección, la frase del autor se propaga sola.**

Si todas las tablas llevan ya el pin en ese paso (`TablesSoundBuild.SingleIdAt`, escrito aquí
desplegado para no invertir la dependencia entre módulos), la cadena que
`SupportedS` da por `x` elige allí un owner de `x` — posesión por pares —, ese owner lleva el pin, y
la cadena sobrevive.

**Es la primera vez que `SupportedS` atraviesa un pin sin ninguna hipótesis abierta.** Y por
`TablesSoundBuild.singleIdAt_of_pruned`, un paso que ya se fijó cumple `SingleIdAt` para siempre:
así que todo pin que el lector repita sobre la zona ya fijada es gratis, y solo el frente de la
lectura cuesta. -/
theorem pinCompatChain_of_singleId (g : GPathM) (r : NodeId)
    (hr0 : 0 ≤ r.step) (hrs : r.step < g.current_step)
    (hb : ∀ x n, g.node? x = some n → 0 ≤ x.id.step ∧ x.id.step < g.current_step)
    (hsup : SupportedS g)
    (hsingle : ∀ x nx, g.node? x = some nx → ∀ u ∈ nx.owners, u.id.step = r.step → u.id = r)
    (hself : ∀ pid n, g.node? pid = some n → pid ∈ n.owners) : PinCompatChain g r := by
  intro x n₀ hx₀ _
  obtain ⟨hx0, hx1⟩ := hb x n₀ hx₀
  obtain ⟨sel, hsc, hsx⟩ := hsup x n₀ hx₀
  refine ⟨sel, hsc, hsx, ?_⟩
  rcases int_eq_or_ne r.step x.id.step with he | hne
  · rw [he, hsx]
    exact hsingle x n₀ hx₀ x (hself x n₀ hx₀) he.symm
  · have hmem := hsc.chain.2.1 r.step x.id.step hr0 hx0 hrs hx1 hne
    rw [hsx] at hmem
    simp only [ownersAt, List.mem_filter, ownersOf, hx₀] at hmem
    exact hsingle x n₀ hx₀ _ hmem.1 (eq_of_beq hmem.2)

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.supportedS_pin_of_compatChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms supportedS_pin_of_compatChain

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.pinCompatChain_of_singleId' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinCompatChain_of_singleId

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.supportedS_pin_of_pinStepSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms supportedS_pin_of_pinStepSound

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.hasChain_of_pinStepSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasChain_of_pinStepSound

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.ownTable_of_tablesSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownTable_of_tablesSound

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.pinKeepsPartner_of_ownTable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pinKeepsPartner_of_ownTable

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.partner_after_filterRequire' does not depend on any axioms -/
#guard_msgs in
#print axioms partner_after_filterRequire

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.partner_survives_pin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms partner_survives_pin

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.partner_inSlice' does not depend on any axioms -/
#guard_msgs in
#print axioms partner_inSlice

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.pair_seed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pair_seed

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.rootChained_pin_of_tablesSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rootChained_pin_of_tablesSound

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.readerVerdictW_of_rootPinChained' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_of_rootPinChained

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.rootChained_pin_of_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rootChained_pin_of_pairs

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.readerVerdictW_of_rootPair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_of_rootPair

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.rootSound_pin_of_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rootSound_pin_of_pairs

-- ============================================================
-- La forma exacta del hueco: un ∃ frente a un ∀
-- ============================================================

/-- **El lector siempre TIENE un pin bueno: el que su propia cadena elige.**

Si el estado tiene una cadena, pinchar el nodo que la cadena escoge en ese paso la conserva entera
(`ChainSound_filterAllAgg`), y una cadena hace válido al estado (`isValid_of_ChainG`). Así que en
todo estado con cadena hay, en todo paso, **al menos un** pin que deja el grafo válido **y con
cadena**.

Demostrado, sin hipótesis. -/
theorem goodPin_exists (g : GPathM) (h : HasChain g) (k : Int) (h0 : 0 ≤ k)
    (h1 : k < g.current_step) :
    ∃ q ∈ ownersAt g.gowners k, isValid (filterAllAgg g [q.id]) = true ∧
      HasChain (filterAllAgg g [q.id]) := by
  obtain ⟨sel, hsc⟩ := h
  obtain ⟨_, hstep⟩ := hsc.chain.1.1 k h0 h1
  have hkeep : ChainSound (filterAllAgg g [(sel k).id]) sel :=
    ChainSound_filterAllAgg g [(sel k).id] sel hsc (fun req hreq _ _ => by
      rw [List.mem_singleton.mp hreq, hstep])
  exact ⟨sel k, List.mem_filter.mpr ⟨hsc.chain.2.2 k h0 h1, beq_iff_eq.mpr hstep⟩,
    PickInduction.isValid_of_ChainG _ sel hkeep.chain, ⟨sel, hkeep⟩⟩

/-- **Y el hueco entero es el salto de ese `∃` a un `∀`.**

`goodPin_exists` da **un** pin bueno. El lector sin retroceso toma el **primero que deja el grafo
válido**, que no tiene por qué ser ése. Para que su elección sea siempre correcta hace falta que
**todo** pin válido sea bueno — que es esto. -/
def AllValidPinsGood : Prop :=
  ∀ (g : GPathM) (q : PathNodeId), HasChain g → isValid (filterAllAgg g [q.id]) = true →
    HasChain (filterAllAgg g [q.id])

theorem pinKeepsChain_of_allValidPinsGood (h : AllValidPinsGood) : PinKeepsChain :=
  fun g mid _ hc hv => by
    -- el pin del lector es siempre el id de un owner global, luego de la forma `q.id`
    exact h g ⟨mid, none, none⟩ hc hv

/-! **Y esto ordena las dos direcciones del problema, que no son la misma:**

* **La corrección de la máquina está cerrada.** `ReaderBT.readerVerdictBT_iff` decide 3-SAT sin
  ninguna hipótesis, y `ReaderExec.readerVerdictW_sound` dice que lo que el lector sin retroceso
  devuelve es siempre un modelo de verdad. Un pin malo **no puede** producir un SAT falso: la salida
  se decodifica y se comprueba.
* **Lo abierto es que el lector barato baste.** `goodPin_exists` demuestra el `∃`; el lector sin
  retroceso necesita el `∀`. `readBT` cubre la diferencia retrocediendo, y las sondas no encuentran
  un solo estado donde haga falta.

Dicho de otro modo: lo que queda no es si la máquina es correcta, sino **si se puede leer sin
retroceso**, y eso es exactamente la exactitud de la criba — que todo lo que deja viva tenga
camino. -/

/-- **El caso base, cerrado: un estado válido SIN ELECCIÓN tiene cadena.**

Cuando en cada paso los owners globales ya coinciden en un nodo de mapa, no queda nada que elegir, y
`Reader.inhabited_of_noChoice_readable` entrega la denotación — una selección enlazada y con
posesión por pares. `SupportedRun.chainSound_of_chain` la eleva a `ChainSound` con lo que el
contexto del lector ya trae, sin hipótesis nueva.

Dicho en claro: **cuando el lector termina, el estado tiene cadena demostrada.** Todo el hueco está
en el camino, no en el final — y eso es lo que hace que `AllValidPinsGood` sea un enunciado sobre la
*trayectoria* y no sobre los estados finales. -/
theorem hasChain_of_noChoice (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true)
    (hpms : Sons.PMS g) (hsn : Sons.SN g) (hsmp : Sons.SMP g) (hpos : 0 < g.current_step)
    (hc : PickInduction.NoChoice g) : HasChain g := by
  obtain ⟨_, sel, hchain, howned, _⟩ :=
    Reader.inhabited_of_noChoice_readable g (readable_of_readableAgg g hR) hv hc
  exact ⟨sel, SupportedRun.chainSound_of_chain g
    (AdjacentOwners.adj_of_readable g hR hv hpms hsn) hsmp hpos sel hchain howned⟩

/-! **Y entonces `AllValidPinsGood` solo pide algo de los estados intermedios.**

En los dos extremos de una lectura la cadena está: en la semilla la pone la conservación
(`ConservationImproves.pureRunW_full_chain`), y al final la pone `hasChain_of_noChoice`. Lo que
falta es que no se pierda **por el camino** — y ni una sola de las sondas encuentra un estado donde
se pierda.

Es la misma forma que tenía la simetría de owners cuando se midió (v63): disponible en los dos
extremos de la lectura, y lo que cuesta es llevarla por el medio. -/

/-- **Que el lector barato acierte en un estado ES que ese estado tenga cadena.**

`readLoop_sound` entrega `Inhabited` de todo estado en el que el lector termina, y
`SupportedRun.chainSound_of_chain` lo eleva a `ChainSound`. Es la vuelta de `goodPin_exists`: allí
la cadena daba el pin, aquí el pin da la cadena. -/
theorem hasChain_of_readAgg (P : GPathM) (hR : ReadableAgg P) (hv : isValid P = true)
    (hpms : Sons.PMS P) (hsn : Sons.SN P) (hsmp : Sons.SMP P) (hpos : 0 < P.current_step)
    (h : (ReaderExec.readAgg P).isSome = true) : HasChain P := by
  unfold ReaderExec.readAgg at h
  rw [if_pos hv] at h
  obtain ⟨h', hh'⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨_, sel, hchain, howned, _⟩ := ReaderExec.readLoop_sound _ P h' hR hv hh'
  exact ⟨sel, SupportedRun.chainSound_of_chain P
    (AdjacentOwners.adj_of_readable P hR hv hpms hsn) hsmp hpos sel hchain howned⟩

/-- **Y el hueco entero, en una línea: que el lector barato coincida con el que retrocede.**

`ReaderBT.readerVerdictBT_iff` decide 3-SAT **sin ninguna hipótesis**, y
`ReaderBT.readerVerdictBT_of_readerVerdictW` ya da una de las dos direcciones — lo que el lector sin
retroceso acierta, el que retrocede también—.

Así que todo lo que queda abierto en esta línea de trabajo cabe aquí: **que el que retrocede no
acierte nunca donde el barato falla.** Y la sonda `row-degree bt` no encuentra un solo estado donde
eso ocurra, sobre todos los corpus.

Nótese lo que esto no es: no es un hueco en la **corrección**. Es un hueco en que la lectura
**barata** baste. -/
theorem readerVerdictW_iff_of_agrees
    (hagree : ∀ ψ : Cnf, ReaderBT.readerVerdictBT ψ = true → ReaderExec.readerVerdictW ψ = true)
    (φ : Cnf) (hwf : WF φ) : ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  ⟨fun h => (ReaderBT.readerVerdictBT_iff φ hwf).mp
      (ReaderBT.readerVerdictBT_of_readerVerdictW φ h),
   fun h => hagree φ ((ReaderBT.readerVerdictBT_iff φ hwf).mpr h)⟩

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.hasChain_of_readAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasChain_of_readAgg

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.readerVerdictW_iff_of_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_agrees

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.hasChain_of_noChoice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasChain_of_noChoice

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.goodPin_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms goodPin_exists

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.readerVerdictW_of_pinPair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_of_pinPair

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.tablesSound_pin_of_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_pin_of_pairs

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
