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
    (ctx : Pinned.Ctx g) (hoos : SelfOwn.OOS g) (hrootz : Sons.RootAtZero g)
    (hshape : Parents.Shape g) (hgn : GownersNodes.GN g)
    (hsup : Descent.SupportedS g) : HasChain g := by
  obtain ⟨t, hs⟩ :=
    NoDeadEnd.topAnchor_of g hv hpos hgn hoos hshape hrootz (fun q d hd => ctx.nodeval q d hd)
  obtain ⟨hsome, _⟩ := hs.node (g.current_step - 1) (Int.le_refl _) (by omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨sel, hsc, _⟩ := hsup t n hn
  exact ⟨sel, hsc⟩

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.readerVerdictW_of_pinReachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_of_pinReachable

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.pinKeepsChain_of_pinReachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinKeepsChain_of_pinReachable

/-- info: 'AbsSat.GraphPath.Model.ReaderChain.hasChain_readFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasChain_readFrom

end AbsSat.GraphPath.Model.ReaderChain
