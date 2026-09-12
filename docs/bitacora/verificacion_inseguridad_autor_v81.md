# Verificación para el Autor v81: P4 cerrada — y el desajuste no existía

Ricardo, soy Claude (Opus 5). P4 está demostrada, y resulta que el «desajuste real» que declaré en v77 y repetí en v78, v79 y v80 **no hacía falta resolverlo**: había que rodearlo por el lado bueno.

---

## 1. El desajuste que no era

Yo decía: `PickSome` pide `isValid (filterAll g [q.id])` —el pinchazo y el review **originales**— mientras que el teorema de v65 responde sobre `readStepSym = reviewSym ∘ pinOwners`. Dos operaciones distintas, y reconciliarlas parecía trabajo.

No hace falta. v65 dejó demostrados, **para la máquina original**, justo los dos hechos que importan:

- `FOk_filterAll` — un tejido que concuerda con los pines sobrevive al filtro entero, review incluido;
- `isValid_of_Fabric` — **un tejido no vacío hace válido el grafo**, porque su cláusula `support` alcanza todos los pasos, que es exactamente lo que `isValid` cuenta.

Con `Fabric_core` (v80) en medio, el puente son tres líneas:

```lean
theorem isValid_filterAll_of_PinNonEmpty (g) (q) (hsmp) (hnr) (h : PinNonEmpty g q) :
    isValid (filterAll g [q.id]) = true

theorem PickSome_of_PinNonEmpty (g) (hsmp) (hnr) (h : …) : PickInduction.PickSome g
```

donde `PinNonEmpty g q` es simplemente: *el mayor tejido que concuerda con pinchar `q` no está vacío*.

**Y esto importa más que por ahorrarme trabajo:** la ruta ya no tiene que comprometerse con la variante simétrica. Todo lo que viene después habla de tu máquina tal y como está escrita.

## 2. La ruta, ensamblada

```lean
theorem Inhabited_of_PinNonEmpty (reqOf) (g) (reqs)
    (hreach : Reachable reqOf g) (hv : isValid (filterAll g reqs) = true)
    (hinv  : ∀ h', Reader.Readable h' → isValid h' = true → Sons.SMP h' ∧ Parents.NotRoot h')
    (hpins : ∀ h', Reader.Readable h' → isValid h' = true →
       hasChoice h' → ∃ k …, ∃ q ∈ ownersAt h'.gowners k, PinNonEmpty h' q) :
    Inhabited (filterAll g reqs)
```

Y `Inhabited` es lo que consume el veredicto (`L7.satisfiable_of_inhabited`, verificado en v77). Así que de la construcción al veredicto ya no queda nada que no sea teorema, **salvo una cosa**.

## 3. Lo que queda: una sola forma de enunciado

| pieza | estado |
|---|---|
| **P1** el tejido nace (semilla, `addNode`) | ✅ v78 |
| **P2** lo preservan las operaciones y el `join` | ✅ v65 + v79 |
| **P3** el estrechado a los pines sigue llegando | reducida a **`PinReaches`** (v80) |
| **P4** el puente a `PickSome` | ✅ **hoy** |
| **P5** cierre con `L7` | libre |

Y lo que más me llama la atención al mirarlo entero: **`PinReaches` y `PinNonEmpty` son el mismo enunciado**. Los dos dicen *el mayor tejido compatible con estos pines no está vacío* — uno pidiendo que alcance un nodo concreto, el otro que alcance alguno. Después de cuarenta informes, toda la mitad abierta de tu afirmación de diseño se ha condensado en **una sola forma de frase**, escrita sobre tus `owners` y sobre tu filtro.

## 4. El límite, por última vez en este informe

Esa frase, para toda fórmula, es 3SAT en P. Así que no se va a demostrar entera, y no hay que intentarlo de frente. Lo que sí se puede —y es el trabajo que queda— es **demostrarla bajo la hipótesis de clase** de v76, que ahora se puede enunciar donde debe: sobre el tejido y los owners, no sobre un modelo paralelo.

Dicho de otro modo: el andamiaje está terminado. Lo que falta es exactamente una cosa, se sabe cuál, se sabe dónde entra la hipótesis, y está medida en 124.246 nodos sin un fallo.

Build: `lake build AbsSat` verde, 100 módulos, 0 `sorry`, 0 axiomas de proyecto; los catorce teoremas de `FabricAdd.lean` cierran en `[propext, Quot.sound]` salvo `Fabric_core`, que no usa ninguno.
