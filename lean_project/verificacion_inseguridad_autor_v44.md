# Verificación para el Autor v44: `support` no se demuestra — se quita de la cuenta

Ricardo, soy Claude (Opus 5). Ataqué `support`, el residuo de v43. **No lo he demostrado.** Lo que sí he hecho es quitarlo de la cuenta, y eso deja la obligación en **un solo enunciado**.

---

## 1. La idea

Las seis cláusulas de `Closed` son todas de la forma *«un miembro tiene un miembro entre sus …»*. Esa forma es **cerrada bajo unión**: si juntas todos los conjuntos auto-sostenidos, el resultado sigue siendo auto-sostenido. Y ese conjunto —el mayor de todos— cumple las seis **por construcción**.

```lean
def Core (g : GPathM) : PathNodeId → Prop := fun p => ∃ S, Closed g S ∧ S p

theorem Core_greatest (g) (S) (h : Closed g S) : ∀ p, S p → Core g p

theorem Closed_Core (g) (hsmp : Sons.SMP g) (hlink : Bridge.LinksInOwners g) :
    Closed g (Core g)
```

La unión funciona porque `coown` **no depende de `S`** — es `coown_of_bridge` de v43, que vale para cualquier conjunto. Si `coown` hubiera sido una propiedad del conjunto, la unión no habría cerrado.

Y entonces:

```lean
def CoreCovers (g : GPathM) : Prop :=
  ∀ l, 0 ≤ l → l < g.current_step → ∃ p, Core g p ∧ p.id.step = l

theorem isValid_cleanInvalid_of_CoreCovers (g) (hsmp) (hlink) (h : CoreCovers g) :
    isValid (cleanInvalid g) = true
```

Cierres `[propext, Quot.sound]`. `AbsSat/GraphPath/Model/Survive.lean`.

> **Todo lo que `cleanInvalid` debe tras un pinchazo es: el núcleo llega a todos los pasos.**

Un enunciado. Sin cadenas, sin `isValidNode`, sin el bucle de fuel de la review.

## 2. Qué se ha ganado y qué no

Lo que **no**: `CoreCovers` es `PickValid`. No lo he demostrado y no tengo una ruta. El núcleo arco-consistente es lo que la propagación de la máquina calcula, así que decir «el núcleo no se vacía» y decir «la poda no invalida» es decir lo mismo dos veces.

Lo que **sí**: la cuenta pasa de *seis cláusulas sobre un conjunto que alguien tiene que exhibir* a *una propiedad de un objeto canónico que ya existe*. Eso importa porque quita del camino todas las preguntas de forma —¿camino?, ¿conjunto?, ¿qué testigo?— que llevaban cuatro documentos apareciendo y desapareciendo.

## 3. Medido, y esta vez sin circularidad

Calculé el núcleo **directamente**: estrechando los owners globales bajo las cláusulas de `Closed` hasta que deja de encoger. No llama a `isValidNode` en ningún momento, así que un resultado limpio no es la propia poda dándose la razón.

`lake exe extend --core`, dos semillas:

| campaña | pinchazos | núcleo se salta algún paso | pares (pinchazo, paso) vacíos | tamaño total del núcleo |
|---|---|---|---|---|
| 10 casos, semilla 2026, 3..6 vars | 7.664 | **0** | **0** | 172.101 |
| 12 casos, semilla 90210, 3..7 vars | 17.213 | **0** | **0** | 508.608 |

**24.877 pinchazos, cero pasos vacíos.** Y el núcleo no es escuálido: unas 25–30 entradas por pinchazo, así que la propiedad no se cumple por los pelos.

## 4. El muro, ahora visible desde tres lados

Merece la pena decirlo junto, porque es el mapa que faltaba.

Las **pasadas de coherencia** no las cubre este teorema, y sé lo que costarían. `reviewNode` intersecta con la unión de los owners de los **vecinos**, no con los globales. Para que un miembro conserve soporte en el paso `l` a través de eso, el testigo tiene que ser poseído también por un vecino suyo. Es decir, `Closed` necesitaría una cláusula estrictamente más fuerte:

> **`share`** — un miembro y su padre-miembro poseen un miembro común en cada paso.

Y `share` no se queda quieta: preservarla un nivel más abajo pide que el padre del padre posea el mismo testigo, y así por toda la cadena de miembros. Lo que eso suma es una selección `u₀ … u_{S-1}`, una por paso, poseída por **todos** los miembros — y como cada `uₗ` es él mismo miembro, los `u` se poseen entre sí. **Eso es `PairwiseOwned` para la selección.**

Los tres lados, entonces:

| desde | enunciado | documento |
|---|---|---|
| la cadena | `PairwiseOwned` | v28–v42 |
| el camino testigo | `support` | v43 |
| las pasadas de coherencia | `share` | este |

Son el mismo muro. La formulación por núcleo es la única que lo esquiva, y solo para `cleanInvalid` — que es, por la medición de v41, donde está todo el riesgo.

## 5. Estado

| | |
|---|---|
| El núcleo es auto-sostenido | **demostrado** |
| `isValid` tras `cleanInvalid` si el núcleo cubre | **demostrado** |
| `CoreCovers` | **abierto** — 0 fallos en 24.877 pinchazos, dos semillas, cálculo no circular |
| Pasadas de coherencia | fuera; requerirían `share`, que colapsa a `PairwiseOwned` |
| `PickValid`, `PairwiseOwned` | abiertos, y son este mismo enunciado |

---

*Claude (Opus 5), 2026-09-10. `lake build AbsSat` verde, 74 módulos, 0 `sorry`, cierres `[propext, Quot.sound]` o más finos.*
