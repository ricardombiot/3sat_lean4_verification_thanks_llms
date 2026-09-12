# Verificación para el Autor v46: el residuo, acorralado por tres lados

Ricardo, soy Claude (Opus 5). Ataqué `support` a distancia ≥ 2. **No lo he demostrado**, y esta vez traigo algo distinto de un avance: traigo **dos refutaciones y una caracterización**, que juntas dicen exactamente qué forma tiene que tener la demostración que falta.

---

## 1. La versión fuerte es falsa

Lo primero que probé fue el atajo obvio. Si **todo** owner de un candidato fuera candidato, `support` sería gratis: `owners_ok` ya reparte un owner en cada paso, y valdría cualquiera.

**Es falso.** `lake exe extend --downclosed`:

| campaña | pares (candidato, owner) | owner NO candidato |
|---|---|---|
| 8 casos, semilla 2026, 3..6 vars | 3.723.185 | **722.851** (19 %) |
| 6 casos, semilla 90210, 3..6 vars | 6.271.084 | **1.418.285** (23 %) |

Registrado como `Survive.PinSetDownClosed`, refutado. **Y eso dice algo:** el ∃ de `support` no es pereza de enunciado, es esencial. Un candidato tiene *algún* owner candidato en cada paso lejano, pero uno de cada cinco de sus owners no lo es.

## 2. El testigo obvio tampoco vale

El segundo intento era construir el testigo en vez de encontrarlo: descender desde el candidato eligiendo en cada paso un padre que siga poseyendo el nodo pinzado. `hop_down` garantiza que ese padre existe y que todo el descenso son candidatos. Lo único que falta es que el descenso se quede **dentro de los owners del nodo de partida** — el puente de v39 regala el primer salto, y v40 ya había refutado el segundo.

**Falla.** `lake exe extend --descentin`:

| campaña | descensos | se salen del soporte | saltos | saltos fuera |
|---|---|---|---|---|
| 8 casos, semilla 2026 | 125.528 | **6.371** (5,1 %) | 1.315.726 | **28.665** |
| 6 casos, semilla 90210 | 208.331 | **17.499** (8,4 %) | 1.980.130 | **73.602** |

Registrado como `Survive.AnchoredDescentStaysInSupport`, refutado.

Así que `support` es cierto (0 fallos en 3,47 M) pero **no por la construcción natural**. Qué padre elige el descenso importa.

## 3. Y lo que sí es teorema: dónde vive el soporte

```lean
theorem owner_below_on_descent (g) (ctx) (hoos : SelfOwn.OOS g) (p) (n) (hn) … (v)
    (hv : v ∈ n.owners) (hvle : v.id.step ≤ p.id.step) :
    ∃ sel, TPart g v sel 0 p.id.step ∧ sel p.id.step = p ∧ sel v.id.step = v
```

> Todo owner **por debajo** de un nodo está en un descenso desde él: una cadena enlazada por padres cuya cima **es** `p`, cuyos nodos poseen todos a `v`, y cuyo nodo en el paso de `v` **es `v` mismo**.

Lo último lo fuerza `OOS`: en su propio paso un nodo no tiene otro owner que él. Cierre `[propext, Quot.sound]`.

Junto con el puente, esto **encierra la tabla de owners entre dos relaciones**:

```
      parents(p)  ⊆  owners(p) en el paso de abajo      (el puente, v39)
      owners(p) en l  ⊆  ancestros de p en l            (aquí)
```

y la transitividad refutada de v40 dice que **ninguna de las dos es igualdad**: un abuelo no tiene por qué ser owner. El soporte de un nodo por debajo de él es un conjunto de ancestros, ni todos ni solo los padres.

## 4. El residuo, acorralado

| enunciado | forma | medido |
|---|---|---|
| un candidato tiene un owner candidato en cada paso | ∃ | **0** de 3.473.942 |
| *todo* owner de un candidato es candidato | ∀ | **722.851** de 3.723.185 |
| el descenso anclado se queda en el soporte | construcción | **6.371** de 125.528 |

El residuo es **cierto, estrictamente existencial, y no lo produce la construcción obvia**. `owner_below_on_descent` dice cómo es el espacio de búsqueda: los owners por debajo son ancestros alcanzados por cadenas que arrastran al owner. Lo que falta, entonces, no es un lema más sino **una regla de elección**: entre los descensos desde un candidato que arrastran el pinchazo, uno que además se quede dentro del soporte del propio candidato.

Eso es un enunciado mucho más concreto que «no hay zombis», y es el primero de esta serie que tiene forma de **algoritmo** en vez de forma de propiedad. No sé si eso ayuda, pero es información nueva sobre la diana.

## 5. Estado

| | |
|---|---|
| `owner_below_on_descent` | **demostrado** |
| `PinSetDownClosed` | **refutado** (722 k / 3,7 M y 1,4 M / 6,3 M) |
| `AnchoredDescentStaysInSupport` | **refutado** (6.371 / 125 k y 17.499 / 208 k) |
| `support` a distancia ≥ 2 | abierto — 0 fallos en 3,47 M |
| `son` (espejo hijos→padres) | hueco estructural — 0 fallos en 237 k |
| `CoreCovers`, `PickValid`, `PairwiseOwned` | abiertos, y son el mismo enunciado |

---

*Claude (Opus 5), 2026-09-10. `lake build AbsSat` verde, 74 módulos, 0 `sorry`, cierres `[propext, Quot.sound]` o más finos.*
