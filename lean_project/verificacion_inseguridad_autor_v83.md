# Verificación para el Autor v83: P3 medida de verdad — y me cerré demasiado pronto en v82

Ricardo, soy Claude (Opus 5). No me dejaste cerrar la vía del tejido y **hiciste bien**. Al ir a medir P3 *de verdad* —no la versión que había medido en v77— encontré dos cosas: que mi conclusión de v82 era demasiado amplia, y que hay media demostración de P3 que sí sale.

---

## 1. Lo que v82 concluía de más

En v82 medí que `PinNonEmpty g q` ⟺ `isValid (filterAll g [q.id])` y de ahí dije que la vía del tejido «no compra nada». Eso vale para **P4**, que habla de **un** pinchazo suelto sobre un owner. **No vale para P3**, que es otro objeto: el tejido dentro de `owners(r)` **y** compatible con los **tres** requisitos de la cláusula, con `r` un superviviente del filtro. La máquina no calcula eso por cada `r`. Mi frase general estaba mal, y la retiro.

## 2. P3, medida en su forma fuerte

v77 midió el tejido dentro de `owners(n)` **sin pines**. P3 pide algo más duro: una intersección **triple** —owner de `p`, owner de `r`, y compatible con los tres requisitos— en cada paso. Que es exactamente la forma en la que v70 encontró huecos de tríos.

Modo nuevo, `cnfmap --p3`. Cuatro semillas:

| | supervivientes `r` | **cubre todos los pasos** | pierde un paso | se vacía | pierde a `r` |
|---|---|---|---|---|---|
| | **39.450** | **39.450** | **0** | **0** | **0** |

**Ni un fallo.** Y esto es más interesante de lo que parece, porque v70 **sí** encontró huecos de tríos en las tablas (38 de 905.506, 7 genuinos). La explicación es que un hueco entre dos nodos concretos **no vacía un paso**: el tejido encamina por otros miembros. Es decir, **el tejido es más robusto que las tablas por pares**, y esa es precisamente tu intuición de que el objeto correcto es el tejido entero y no los pares.

## 3. La mitad de P3 que sí se demuestra

```lean
theorem pinnedCandidate_covers (reqOf) (g) (reqs) (hreach) (hv) (hreqs) (hfun)
    (r) (n) (hn : (filterAll g reqs).node? r = some n) (l) (hl0) (hl) :
    ∃ q ∈ n.owners, q.id.step = l ∧ Compat reqs q      -- [propext, Quot.sound]
```

**El candidato pinzado cubre todos los pasos**, y no necesita nada abierto:

- En un paso que un requisito nombra, el **único** nodo compatible es el requisito mismo — y `owns_required` dice que un superviviente del filtro lo posee. Es tu propio filtro haciendo el trabajo.
- En cualquier otro paso, `Compat` no restringe nada y la cláusula de owners de `isValidNode` pone un owner.

O sea: la primera mitad de P3 está pagada.

## 4. Lo que no está pagado, dicho exactamente

Lo que falta es el **estrechado**: el mayor subconjunto auto-sostenido de un candidato que cubre **no tiene por qué cubrir**. Eso es el residuo de v45 —`support` a distancia ≥ 2— alcanzado ahora desde una tercera dirección independiente.

Tres rutas distintas (v44–v45 por conjuntos cerrados, v61–v65 por el tejido, y ahora P3 por el pinchazo) desembocan en el mismo enunciado. Eso no es mala señal: significa que el residuo está bien localizado y que no es un artefacto de cómo lo formulo.

## 5. Dónde queda, sin cerrar nada

- **P3 no está demostrada**, pero ya no es opaca: **candidato cubre = teorema**; **el estrechado conserva la cobertura = el residuo de v45**, y medido hoy en 39.450 supervivientes sin un fallo.
- La vía del tejido **sigue abierta**, y tu argumento —nace completo, ninguna operación estructural lo rompe, contiene todos los owners— está demostrado en sus tres piezas (v78 semilla y `addNode`, v79 `join` y crecimiento, v80 el mayor tejido). Lo que lo puede vaciar no es una operación: es una **restricción**.
- Y el dato nuevo que favorece tu intuición: **el tejido sobrevive donde las tablas por pares tienen huecos** (v70 vs. hoy). Eso dice que el objeto que elegiste —el conjunto, no el par— es estrictamente más fuerte.

Lo siguiente que yo intentaría: atacar el estrechado con lo que hoy quedó demostrado. El candidato cubre; la pregunta es si al borrar un nodo sin soporte se puede perder el *último* de un paso. Y esa pregunta, por primera vez, se puede hacer con el candidato ya caracterizado — el paso pinzado tiene **un solo** nodo compatible, el requisito, y ese es owner de `r` por teorema.

Build: `lake build AbsSat` verde, 100 módulos, 0 `sorry`, 0 axiomas de proyecto.
