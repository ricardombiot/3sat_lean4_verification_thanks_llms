# Verificación para el Autor v77: el tejido en los pasos de cláusula — y una ruta que no pasa por `PairwiseOwned`

Ricardo, soy Claude (Opus 5). Medido el tejido donde te dije que había que medirlo: no en la lectura, como hizo v65, sino en los **pasos de cláusula**, que es donde el filtro estrecha las tablas y donde la ruta podía romperse.

No se rompe. Y al preparar la medición encontré algo que creo que importa más que el número: **hay un camino al veredicto que no pasa por `PairwiseOwned`.**

---

## 1. Lo medido

Modo nuevo, `lake exe cnfmap --fabclause`. En cada estado válido de cada paso de cláusula, para **cada nodo** `n`, calculo el mayor tejido dentro de `owners(n)` y miro tres cosas: si conserva todos sus miembros, si **cubre todos los pasos**, y si contiene al propio `n`.

| máquina simétrica | estados | nodos | miembros conservados | **cubre todos los pasos** | pierde un paso | se pierde a sí mismo |
|---|---|---|---|---|---|---|
| fórmulas aleatorias (4 semillas, 3–5 y 4–6 vars) | 3.730 | **84.538** | 84.538 | **84.538** | **0** | **0** |
| control Tseitin (K4, K3,3, prisma, ambas paridades) | 638 | **39.708** | 39.708 | **39.708** | **0** | **0** |

**124.246 nodos, ni una sola excepción**, y con la máquina original los números son idénticos a los de la simétrica.

Lo que sí varía son las **entradas** de las tablas:

| | entradas conservadas / totales | recorte |
|---|---|---|
| aleatorias 3–5 vars | 27.496.985 / 27.496.985 | **0 %** |
| aleatorias 4–6 vars | 13.665.383 / 13.665.797 | 0,003 % |
| K4 (ambas paridades) | 3.345.018 / 3.345.018 | 0 % |
| K3,3 y prisma | 70.742.288 / 71.800.224 | 0,9–2,0 % |

Tres lecturas:

- **El recorte es de entradas, nunca de miembros.** Eso está *dentro* de la definición de `Fabric` de v65, no en contra: un tejido conserva una **subtabla** de los owners de cada miembro, no la tabla entera.
- **Lo que `Closed`/`CoreCovers` necesita —miembros y cobertura— no se toca nunca.** Ni en las familias adversarias.
- **Dónde aparece el recorte es informativo:** 0 % en aleatorias pequeñas y en K4; 0,9–2,0 % en K3,3 y prisma. Es un fenómeno de **ciclicidad**, el mismo eje que v17, v70 y v75 vienen señalando desde hace tiempo.

## 2. La ruta que encontré preparando esto

Yo te había dicho que el objetivo era `PairwiseOwned`. Revisando el código para montar la medición vi que hay un camino más corto, y que **el veredicto no necesita `PairwiseOwned` ni `ClauseStepExact`**. Lo comprobé en las firmas, no de memoria:

```lean
L7.satisfiable_of_inhabited (φ) (hwf) (g) (hmr) (hcs)
    (hinh : Inhabited g) : Satisfiable φ
```

**El veredicto solo consume `Inhabited` del estado final.** Y `Inhabited` ya está reducido:

- `Reader.Inhabited_of_pickSome_machine` (v58): de `PickSome` en todo estado legible y válido sale `Inhabited (filterAll g reqs)`.
- `PickSome g` (v41) es literalmente: *si queda elección, hay un paso y un owner `q` tal que `filterAll g [q.id]` sigue válido*. Es tu `throw("GRAVE ERROR READER")`.
- `Fabric.isValid_readStepSym_of_FabricAt` (v65): **si `owners(r)` contiene un tejido que pasa por `r`, elegir `r` no atasca al lector.**

Y eso último es exactamente lo que acabo de medir en los pasos de cláusula, con 124.246 nodos y cero fallos.

## 3. Cómo haría la demostración

Cinco piezas, y digo el estado real de cada una:

**P1 — el tejido nace completo.** En `addNode` el nodo nuevo recibe todos los owners globales y todo nodo existente recibe al nuevo (tu `all_previous_nodes_are_owners_of_me!`). v62 ya demostró que `addNode` **crea la propiedad simétricamente**, y v38/v39 que los enlaces quedan dentro de los owners. Ahí el tejido es trivial: simétrico, cubriendo (los owners globales cubren todo paso por `isValid`) y respaldado por padres e hijos. *Esperable barato.*

**P2 — lo preserva el review.** **Hecho**: v65 demostró que el tejido sobrevive a las cuatro operaciones y al review entero.

**P3 — lo preserva el filtro de cláusula.** **Es la pieza nueva**, y la medición de hoy es su evidencia. Es el único paso que añade restricciones de verdad.

**P4 — el puente `FabricAt ⟹ PickSome`.** Aquí hay un desajuste real que no pienso disimular: `PickSome` habla de `filterAll g [q.id]` —el pinchazo y el review **originales**— mientras que el teorema de v65 habla de `readStepSym g r = reviewSym (pinOwners g r)`, que es el pinchazo **por owners** y el review **simétrico**. Son operaciones distintas. Hay que demostrar el análogo simétrico de `Inhabited_of_pickSome_machine`, o bien una versión de `Fabric` para `filterAll g [q.id]`. Es trabajo acotado y concreto, pero es trabajo.

**P5 — cerrar.** Con P1–P4, `Inhabited` del estado final, y `L7.satisfiable_of_inhabited` da el veredicto. La otra dirección ya está demostrada desde v53.

Lo que me gusta de esta ruta: **esquiva todos los callejones documentados**. No construye caminos (v43 la haría circular), no usa transitividad (refutada en v40), no usa el clique del soporte (refutado en v28), y no supone la simetría (es teorema desde v64 para la máquina simétrica). Y va entera sobre tus estructuras: `owners`, `review`, el lector.

## 4. El límite, dicho antes de que me lo recuerdes

Si las cinco piezas cerraran **para toda fórmula**, 3SAT estaría en P. Así que al menos una tiene que fallar en el caso general, y los candidatos son P3 —el único paso que añade restricciones— y P4.

Mi medición de hoy **no puede distinguirlo**: con 3–6 variables todo tiene anchura pequeña, así que el tejido sobrevive por razones que no se ven a esa escala. Lo honesto es esperar que **P3 necesite la hipótesis de clase**, y ahí vuelve la anchura acotada de v76 — pero esta vez enunciada sobre tus estructuras y no sobre un modelo paralelo, que era la deuda que dejó v74.

**Siguiente paso concreto que propongo:** P1, que es barata y da el caso base; y en paralelo empujar la medición de P3 a fórmulas más grandes buscando el primer nodo cuyo tejido pierda un paso. Si aparece, nos dice exactamente dónde está la frontera de la clase. Si no aparece hasta tamaños grandes, la frontera está más lejos de lo que pensábamos.

Build: `lake build AbsSat` verde, 99 módulos, 0 `sorry`, 0 axiomas de proyecto.
