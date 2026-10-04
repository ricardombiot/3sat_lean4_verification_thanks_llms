# Verificación para el Autor v200: el modelo Lean de la máquina con grafo de owners, y el lector reducido a `NoDeadEnd`

Ricardo, este informe cuenta lo que se hizo en `lean/improves_bingo` desde el v199: un proyecto Lean nuevo que
modela la máquina de `julia/improves_bingo`, con los owners como un grafo por gpath en vez de una tabla por nodo.
Termina con el plan para lo que queda.

> **Corrección (28-sept).** La primera versión de este informe presentaba `NoZombie` (todo estado válido que visita el
> lector lleva una solución) como la única hipótesis abierta. Me lo señalaste: en `improves_bin` los zombis ya
> estaban superados. No afectan a la solidez (`denot_has_no_zombies`: un zombi es un problema de eficiencia, no de
> corrección), y el caso base está demostrado (`inhabited_of_noChoice_readable`). Lo único abierto allí es que el
> lector sin retroceso no se atasque, `NoDeadEnd`. En bingo, `NoZombie` junta dos cosas en una hipótesis más fuerte
> de lo necesario. Este informe ya está corregido: §4 y §5 separan lo que es trabajo pendiente (el caso base) de lo
> que es la pregunta abierta (`NoDeadEnd`, la misma que en bin).

**La conclusión, por adelantado.**
* **Hay un teorema de veredicto con una sola hipótesis.** `readerVerdict_iff_of_noZombie`: si ningún estado que el
  lector visita desde la línea final es un *zombi* (un estado válido que no lleva ninguna solución), entonces el
  lector dice SAT **exactamente** cuando la fórmula es satisfacible. Sin `sorry`. Esa hipótesis es más fuerte de lo
  necesario (§4): la forma buena es `readerVerdict_iff_of_noDeadEnd`, como en bin.
* **La completitud de la máquina está demostrada sin hipótesis** (`machineVerdict_of_sat`, solo con `Bounded`): si
  `φ` es satisfacible, la línea final lleva la camarilla de la solución.
* **El marco de reglas existe**: una regla nueva entra en el review demostrando tres cosas (solo borra, no pierde
  ninguna camarilla, todo vivo conserva su documento), y los teoremas anteriores la aprovechan sin tocarlos.
* **Lo abierto es `NoDeadEnd`, la misma pregunta que en `improves_bin`**: que el lector sin retroceso no se atasque.
  La solidez no depende de ella; solo falta demostrar en bingo el caso base que bin ya tiene (§5).
* **Pendiente práctico:** el modelo en listas es muy lento, así que el diferencial con Julia (L4) está aplazado.

---

## 1. El proyecto

`lean/improves_bingo` (namespace `AbsSatBingo`, 3.491 líneas, 0 `sorry`, `warningAsError`). La capa de base (CNF,
mapa bin, ids) viene de `lean/improves_bin` como dependencia de Lake, sin copiarla. Plan: `docs/plans/lean_bingo.md`.

| fase | commit | qué |
|---|---|---|
| L0, L1 | `7ca3dd2` | el proyecto y el modelo `GPathB`: nodos sin owners + `alive` + `edges` |
| L2, L3 | `eabe58a` | las operaciones de la máquina, espejo de Julia; el driver, el lector; ejecutables |
| L5 | `97ebd56` | el review solo borra (`Shrinks`) |
| L6 | `c00ab6f` | camarillas llevadas; el review las conserva; el marco `Rule`; el lector bajo `NoZombie` |
| L6b | `2375ef8` | la máquina lleva la camarilla de toda solución |
| L7 | `833a6c3` | invariantes estructurales, la decodificación y `readerVerdict_iff_of_noZombie` |

### Decisiones de diseño

* **La simetría, por definición.** Cada arista se guarda en una orientación cualquiera y la posesión `Adj` mira las
  dos, así que `adj_symm` no necesita demostración. No hace falta el espejo ni sus lemas.
* **El indicador `dirty`** (Julia `review_owners`) está en el modelo: el review solo corre con él activo, como en
  Julia. Sin él, el modelo revisaría más a menudo y los estados no coincidirían.
* **Especificación, no implementación**: listas planas y validez derivada, como `GPathM`. El precio es la
  velocidad (§4).

## 2. La idea central: la camarilla llevada

`Carried g S` dice que la selección `S` (un nodo de camino por paso) está viva en `g`: sus nodos viven, se poseen
dos a dos y los consecutivos están enlazados. Es la forma, puramente combinatoria, en que un estado lleva una
solución: no menciona la fórmula.

Todo lo demás se apoya en ella:

| teorema | qué dice |
|---|---|
| `isValidNode_of_carried` | todo nodo de una camarilla llevada es válido |
| `carried_review` | **ninguna regla del review pierde una camarilla llevada** |
| `carried_filterAll` | tampoco el filtro por requisitos que concuerdan con ella |
| `carried_up`, `carried_join_*` | el UP la alarga un paso; el join la conserva por cualquiera de los dos lados |
| `run_carries` | si `a` satisface `φ`, la línea final lleva la camarilla de `a` |
| `sat_of_carried` | una camarilla llevada en el último paso **es** una solución |

Las razones, regla a regla, son cortas:
* la purga no toca un nodo válido;
* en la regla de parejas, el nodo de la camarilla de cada paso es un vecino común;
* en las pasadas, el padre o el hijo de la camarilla da el apoyo;
* los enlaces de la camarilla unen nodos que se poseen.

## 3. Los teoremas del veredicto

**Completitud de la máquina** (`machineVerdict_of_sat`). Es una inducción sobre las líneas. En cada paso:
* el filtro conserva la camarilla, porque los requisitos de la rama concuerdan con ella (`reqSat_selOfAssign`);
* el UP la alarga, porque la ventana de la rama no está prohibida (`pidOfAssign_not_prohibited`, el único sitio
  donde entra `Sat`);
* los joins de la línea no la pierden.

**El lector termina bajo `NoZombie`** (`readG_isSome_of_noZombie`). Si el estado visitado lleva una camarilla, el pin
de su nodo en el primer paso con elección la conserva, así que el lector nunca se queda sin pin. Para el combustible
hizo falta un invariante más: todo nodo vivo tiene documento (`AliveDocs`). Con él, cada pin mata a alguien y la
medida baja estrictamente.

**Decodificación** (`sat_of_carried`). Es el argumento de `CnfChain` de `improves_bin`, con aristas en lugar de
tablas. Se apoya en cinco invariantes estructurales que todo estado de la máquina y del lector cumple
(`Struct.lean`):
* el id de un nodo declara a su padre y a su abuelo;
* ningún nodo es una ventana prohibida;
* todo nodo está sobre el mapa;
* **`ReqEdges`, los requisitos como invariante de aristas**: si `x` posee a otro nodo `w` que está en el paso de un
  requisito de `x`, entonces `w` es el nodo requerido. Se cumple porque las aristas nacen en el UP justo después del
  filtro por requisitos, y el review solo borra.

**El veredicto** (`readerVerdict_iff_of_noZombie`):
* satisfacible ⇒ el lector dice SAT, por `run_carries` y el lector bajo `NoZombie`;
* el lector dice SAT ⇒ satisfacible: el estado donde termina es válido, por `NoZombie` lleva una camarilla, y la
  camarilla se decodifica en una solución.

## 4. Lo que falta y lo que no funciona todavía

* **Velocidad.** `bingo-check` acierta en las 8 fórmulas de `cnf/crafted` (máquina y lector iguales a la fuerza
  bruta, sin nodos muertos), pero tarda 0,7 s con 3 variables y 6 min con 9. Cada consulta de posesión recorre la
  lista entera de aristas. El diferencial con Julia (L4) necesita versiones rápidas con `@[csimp]`.
* **Invariantes de forma (L5).** Faltan el lema de que el orden dentro de una línea no importa y la suficiencia del
  combustible del review. La segunda hace falta para el caso base de §5.
* **`Classical.choice`** aparece en los axiomas de los teoremas del lector; viene de tácticas. `sat_of_carried` no lo
  usa. Se puede limpiar.
* **`NoZombie` es más fuerte de lo necesario.** Mezcla dos cosas que `improves_bin` ya había separado:
  * **la solidez** («el lector dice SAT ⇒ satisfacible»). En bin no tiene hipótesis: los zombis no la afectan
    (`denot_has_no_zombies`), porque lo que el lector lee al terminar es siempre una cadena real, y el caso base está
    demostrado (`inhabited_of_noChoice_readable`: sin nada que elegir, el estado contiene un camino). En bingo solo
    hay que demostrar ese caso base: es **trabajo pendiente, no una hipótesis abierta**;
  * **la completitud** («satisfacible ⇒ el lector dice SAT»). La demostración de `readG_isSome_of_noZombie` usa
    `NoZombie` para una sola cosa: obtener un pin que deje válido el estado. Eso es exactamente **`NoDeadEnd`**: en
    todo estado válido que visita el lector, algún pin del primer paso con elección lo deja válido. `NoZombie`
    implica `NoDeadEnd`, pero no al revés.

## 5. El plan

### 5.1 Reenunciar con `NoDeadEnd`

Cambiar la hipótesis del teorema del lector de `NoZombie` a `NoDeadEnd`, que es lo que la demostración usa de verdad.
Es un cambio pequeño.

### 5.2 La solidez sin hipótesis: el caso base

El estado final del lector no tiene elección: un único nodo de mapa por paso. Hay que demostrar que **un estado
válido y limpio sin elección lleva una camarilla**, el análogo de `inhabited_of_noChoice_readable` de bin. Con eso
y `sat_of_carried`, la dirección «el lector dice SAT ⇒ satisfacible» queda sin hipótesis, como `readerVerdictW_sound`.

Requisito previo: que el review termine en un estado limpio (todos los nodos válidos), es decir, que el combustible
basta. Cada vuelta que sigue borró algo, así que la medida baja.

Resultado de 5.1 y 5.2: **`readerVerdict_iff_of_noDeadEnd`**, con la misma forma que `readerVerdictW_iff_of_noDeadEnd`
de bin. La pregunta abierta pasa a ser literalmente la misma en los dos proyectos.

### 5.3 La pregunta abierta: `NoDeadEnd`

En cada elección, algún pin tiene que dejar el estado válido. **Es el punto difícil de bin** (`NoDeadEnd` /
`KernelSplit`, reformulado como `TriPin₁`, `CliqueTri`, `PieceLocal` y ahora la ruta M1). Hay dos vías, que se pueden
llevar a la vez:

* **Traerlo de bin (puente completo, L8).** La otra sesión avanza por la ruta M1 («el lector decide bajo `M1aAll` y
  `CoverRow`», `03dfe07` y siguientes). Un puente que traduzca los estados de bingo a tablas y demuestre que las
  operaciones conmutan con esa traducción traería a bingo lo que se consiga allí, sin rehacerlo. La F4 de Julia
  (mismos estados finales y mismas vueltas en 81 de 81) dice que el enunciado es plausible.
* **Atacarlo en bingo con reglas sobre aristas.** Enunciado como invariante: todo nodo vivo en un paso con elección
  está en una camarilla prefijo (pasos `0 … k`) que se puede extender, la forma bingo de `PrefixTri` / `CliqueTri`.
  Las reglas actuales son locales (pares, apoyos): conservan camarillas, pero no garantizan que todo vivo esté en
  alguna. El salto de «consistente por pares» a «existe una camarilla completa» es el hueco tipo Helly, y el enfoque
  de subconjuntos lo rodea pidiendo que exista un camino dentro del subconjunto relevante. La regla 6.4 del v199
  (camino común) es exactamente una prueba de vacío sobre el subconjunto de caminos compatibles con un par, así que
  es la candidata natural. Entra como una `Rule` más, con su lema de conservación; los teoremas de §3 no se tocan.

### 5.4 Orden propuesto

| # | qué | tipo | depende de |
|---|---|---|---|
| 1 | reenunciar el teorema del lector con `NoDeadEnd` | demostración (pequeña) | — |
| 2 | el review termina en un estado limpio (el combustible basta) | demostración | — |
| 3 | caso base (sin elección + limpio ⇒ camarilla) y **`readerVerdict_iff_of_noDeadEnd`** | demostración | 1, 2 |
| 4 | el puente completo con `improves_bin` (L8), para traer lo que se consiga en `NoDeadEnd` allí | demostración | 3 |
| 5 | medir en Julia bingo el invariante de camarillas prefijo en los estados que visita el lector | sonda (pide tu permiso: busca contraejemplos) | — |
| 6 | la regla 6.4 (camino común) en Julia y en Lean, con su lema de conservación | regla + demostración | 5 |
| 7 | versiones `@[csimp]` y el diferencial Lean ↔ Julia (L4) | ingeniería | — |

Los puntos 1 a 3 dejan bingo a la altura de bin, con la misma pregunta abierta.

---

**Commits:** `7ca3dd2`, `eabe58a`, `97ebd56`, `c00ab6f`, `2375ef8` y `833a6c3`, en la rama `graph_owners`. Código:
`lean/improves_bingo` (README con la tabla de módulos y el estado de los teoremas). Plan: `docs/plans/lean_bingo.md`.
