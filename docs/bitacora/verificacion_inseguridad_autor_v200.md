# Verificación para el Autor v200: el modelo Lean de la máquina con grafo de owners, y el lector reducido a `NoZombie`

Ricardo, este informe cuenta lo que se hizo en `lean/improves_bingo` desde el v199: un proyecto Lean nuevo que
modela la máquina de `julia/improves_bingo`, con los owners como un grafo por gpath en vez de una tabla por nodo.
Termina con el plan para atacar la única hipótesis que queda.

**La conclusión, por adelantado.**
* **Hay un teorema de veredicto con una sola hipótesis.** `readerVerdict_iff_of_noZombie`: si ningún estado que el
  lector visita desde la línea final es un *zombi* (un estado válido que no lleva ninguna solución), entonces el
  lector dice SAT **exactamente** cuando la fórmula es satisfacible. Sin `sorry`.
* **La completitud de la máquina está demostrada sin hipótesis** (`machineVerdict_of_sat`, solo con `Bounded`): si
  `φ` es satisfacible, la línea final lleva la camarilla de la solución.
* **El marco de reglas existe**: una regla nueva entra en el review demostrando tres cosas (solo borra, no pierde
  ninguna camarilla, todo vivo conserva su documento), y los teoremas anteriores la aprovechan sin tocarlos.
* **Lo abierto se reduce a `NoZombie`.** Propongo partirla en un caso base demostrable y un paso, que es el mismo
  punto difícil que en `improves_bin` (§5).
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
* **Una diferencia con `improves_bin`:** allí la solidez del lector no necesita hipótesis. Aquí, la dirección
  «el lector dice SAT ⇒ satisfacible» también pasa por `NoZombie`. §5 lo resuelve con el caso base.

## 5. El plan: cómo atacar `NoZombie`

El lector usa `NoZombie` en dos sitios de dificultad muy distinta. La propuesta es separarlos.

### 5.1 Caso base: al terminar

El estado final del lector no tiene elección: un único nodo de mapa por paso. Solo hace falta que **un estado
válido y limpio sin elección lleve una camarilla**. Es el análogo de `inhabited_of_noChoice_readable`, que
`improves_bin` ya tiene demostrado.

Requisito previo: demostrar que el review termina en un estado limpio (todos los nodos válidos), es decir, que el
combustible basta. Cada vuelta que sigue borró algo, así que la medida baja.

Resultado: la solidez del lector sin hipótesis, como en bin.

### 5.2 Paso: en cada elección

En un estado válido que visita el lector, algún pin del primer paso con elección tiene que dejarlo válido. **Es el
mismo punto difícil que en bin** (`NoDeadEnd` / `KernelSplit`, reformulado como `TriPin₁`, `CliqueTri`,
`PieceLocal` y ahora la ruta M1). El grafo no lo hace fácil, pero da un sitio limpio donde enunciarlo y atacarlo:

* **Enunciado como invariante:** todo nodo vivo en un paso con elección está en una camarilla prefijo (pasos
  `0 … k`) que se puede extender. Es la forma bingo de `PrefixTri` / `CliqueTri`.
* **Por qué hacen falta reglas.** Las reglas actuales son locales (pares, apoyos) y conservan camarillas, pero no
  garantizan que todo vivo esté en alguna. El salto de «consistente por pares» a «existe una camarilla completa» es
  el hueco tipo Helly. El enfoque de subconjuntos lo rodea: pedir que exista un camino dentro del subconjunto
  relevante. La regla 6.4 del v199 (camino común) es exactamente una prueba de vacío sobre el subconjunto de caminos
  compatibles con un par, así que es la candidata natural.
* **Cómo entra una regla:** una `Rule` más (solo borra, conserva camarillas, conserva documentos), y su lema de que
  conserva el invariante del paso. Los teoremas de §3 no se tocan.

### 5.3 En paralelo: el puente completo (L8)

La otra sesión avanza en `improves_bin` por la ruta M1 («el lector decide bajo `M1aAll` y `CoverRow`», `03dfe07`
y siguientes). Un puente que traduzca los estados de bingo a tablas y demuestre que las operaciones conmutan con esa
traducción traería esos resultados a bingo sin rehacerlos. Es la fase más cara. La F4 de Julia (mismos estados
finales y mismas vueltas en 81 de 81) dice que el enunciado es plausible.

### 5.4 Orden propuesto

| # | qué | tipo | depende de |
|---|---|---|---|
| 1 | el review termina en un estado limpio (el combustible basta) | demostración | — |
| 2 | caso base: sin elección + limpio ⇒ camarilla; la solidez del lector sin hipótesis | demostración | 1 |
| 3 | medir en Julia bingo si el invariante del paso se cumple en los estados que visita el lector | sonda (pide tu permiso: busca contraejemplos) | — |
| 4 | la regla 6.4 (camino común) en Julia y en Lean, con su lema de conservación | regla + demostración | 3 |
| 5 | versiones `@[csimp]` y el diferencial Lean ↔ Julia (L4) | ingeniería | — |
| 6 | el puente completo con `improves_bin` (L8), si la ruta M1 cierra antes | demostración | — |

Los puntos 1 y 2 son ganancias seguras. El 3 decide si el 4 va en la buena dirección antes de invertir en él.

---

**Commits:** `7ca3dd2`, `eabe58a`, `97ebd56`, `c00ab6f`, `2375ef8` y `833a6c3`, en la rama `graph_owners`. Código:
`lean/improves_bingo` (README con la tabla de módulos y el estado de los teoremas). Plan: `docs/plans/lean_bingo.md`.
