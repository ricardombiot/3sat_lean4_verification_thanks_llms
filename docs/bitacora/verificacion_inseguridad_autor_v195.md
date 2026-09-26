# Verificación para el Autor v195: el lector del mapa bin, de `TriPin` a dos enunciados de una misma forma

Ricardo, este informe recoge todo el trabajo desde el v194: 80 commits en la rama `lean_improves_bin`, de `4914f15`
a `e19b53a` (25 al 27 de septiembre). Hay trabajo en Lean (`lean/improves_bin`), sondas en Julia
(`julia/improves_bin/test_3sat/probes/`) y tres correcciones de la review de Julia para que coincida con el modelo
Lean. El detalle técnico, sección a sección, está en `docs/context/ambfar.md` (§3 a §4.2λ).

**La conclusión, por adelantado.**
* El lector sin retroceso decide `φ` bajo dos hipótesis, `PieceLocalF` y `MergeSplit`
  (`FiltCert.readerVerdictW_iff_of_mergeSplit`). Está **demostrado**, con 0 `sorry` y solo `[propext, Quot.sound]`.
* Las dos tienen la misma forma: **una clique con testigos se queda en un lado de dos fijaciones complementarias**.
  En el join, las fijaciones son las dos claves del paso `n`; en una fusión de ventana, los dos abuelos del paso `n-2`.
* `PieceLocalF` está medida sin fallos en 66,9 M casos. `MergeSplit` se está midiendo ahora.
* Por el camino han caído varios enunciados que parecían ciertos. El más importante lo encontré esta última sesión:
  **`MapCert` es falso en los estados unidos**, y con él `PieceLocal`, la hipótesis única del informe anterior de
  estado. No es un fallo de la máquina, que acierta en todo lo medido, sino del invariante: pedía las restricciones
  solo a los testigos, mientras que la máquina las aplica filtrando. El sustituto, `FCert`, está formalizado.

Cada afirmación lleva su estado: **demostrado** (teorema Lean), **medido** (sonda), **deducido** (argumento sin
formalizar), **falso** (contraejemplo) o **abierto**.

---

## 1. El núcleo del lector, reformulado hasta los certificados (25–26 sep, mañana)

El v194 terminaba en `AmbTri`: dos nodos ambiguos que se poseen y poseen al pin comparten, en cada paso, una entrada
que el pin admite.

### 1.1 Recortes del trío

* **`AmbTri ⇐ AmbFar`** (`AmbTriCore`). Por debajo de la primera elección el camino está fijado (`gowner_eq`). En los
  pasos `k`, `k+1` y `k+2` la ventana fija el bit, así que los nodos ambiguos solo están por debajo de `k` o a partir
  de `k+3`. **Demostrado.**
* **`AmbFar ⇐ AmbHigh`** (`AmbHighCore`). Un nodo forzado está en todas las tablas y posee a todos, así que solo
  quedan tríos enteramente por encima de `k+3`. **Demostrado.**
* **`TriPin` no vale para los dos bits.** En `simple3sat_v3_c2` el bit 0 falla `TriPin` y su pin sobrevive; lo
  verifiqué con un volcado independiente (el estado es un kernel, y ninguna solución pasa por los dos nodos). Por
  tanto no se puede pedir `TriPin` para todo nodo. **Medido.**

### 1.2 Una ronda de cortes, y la forma cerrada

* **`TriPin₁`** (`TriPinCut`): la regla de parejas dentro del subkernel que deja una sola ronda de cortes. Es más débil
  que `TriPin` y basta al lector. Vale en el caso donde `TriPin` falla, y en los 70 nodos de primera elección medidos.
  **Demostrado; medido.**
* **`AllTriPin₁`** (`TriPinAll`): `TriPin₁` para todo nodo. Da que todo pin sobrevive. Medido en 3 427
  comprobaciones sin fallos. **Demostrado; medido.**
* **`CliqueTri`** (`CliqueTri`): la versión relativa a cualquier clique. El pin **es** el subkernel cortado
  (`pin_eq_cut`) y conserva `CliqueTri`, así que basta en los estados de partida. **Demostrado.**
* **Por certificados** (`CertFix`, `CertDescent`, `CertInvariant`):
  * `CertLink`: todo enlace compatible está en un certificado.
  * `CertLink ⇔ CliqueTri` en los estados del lector: el certificado se hace crecer como una clique.
  * `CertClique`: toda clique con testigos está en un certificado. Es equivalente, y se puede seguir operación a
    operación.
  * **Demostrado.**
* **`PrefixTri`**: el lector solo necesita cliques prefijo. **`OneShot`**: `TriPin₁` equivale a que el review tras el
  pin sea de una sola ronda. Los cortes solo pueden actuar en las fusiones. **Demostrado.**

**Lectura.** El núcleo tiene una sola forma: la máquina guarda exactamente los certificados, y las tablas los leen.
Lo que faltaba era demostrarlo siguiendo la máquina.

---

## 2. Siguiendo la máquina: las uniones (26 sep, mañana)

### 2.1 Dónde se mezclan las ramas

Una fusión de ventana `z` hereda la **unión** de las tablas de sus dos padres. Un `join` une las tablas de dos
historias. Un requisito en un paso de variable deja dos nodos de camino. En los tres casos, testigos de pasos
distintos pueden venir de ramas distintas.
* `PairExact` (exactitud por parejas) se conserva por review, `join` y `addNode` con fusiones. **Demostrado.**
* La versión relativa a un nodo se conserva sin fusiones. Con fusiones, `join` o requisito se reduce a tres
  condiciones de «coherencia de rama» (`ShadowChoice`, `JoinChoice`, `FilterChoice`). **Demostrado.**
* Helly con número 2 (`HellyTwo`): en un paso con dos nodos vivos, un trío comparte. **Demostrado**, pero no cierra la
  coherencia (§4.2q de `ambfar`).

### 2.2 El certificado elige la ventana: `MapCert`

* **`MapCert`** añade restricciones a nivel de nodo de mapa: `WitR g Q R` (los testigos poseen `Q` y algún nodo de
  camino de cada nodo de `R`) ⇒ hay un certificado por `Q` y por `R`.
* Lo conservan el review, todo filtro por requisito (`mapCert_filter`) y `addNode` con fusiones
  (`mapCert_addNode`). `FilterChoice` y `ShadowChoice` dejaron de ser obligaciones. **Demostrado.**
* **`PrefixCarry`**: la máquina conserva toda solución parcial. **`PrefixDecode`**: toda cadena de un estado es una
  solución parcial. **Demostrado.**

### 2.3 La ruta por entradas de la línea, y por qué cayó

* `LineSem.SemCert`: una clique con testigos «de la línea» (cada entrada tomada de cualquier estado) la atraviesa una
  solución parcial. Con eso el lector quedaba reducido a la cláusula (`ClauseChoice` ⇐ `ClauseLocal` ⇐ `ClauseKey` ⇐
  `ExtAt`). **Demostrado como cadena de implicaciones.**
* **Falso por entradas**: en `rand3sat_v8_c10`, paso 38, hay 16 cliques de tres nodos con testigos por entradas y sin
  solución. **Por estado**, 0 fallos en 1,3 M cliques.
* Lección: **el invariante tiene que ser por estado**, no por entradas de la línea.

---

## 3. Por estado: el join como único punto (26 sep, tarde)

* **`StateGrow`**: si toda clique con testigos crece dentro del estado, el lector decide. **Demostrado.**
* **`PieceLocal`** (`PieceJoin`, `StatePiece`, `StateLine`): toda clique con testigos de un estado unido vive en una
  pieza.
  * `mapCert_piece` (con la ventana saltada, `mapCert_skip`) y `mapCert_join`.
  * `readerVerdictW_iff_of_pieceLocal`: el lector decide con `PieceLocal` como única hipótesis. **Demostrado.**
* **Sondas del join** (`piece_learn`, `paths`, `join_grow`):
  * La pieza buena no la fija ninguna regla local: E1, E1w, H13 y H16 fallan miles de veces.
  * H19: la pieza buena es aquella donde `Q` es clique y tiene testigos en todos los `L3` anteriores. **Medido.**
* **La unión no inventa cadenas** (`chain_in_piece`): toda cadena de un estado unido lo es de una pieza, la de su
  propia clave. **Demostrado.**
* **Dos vías, lado a lado** (`ChainRoute`):
  * La de cliques pasa filtros y cláusulas; la de caminos pasa el join.
  * `combined_invariant`: `MapCert` en toda la máquina **⇔** `PieceLocal` en todo join. **Demostrado.**

---

## 4. Kernels, la review de Julia y la unión de línea (26 sep, noche)

### 4.1 Tres correcciones en Julia

* **Enlaces caducados** (`f463d92`): el corte en dos fases, la regla de parejas, el espejo y la regla de la cadena
  quitaban dueños sin desenlazar. Ahora se desenlaza, como en Lean (`LINK_MODE = :on`).
* **La review contra hijos llega al paso 0** (`e1acfd4`). Los bucles empezaban en el paso 1.
* **Regla de la cadena desactivada** (`e1acfd4`): no está en el modelo Lean.
* Tras los tres cambios, **veredictos 55/55 frente a fuerza bruta**, y todas las piezas (5 033) y estados de línea
  (2 986) son kernels. **Medido.**
* Las sondas anteriores, reejecutadas con la review corregida, dan lo mismo. **Medido.**

### 4.2 Resultados incondicionales en Lean

* **Todo estado de la máquina es un kernel** (`KernelUp.kernel_reachable`): el `UP` y el join conservan kernels, por
  inducción sobre la corrida. Todo estado de línea tiene el contexto completo del lector (`aCtx_line`).
  **Demostrado.**
* **Crecer con restricciones es exactamente `MapCert`** (`growR_iff_mapCert_line`). **Demostrado.**
* **Descompresión del join** (`PieceFilter`): la pieza revisada cabe en el estado unido filtrado por su clave.
  **Demostrado.** Medido exacto (D1) en 4 094 de 4 094 piezas.
* **Truncar la cima de un kernel da un kernel** (`Trunc`). **Una pieza fijada sin su cima queda bajo su fuente
  fijada** (`piece_pinned_below`). **Demostrado.** Esto es lo que ha servido después.

### 4.3 La unión de línea: demostrada como implicación, pero su hipótesis es falsa

`LineUnion`: `GL` (y `GLF`, con fijaciones) dice que una clique con testigos en la unión de los estados de una línea
lo es de un solo estado. **Demostrado**: `GLF` y `MapCert` en la línea `n` dan `MapCert` en la línea `n+1`. Pero
**`GL`/`GLF` son falsos** con una restricción en la cima: 20 casos, todos en `clause_mix.cnf`, paso 26. En esos casos
un testigo posee `Q` por una pieza y el nodo `25:0` por la otra. Ninguna entrada es falsa, así que no lo arregla una
regla de review. **Falso (medido).**

---

## 5. `MapCert` es falso en el estado unido; el sustituto `FCert` (27 sep)

### 5.1 El contraejemplo

Busqué cadenas de forma exhaustiva en esos casos (`certj_probe.jl`). En `clause_mix.cnf`, paso 26, hay 4 cliques
(por ejemplo `{21:1, 5:0}`) con testigos que poseen `Q` y un nodo `25:0` en cada paso, **sin ninguna cadena que pase
por `Q` y por `25:0`**. Así que `MapCert J` es falso, y con él `PieceLocal`. La sonda antigua de `PieceLocal` (3,5 M
cliques) solo miraba restricciones vacías. **Falso (medido).**

**Por qué no afecta a la máquina.** Una restricción `25:0` solo aparece cuando la máquina filtra `J` por `25:0`. Ese
filtro es la pieza `25:0`, donde `Q` ya no es clique con testigos. `MapCert` pedía la restricción solo a los
testigos; la máquina la aplica a **todos** los nodos, filtrando.

### 5.2 Lo que sí vale (medido, con la review corregida)

| medida | casos | fallos |
|---|---|---|
| `CertClique` en estados de línea y en piezas | 2,1 M + 2,6 M | 0 |
| cada testigo posee `Q` y `R` dentro de un mismo estado (GLJ) | 52,9 M | 0 |
| en cada paso, un testigo coherente con su propia clave (GLK/GLKs) | 1,55 M | 0 |
| **`PieceLocalF`** (filtro vacío, de un nodo, de 2–4 nodos al azar) | **66,9 M** | **0** |

### 5.3 El invariante nuevo, formalizado (`FiltCert.lean`)

* **`FCert g`**: todo filtro válido de `g` cumple `CertClique`. La restricción se aplica como filtro, igual que en la
  máquina.
* **Base**: `MapCert` da `FCert` (semilla y piezas de la línea 0). **Demostrado.**
* **Join** (`fCert_join`): con **`PieceLocalF`** (la clique con testigos de un estado unido filtrado vive en una pieza
  filtrada igual), el join conserva `FCert`. El certificado de la pieza filtrada sube al estado unido y sobrevive al
  filtro. **Demostrado.**
* **Pieza sin miembro en la cima** (`cert_piece_low`): sale de `FCert` de la fuente **sin hipótesis nuevas**.
  **Demostrado.** Es la pieza más larga. Encadena:
  * la pieza filtrada, sin su cima, queda bajo la fuente fijada (`piece_pinned_below`);
  * allí `FCert` da el certificado;
  * el certificado pasa por los requisitos y por `L1 = 1` cuando la ventana se salta, así que su extensión está
    permitida;
  * sube por el `up` y sobrevive a los pins.
* **Pieza con miembro `w` en la cima**:
  * **Un solo padre `c`** (`single_parent`, en cualquier kernel): la regla de vecinos pone toda la tabla de `w` en la
    de `c`, y la simetría hace el resto. **Demostrado.**
  * **Fusión (dos padres)** (`topMerge_of_mergeSplit`, con `gparent_owner`): los dos padres solo difieren en el abuelo,
    un nodo de mapa del paso `n-2`. Fijando uno de los dos abuelos, `w` se queda con un solo padre y aplica el caso
    anterior. **Demostrado**, bajo **`MergeSplit`**: la clique sobrevive al filtro por uno de los dos abuelos.
* **Lector**: `readerVerdictW_iff_of_mergeSplit`. **Demostrado.**

---

## 6. Mediciones en curso

Mientras escribo siguen corriendo tres sondas:
* `fcert_any_probe.jl`: `FCert` con filtros arbitrarios en los estados de línea.
* `toppar_probe.jl`: `TopParent` y `CertClique` de piezas filtradas; cuenta cuántas cimas tienen fusión.
* `mergesplit_probe.jl`: `MergeSplit`, la hipótesis exacta.

Si `MergeSplit` fallara, la reducción seguiría siendo correcta, pero habría que volver a `TopMerge` o a `TopParent`,
que son más débiles.

---

## 7. Resumen

| pieza | estado |
|---|---|
| `AmbTri ⇐ AmbFar ⇐ AmbHigh`; `TriPin₁`, `CliqueTri`, `CertLink ⇔ CliqueTri`, `CertClique`, `PrefixTri` | **demostrado** |
| `TriPin` para los dos bits | **falso** (medido) |
| `MapCert` por filtros, fusiones y ventana saltada dentro de una pieza | **demostrado** |
| ruta por entradas de la línea (`SemCert`, `ExtAt`) | implicaciones **demostradas**; hipótesis **falsa** |
| la unión no inventa cadenas (`chain_in_piece`); `combined_invariant` | **demostrado** |
| review de Julia = modelo Lean (enlaces, paso 0, sin regla de la cadena); veredictos 55/55 | **hecho, medido** |
| todo estado de la máquina es un kernel; crecer ⇔ `MapCert` | **demostrado** |
| `GL`/`GLF` (unión de línea) | **falso** con restricción en la cima |
| `MapCert` del estado unido, `PieceLocal` | **falso** |
| `FCert`: base, join desde `PieceLocalF`, pieza sin cima, cima sin fusión, fusión desde `MergeSplit` | **demostrado** |
| lector decide bajo `PieceLocalF` + `MergeSplit` | **demostrado** |
| `PieceLocalF` | **abierto**; medido 66,9 M sin fallos |
| `MergeSplit` | **abierto**; midiéndose |

## 8. Lo siguiente

1. Leer las tres sondas en curso y ajustar la hipótesis de la fusión si hace falta.
2. Atacar `PieceLocalF` y `MergeSplit` como un solo lema: «una clique con testigos se queda en un lado de dos
   fijaciones complementarias». Las sondas del join dicen que la selección la hace la clique entera con sus testigos
   de los pasos de cláusula (H19), no una entrada ni un testigo suelto.
3. No construir sobre `MapCert` del estado unido. `LineUnion`, `filter_union` y `GrowCert` siguen siendo correctos
   como implicaciones, pero su hipótesis es falsa.

## 9. Una frase

La máquina aplica las restricciones filtrando, y con el invariante escrito así, todo lo que separa al lector de
decidir `φ` es que una clique con testigos no se reparta entre los dos lados de una unión: en el join, entre dos
claves; en una fusión, entre dos abuelos. Lo primero está medido sin fallos en casi 67 millones de casos.
