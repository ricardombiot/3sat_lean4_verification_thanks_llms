# La escalera del lector sin retroceso (mapa bin): dónde está y cómo seguir

> Proyecto `lean/improves_bin`, rama `lean_improves_bin`. Antes se llamaba `ambfar` (`docs/context/ambfar.md`). Estado al día en **§4.2ο.2** (M1 ⇐
> `CertPin`, el círculo de la inducción y el reparto de M1 en M1a + M1b), §4.2ο.1 (**el lector decide bajo M1**, un solo
> enunciado sobre el join) y §4.2ο (las cliques de nodos de camino fallan en el join), §4.2ξ (ruta de `CliqueTri`,
> ⚠ hipótesis falsa), §4.2ν (línea global: empalme) y §4.2μ (núcleo en cinco hipótesis locales). Sesión 2026-09-27; §4.2λ y §4.2κ son las anteriores. Antes: estado en §4.2λ (sesión 2026-09-27; §4.2κ es la
> sesión anterior). Informe de todo lo hecho desde el v194: `docs/bitacora/verificacion_inseguridad_autor_v195.md`.
> Cada pieza va marcada como **demostrado** (teorema Lean, 0 `sorry`, solo `[propext, Quot.sound]`),
> **medido**, **deducido** (argumento en papel, sin formalizar), **propuesto** o **abierto**.
> Informes de referencia: `docs/bitacora/verificacion_inseguridad_autor_v194.md` (hasta `TriPin`/`AmbTri`) y `…_v195.md`
> (de `AmbTri` a `PieceLocalF` + `MergeSplit`). Propuesta de máquina para M1b (etiqueta de clave de un nivel): `…_v196.md`. Reglas formalizadas y propuesta de etiquetas de todos los niveles: `…_v197.md` (ambas retiradas del código; en la historia, merge `e0be7a3`). Marcha atrás: `…_v198.md`.
> Este documento añade el peldaño `AmbTri ⇐ AmbFar` y las propuestas para seguir.

---

## 0. Qué se quiere demostrar

El lector (`ReaderExec.readerVerdictW`) recorre la corrida de la máquina (`pureRun φ`), y para cada
entrada `kv` parte de `filterAll kv.2 []`. En cada estado toma el **primer paso con elección**
(`firstChoice`), pincha el primer nodo de ese paso cuyo review deja el grafo válido y **nunca deshace**.

* **Solidez** (`readerVerdictW_sound`): **demostrado**, sin hipótesis.
* **Completitud**: el lector no se atasca. Todo lo que queda abierto está aquí.

Meta final: `readerVerdictW φ = true ↔ Satisfiable φ`.

## 1. Vocabulario mínimo

* `GPathM`: `nodes`, `gowners` (la global: entradas vivas), `current_step`.
* `PathNodeId = (id, parent_id, gparent_id)`: nodo del mapa más su ventana de tres pasos.
* Tabla de un nodo `y`: `ny.owners`. «`y` posee a `r`» = `r ∈ ny.owners`. Las tablas son simétricas.
* `choiceAt g k`: hay dos ids de mapa distintos entre las entradas de la global en `k`. En bin son los
  dos bits del paso.
* `PrefixUpTo g k`: ningún paso por debajo de `k` tiene elección.
* Pinchar `q`: `filterAll g [q.id]` (review normal; el agresivo es equivalente a lo largo del lector,
  **demostrado**, ver §2).
* **Kernel** (`Kernel.lean`): las propiedades estáticas de un punto fijo válido del review:
  * nodos válidos, tablas dentro de la global, simetría;
  * enlaces a padres e hijos presentes en las tablas de ambos extremos;
  * **regla de parejas**: dos nodos que se poseen comparten entrada en cada paso;
  * toda entrada de una tabla está en la tabla de algún padre y de algún hijo.
* **Invariantes de forma** usados abajo:
  * `OOS`: en su propio paso, la tabla de un nodo solo le contiene a él;
  * `PBelow`/`SAbove`: padres un paso abajo, hijos un paso arriba;
  * `PMP`: `some p.id = n.parent_id` para todo padre `p` de `n`;
  * `GPMP`: `n.gparent_id = p.parent_id`, y sin padre no hay abuelo;
  * `RootAtZero`, `NotRoot`: en el paso 0 no hay padre, y por encima sí.

## 2. La escalera, peldaño a peldaño

Cada flecha es un teorema. Todas están **demostradas**. Cada peldaño tiene su
`readerVerdictW_iff_of_X : (∀ kv ∈ pureRun φ, X …) → (readerVerdictW φ = true ↔ Satisfiable φ)`.

| # | hipótesis | módulo | idea del paso |
|---|---|---|---|
| 1 | `ProgressFirst` | `ReaderPrefix` | el lector solo pincha en `firstChoice`; el prefijo fijado crece (`firstChoice_pin_gt`, `prefixUpTo_pin`) |
| 2 | ⇐ `PinChain` | `ReaderPrefix` | un pin válido en `firstChoice` conserva alguna cadena sólida |
| 3 | ⇐ `OtherBit` | `PinChainBin` | en bin cada paso tiene dos bits; el bit de la cadena es gratis (`chainSound_pin_same`), queda el contrario. `chainG_through_pin` lo hace también necesario |
| 4 | ⇐ `OtherBitSem` | `OtherBitSem` | enunciado sobre la fórmula: los pins son una asignación parcial y la línea final lleva **todas** las soluciones (`carried_unique`) |
| 5 | ⇐ `NoDeadEnd` | `NoDeadEnd` | en un estado válido del lector no mueren los dos pins (`NoDeadEnd := ProgressFirst`) |
| 6 | ⇔ `KernelSplit` | `Kernel`, `KernelReader`, `KernelIff` | un pin sobrevive ⇔ hay por debajo un kernel válido que lo fija |
| 7 | ⇐ `TriPin` | `KernelSplit` | regla de parejas con el pin como tercer miembro fijo ⇒ `restrictPin g x` es ese kernel |
| 8 | ⇐ `AmbTri` | `TriPinCore` | si uno de los dos nodos es exclusivo de `x`, el trío siempre comparte |
| 9 | ⇐ `AmbFar` | `AmbTriCore` (nuevo, `4914f15`) | prefijo fijado + ventana de tres pasos (§3) |
| 10 | ⇐ `AmbHigh` | `AmbHighCore` (nuevo) | los nodos forzados poseen a todos (§4.1) |

Piezas auxiliares que sostienen la escalera (todas **demostradas**):

* **Simetría de toda la máquina** (`SymMachine.symInv_reachable`), `join` incluido, gracias al
  invariante `CutClosed`: toda entrada de tabla en un paso cubierto por la global es un owner global.
* **Review agresivo = normal** a lo largo del lector (`PairInactive.reviewAgg_eq_review`,
  `SymMachine.start_agg_eq`, `pin_agg_eq`).
* **El review nunca baja de un kernel** (`below_review`); todo estado válido del lector es un kernel
  (`kernel_readPins`, con el invariante `OwnAbove`); el review nunca añade hijos (`sonsSub_review`).
* **Solidez de la máquina sin `ClauseStepExact`/`SkipExact`** (`soundness_of_noDeadEnd`), con
  `NoDeadEnd` + `RootValid`.

### Por qué el peldaño 7 es donde cambia la naturaleza del problema

Los peldaños 1–6 son equivalencias o reducciones «de bookkeeping»: `KernelSplit ⇔ NoDeadEnd` muestra que
reformular sobre kernels **no** hizo el núcleo más fuerte. `TriPin` en cambio es **local**: habla de
tríos de tablas en un solo estado.

Pero **`TriPin` no se deduce de los axiomas del kernel**. Son consistencia local (arco + parejas), y la
consistencia local admite puntos fijos sin ninguna cadena. Cualquier prueba tiene que usar **la historia
de la máquina**: cómo heredó las tablas el UP y cómo las filtraron los requisitos y los pins.
**Deducido** (argumento estándar; sin contraejemplo formal en Lean).

## 3. El peldaño nuevo: `AmbTri ⇐ AmbFar` (`AmbTriCore.lean`)

Contexto `ACtx g` = `PinCtx g` (kernel, `NodupIds`, `OOS`, `PBelow`, `SAbove`, `SNN`, `below`) +
`Reader.RCtx g` (`PMP`, `GPMP`, `RootAtZero`, `NotRoot`…). Vale en todo estado válido del lector
(`aCtx_readPins`). Sea `k = firstChoice g` y `x` una entrada de la global en `k`.

**Demostrado:**

1. **Bajo la elección el camino está fijado** (`gowner_eq`). Dos owners globales con el mismo nodo de
   mapa en un paso `≤ k` son el mismo `PathNodeId`. Inducción sobre el paso:
   * la ventana de un nodo se lee de sus padres (`PMP`, `GPMP`);
   * el padre existe (`NotRoot` + validez) y es owner global en el paso anterior;
   * sin elección en ese paso, los padres tienen el mismo id, y por inducción son iguales;
   * en el paso 0 no hay padre ni abuelo (`RootAtZero`, `GPMP`).
2. **En los pasos `l < k` el trío comparte** (`share_below`). Las tres tablas tienen entrada en `l`
   (validez), las tres son owners globales del mismo nodo de mapa, y por (1) son la misma.
3. **En el paso `l = k` comparten `x`**, porque `x` se posee a sí mismo (`self_own`, por `OOS` +
   validez).
4. **La ventana fija el bit** (`excl_near`). Un nodo en `k`, `k+1` o `k+2` que posee a `x` es
   exclusivo de `x`:
   * en `k`, por `OOS`;
   * en `k+1`, sus entradas de `k` son padres y llevan el id `parent_id` (`parentId_of_owner`);
   * en `k+2`, llevan el id `gparent_id` (`gparentId_of_owner`);
   * con el mismo id en el paso `k`, (1) da el mismo nodo.
5. Por tanto los nodos ambiguos están en pasos `< k` o `≥ k+3` (`far_of_ambiguous`).

**Lo que queda, abierto:**

> **`AmbFar g k x`**: para `y`, `w` ambiguos respecto a `x` (ambos poseen `x` y otra entrada del paso
> `k`), que se poseen, y con pasos `< k` o `≥ k+3`, en cada paso `l` con `k < l < current_step` hay una
> entrada común a `y`, `w` y `x`.

`readerVerdictW_iff_of_ambFar`: si en cada estado válido que visita el lector algún nodo de la primera
elección cumple `AmbFar`, el lector decide `φ`. **Demostrado.**

Recordatorio del peldaño 3: basta **uno de los dos bits**. `NoDeadEnd` solo falla si `AmbFar` falla a la
vez para el bit 0 y para el bit 1, en el mismo estado.

## 4. Propuestas para seguir

### 4.1 Recortar `AmbFar` a nodos altos — **hecho** (`AmbHighCore.lean`)

**Demostrado** (`forced_in_all`, `forced_owns_all`, `ambFar_of_ambHigh`, `readerVerdictW_iff_of_ambHigh`).
* Un nodo `y` en un paso `s < k` es el único nodo vivo de su paso, por `gowner_eq`.
* Todo nodo vivo tiene una entrada en `s` (validez), y esa entrada es `y`. Así que **`y` está en todas
  las tablas**, y por simetría **la tabla de `y` contiene a todos los nodos vivos**: los nodos forzados
  poseen todo.

Consecuencias:
* **`y` y `w` ambos bajo `k`**: sirve cualquier entrada de `x` en `l`.
* **`y` bajo `k` y `w` por encima**: la regla de parejas de `(w, x)` da `r` en `l`, y `y` lo posee
  automáticamente.

Queda **`AmbHigh g k x`**, el único enunciado abierto del lector:

> para `y`, `w` ambiguos respecto a `x`, que se poseen, **ambos en pasos `≥ k+3`**, en cada paso `l` con
> `k < l < current_step` hay una entrada común a `y`, `w` y `x`.

El núcleo queda en su forma más limpia: **tríos enteramente por encima del prefijo fijado**.

### 4.2 Medir `AmbHigh` / `AmbFar` (pendiente de confirmación)

Una sonda solo sobre tablas, en los estados del lector. Mediría:
* cuántos nodos ambiguos hay en pasos `≥ k+3`, y cuántas parejas;
* si alguna pareja rompe el trío, y en qué `l` respecto a `k` y a los pasos de `y` y `w`;
* si el fallo ocurre **para los dos bits a la vez** (lo único que rompe `NoDeadEnd`).

Mejor en Julia: el modelo Lean en listas tarda unos 100 s de máquina en `v4_c12_i1`, y la sonda
`otherbit-probe` no terminó en más de 18 min. La sonda Lean existente (`OtherBitProbeMain.lean`) puede
servir de oráculo en instancias de 3 variables. Sin lanzar hasta que lo confirmes.

**Primera medida (Lean, `lake exe ambhigh-probe`, 6 instancias pequeñas, todas las ramas del lector).**
* `highBoth = 0`: en cada estado con elección, algún bit cumple `AmbHigh`. `dead = 0`.
* **Un fallo de un solo bit** en `simple3sat_v3_c2` (4 variables): en `k=1`, el bit 0 falla `AmbHigh`
  y `TriPin`. Los nodos son `y` en el paso 9 y `w` en el 5, y falla en `l=7`. **El pin de ese bit
  sobrevive.** Así que `TriPin` es estrictamente más fuerte que la supervivencia: no se puede pedir para
  todo `x`, solo para uno. Eso descarta un invariante que dé `TriPin` para todos los bits (como la
  versión «para todo `x`» de `SecPair` en §4.3, o la regla de tríos de §4.4 como invariante de la
  máquina actual). **Medido, sin valor estadístico.**
* **Verificado que no es un error** (`lake exe ambhigh-dump`, independiente del bucle de la sonda):
  * el estado es el de partida, sin pins, y es un kernel (0 roturas de simetría y de regla de parejas);
  * `x = [1.0|0.0|_]`, `y = [9.0|8.1|7.0]`, `w = [5.1|4.1|3.0]`; en el paso 7, `y∩w = {[7.0|6.0|5.1]}` y
    ese nodo no está en la tabla de `x`;
  * semántica: 6 soluciones concuerdan con `x`, y **ninguna pasa por `y` y `w` a la vez**. El enlace
    `y–w` es legítimo por parejas, pero no es compatible con `x`;
  * al pinchar `x`, el review corta `w` de la tabla de `y` y el estado sigue válido.

### 4.2b `TriPin₁`: debilitar `TriPin` por la estructura — **hecho** (`TriPinCut.lean`)

**Demostrado.**
* `Cx g x y w`: el enlace `y–w` tiene, en cada paso, un testigo que `x` también posee.
* `restrictPin₁ g x`: los nodos que poseen `x`, con tablas y enlaces restringidos a entradas `Cx`.
* `TriPin₁ g x`: regla de parejas dentro de `restrictPin₁`. Es una ronda de cortes, sin cascada.
* `triPin₁_of_triPin`: es más débil que `TriPin`.
* `restrict₁_kernel`: bajo `TriPin₁`, `restrictPin₁` es un kernel válido bajo `g` que fija `x`.
* `kernelSplit_of_triPin₁`, `readerVerdictW_iff_of_triPin₁`.

La escalera tiene ahora una rama paralela: `KernelSplit ⇐ TriPin₁ ⇐ TriPin ⇐ AmbTri ⇐ AmbFar ⇐ AmbHigh`.
En el caso medido, el enlace `y–w` no es `Cx`, así que `TriPin₁` no lo exige. Falta medir si
`TriPin₁` vale en los pins que sobreviven, y si hacen falta más rondas (`TriPinₙ`, cuyo límite es
`NoDeadEnd`).

**Medida (`ambhigh-probe`, 6 instancias pequeñas, todas las ramas del lector).** `TriPin₁` vale para
los 70 nodos de primera elección examinados, **incluido el caso en que `TriPin` falla**
(`simple3sat_v3_c2`, `k=1`, bit 0). Coherencia de la sonda: 0 casos de `TriPin` o `TriPin₁` ciertos
con el pin muerto, como exigen los teoremas. **Límite**: en estas instancias **todo pin sobrevive**
(`otherbit-probe`: `pins = valid`), así que aún no se ha visto a `TriPin₁` separar un pin vivo de uno
muerto. **Medido, sin valor estadístico.**

### 4.2c El invariante `AllTriPin₁` — **formalizado** (`TriPinAll.lean`)

La máquina guarda exactamente el conjunto de certificados: en todo lo medido (6 pequeñas, 6 construidas
a mano, 20 aleatorias de 4 variables) **ningún pin muere** y todo estado visitado tiene solución. Las
tablas lo registran por parejas, y una ronda de cortes basta para leer los certificados que pasan por `x`.

* `AllTriPin₁ g`: `TriPin₁ g x` para **todo** nodo vivo `x`. Uniforme en `x`: la forma de un invariante.
* `allPinsAlive_reader`: bajo él, **todo** pin en la primera elección sobrevive (más fuerte que
  `NoDeadEnd`, que pide uno). **Demostrado.**
* `readerVerdictW_iff_of_allTriPin₁`. **Demostrado.**
* **Abierto**: que `AllTriPin₁` valga en los estados del lector (`AllTriPin₁Reader`). Ruta: que lo
  construyan `addNode` y `join` y que lo conserven el review y el pin.
* **Medido** (`ambhigh-probe --all`, 12 instancias pequeñas: las 6 de `example_cnf` más las 6
  construidas a mano, todas las ramas del lector): `AllTriPin₁` vale en **todos** los estados válidos,
  para **todo** nodo vivo `x` (3427 comprobaciones, 0 fallos). Sin valor estadístico.

### 4.2d `CliqueTri`: la forma cerrada, y el pin la conserva — **demostrado** (`CliqueTri.lean`)

**Por qué `AllTriPin₁` no basta como invariante.**
* Tras pinchar `x`, `x` queda en todas las tablas. `TriPin₁` para el siguiente `x'` habla de `x` y `x'`
  juntos en el estado anterior: cada pin sube un orden.
* En `addNode` ocurre lo mismo: un nodo nuevo hereda la unión de las tablas de sus padres, y la
  compatibilidad en el paso nuevo pide cuatro nodos en la fila anterior.

**Definiciones.**
* `TriP g P`, relativo a un conjunto `P` de nodos:
  * se restringe a los nodos que poseen todo `P`;
  * un enlace es `P`-compatible (`CxP`) si en cada paso tiene un testigo que posee `P`;
  * sobre los enlaces `P`-compatibles vale la regla de parejas, con testigos `P`-compatibles.
* `CliqueTri g`: `TriP g P` para toda clique `P` (nodos que se poseen dos a dos).
* Extremos: `TriP g []` es la regla de parejas del kernel (`triP_nil`), y `TriP g [x]` da
  `TriPin₁ g x` (`triPin₁_of_triP`). Por tanto `CliqueTri ⇒ AllTriPin₁`.

**Demostrado:**
1. **El pin es el subkernel cortado** (`pin_eq_cut`). Con `TriPin₁ g x` en un estado del lector, el
   estado pinchado y `restrictPin₁ g x` están cada uno dentro del otro: tienen las mismas tablas.
   * Una inclusión es `below_filterAll`: el review nunca baja de un kernel.
   * La otra (`below_cut_pin`): todo nodo del estado pinchado posee `x` (`pin_owns_x`, porque con el
     prefijo fijado `x` es la única entrada de su paso), y todo enlace del estado pinchado tiene sus
     testigos dentro, que poseen `x`, así que es `x`-compatible en `g`.
   * **El paso del lector es exactamente una ronda de cortes.**
2. **El pin conserva `CliqueTri`** (`cliqueTri_pin`, vía `cliqueTri_of_cut`).
   * Una clique `P` del estado pinchado es la clique `x :: P` de `g`.
   * `TriP g (x :: P)` se aplica dos veces: una para el testigo, y otra para los testigos de los
     enlaces del testigo, que es la compatibilidad anidada que exige el corte.
3. **Solo importan los estados de partida** (`cliqueTri_reader`, `readerVerdictW_iff_of_cliqueTri`).
   * Si `CliqueTri` vale en los estados de partida válidos `filterAll kv.2 []`, vale en todo estado
     del lector.
   * Por tanto el lector decide `φ` y **todo** pin sobrevive.

**Lo que queda (abierto): `CliqueTri` en la salida de la máquina.** Es un enunciado sobre la máquina
sola, sin lector. Lo explorado:
* **No es un invariante de cada operación.** El review quita testigos al quitar entradas, así que solo
  cabe pedirlo en los puntos fijos. Igual que la regla de parejas.
* **Helly no sirve.** Si las tablas fueran proyecciones por parejas de un conjunto de certificados con
  la propiedad de Helly (toda clique tiene un certificado común), `TriP` sería trivial. Pero
  `TriPin` (sin cortes) falla en `simple3sat_v3_c2`, así que Helly falla en la máquina. `CliqueTri` es
  estrictamente intermedio: los cortes descartan justo los enlaces sin certificado común.
* **`addNode`.** Una clique con nodos de la fila nueva se traduce a una clique con sus padres. El
  obstáculo es que un nodo nuevo `z` hereda la **unión** de las tablas de sus padres. En bin, los
  padres de `z` comparten `id` y `parent_id` y solo difieren en `gparent_id`, lo que acota la unión a
  como mucho dos padres.
* **`join`.** Une las tablas de dos estados con la misma clave. Aparecen enlaces cruzados sin testigos
  comunes, que solo el review posterior puede cortar. Tiene que razonarse sobre el punto fijo.
* **Ruta propuesta.** Una caracterización del punto fijo del review en términos de certificados: que
  las tablas cortadas relativas a una clique sean exactamente las proyecciones de los certificados que
  pasan por la clique. De ahí `CliqueTri` saldría por los certificados de la propia clique. Es la
  versión en tablas de la visión de subconjuntos de caminos.

### 4.2e La caracterización por certificados — **formalizada** (`CertFix.lean`)

* **Certificado**: una cadena `ChainSound g sel`, con un nodo vivo por paso, enlazados por padres e
  hijos y poseyéndose todos. En la línea final son las soluciones. En un estado intermedio son los
  caminos parciales que cumplen los requisitos vistos.
* `cxP_of_cert` (**demostrado, siempre**): si un certificado pasa por la clique `P`, por `y` y por
  `w`, el enlace `y–w` es `P`-compatible. Los testigos son los nodos del propio certificado.
* **`CertLink g`** (la caracterización): el converso. Todo enlace `P`-compatible está, junto con `P`,
  en un certificado.
* `cutTable_iff_cert` (**demostrado**): bajo `CertLink`, la tabla cortada de `y` relativa a `P` es
  exactamente lo que proyectan los certificados que pasan por `y` y `P`.
* `cliqueTri_of_certLink` (**demostrado**): el testigo en cada paso es el nodo del certificado, y sus
  enlaces son compatibles por el mismo certificado.
* `readerVerdictW_iff_of_certLink` (**demostrado**): si los estados de partida cumplen `CertLink`, el
  lector decide `φ`.

`CertLink` con `P = []` es la exactitud por parejas: todo enlace que pasa la regla de parejas está en
un certificado. La cadena queda así:

  `CertLink` (partida) ⇒ `CliqueTri` (partida) ⇒ `CliqueTri` (todo estado del lector) ⇒ `AllTriPin₁`
  ⇒ `TriPin₁` ⇒ `KernelSplit` ⇔ `NoDeadEnd` ⇒ el lector decide.

**Abierto:**
* **`CertLink` en la salida de la máquina.** Es el enunciado semántico de que la máquina guarda
  exactamente los certificados, en su forma de tablas.
* ~~Conjetura~~ **`CliqueTri ⇒ CertLink`: demostrado** (`CertDescent.lean`, `certLink_iff_cliqueTri`).
  No hacen falta ni pins ni restricciones: el certificado se hace crecer como una clique.
  * **Invariante** `Wit g Q`: `Q` es clique y en cada paso algún nodo vivo posee todo `Q`.
  * **Arranque**: `y :: w :: P`, cuyos testigos son los del enlace `P`-compatible.
  * **Crecimiento** (`grow`): `TriP g Q` sobre la pareja `(q, q)` da un nodo `r` en el paso deseado,
    con un enlace `Q`-compatible desde `q`. Sus testigos poseen `Q` y `r`.
  * **Cierre** (`chain_of_cover`): una clique con un nodo en cada paso tiene exactamente uno por paso
    (`OOS`) y es un certificado. Las entradas de los pasos vecinos son padre e hijo, y el nodo del
    paso 0 es la raíz.
  * **En los estados del lector, `CliqueTri` y `CertLink` son el mismo enunciado.** El núcleo tiene
    una sola forma: la máquina guarda exactamente los certificados, leídos por las tablas cortadas.

### 4.2f Intento: `CertLink` en la salida de la máquina — **no demostrado**

**Qué dice en la salida.** En `g₀ = filterAll kv.2 []` (paso final), los certificados son exactamente
las soluciones:
* toda solución da una cadena en `g₀` (`OtherBitSem.chain_of_agrees`, sobre `carried_unique`);
* toda cadena decodifica a una solución (`NoDeadEnd.selOfAssign_decode`);
* y la ventana de un nodo (`PMP`, `GPMP`) fija el `PathNodeId` a partir de los nodos de mapa.

Así, `CertLink(g₀)` es un enunciado **sobre `φ`**: todo enlace compatible relativo a una clique está,
junto con la clique, en el camino de una solución.

**Intento 1: inducción sobre la corrida de la máquina.** No funciona paso a paso.
* Tras `addNode`, la compatibilidad en el paso nuevo pide un testigo `z` que posea `y`, `w` y `P`. La
  tabla de `z` es la unión de las de sus padres (como mucho dos en bin), así que distintos miembros
  pueden venir de padres distintos.
* Además, en `CxP` los testigos de pasos distintos son independientes entre sí.
* Por tanto `CertLink(addNode g)` no se sigue de `CertLink(g)`: solo el review posterior puede
  restaurarlo. Tampoco `join` lo conserva, porque crea enlaces cruzados.

**Intento 2: razonar sobre el punto fijo.**
* `CertLink ⇔ CliqueTri`, y el review solo impone la regla de parejas.
* Los axiomas del kernel admiten puntos fijos sin cadenas.
* El fallo medido de `TriPin` muestra que las tablas no tienen la propiedad de Helly.
* Lo que la historia sí da (demostrado) es que **no se pierde ningún certificado**. Lo que falta es el
  converso: que toda estructura compatible esté respaldada por una solución, es decir, **la exactitud
  del review respecto a la fórmula**.

**Diagnóstico.**
* Es el contenido entero de la completitud del lector. Ya no queda un lema más pequeño en la cadena.
* Cualquier prueba tiene que usar la estructura concreta de los requisitos bin: cada paso de
  cláusula prohíbe localmente la ventana `000`, y las ventanas son de tres pasos.
* Rutas posibles:
  * **Local a global**: exactitud dentro de un bloque de cláusula, y pegado a lo largo de la cadena de
    pasos, aprovechando que las ventanas solapadas dan una estructura de anchura acotada. **Propuesto.**
  * **Medir antes** si `CliqueTri` vale en la salida, en las instancias pequeñas, por ejemplo con
    cliques de tamaño ≤ 2, porque la versión completa es exponencial. Si falla, esta ruta muere
    aunque el lector siga funcionando. `NoDeadEnd` es lo necesario; `CliqueTri` es suficiente.
    **Pendiente de confirmación.**

### 4.2g Segundo intento, operación a operación: `CertClique` — **en curso**

**`CertClique g`**: toda clique con testigos (`Wit`) está en un certificado. En los estados del lector
es `CertLink` (`certClique_iff_certLink`, **demostrado**). Se enuncia sobre cualquier estado, así que
puede seguirse a lo largo de la máquina.

**Por operación de la máquina** (la salida es `filterAll kv.2 []` de estados hechos con
`up = addNode ∘ filterAll reqs`, `join` e `insertPure`):

| operación | ¿conserva `CertClique`? | por qué |
|---|---|---|
| review sin requisitos | **sí, demostrado** (`certClique_filterAll_nil`) | tras el review hay menos cliques y menos testigos, y los certificados sobreviven (`ChainSound_filterAll`) |
| filtro por requisito | abierto | la clique `Q` tiene testigo en el paso del requisito con el id pedido, pero `Q ∪ {ese testigo}` no tiene por qué tener testigos en los demás pasos |
| `addNode`, fila sin fusión (un padre) | plausible, sin formalizar | los testigos que poseen `z` poseen a su único padre `p`; el certificado de `Q ∪ {p}` se extiende por `z` (`ChainSound_addNode`) |
| `addNode`, nodo con dos padres | abierto | `z = (d,a,b)` con padres `(a,b,c₁)` y `(a,b,c₂)`: un testigo puede poseer `Q` con `p₁` y otro, en otro paso, `Q` con `p₂`, sin testigo común |
| `join` | abierto | une tablas de historias distintas con la misma clave |

**El mecanismo común**: `Wit` permite testigos distintos en pasos distintos. El review, que es por
parejas, no los correlaciona. Donde la máquina **une** (fusiones de ventana, `join`, requisitos que
dejan varios nodos de camino con el mismo nodo de mapa), testigos de ramas distintas pueden
completar una clique que ninguna rama sola completa.

**Siguientes pasos posibles**:
1. Formalizar `addNode` sin fusión.
2. Ver si la estructura bin impide la mezcla en las fusiones. Los padres solo difieren en el paso
   `s−3`, y lo que puede distinguirlos son los requisitos que miran a ese paso.
3. Si no la impide, cambiar la máquina para que registre la rama (por ejemplo, tablas relativas al
   `gparent` en las fusiones).

### 4.2h ¿Impide la estructura bin la mezcla en las fusiones? — **no, por sí sola** (deducido)

**Dónde hay fusiones.** Un nodo nuevo `z = shiftPid q d = (d, q.id, q.parent_id)` tiene como padres
los nodos de la fila anterior con el mismo `(id, parent_id)`, que solo difieren en el paso `s−3`.
Recorriendo el mapa (`CnfMapBin`):

| paso de `z` | padres | qué olvida |
|---|---|---|
| `2v+1` (variable, positiva) | 2 | `¬a_{v−2}` (el paso `2v−2`) |
| `2v+2` (negación) | 1 | nada: el padre en `2v+1` tiene un único padre posible (el hijo de un positivo es único) |
| `2n+1` (fusión media `F`) | 2 | `¬a_{n−2}` |
| primer literal tras `F` | 1 | nada: solo hay un `F` |
| segundo literal tras `F` | 2 | `a_{n−1}` |
| resto de pasos de cláusula | 2 | el bit de literal de hace tres pasos |

Hay fusión en casi todos los pasos.

**Qué información se pierde.**
* En la sección de cláusulas, el bit olvidado es el valor de un literal, que por el requisito es
  función de una variable `x_u`.
* Las tablas de los dos padres sí distinguen `x_u`: `T(p₁)` solo ve `x_u = v₁` y `T(p₂)` solo
  `x_u = v₂`.
* Pero `T(z) = T(p₁) ∪ T(p₂)`, y una clique `Q ∪ {z}` puede tener testigos que en un paso poseen `p₁`
  y en otro `p₂`. Nada en las tablas por parejas obliga a que un testigo que posee `p₂` sea
  incompatible, junto con el resto de `Q`, con `x_u = v₁`.
* La exclusión es de tres vías (`p₂`, `x_u`, testigo), y el review es de dos.

**Conclusión.** La estructura bin no impide la mezcla por sí sola. El olvido de ventana es inherente a
cualquier ventana finita, y las fusiones aparecen en casi todos los pasos, incluidos todos los de
cláusula.

**¿Quitar la fusión media `F`?**
* No resuelve esto. Sin `F`, el primer paso de cláusula tendría ventana `(b₁, ¬a_{n−1}, a_{n−1})` y las
  fusiones de los pasos de cláusula seguirían igual: las crea el bloque de tres literales, no `F`.
* Tampoco estorba: `F` solo concentra en un paso el olvido de la sección de variables, y simplifica la
  aritmética y las pruebas (`selOfAssign`, `step_cases`).
* Recomendación: **mantenerla**.
* Una observación más útil: los pasos de negación `2v+2` duplican la variable, así que en la sección de
  variables la ventana de tres cubre en la práctica 1,5 variables. No afecta a la mezcla, pero sí al
  tamaño.

**Lo que sí atacaría la mezcla es cambiar qué guardan las tablas en las fusiones** (propuesto):
* Guardar los owners de `z` **por rama de padre**: `T_{p₁}(z)` y `T_{p₂}(z)` en vez de la unión. En bin
  cada nodo tiene como mucho dos padres, así que la memoria como mucho se duplica.
* La duda es si basta con un nivel. Un nodo posterior fusiona ramas de `z`, que a su vez tenía ramas.
  Si la separación se anida, crece exponencialmente. Si no se anida, la mezcla sube un nivel.
* Decidir si el review puede colapsar las ramas anidadas sin perder la exclusión de tres vías es
  exactamente el «test de vacío» de la visión de subconjuntos.

### 4.2i El diseño se mantiene; el invariante era demasiado fuerte: `PrefixTri` — **demostrado**

El usuario descarta cambiar la máquina: el diseño actual no tiene fallos y falta la demostración. Si
es así, el escenario de mezcla de §4.2g–h tiene que ser un problema **del invariante**, no de la
máquina. Y lo es:
* `CliqueTri` y `CertLink` piden la regla de tríos para **toda** clique.
* El escenario de mezcla usa cliques con huecos: dos nodos lejanos y una fusión entre medias.
* El lector nunca forma esas cliques. Sus pins van en pasos crecientes, y todo lo que queda por debajo
  del último pin está forzado (un solo nodo, presente en todas las tablas).

**Definiciones.**
* **`PrefixClique g Q k`**: clique con un nodo en cada paso `0 … k` y ninguno por encima.
* **`PrefixTri g`**: `TriP g Q` para toda clique prefijo.

**Demostrado** (`PrefixTri.lean`):
* `prefixTri_of_cliqueTri`: es más débil que `CliqueTri`.
* `triP_congr`: `TriP g P` solo depende de qué nodos poseen `P`, así que añadir nodos forzados no
  cambia nada (`ownsAll_forced`).
* `triPin₁_of_prefixTri`: en un estado del lector, los forzados bajo `k` junto con el pin `x` forman una
  clique prefijo, y su regla de tríos es `TriPin₁ g x`.
* `prefixTri_pin`: el pin conserva `PrefixTri`. Una clique prefijo del estado pinchado, con `x` y los
  forzados añadidos, es clique prefijo del estado anterior, y `triP_of_cut` la traslada.
* `readerVerdictW_iff_of_prefixTri`: **basta `PrefixTri` en los estados de partida.**

**Por qué es el objetivo correcto.** Va en el mismo orden que la máquina, de izquierda a derecha: una
clique prefijo es un camino parcial hasta `k`, que es exactamente lo que la máquina construye paso a
paso. Las mezclas en fusiones de §4.2h necesitaban nodos por encima y por debajo de la fusión sin los
pasos intermedios, y en una clique prefijo todos los pasos hasta `k` están fijados.

**Siguiente**: `PrefixTri` en la salida de la máquina, siguiendo la corrida.

### 4.2j `PrefixTri` en la salida: forma operativa — **demostrado** (`OneShot.lean`)

Por `prefixTri_pin`, `PrefixTri` en un estado de partida equivale a tener `TriPin₁` en la primera
elección de **toda** rama del lector.

**`triPin₁_iff_oneShot`** (demostrado): en un estado del lector, `TriPin₁ g x` equivale a que el estado
pinchado, que es un kernel válido, **contenga** el subkernel cortado `restrictPin₁ g x`.
* La inclusión contraria vale siempre (`below_cut_pin`).
* Así, `TriPin₁` significa que **el review tras el pin es de una sola ronda**: quita los nodos que no
  poseen `x` y los enlaces no compatibles con `x`, y nada más. **No hay cascada.**
* `readerVerdictW_iff_of_oneShot`: si en cada estado visitado algún pin sobrevive con un review de una
  ronda, el lector decide.

**Dónde puede actuar el corte** (demostrado):
* `cx_unique_parent`: un nodo con un único padre conserva el enlace con él. Su tabla está dentro de la
  del padre (cláusula de vecinos del kernel), así que la regla de parejas con `x` ya da testigos
  compatibles.
* `cx_unique_son`: lo mismo para el hijo de un único padre.
* **Los enlaces padre–hijo solo pueden cortarse en las fusiones** (nodos con dos padres, §4.2h).

**Lo que queda.** En una fusión `z` con padres `p₁`, `p₂`, se tiene `T(z) ⊆ T(p₁) ∪ T(p₂)`.
* El corte puede quitar `z–p₁` si los testigos compatibles con `x` de `z` pasan todos por `p₂`. Eso es
  legítimo: las continuaciones de `x` por `z` vienen de `p₂`.
* **La condición local que impediría la cascada:** si `w` es compatible con `z` relativo a `x`, algún
  padre `pᵢ` de `z` es compatible con `z` y con `w`. En el paso `s−1`, el testigo del enlace `z–w` tiene
  que ser un padre de `z`.
* Siguiente paso: ver si todo fallo de un solo paso se reduce a esa condición en fusiones, y si la
  historia de la máquina da esa condición en los estados de partida. La tabla de `z` se construyó como
  la unión exacta de las de sus padres (`rowOwners`), y el review posterior es monótono.

### 4.2k Los dos pasos (formales)

**Paso 1: ¿toda cascada se reduce a fusiones?** Sí, en el siguiente sentido (**demostrado**,
`OneShot.lean`):
* `cx_mono`: la compatibilidad es monótona en la tabla del extremo lejano. `cx_to_unique_parent`: la
  compatibilidad **sube** a un padre único. Leído al revés, un corte en un padre baja a sus hijos de
  padre único.
* `UDesc g y a`: se llega de `y` a `a` bajando por padres únicos. `udesc_sub`: al bajar así, las tablas
  solo crecen. `udesc_entry`: la entrada de `y` en el paso de `a` es `a`.
* `tri_below`: si `y` (o `w`) baja por padres únicos hasta el paso `l`, su antepasado es un testigo
  bueno. `tri_above`: un testigo en `l` que baja por padres únicos hasta `y` y hasta `w` es bueno.
* **`fail_is_merge_separated`**: si `TriPin₁` falla en `(y, w, l)`, ni `y` ni `w` bajan por padres
  únicos hasta `l`, y ningún testigo en `l` baja por padres únicos a ambos. Está enunciado por
  contrarrecíproco, sin `Classical`.

**Alcance, con honestidad.**
* En bin, los padres únicos son escasos (§4.2h): los pasos de negación y el primer literal tras `F`.
  Por encima del prefijo fijado, casi todo trío que abarque dos o más pasos cruza una fusión, así que la
  localización reduce poco.
* Por debajo del prefijo todo está forzado, y ahí ya lo cubría `share_below`.
* Lo que sí aporta es la forma del obstáculo: **toda cascada nace en fusiones que separan el paso del
  testigo de los dos extremos.**

**Paso 2: ¿qué da la historia en una fusión `z` con padres `p₁`, `p₂`?**
* Al nacer, `T(z) = (T(p₁) ∪ T(p₂)) ∩ gowners ∪ {z}` (`rowOwners`). Después todo review solo encoge, y en
  todo kernel `T(z) ⊆ T(p₁) ∪ T(p₂)` (cláusula de vecinos).
* Para un enlace `z–w` compatible con `x`, el testigo en el paso `s−1` es un padre `pᵢ`
  (`parent_of_owner`). Lo que evitaría la cascada es que ese `pᵢ` sea compatible con `x` con `z` y con
  `w`.
* Escribiendo `Bᵢ = T(z) ∩ T(pᵢ) ∩ T(x)` para la rama `i` de la sección de `x`:
  * `Cx(z, pᵢ)` equivale a que `Bᵢ` tenga entrada en cada paso;
  * `Cx(w, pᵢ)` pide lo mismo para `T(w) ∩ T(pᵢ) ∩ T(x)`.
* **No está demostrado.** La unión al nacer es exacta, pero el review posterior encoge `T(z)`, `T(pᵢ)` y
  `T(w)` por separado, y nada de lo demostrado liga lo que quita en `T(z)` con la rama de la que venía.
* **El lema que falta** es una afirmación sobre el review en fusiones: **lo que el review quita de la
  tabla de una fusión lo quita rama a rama** (llenura de ramas). Es el siguiente objetivo formal.

### 4.2l Llenura de ramas — **formalizada**; exactitud por parejas a lo largo de la máquina — **en parte demostrada** (`BranchFull.lean`)

**Qué es una rama.** Relativo al pin `x`, la rama del padre `p` de `z` es `T(z) ∩ T(p) ∩ T(x)`. Está
llena cuando tiene entrada en cada paso, es decir, `Cx g x nz p`.
* `FullBranch g x`: todo nodo que posee `x` tiene una rama llena.
* `CommonBranch g x`: todo enlace `z–w` compatible con `x` tiene un padre de `z` que es rama llena de
  ambos extremos.
* **Necesarias** (demostrado): `commonBranch_of_triPin₁`, `fullBranch_of_triPin₁`. Son `TriPin₁` un paso
  por debajo del nodo.
* `fullBranch_of_pairExact` (demostrado): la exactitud por parejas (`PairExact`: todo enlace de tabla
  está en un certificado) da ramas llenas. El certificado del enlace `z–x` pasa por un padre y llena
  su rama.

**`PairExact` a lo largo de la máquina** (demostrado):

| operación | ¿conserva `PairExact`? |
|---|---|
| review | **sí** (`pairExact_filterAll_nil`): los enlaces solo desaparecen y los certificados sobreviven |
| `join` / `doJoin` | **sí** (`pairExact_join`): un enlace del join viene de un lado, y su certificado también |
| `addNode` sin ventana saltada | **sí, fusiones incluidas** (`pairExact_addNode`): la unión se toma enlace a enlace, cada enlace nuevo viene de **un** padre, y el certificado por ese padre se extiende por el nodo nuevo |
| filtro por requisito | abierto |
| review tras ventana saltada | abierto (es la antigua `SkipExact`) |

**Lectura.**
* Las fusiones **no** rompen la exactitud por parejas: una pareja nunca necesita dos ramas.
* Lo que queda para `PairExact` son exactamente **las dos operaciones que imponen la fórmula**: los
  requisitos (literal ↔ variable) y la ventana prohibida `000` (la cláusula).
* Es el mismo sitio donde estaban `HardStepExact` y `SkipExact` en la ruta original de la solidez: las
  dos líneas de trabajo convergen.

**Lo que `PairExact` no da.** `CommonBranch` para parejas `z–w` relativas a `x` necesita un certificado
por `x`, `z` y `w` a la vez (la versión relativa, `CertLink [x]`). Las fusiones sí afectan a esa versión
de tres nodos (§4.2g). El siguiente paso es la versión relativa de estos mismos lemas: ver si
`addNode` conserva «todo enlace compatible con `x` está en un certificado por `x`», usando que cada
enlace nuevo viene de un solo padre.

### 4.2m Versión relativa a `x` — **formalizada**, conservada sin fusiones (`BranchRel.lean`)

**`PairExactRel g x`**: todo enlace `y–w` compatible con `x` está, junto con `x`, en un certificado. Es
`CertLink` para la clique `[x]`. **`PairExactRelAll`**: para todo nodo vivo `x`.

**Demostrado:**
* `triPin₁_of_pairExactRel` (y por tanto `commonBranch_of_pairExactRel`): el testigo en cada paso es el
  nodo del certificado, y sus enlaces son compatibles por el mismo certificado (`cx_of_cert3`).
* `pairExactRelAll_filterAll_nil`: **el review la conserva**.
* `pairExactRelAll_addNode`: **`addNode` la conserva cuando ningún nodo nuevo fusiona**, es decir, cuando
  cada nodo nuevo tiene un solo padre.
  * Cada nodo del estado nuevo tiene una **sombra** en el anterior (`sh`): él mismo si es viejo, su padre
    si es nuevo.
  * Las entradas por debajo del paso nuevo pasan a la sombra (`sh_entry`), y los enlaces también
    (`sh_link`).
  * El certificado por las sombras se extiende por los nodos nuevos (`sh_extend`).

**Dónde puede romperse, con precisión.** En las fusiones (dos padres) y en `join`:
* La versión por parejas sobrevive porque un enlace viene de **un** lado.
* La relativa necesita testigos en **cada** paso, y en una unión esos testigos pueden venir de lados
  distintos en pasos distintos.
* Es exactamente el mecanismo de mezcla de §4.2g. Con los lemas de sombra, la prueba de `addNode` falla
  en un único punto: `sh_entry` para un nodo nuevo con dos padres, donde una entrada viene de un padre u
  otro según el paso.

**Siguiente, dentro del diseño actual.** En una fusión `z = (d, a, b)`, los dos padres `(a, b, c₁)` y
`(a, b, c₂)` solo difieren en el paso `s−3`. Un certificado relativo a `x` que pasa por `z` elige un
`cᵢ`, y las entradas de `z` que dependen de esa elección están en el paso `s−3` o las fijan los
requisitos que miran allí. Queda ver si `PairExactRel` en el estado anterior, aplicada a cada padre, más
la estructura del paso `s−3`, basta para reconstruir un certificado a través de uno de ellos.

### 4.2n El caso de la fusión — **reducido a una condición local** (`BranchRel.lean`)

**Demostrado:**
* `ShOK g d forb q q̂`: `q̂` es una sombra válida de `q`. Es el propio `q` si ya existía, o **alguno** de
  sus padres si es nuevo.
* `cert_of_shadows`: si las sombras de `x`, `y` y `w` forman un enlace compatible con `x̂` en el estado
  anterior, el certificado por las sombras se extiende a uno por `x`, `y` y `w` en el estado nuevo.
* **`ShadowChoice`**, la condición local: para todo enlace compatible del estado nuevo se pueden elegir
  sombras así.
* `pairExactRelAll_addNode_of_choice`: con `ShadowChoice`, `addNode` conserva `PairExactRelAll`, fusiones
  incluidas.
* `shadowChoice_of_single`: sin fusiones, `ShadowChoice` se cumple siempre.

**Lo que queda.**
* Solo los tríos que contienen un nodo nuevo `z` con dos padres `p₁ = (a,b,c₁)` y `p₂ = (a,b,c₂)`. Entre
  `x`, `y` y `w` hay como mucho un nodo nuevo distinto, porque dos nodos nuevos distintos no se poseen.
* Hay que elegir un `pᵢ` tal que el enlace, con `z` sustituido por `pᵢ`, sea compatible en el estado
  anterior. El testigo en el paso `s−1` ya es un padre `pⱼ` (sus entradas en ese paso son sus padres),
  pero los testigos de otros pasos pueden estar en la rama contraria.

**¿Sale de `PairExactRelAll` en el estado anterior?** No en abstracto (deducido, modelo de
restricciones, no una instancia de la máquina).
* Basta que en un paso `l₁` los nodos que poseen a `x` y a `w` solo sean compatibles con `c₂`, y en otro
  paso `l₂` solo con `c₁`.
* Si el par `x–w` tuviera un certificado **por la ventana `(a,b)`**, ese certificado fijaría la misma
  rama en todos los pasos y no habría mezcla. Pero la exactitud por parejas del estado anterior solo
  garantiza **algún** certificado por `x` y `w`, que puede pasar por otra ventana `(a′,b′)`.
* La obligación exacta es, por tanto: **si `x` y `w` son compatibles con la ventana `(a,b)` en cada
  paso, lo son con una misma rama `cᵢ`.** Es una afirmación sobre el paso `s−3`, lo que la fusión olvida.

**Siguiente**: ver si la estructura bin la da. En los pasos de cláusula, `cᵢ` es un bit de literal fijado
por un requisito sobre una variable `x_u`, y la tabla recuerda `x_u` en la sección de variables. Una
mezcla necesitaría un nodo compatible con `x`, `w` y `x_u = v₁` en un paso, y otro compatible con `x`, `w`
y `x_u = v₂` en otro. Hay que ver si el filtro por requisito sobre `x_u`, aplicado cuando se creó el
literal `cᵢ`, lo impide.

### 4.2o ¿Fija el requisito la rama? — **no; la mezcla nace en el `join`** (deducido del código) + `JoinChoice` (demostrado)

**Cómo se unen las historias** (`PureDriver.sendTo`, `insertPure`):
* La línea tiene un estado por nodo de mapa del paso actual.
* En el paso `s−3`, los literales `c₁` y `c₂` son **estados distintos**. En cada uno, el requisito ha
  fijado `x_u`, así que las tablas de ese estado solo ven `x_u = vᵢ`.
* En el paso `s−2`, ambos estados se envían a la misma clave `b` y se unen con `doJoin`.
* En el estado unido, los nodos nuevos de cada rama (`(b, cᵢ, ·)` y después `pᵢ = (a, b, cᵢ)`) conservan
  tablas de su rama. Pero los nodos **anteriores** a `s−3`, comunes a ambas historias, tienen como tabla
  la **unión** de las dos (`mergeNode`).
* La fusión de ventana en el paso `s` solo hace visible una mezcla que ya creó el `join` en `s−2`.

**Qué fija el requisito y qué no.**
* Fija la rama de los testigos que llevan el valor explícitamente: en el paso de `x_u` (su índice es el
  valor) y en `s−3` (su id es `cᵢ`, por `gparentId_of_owner`). También en `s−1` y `s−2` (son los padres y
  abuelos de la rama).
* En los demás pasos, un nodo viejo `r` puede poseer a `x` por la historia 1 y a `p₂` por la historia 2.
  En el estado unido, su tabla no recuerda qué historia respaldaba cada entrada.
* Por tanto **el requisito no impide la mezcla**. La raíz es el `join` de historias.

**Demostrado** (`BranchRel.lean`):
* `JoinChoice g₁ g₂`: todo enlace compatible con `x` del `join` ya lo es en uno de los dos lados.
* `pairExactRelAll_join`, `pairExactRelAll_doJoin`: con `JoinChoice`, el `join` conserva
  `PairExactRelAll`.

**Estado de la ruta por exactitud relativa** (`PairExactRelAll`, que da `TriPin₁`):

| operación | ¿conserva? |
|---|---|
| review | sí (demostrado) |
| `addNode` sin fusión | sí (demostrado) |
| `addNode` con fusión | sí, si `ShadowChoice` (demostrado; la condición, abierta) |
| `join` | sí, si `JoinChoice` (demostrado; la condición, abierta) |
| filtro por requisito | abierto: necesita exactitud relativa a **dos** nodos (el `x` y el requerido), así que la jerarquía sube, como con los pins |
| review tras ventana saltada | abierto |

Las dos condiciones abiertas son del mismo tipo: **coherencia de rama en una unión**. Los testigos
compatibles de pasos distintos tienen que poder elegirse de una misma historia.

### 4.2p El filtro por requisito — **es un pin; reducido a `FilterChoice`** (`ReqFilter.lean`)

En bin un nodo tiene como mucho un requisito (`reqOf_length_le_one`): un nodo de mapa `req` en un paso de
variable. `filterAll g [req]` deja en ese paso solo los nodos de camino cuyo nodo de mapa es `req`, y
revisa. **Es un pin sobre un nodo de mapa.**

**Demostrado:**
* `req_id`: tras el filtro, una entrada viva en el paso del requisito nombra `req`.
* `FilterChoice g req`: todo enlace superviviente era compatible, antes del filtro, relativo a **uno** de
  los nodos de camino de `req`.
* `pairExact_filter_of_choice`: la exactitud relativa previa (`PairExactRelAll g`) junto con
  `FilterChoice` dan la exactitud por parejas después (`PairExact`). El certificado por ese nodo cumple
  el requisito y sobrevive (`ChainSound_filterAll`).
* `filterChoice_of_unique`: si `req` tiene **un único** nodo de camino vivo `x` tras el filtro, se cumple
  `FilterChoice`.
  * Todo nodo lo posee, porque es la única entrada de su paso.
  * Los testigos de cada enlace superviviente también lo poseen, así que por simetría están en la tabla
    de `x` en el estado anterior.
  * Es el mismo argumento que `below_cut_pin` en el lector.

**Cuándo hay unicidad.** Un nodo de camino en el paso de variable `2u+1` o `2u+2` lleva en su ventana
el valor de la variable anterior `a_{u−1}`, así que `req` tiene en general **dos** nodos de camino. Hay
unicidad:
* para `u = 0`, cuya ventana llega a la raíz;
* cuando el estado ya tiene `a_{u−1}` fijado.

En otro caso el filtro es un **pin disyuntivo**: otra unión.

**Lectura del conjunto.**
* El filtro baja la jerarquía un orden: de exactitud relativa a exactitud por parejas. Para conservar
  la exactitud relativa haría falta exactitud relativa a **dos** nodos antes, igual que con los pins
  del lector.
* Las tres uniones de la máquina reciben el mismo tratamiento:
  * fusión de ventana → `ShadowChoice`;
  * `join` de historias → `JoinChoice`;
  * pin disyuntivo del requisito → `FilterChoice`.
* Todas dicen lo mismo: **los testigos compatibles de pasos distintos pueden elegirse de una misma
  rama.**
* Con un único nodo de camino o un único padre, las tres están demostradas. El núcleo abierto es esa
  coherencia de rama en las uniones de dos elementos, que en bin siempre difieren en un solo paso de
  ventana: el olvidado.

### 4.2q Ataque a la coherencia de rama — **no demostrada; una palanca demostrada** (`HellyTwo.lean`)

**Forma común de las tres condiciones.** Se unen dos ramas que solo difieren en el paso olvidado `f`.
* En la rama `i`, todas las tablas ven en `f` solo nodos `cᵢ`: en el estado de clave `cᵢ` no hay otros
  nodos en ese paso, y la validez obliga a tener entrada ahí.
* Tras la unión, la tabla de un nodo antiguo es `T₁ ∪ T₂`.
* La regla de parejas en `f` obliga a que dos nodos enlazados compartan algún `cᵢ`, pero la tabla no
  registra **qué rama respalda cada pertenencia**.

**La palanca de bin: Helly con número 2** (demostrado).
* `helly2`: en un dominio de dos valores, tres conjuntos que se cortan dos a dos tienen un punto común.
* `share3_of_two`: en un paso con a lo sumo dos nodos de camino vivos, tres nodos que se poseen dos a dos
  comparten entrada. La regla de parejas basta para el testigo de un trío. Depende solo de `propext`.

**Hasta dónde llega** (deducido):
* **A las ramas.** Las dos ramas son un dominio de dos valores. Cada pertenencia que necesita la
  condición está respaldada por un subconjunto no vacío de `{1, 2}`. Por Helly-2, basta que **cada dos**
  pertenencias compartan rama para que haya una rama común a todas, es decir, la coherencia. La
  coherencia de rama se reduce así a **coherencia por parejas de pertenencias**.
* **Por qué no cierra.**
  * La coherencia por parejas tampoco se lee de las tablas, porque no llevan la rama.
  * Los testigos se eligen paso a paso, y eso añade un cuantificador que Helly no absorbe.
  * `share3_of_two` da solo la primera capa de `TriPin` (entrada común), no la segunda (compatibilidad de
    los enlaces del testigo).
  * Con ventanas de tres pasos, un paso puede tener hasta cuatro nodos de camino por encima del prefijo
    fijado, así que la hipótesis de «dos vivos» solo se da donde la ventana ya está determinada.

**Diagnóstico honesto.** Tras reducir todo a la coherencia de rama en uniones de dos, no he encontrado
una derivación a partir de las invariantes locales de la máquina. Lo que falta es información que las
tablas no guardan tras una unión: qué rama respalda cada pertenencia. Cualquier prueba tendrá que
obtenerla de forma global, a partir de cómo se construyeron las dos ramas antes de unirse (desde el paso
`f` hasta la unión en `f+1` o `f+3`), no del estado unido.

### 4.2r Las dos líneas: historia de una unión y ventana saltada (`CertMachine.lean`)

**A. Historia de una unión.**

**Lo que muestra el código.** Los dos lados de un `join` en el paso `f+1` descienden del **mismo**
estado anterior `J_e` (paso `f−1`) por pins complementarios sobre la variable del literal:
`Sᵢ = up (filterAll J_e [x_u = vᵢ]) cᵢ`. Sobre los nodos comunes, la unión de los dos pins de un estado
exacto reconstruye ese estado. Ahí la mezcla desaparece: un certificado de `J_e` lleva su propio valor
de `x_u`, y ese valor elige la rama.

**`CertClique` es monótono, y con él se puede seguir la máquina sin el sándwich del lector.**
Demostrado:
* **El filtro por requisito lo conserva** si el nodo requerido tiene un único nodo de camino vivo
  (`certClique_filter_unique`). Todo nodo lo posee tras el filtro, así que una clique `Q` con testigos
  da `x :: Q` con testigos antes, y su certificado cumple el requisito.
* **`addNode` sin fusiones lo conserva** (`certClique_addNode_old`, `certClique_addNode_single`):
  * las cliques de nodos viejos extienden su certificado por su propio último nodo;
  * una clique con un nodo nuevo `z` pasa a su único padre, porque los testigos que poseen `z` poseen a
    ese padre.
* El review lo conserva (`certClique_filterAll_nil`, ya demostrado).

**Idea para fusiones y `join` a la vez** (propuesta, sin formalizar). Enrutar el certificado del
ancestro común por las claves `cᵢ → b → a → d`, eligiendo `i` por su propio `x_u`. La rama la decide el
certificado, así que da igual de qué rama viniera cada testigo. Hace falta:
1. que la clique posterior, con los nodos requeridos por `b`, `a` y `d` añadidos, tenga testigos en el
   ancestro;
2. que esos requisitos no sean disyuntivos.

El obstáculo restante es el punto 2. Un nodo requerido en un paso de variable tiene dos nodos de
camino, según la variable anterior, así que la disyunción vuelve a nivel de ventana.

**B. Ventana saltada** (antigua `SkipExact`). Demostrado:
* `SkipChoice`: una clique de nodos viejos con testigos tras la fila está en un certificado previo cuya
  extensión no está prohibida. `certThrough_addNode_skip`: con esa condición, la fila con ventana
  saltada conserva los certificados, y el review posterior también.
* `skipChoice_of_parent`: basta, junto con `CertClique` previo, que la clique tenga testigos **a través
  de un padre de un nodo permitido de la fila**.

En bin, en el tercer literal de una cláusula con valor `0`, eso es un padre con `(L1, L2) ≠ (0, 0)`: una
**disyunción de tres ventanas**, la propia cláusula.

**Conclusión de las dos líneas.**
* Todo lo que no es una unión está demostrado para `CertClique`: review, filtro con un único nodo de
  camino y `addNode` sin fusión.
* Lo que queda son disyunciones, cuatro en total: la fusión de ventana (dos padres), el `join` de
  historias, el requisito con dos ventanas y la cláusula (tres ventanas).
* En las tres primeras, la rama la fija el valor de una variable que el certificado ya lleva. La
  propuesta de enrutado explota eso.
* La cuarta, la cláusula, es la disyunción propia de la fórmula.

### 4.2s Enrutado formalizado: `MapCert` — **demostrado** (`CertRoute.lean`, `MapCert.lean`)

**Idea.** Tres de las cuatro uniones son disyunciones sobre **nodos de camino del mismo nodo de mapa**:
* un requisito nombra un nodo de mapa con un nodo de camino por valor de la variable anterior;
* los padres de una fusión comparten nodos de mapa y difieren en el paso olvidado;
* los dos lados de un `join` son pins complementarios de un nodo de mapa.

Una clique de nodos de camino no puede decir «uno de estos», pero un nodo de mapa sí. **Es el
certificado el que elige la ventana.**

**Demostrado:**
* `certClique_join_pins` / `mapCert_join_pins`: **la unión de dos pins complementarios de un estado
  exacto es exacta.** El certificado de la clique en el estado anterior pasa, en el paso fijado, por
  `r₁` o por `r₂`, sobrevive a ese pin y está en la unión. No importa de qué lado viniera cada testigo.
* **`MapCert g`**: si `Q` es clique y en cada paso un nodo vivo posee `Q` y **algún** nodo de camino de
  cada nodo de mapa de `R`, hay un certificado por `Q` y por los nodos de mapa de `R`. Con `R = []` es
  `CertClique` (`certClique_of_mapCert`).
* `mapCert_filterAll_nil`: el review lo conserva.
* **`mapCert_filter`: todo filtro por requisito lo conserva, con cualquier número de ventanas.** Tras el
  filtro todo nodo posee algún nodo de camino del nodo requerido, así que el requisito es una
  restricción de mapa más. **`FilterChoice` deja de ser una obligación.**
* **`mapCert_addNode`: `addNode` lo conserva, fusiones incluidas** (sin ventana saltada, desde el paso
  2).
  * Una clique con un nodo nuevo `z = (d, a, b)` pasa a la clique vieja con las restricciones de mapa
    `a` (un paso abajo) y `b` (dos abajo).
  * Un testigo que posee `z` posee un padre `(a, b, ·)` y, por la regla de parejas y `PMP`, un nodo de
    camino de `b`.
  * El certificado por `a` y `b` termina en **algún** padre de `z`, el que dé su propia ventana, y se
    extiende por `z`.
  * **`ShadowChoice` deja de ser una obligación.**

**Lo que queda para `MapCert` a lo largo de la máquina:**
1. **El `join` de la máquina.** Une estados de la misma clave que vienen de claves anteriores
   distintas, y no es literalmente la unión de dos pins de un mismo estado: entre el pin y el `join`
   median `addNode` y otro filtro. Hace falta un lema de «cobertura por enrutado»: si los lados
   descienden de un estado común con `MapCert` por operaciones que conservan certificados y cada
   certificado del estado común entra en uno de los lados, el `join` hereda `MapCert`.
   `mapCert_join_pins` es el caso base.
2. **La ventana saltada: la cláusula** (`SkipChoice`, §4.2r).
3. **Hipótesis de contexto**: que los estados filtrados sean kernels (validez), y los pasos 0 y 1.

**Medida `v4_c12`** (lanzada antes, `--cap 100`, 40 min por instancia): solo terminaron 3 de 15, con 1
estado o 3 estados y 0 fallos. No es informativa: el modelo Lean en listas no llega.

### 4.2t Cobertura por enrutado para el `join` real — **herramienta demostrada; arquitectura fijada** (`PrefixCarry.lean`)

**El obstáculo de «pureza».** Un certificado de la unión de dos estados no es en general un certificado
de uno de ellos: sus pertenencias pueden venir de tablas de lados distintos. Así que el certificado que
da `MapCert` de un ancestro no se puede meter con `ChainSound_upFiltering` en el estado concreto de una
clave. Pero **semánticamente** es una solución parcial:
* sus nodos de literal solo poseen, en el paso de su variable, el valor requerido (la tabla nació
  filtrada);
* sus ventanas existen, así que no están prohibidas.

Y la máquina conserva toda solución parcial en el estado de su propia clave. Eso es lo que falta
enchufar.

**Demostrado:**
* `PreSat φ a T`: las ventanas de la asignación antes de `T` están permitidas, es decir, las cláusulas
  cerradas antes de `T` se satisfacen. `preSat_of_sat`.
* `chainSound_along_pre`, `isValid_along_pre`, `advance_target_pre`, `sons_fold_establish_pre`,
  `Carries_pureAdvance_pre`, `run_ok_pre`: la cadena de `pureRun_carries` con `PreSat` en lugar de `Sat`.
  `Sat` solo entraba por `pidOfAssign_not_prohibited`.
* **`cert_of_prefix`**: en cada paso `t < T`, la línea tiene, en el nodo de mapa de la asignación, un
  estado que contiene su cadena como certificado.

**Arquitectura resultante para `MapCert` a lo largo de la máquina** (por formalizar):
1. **Decodificación de prefijos** (L1): una cadena de un estado de la máquina, o de la unión de estados
   de una línea, decodifica a una asignación con `PreSat` cuya selección coincide con la cadena. Hay
   que generalizar `NoDeadEnd.selOfAssign_decode`, hoy solo para el estado final.
2. **Inducción sobre la línea unida** `U_t`. Una clique con testigos en el estado de clave `d` en `t+1`
   tiene testigos, con el requisito de `d` y las restricciones de ventana, en `U_t`. `MapCert(U_t)` da
   una cadena, L1 la hace solución parcial, y `cert_of_prefix` la lleva al estado de clave `d`.
3. **Los pasos de cláusula** (tercer literal). Allí la solución parcial puede morir, con ventana `000`,
   y hay que elegir otra: es `SkipChoice`, la disyunción de la cláusula.

Si 1 y 2 salen, **toda la ruta del lector queda reducida a los pasos de cláusula**: lo único abierto
sería la disyunción propia de la fórmula.

### 4.2u Pasos 1 y 2 — **demostrados**; el lector queda reducido a la cláusula (`PrefixDecode.lean`, `LineSem.lean`)

**Paso 1** (`decode_prefix`): una cadena de cualquier estado de la máquina es una solución parcial.
* La asignación decodificada nombra en cada paso el nodo de mapa de la cadena
  (`selOfAssign_decode_pre`), y su ventana es el nodo de camino de la cadena (`pidOfAssign_decode_pre`).
* Sus ventanas por debajo del paso actual están permitidas (`preSat_decode`).

**Paso 2** (`LineSem`): se sigue la línea de la máquina entera, entrada a entrada, sin construir un
estado unión.
* `Owns n r q`: en algún estado de la línea `n`, la tabla de `r` contiene `q`. `LClique` y `LWit` son la
  clique y los testigos para esa relación. **`SemCert n`**: toda clique con testigos en la línea `n` la
  atraviesa una solución parcial (`PreSat`).
* **Orígenes** (`src_pureAdvance`): todo nodo y toda entrada de un estado de la línea `n+1` viene de
  `upFiltering` de un estado de la línea `n`, pasando por `sendTo`, `insertPure` y `doJoin`.
* **Traspaso** (`upF_old`, `upF_new`, `upF_owner_new`, `row_owner_window`, `filt_owns_req`, `owns_top`):
  * una entrada vieja ya estaba antes;
  * un nodo que posee un nodo nuevo `z` poseía, antes, un padre de `z`, un nodo del mapa del abuelo de
    `z` y el requisito de `z`.
* **Nodos del último paso** (`top_node`, `top_owns_self`, `top_entry_key`): en su propio paso solo se
  poseen a sí mismos, no están prohibidos y llevan la clave del estado. **El testigo del último paso
  fija la clave y la ventana.**
* **Extensión semántica** (`extend_to`, `selOfAssign_of_req`, `selOfAssign_congr`, `chain_eq_pid`): una
  solución parcial por la parte vieja se extiende al último paso. En una variable positiva el valor es
  libre; en el resto lo fija el requisito.
* **Inducción** (`semCert_zero`, `semCert_succ`, `semCert_all`).
  * En cada paso se trata la clique con miembro en el último paso y la que no lo tiene.
  * La segunda solo necesita hipótesis cuando ese paso es el **tercer literal de una cláusula**: la
    extensión de la solución parcial puede caer en la ventana `000`.
  * Esa hipótesis es **`ClauseChoice`**.
* **Conclusión** (`mapCert_start`, `readerVerdictW_iff_of_clauseChoice`): `SemCert` en la línea final da
  `MapCert` en el estado de partida revisado. De ahí salen `CertClique`, `CertLink` y `CliqueTri`, y el
  lector decide.

> **`readerVerdictW φ = true ↔ Satisfiable φ`, suponiendo solo `ClauseChoice` en el tercer literal de
> cada cláusula.**

`ClauseChoice n`: si el paso `n+1` es el tercer literal de una cláusula, toda clique de la línea `n+1`
sin miembro en ese paso, y con testigos, la atraviesa una solución parcial. Es la disyunción propia de
la fórmula, y es lo único que queda.

### 4.2v `ClauseChoice`: el diseño de las cláusulas y la versión en tablas — **reducido** (`LineSem.lean`)

**El diseño** (v193, `CnfMapBin`):
* Cada cláusula `j` son tres pasos seguidos, `L1`, `L2` y `L3`, con 2 nodos por paso. El nodo `Lp = b`
  requiere que el literal `p` valga `b`, así que el bit de cada paso de cláusula es el valor de un
  literal, fijado por una variable anterior.
* **La ventana mide lo mismo que la cláusula.** En `L3`, el nodo de camino `(L3, L2, L1)` es la
  asignación completa de la cláusula.
* La disyunción no está en las tablas, sino en la **existencia de nodos**: la ventana `000` no se crea.
  En la clave `L3 = 0` el `UP` salta esa ventana y revisa. En `L3 = 1` no salta nada.
* La intención del diseño es que cada paso tenga 2 nodos, para que el Helly de un paso sea el de dos
  elementos (`HellyTwo.share3_of_two`).

**Qué pide `ClauseChoice`.**
* Ninguna solución de 3-SAT tiene los tres literales de una cláusula a 0. Pero la solución parcial que da
  la hipótesis de inducción solo está comprobada hasta `L2`: con `L1 = L2 = 0` sigue siendo válida ahí, y si
  la variable del tercer literal (ya asignada) lo pone a 0, necesitaría la ventana `000`, que la máquina no
  crea. Esa solución parcial no se extiende; hay que encontrar otra dentro de la clique.
* Cada testigo de un paso inferior posee algún nodo superior permitido: todo nodo de un estado de
  `L3` tiene entrada en ese paso (en `L3 = 0` por el review; en `L3 = 1` porque su padre tiene hijo).
* Pero testigos de pasos distintos pueden apoyarse en **literales distintos**. Helly-2 actúa dentro
  de un paso, no entre pasos.
* A diferencia de las uniones de §4.2g–s, aquí la rama no es el valor de una variable, sino **cuál de
  los tres literales es cierto**: la disyunción de la fórmula.

**Demostrado:**
* `semConcl_of_top`: una clique con miembro en el paso nuevo la atraviesa una solución parcial, sin
  hipótesis (el caso ya demostrado dentro de `semCert_succ`, extraído).
* **`ClauseLocal n`**: en el tercer literal, toda clique con testigos y sin miembro en ese paso se
  amplía con un nodo superior (una ventana permitida de la cláusula) conservando los testigos. Es
  **solo de tablas**.
* `clauseChoice_of_local`: `ClauseLocal ⇒ ClauseChoice`.
* **`readerVerdictW_iff_of_clauseLocal`**: el lector decide `φ` suponiendo solo `ClauseLocal` en cada
  tercer literal.

**Lo que dice `ClauseLocal` en términos del diseño.** La disyunción vive en la existencia de los nodos
superiores, y `ClauseLocal` pide que los testigos de una clique puedan elegirse **a través de uno de
esos nodos**. El candidato natural es el testigo superior `w`, que ya posee la clique. Falta que en cada
paso inferior haya un nodo que posea la clique **y** `w`. Es una condición de un solo paso de la máquina
(el `UP` del tercer literal: `addNode` más el review de la ventana saltada) sobre los estados de la línea.

### 4.2w La cláusula por claves: los testigos eligen un literal cierto — **reducido** (`ClauseKey.lean`)

**Cómo trabaja la máquina en `L3`** (paso `n+1`; fuentes de la línea `n`: `A` con clave `L2 = 0`, `B` con
`L2 = 1`). Cuatro piezas, cada una fija un **literal cierto** que poseen todos sus nodos:
* `(A, 1)` y `(B, 1)`: el filtro de requisito deja solo el valor de la variable que hace cierto el tercer
  literal. No se salta nada. Literal: `⟨n+1, 1⟩`.
* `(B, 0)`: toda ventana `(·, 1, 0)` está permitida. No se salta nada. Literal: `⟨n, 1⟩` (la clave de `B`).
* `(A, 0)`: se salta `000`; el review deja solo lo que pasa por `L1 = 1`, la ventana `(1, 0, 0)`.
  Literal: `⟨n-1, 1⟩`.

**Demostrado:**
* `notProh_of_true`: una solución parcial que pasa por un literal cierto (`trueLits n`) tiene ventana
  permitida en `L3`.
* `semConcl_low`: el paso de `semCert_succ` sin la cláusula: basta con que toda asignación que respete las
  restricciones de mapa tenga ventana permitida.
* **`ClauseKey n`**: una clique con testigos admite un literal cierto `t` que los testigos poseen también
  (`LWit (n+1) Q (t :: R)`). `clauseChoice_of_key` y **`readerVerdictW_iff_of_clauseKey`**.

**Actualización.** `ClauseKey` se enuncia ahora con los literales como restricciones **por debajo** de
`L3` (`keyOpts`: `L2 = 1`, `L1 = 1`, o el valor de variable que hace cierto el tercer literal), poseídas
por los testigos en la línea `n` (`OldWit`); `semConcl_low` admite esas restricciones extra.

**Demostrado: el caso con un nodo en `L2`** (`clauseKey_mid`). Si la clique tiene un nodo `q` en `L2`, su
ventana elige el literal para **todos** los testigos:
* `q` con `L2 = 1`: todo testigo posee `q`;
* `q` con `L1 = 1`: todo testigo posee el padre de `q` (regla de parejas en la fuente, `owns_parent_map`);
* `q` con ventana `00` (`owns_mid00`): en una pieza de clave `0` el único hijo de `q` sería `000`; el `UP`
  lo salta, el review elimina `q` y el corte lo quita de toda tabla. Así que todo testigo que posee `q`
  está en una pieza de clave `1` y posee el valor que hace cierto el tercer literal. Es exactamente el
  review de la ventana saltada.

**Lo que falta.** Cliques sin nodo en `L2` (ni en `L3`). Cada testigo, por separado, posee el literal de su pieza. Falta que testigos de pasos
distintos coincidan en el literal. `ClauseKey` equivale a `ClauseChoice` (la solución, que la máquina
lleva por `PrefixCarry`, da testigos que poseen su literal), así que no es más débil: es la misma
condición dicha con las piezas de la máquina.

**Riesgo detectado (sin verificar).** `Owns` es existencial por hecho: cada entrada puede venir de una
pieza distinta, y la línea `n+2` une las piezas de `L3 = 0` y `L3 = 1` en un solo estado. Escenario:
cláusulas previas `a∧b → ¬x`, `b∧c → ¬y`, `a∧c → ¬z` y la cláusula `x ∨ y ∨ z`; `Q = {a=1, b=1, c=1}`.
Cada pareja de `Q` está en una solución real (con literales ciertos distintos); el testigo superior `w`
de `(A, 0)` posee los tres; toda solución por los tres pone `x = y = z = 0`. Si la sobreaproximación de
las tablas mantiene testigos en todos los pasos (en particular en el `L3` de `a∧b → ¬x`, donde ninguna
solución real da uno), `ClauseChoice` es falso aunque la máquina acierte: el lector repasa el estado tras
cada pin, y ese repaso mata la clique. Entonces el invariante correcto no es `SemCert` para cliques
arbitrarias del estado original, sino algo que lleve el pin (ruta `PrefixTri`, §4.2l).

### 4.2x «Ninguna entrada es inventada» — **formalizado** (`NoInvent.lean`)

La máquina elimina conjuntos enteros que se invalidan antes de llegar a un destino, une en el destino
solo conjuntos válidos, y su `UP` crea un nodo por hoja salvo la ventana que sabe incorrecta. La
afirmación que se sigue: **toda entrada de una tabla es co-ocurrencia en un camino real hasta ese paso.**

* **`NoInvent g n`**: si `r` posee `q` en `g`, hay una solución parcial (`PreSat` hasta `n+1`) que pasa
  por los dos.
* **`noInvent_of_semCert`**: en todo estado revisado de la línea, `SemCert` la da. La pareja `{r, q}` es
  clique y la regla de parejas del kernel da sus testigos.
* **`filter_entry_req`**: tras el filtro de requisito, cada entrada `r → q` lleva un tercer nodo (un nodo
  de camino del requisito en las dos tablas). Para llevar la entrada al paso siguiente hace falta una
  solución por los tres. Por eso la forma que se conserva paso a paso es la de cliques con testigos
  (`SemCert`) y la pareja es su primer caso; y en el tercer literal esas restricciones de mapa pueden
  venir de piezas distintas, que es el mismo punto abierto que `ClauseKey`.

### 4.2y La sonda Julia y la regla de los testigos de cláusula — **formalizada** (`ClauseWitness.lean`)

**Sonda** (`julia/improves_bin/test_3sat/probes/clause_mix_probe.jl`, 8 s; la de Lean tarda >1 h). Instancia
`cnf/crafted/clause_mix_sep.cnf` (`a∧b → ¬x`, `b∧c → ¬y`, `a∧c → ¬z`, `x ∨ y ∨ z`, con variables
separadoras), `Q = {a=1, b=1, c=1}`:
* hasta el paso 30, `Q` es clique con testigos en todos los pasos (correcto: aún vale `x = y = z = 0`);
* en el paso 31 (`L3` de `x ∨ y ∨ z`) **falta el testigo en el paso 21**, por entradas y en cada estado;
  sigue faltando en el estado final.

El paso 21 es el `L2` de `a∧b → ¬x`. Un nodo ahí que posea `a=1` y `b=1` tiene ventana `(¬a, ¬b) = (0, 0)`:
su identidad lleva `a = b = 1` (y `x = 0` por su único hijo). Para ser testigo tendría que poseer `c = 1`
en alguna pieza, y el `L3` de `x ∨ y ∨ z` no lo deja en ninguna. **La mezcla de piezas la mata un testigo de
un paso de cláusula, cuya ventana ve a la vez dos miembros de la clique.**

**Formalizado:**
* `req_in_table`, `parent_req_in_table`: un nodo posee, en el paso del requisito propio y en el del
  requisito de su padre, solo el nodo de camino que su ventana nombra (`ReqFiltered` + regla de parejas +
  enlace de padre).
* `owns_window_req`: lo mismo en la línea (entradas de cualquier estado).
* **`witness_fixes_clique`**: un testigo en `L_p` fija el valor de todo miembro de la clique en las
  variables de los literales `p` y `p-1`.

**Dos casos cerrados con la regla** (opciones de literal ampliadas con los valores de variable que hacen
cierto cada literal, `keyOpts`):
* `clauseKey_trueVar`: la clique contiene un valor que hace cierto un literal de la cláusula; todos los
  testigos lo poseen.
* `clauseKey_allFalse`: la clique contiene los tres valores que hacen falsos los literales; el testigo de
  `L2` tendría ventana `00` (`owns_window_req`), no cabe en una pieza de clave `0` (`no00_key0`) y en una de
  clave `1` el filtro no deja el valor falso del tercer literal: no hay testigo, caso vacío.

**Composición** (`clauseKey_of_ext`): si en la línea del `L3` toda clique con testigos se puede ampliar con
un nodo en cualquier paso de variable conservando sus testigos (`ExtAt`), se amplía con las tres variables
de la cláusula; un valor cierto da `clauseKey_trueVar`, los tres falsos `clauseKey_allFalse`. Así
**`ExtAt ⇒ ClauseKey ⇒ el lector decide`** (`readerVerdictW_iff_of_ext`).

**Abierto:** `ExtAt` en la línea del `L3`. Es una propiedad de un solo nodo (como la supervivencia del
pin del lector), pero su prueba es la composición global: en el ejemplo, el testigo que decide está en
otra cláusula. En el ejemplo actúa el testigo de **otra**
cláusula anterior, así que la composición es global (cadenas de cláusulas), no local al `L3`.

### 4.2z Sonda `ExtAt` en Julia: la versión por entradas es falsa, la versión por estado vale

Sonda `julia/improves_bin/test_3sat/probes/extat_probe.jl` (cliques de tamaño 1–3 con testigos, en cada `L3`
y en la línea final; `--state` = dentro de un solo estado) y `trace_clique.jl` (traza de una clique).
Corpus: `cnf/crafted`, `cnf/random_small` y los ejemplos pequeños de Julia.

* **Por entradas de la línea (como `LineSem.Owns`)**: 16 cliques de tamaño 3 con testigos y **sin solución**, y
  64 fallos de `ExtAt`, todos en `rand3sat_v8_c10`, paso 38 (`L3` de la cláusula 7). Ejemplo:
  `Q = {v1=0, v3=0, (v4=1, v7=1)}`: la cláusula 1 (`¬4 ∨ ¬7 ∨ ¬2`) fuerza `v2 = 0` y la 7 (`3 ∨ 1 ∨ 2`) pide
  `v2 = 1`. **`SemCert`/`ClauseChoice`/`ClauseKey`/`ExtAt` tal como están enunciados (por entradas) son
  falsos.**
* **Por estado**: 0 fallos semánticos y 0 fallos de `ExtAt` en todo el corpus (1,3 M cliques, 13 M
  ampliaciones). La traza muestra que la clique del ejemplo **no es clique en ningún estado** del paso 38, y
  en el paso 39, tras el join, le falta el testigo del paso nuevo (39): el testigo superior vive en una sola
  pieza, que viene de un solo estado de origen, y no posee la mezcla.
* Los candidatos descartados tienen siempre testigos por parejas con cada miembro; les falta el testigo del
  trío, casi siempre en un paso `L2`.

**Consecuencia**: la máquina no se equivoca; el invariante tiene que ser **por estado**, no por entradas de la
línea. Regla observada para el join: **el testigo del paso nuevo fija la pieza (y el estado de origen)**.
Los módulos `LineSem`/`ClauseKey`/`ClauseWitness` siguen siendo correctos como implicaciones, pero su
hipótesis (por entradas) no se cumple; hay que reenunciar `SemCert` por estado.

### 4.2α La corrección: por estado, y el testigo del paso nuevo fija el origen (`StateGrow.lean`)

* **`GrowState g`**: dentro del estado `g`, toda clique con testigos gana un nodo en cualquier paso sin perder
  testigos (el `ExtAt` por estado, 0 fallos en la sonda).
* `certClique_of_grow`: creciendo hasta tener un nodo en cada paso sale un certificado; **`readerVerdictW_iff_of_grow`**:
  el lector decide `φ` si los estados de partida crecen. Sustituye a la ruta por entradas (`LineSem`),
  cuya hipótesis es falsa.
* **La regla del join, demostrada**: `row_parent_key` (un nodo del paso nuevo de una pieza tiene por padre la
  clave de su origen) y **`top_one_source`**: en un estado de la línea `n+1`, **toda** entrada de un nodo del
  paso nuevo viene del mismo estado de origen (claves únicas en la línea). `clique_in_source`: una clique que
  posee un nodo del paso nuevo está entera en el origen filtrado, y cada miembro posee allí un padre suyo.

**Abierto:** `GrowState` en los estados de la máquina. La regla del join fija el origen de las entradas del nodo
superior; falta llevar a ese origen los testigos de los demás pasos (pueden venir de otras piezas del join).

### 4.2β El lector decide con `PieceLocal` como única hipótesis (`PieceJoin`, `StatePiece`, `StateLine`)

**Sonda** `piecelocal_probe.jl` (reconstruye las piezas de cada join con `do_up_filtering!`): 3,5 M cliques de
tamaño 1–3 con testigos en estados unidos; **todas** son clique con testigos dentro de una sola pieza.

**Demostrado, estado por estado:**
* `piece_grown`: toda pieza válida crece (`Grown`) en el estado de su destino: el join solo añade.
* `mapCert_join`: con `PieceLocal`, `MapCert` de las piezas da `MapCert` del estado unido.
* `mapCert_piece`: una pieza conserva `MapCert`: filtro de requisito, `addNode`, y **la ventana saltada**
  (`mapCert_skip`). Dentro de una pieza la cláusula es uniforme: la ventana `000` solo se salta en la clave
  `L3 = 0` desde el estado `L2 = 0`; todo nodo de la pieza revisada posee un nodo del paso nuevo, cuya ventana
  está permitida, así que posee `L1 = 1`; un certificado por `L1 = 1` extiende por una ventana permitida
  (`MapCert.certR_addNode_sub`, generalización de `mapCert_addNode` a un subestado cuyos nodos poseen `E`).
* Base: semilla y línea 1 calculadas (`decide`).
* **`readerVerdictW_iff_of_pieceLocal`**: el lector decide `φ` si `PieceLocal` vale en cada join.

**Abierto:** `PieceLocal` (la regla del join). `top_one_source` ya da su primera parte (la tabla de un nodo del
paso nuevo viene de un solo origen). Falta que los testigos de los pasos inferiores y las entradas entre
miembros puedan tomarse en esa misma pieza.

### 4.2γ Sonda para formalizar `PieceLocal` (`piece_learn_probe.jl`)

Corpus pequeño completo, 3,5 M cliques de tamaño 1–3 con testigos en estados unidos:
* **E1 falla** (20 304): si `r` y `q` son nodos de una pieza y `r` posee `q` en el estado unido, `r` no tiene por
  qué poseerlo en esa pieza: el join sí añade entradas cruzadas.
* **La pieza de un testigo cualquiera del paso nuevo no siempre sirve** (E4 falla 25 873 veces).
* **H9 vale siempre**: toda clique con testigos del estado unido es clique en alguna pieza.
* **H12 vale siempre**: la pieza buena contiene un nodo del paso nuevo que posee `Q` en ella.
* **H10**: «clique en `P` y un nodo del paso nuevo de `P` la posee en `P`» ⇒ `P` buena, salvo **160 casos**, y en
  todos falta **solo el testigo de un `L3` anterior** (p. ej. `clause_mix_sep`, paso 32, `Q = {x=1, c=1, b=1}`,
  falta el paso 22 = `L3` de `a∧b → ¬x`); otra pieza sí lo tiene.

Ruta de formalización que sugiere: `PieceLocal` = H9 + «en una pieza donde `Q` es clique poseída por un nodo del
paso nuevo, hay testigos en todos los pasos salvo `L3` anteriores» + la elección de pieza en esos `L3`.

### 4.2δ La frontera del join (`PieceJoin.lean`, parte nueva)

Sonda (`piece_learn_probe.jl`, H13–H15, 3,5 M cliques):
* **H15 siempre**: un testigo del paso `n` vive en una sola pieza. **Demostrado** (`mid_key`, `mid_one_source`).
* Con `top_one_source` (paso `n+1`): **`frontier_owns`**: los dos testigos frontera poseen la clique entera
  dentro de su única pieza.
* **H14 siempre**: alguna pieza contiene un testigo de cada paso frontera y es buena. **H13 falla** (13 847): no
  basta cualquier pieza con ambos.

Descartados también: **E1w** (la entrada entre dos nodos que posee un mismo nodo del paso nuevo de la pieza es
local a la pieza; falla 10 338) y **H16** (la clique es clique en la pieza de cada testigo del paso nuevo; falla
25 713). La pieza buena no la fija la tabla de un solo testigo frontera.

**Abierto:** el lema 1 (H9: la clique es clique en alguna pieza) para tamaño ≥ 3. Los testigos frontera fijan
la pieza de sus propias entradas, pero las entradas entre miembros pueden venir de la otra pieza (E1 falla).

### 4.2ε Qué decide la pieza buena: los pasos de cláusula (`piece_learn_probe.jl`, H18–H19)

* **H18**: en una pieza donde `Q` (con testigos en el estado unido) es clique, o no falta ningún testigo, o faltan
  **solo pasos de cláusula** (`L1`, `L2` y `L3` a la vez: 160 casos). Nunca falta un testigo de un paso de
  variable, de fusión ni del paso nuevo.
* **H19 siempre**: pieza buena ⇔ `Q` es clique en ella y tiene testigo en todos los `L3` anteriores.
* Ejemplo (`clause_mix_sep`, paso 32, `Q = {x=0, c=1, b=1}`): en la pieza `z = 0` es clique pero no tiene
  testigos en los pasos de `a∧b → ¬x`; con `z = 0`, `x = 0` y `b = c = 1` (que fuerza `y = 0`) no se cumple
  `x ∨ y ∨ z`. En la pieza `z = 1` hay solución (`a = 0`) y testigos en todos los pasos.

Lectura: la pieza buena es la que contiene una solución por `Q`; las cláusulas son los únicos pasos donde una
pieza sin solución pierde testigos.

### 4.2ζ «La unión no inventa caminos» (`paths_probe.jl`, `PieceJoin.join_no_new`)

* **Entrada a entrada, demostrado** (`join_no_new`): todo nodo y toda entrada de un estado unido vienen de una de
  sus piezas.
* **Caminos, medido** (1,25 M caminos completos enlazados por padres en estados unidos):
  * **P1 falla** (932 867): un camino enlazado puede mezclar piezas; pero esos caminos no son cadenas (sus
    nodos no se poseen todos entre sí).
  * **P3 vale siempre** (20 296 cadenas): **toda cadena del estado unido —camino enlazado cuyos nodos se poseen
    dos a dos, una configuración real— es cadena dentro de una sola pieza.** Es la frase del usuario en su
    forma exacta: la unión no inventa caminos válidos.

**Demostrado** (`PieceJoin.chain_in_piece`): toda cadena (certificado) de un estado unido es cadena de la pieza
que viene de su propia clave. La cadena se decodifica en una solución parcial (`PrefixDecode`) y la máquina la
lleva por sus claves hasta esa pieza (`PrefixCarry`), donde es la misma cadena.

Consecuencia: `PieceLocal` equivale a que toda clique con testigos del estado unido tenga certificado en él (si lo
tiene, `chain_in_piece` lo pone en una pieza, con la clique y sus testigos dentro).

El lector necesita la versión para cliques con testigos (`PieceLocal`), porque `MapCert` habla de cliques. P3 es
su caso de cliques completas.

### 4.2η Crecer en el estado unido y la clave de la clique (`join_grow_probe.jl`)

Mismo corpus, 3,5 M cliques con testigos en estados unidos:
* **A, crecer:** en todo paso sin miembro hay un nodo que amplía la clique conservando testigos. **84,6 M
  comprobaciones, ninguna falla.** Es `GrowState` en los estados unidos.
* **B1:** siempre hay testigos frontera `r` (paso `n`) y `w` (paso `n+1`) compatibles (`w` posee `r`).
* **B2:** algún par así amplía la clique (siempre); no todos (B2' falla 33 162).
* **B3:** la pieza de todo par frontera que amplía la clique es buena (siempre).

Consecuencia lógica (sin nuevas hipótesis): si la clique crece hasta tener un nodo en cada paso, es una cadena
(`chain_of_cover`), y `chain_in_piece` la pone en la pieza de su propia clave. Así **`GrowState` en el estado
unido ⇒ `PieceLocal`** (y B3 es este argumento). Y `GrowState` en los estados de partida ya basta al lector
(`StateGrow.readerVerdictW_iff_of_grow`). El núcleo es **crecer**.

### 4.2θ Las dos vías, lado a lado (`ChainRoute.lean`)

| | vía de cliques (`MapCert`/crecer) | vía de caminos (`SupportedG`/cadenas) |
|---|---|---|
| filtro de requisito | demostrado (`mapCert_filter`) | abierto (`HardStepExact`: el review tras el filtro) |
| `UP` con ventana saltada | demostrado por pieza (`mapCert_skip`) | abierto (`SkipExact`) |
| `UP` sin salto | demostrado (`mapCert_addNode`) | demostrado (`SupportedS_addNode`) |
| join | abierto (`PieceLocal` / crecer en el unido) | **demostrado** (`supported_join`, `chain_in_piece`) |
| lector | `readerVerdictW_iff_of_pieceLocal`, `_of_grow` | **`readerVerdictW_iff_of_chains`**: basta que todo estado válido que visita el lector tenga una cadena |

Cada vía resuelve justo lo que la otra deja abierto: la de cliques pasa filtros y cláusulas porque lleva restricciones
de mapa, la de caminos pasa el join porque la unión no inventa cadenas.

### 4.2ι El invariante combinado, formalizado (`ChainRoute.combined_invariant`)

* **`PieceJoin.pieceLocal_of_mapCert`**: si los estados de la línea `n+1` tienen `MapCert`, vale `PieceLocal n`: el
  certificado de una clique con testigos del estado unido está en una pieza (`chain_in_piece`) y lleva allí la
  clique y sus testigos (los nodos de una cadena se poseen dos a dos).
* **`combined_invariant`**: `MapCert` en todos los estados de la máquina **⇔** `PieceLocal` en todos los joins.
  Cliques dentro de cada pieza (filtro, `UP`, ventana saltada: demostrados) y cadenas a través del join.
* Reglas locales del join descartadas con datos: E1 (20 304 fallos), E1w (10 338), E1rw (7 296), H13, H16. La
  pieza buena la fija la clique entera con todos sus testigos (H19: clique y testigos en todos los `L3`
  anteriores), no una entrada.

**Abierto, único:** `PieceLocal` (equivalente a `MapCert` del estado unido). Medido: 3,5 M cliques sin excepción.

> ⚠ **Corrección (§4.2λ):** esa medida solo cubría `R = ∅`. Con una restricción en el paso `n`, `MapCert` del estado
> unido y `PieceLocal` son **falsos** (`certj_probe.jl`). `combined_invariant` sigue siendo una equivalencia correcta,
> pero entre dos enunciados falsos. El sustituto es `FCert` (§4.2λ).

### 4.2κ Después del invariante combinado: el join, los kernels y la unión de línea (sesión 2026-09-26)

**Resumen de estado.**

| pieza | estado |
|---|---|
| Todo estado de la máquina es un kernel; `GrowR ⇔ MapCert` en cada estado de línea | **demostrado**, sin hipótesis |
| El join se descomprime por la clave: la pieza revisada cabe en `filter(J,{k})` | **demostrado** |
| FU: filtrar el estado unido cabe en la unión de sus piezas filtradas, bajo `MapCert J` | **demostrado** |
| Bajada fijada: pieza fijada sin cima ⊆ fuente fijada; truncar un kernel da un kernel | **demostrado** |
| `MapCert` de la línea `n+1` desde GL/GLF de la línea `n` | **demostrado como implicación**; su hipótesis es **falsa** en 20 casos (restricción en la cima) |
| `PieceLocal` (≡ `MapCert` del estado unido ≡ X1 en el estado unido) | ⚠ **falso** con restricción en el paso `n` (§4.2λ); sustituido por `FCert` |

Lo único que falta para que el lector decida sigue siendo `PieceLocal`. Esta sesión lo ha reducido y medido desde varios
lados; el núcleo que queda en todas las formas es el mismo: **elegir, con la clique entera, la pieza (o el destino)
donde vive**; ninguna regla local lo decide.

#### 4.2κ.1 Compresión sin pérdida (`decompress_probe.jl`, `PieceFilter.lean`)

* **Medido** (review antigua; reejecución pendiente, ver 4.2κ.8): D1, `filter(J,{k_i}) = P_i` tabla a tabla en 4 094
  de 4 094 piezas; SYM, posesión simétrica en todo estado unido; H20, toda clique con testigos de `J` admite una clave
  `k_i` co-poseída por testigos en todos los pasos, pero **FP/H21 fallan en 20 casos** (`WitR J Q [k_i]` no basta para
  sobrevivir al filtro por `k_i`); F3 falla 2 503.
* **Demostrado**: `piece_survives_filter` (la pieza revisada cabe en `filter(J,{k})`: es un kernel bajo `J` que en el
  paso `n` solo nombra `k`, y la review nunca baja de un kernel); `filter_in_piece` (la otra mitad, si toda entrada del
  filtrado está en una cadena, `EntryOnChain`); `entryOnChain_of_mapCert` (en un kernel, una entrada es una clique de
  dos con testigos: regla de parejas y simetría); `mapCert_filter_pin`; `filter_in_piece_of_mapCert` (bajo `MapCert J`
  el join se descomprime exacto). Circular para `PieceLocal`, pero muestra que la mitad dura de la descompresión y
  `PieceLocal` son el mismo enunciado.

#### 4.2κ.2 Reglas locales para la entrada filtrada: ninguna (`lift_probe.jl`, review antigua)

Inducción de arriba abajo en el kernel filtrado. Si `v` está por encima de `q`, basta la simetría; con `v` debajo
(260 301 entradas): SL falla 4 302, SL2 1 872, C2 (co-poseedores en `P` en todo paso por encima) 287. **FW, 0 fallos**:
si `v ∉ P(q)`, algún paso no tiene nodo de `P` que posea `q` y `v`. Usarlo pide los pasos de abajo: no bien fundado.

#### 4.2κ.3 Crecer un nodo (`grow_step_probe.jl`, review antigua; `GrowCert.lean`)

* **Medido**: X1 (toda clique con testigos gana un nodo en cualquier paso, 55 M pruebas), X3 (la voraz con cualquier
  extensión válida nunca se atasca), X4 (en el estado unido, la extensión se toma en la pieza buena): 0 fallos. X2
  (todo testigo extiende) falla 318 k.
* **Demostrado**: `growR_iff_mapCert` (en un kernel con el contexto del lector, crecer con restricciones de mapa es
  exactamente `MapCert`); `growR_join` (si crecen las piezas y vale `PieceLocal`, crece el estado unido). X1 es el
  núcleo en su forma más pequeña, no una hipótesis más débil.

#### 4.2κ.4 Todo estado de la máquina es un kernel (`KernelUp.lean`) — demostrado, incondicional

* Julia tenía **enlaces caducados** (padre–hijo entre nodos que ya no se poseen): el corte en dos fases, la regla de
  parejas, el espejo y la regla de la cadena quitaban dueños sin desenlazar. Corregido (`LINK_MODE = :on`, f463d92),
  como el modelo Lean (`unlinkIncompatible`, `cutNode`). Además (e1acfd4) la review contra hijos llega al paso 0 (la
  asimetría de v48) y se desactiva la regla de la cadena (no está en el modelo Lean). Tras los tres cambios: veredictos
  55/55 frente a fuerza bruta, piezas 5 033/5 033 y estados de línea 2 986/2 986 son kernels (`kernel_probe.jl`).
* **Demostrado**: `kernel_addNode`/`kernel_up` (el `UP` sin ventana saltada conserva el kernel; con salto aplica la
  review y `kernel_of_review`), `kernel_join` (la unión de dos kernels es un kernel; se añadió `Join.join_sons_source`),
  `kernel_initSeed`, **`kernel_reachable`** (inducción sobre `Reachable`), **`aCtx_line`** (todo estado de línea tiene el
  contexto completo del lector) y **`growR_iff_mapCert_line`**.

#### 4.2κ.5 La unión de línea como invariante (`global_local_probe.jl`, `dest_probe.jl`, `glpin_probe.jl`, `glfstar_probe.jl`)

Medido con la review corregida, sin fallos salvo lo indicado:
* **GL** (1,78 M): en bin cada línea tiene como mucho 2 estados; su unión (claves distintas) no crea cliques con
  testigos (con `R` vacío). **AP** (1,95 M): la unión de todas las piezas de un paso tampoco.
* **Por destino**: el destino de un testigo cualquiera de la cima no siempre tiene testigos (Wd falla 5 701 de 2,67 M);
  siempre hay algún destino bueno. **B1** (26 M pares, con tríos): el destino es bueno ⇔ `Q` es clique en `J_d` con
  testigos en todos los `L3`; de los malos, 12,13 M no son clique y 184 fallan por testigos en una cláusula.
* **GLF** (GL con fijaciones): caso ventana 251 076, fijaciones al azar 2,83 M. **GLF\*** (familias con estados repetidos
  y fijaciones al azar): 4,29 M. **FU** (filtrar el estado unido cabe en la unión de sus piezas filtradas): 5 337.

#### 4.2κ.6 El paso del join desde la unión de línea (`LineUnion.lean`, `Trunc.lean`, `FilterUnion.lean`)

**Demostrado** (implicaciones):
* `certR_low_of_GL` y `certR_top_of_GL`: con GL y `MapCert` en la línea `n`, cliques con testigos de la línea `n+1`
  sin/con miembro en la cima tienen certificado. El filtro se resuelve (`req_of_join`: las piezas de un destino
  comparten requisitos; `owns_of_join`; `son_of_req`: la clave de la cadena es padre del destino); con miembro en la
  cima, los testigos poseen las claves de su ventana (`wit_owns_window`) y la cadena sube justo a él.
* **Ventana prohibida**: `StatePiece.skip_window` (extraído de `mapCert_skip`), `Trunc.kernel_trunc` (truncar la cima de
  un kernel da un kernel), `skip_trunc_below`; con fijaciones `pinsW` (requisitos del destino y `L1 = 1` para la fuente
  que salta), `certR_low_of_GLF` y `mapCert_next_F`: **GLF y `MapCert` en la línea `n` dan `MapCert` en la línea `n+1`**.
* **Hacia GLF(n+1)**: `mapCert_filter_pins`, **`filter_union`** (FU desde `MapCert J`) y **`piece_pinned_below`** (bajada
  fijada), ambos incondicionales dada `MapCert J`.

#### 4.2κ.7 ⚠ Refutado: GL/GLF con restricción en la cima (`select_probe.jl`, `gltop_probe.jl`)

`LineUnion.GL`/`GLF` cuantifican sobre todo `R`. Con `R` que fija un nodo de la cima (todos los testigos poseen, en la
unión, un nodo de la cima con id `m`): **GLtop falla 20 de 2,08 M** (estados sin fijar) y **GLFtop 20 de 2,1 M**
(fijados por `pinsW`): los mismos 20 casos que FP en 4.2κ.1. Los usos lo necesitan: la clave de la ventana (paso `n`)
y las restricciones de `R` en el paso `n` son restricciones en la cima de la línea `n`. Por tanto `certR_*_of_GL(F)` y
`mapCert_next(_F)` son **implicaciones correctas con hipótesis falsa**; los resultados de 4.2κ.4 y las piezas FU/bajada
no dependen de ella.

**Los 20 casos (`twenty_probe.jl`)**: todos en `clause_mix.cnf`, paso 26. Un testigo `r` posee `Q` por la pieza buena
(clave `25:1`) y el nodo `25:0` por la otra pieza; ningún camino pasa por `Q` y `25:0` a la vez. Ninguna entrada es falsa
(cada una la respalda un camino real): **no lo arregla una regla de review** (borraría información verdadera); falla el
hecho de tres miembros «`r` con `Q` y con `k` a la vez», que las tablas por parejas no guardan. El defecto está en
GL/GLF, que dejan que cada entrada de un testigo venga de un estado distinto. Con restricciones solo por debajo de la
cima también falla: 76 de 37,8 M (`gltop_probe.jl`, GLtop-below). Corrección candidata: cada testigo posee `Q` y `R`
dentro de un mismo estado.

Selección de miembro en familias fijadas: WL falla 319 575, WL1 y CL 1 610 de 5,19 M. Vía de cadenas: 519 de 61 108
cadenas de la unión no son cadena de ningún miembro (mezclan versiones fijadas de un mismo estado).

#### 4.2κ.8 Qué queda y repaso

* ⚠ **Superado por §4.2λ**: `PieceLocal` y `MapCert` del estado unido son falsos con restricción en el paso `n`.
* **Abierto, único** (antes de §4.2λ): `PieceLocal` (≡ X1 en el estado unido). En cada reformulación reaparece la misma selección: la
  pieza (o el destino) buena la fija la clique entera con sus testigos en los `L3` (H19, B1), no una entrada, un
  testigo suelto ni la posesión de la cima.
* **Siguiente candidato**: GL/GLF con restricciones solo por debajo de la cima (sonda en curso) y tratar la clave de la
  cima como miembro de `Q` en vez de restricción; o un invariante que lleve la selección por cláusulas (`L3`).
* **Reejecución pendiente** con la review corregida: `decompress_probe.jl`, `lift_probe.jl`, `grow_step_probe.jl`
  (medidos antes de f463d92/e1acfd4).

### 4.2λ `MapCert` es falso en el estado unido; el sustituto `FCert` (sesión 2026-09-27, `FiltCert.lean`)

**Resumen de estado.**

| pieza | estado |
|---|---|
| `MapCert`/`PieceLocal` en el estado unido | **falso** (4 cliques en `clause_mix.cnf`, paso 26) |
| `FCert` (todo filtro válido tiene `CertClique`): base, join desde `PieceLocalF`, lector | **demostrado** |
| Pieza sin miembro en la cima (`cert_piece_low`) | **demostrado**, sin hipótesis nuevas |
| Pieza con miembro en la cima sin fusión (`single_parent`) | **demostrado** |
| Pieza con miembro en la cima fusionado | reducido a `MergeSplit` (**demostrado** `topMerge_of_mergeSplit`) |
| `PieceLocalF` | **abierto**; medido 66,9 M sin fallos |
| `MergeSplit` | **abierto**; sonda en curso |

> **`readerVerdictW_iff_of_mergeSplit`: el lector decide `φ` bajo `PieceLocalF` en cada join y `MergeSplit` en cada
> pieza.** Las dos dicen lo mismo: una clique con testigos se queda en un lado de dos fijaciones complementarias.

#### 4.2λ.1 El contraejemplo (`twenty_probe.jl`, `certj_probe.jl`)

En `clause_mix.cnf`, paso 26 (estado unido `J`, piezas de claves `25:0` y `25:1`), hay cliques `Q` como
`{21:1, 5:0}` tales que:
* `Q` es clique en `J` y en cada paso hay un testigo que posee `Q` y un nodo `25:0` (`WitR J Q [25:0]`);
* **no hay ninguna cadena de `J` que pase por `Q` y por un nodo `25:0`** (búsqueda exhaustiva, 4 casos de 4).

Así que `MapCert J` es falso, y con él `PieceLocal` (un nodo `25:0` solo existe en la pieza `25:0`, donde `Q` no es
buena). La sonda antigua de `PieceLocal` (3,5 M) y la de crecer (X1, 48 M) solo miraban `R = ∅`. La causa es la de
§4.2κ.7: `WitR` pide la restricción solo a los testigos, y cada testigo toma `Q` de una pieza y `25:0` de la otra.

No afecta al lector: una restricción `25:0` solo aparece cuando la máquina filtra `J` por `25:0`, y ese filtro es la
pieza `25:0` (D1), donde `Q` ya no es clique con testigos. **La máquina aplica las restricciones filtrando.**

#### 4.2λ.2 Lo que sí vale (medido, review corregida)

| medida | sonda | casos | fallos |
|---|---|---|---|
| GLJ: cada testigo posee `Q` y `R` dentro de un mismo estado (`R` ∅ / cima / bajo) | `joint_probe.jl` | 52,9 M | 0 |
| DJ con `R = ∅`: `Q` buena en `J` ⇒ testigos por pieza | `joint_probe.jl` | 1,94 M | 0 |
| DJ con `R = [k_i]` | `joint_probe.jl` | 2,26 M | **20** (el contraejemplo) |
| GLK/GLKs: en cada paso, un testigo coherente con su propia clave; GLKany: una sola pieza | `key_probe.jl` | 1,55 M | 0 |
| `CertClique` sin filtro, estados de línea / piezas | `fcert_probe.jl` | 2,1 M / 2,6 M | 0 |
| **`PieceLocalF`** (filtro vacío, de un nodo, de 2–4 al azar) | `djf_probe.jl` | 66,9 M | **0** |
| `FCert` con filtros arbitrarios | `fcert_any_probe.jl` | en curso | |
| `TopParent`, `CertClique` de piezas filtradas | `toppar_probe.jl` | en curso | |
| `MergeSplit` | `mergesplit_probe.jl` | en curso | |

Reejecución con la review corregida de las sondas anteriores a f463d92/e1acfd4: `decompress` igual (D1 4 094/4 094; FP y
H21 fallan 20, el contraejemplo); `lift` casi igual (FW 0 fallos; SL 4 302, SLa 3 392, PL 5 530); `grow_step` igual (X1,
X3, X4 sin fallos; X2 falla 318 k).

#### 4.2λ.3 El invariante `FCert` (**demostrado**)

* **`FCert g`**: todo filtro válido `filterAll g R`, con pins dentro de los pasos, cumple `CertClique`.
* `chain_pins`: una cadena de un estado filtrado pasa por sus pins. `certThrough_grown`: un certificado de un estado
  filtrado sube al mismo filtro de un estado que lo contiene.
* **`fCert_of_mapCert`**: `MapCert` da `FCert` (base: semilla y piezas de la línea 0).
* **`PieceLocalF n`**: una clique con testigos de un estado de la línea `n+1` filtrado por `R` lo es de una pieza
  filtrada por `R`. **`fCert_join`**: con `PieceLocalF`, el join conserva `FCert`.
* **`readerVerdictW_iff_of_fCert`**: `FCert` en la última línea basta al lector (con `R = []` es `CertClique` del estado
  de partida).
* **`fCert_line`**, **`readerVerdictW_iff_of_pieceLocalF`**: bajo `PieceLocalF` y `PieceF` (una pieza de un estado con
  `FCert` tiene `FCert`), toda la máquina.

#### 4.2λ.4 La pieza (**demostrado**, salvo la fusión)

* **`cert_piece_low`**: una clique con testigos de una pieza filtrada, sin miembro en la cima, está en un certificado
  cuyo nodo de la cima es la extensión de su nodo del paso `n`. La pieza filtrada sin su cima queda bajo la fuente
  fijada por `pinsW` y por los pins bajo la cima (`piece_pinned_below`). `FCert` de la fuente da el certificado allí.
  El certificado pasa por los requisitos y por `L1 = 1` cuando se salta la ventana, así que su extensión está
  permitida. Sube por el `up` (`ChainSound_upFiltering`) y sobrevive a los pins (el pin de la cima solo puede ser
  `d`). La fuente fijada es válida porque cada paso tiene un testigo.
* **`single_parent`** (en cualquier kernel): si `w` tiene un solo padre `c`, `nbrP` pone toda la tabla de `w` en la de
  `c`, y la simetría hace el resto. Así `w :: Q₀` con testigos da `c :: Q₀` con testigos.
* **`topParent_of_topMerge`**: todo nodo de la cima tiene padre (validez y `NotRoot`). Si todos sus padres son uno,
  `single_parent`. Queda **`TopMerge`**, las cimas con dos padres.
* **`pieceF_of_topParent`**: con miembro `w` en la cima (el único: dos nodos de un paso no se poseen), el padre `c`
  sustituye a `w`. El certificado por `c` y los miembros de abajo se extiende en la cima por el desplazamiento de `c`,
  que es `w` (mismo id, padre y abuelo, por `PMP`/`GPMP`).
* **`gparent_owner`**: un nodo solo posee, dos pasos más abajo, a su abuelo.
* **`topMerge_of_mergeSplit`**: los dos padres de una fusión comparten id y padre, y solo difieren en el abuelo (un
  nodo de mapa en el paso `n-2`). Fijando uno de los dos abuelos, `w` se queda con un solo padre y aplica
  `single_parent`; la pieza fijada queda bajo la pieza sin fijar (`below_filterAll`).

**Abierto**:
* **`PieceLocalF`**: la clique con testigos de un estado unido filtrado vive en una pieza filtrada.
* **`MergeSplit`**: la clique con testigos con cima fusionada sobrevive al filtro por uno de los dos abuelos.

Las dos tienen la misma forma: **una clique con testigos se queda en un lado de dos fijaciones complementarias**. En
el join las fijaciones son la clave del paso `n`; en la fusión, el abuelo del paso `n-2`. Es un hecho de tres
miembros: la tabla unida no guarda qué lado respalda cada entrada, así que no sale de las reglas por parejas. Es el
núcleo de siempre (§4.2q), ahora en una forma que sí está medida sin fallos (`PieceLocalF`).

### 4.2μ LUA demostrado por inducción; el núcleo en cinco hipótesis locales (`AnchorPiece.lean`, `UnionLine.lean`)

**Teorema final:** `UnionLine.readerVerdictW_iff_of_luau` — el lector decide `φ` bajo cinco hipótesis, todas medidas sin
fallos en su forma exacta y todas del mismo tipo (una unión filtrada no reparte una clique con testigos entre sus lados):

| hipótesis | enunciado | medida (forma exacta) |
|---|---|---|
| A1K | una clique con testigos de la cima truncada de un estado unido filtrado crece con un nodo del paso `n` | 6,20 M |
| AFU | en la unión filtrada de una línea, una clique anclada en la cima sobrevive a fijar el requisito del ancla | 6,30 M |
| `TopMergeU` | ídem con cima fusionada: un padre ocupa el lugar del ancla | 124 k |
| `TopMergeJ` | fusión en el estado unido filtrado | 1,45 M |
| AFP (AF en las piezas) | una clique anclada sobrevive a fijar un nodo que el ancla fija | en curso |

**Demostrado (sin `sorry`, solo `[propext, Quot.sound]`):**
* **Ancla en la cima** (`AnchorPiece`): `PieceLocalF ⇐ A1 + S2` (`pieceLocalF_of_anchor`). S2 en la línea 0 (`line_one`,
  `topPieceF_zero`: con una sola fuente, todo estado de la línea 1 es su pieza); A1 en la línea 0 (`anchorF_zero`).
* **S2 desde LUA** (`topPieceF_of_luaJ`): el miembro de la cima cede su sitio a un padre (`single_parent`, `parent_or_merge`;
  fusión: `TopMergeJ`, o `MergeSplitJ` vía `merge_pin`), la cima truncada cabe en la unión de las fuentes, LUA la pone en la
  fuente del padre, `FCert` da la cadena y sube con extensión `w` (`good_of_chain`).
* **La fusión en la pieza desde AF** (`topParent_of_afp`): la cima fija el nodo del paso `n-1` (`gparent_owner`); fijado,
  `cert_piece_low` da una cadena cuya extensión es `w` sea cual sea el padre. `MergeSplit` deja de hacer falta.
* **La unión de una línea como estado** (`UnionLine`): `lineU` (pliegue de `join`; `join` ignora el `map_parent` del segundo,
  así que los lemas `_join` dan el contexto del lector: `UCtx_join`, `lineU_props`); procedencia de dueños, padres e hijos a
  través del driver (`srcF_pureAdvance`, `piece_old`, `line_old`); la cima truncada de un estado filtrado de la línea `n+1`
  queda bajo la unión de la línea `n` (`LowIn`, `trunc_below`).
* **LUA por inducción** (`luau_zero`, `luau_succ`): una clique anclada de la unión filtrada de la línea `n+1` fija el
  requisito del ancla (AFU), el ancla cede su sitio a un padre (`TopMergeU` en la fusión), baja a la unión de la línea `n`,
  LUAU allí la pone en la fuente del padre, y la cadena de `FCert` sube con el ancla (`climbE`). `luaJ_of_luau`: la forma
  que usa S2. `anchorF_of_a1k`: A1 desde A1K y LUA. `fCert_luau_line`: `FCert` y LUAU avanzan juntas por la línea.
* **AFU es exactamente lo que LUAU añade por línea** (`afu_of_luau`, con `line_pinned_req`): LUAU en la línea `n+1` implica
  AFU; y LUAU(n) + AFU(n+1) + `TopMergeU` + `FCert` implican LUAU(n+1).

**Refutado (formas o mecanismos que no valen):**
* `MapCert` y `PieceLocal` en el estado unido (§4.2λ.1).
* Elegir la fuente con un testigo cualquiera del paso `n` (ULUA con R1∀: 5 226 fallos; con algún testigo o con el ancla que
  da A1K, 0).
* `TriPin` con un nodo de la cima como pin (0,1 %): la estrella del ancla no es siempre un kernel.
* La estrella del ancla sobrevive entera a fijar su requisito (1,5 %, `afu_star_probe.jl`; sus nodos sí, siempre).
* Localidad anclada de entradas: si `x` y `v` poseen al ancla, la entrada `x→v` está en el estado del ancla (0,2 %,
  `entry_anchor_probe.jl`).

**Lectura.** Las cinco hipótesis se cumplen siempre, pero ningún mecanismo local las da: la clique se salva por sus testigos
concretos en todos los pasos, no por propiedades de entradas sueltas ni de la estrella del ancla. Es el patrón del join (E1,
E1w, H13). Una prueba necesita un argumento global que use los testigos de todos los pasos; la única herramienta global que
ha funcionado es la semántica (cadena = solución parcial, `chain_in_piece`, `PrefixCarry`), que vale para cadenas.

**Otras medidas de la sesión** (review corregida, sin fallos): `FCert` con filtros arbitrarios (68,5 M), `PieceLocalF`
(66,9 M), ULUA (65,6 M), LUA exacta (5,70 M), `TopParent` y `CertClique` de piezas filtradas (5,4 M / 83,5 M),
`MergeSplit` (1,63 M), A1/S2 con filtros (58,8 M / 81 M), AFU y A1KU en la unión de estados filtrados (6,26 M / 3,51 M),
LUAU (387 k).

### 4.2ν Línea global: la red como CSP, el empalme de certificados y la inducción por el paso más alto (`Splice.lean`)

Las tablas son locales; la red de cliques que construyen es global. Los mecanismos locales para las hipótesis de §4.2μ
están refutados, así que esta línea busca argumentos sobre la red entera.

**Qué testigos llevan la información** (`witsteps3_probe.jl`, `witclause_probe.jl`, tríos). Con 1–2 nodos la pregunta es
vacía (la regla de parejas ya da testigos). Con tríos:

| testigos exigidos solo en | sin cadena (estados / unión) |
|---|---|
| ninguno | 477 / 732 |
| pasos de variable | 230 / 191 |
| pasos de cláusula | 1 / 1 |
| **cláusulas + frontera de la fusión media** | **0 / 0** |
| solo las cláusulas que tocan a la clique (+ frontera) | 13 / 17 |

La información vive en los testigos de cláusula (los nodos con requisitos), no en los de variable, pero no es local por
cláusula: a veces decide una cláusula lejana (cadenas de implicaciones).

**La red como CSP binario** (`majority_probe.jl`, `polymorphism_probe.jl`, `relmaj_probe.jl`). Pasos = variables, nodos de
camino = valores, «x posee v» = relación; el review da 3-consistencia fuerte. Si las relaciones fueran cerradas bajo una
mayoría habría consistencia global (Jeavons–Cohen–Cooper). La mayoría bit a bit sobre ventanas conserva la relación en el
99,8 % (mín/máx 88 %, minoría 97 %); relativa a una clique con testigos, 99,99 %; no exacta. La ruptura es inevitable: la
relación de una cláusula (todo menos `000`) no es cerrada bajo mayoría (`maj(001,010,100) = 000`). **La ventana prohibida
es el filtro semántico** (elimina los certificados que violan una cláusula), no un defecto.

**Empalme** (`splice_probe.jl`). Dos certificados que comparten un nodo en el paso `s` se empalman (prefijo de uno, sufijo
del otro): 198 650 empalmes válidos; de los 266 824 que fallan, **todos violan un requisito**. La ventana prohibida es local
(un nodo es una ventana), así que nunca rompe un empalme; solo lo rompen los requisitos de largo alcance.

**Demostrado** (`Splice.lean`, sin `sorry`, solo `[propext, Quot.sound]`):
* **`splice`**: el empalme de dos certificados de un estado de la línea en un nodo compartido, con los requisitos que cruzan
  cumplidos por el primero, es un certificado del mismo estado. Prueba semántica: el empalme es un camino enlazado que cumple
  los requisitos, se lee como solución parcial (`preSat_decode`), la máquina la lleva al estado de su clave
  (`cert_of_prefix`), que es el del segundo certificado (`key_inj`).
* **`certUpTo_succ`, `certClique_of_splits`**: por inducción sobre el paso más alto, si toda clique con testigos se corta
  (`SuffixSplit`: un sufijo `τ` por su parte alta y una clique con testigos `P` en pasos ≤ `s` con su parte baja y un nodo
  por cada requisito de `τ` que cruza), toda clique con testigos tiene certificado: `P` lo tiene por inducción y se empalma
  con `τ`.
* **`readerVerdictW_iff_of_splits`**: el lector decide si en la última línea toda clique con testigos se corta (y las del
  paso 0 tienen certificado).

**Medido sobre la elección del sufijo** (tríos con testigos, `splicechoice_probe.jl`, `goodsuffix*_probe.jl`,
`choosesuffix*_probe.jl`):
* pares (prefijo, sufijo) al azar compatibles: 78 %; no todo sufijo tiene prefijo compatible (7 %): hay que elegir juntos;
* un sufijo tiene prefijo compatible **exactamente** cuando la parte baja ampliada con sus requisitos que cruzan es clique
  con testigos (V3: 133 968 / 8 407, sin excepción; es `CertClique` de esa clique, pero da la forma de la inducción); la
  versión requisito a requisito con testigos (V2) falla 12 veces de 142 k, cuando cruzan 6–7 requisitos;
* elegir el sufijo con sus nodos por encima del corte en la red de los que poseen la clique: existe siempre y es bueno en
  84 809 de 84 810 tríos. El caso malo (`rand3sat_v8_c10`, paso 32): un testigo de la clique en el paso 14 posee a los tres
  miembros pero no está en ninguna cadena con los dos de abajo — **testigos espurios respecto a una parte de la clique**.

* **Regla con testigos buenos (R_gw, `goodwit_probe.jl`)**: sufijo con sus nodos por encima del corte en la red de la
  clique y cuyos requisitos que cruzan nombran, **cada uno**, un testigo bueno (la parte baja más ese testigo es clique con
  testigos): existe en los 84 810 tríos y los 152 519 sufijos así muestreados son todos buenos. Con testigos buenos basta
  requisito a requisito: la compatibilidad conjunta desaparece.

* **Composición de testigos buenos (`compose_probe.jl`, cliques de 3 y 4 nodos, todos los cortes)**: para un sufijo R_gw,
  **alguna** elección de un testigo bueno por requisito que cruza da una parte baja ampliada con testigos (109 144 y
  152 129 sufijos, 0 fallos); **no toda** elección (fallan el 5,8 % y el 3,3 %). Los testigos buenos componen, pero hay que
  elegir cuáles.

* **Elección voraz (`greedy_probe.jl`)**: añadir los testigos de uno en uno, cada uno bueno respecto a la parte baja ya
  ampliada, eligiendo al azar entre los candidatos. En orden de pasos **ascendente** se atasca 5 veces de 109 568 (tríos) y
  4 de 152 041 (cliques de 4); en orden descendente 2,3 % y 1,6 %; en orden aleatorio 1,2 % y 0,6 %. Con vuelta atrás no se
  atasca nunca (es la «alguna elección» anterior: un subconjunto de una clique con testigos lo es). El orden natural de la
  máquina, de izquierda a derecha, es casi voraz.

**Lo que queda**: (a) que exista un sufijo así (siempre medido); (b) que alguna elección de testigos buenos, uno por
requisito que cruza, componga con la parte baja en una clique con testigos (siempre medido, cliques de 3 y 4); en orden
ascendente la elección es voraz salvo 9 casos de 261 k. «Testigo bueno» es una clique con testigos con un miembro
más y todos en pasos ≤ `s`: la recursión baja por el paso más alto.

### 4.2ξ La ruta de `CliqueTri`: el lector decide bajo dos hipótesis (`JoinTri.lean`)

Con la review corregida, `TriPin₁` (632 k) y `CliqueTri` (cliques de 1 a 4 nodos, ~630 k cada tamaño) no fallan en ningún
estado de línea; tampoco en las fuentes filtradas ni en las piezas (1,1 M cada una). `TriPin` sin cortes falla 317 (0,05 %):
el review tras una fijación es de una ronda y elimina justo los testigos espurios (el lector no se atasca porque revisa
tras cada elección). En los estados del lector `CliqueTri ⇔ CertLink ⇔ CertClique` (demostrado), así que es la forma más
local del núcleo: parejas, pasos y una ronda de cortes.

El estado unido es la unión de sus piezas **sin review posterior**, y aun así tiene `CliqueTri`: tiene que venir de las piezas.

**Demostrado** (`JoinTri.lean`):
* `cxP_grown`; **`cliqueTri_of_joinChoice`** (sin axiomas): estados que crecen en `J`, cada uno con `CliqueTri`, y
  `JoinChoiceP` (todo enlace compatible con una clique de `J` lo es ya en uno de ellos, con la clique allí) dan
  `CliqueTri J`. `cliqueTri_line_of_pieces`: la instancia para las piezas.
* `joinChoice_nil`: `JoinChoiceP` con la clique vacía (`join_no_new` + la regla de parejas de la pieza).
* **`fCert_join_of_choice`, `fCert_line_choice`, `readerVerdictW_iff_of_joinChoice`**: las piezas filtradas crecen en el
  estado unido filtrado (kernel bajo `J` fijado por `R`), así que `JoinChoicePF` da `CliqueTri` y `CertClique` de cada filtro
  del estado unido; las piezas conservan `FCert` (`pieceF_of_topParent`, con AF). **El lector decide bajo `JoinChoicePF`
  y AF en las piezas.**

**Medido en forma exacta, sin fallos**: `JoinChoicePF` 4,55 M (sin filtro y con filtros, cliques de 0 a 3 nodos); AF en las
piezas (`afp_probe.jl`) 100,5 M.

Frente a la ruta de LUA (§4.2μ, cinco hipótesis), esta tiene dos, y las dos son el mismo hecho: una clique con testigos no se
reparte entre los lados de una unión (en el join, entre piezas; en la fusión, entre padres).

> ⚠ **Corrección (§4.2ο):** `JoinChoicePF` es **falso**. En el exhaustivo con cliques de un nodo falla 120 veces de 133,4 M
> (`joinchoice_exh_probe.jl`), y en esos 120 también falla `CliqueTri` del estado unido. `readerVerdictW_iff_of_joinChoice`
> es correcto, pero su hipótesis es falsa en `clause_mix.cnf` y `clause_mix_sep.cnf`.

### 4.2ο Las cliques de nodos de camino fallan en el join; `CliqueTri` al grano del mapa: `FExt` y `KExt` (`MapTri.lean`)

**El contraejemplo.** Los 120 fallos de `JoinChoiceP` son **20 tríos** de nodos de camino, contados en sus 6 órdenes.
Salen en dos estados unidos: 4 en `clause_mix.cnf` (cima 26) y 16 en `clause_mix_sep.cnf` (cima 32), los dos con dos
piezas. Por ejemplo, `(6,0)–(19,0)–(27,1)`.
* Los tres pares de cada trío son compatibles de verdad, y el trío es clique con testigos en todos los pasos.
* No es clique en ninguna pieza: cada pieza aporta parte de los pares.
* No tiene solución (fuerza bruta): choca con la última cláusula cerrada, porque con una cláusula menos 96 de los 120 sí
  la tienen.
* No hay ninguna cadena del estado que pase por él. La búsqueda de cadenas encuentra cadena en 300 tríos verdaderos de
  control.

**Qué sale de ahí** (medido):
* **`CertClique` es falso** en esos estados unidos, también después del review (`filterAll J []`). Por tanto **`FCert` es
  falso** ahí. Toda ruta del lector que pase por `CertClique` o `FCert` de los estados de línea tiene una hipótesis falsa
  en esas dos fórmulas: §4.2λ, la de LUA de §4.2μ, la del empalme de §4.2ν y la de §4.2ξ. Las implicaciones siguen siendo
  correctas. Las medidas por muestreo no llegaban a esos 20 tríos.
* **Fijar nodos del mapa no los elimina** (`joinpin_probe.jl`). Con uno, dos o los tres nodos del mapa fijados y
  revisados, siguen vivos con testigos en 84, 56 y 36 de los 120 casos. El pin fija un paso y un valor, pero no el
  nodo de camino concreto.
* **Con nodos del mapa sí se sostiene.** En los 120 casos, todo conjunto de pins que deja el estado válido tiene una
  cadena por esos nodos del mapa.
* **Por parejas, los owners del estado unido son exactos** (`absent_probe.jl`, `absent_sem_probe.jl`). Lo relacionado
  es compatible (2,90 M, 100 %). Lo no relacionado no tiene solución por una cima del estado (2,74 M, 0 compatibles), y
  eso vale tanto si alguna pieza tenía los dos nodos (47 %) como si no (53 %). Unos «owners inversos» no añadirían
  información.
* **Por tríos casi son exactos** (`triple_sem_probe.jl`): 13,02 M cliques de tres con testigos tienen solución y solo
  los 20 tríos de arriba no.
* **Una regla de parejas no puede con ellos**, porque los tres pares son verdaderos. Una regla de tríos por testigos
  tampoco, porque los tienen en cada paso. Quitarlos pide guardar owners condicionados a un tercer nodo (§4.4).

**La reformulación** (**demostrado**, `MapTri.lean`, solo `[propext, Quot.sound]`). El lector nunca ve nodos de camino:
fija nodos del mapa.
* `ReadAny g₀`: los estados que se alcanzan fijando nodos del mapa uno tras otro, cada uno con su review, en cualquier
  orden y en cualquier paso, mientras el estado siga válido.
* **`FExt g₀`**: en todo estado válido de `ReadAny`, cada paso con elección tiene un nodo cuyo pin deja el estado
  válido. Es `CliqueTri` al grano del mapa y no depende del orden del lector.
  **`progressFirst_of_fExt`** (`FExt ⇒ NoDeadEnd`) y **`readerVerdictW_iff_of_fExt`**.
* **`KExt g₀`**, la misma idea sobre kernels y sin lector: todo kernel válido podado de `g₀` se estrecha, en el paso
  de cualquiera de sus nodos, a un kernel válido por debajo que nombra un solo nodo del mapa en ese paso.
  `kernel_readAny` (todo estado válido de `ReadAny` es un kernel), `pruned_readAny`, **`fExt_of_kExt`** y
  **`readerVerdictW_iff_of_kExt`**: **el lector decide bajo `KExt` de los estados de partida.**

**Medido:** `FExt` no falla en `clause_mix*`: 5.792 conjuntos de pins válidos, los de 0 y 1 nodo todos, los de 2 y 3
nodos al azar (`fext_probe.jl`). El resto del corpus está en curso.

**Inducción de `FExt` a lo largo de la máquina** (en curso, `fextind_probe.jl`). Un paso de la máquina sube cada estado
padre X a una pieza `P = upF X d` y une las piezas en J. Con pins de nodos del mapa, uno tras otro con su review,
en `clause_mix*`:

| puente | enunciado | correctos | fallos |
|---|---|---|---|
| M1 (join) | J fijado en R válido ⇒ alguna pieza fijada en R válida | 5.323 (3.939 con ≥ 2 piezas) | **0** |
| M2 (bajar) | P fijado en R válido ⇒ X fijado en requisitos de d más R sin la cima válido | 8.894 | 0 |
| M3 (subir) | X fijado así válido ⇒ P fijado válido | 7.903 | **1** |
| M2w | P fijado en R válido ⇒ hay una ventana (a, b) de los pasos s−1, s no prohibida con d y X fijado en requisitos, R⁻, a, b válido | 3.645 | 0 |
| M3w | ventana no prohibida y X fijado en requisitos, R⁻, a, b válido ⇒ P fijado en R⁻, a, b válido | 5.472 | 0 |

M2w y M3w solo están medidos en `clause_mix.cnf`. El fallo de M3 es la ventana prohibida: con esos pins, X solo es
válido con valores de los dos pasos anteriores que la ventana prohíbe junto con d. Con la ventana fijada, M3w no falla.

El esquema de la inducción:
1. M1 lleva un pin válido de J a una pieza.
2. M2w lo baja a X, con una ventana permitida.
3. `FExt` de X da la extensión.
4. M3w la sube a la pieza.
5. La pieza está por debajo de J, así que la extensión vale también en J.

En Lean, el camino es transportar kernels fijados: `isValid_filterAll_of_kernel`, `kernel_up`, `kernel_trunc` y
`kernel_join` ya están demostrados. M1 es el global (la mezcla de piezas).

#### 4.2ο.1 La inducción de `FExt`, formalizada: el lector decide bajo M1 (`UpMono`, `PieceBridge`, `FExtInd`)

**Demostrado** (solo `[propext, Quot.sound]`):
* `UpMono.below_addNode`: `addNode` conserva `Below`.
* **M2w** (`PieceBridge.src_of_piece`) y **M3w** (`PieceBridge.piece_of_src`), con `pinsW` como ventana: los requisitos de
  `d` y, si el filtro de la fuente salta una ventana, L1 = 1. En M3w, la fuente fijada no salta ventana, porque la
  única prohibida es (0, 0, 0) y pide L1 = 0. Así la subida es un `addNode` sin review, un kernel válido por debajo
  de la pieza.
* `FExtInd.LExt`: `FExt` con listas de pins. `readAny_track` y `fExt_of_lExt` hacen el encaje: un estado de pins
  sucesivos es un kernel que respeta sus pins, y todo kernel que los respete queda por debajo de él.
* `lExt_low`: líneas 0 y 1, porque cada paso tiene un solo nodo del mapa.
* `lExt_succ`: el paso de la línea n a la n+1. Encadena M1, M2w, `LExt` de la fuente, reordenar los pins, M3w y subir
  la pieza a J. En la cima de J solo vive la clave.
* **`readerVerdictW_iff_of_m1`: el lector decide `φ` bajo M1 en cada join (n ≥ 1).**

**Lo único abierto es M1**: si el estado unido fijado es válido, alguna pieza fijada igual es válida. Dado lo
demostrado, M1 equivale a que un filtro válido del estado unido tenga cadena, es decir, a que la unión de piezas
exactas siga siendo exacta. Es el hecho de tres miembros en su forma de validez, sin cliques de nodos de camino.

#### 4.2ο.2 M1 desde certificados y el reparto de M1 (`M1Sem.lean`, `m1split_probe.jl`)

**Demostrado** (solo `[propext, Quot.sound]`):
* `isValid_of_chainSound`: un estado con cadena es válido.
* **`m1_of_certPin`**: `CertPin ⇒ M1`. `CertPin n` dice que un pin válido de un estado unido de la línea n+1 está en
  una cadena del estado. Esa cadena está en una pieza (`chain_in_piece`) y sobrevive a su filtro
  (`ChainSound_filterAll`). Una cadena es una solución parcial (`PrefixDecode`), así que `CertPin` es la solidez
  semántica del test de validez del estado unido.
* `readerVerdictW_iff_of_certPin`: el lector decide bajo `CertPin` en cada join.
* La inducción (`lExt_line`, `readerVerdictW_iff_of_m1`) solo pide M1 en las líneas que existen (n + 1 < `stepCount`).

**El círculo.** M1(n) ⇐ `CertPin(n)` ⇐ `LExt` del estado unido (fijando todos los pasos) ⇐ M1(n). Con lo ya
demostrado, M1 no se obtiene: hace falta un argumento nuevo sobre el join. Semánticamente solo sale la dirección
contraria: toda solución parcial que respeta los pins hace válidos al estado unido y a su pieza (`cert_of_prefix`).
Esa dirección no es la que necesita el lector.

**Reparto de M1** (en el estado unido J, los nodos del paso n y los de la cima son puros: vienen de una sola pieza, la de
su clave k; por debajo de n las tablas son uniones):

| parte | enunciado | papel |
|---|---|---|
| M1a | J fijado en R válido ⇒ alguna clave k del paso n deja J fijado en R + k válido | `FExt` de J solo en el paso de las claves |
| M1a-todas | toda clave presente en J fijado en R sirve | versión fuerte de M1a |
| M1a-cima | la clave de todo nodo de la cima sirve | versión fuerte de M1a |
| M1b | J fijado en R + k válido ⇒ la pieza k fijada en R es válida | descompresión con pins |
| M1b-entradas | toda entrada de J fijado en R + k es entrada de la pieza k | si vale, M1b es inmediato (kernel por debajo de la pieza) |

M1 = M1a + M1b. **Medido sin fallos** (`m1split_probe.jl`, en `clause_mix.cnf`, `clause_mix_sep.cnf` y las 6 primeras de
`random_small`; R vacío, de un nodo, y de dos y tres nodos al azar):

| parte | estados con ≥ 2 piezas | estados con 1 pieza | fallos |
|---|---|---|---|
| M1a | 12.951 | 4.180 | 0 |
| M1a-todas | 12.951 | 4.180 | 0 |
| M1a-cima | 12.951 | 4.180 | 0 |
| M1b | 20.789 | 4.180 | 0 |
| M1b-entradas | 20.789 | 4.180 | 0 |

La sospecha previa (que M1b-entradas fallaría por la forma de los tríos falsos) era equivocada. Las dos versiones
fuertes se cumplen, así que M1 se divide en dos enunciados más fáciles de atacar:
* **M1a-todas**: en J fijado, fijar la clave de cualquier nodo vivo del paso n no deja el estado inválido.
* **M1b-entradas**: con la clave k fijada, J fijado solo contiene entradas de la pieza k. Queda un kernel por debajo
  de la pieza, que respeta los pins, y M1b se sigue directamente.

Tiempo: ~21 min, porque cada comprobación copia y revisa el estado entero. Pendiente: medir en todo el corpus.

**Formalizado** (`M1Parts.lean`, solo `[propext, Quot.sound]`):
* `M1aAll` (M1a-todas), `M1bBelow` (con la clave fijada, J fijado queda por debajo de su pieza) y `M1bLow` (lo mismo,
  solo para los nodos por debajo del paso n).
* **`m1_of_parts`**: `M1aAll ∧ M1bBelow ⇒ M1`. Un nodo vivo del paso n nombra su fuente (`mid_one_source`). Al fijar su
  clave queda un kernel válido por debajo de la pieza que respeta los pins.
* **`pure_field`, `pure_mid`, `pure_top`, `pure_node`**: las filas del paso n y de la cima de J son puras. Un nodo de
  ellas tiene, campo por campo (owners, padres, hijos), lo que tiene en la pieza de su clave.
* **`m1bBelow_of_low`**: `M1bLow ⇒ M1bBelow`. Con la clave fijada, los nodos de la cima de J fijado cuelgan de ella,
  porque sus padres están fijados, así que también son puros.
* **`readerVerdictW_iff_of_parts`**: el lector decide bajo `M1aAll` y `M1bLow` en cada join.

**Reducciones** (`M1Parts.lean`, solo `[propext, Quot.sound]`):
* **`m1bLow_of_own`**: `M1bLowOwn ⇒ M1bLow`. `M1bLowOwn` pide solo los owners (la forma que mide la sonda). Un padre
  (hijo) de un nodo del estado fijado es una entrada de su tabla en el paso de al lado (`linkP`, `linkS`). La pieza
  tiene esa entrada, y en la pieza una entrada del paso de al lado es padre (hijo) (`parent_of_owner`,
  `son_of_owner`, con `piece_pinCtx`: una pieza válida es un estado alcanzable con su `PinCtx`). **Los padres y los
  hijos ya no hacen falta medirlos.**
* **`m1aAll_of_keyTri`**: `KeyTri ⇒ M1aAll`. `KeyTri`: en J fijado en R válido, toda clave viva del paso n tiene un
  nodo x con `TriPin` (la regla de parejas con x como tercer miembro fijo). El subkernel de x (`restrict_kernel`)
  queda por debajo de J fijado, respeta R y solo nombra la clave en el paso n.
* `readerVerdictW_iff_of_own` (bajo `M1aAll` y `M1bLowOwn`) y **`readerVerdictW_iff_of_keyTri`** (bajo `KeyTri` y
  `M1bLowOwn`).

Sobre `KeyTri`: en el paso n, x es su propia entrada común (`TriPin` en l = n es inmediato), y un nodo del paso n
que posee x es x (OOS). Por `triPin_of_ambTri`, solo cuentan las parejas ambiguas: y, w que se poseen, poseen x y
también otro nodo del paso n. Son nodos por debajo de n, o de la cima si la clave tiene varios nodos de camino.

* **`m1aAll_of_keyTri₁`**: `KeyTri₁ ⇒ M1aAll`. `KeyTri₁` es `KeyTri` tras una ronda de cortes (`TriPin₁`, `TriPinCut`):
  y, w que poseen x con enlace x-compatible comparten, en cada paso, un testigo que x posee y que es entrada
  x-compatible de los dos. El subkernel cortado (`restrict₁_kernel`) hace el mismo papel.
  `readerVerdictW_iff_of_keyTri₁` (bajo `KeyTri₁` y `M1bLowOwn`).

**Medido** (`keytri_probe.jl`, `m1aall_probe.jl`, con `keytri_common.jl`; `clause_mix.cnf`, `clause_mix_sep.cnf` y las 6 (KeyTri) o 12 (M1aAll) primeras de
`random_small`; R vacío, de un nodo, y de dos y tres nodos al azar):

| enunciado | correctos | fallos |
|---|---|---|
| `KeyTri` | 24.203 | **360** (en todos, M1a-todas vale) |
| `KeyTri₁` | 24.563 | 0 |
| `M1aAll` | 42.463 (25.516 con ≥ 2 claves) | 0 |

**`KeyTri` es FALSO**: en `clause_mix.cnf`, cima 21, clave (20, 0), hay parejas y, w de los pasos 3 a 10 que se poseen
y poseen x, pero sus testigos comunes del paso 3 no los posee x. Es el mismo tipo de fallo que `TriPin` en el lector.
Con una ronda de cortes desaparece: `KeyTri₁` no falla.

**`M1bLowOwn` por la fila de la clave** (`M1bOwn.lean`, solo `[propext, Quot.sound]`; `ktri_probe.jl`). En J fijado en
k :: R solo vive k en el paso n, así que la regla de parejas da a p y v, en cada paso, una entrada común que posee un
nodo de k. Dos formas locales, sobre J fijado en R cualquiera (sin fijar k):
* `KTri`: p y v se poseen y poseen un nodo x del paso n ⇒ v está en la tabla de p en la pieza de x.id.
  **FALSO**: 716 / 2.732 / 40 fallos con R vacío (`clause_mix`, `clause_mix_sep`, 6 de `random_small`). Son los enlaces
  de `KeyTri`: sin testigo común que posea x.
* **`KTriK`**: si además en cada paso tienen un testigo común que posee un nodo de k ⇒ v está en la tabla de p en la
  pieza k. **`m1bLowOwn_of_kTriK`** (`KTriK ⇒ M1bLowOwn`) y `readerVerdictW_iff_of_kTriK` (bajo `M1aAll` y `KTriK`).
  **FALSO también**, aunque mucho más raro: 8 + 56 fallos en `clause_mix` (cima 26, clave (25, 0), p del paso 21, v del
  paso 5), 32 + 544 en `clause_mix_sep`, 0 en `random_small` (≈ 24 M casos en total).

Así que `M1bLowOwn` (que no falla) no sale de ninguna propiedad de J fijado en R leída enlace a enlace: los testigos
que poseen k existen en J, pero la cascada del review tras fijar k corta algunos, y con ellos el enlace. Hace falta un
argumento de punto fijo (el mayor kernel por debajo de J fijado en k :: R), igual que `TriPin` → `TriPin₁` → review.

**Dónde mueren los enlaces de `KTriK`** (`keycut_trace.jl`: rehace el review de J fijado en k :: R operación a
operación). Los 704 fallos (64 en `clause_mix`, 640 en `clause_mix_sep`) caen igual: vuelta 1 del review, dentro de la
regla de parejas. En su ronda 1 se deshacen otras parejas (8 en `clause_mix`, 24 o 32 en `clause_mix_sep`) y la purga
se lleva sus nodos. Con eso p–v pierde sus testigos en algún paso y en la ronda 2 es una pareja mala. Ni el corte
contra padres o hijos ni los enlaces caducados intervienen.

**`KFix`**: la regla de parejas relativa a k, llevada a su punto fijo (`KTriK` es su primera ronda). Un conjunto de
enlaces de J fijado en R es **cerrado para k** (`KClosed`) si cada enlace (a, b) tiene, en cada paso, un testigo r que
posee un nodo de k con (a, r) y (b, r) en el conjunto. `KFix`: todo enlace de un conjunto cerrado para k que sale de
un nodo por debajo del paso n es un enlace de la pieza k.
* **`m1bLowOwn_of_kFix`** (`KFix ⇒ M1bLowOwn`; con k fijada, todos los enlaces forman un conjunto cerrado) y
  **`readerVerdictW_iff_of_kFix`**: el lector decide bajo `M1aAll` y `KFix`.
* **Medido sin fallos** (`kfix_probe.jl`, el mayor conjunto cerrado por iteración): 24.560 pares (estado, clave), 660
  con R vacío; **24,7 M enlaces** comprobados (`clause_mix`, `clause_mix_sep`, 6 de `random_small`).

`KFix` habla solo de J fijado en R y de las piezas, sin el review del estado fijado en k: es la forma coinductiva de
«la unión de piezas es exacta por debajo de la clave».

**`KeyTri₁ ⇐ KeyExact`** (`M1Parts.keyTri₁_of_keyExact`, vía `BranchRel.triPin₁_of_pairExactRel`). `KeyExact`: en J
fijado en R válido, cada clave viva tiene un nodo x tal que todo enlace y–w x-compatible está, con x, en una cadena
(una solución parcial) de J fijado. **Medido sin fallos** (`keyexact_probe.jl`, búsqueda de cadena por nodos poseídos
dos a dos): 25.242.784 enlaces en `clause_mix*` con x en la clave; en `clause_mix`, 3.822.073 con x en la cima,
4.235.930 dos pasos por debajo y 4.114.163 tres pasos por debajo. **La posición de la clave no es lo decisivo**: todo
apunta a `PairExactRel` para todo x en los estados unidos fijados. No choca con los 20 tríos sin cadena de §4.2ο:
allí los testigos no los posee también x.

**`PairExact` con pins, medido sin fallos** (`pairexact_probe.jl`): todo enlace y–w de J fijado en R está en una
cadena de J fijado en R. 5.426.185 enlaces en `clause_mix*`. Con él, `KeyExact` se reduce a que un enlace
x-compatible sobreviva al fijar la ventana de x (la cadena de J fijado en R + ventana de x pasa por x y baja a J fijado
en R). Eso es otra vez `TriPin₁` (el subkernel cortado queda por debajo del estado fijado), así que no cierra el
círculo. `PairExact` sin pins lo conservan el review, el join y `addNode` sin ventana saltada (`BranchFull`); lo
abierto es el filtro por pins.

**`KeyTri₁` partido en el join** (`KeyCone.lean`, solo `[propext, Quot.sound]`; `triPin₁_of_below` sin axiomas):
* **`triPin₁_of_below`**: si Π está por debajo de K, `TriPin₁ Π x` y todo enlace x-compatible de K ya es x-compatible
  en Π (**`CxPull`**), entonces `TriPin₁ K x`.
* **`keyTri₁_of_split`**: `KeySplit ⇒ KeyTri₁`, con Π = la pieza de la clave fijada en R (un kernel por debajo de J
  fijado, `below_filterAll`). `KeySplit` = Π válida, `TriPin₁ Π x` y `CxPull`. `readerVerdictW_iff_of_split`.
* **Medido sin fallos** (`keysplit_probe.jl`, `clause_mix*`): 8.115 claves; Π válida, `TriPin₁(Π, x)` y `CxPull`
  en todas.
`CxPull` es la mezcla del join en su forma mínima; `TriPin₁ Π x` habla de una sola pieza, con x en la cima de la
fuente. Π válida es M1 para esa clave (`M1aAll` + M1b), así que `KeySplit` no rompe el círculo; separa las partes.

Demostrar `KeyExact` pide exactitud por cadenas a través del join con pins: los testigos de un enlace x-compatible de
J fijado pueden venir de piezas distintas, y la cadena tiene que estar en una sola (`chain_in_piece`). Es el núcleo de
M1 (`BranchRel.JoinChoice`, ahora con pins), no un atajo.

**Abierto**: `M1aAll` (vía `KeyTri₁ ⇐ KeyExact`) y `M1bLowOwn` (vía `KFix`, medido sin fallos; `KTri` y `KTriK` falsos).

**`KFix` es `M1bLowOwn` otra vez** (`KFixCore.lean`, `wk_probe.jl`).
* **Demostrado** (solo `[propext, Quot.sound]`): `witness_key` (en un conjunto cerrado para k, el testigo de la fila
  de claves es un nodo de k), `pure_link` (un enlace hacia un nodo puro está en la pieza), **`kFix_of_low`**
  (`KFixLow ⇒ KFix`: solo cuentan los enlaces entre filas de abajo) y `readerVerdictW_iff_of_kFixLow`.
* **Deducido:** el mayor conjunto cerrado para k, W_k, es un kernel por debajo de J fijado en R que solo nombra k en
  la fila de claves.
  * Es simétrico (el testigo de (a, b) sirve para (b, a)) y admite los lazos (a, a).
  * Su testigo en el paso de al lado es un padre o un hijo (`parent_of_owner`), lo que da las cláusulas de vecinos.
  * Por `below_filterAll`, W_k está dentro de K_k = J fijado en k :: R. Y K_k es cerrado para k, así que K_k ⊆ W_k.
  * Por tanto **W_k = K_k**, y `KFix` equivale a `M1bLowOwn`: no es una vía independiente.
* **Medido:** W_k = K_k en 19.763 casos de 19.763 (`clause_mix` y 6 de `random_small`).
* **Qué queda:** demostrar `M1bLowOwn` en sí, es decir, que el kernel de J fijado en la clave k está dentro de la
  pieza k. Truncando la cima (`Trunc.kernel_trunc`) es un kernel por debajo de la unión de las fuentes filtradas F_j,
  cuya fila de arriba solo tiene nodos de F_k. La pregunta es si está por debajo de F_k.

**La forma truncada de `M1bLowOwn`: se reduce a partir el kernel por la fila de debajo** (deducido;
`split_probe.jl`). Sea K = J fijado en k :: R, sin la cima. K es un kernel por debajo de la unión de las fuentes
filtradas F_j, y su fila n solo tiene nodos de k.
1. **K respeta los requisitos de k.** Un nodo de K en el paso de un requisito de k posee un nodo de k de la fila n, que
   es puro. Así que el primero está en la fuente X_k, donde ese paso solo tiene el nodo requerido. K también respeta los
   requisitos del destino d.
2. **Basta que las tablas de abajo de K estén en X_k** (`M1bSrc`). Por `below_filterAll`, K queda entonces por debajo de
   F_k, y con la cima pura por debajo de la pieza P_k.
3. **X_k es la unión de las piezas Q_{k,i}** de la línea anterior, una por clave i de la fila n-1. Todas salen del mismo
   estado W_i y solo difieren en el filtro de requisitos. Así que el paso 2 pide dos cosas:
   * **CoverSplit(n-1):** K es la unión de sus fijaciones por la fila n-1: todo enlace de K está en K_{k,i} = J fijado en
     k :: i :: R, para alguna clave i.
   * **El mismo enunciado un nivel más abajo**, con dos claves fijadas: las tablas bajo la fila n-1 de K_{k,i} están en
     W_i. Después, por el paso 1 con los requisitos de k, están en Q_{k,i} ⊆ X_k.
   La inducción baja fila a fila hasta el paso 0, donde todo está fijado. **Solo queda como hipótesis CoverSplit en
   cada fila.**

**Pasos 1 y 2, demostrados** (`M1bSrc.lean`, solo `[propext, Quot.sound]`):
* **`key_reqs`** (paso 1): J fijado en k :: R respeta los requisitos de k. Usa `node_in_piece` (todo nodo de K hasta la
  fila de claves es nodo de la pieza y de la fuente filtrada) y `line_node_req` (un nodo de un estado de línea, en el
  paso de un requisito de su clave, nombra el requisito).
* **`m1_of_src`** (paso 2): **`M1aAll ∧ M1bSrc ⇒ M1`**. `M1bSrc` pide que las tablas de las filas de abajo de K (con
  entradas hasta la fila de claves) sean tablas de la fuente X_k. Entonces K sin la cima es un kernel por debajo de
  X_k que respeta `pinsW` (requisitos de d, y `L1 = 1` si hay ventana saltada) y los pins de R bajo la cima. X_k fijado
  ahí es válido, y M3w (`piece_of_src`) sube a la pieza.
* **`readerVerdictW_iff_of_src`**: el lector decide bajo `M1aAll` y `M1bSrc` en cada join.

Frente a `M1bLowOwn`, `M1bSrc` compara con la fuente sin filtrar, y la pieza la pone la prueba. Es la forma que admite la
inducción hacia abajo con CoverSplit.

**Paso 3, primer nivel, demostrado** (`M1bDeep.lean`, solo `[propext, Quot.sound]`): **`m1bSrc_of_cover`**:
`CoverSplit ∧ M1bDeep ⇒ M1bSrc`, y `readerVerdictW_iff_of_cover` (el lector decide bajo `M1aAll`, CoverSplit y
`M1bDeep`).
* `CoverSplit` (versión formal): toda entrada (p, v) de K con p por debajo de la fila n-1 y v por debajo de la fila n
  está en J fijado en k :: i :: R, con esa fijación válida, para alguna clave i de la fila n-1.
* **`M1bDeep`**: en J fijado en k :: i :: R, las entradas (p por debajo de la fila n-1, v por debajo de la fila n)
  son entradas de la pieza Q_{k,i} = `upF` W_i k, la de la línea anterior que entró en X_k. Es `M1bSrc` una fila más
  abajo. **Medido sin fallos:** 11.281.468 entradas (`m1bdeep_probe.jl`; `clause_mix` y 6 de `random_small`).
* La prueba separa (p, v) en tres casos:
  * v en la fila n: nodo de la clave, puro, así que su tabla es la de la fuente;
  * p por debajo de n-1: CoverSplit y `M1bDeep`, y después Q_{k,i} está por debajo de X_k (`piece_grown`);
  * p en la fila n-1: v = p, o la entrada simétrica (v, p).

**La forma de cadena, demostrada** (`NodeHistory.lean`, `UpSelf.lean`, `TruncN.lean`, `M1bChain.lean`; 0 `sorry`, solo
`[propext, Quot.sound]`). El esquema del «siguiente nivel» de abajo, hecho de una vez para todas las filas:
* **`node_history`**: un nodo y de un estado de la línea N, en la fila m ≤ N, es nodo del estado de la línea m en
  `y.id`, con menos padres y, hasta la fila m, con menos entradas. Sustituye a la pureza, que solo vale en las dos
  filas de arriba de un estado unido.
* **`below_up_trunc`**: un kernel cuya fila de arriba es de un solo nodo de mapa d está por debajo del `up` a d de su
  propia truncación. Los nodos nuevos poseen lo que poseen sus padres, sus padres son los que se desplazan a ellos, y
  los nodos viejos ganan los nuevos que los poseen.
* **`TruncN`**: cortar un estado hasta una fila conserva su contexto (`good_truncN`); `below_of_owners` (tablas dentro
  de tablas dan `Below`).
* **`SrcAt n m`**: J fijado en L, con la clave de un estado S de la línea m en L, tiene las entradas (nodo por debajo
  de m, entrada hasta m) dentro de S. **`srcAt_succ`**: `SrcAt n m ∧ CoverRow n (m+1) ⇒ SrcAt n (m+1)`:
  * las entradas hacia un nodo de la clave salen de la historia;
  * para el resto, `CoverRow` añade una clave j de la fila m, con su estado W. El estado fijado también en j,
    cortado hasta la fila m+1, está por debajo:
    * del `up` de su corte (`below_up_trunc`);
    * de W filtrado para k (por `SrcAt n m`, la historia y los requisitos de k, que están fijados en S);
    * de la pieza Q = `upF` W k, y por tanto de S.
* `SrcAt n 0` vale sin más; `SrcAt n n` es `M1bSrc`.
* **`readerVerdictW_iff_of_chain`: el lector decide `φ` bajo `M1aAll` y `CoverRow` en cada fila de cada join.**

`M1bLowOwn` queda así reducido a una sola propiedad por fila, **CoverRow** (el estado fijado es la unión de sus
fijaciones por la fila de debajo). Junto con `M1aAll`, son las únicas hipótesis del lector.

**`CoverRow` medido en todas las filas sin fallos** (`coverrow_probe.jl`; `clause_mix` y 3 de `random_small`; R al
azar, cada fila 2 ≤ m ≤ n y cada clave viva de la fila m):

| filas | entradas | fallos |
|---|---|---|
| m < n | 27.948.768 | 0 |
| m = n | 5.213.722 | 0 |

**Siguiente nivel** (propuesto; ya cubierto por la forma de cadena de arriba): `M1bDeep` ⇐ CoverSplit en la fila n-2 ∧ el mismo enunciado con tres claves ∧ subir de
W_i a Q_{k,i}. Subir de W_i a Q_{k,i} usa `key_reqs` para los requisitos de k, y el argumento de la fila nueva del `up`:
un nodo nuevo posee la unión de las tablas de sus padres. A diferencia del primer nivel, las filas bajas de J no son
puras, así que la entrada hacia la fila nueva tiene que salir del kernel y no de la pureza. Iterado hasta la fila 0,
donde todo está fijado, deja **`M1aAll` y CoverSplit en cada fila** como únicas hipótesis.

**Medido sin fallos** (`clause_mix`, `clause_mix_sep` y 6 de `random_small`):

| enunciado | casos | fallos |
|---|---|---|
| LinkSplit: todo enlace de filas bajas de K es compatible con algún nodo de la fila n-1 | 20.262.014 | 0 |
| **CoverSplit**: todo enlace de filas bajas de K está en K_{k,i} para alguna clave i | 23.310.243 | 0 |
| PartValid: fijar además cualquier clave viva de la fila n-1 deja el estado válido | 32.360 | 0 |

**Lectura.** Todas las rutas acaban en el mismo núcleo: **el kernel de un estado fijado es la unión de sus fijaciones
por cualquier fila de claves** (exactitud de la unión, fila a fila).
* CoverSplit en la fila n es M1 en forma de enlaces.
* CoverSplit en todas las filas lo da `PairExact` con pins: un enlace que está en una cadena elige un nodo en cada fila.
* `M1aAll` es la parte de validez: si K tiene enlaces, CoverSplit da una fijación válida.

`M1bLowOwn` pide CoverSplit en las filas de abajo; `M1aAll`, en la fila de claves.

**Las reglas de la fila de claves** (v196; `KeyRules.lean`, solo `[propext, Quot.sound]`; ⚠ retirado del código, queda en la historia: commit `82c121f`, merge `e0be7a3`). Etiqueta de clave
(`restrictTo` con la pieza) y comprobación de claves (`reviewKC`), como operaciones nuevas del modelo; filtro
`filterKC`. Implementadas en Julia en la rama `julia_key_rules`.
* **`m1_keyRules`**: con las dos reglas, M1 vale en el join donde actúan. `below_piece` es `M1bLowOwn` por
  construcción.
* **`below_reviewKC`**: el review con la comprobación no baja de un kernel cerrado por claves (`KeyClosed`).
  **`isValid_filterKC_of_kernel`**: el análogo de `isValid_filterAll_of_kernel`.
* **No cierran la inducción** (deducido, v196 §6.2): `lExt_succ` baja a las fuentes, que son estados unidos, y con
  etiquetas de un nivel el kernel de la pieza no respeta las etiquetas de la fuente. Harían falta etiquetas de todos
  los niveles. `M1aAll` sigue abierto con o sin reglas.

### 4.3 Buscar el invariante de historia (el trabajo de fondo)

Hay que elegir una propiedad de las tablas que (a) implique `AmbHigh` y (b) conserven `addNode`, `join`,
`filterRequire` y el review. Tres candidatos, de más a menos prometedor según lo que sabemos:

* **Tablas descomponibles por bit** (visión de subconjuntos de caminos). **Propuesto.**
  * La tabla de un nodo ambiguo `y` es la unión de dos secciones, `S_y^0` y `S_y^1` (entradas
    compatibles con cada bit de `k`).
  * La regla de parejas vale **dentro de cada sección**: si `w ∈ S_y^b`, entonces `S_y^b ∩ S_w^b` es no
    vacío en cada paso.
  * Es `TriPin` para todo `x` a la vez, así que implica `AmbHigh` directamente. La pregunta es si la
    máquina lo conserva. El UP hereda las tablas de los padres por unión, que respeta secciones. Lo
    delicado es la intersección del review contra vecinos y `join`.
  * Formalizarlo como `SecPair g k` y atacar primero `addNode` (el caso de un nodo nuevo por encima de
    `k`).
  * **Medido como regla del review** (28-sept-2026, `probe_tri_sec.jl`, mismas 88 instancias que §4.4).
    Hay dos modos: `sec` hace una sección por nodo del mapa de `k`, y `secx` una por nodo del camino.
    Los dos cortan **0 aristas**, y son unas 3,5 y 5 veces más lentos. `SecPair` ya vale en los estados
    de la máquina: no hace falta como regla, pero sí como **lema** que el review actual cumple.
  * **La sección es el pin** (28-sept-2026, `julia/improves_bingo/test_3sat/probe_sec_vs_pin.jl`). En cada
    estado del lector (1 615 estados, todas las ramas, 88 instancias) y en cada paso con elección, se compara la
    sección de cada nodo del mapa `b` con las aristas que deja `filter!(b)` (el review entero). **17 158 de
    17 158 son iguales**: 0 veces mayor la sección, 0 aristas del pin fuera de ella, 0 pins muertos con
    sección no vacía. No es trivial: en `clause_mix`, el pin baja de 2 991 aristas a entre 359 y 2 058.
  * Así, tras un pin, el review se reduce a restringir y hacer el punto fijo de parejas; padres, hijos y
    enlaces no cortan nada más. `SecPair` es literalmente «el grafo es la unión de sus pins en cada paso con
    elección». Con `PinEqSec` (el pin de `b` es la mayor sección de `b`), `SecDeadEnd` es inmediato: toda
    arista está en alguna sección no vacía, así que su pin es válido.
  * **Por qué sobrevive la sección** (`SecInPin`; `julia/improves_bingo/test_3sat/probe_secinpin.jl`, las mismas
    17 158 comparaciones). Durante el review de los pins, lo que corta es la purga (19,8 M aristas, al quitar
    nodos), la regla de parejas (19 970) y los enlaces (515 enlaces). **Las pasadas de padres e hijos no cortan
    nada** (0 y 0), y ninguna regla toca la sección (`s_hit` = 0).
  * Antes del pin, cada sección está **cerrada por las reglas de estructura**, con 0 fallos:
    * todo nodo de la sección (no raíz, no cima) tiene un padre y un hijo enlazados dentro de ella;
    * toda arista `(x, w)` de la sección tiene un padre de `x`, dentro de ella, que posee a `w` (y lo mismo con los
      hijos).
  * Así, `SecInPin` es la generalización de `carried_review` de una camarilla a una sección: una estructura
    cerrada por parejas, por enlaces y por apoyo sobrevive a cada operación del review. El trabajo es demostrar que
    la mayor sección de `b` hereda esos cierres de un estado del lector.
  * **Demostrado** (`lean/improves_bingo/AbsSatBingo/Model/SecStruct.lean`): `secStruct_review` y
    `secStruct_filterAll`, el review y el pin conservan toda `SecStruct` (parejas, enlaces, y apoyo con `R x p` y
    `R p w`). Con ellos, `secInPin_of_secStructAt`: `SecInPin` se reduce a **`SecStructAt`**, que toda sección de
    `b` se extienda a una `SecStruct` que concuerde con `b`. Medido con el apoyo reforzado (`R x p` y `R p w`):
    0 fallos en las 17 158 secciones.
  * **Inducción a lo largo del lector** (`SecInduction.lean`). Demostrados el esqueleto (`secPair_visited`,
    `noDeadEnd_visited`) y el paso condicional `secPair_filterAll`: `SecPair` en `h` más `SecMeet` dan `SecPair` en el
    pin de `b`. `SecMeet` pide que la intersección de las secciones de `b` y de `b'` sea una sección de `b'` en el pin.
    **`SecMeet` es FALSO** (`probe_secmeet.jl`): 21 044 casos en 13 de 22 instancias, incluida `basic_v3_c1`, con
    2,3 M aristas que faltan; la inclusión contraria vale siempre. `SecPair` sigue valiendo en el pin (0 cortes), pero
    la cubre **otro** `b''`: al fijar `b`, cambia la sección que cubre cada arista. El paso no es local por
    intersección; hace falta otro invariante o un argumento directo en cada estado fijado.
  * **Qué sección cubre una arista tras el pin** (`probe_seccover.jl`, hasta 60 estados por instancia, 88
    instancias, 139,7 M pares arista × paso). `SecMeet` falla en 4,49 M (3,2 %).
    * El 92,6 % de esos fallos son solo porque el `b''` que la cubría muere en el pin.
    * Pero **`SecMeetAlive` también es falso**: 330 507 casos en los que un `b''` que la cubría y sigue vivo ya no la
      cubre, en 17 instancias, incluida `basic_v3_c1` (8).
    * Tampoco vale «toda ancla cubre»: en `h`, la cubren todas las anclas en el 99,88 % de los casos, no en todos.
    * `SecPair` en el pin sigue sin fallos (`empty_h2` = 0).
    * Conclusión: fijar `b` rompe compatibilidades entre una arista y otro `b''` vivo, que es un efecto de tríos
      (`b`, `b''`, arista). Es la reserva de §4.4 («cada pin sube un nivel»), que vuelve a aparecer en forma de
      secciones. El paso no se reduce a ninguna de las tres formas locales medidas.
  * **`SecPair` con pins cualesquiera** (`probe_secpair_anypin.jl`, 30 paseos al azar por instancia desde el estado
    final, pins en cualquier paso con elección y en cualquier orden, uno de cada tres movimientos doble, y el review
    entero tras cada pin).
    * Por nodo del mapa: 5 027 estados, 6 891 pins, 145 dobles: **0 fallos de `SecPair`/`SecPairX`, 0 pins muertos**.
    * Por nodo del camino (se deja vivo solo `x` en su paso): 4 552 estados, 8 022 pins, 53 dobles: **0 fallos,
      0 pins muertos**. Todo nodo vivo, fijado, deja el estado válido.
    * No es una propiedad de los estados del lector: vale en todo estado revisado que sale de la máquina por pins.
      La prueba debería ir por el punto fijo del review sobre la salida de la máquina, no por una inducción a lo
      largo del lector.
  * **`SecPair` durante la ejecución de la máquina** (`probe_secpair_machine.jl`): después de cada paso, en cada
    gpath de la línea (10 006 gpaths, 7 570 con algún paso con elección, 88 instancias), **0 fallos** de `SecPair`,
    de `SecPairX` y del cierre por parejas. Es un invariante de la máquina medido, no solo del estado final: la
    inducción natural va a lo largo de la máquina (UP, join y filtro seguidos del review).
* **`PairExact` conservado por el pin** (propuesta B del v191). Da `TriPin` directamente si el pin no
  rompe la exactitud por parejas. Riesgo: en bin ya no existe la escalera débil sobre la que se medía.
* **Inducción a lo largo del lector.**
  * Tras pinchar `x` en `k`, el siguiente estado tiene `x` forzado, que por §4.1 está en todas las
    tablas.
  * `AmbHigh` en el estado siguiente habla de tríos por encima de `k'` > `k`, con `x` implícito en
    todas las tablas.
  * Puede permitir heredar la propiedad del estado anterior en lugar de pedirla de la máquina. Hay que
    comprobar si la cláusula necesaria no crece a cuartetos (ver 4.4).

### 4.4 Cambiar el algoritmo: una regla de tríos en el review (creativo)

**Propuesto, con reserva.** Añadir al review una pasada «de tríos».

**Corrección (28-sept-2026).** La primera redacción era: si `y`, `w`, `x` se poseen dos a dos y en un paso
`l` no tienen entrada común, se quita `w` de la tabla de `y`. **Esa regla pierde soluciones.** Una solución
por `y` y `w` que no pasa por `x` no da ninguna entrada común a los tres, y aun así el enlace `y–w` es
suyo. El trío sin entrada común solo dice que ninguna solución pasa por los **tres**, y eso no permite
cortar ninguna de sus tres aristas. La forma sólida cuantifica `x` por paso:
* **Regla de tríos (sólida).** El enlace `y–w` sobrevive si **en cada paso `m`** hay un `x` que posee a los
  dos y tal que `x`, `y`, `w` comparten entrada en cada paso `l`. En `m` = paso de `y` o de `w` basta
  `x = y` o `x = w`, que es la regla de parejas.
* **No pierde soluciones:** el nodo de la solución en `m` hace de `x`. Se prueba como `no-solution-lost`
  de la máquina `improves`.
* **Lo que da:** su punto fijo es consistencia de tríos por caminos (un nivel más que la regla de
  parejas). **No** da `TriPin` para todo `x`, solo para los `x` que son testigos. `TriPin` para todo `x`
  era la consecuencia de la regla que no es sólida, y §4.2 ya la descarta: en `simple3sat_v3_c2`, `TriPin`
  falla con un pin que sobrevive. Queda por ver si basta para `NoDeadEnd`.
* **Medida (28-sept-2026, `julia/improves_bingo/test_3sat/probe_tri_sec.jl`, máquina bingo).** Son 88
  instancias: el corpus de Julia más `lean/improves_bin/cnf/crafted`, sin `tseitin_petersen_H`. La regla
  va dentro del review, hasta su punto fijo, y después se recorre el lector por todas sus ramas.
  * Modo `tri`: **0 aristas cortadas**, en la máquina y en el lector. Veredictos y soluciones iguales
    que en la base, y 8,4 veces más lento.
  * El review actual ya está cerrado por tríos sólidos. Los fallos de `TriPin` (3 542 tríos en 10
    instancias, 264 en `clause_mix`) tienen siempre **otro** `x` del mismo paso que cierra el trío.
  * En la base, además, **0 pins muertos y 0 callejones** en todas las ramas del lector, y las hojas
    coinciden con las soluciones del exhaustivo (sin truncar). `NoDeadEnd` vale en todo el corpus.
* **La reserva.** Para que el estado pinchado vuelva a estar cerrado por tríos, `restrictPin` tendría
  que estarlo. Eso pide cuartetos en el estado anterior, y cada pin sube un nivel de consistencia.
* La observación de §4.1 lo mitiga en parte: los nodos forzados están en todas las tablas, así que el
  cuarto miembro de un cuarteto que es un pin anterior es gratis.
* Falta ver si basta: el cuarteto real es `y`, `w`, `v` (por encima) con `x` (el pin nuevo), y `x` aún
  no está forzado en el estado anterior.
* Coste: de `O(pares)` a `O(tríos)` por paso. Merece medirlo en Julia antes de formalizar.

### 4.5 Deudas laterales (no bloquean `AmbFar`)

* **`RootValid`** (el review no mata el estado final, el caso de cero pins). Hace falta para la solidez
  de la máquina por la ruta `NoDeadEnd`. **Abierto.**
* **`SkipExact` / `SkipChainBin`**, por la ruta original de `soundness_pure`. **Abierto**; la ruta
  `NoDeadEnd` lo evita.
* Diferencial de estados Lean vs Julia; el modelo en listas es lento.

## 5. Orden recomendado

0. **M1 (§4.2ο.1, §4.2ο.2)**, la única hipótesis que queda del lector: un kernel válido fijado del estado unido deja uno
   válido con los mismos pins en alguna pieza. M2w, M3w, la inducción y M1 ⇐ `CertPin` ya están demostrados. Siguiente:
   M1 = M1a + M1b según la medición; empezar por M1b si M1b-entradas vale. No construir
   sobre `CertClique`/`FCert` de estados de línea, que son falsos en `clause_mix*`.
1. **Línea de investigación (§4.2μ):** un invariante semántico por testigos: qué garantiza, desde la historia, que una
   clique con testigos en todos los pasos esté respaldada por una solución parcial. Empezar con sondas (¿bastan los testigos
   de los pasos de cláusula, H19?).
2. Atacar `PieceLocalF` y `MergeSplit` como un solo enunciado: «una clique con testigos se queda en un lado de dos
   fijaciones complementarias» (en el join: la clave; en la fusión: el abuelo). La selección la hace la clique entera
   (H19/B1: los testigos de los `L3`).
3. Las reducciones antiguas bajo `MapCert` (`LineUnion`, `FilterUnion.filter_union`, `GrowCert`) siguen siendo
   implicaciones correctas, pero su hipótesis es falsa en el estado unido; no construir encima.

## 6. Mapa de ficheros (todos en `lean/improves_bin/AbsSatBin/GraphPath/Model/`)

| fichero | teoremas clave |
|---|---|
| `ReaderExec.lean` | `readerVerdictW`, `readG`, `readLoop`, `firstChoice`, `readerVerdictW_sound` |
| `ReaderPrefix.lean` | `ReadFirst`, `ProgressFirst`, `PrefixUpTo`, `prefixUpTo_firstChoice`, `firstChoice_pin_gt`, `PinChain` |
| `PinChainBin.lean` | `OtherBit`, `pinChain_of_otherBit`, `chainG_through_pin` |
| `OtherBitSem.lean` | `ReadPins`, `OtherBitSem`, `carried_unique` |
| `NoDeadEnd.lean` | `NoDeadEnd`, `otherBitSem_of_noDeadEnd`, `RootValid`, `soundness_of_noDeadEnd` |
| `SymMachine.lean`, `PairInactive.lean` | `CutClosed`, `symInv_reachable`, `reviewAgg_eq_review` |
| `Kernel.lean`, `KernelReader.lean` | `Kernel`, `Below`, `below_review`, `kernel_readPins`, `KernelSplit` |
| `KernelIff.lean` | `sonsSub_review`, `kernelSplit_iff_noDeadEnd` |
| `KernelSplit.lean` | `TriPin`, `PinCtx`, `restrictPin`, `restrict_kernel`, `parent_of_owner`, `TriPinReader` |
| `TriPinCore.lean` | `Exclusive`, `excl`, `tri_of_exclusive`, `AmbTri`, `triPin_of_ambTri` |
| `AmbTriCore.lean` | `ACtx`, `gowner_eq`, `share_below`, `excl_near`, `AmbFar`, `ambTri_of_ambFar`, `readerVerdictW_iff_of_ambFar` |
| `AmbHighCore.lean` | `forced_in_all`, `forced_owns_all`, `AmbHigh`, `ambFar_of_ambHigh`, `readerVerdictW_iff_of_ambHigh` |
| `PieceJoin.lean`, `StatePiece.lean`, `StateLine.lean` | `PieceLocal`, `chain_in_piece`, `mapCert_skip`, `skip_window`, `mapCert_line`, `readerVerdictW_iff_of_pieceLocal` |
| `ChainRoute.lean` | `supported_join`, `readerVerdictW_iff_of_chains`, `combined_invariant` |
| `PieceFilter.lean` | `piece_survives_filter`, `filter_in_piece`, `entryOnChain_of_mapCert`, `mapCert_filter_pin` |
| `GrowCert.lean` | `GrowR`, `growR_iff_mapCert`, `growR_join` |
| `KernelUp.lean` | `kernel_addNode`, `kernel_up`, `kernel_join`, `kernel_reachable`, `aCtx_line`, `growR_iff_mapCert_line` |
| `Trunc.lean` | `trunc`, `kernel_trunc` |
| `LineUnion.lean` | `GL`, `GLF` (⚠ refutados con restricción en la cima), `certR_top_of_GLF`, `certR_low_of_GLF`, `mapCert_next_F` |
| `FilterUnion.lean` | `mapCert_filter_pins`, `filter_union`, `piece_pinned_below` |
| `FiltCert.lean` | `FCert`, `fCert_join`, `PieceLocalF`, `cert_piece_low`, `single_parent`, `gparent_owner`, `TopParent`, `TopMerge`, `MergeSplit`, `readerVerdictW_iff_of_mergeSplit` |
| `AnchorPiece.lean` | `AnchorF`, `TopPieceF`, `pieceLocalF_of_anchor`, `topPieceF_of_luaJ`, `merge_pin`, `topParent_of_afp`, `ULUA`, `LUAJ`, `climb`, `line_one`, `anchorF_zero` |
| `UnionLine.lean` | `lineU`, `UCtx_join`, `line_old`, `trunc_below`, `LUAU`, `luau_succ`, `climbE`, `afu_of_luau`, `anchorF_of_a1k`, `fCert_luau_line`, `readerVerdictW_iff_of_luau` |
| `Splice.lean` | `splice`, `CertUpTo`, `SuffixSplit`, `certUpTo_succ`, `certClique_of_splits`, `readerVerdictW_iff_of_splits` |
| `JoinTri.lean` | `cxP_grown`, `JoinChoiceP`, `cliqueTri_of_joinChoice`, `joinChoice_nil`, `JoinChoicePF` (⚠ falso), `fCert_join_of_choice`, `readerVerdictW_iff_of_joinChoice` |
| `UpMono.lean`, `PieceBridge.lean` | `below_addNode`, `src_of_piece` (M2w), `piece_of_src` (M3w) |
| `FExtInd.lean` | `LExt`, `M1`, `readAny_track`, `fExt_of_lExt`, `lExt_low`, `lExt_succ`, `lExt_line`, `readerVerdictW_iff_of_m1` |
| `M1Parts.lean` | `M1aAll`, `M1bBelow`, `M1bLow`, `M1bLowOwn`, `KeyTri` (⚠ falso), `KeyTri₁`, `m1_of_parts`, `pure_node`, `m1bBelow_of_low`, `piece_pinCtx`, `m1bLow_of_own`, `m1aAll_of_keyTri`, `m1aAll_of_keyTri₁`, `readerVerdictW_iff_of_parts`, `readerVerdictW_iff_of_keyTri₁` |
| `M1bOwn.lean` | `KTri` (⚠ falso), `KTriK` (⚠ falso), `KClosed`, `KFix`, `m1bLowOwn_of_kTriK`, `m1bLowOwn_of_kFix`, `readerVerdictW_iff_of_kFix` |
| `KeyCone.lean` | `CxPull`, `cx_up`, `triPin₁_of_below`, `KeySplit`, `keyTri₁_of_split`, `readerVerdictW_iff_of_split` |
| `KeyRules.lean` (⚠ retirado; en la historia, `82c121f`) | `restrictTo`, `reviewKC`, `filterKC`, `pieceOf`, `kc_spec`, `below_piece`, `m1_keyRules`, `KeyClosed`, `TagBelow`, `below_reviewKC`, `isValid_filterKC_of_kernel` |
| `KFixCore.lean` | `KFixLow`, `witness_key`, `pure_link`, `kFix_of_low`, `readerVerdictW_iff_of_kFixLow` |
| `M1bSrc.lean` | `M1bSrc`, `line_node_req`, `node_in_piece`, `key_reqs`, `line_pinCtx`, `m1_of_src`, `readerVerdictW_iff_of_src` |
| `M1bDeep.lean` | `CoverSplit`, `M1bDeep`, `m1bSrc_of_cover`, `readerVerdictW_iff_of_cover` |
| `NodeHistory.lean` | `piece_node_src`, `node_history` |
| `UpSelf.lean` | `Ctx`, `shift_parent`, `top_newRow`, `below_up_trunc` |
| `TruncN.lean` | `Good`, `good_trunc`, `truncN`, `good_truncN`, `truncN_node_inv`, `truncN_node_of`, `below_of_owners` |
| `M1bChain.lean` | `SrcAt`, `CoverRow`, `hist_key`, `srcAt_succ`, `srcAt_all`, `m1bSrc_of_srcAt`, `readerVerdictW_iff_of_chain` |
| `M1Sem.lean` | `isValid_of_chainSound`, `CertPin`, `m1_of_certPin`, `readerVerdictW_iff_of_certPin` |
| `MapTri.lean` | `ReadAny`, `FExt`, `progressFirst_of_fExt`, `readerVerdictW_iff_of_fExt`, `KExt`, `kernel_readAny`, `fExt_of_kExt`, `readerVerdictW_iff_of_kExt` |

Sondas: `lean/improves_bin/OtherBitProbeMain.lean` (exe `otherbit-probe`, `--chain`, `--cap N`); Julia en
`julia/improves_bin/test_3sat/probes/` (`decompress`, `lift`, `grow_step`, `kernel`, `global_local`, `dest`, `glpin`,
`glfstar`, `select`, `gltop`, `verdict_brute`, `supported`, `twenty`, `joint`, `key`, `certj`, `fcert`, `fcert_any`,
`djf`, `toppar`, `mergesplit`; de §4.2ο: `joinchoice_exh`, `absent`, `absent_sem`, `triple_sem`, `joinpin`, `fext`,
`fextind`, `m1split`, `keytri`, `m1aall`, `keyexact`, `pairexact`, `keysplit`, `ktri`, `keycut_trace`, `kfix`).
