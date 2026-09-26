# `AmbFar`: dónde está la escalera del lector sin retroceso (mapa bin) y cómo seguir

> Proyecto `lean/improves_bin`, rama `lean_improves_bin`, hasta el commit de `AmbHighCore` (peldaño 10).
> Cada pieza va marcada como **demostrado** (teorema Lean, 0 `sorry`, solo `[propext, Quot.sound]`),
> **medido**, **deducido** (argumento en papel, sin formalizar), **propuesto** o **abierto**.
> Informe de referencia: `docs/bitacora/verificacion_inseguridad_autor_v194.md` (hasta `TriPin`/`AmbTri`).
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
  construyan `addNode` y `join` y que lo conserven el review y el pin. **Sin medir** para `x` fuera de la
  primera elección (solo se midió en `firstChoice`).

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

**Propuesto, con reserva.** Añadir al review una pasada «de tríos»: si `y`, `w`, `x` se poseen dos a dos y
en un paso `l` no tienen entrada común, se quita `w` de la tabla de `y` (y viceversa).
* No pierde soluciones: una solución da la entrada común en cada paso. Se prueba como `no-solution-lost`
  de la máquina `improves`.
* En su punto fijo, `TriPin` vale **para todo `x`**, así que el pin en `k` siempre sobrevive **un paso**
  (peldaño 7).
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

1. ~~§4.1: `AmbFar ⇐ AmbHigh`~~ — hecho.
2. §4.2: medir `AmbHigh` en Julia. Decide entre §4.3 y §4.4: si nunca falla, buscar el invariante; si
   falla para un bit pero no para los dos, el invariante tiene que ser por bit; si falla para los dos,
   la máquina actual no basta y toca §4.4.
3. §4.3: formalizar `SecPair` y atacar su conservación por `addNode`.

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

Sondas: `lean/improves_bin/OtherBitProbeMain.lean` (exe `otherbit-probe`, `--chain`, `--cap N`).
