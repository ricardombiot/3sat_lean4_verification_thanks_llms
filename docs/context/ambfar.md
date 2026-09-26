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
