# `AmbFar`: dónde está la escalera del lector sin retroceso (mapa bin) y cómo seguir

> Proyecto `lean/improves_bin`, rama `lean_improves_bin`, hasta el commit `4914f15`.
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

### 4.1 Recortar `AmbFar` a nodos altos (siguiente paso formal, barato)

**Deducido, sin formalizar.**
* Un nodo `y` en un paso `s < k` es el único nodo vivo de su paso, por `gowner_eq`.
* Todo nodo vivo tiene una entrada en `s` (validez), y esa entrada es `y`. Así que **`y` está en todas
  las tablas**, y por simetría **la tabla de `y` contiene a todos los nodos vivos**: los nodos forzados
  poseen todo.

Consecuencias:
* **`y` y `w` ambos bajo `k`**: sirve cualquier entrada de `x` en `l`.
* **`y` bajo `k` y `w` por encima**: la regla de parejas de `(w, x)` da `r` en `l`, y `y` lo posee
  automáticamente.

Queda **`AmbHigh g k x`**: los dos nodos en pasos `≥ k+3`, con `l > k`. Es una prueba corta con lo que ya
hay en `AmbTriCore` (`gowner_eq`, `entry_at`, `ker.sym`, `ker.pair`). La propongo como siguiente paso
formal: deja el núcleo en su forma más limpia, **tríos enteramente por encima del prefijo**.

### 4.2 Medir `AmbHigh` / `AmbFar` (pendiente de confirmación)

Una sonda solo sobre tablas, en los estados del lector. Mediría:
* cuántos nodos ambiguos hay en pasos `≥ k+3`, y cuántas parejas;
* si alguna pareja rompe el trío, y en qué `l` respecto a `k` y a los pasos de `y` y `w`;
* si el fallo ocurre **para los dos bits a la vez** (lo único que rompe `NoDeadEnd`).

Mejor en Julia: el modelo Lean en listas tarda unos 100 s de máquina en `v4_c12_i1`, y la sonda
`otherbit-probe` no terminó en más de 18 min. La sonda Lean existente (`OtherBitProbeMain.lean`) puede
servir de oráculo en instancias de 3 variables. Sin lanzar hasta que lo confirmes.

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

1. §4.1: `AmbFar ⇐ AmbHigh`, en Lean. Corto, seguro, y limpia el enunciado.
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

Sondas: `lean/improves_bin/OtherBitProbeMain.lean` (exe `otherbit-probe`, `--chain`, `--cap N`).
