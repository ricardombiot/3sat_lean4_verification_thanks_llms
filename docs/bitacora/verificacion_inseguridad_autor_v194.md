# Verificación para el Autor v194: el proyecto Lean del mapa bin — de la migración al núcleo `TriPin`

Ricardo, este informe recoge todo el trabajo Lean sobre el mapa binario, en la rama `lean_improves_bin`
(proyecto `lean/improves_bin`, 26 commits desde `898abf3` hasta `f439515`). Complementa al v192 (qué
podía ganar la prueba con el mapa bin, en teoría) y al v193 (la máquina bin en Julia).

**La conclusión, por adelantado.** La migración está completa y sin deudas: 0 `sorry`, `warningAsError`
activo, y solo los axiomas de Lean (`propext`, `Quot.sound`). La completitud de la máquina está
demostrada sin hipótesis abiertas. Para el lector sin retroceso, toda la escalera hasta el núcleo está
demostrada. Lo único abierto es **una condición local sobre las tablas, `TriPin`**, que solo puede
fallar en **parejas ambiguas**. Esa condición no puede deducirse de que el estado sea un punto fijo del
review: necesita un invariante de cómo la máquina construyó las tablas.

Cada afirmación lleva su estado: **demostrado** (teorema en Lean, sin `sorry`), **medido** o
**abierto**.

---

## 1. La migración (Parte I)

### 1.1 Cómo se hizo

Proyecto nuevo e independiente (`namespace AbsSatBin`), con módulos traídos de `lean_project` solo
cuando hacían falta. Cada módulo se registra en `lean/improves_bin/README.md` como **copia**,
**reescrito** o **revisado**.

La preocupación era que un índice heredado del mapa clásico compilara sin error. Para evitarlo:

* `Lit.step` pasó a llamarse `Lit.binStep` (`2v+1` / `2v+2`), así que ningún uso heredado compila.
* `scripts/index_lint.py` rechaza aritmética de pasos sin anotación `-- idx:`. Las únicas fuentes de
  aritmética del mapa son `CnfMapBin`, `CnfSelBin` y `Formula`.
* Herramientas para hilar el parámetro `forb` (ventanas prohibidas) por la API del UP sin tocar
  comentarios: `thread_forb.py`, `fix_forb.py`, `port.sh`.
* **Diferencial del mapa contra Julia** (`scripts/diff_map_bin.sh`): **74/74** iguales (pasos, nodos,
  requisitos, hijos y ventanas prohibidas); una mutación de `sonsOf` da 0/74, así que el diferencial sí
  distingue. **Medido.**

### 1.2 El mapa y el UP

* `CnfMapBin`: el mapa como aritmética. `stepCount = 2n+3m+3`; raíz en el paso 0, variable positiva en
  `2v+1`, negada en `2v+2`, fusión media en `2n+1`, literales de la cláusula `j` en `2n+2+3j+p`, fusión
  final en `2n+3m+2`.
* La **ventana prohibida** es solo `(L1,L2,L3) = (0,0,0)`. Un test comprueba las 8 combinaciones sobre
  el identificador que construye el UP: solo `(0,0,0)` queda prohibida, y `(1,0,0)`, `(0,1,0)` y
  `(1,1,0)` pasan. **Demostrado por evaluación.**
* UP con filtro: `shiftRowIds` son los candidatos y `newRowIds` los no prohibidos; la revisión solo se
  lanza si se saltó alguna ventana (como `review_owners` en Julia).

### 1.3 Teoremas finales de la máquina

* **`completeness_pure`** (satisfacible ⇒ la máquina dice SAT): **demostrado**, solo con `Bounded`.
  `Sat` entra en un único lema: `pidOfAssign_not_prohibited` (una solución nunca pasa por la ventana
  `000`).
* **`soundness_pure`**: demostrado bajo `ClauseStepExact`, que en bin agrupa dos obligaciones:
  `HardStepExact` (los `3m` pasos `L`) y una nueva, **`SkipExact`**. El UP que salta una ventana puede
  dejar padres sin hijos (el error 4 del informe de errores de Julia); `SkipExact` pide que la revisión
  posterior lo repare. Está reducido a `SkipChainBin`: los supervivientes están sobre una cadena sólida
  que elige `L1 = 1`. **Abierto** en esa forma. La §3 da otra ruta que lo evita.

### 1.4 Correcciones al v192

* §2: para un candidato hacia abajo, la parte variable es el `gparent` del padre, en el paso `lo−3`, no
  `lo−2`. La conclusión (≤ 2 candidatos) se mantiene.
* §8 decía que «no cambian el review, la limpieza… ni la escalera del lector». En la práctica:
  * la escalera (`OneStep`, `PairHelly`…) estaba construida sobre requisitos débiles, que en bin no
    existen (74 módulos);
  * el salto de ventana creó la obligación `SkipExact`;
  * `rowParents_of_not_mem` cambió de hipótesis (`p ∉ shiftRowIds`), porque un id prohibido también
    tiene padres.

---

## 2. El lector: de la solidez a un solo lema (Parte II)

### 2.1 El programa y su solidez

`ReaderExec.readerVerdictW` recorre la línea final, toma el primer paso con elección, pincha el primer
nodo cuyo review deja el grafo válido y nunca deshace.

* **Solidez** (`readerVerdictW_sound`): si el lector termina, `φ` es satisfacible. **Demostrado**, sin
  hipótesis.
* **Review normal, no agresivo.** Como en Julia desde `4c644ac`, el lector usa `filterAll`. Para que el
  cambio sea exacto:
  * `PairInactive.reviewAgg_eq_review`: con la regla de parejas, el barrido agresivo no hace nada en el
    punto fijo del review, siempre que haya simetría (`RevOk`). **Demostrado.**
  * `SymMachine.symInv_reachable`: **todo estado válido de la máquina tiene tablas simétricas**, `join`
    incluido. La clave es un invariante nuevo, **`CutClosed`**: toda entrada de una tabla en un paso
    cubierto por la global es un owner global. Vale en el punto fijo del review, y `addNode` y `join`
    lo conservan. **Demostrado.**
  * Por tanto, a lo largo del lector, `filterAllAgg = filterAll` (`start_agg_eq`, `pin_agg_eq`).
    **Demostrado.**

### 2.2 La cadena de reducciones de la completitud

Cada flecha es un teorema. Todas **demostradas**, con solo `[propext, Quot.sound]`.

| paso | módulo | enunciado |
|---|---|---|
| el lector lee un prefijo | `ReaderPrefix` | pincha solo en `firstChoice`; el primer paso con elección solo avanza (`firstChoice_pin_gt`) |
| ⇐ `PinChain` | `ReaderPrefix` | un pin válido conserva alguna cadena |
| ⇐ `OtherBit` | `PinChainBin` | en bin cada paso tiene dos bits (`entry_bit`); el de la cadena es gratis; queda el contrario. `chainG_through_pin`: es también necesario |
| ⇐ `OtherBitSem` | `OtherBitSem` | enunciado sobre la fórmula: los pins son una asignación parcial; la línea final lleva **todas** las soluciones (`carried_unique`) |
| ⇐ `NoDeadEnd` | `NoDeadEnd` | en un estado válido del lector, no mueren los dos pins |
| ⇔ `KernelSplit` | `Kernel`, `KernelReader`, `KernelIff` | un kernel con elección tiene un subkernel cubriente que fija un bit |
| ⇐ `TriPin` | `KernelSplit` | regla de parejas con el pin como tercer miembro fijo |
| ⇐ `AmbTri` | `TriPinCore` | lo mismo, solo en parejas ambiguas |

Teoremas finales de cada peldaño: `readerVerdictW_iff_of_pinChain`, `…_of_otherBit`,
`…_of_otherBitSem`, `…_of_noDeadEnd`, `…_of_kernelSplit` y `…_of_triPin`, todos de la forma
`readerVerdictW φ = true ↔ Satisfiable φ` bajo la hipótesis correspondiente.

### 2.3 Tres piezas que merecen detalle

**`NoDeadEnd` también da la solidez de la máquina.** `soundness_of_noDeadEnd`: con `NoDeadEnd` y
`RootValid` (el review no mata el estado final: es el caso de cero pins), la máquina es sólida **sin
`ClauseStepExact` ni `SkipExact`**. La prueba desciende hasta un estado sin elecciones, que contiene un
camino (`inhabited_of_noChoice_readable`), y lo decodifica. Para eso hizo falta `selOfAssign_decode`: la
asignación decodificada nombra, en cada uno de los seis tipos de paso, exactamente el nodo de la cadena.
**Demostrado.** `RootValid` queda como hipótesis.

**Kernels: la caracterización de la muerte de un pin.** Un *kernel* es un estado con las propiedades
estáticas de un punto fijo válido del review:
* nodos válidos;
* tablas dentro de la global;
* simetría;
* enlaces en las tablas de sus dos extremos;
* regla de parejas;
* toda entrada en la tabla de algún padre y de algún hijo.

Resultados:
* `below_review`: **el review nunca baja de un kernel**. Cada operación (purga, corte, regla de parejas,
  review contra vecinos con espejo y desenlace, pasadas y bucle) conserva `Below X h`.
* `kernel_readPins`: **todo estado válido del lector es un kernel**. Hizo falta el invariante `OwnAbove`
  (entradas en pasos ≥ 0).
* `sonsSub_review`: el review nunca añade hijos.

Con esto, **un pin sobrevive si y solo si hay por debajo un kernel válido que lo fija**, y `KernelSplit`
es exactamente `NoDeadEnd`: reformular el núcleo sobre kernels no lo hizo más fuerte.

**El subkernel de un pin.** `restrictPin g x` se queda con los nodos cuya tabla contiene a `x` y recorta
todo a ellos. Con `TriPin` es un kernel válido que fija `x` (`restrict_kernel`). La cláusula de vecinos
sale de `TriPin` en el paso adyacente: una entrada de `y` en el paso de al lado es un padre (o hijo),
por la cláusula de vecinos del kernel original, `OOS` (en su propio paso, la tabla de un nodo es solo él
mismo) y `PBelow`/`SAbove` (padres un paso abajo, hijos un paso arriba).

---

## 3. El núcleo: `TriPin` y lo que hay debajo (Parte III)

### 3.1 El enunciado

> **`TriPin g x`**: dos nodos que se poseen y que poseen ambos a `x` comparten, en cada paso, una
> entrada que también está en la tabla de `x`.

Basta que valga para **uno** de los dos bits del primer paso con elección. Es la propuesta B del v191
(«parejas con el pin») en forma exacta. No pide nada de tríos sin el pin, y la construcción no usa que
el mapa sea binario.

### 3.2 Solo importan las parejas ambiguas (demostrado)

Un nodo que posee a `x` es **exclusivo** si en el paso de `x` su tabla solo contiene a `x`.
`tri_of_exclusive`: si uno de los dos miembros es exclusivo, el trío siempre comparte (la regla de
parejas contra la entrada común solo puede coincidir en `x`). Por tanto `TriPin ⇐ AmbTri`, que solo mira
**parejas ambiguas**: los dos nodos admiten ambos bits.

Que falle `NoDeadEnd` exige a la vez:
* dos nodos ambiguos cuyas entradas comunes en algún paso son todas incompatibles con el bit 0;
* y otros dos en la misma situación respecto al bit 1.

En bin, la ventana de tres pasos fija el bit de `k` en los pasos `k+1` y `k+2`, así que esos nodos son
exclusivos. Los ambiguos solo están por debajo de `k` o a partir de `k+3`. **Deducido, sin formalizar.**

### 3.3 Por qué no sale de los axiomas del kernel

Los axiomas del kernel son consistencia local (arco más parejas). La consistencia local admite puntos
fijos no vacíos sin ninguna cadena, así que existen kernels abstractos donde, al descender, mueren los
dos pins. **Cualquier prueba de `TriPin` tiene que usar la historia de la máquina**: cómo se heredaron
las tablas en el UP y cómo las filtraron los requisitos. Dos candidatos a invariante:

* **Tablas descomponibles**: la tabla de un nodo ambiguo es la unión de una parte compatible con cada
  bit, y cada parte es consistente por sí misma (encaja con la visión de subconjuntos de caminos).
* **`PairExact` conservado por el pin** (propuesta B del v191): da `TriPin` directamente.

**Abierto.**

---

## 4. Mediciones hechas

* Diferencial del mapa: 74/74 (§1.1).
* Máquina y lector contra fuerza bruta (`driverbin-check`): de acuerdo en las 6 instancias pequeñas y en
  `v4_c12_i1`. El modelo Lean en listas es lento: unos 100 s de máquina en `v4_c12_i1`.
* Sonda `otherbit-probe` (todas las ramas del lector, fuerza bruta sobre soluciones): **0 fallos** de
  `OtherBitSem` en 6 instancias de 3 variables. En `v4_c12` es inviable en Lean (más de 18 min sin
  terminar la primera instancia). **Medido, pero sin valor estadístico.**

No se ha medido `TriPin` ni `AmbTri`.

---

## 5. Resumen

| pieza | estado |
|---|---|
| migración, 0 `sorry`, `warningAsError`, lint de índices limpio | hecho |
| mapa bin = Julia (74/74) | medido |
| `completeness_pure` | **demostrado** |
| `soundness_pure` bajo `ClauseStepExact` (`HardStepExact` + `SkipExact`) | demostrado bajo hipótesis |
| simetría de toda la máquina; review agresivo = normal a lo largo del lector | **demostrado** |
| lector: solidez | **demostrado** |
| lector: completitud ⇐ `PinChain` ⇐ `OtherBit` ⇐ `OtherBitSem` ⇐ `NoDeadEnd` | **demostrado** |
| `NoDeadEnd` ⇔ `KernelSplit` ⇐ `TriPin` ⇐ `AmbTri` | **demostrado** |
| máquina sólida ⇐ `NoDeadEnd` + `RootValid` (sin `ClauseStepExact`) | **demostrado** |
| `AmbTri` (parejas ambiguas con el pin) | **abierto** |
| `RootValid` (el review no mata el estado final) | **abierto** |

## 6. Lo siguiente

1. **Medir `AmbTri`** en los estados del lector, de forma barata (solo tablas): cuántas parejas ambiguas
   hay, si alguna rompe el trío y en qué pasos respecto al pin. Conviene hacerlo en Julia por velocidad.
   Pendiente de tu confirmación.
2. Según lo que salga, buscar el invariante de historia (tablas descomponibles o `PairExact` en el pin)
   y demostrar que la máquina lo conserva.
3. Formalizar la exclusividad por ventana en `k+1` y `k+2` (§3.2), que acota dónde pueden estar las
   parejas ambiguas.

## 7. Una frase

Todo lo que separa al lector sin retroceso de decidir `φ` es ya una sola afirmación local sobre las
tablas: dos nodos ambiguos que se poseen y poseen al pin tienen, en cada paso, un testigo común que el
pin también admite.
