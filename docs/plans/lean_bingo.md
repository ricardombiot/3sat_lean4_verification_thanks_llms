# Plan: `lean/improves_bingo`, el espejo Lean de `julia/improves_bingo`

27-sept-2026. Rama `graph_owners`. Estado: **L0–L3 hechos** (L4 aplazado: el modelo es muy lento; L5 y L6 en curso). Decisiones: (1) `require` de `improves_bin`, (2) aristas en una orientación con `Adj` simétrica por definición, (3) rama `graph_owners`.

## Objetivo

Un proyecto Lean 4 nuevo, `lean/improves_bingo`, que modele la máquina de `julia/improves_bingo`: los owners como
un **grafo por gpath** (vivos + aristas simétricas), sin tablas por nodo. No es una copia de `lean/improves_bin`:
es un modelo nuevo, pensado para que **cada regla del review sea un operador que solo borra** y para que añadir una
regla cueste un lema.

La meta de fondo es el veredicto del lector. En `lean/improves_bin`:
* `readerVerdictW_sound` está demostrado **sin hipótesis**: si el lector termina, la fórmula es satisfacible;
* lo abierto es la **completitud del lector**: que nunca llegue a un callejón sin salida (`NoDeadEnd`, y sus formas
  `KernelSplit`, `TriPin₁`, `CliqueTri`, `PieceLocal`, M1…).

Con el grafo, eso se enuncia de forma directa: **basta que todo punto fijo válido del review que el lector visita
contenga una solución compatible con sus pins** (§ «La meta», abajo). Las reglas nuevas sobre aristas (informe v199
§6) son el camino para llegar ahí, y este proyecto es el marco para escribirlas y demostrarlas.

## Principios de diseño

1. **Especificación, no implementación.** Como `GPathM`: listas planas, validez derivada, cada poda es un
   `filter`. El modelo no tiene que ser rápido; tiene que coincidir en lo observable con Julia (diferencial, L4)
   y ser fácil de demostrar. Si hace falta velocidad, versiones rápidas con `@[csimp]` (el patrón de
   `pairShares_eq_fast`).
2. **La simetría, por definición.** Sin Mathlib no hay `Sym2`. Propuesta: `edges : List (PathNodeId × PathNodeId)`
   y
   ```lean
   def adj (g : GPathB) (x w : PathNodeId) : Prop := x = w ∧ x ∈ g.alive ∨ (x, w) ∈ g.edges ∨ (w, x) ∈ g.edges
   theorem adj_symm : adj g x w ↔ adj g w x   -- por definición, sin orden entre ids
   ```
   Quitar una arista quita las dos orientaciones. No hace falta un orden total en `PathNodeId` (la clave ordenada
   de Julia es una optimización, no parte de la especificación).
3. **Los datos de las aristas se calculan, no se guardan.** Julia guardará contadores y testigos como caché; Lean los
   define como funciones del estado (`parSupport g x w := (parentsOf g x).countP (adj g · w)`). Así los lemas no
   tienen que mantener cachés, y el diferencial solo compara lo observable.
4. **La capa de base se reutiliza, no se copia.** `Cnf`, `Formula`, `CnfMapBin`, `CnfSelBin`, `Alias` vienen de
   `lean/improves_bin` como dependencia de Lake (decisión 1). Mismos tipos, así que el puente de la L8 es directo.
5. **`warningAsError = true` y 0 `sorry`** desde el primer commit, como en `improves_bin`.

## La meta: qué hay que demostrar para el veredicto

Con `Sol φ g` = «el conjunto de nodos que decodifica una solución de φ está vivo en g, con todas sus aristas y
enlaces» (una camarilla que toca cada paso):

* **Completitud de la máquina** (la parte fácil con el grafo): toda regla conserva `Sol` (`KeepsSol`), así que si φ
  es satisfacible, la línea final tiene un estado con `Sol`. Es el análogo de `completeness_pure`.
* **Solidez del lector**: si el lector termina (un nodo por paso), eso es una solución. En bin está demostrado
  (`readerVerdictW_sound`, vía `L7`); aquí se reutiliza por el puente estructural (L7, abajo).
* **Completitud del lector**, lo abierto. Con el grafo se enuncia así:
  ```lean
  def NoZombie (g : GPathB) : Prop := isValid g → ∃ S, Sol φ g S
  theorem readerVerdict_iff_of_noZombie :
      (∀ g ∈ estados que el lector visita, NoZombie g) → (readerVerdict φ ↔ Satisfiable φ)
  ```
  Si un estado válido contiene una solución, el pin del nodo de esa solución en el primer paso con elección deja el
  estado válido (por `KeepsSol`), así que el lector nunca se queda sin pin. **Cada regla nueva es un intento de
  hacer demostrable `NoZombie`**: cuanto más fuerte el review, más cerca un estado válido está de contener una
  solución.

## Fases

### L0 — esqueleto del proyecto

* `lean/improves_bingo/`: `lakefile.toml` (namespace `AbsSatBingo`, `warningAsError`), `lean-toolchain` igual al de
  `improves_bin` (`v4.33.1`), `require` de `improves_bin` por ruta (decisión 1), `README.md` con la tabla de
  procedencia de módulos (el formato del README de `improves_bin`), `scripts/gen_root.sh`.
* Criterio: `lake build` compila un módulo vacío que importa `AbsSatBin.GraphMap.CnfMapBin`.

### L1 — el modelo

`AbsSatBingo/Model/GPathB.lean`:
```lean
structure PNodeB where id : PathNodeId; title : String; parents sons : List PathNodeId
structure GPathB where
  nodes : List PNodeB
  alive : List PathNodeId                    -- Julia og.alive (antes gowners)
  edges : List (PathNodeId × PathNodeId)     -- Julia og.edges (una orientación basta)
  current_step : Int
  map_parent : Option NodeId
```
Vistas derivadas: `adj` (con `adj_symm`), `neighbors g x k`, `isValid` (cada paso con un vivo), `isValidNode`
(cada paso con un vecino vivo + padres/hijos, la de Julia), `measure` (vivos + aristas + enlaces).
Primitivas: `removeNode` (sale de `alive`, de `edges` y de los enlaces), `removeEdge`, `addEdge`.
Criterio: lemas básicos (`adj_symm`, `removeNode` solo quita, `measure` baja).

### L2 — las operaciones, espejo de `julia/improves_bingo`

| Julia (`improves_bingo`) | Lean |
|---|---|
| `add_row!` + `create_from_parents!` (vecinos de los padres, vivos, pasos anteriores) | `addNode … forb`, `up`, `upFiltering` (UP de `GPathM` con ventanas prohibidas) |
| `filter_require!` → `remove_node!` | `filterRequire`: quita de `alive` y de `edges`; el documento sigue hasta la purga |
| `clean_invalid_nodes!` (una fase, hasta el punto fijo) | `purgeFuel` (el de `CleanTwoPhase`, sin `cutAll`) |
| `pair_consistency_after_clean!` | `pairSweep` sobre aristas (todas contra el mismo estado) + purga, `pairFuel` |
| `prune_stale_links!` | `pruneLinks`: un enlace vive si `adj` |
| pasadas de padres / hijos (`cut_by_support!`) | `reviewParents` / `reviewSons` con `cutSupport` |
| `make_review_owners!` | `reviewPass`, `reviewFuel`, `review`; `filterAll` |
| `do_join!` (`PathOwnersGraph.union!`) | `join` / `doJoin` |
| máquina (`sat_machine.jl`) | `PureDriver`: `pureRun` |
| lector sin retroceso | `ReaderExec`: `readerVerdict` (el de `improves_bin`, sobre `GPathB`) |

Terminación por `measure`, como `Fuel.lean`. Criterio: todo compila y `lake exe bingo-check` da el mismo veredicto
que la fuerza bruta en `cnf/random_small` y `cnf/crafted`.

### L3 — ejecutables

* `bingo-dump`: vuelca el estado final **en el formato de `julia/improves_bingo/test_3sat/dump_final.jl`** (por
  gpath: nodos, global, tabla de cada nodo, padres, hijos), para reutilizar `compare_bingo.jl` tal cual.
* `bingo-check`: veredicto contra `bruteSat` y ningún nodo muerto (como `driverbin-check`).

### L4 — diferencial Lean ↔ Julia (bingo)

`scripts/diff_bingo.sh`: `dump_final.jl` en Julia y `bingo-dump` en Lean sobre el mismo corpus, y
`compare_bingo.jl` entre los dos. El modelo en listas es lento: corpus de instancias pequeñas (hasta `v5_c20`),
con límite de tiempo. Criterio: mismos veredictos y mismos estados finales en todo lo que termine; y una mutación
del modelo (por ejemplo, olvidar la simetría en `pairSweep`) tiene que detectarse.

### L5 — invariantes de forma

`WF g`: aristas entre vivos, ids sin repetir, enlaces ⊆ `adj` tras `pruneLinks`, vivos = ids de nodos tras la purga,
aristas solo entre pasos distintos. Se demuestra que todas las operaciones de L2 lo conservan. Aquí entra también el
**orden dentro de una línea no importa** en las pasadas (dos hermanos no son vecinos; Julia recorre en orden de hash):
un lema, no una suposición.

### L6 — el marco de reglas

```lean
structure Rule where
  apply    : GPathB → GPathB
  defl     : ∀ g, Sub (apply g) g            -- solo borra: vivos, aristas y enlaces
  keepsSol : ∀ φ g S, Sol φ g S → Sol φ (apply g) S
```
* `review` como punto fijo de una lista de reglas (purga, parejas, enlaces, pasadas) con combustible.
* Teoremas genéricos: el review es `defl`, conserva `Sol`, y **si las reglas son monótonas, el punto fijo no depende
  del orden** (el mayor estado estable por debajo de g). Esto sustituye, de una vez, a los resultados por modo de
  `improves_bin` (`CleanTwoPhase`, `pairSweep`, espejo).
* `completeness_bingo`: φ satisfacible ⇒ la máquina dice SAT (`Sol` a lo largo de `pureRun`; la idea de
  `PrefixCarry`).
* `readerVerdict_iff_of_noZombie` (§ «La meta»).

### L7 — puente estructural con `improves_bin`

`toM : GPathB → GPathM` (owners de x := vecinos vivos de x). Solo la parte **estructural**: nodos, ids, enlaces y
cadenas no dependen de las tablas, así que los lemas de decodificación (`PrefixDecode`, `L7.sat_of_inhabited`,
`CnfChain`) se transportan sin rehacerlos. Da la solidez del lector en bingo a partir de `readerVerdictW_sound`.

### L8 — puente completo (opcional)

`toM` conmuta con `filterAll`, `upFiltering` y `join` en los estados alcanzables (igualdad de puntos fijos, no de
estados intermedios: el desfase de ids muertos, el espejo y `cutAll` hacen distintos los pasos intermedios).
Permitiría transportar todo lo demostrado en `improves_bin` (`completeness_pure`, la ruta `PieceLocal`/M1, `KFix`…).
Es la fase más cara y la más arriesgada; la F4 de Julia (estados finales y vueltas idénticos en 81/81) dice que el
enunciado es plausible. Se decide después de L6: si el marco de reglas llega antes a la meta, no hace falta.

### L9 — la primera regla sobre aristas

La elegida del informe v199 §6 (propuesta: 6.1, apoyo contado), **a la vez** en Julia (`improves_bingo`, detrás de un
interruptor, medida con `REMOVED_BY`) y en Lean (una `Rule` con su `keepsSol`), y el diferencial de L4 sobre las dos.

## Decisiones antes de L0

1. **Dependencia de `improves_bin`.** (a) `require` por ruta: mismos tipos, puente directo, sin duplicar; pero
   depende de un proyecto que otra sesión modifica a diario (solo se compilan los módulos que se importan; la capa
   de base casi no cambia). (b) Copiar la capa de base (~1.100 líneas) con namespace propio: independiente, pero el
   puente de L7/L8 necesitaría convertir tipos gemelos. **Propuesta: (a).**
2. **Representación de las aristas**: pares en una orientación con `adj` simétrica por definición (propuesta), o
   pares normalizados por un orden total (más cerca de Julia, pero exige el orden y sus lemas).
3. **Rama**: seguir en `graph_owners` o abrir `lean_bingo`. Ojo: otra sesión está haciendo commits de Lean en
   `graph_owners` porque comparte la carpeta de trabajo.

## Riesgos

* **Lentitud del modelo.** El diferencial solo cubrirá instancias pequeñas; si hace falta más, versiones `@[csimp]`.
* **`NoZombie` puede ser falso** para el review actual (es otra forma de lo abierto en bin). El marco no lo hace
  cierto; hace que cada regla nueva cueste un lema y que su efecto sobre `NoZombie` se pueda medir y enunciar.
* **Deriva Julia ↔ Lean.** Cada regla entra a la vez en los dos lados (L9), con el diferencial de L4 en verde.

## Commits

Uno por fase, con `lake build` en verde y 0 `sorry`; L4 y L9 con la tabla del diferencial en el mensaje.
