# El puente formal: lectura vía Owners ≡ caminos de `run_pure`

**Estado: propuesta de diseño (no formalizado aún).**
El plan de ejecución de la primera etapa (espejo puro `GPathM` + Lema L1) está en
[`docs/plans/espejo_gpathm_lema_L1.md`](../docs/plans/espejo_gpathm_lema_L1.md).
Este documento revisa el algoritmo formal completo y plantea cómo demostrar en Lean 4 el
eslabón que hoy falta: que la representación comprimida basada en Owners (el grafo
ejecutable) denota *exactamente* el conjunto de caminos que el modelo puro verificado
(`run_pure`) enumeraría. Se apoya en la semántica de lectura del Reader original de Julia
(`docs/original_julia/src/graph_path/reader/`) y en las correcciones del filtro de Owners
aplicadas el 2026-07-04.

---

## 1. La cadena de corrección completa: qué existe y qué falta

Para que "la máquina dice SAT" implique "la fórmula es satisfacible" (y viceversa), hacen
falta cuatro eslabones:

| # | Eslabón | Enunciado informal | Estado |
|---|---------|--------------------|--------|
| E1 | CNF ↔ GMap | El mapa construido por `ImportCnf`/`add_var!`/`add_gate!` codifica fielmente la fórmula: una asignación satisface el CNF ⟺ existe secuencia de elecciones válida sobre las capas del mapa (`Solvable`). | **Abierto** (no hay teorema; hoy es un argumento informal + tests) |
| E2 | GMap ↔ `run_pure` | El evolucionador exhaustivo por capas es correcto y completo respecto a `is_valid_solution`/`Solvable`. | **Demostrado, sin axiomas** (`Soundness.lean`, `Completeness.lean`, bajo `WellFormedGMap`) |
| E3 | `run_pure` ↔ máquina/Owners | La representación comprimida (GPaths + Owners + Join en el Timeline) denota exactamente los caminos de `run_pure`. | **Abierto — este documento** |
| E4 | máquina ↔ Reader | La lectura vía Owners enumera exactamente la denotación (y el reader simple nunca se atasca). | **Abierto** (Reader en Lean es un stub; semántica solo en Julia) |

Observación importante de la revisión: el modelo puro verificado (E2) es
*enumerativo* — mantiene cada camino por separado, con coste exponencial. Toda la promesa
del algoritmo (espacio polinomial) vive en E3: el grafo con Owners es la compresión. Por
eso E3 es el teorema decisivo: transfiere la corrección ya demostrada de `run_pure` a la
estructura que de verdad se ejecuta. (La *polinomialidad* del espacio es una rama aparte —
`formal_compression_strategy.md` — y no se toca aquí: el puente demuestra corrección
funcional, no complejidad.)

## 2. Qué es "leer vía Owners" exactamente (semántica observada en Julia)

El hallazgo clave al revisar `path_reader.jl` / `path_exp_reader.jl`: **el Reader no tiene
lógica propia — es el propio filtro de la máquina aplicado con requisitos unitarios.**

- `GPathReader.read_step!`: elige un nodo cualquiera del paso actual
  (`first(ids)`), registra su `index` (0/1) como valor del literal, y ejecuta
  `GraphPath.filter!(gpath, {nodo_elegido})` — el mismo `filter!` de construcción.
  Avanza de 2 en 2 (bloque de literales: paso par = valor, paso impar = nodo `!X`).
  Termina al llegar a un nodo `or*` o `FusionNode`. Si el grafo queda inválido tras un
  filtro, lanza `"GRAVE ERROR READER"` — es decir, **el diseño asume como invariante que
  cualquier nodo superviviente es extensible a una solución completa**.
- `GPathExpReader`: idéntico, pero bifurca un reader (deepcopy) por *cada* nodo del paso
  actual — enumera todas las configuraciones representadas.

Consecuencia para la formalización: la "lectura" se define operacionalmente como
*filtrados unitarios encadenados*, así que el puente no necesita un modelo separado del
Reader — necesita una **denotación** del estado del grafo y tres propiedades del filtro
respecto a ella.

## 3. La denotación correcta: cadenas co-poseídas, no cadenas de aristas

Primer intento natural (y **erróneo**): denotar un GPath como el conjunto de cadenas por
las aristas padre/hijo (una selección de un nodo por paso con enlaces consecutivos).

Por qué falla: tras un `do_join!`, dos ramas que visitaron nodos-caso distintos de una
cláusula (p.ej. `or1=001` y `or1=011`) se fusionan. Los nodos *compartidos* entre ramas
(mismo `PathNodeId`, p.ej. el `FusionNode` del bloque de literales) unen sus conjuntos de
padres e hijos (`PathDocNode.union`). Una cadena de aristas puede entonces **entrar** al
nodo compartido por padres de la rama B y **salir** por hijos de la rama A — una "cadena
mixta" que combina valores de literales de B con un nodo-caso de A cuyos requisitos esos
literales violan. Las aristas solas sobre-aproximan.

Lo que bloquea las cadenas mixtas inválidas es exactamente la red de Owners: `or1=001`
solo existía en la rama A, así que sus owners en los pasos de literales siguen siendo los
de A (solo los literales consistentes con `001`). El Reader lo explota: cada filtrado
unitario poda vía owners, no vía aristas.

**Denotación propuesta** — una selección por pasos que sea (a) cadena de aristas y (b)
*co-poseída par a par*:

```lean
-- Selección: un PathNodeId por paso 0..S-1
def IsChain (g : GPathM) (sel : Fin S → PathNodeId) : Prop :=
  (∀ k, sel k ∈ g.line k) ∧
  (∀ k, (h : k+1 < S) → sel k ∈ (g.node (sel ⟨k+1, h⟩)).parents)

def PairwiseOwned (g : GPathM) (sel : Fin S → PathNodeId) : Prop :=
  ∀ i j, i ≠ j → sel i ∈ (g.node (sel j)).owners i.val

def denot (g : GPathM) : Set PurePath :=
  { p | ∃ sel, IsChain g sel ∧ PairwiseOwned g sel ∧ p = pathOf sel }
```

donde `pathOf` proyecta cada `PathNodeId` a su `NodeId.id` de mapa y construye la
`PurePath` en el orden de `run_layers` (último paso en cabeza, como `fold_choices`).
`GPathM` es un **espejo puro** de `GPath` (ver §6.1).

## 4. Enunciado del puente y de sus corolarios

Sea `gmap : PureGMap` bien formado (`WellFormedGMap`), `machine_run gmap` la ejecución
pura de la máquina (init + bucle make_step con clone/up_filtering/join en el timeline), y
`final` el conjunto de GPaths del último paso del timeline.

```lean
-- E3, el puente:
theorem bridge (hwf : WellFormedGMap gmap) :
    (⋃ g ∈ final gmap, denot g) = { p | p ∈ run_pure gmap }

-- E4a: el ExpReader enumera la denotación
theorem exp_reader_enumerates (g) (hinv : Invariant g) :
    (expReader_solutions g : Set PurePath) = denot g

-- E4b: el Reader simple nunca se atasca (el "GRAVE ERROR" es inalcanzable)
theorem reader_nonstuck (g) (hinv : Invariant g) (hvalid : g.valid = true) :
    ∃ p ∈ denot g, reader_read g = some p
```

Con E2 ya demostrado, el puente da los corolarios extremo a extremo (módulo E1):

- `machine dice SAT ∧ p leída ⟹ is_valid_solution gmap p` (soundness transferida), y
- `Solvable gmap ⟹ machine dice SAT` (completeness transferida).

### Reducción útil del enunciado

No hace falta demostrar la igualdad de golpe. Por la exhaustividad ya probada de
`run_pure` (`run_pure_complete`: contiene *todas* las secuencias de elecciones válidas),
la igualdad equivale a dos inclusiones de naturaleza muy distinta:

1. **Completitud (ningún camino se pierde):** `run_pure gmap ⊆ ⋃ denot`.
   Es una inducción sobre el bucle de la máquina, camino por camino: cada
   `ChoicesValid` sobrevive a cada `up_filtering` (su nodo elegido es el requerido) y a
   cada `join` (unión). Es la dirección "fácil" — puramente estructural.
2. **Soundness (ninguna cadena inventa un camino inválido):** toda `sel` co-poseída
   induce una secuencia que satisface `satisfies_requirements` paso a paso — es decir,
   `denot ⊆ ChoicesValid`-secuencias, que por `run_pure_complete` están en `run_pure`.
   Aquí vive toda la dificultad; se descompone en §5.

## 5. Los lemas, en orden de ataque

### L1 — Soundness local de requisitos (el lema "estrella", demostrable ya)

> Si `sel` es co-poseída y `d = sel j` tiene `req ∈ requires(d.id)` en el paso `i`,
> entonces `sel i` es *el* nodo requerido.

Argumento: todo GPath que contiene el `PathNodeId` `d = (map_id, parent_map_id)` pasó por
`do_up_filtering(requires(map_id), map_id)` en el mismo punto del timeline; en cada uno,
`filter_require!` dejó en los owners de `d` del paso `i` únicamente el nodo requerido.
`do_join!`/`PathDocNode.union` solo fusiona owners de nodos con el **mismo** `PathNodeId`
— y todos fueron filtrados por los *mismos* requisitos — luego la unión de owners de `d`
en el paso `i` sigue siendo `{nodo requerido}`. Como `sel i ∈ owners(d) i`, se concluye.
**Este es el teorema que justifica formalmente la frase del libro: el sistema de
identificación `(id, parent_id)` convierte la consistencia global en consistencia local.**

### L2 — El filtro respeta la denotación (cuadrado conmutativo del Reader)

> `denot (filter g {n}) = { p ∈ denot g | p pasa por n }`, y
> `(filter g {n}).valid = true ↔ ese conjunto es no vacío`.

La primera igualdad separa en: `filter_require` (poda owners del paso — directo) +
`make_review_owners` (clausura — necesita L5/L6). La segunda es la corrección del flag
`valid` (los arreglos de 2026-07-04: `checkIfEmpty`, `emptySteps`).

### L3 — UP respeta la denotación

> `denot (up_filtering g (requires d) d) = { d.id :: p | p ∈ denot g, p satisface requires d }`
> — el análogo exacto de `evolve_path_nodes` para un solo destino.

### L4 — Join respeta la denotación (la dirección que el doc del Join deja en el aire)

> Bajo `is_valid_join` (mismo paso, mismo `map_parent_id`):
> `denot (join g₁ g₂) = denot g₁ ∪ denot g₂`.

`⊇` es trivial (monotonía de la unión de nodos/aristas/owners). `⊆` es el punto que
`formal_verification_join.md` §4 despacha con *"preserved loosely (monotonicity of
ownership)"*: hay que demostrar que una cadena co-poseída del grafo unido, aunque mezcle
aristas de ambas ramas por nodos compartidos, o bien ya era co-poseída en `g₁`, o en
`g₂`, **o es una mezcla cuya secuencia de mapa sigue siendo válida** (y entonces basta
que esté en `run_pure`, no que estuviera en alguna de las dos denotaciones — para el
puente global la igualdad por gpath puede relajarse a: soundness respecto a
`ChoicesValid` + completitud de la unión). Recomendación: **enunciar L4 en la forma
relajada** (soundness global + completitud), no como igualdad exacta por gpath; es lo
único que el puente necesita y evita pelear con mezclas benignas.

### L5 — Terminación y punto fijo de `make_review_owners!`

La recursión termina: cada pasada o no cambia nada (y `review_owners` queda en falso) o
elimina al menos una entrada (nodo u owner) de un total finito. En Lean: versión con
*fuel* = `Σ |owners(n)| + |nodos|`, y lema de que el resultado es un punto fijo:
tras la revisión, todo nodo superviviente es `is_valid_node` y sus owners son coherentes
con la unión de padres y la de hijos.

### L6 — El invariante de soporte total ("no zombies"), el lema Helly del sistema

> `Invariant g` := todo nodo superviviente pertenece a *alguna* cadena co-poseída
> completa; y `g.valid = true ⟹ denot g ≠ ∅`.

Este es el **make-or-break** de todo el puente, y la razón de ser de las dos reglas de
coherencia del libro (Figs. 2.31–2.33). La co-propiedad par a par es una
2-consistencia; que 2-consistencia implique una cadena global no es cierto en general —
tiene que salir de la estructura específica del mapa 3SAT:

- en el bloque de literales, los requisitos son de alcance 1 (cada `!X=v` requiere solo
  el paso anterior), así que la consistencia local encadena;
- en el bloque de cláusulas, cada nodo-caso tiene ≤3 pasos requeridos y las pasadas
  padres/hijos propagan la poda entre bloques.

Estrategia: no intentar el lema para grafos arbitrarios; demostrarlo por inducción sobre
la construcción (los únicos estados alcanzables son los producidos por
init/up_filtering/join/review), manteniendo `Invariant` como invariante de máquina. Si
en algún caso la preservación falla, el fallo señalará **el contraejemplo exacto** del
algoritmo — resultado igual de valioso (véase §7).

### L7 — Inducción del bucle (ensamblaje del puente)

Con L2–L4 + invariante L6: inducción sobre los pasos del timeline igual que
`run_layers_sound`/`run_layers_mem_complete`, con la correspondencia
`⋃_{g ∈ timeline t} denot g = run_layers (capas hasta t) semillas`.

### L8 — El Reader (E4)

Con L2 y L6, `exp_reader_enumerates` y `reader_nonstuck` son inducciones directas sobre
los pasos de lectura (cada `read_step` = un filtrado unitario + proyección).

## 6. Decisiones de ingeniería para que esto sea demostrable

1. **Espejo puro único (`GPathM`)**: el `GPath` actual vive en `IO.Ref` y no se puede
   razonar sobre él. Definir el núcleo como funciones puras sobre
   `List`/`Finset` (como ya hace `PureSatMachine`) y hacer que el ejecutable sea *el
   mismo núcleo* envuelto en un `IO.Ref` de estado — así no hay teorema de refinamiento
   IO↔puro que demostrar, solo uno de estado trivial. Evitar `Std.HashMap` en el modelo
   (los lemas existen pero encarecen todo; `List`+`Finset` mantiene el estilo de
   `Model/`).
2. **Filtro-especificación primero**: definir `filterSpec g n := restricción de denot`
   y demostrar el puente contra `filterSpec` (L3, L4, L7 no dependen de owners).
   Después, por separado, que el filtro por owners implementa `filterSpec` bajo el
   invariante (L1, L2, L5, L6). Dos frentes independientes y acumulativos.
3. **Blindaje empírico antes de invertir meses** — ✅ **implementado (2026-07-04)**:
   `AbsSat/SatMachine/DiffTest.lean` + `lake exe diffTest [casos] [semilla]` genera CNFs
   3SAT aleatorios (n ∈ 3..7, dos regímenes de densidad: 1..4n y, cada tercer caso,
   4n..6n para cubrir UNSAT pasada la transición de fase ~4.26n) y compara contra
   `ExhaustiveSolver` no solo el veredicto sino el **conjunto completo de soluciones
   leídas** vía `GPathExpReader`. RNG determinista (LCG) — todo fallo es reproducible
   con `(semilla, nº de casos)`; las instancias que fallan se vuelcan a
   `difftest_failure_<k>.cnf`. Un error del Reader (grafo invalidado a mitad de
   lectura) se reporta como hallazgo, no se salta: es exactamente una violación de L6.
   **Resultado inicial: 5.210 casos, 0 desacuerdos** (≈4.800 SAT con conjuntos de
   soluciones idénticos, ≈400 UNSAT), más verificación manual de recuentos exactos
   (7/6/14/1 soluciones en instancias calculadas a mano). Evidencia empírica — no
   prueba — de que L6 no tiene contraejemplo en n pequeño.
4. **Portar el Reader a Lean** — ✅ **hecho (2026-07-04)**: `Reader/PathReader.lean` y
   `Reader/PathExpReader.lean` implementan la semántica de Julia (§2). Desviación
   deliberada documentada: el ExpReader bifurca por id de mapa distinto, no por
   `PathNodeId` (equivalente tras el filtro, evita soluciones duplicadas).

## 7. Qué significaría cada desenlace

- **Puente demostrado (L1–L8):** la corrección funcional de la representación comprimida
  queda verificada extremo a extremo (módulo E1, que conviene atacar en paralelo por ser
  independiente y mucho más corto). No demuestra por sí solo la polinomialidad — esa
  rama (cotas de `formal_compression_strategy.md`) se convertiría entonces en el único
  frente restante, y pasaría a ser *el* enunciado extraordinario.
- **L6 falla con contraejemplo:** se obtiene la instancia CNF concreta donde la
  2-consistencia de Owners no captura la consistencia global — es decir, el punto exacto
  donde la compresión pierde información. Eso delimita el algoritmo con una precisión
  que ningún test puede dar, y es exactamente el tipo de resultado que hace que esta
  formalización valga la pena con independencia del veredicto.

Ambos desenlaces son victorias de conocimiento. El puente es la pregunta correcta.

---
*Propuesto por Claude (Fable 5) el 2026-07-04, tras la revisión del filtro de Owners y
sus correcciones. Documento de diseño: los enunciados Lean son esquemas, no código
compilado.*
