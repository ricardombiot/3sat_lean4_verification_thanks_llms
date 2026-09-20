# Plan — subir la ventana del identificador a 3 en la máquina `Improves` de Lean 4

Ricardo, esto es el plan de puerto del diseño que ya está en `julia/improves`
(commits `140bc3b`, `bd46899`) a la máquina pura de Lean (`GPathM` +
`ImprovesCima`). Escrito después de leer v173 y el código de Julia, no antes.

El objetivo no es "añadir un campo". Es lo que v173 §5 dejó dicho: **hacer que la
revisión agresiva, sin tocarla, dé consistencia de tríos**, porque dos nodos del
mundo nuevo son tres del viejo. El campo es el medio; el teorema es el fin.

---

## 0. Qué cambió en Julia, exactamente — cuatro hechos, no uno

Leído de `src/utils/alias.jl` y `src/graph_path/graph_path_up.jl`. Conviene
separarlos porque en Lean cuestan muy distinto.

**(a) El identificador tiene tres componentes.**
`PathNodeId = (gparent_id, parent_id, id)`, con `WINDOW[] ∈ {2,3}` decidiendo si
`gparent` se rellena o queda en `nothing`. `shift_path_id` desplaza la ventana:
`(gp, p, last) + id ↦ (p, last, id)`.

**(b) El UP ya no añade un nodo: añade una fila.**
`add_row!` agrupa la última fila por el identificador desplazado
(`group_parents_by_shifted_id`) y crea **un nodo por grupo**. Con `W=2` todos los
nodos de la última fila comparten `last.id` (la fila de arriba es homogénea en
id de mapa — eso es `ParentId.TL` en Lean), así que todos caen en el mismo grupo
y sale **exactamente el nodo único de antes**. Con `W=3` la fila se parte por el
`parent_id` de la fila anterior: un nodo nuevo por abuelo distinto.

**(c) Los owners del nodo nuevo ya no son los globales.**
`create_node_from_parents!`: `owners = (⋃ owners de sus padres) ∩ gowners`, más él
mismo. Antes era `owners := gowners` a secas.

**(d) La simetría de posesión ya no es universal.**
`its_owners_are_owned_by_me!` devuelve la posesión **solo a quien ya es owner del
nodo nuevo**. Antes `all_previous_nodes_are_owners_of_me!` se la daba a todos.

**(c) y (d) son la mitad que importa.** (a) y (b) reparten los nodos; (c) y (d)
son los que hacen que el UP pase a ser, por sí solo, un paso de poda. Y son los
que rompen más demostraciones en Lean, porque la máquina actual usa
"el nodo nuevo posee a todo el mundo" como atajo en muchos sitios.

**Coste medido (tuyo, `test_window/w2.tsv` vs `w3.tsv`, 22 instancias):**
veredictos idénticos, número de soluciones idéntico, `m_valid` en todas.
Nodos totales del gpath final: +0 % a +18 %. `peak_row`: igual en 18 de 22,
8→16 en el peor. Segundos: +5 % a +19 %. **Es barato.** No hay motivo de
rendimiento para no hacerlo.

---

## 1. El cambio de datos en Lean

`lean_project/AbsSat/Utils/Alias.lean:18`.

```lean
structure PathNodeId where
  id         : NodeId
  parent_id  : Option NodeId
  gparent_id : Option NodeId := none      -- ← campo nuevo, CON default
  deriving DecidableEq, Hashable, Repr
```

**El `:= none` no es cosmético.** La notación de instancia `{ id := …, parent_id := … }`
aparece en unos 83 ficheros (`Db/Path/Cols/*`, `GraphPath/GraphPath.lean`,
tests del ejecutable). Con default, **todas siguen compilando sin tocarse** y
significan "ventana 2", que es el comportamiento actual. Solo rompen:

* los 7 usos posicionales de `PathNodeId.mk` (los defaults no aplican a `.mk`);
* `new_path_id` (`Alias.lean:28`), que gana una variante de tres;
* `as_key_from_PathNodeId`, que debe imprimir el tercer componente cuando lo hay
  (mismo formato que Julia: `id__parent__gparent`), o el diferencial de tres vías
  deja de casar con Julia;
* `AggressiveReview.dropList` (`AggressiveReview.lean:53`), que fabrica un
  centinela `{ id := step, index+1, parent_id := w.parent_id }`: debe arrastrar
  también `gparent_id := w.gparent_id`, o el centinela deja de ser "el mismo nodo
  desplazado" y `intersectOwners` puede no borrar lo que debe.

En Julia la ventana es un `Ref` global. **En Lean no la hagas global.** Ponla
como parámetro de la construcción del id (§2), y deja `WINDOW = 3` fijo en el
driver. Un `Ref` mutable en Lean obliga a `IO` y contamina todo lo puro; y un
parámetro te da gratis el `W=2` como caso particular para el diferencial.

---

## 2. El cambio de UP: `addNode` → `addRow`

`lean_project/AbsSat/GraphPath/Model/GPathM.lean:287` y las piezas de
`Up.lean:43-60` (`newPid`, `newParents`, `upNode`, `upSons`, `upMap`).

Forma propuesta, deliberadamente cerca de Julia para que el diferencial siga
valiendo:

```lean
/-- Desplazamiento de la ventana, el `shift_path_id` de Julia. -/
def shiftPid (w : Nat) (last : PathNodeId) (d : NodeId) : PathNodeId :=
  { id := d, parent_id := some last.id,
    gparent_id := if w ≥ 3 then last.parent_id else none }

/-- La fila nueva: un nodo por identificador desplazado de la última fila. -/
def newRow (w : Nat) (g : GPathM) (d : NodeId) : List (PathNodeId × List PathNodeId)

def addRow (w : Nat) (g : GPathM) (d : NodeId) (title : String) : GPathM
```

Tres decisiones de diseño, y por qué:

1. **`newRow` devuelve la agrupación, no el estado.** Así `addRow` se demuestra
   por separado de la agrupación, y los lemas de forma (`addRow_nodes`,
   `addRow_gowners`, `addRow_current`) quedan en términos de una lista explícita.
   `addNode_nodes` (`Up.lean:74`) tiene hoy la forma `… ++ [newNode]`; pasará a
   `… ++ (newRow w g d).map mkNode`. Es el lema del que cuelgan ~65 ficheros.

2. **Agrupar con `List`, no con `HashMap`.** El orden de `Dict` de Julia no es
   observable en el punto fijo (ya está dicho en la cabecera de `GPathM.lean`), y
   una lista te da `Nodup` por construcción vía `dedup` sobre los ids
   desplazados — que es justo lo que `NodeIds.lean` necesita y hoy nadie
   descarga en el UP.

3. **`up` sigue siendo `if isValid g then addRow …`, sin `cleanInvalid` detrás.**
   Igual que Julia. Ojo con la tentación de meterlo: el hecho (d) hace que tras
   el UP haya nodos viejos sin owner en el paso nuevo, es decir **`isValidNode`
   falso**. Eso *no* rompe nada hoy porque `Pinned.Ctx.nodeval`
   (`Pinned.lean:61`) solo se afirma sobre estados ya revisados (`ReadableAgg`),
   nunca sobre el resultado crudo de `up`. Verifícalo antes de tocar: si algún
   lema afirma `nodeval` justo después de `addNode`, hay que revisarlo.

---

## 3. El libro mayor de invariantes

Esto es lo que decide si el puerto es una semana o un mes. Los he clasificado
mirando cada definición.

### 3.1 Sobreviven sin tocar (el campo nuevo les es indiferente)

| invariante | dónde | por qué aguanta |
|---|---|---|
| `ParentId.TL` | `ParentId.lean` | la fila nueva entera lleva el id de mapa `d` |
| `ParentId.PMP` | `ParentId.lean:102` | los miembros de un grupo comparten `last.id`, así que `some p.id = n.id.parent_id` sigue valiendo **para todos los padres** |
| `Sons.RootAtZero` | `Sons.lean:1124` | mira `parent_id`, no `gparent_id` |
| `Ownership.SelfOwned` | `Ownership.lean:83` | `add_owner!(node, node.id)` explícito |
| `Pinned.Ctx.ownGow` | `Pinned.lean:62` | **mejora**: ahora owners ⊆ gowners por construcción (`∩ gowners`), antes había que argumentarlo |
| `Pinned.mapId_eq` | `Pinned.lean:80` | el pin (`filterRequire`, `GPathM.lean:276`) sigue siendo por id de mapa |
| `isValidNode` | `GPathM.lean:111` | `is_root := n.id.parent_id.isNone` — sin cambio |

Que **PMP sobreviva es el resultado central del diseño de Julia**. Si el grupo
se hubiera formado por otra clave, PMP moriría y con ella
`chain_eq_of_mapIds_eq`, y el puerto sería inviable.

### 3.2 Se re-demuestran, con argumento nuevo pero disponible

* **`ChainSound_addNode`** (`AddNode.lean:~100`). Hoy el caso `self_owned` sale
  de que los owners del nodo nuevo *son* `gowners`. Con (c) hay que dar dos
  pasos: `sel k ∈ owners (sel (cs-1))` — es la posesión mutua que `ChainSound` ya
  lleva — y `sel k ∈ gowners` — es `ctx.ownGow`. **Ambos están.** El lema se
  alarga, no se cae.
* **Conservación / "no se pierde solución"** (`ConservationImproves.lean`). Mismo
  argumento: una cadena genuina que llega al paso `cs-1` por el nodo `n` se
  extiende por el nodo de la fila nueva cuyo grupo contiene `n`, y ese nodo
  hereda los owners de `n`. La extensión existe siempre porque **todo nodo de la
  última fila está en exactamente un grupo**. Este es el lema que hay que
  escribir primero y el que hay que medir en Julia antes de escribirlo.
* **`Sons.PMS` / `Sons.SN`** — el enlace hijo↔padre ahora es de un nodo a varios
  de la fila de abajo y de uno de abajo a **uno** de arriba. Es la misma forma,
  con la lista de padres del grupo en vez de la fila entera.

### 3.3 Rompen de verdad — y hay que decidir qué se hace

**El único punto serio del plan.** `ImprovesCima.FamTopSingle`
(`ImprovesCima.lean:3122`): *"el último paso de una familia tiene un nodo: su
cima"*. Con la fila, el último paso de un lado tiene **un nodo por abuelo
distinto**, no uno. Y `famTriOk_of_cone` (`:3139`) lo consume directamente: es la
mitad estructural del cono y lo que hace que el cuarto pick salga gratis.

Tres salidas, en orden de preferencia:

1. **Reformular a `FamTopSingleMod`**: el último paso tiene un nodo *por clase de
   `(parent_id, gparent_id)*`, y el cono se ancla en la clase de `t`, no en `t`.
   Es más trabajo pero es el enunciado honesto, y sospecho que es el que hace
   falta igualmente para el trío.
2. **Restringir `restTest`** para que el `famFix` corte además por la ventana de
   `t`, recuperando el singleton por definición. Barato, pero mueve la dificultad
   a demostrar que ese corte no pierde cadenas.
3. Dejar `W=2` en el camino de `ImprovesCima` y `W=3` solo en el camino del
   descenso. Descartada: rompe el diferencial de tres vías y deja dos máquinas.

**Segundo punto, menor:** `Up.lean` dice en su cabecera *"`up` adds exactly one
node, so the top line holds exactly one node and every chain is forced to select
it there (`chain_top_is_new`)"*. `chain_top_is_new` se usa en 2 ficheros
(`Up.lean`, `SubsetSemantics.lean`). Pasa a ser *"la cadena elige **algún** nodo
de la fila de arriba, y cuál está determinado por su `parent_id`"*. Con PMP vivo
(§3.1) esa determinación es inmediata, así que es reescritura, no investigación.

---

## 4. Lo que se compra: el invariante que da tríos

Aquí es donde el plan deja de ser refactor y pasa a ser el objetivo de v173 §5.

Con la ventana a 3 aparece un invariante nuevo, hermano de PMP, que hoy no se
puede ni enunciar:

```lean
/-- **GPMP** — el abuelo que el id declara es el padre de cada padre. -/
def GPMP (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ p ∈ n.parents, ∀ m ∈ h.nodes, m.id = p →
    n.id.gparent_id = p.parent_id
```

Sale de `shiftPid` por construcción, igual que PMP, y sobrevive a `Pruned` por el
mismo argumento (`PMP_of_pruned`, `ParentId.lean:105`, se copia línea a línea).

**Para qué sirve, dicho con precisión.** El muro de v173 §4 está en
`Descent.extend_of_common_owner` (`Descent.lean:42`), en esta hipótesis:

```lean
(hown : ∀ k, lo ≤ k → k < g.current_step → c ∈ ownersOf g (sel k))
```

*El nodo que baja debe ser dueño de todos los ya elegidos.* `extend_anchor`
(`:158`) lo da para uno; `extend_pair` (`:197`) para dos, usando
`AggOk` (`AggFixpoint.lean:294`), que es consistencia de **pares**. Para tres no
hay.

Con GPMP, los tres picks `sel lo`, `sel (lo-1)`, `sel (lo-2)` **dejan de ser tres
elecciones independientes**: los ids de mapa de los dos de abajo están escritos
dentro del id del de arriba (`parent_id` y `gparent_id`), y
`ParentId.chain_eq_of_mapIds_eq` dice que una cadena queda determinada por su
sucesión de ids de mapa. Así que `extend_triple` no necesita un testigo nuevo:
necesita que el testigo de `extend_pair` sea compatible con un dato que el
identificador **ya lleva encima**.

Y lo mismo, en la otra dirección, con `SpcSupport.SpcStable`
(`SpcSupport.lean:53`), que v173 §4 identifica como "la primerísima forma del
muro": necesita un owner común de `x`, `y` **y** `v`. Con la ventana a 3, `v` es
un componente del id de `x`, así que el owner común de `x` e `y` — que `AggOk` sí
da — es automáticamente compatible con `v`.

**Esta es la hipótesis del plan y hay que decirla como hipótesis:** que
`extend_triple` y `SpcStable` salgan de `AggOk` + GPMP. No está demostrado. Lo
que sí está establecido es que hoy no se pueden ni enunciar, y con la ventana sí.

---

## 5. Etapas, con puerta de build en cada una

Cada etapa termina con `lake build AbsSat` verde y `#print axioms` sin axiomas
nuevos. Nada de etapas largas: este refactor toca 65 ficheros y la única manera
de no perderse es que el build cierre cada pocos días.

**E0 — medir antes de tocar Lean (Julia, 1 sesión).**
Extender `test_window/compare.jl` con dos números que el plan necesita y que hoy
no tenemos:
* el **grado de entrada real** de la fila (cuántos abuelos distintos por fila),
  que es el factor de crecimiento de la §0 y el `c` de la §4;
* la **anchura inducida** de las familias del set sembrado.
Esto es la propuesta 2 de v173 §6, y decide si `c=3` basta o hay que hablar de
`c=4`. Si el grado de entrada resulta ser 2 en casi todo, el resto del plan se
abarata mucho.

**E1 — el campo, con default, sin cambiar nada más.**
`Alias.lean`, los 7 `PathNodeId.mk`, `as_key`, `dropList`. Build verde.
Comportamiento idéntico (todo el mundo construye con `gparent_id := none`).
Esta etapa **no debe cambiar un solo veredicto**, y eso es comprobable con el
diferencial de tres vías.

**E2 — `addRow` con `w = 2`.**
Sustituir `addNode` por `addRow 2`. Con `TL` vivo, `addRow 2 = addNode`
extensionalmente; demuéstralo como lema (`addRow_two_eq_addNode`) y usa ese lema
para que los ~65 ficheros no se enteren. **Es la etapa clave del plan**: si ese
lema sale, el resto del puerto es local; si no sale, hay que repasar `TL`.

**E3 — los owners de la fila (hechos (c) y (d)).**
Aquí sí cambia el comportamiento, con `w = 2` todavía. Se rehace
`ChainSound_addNode` y la conservación (§3.2). El diferencial contra Julia con
`WINDOW=2` debe seguir casando: Julia ya tiene este comportamiento, así que es
comparable hoy mismo.

**E4 — `w = 3` y GPMP.**
Se enuncia GPMP, se demuestra por construcción y bajo `Pruned`. `FamTopSingle`
se reformula (§3.3, salida 1). El diferencial pasa a comparar contra Julia con
`WINDOW=3`.

**E5 — cobrar: `extend_triple`.**
Lo de §4. Es lo único que no es puerto sino demostración nueva, y va al final a
propósito: hasta E4 todo es trabajo seguro con puerta de build, y si E5 no sale,
lo de E0–E4 sigue siendo una máquina mejor y un identificador más informativo.

---

## 6. Riesgos, ordenados por lo que me preocupan

1. **`FamTopSingle`** (§3.3). Es el único sitio donde no sé de antemano cuál de
   las tres salidas es la buena. Conviene atacarlo en E4 con tiempo, no de paso.
2. **El coste real de `c`.** Los 22 casos de `w3.tsv` son de 4–7 variables. El
   crecimiento de `peak_row` de 8→16 en `v7_c30_i1` es un factor 2 en una
   instancia pequeña; hay que ver si se estabiliza o si crece con el grado de
   entrada. Eso lo contesta E0.
3. **El default silencioso.** Que `{ id, parent_id }` siga compilando es lo que
   hace el puerto viable, pero también significa que un sitio que *debería*
   construir con abuelo y se queda en `none` **no da error de compilación**. Vale
   la pena un `#guard` o un test que recorra un gpath de `W=3` y compruebe que
   ningún nodo por encima del paso 1 tiene `gparent_id = none`.
4. **Lo que v130 avisó.** No aplica —ventana acotada, no camino— y v173 §5 ya lo
   descarta explícitamente. Lo dejo escrito para que no vuelva a aparecer.

---

## 7. Lo que este plan NO hace

* No toca la revisión agresiva. **Ese es el punto**: v173 §5 dice que la misma
  revisión de pares, sin modificar, pasa a dar tríos cuando el id lleva dos
  niveles. Si en algún momento hace falta tocar `aggPair`, es señal de que el
  diseño del id no está haciendo el trabajo.
* No promete el caso general. Lo que se compra, si E5 sale, es consistencia
  fuerte de orden `c+1` y completitud demostrable para las fórmulas cuya anchura
  inducida bajo el orden del mapa sea menor que `c` — una clase acotada, con
  matemática conocida detrás.
* No añade axiomas. Si alguna etapa los necesita, es que la etapa está mal
  dividida.
