# Plan — la ventana del identificador a 3 en la máquina `Improves` de Lean 4

**Estado: E1–E4 hechos salvo cinco módulos; E5 no empezado.**
Última actualización: 2026-09-21. Rama `spaik-window3`.

Ricardo: este documento era el plan de puerto del diseño de `julia/improves`
(`140bc3b`, `bd46899`) a la máquina pura de Lean. Ahora es a la vez el plan y el
parte: lo hecho está marcado, y lo que falta está descrito con el detalle
suficiente para que otro (o yo en otra sesión) lo retome sin reconstruir nada.

---

## 0. El cambio, y lo que costó cada mitad

Cuatro hechos, no uno. La clasificación del plan original se confirmó en la
práctica:

**(a) El identificador tiene tres componentes.** `PathNodeId` gana
`gparent_id : Option NodeId := none`. **Barato.** El `:= none` fue la decisión
que hizo el puerto viable: los ~83 ficheros que escriben `{ id := _, parent_id := _ }`
siguieron compilando sin tocarse.

**(b) El UP añade una fila, no un nodo.** `addNode` agrupa la última fila por el
identificador desplazado y crea un nodo por grupo. **Caro en volumen, barato en
ideas**: cambia la forma de ~65 ficheros (`addNode_nodes` pasa de `… ++ [n]` a
`… ++ newRow g d title`), pero cada reparación es la misma.

**(c) Los owners del nodo nuevo ya no son los globales.** `rowOwners = (⋃ owners
de los padres) ∩ gowners + él mismo`. **Caro en ideas.** Es lo que rompe el
atajo *"el nodo nuevo posee a todo el mundo"*, del que colgaban media docena de
construcciones (soportes, fabrics, cadenas).

**(d) La posesión vuelve solo a quien ya es owner.** **Caro en ideas.** Obligó a
un invariante nuevo (`OwnBelow`) para que la simetría siga siendo demostrable.

**Coste medido** (`test_window/w2.tsv` vs `w3.tsv`, 22 instancias): veredictos y
número de soluciones idénticos; nodos +0…+18 %; `peak_row` igual en 18 de 22 y
8→16 en el peor; segundos +5…+19 %.

---

## E1 — el campo, con default ✅ HECHO

`AbsSat/Utils/Alias.lean`. `PathNodeId` es ahora `(id, parent_id, gparent_id)` con
`gparent_id := none`. `as_key` imprime el tercer componente solo cuando lo hay,
así que un identificador de ventana 2 conserva su clave exacta y el diferencial
de tres vías contra Julia sigue casando.

Roto y arreglado, como predijo el plan: los 7 usos posicionales de
`PathNodeId.mk`, cuatro constructores anónimos `⟨d, map_parent⟩`, y los tres
`PathNodeId.mk.injEq`.

**Lo que el plan no anticipó:** E1 no es separable de E2. `chain_eq_of_mapIds_eq`
necesita fijar el tercer componente, y eso exige `GPMP`, que es falso mientras el
constructor sea el viejo. E1 y E2 se fundieron.

---

## E2 — `addNode` como fila ✅ HECHO

`AbsSat/GraphPath/Model/GPathM.lean`. Las piezas nuevas, todas ahí junto a
`addNode`:

```
shiftPid last d           -- (gp,p,last) + d ↦ (p,last,d)
newParents g              -- ids de la última fila
newRowIds g d             -- un id por desplazamiento, deduplicado
rowParents g d pid        -- los de la última fila que desplazan a pid
rowOwners g d pid         -- (⋃ owners de rowParents) ∩ gowners, + pid
rowNode / newRow
gainedSons / gainedOwners -- lo que gana un nodo viejo
upSons / upOwners / upMap
```

`Up.lean` conserva los lemas de forma; las definiciones se movieron a `GPathM`.

**Tres decisiones de diseño que se tomaron sobre la marcha:**

1. **Ventana fija a 3, sin parámetro `w`.** El plan proponía `addRow w` con
   `w = 2` como red de seguridad. Se descartó: `GPMP` es *falso* con ventana 2
   (el nodo nuevo declara `gparent = none` mientras sus padres tienen padre), así
   que mantener `w=2` no ahorra trabajo, lo duplica. El `W=2` de Julia sigue
   siendo la red de regresión, y allí ya hizo su trabajo.
2. **`dedupPids` propio en vez de `List.eraseDups`.** El core no demuestra ni
   `mem` ni `Nodup` de `eraseDups`; `dedupPids` da los dos en una inducción y con
   eso `Reader.nodup_addNode` sale.
3. **`rowOwners` corta contra `gowners` con un `filter` plano, no con
   `intersectOwners`.** Coinciden en todo estado que la máquina construye
   (`intersectOwners` solo difiere donde `gowners` calla por debajo de
   `current_step`, que es exactamente cuando `up` no dispara). El filtro plano da
   `rowOwners_mem_gowners_or_self` **sin hipótesis de validez**, que de otro modo
   habrían tenido que arrastrar decenas de lemas. Está documentado en el sitio.

**Comprobación de comportamiento** (tests del propio módulo, verdes): en el join
del libro las dos ramas ya **no se fusionan en el paso 3 sino en el 4** —
sus identificadores de paso 3 aún discrepan en el abuelo. 11 nodos en vez de 10.
El resto (cadena simple, filtro, UP de cláusula) es idéntico.

---

## E3 — los owners de la fila ✅ HECHO

Rehecho, con el argumento que el plan anticipó (la posesión mutua de `ChainSound`
más `ctx.ownGow`):

* `ChainSound_addNode`, `ChainG_addNode` (`AddNode.lean`, `L6Up.lean`)
* `Exactness.tablesSound_addNode`, `RunInhabited.soundAt_addNode`
* `ConservationCore`, `Conservation`, `PrefixConservation`
* `Reader.OwnSymmetric_addNode` — el hecho (d) en su forma exacta: un nodo gana
  un id de fila **exactamente cuando ese nodo de fila lo posee**, así que las dos
  direcciones son el mismo hecho por construcción.

**Invariante nuevo: `SelfOwn.OwnBelow`** — *los owners viven por debajo de
`current_step`*. Trivial mientras el UP repartía `gowners` enteros; con la fila
es lo que descarta que la tabla de un nodo *viejo* ya contenga un identificador
fresco, que es justo lo que `OwnSymmetric_addNode` necesita. Probado para
semilla, `addNode`, `join`, `Pruned` y `Reachable`, y añadido como campo `ownb`
de `Reader.RCtx`.

---

## E4 — `GPMP` ✅ HECHO (es el resultado)

`ParentId.lean`:

```lean
def GPMP (h : GPathM) : Prop :=
  (∀ n ∈ h.nodes, ∀ p ∈ n.parents, n.id.gparent_id = p.parent_id) ∧
  (∀ n ∈ h.nodes, n.id.parent_id = none → n.id.gparent_id = none)
```

`ParentId.GPMP_reachable` — **sin axiomas** (`[propext, Quot.sound]`). Sale por
construcción: `shiftPid` copia el `parent_id` del padre en el `gparent_id` del
hijo, y los padres de un nodo de fila son exactamente los que desplazan a su
identificador, así que coinciden en él. La segunda cláusula (una raíz no declara
abuelo) hace falta para el caso base de `pid_unique`.

Campo `gpmp` añadido a `Pinned.Ctx` y a `Reader.RCtx`.

**Lo que ya cobra:**

* **`ParentWitness.parents_differ_below`** pasó de *"dos padres se separan en su
  `parent_id`"* a **"dos padres de un nodo difieren solo en el abuelo"** —
  comparten id de mapa por `PMP` y padre por `GPMP`. Es el nivel extra de
  historia, dicho como teorema.
* **`PMP` ya no necesita `TL`.** Con el nodo único hacía falta que toda la fila
  de arriba llevara `map_parent`; con la fila sale por construcción. La hipótesis
  se dejó como `_htl` para no tocar llamadas.
* `Pinned.pid_unique` y `ParentId.chain_eq_of_mapIds_eq` fijan los tres
  componentes. `PinExtends.eq_of_ids` también.
* **`RunNoBorrow.Genuine`** (un camino genuino) lleva ahora el tercer componente,
  y `canon` lo produce. `eq_of_along` lo demuestra con `GPMP` sin coste: lee el
  abuelo del padre de la propia cadena.
* **`PairPins.entryPins`** fija también los abuelos de los dos extremos. Un
  nivel más de fijación es exactamente lo que pide el tercer componente.

---

## Retiradas, con su razón

**`SymTriReview.lean` — borrado (1757 líneas).** Tuya la indicación: modelaba una
revisión triangular abstracta que la máquina no ejecuta. Solo se usaban fuera
`Below`, `Below_addNode`, `Below_join`, `okJoin_step` y los dos lemas de
`isValidNode`; están en `SelfOwn.lean`. `SymCampaign` pierde `--mode symtri`.

**`FabricAdd.FabricAt_addNode_new` y su corolario — retirados.** Decían *"el
fabric del nodo nuevo vive dentro de sus propios owners"*, y su prueba era una
línea de `gow`: el nodo nuevo recibía `gowners` enteros. Con la fila es **falso**:
un nodo de fila hereda solo lo de sus padres. La versión por rama que sería
cierta no la consumía nadie fuera del fichero. Está documentado en el sitio.

**`ReviewJoin` — condición lateral explícita.** "El UP distribuye sobre el join"
ya no sale sin que las tablas de owners de cada lado estén dentro de sus propios
`gowners` (y sus gowners sean nodos). Se añadió `ReviewJoin.OwnGowPinned` en vez
de perder `sat_of_reviewJoin`; arrastra a `SupportSplit.sat_of_split`,
`sat_of_cover` y `PartSplitReal.sat_of_survivors`/`sat_of_paths`.

**`FabricAdd.Fabric_addNode` — rediseñado, no retirado.** `addS`/`addT` pasan de
*"el nodo nuevo se relaciona con todos los miembros"* a *"cada nodo de fila se
relaciona con lo que llevan sus propios padres"* (`rowRel`). Necesita dos
hipótesis nuevas que el contexto ya da: todo nodo es miembro (`hallNode`) y
`OOS`. Esta última es la que convierte *"un owner al mismo paso"* en *"el nodo
mismo"*, y es la pieza que hace que el rediseño cierre.

---

## Lo que falta — al detalle

### F1. `HereditaryUp.add_new` — el único que no es puerto mecánico

**Qué es.** U2 de la validez hereditaria de pines: si `F` es válido bajo
`C ++ [pin q]` y `A = addNode F d ""` es válido bajo `C`, entonces `A` es válido
bajo `C ++ [pin q]`. La prueba construye un soporte `Sup (filterWeakAll A C') S R`
sobre `B = Fw F C'`.

**Por qué rompe.** El soporte viejo es `S p := Mem B p ∨ p = new` con `R`
relacionando `new` con **todos** los miembros. Con la fila `new` no posee a todos:
posee lo que poseen sus padres. La cláusula `cov` (cada miembro tiene un
relacionado en cada paso) falla para un miembro cuyo owner del paso de arriba no
sea el padre de `new`.

**Diseño que sí cierra** (verificado a mano cláusula por cláusula, no escrito aún):

```lean
Row z   := ∃ c, Mem B c ∧ c.id.step = F.current_step - 1 ∧ z = shiftPid c d
S p     := Mem B p ∨ Row p
Rw z v  := ∃ c, Mem B c ∧ c.id.step = F.current_step - 1 ∧ z = shiftPid c d ∧ Rel B c v
R x v   := (Mem B x ∧ Mem B v ∧ Rel B x v)
         ∨ (Rw x v ∧ Mem B v)
         ∨ (Rw v x ∧ Mem B x)
         ∨ (Row x ∧ x = v)
```

Es decir: **el soporte contiene toda la fila superviviente**, cada nodo de fila
se relaciona hacia abajo a través de *algún* padre suyo que siga vivo en `B`, y
**dos nodos de fila se relacionan solo si son iguales**.

La pieza que lo hace funcionar, y que conviene tener presente porque reaparece:

> `Rel B a b` con `a.id.step = b.id.step` implica `a = b`, por `OOS` (un owner al
> paso propio *es* el nodo).

Con ella:
* `son` para `x` en el paso `cs-1` y `v` un nodo de fila: el hijo es
  `shiftPid x d`, y el `c'` que testifica `Rw v x` está al mismo paso que `x`,
  luego `c' = x` y `v = shiftPid x d`. Cierra.
* `link` para `x` de fila y `c` al paso `cs-1`: el testigo de `Rw x c` está al
  mismo paso que `c`, luego es `c`, luego `c ∈ rowParents F d x`. Cierra.
* `agg` para dos miembros a paso `cs`: `supB.agg x v _ (cs-1)` da un owner común
  `c`; el nodo de fila es `shiftPid c d`. Cierra.
* `cov` para un miembro a paso `cs`: su owner en `cs-1` da el nodo de fila.
* `par`/`cov` para un nodo de fila: por su padre testigo.

Trabajo estimado: ~300 líneas de prueba nueva, mecánicas una vez fijado el
diseño. Es el único punto del puerto donde hay que pensar.

### F2. Cuatro ficheros con reparación mecánica pendiente

Están detrás de `HereditaryUp` en el grafo de build, así que el build no ha
llegado a ellos; la forma de la reparación es la que ya se aplicó 35 veces.

| fichero | referencias | forma de la reparación |
|---|---|---|
| `ClauseReview.lean` | 4 | `newPid F d` → *el nodo de fila que la cadena alcanza*; el `x = newPid` de `htop` pasa a `x ∈ newRowIds` |
| `PinHistory.lean` | 1 | un `simp only [addOwner, upNode, newPid]` → `rowNode_owners` |
| `PinSend.lean` | 9 | `notnew`/`top`: "el único nodo del paso nuevo" → "un nodo de la fila"; `newPid G d = newPid B d` → las filas coinciden porque las líneas de arriba coinciden |
| `PinDeath.lean` | 8 | `addNode_gowners` con `[newPid]` → `newRowIds`; los tres `newOk`/`oldOk` sobre `gowners ++ [newPid]` |

Ninguno debería necesitar una idea nueva: todos son el patrón
`rcases … with ⟨n, hn, rfl⟩ | ⟨pid, hpid, rfl⟩` más `mapId_of_mem_newRowIds`.

### F3. Puerta final

* `lake build AbsSat` verde (231 jobs).
* Los `#print axioms` de los teoremas cabecera sin axiomas nuevos. **Atención**:
  varios `#guard_msgs` se rompen por sí solos cuando un teorema pasa a depender
  de `sorryAx` — sirven de alarma, no los quites.
* Diferencial de tres vías contra Julia con `WINDOW=3`: verdicto y número de
  soluciones por instancia. El harness de Julia ya existe
  (`test_window/compare.jl`); falta el lado Lean (`lake exe improves-diff`).

### F4. E5 — cobrar la ventana ❌ NO EMPEZADO

Lo único que no es puerto sino demostración nueva, y va al final a propósito.

**El muro, con la línea exacta.** `Descent.extend_of_common_owner`
(`Descent.lean:42`) pide

```lean
(hown : ∀ k, lo ≤ k → k < g.current_step → c ∈ ownersOf g (sel k))
```

*el nodo que baja debe ser dueño de todos los ya elegidos*. `extend_anchor` lo da
para uno, `extend_pair` para dos usando `AggOk` (consistencia de **pares**). Para
tres no hay.

**Lo que ahora se puede intentar y antes no.** Con `GPMP` demostrado, los picks
`sel lo`, `sel (lo-1)`, `sel (lo-2)` **dejan de ser tres elecciones
independientes**: los ids de mapa de los dos de abajo están escritos dentro del
id del de arriba, y `chain_eq_of_mapIds_eq` dice que la cadena queda determinada
por su sucesión de ids de mapa. La forma concreta del enunciado a demostrar:

```lean
theorem extend_triple (g : GPathM) (a : Adj g) (hok : AggOk g) (hgpmp : GPMP g)
    (hpos : 3 < g.current_step) … : SoundFrom g (upd sel (lo-1) c) (lo-1)
```

y su hermano en `SpcSupport.SpcStable` (`SpcSupport.lean:53`), que v173 §4
identifica como *"la primerísima forma del muro"*: pide un owner común de `x`,
`y` **y** `v`; con la ventana, `v` es un componente del id de `x`.

**Esto es una hipótesis, no un hecho.** Lo establecido es que antes no se podía
ni enunciar y ahora sí, y que la pieza que lo hará cerrar —si cierra— es la misma
que cerró `FabricAdd` y cerrará `add_new`: *un owner al mismo paso es el nodo
mismo*.

### F5. Medición pendiente (era E0, se saltó)

No se midió y sigue mereciendo la pena:

* **grado de entrada real de la fila** (cuántos abuelos distintos por fila) — es
  el factor de crecimiento y el `c` de la §4 de v173;
* **anchura inducida** de las familias del set sembrado.

Con esos dos números se sabe de golpe si `c = 3` basta o hay que hablar de `c=4`,
y qué clase de fórmulas queda cubierta. `test_window/compare.jl` ya instrumenta
`peak_row` y `peak_nodes`; falta contar abuelos distintos por fila.

---

## Riesgos, revisados

1. ~~`FamTopSingle`~~ — **no se materializó.** `ImprovesCima` compila sin tocarse:
   `famFix` restringe por `restTest` a nivel de `PathNodeId`, no por id de mapa,
   así que el cono sigue anclado en el nodo `t` que nombra. Era el riesgo nº 1 del
   plan y resultó ser aire.
2. **El default silencioso** sigue vivo: `{ id, parent_id }` compila y significa
   ventana 2. Vale la pena un test que recorra un gpath de `W=3` y compruebe que
   ningún nodo por encima del paso 1 tiene `gparent_id = none`. **No hecho.**
3. **El coste de `c`** — pendiente de F5.
4. Lo que v130 avisó no aplica (ventana acotada, no camino), como ya decía v173 §5.
