# Plan — la ventana del identificador a 3 en la máquina `Improves` de Lean 4

**Estado: E1–E4 hechos; F1 hecho; F2 hecho salvo `ImprovesCima`; F4 parcial (la clase `SingleParents`, cerrada).**
Última actualización: 2026-09-21. Rama `spaik-window3`.
`lake build AbsSat` llega a 226/231; lo que queda es una decisión de diseño, no
reparación mecánica (ver F2).

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

### F1. `HereditaryUp.add_new` ✅ HECHO

U2 de la validez hereditaria de pines. El soporte viejo era *`B` más un nodo
relacionado con todo el mundo*; ahora es **`B` más la fila superviviente**: un
nodo de fila `shiftPid c d` por cada miembro `c` del paso viejo de arriba
(`SupRow`), relacionado hacia abajo solo a través de *sus propios* padres
(`SupRw`), y dos nodos de fila relacionados solo si son iguales.

La pieza que cierra `son`, `link` y `agg` es la que el plan anticipó y que
reaparece en todas partes:

> `relSame`: por `OOS`, un owner al paso propio *es* el nodo. Un testigo forzado
> al paso viejo de arriba es el padre del que vino.

`add_new` gana `hpos : 0 < F.current_step`, que su único llamador descarga con
`SNN`. `hpv_addNode` sale detrás: `newPid` → `newRowIds`, y el pin sobre un id de
fila es un noop **para toda la fila**, porque todos los ids de fila llevan el
mismo id de mapa `d`.

**Un aviso que costó una hora y conviene no repetir.** `SupRow` y `SupRw` son
definiciones de nivel superior, no `let` locales, a propósito: `omega`
zeta-reduce un `let` y entonces parte por casos la ecuación de pasos que hay
dentro *usando `Classical`*. Con `let`, `add_new` cerraba con
`[propext, Classical.choice, Quot.sound]` y eso se habría propagado a todos los
`#print axioms` de abajo. Como definiciones son opacas a `omega` y el cierre
vuelve a ser `[propext, Quot.sound]`, ahora con su propio `#guard_msgs`.

### F2. El resto del puerto — hecho salvo dos ficheros

La lista de cuatro ficheros del plan se quedó corta: detrás de `HereditaryUp`
había más, y no todo era mecánico. Lo hecho, en orden de build:

| fichero | qué hacía falta |
|---|---|
| `RunHistory` | `tops_addNode` ya no dice *"el top es `newPid`"* sino *"el top lleva `d` y anota **algún** nodo de la línea vieja como padre"*; el testigo se vuelve a convertir en la clave por `ParentId.TL`, igual que en `sendsOk_send` |
| `ClauseReview` | `extend_genuine` construye `shiftPid (sel m) d` en vez de `⟨d, some p⟩` (y pierde `p`/`hp`: el identificador se lee de la cadena). En `clauseWitness_of_glue`, un nodo del top ya no lo posee todo: `q` llega a `x` por **un padre propio** `r`, y el testigo es la cadena del pegamento para `r`, cuya extensión aterriza justo en `x` |
| `PinHistory` | mecánico (`mem_newRow_iff` en vez del singleton) |
| `PinSend` | el `top` de `pin_send` pasa de *"un miembro por encima **es** el nodo nuevo"* a *"es un nodo de fila, y baja solo por un padre propio"* — literalmente `supS.par` leído al paso nuevo. Con eso el encaje en el envío de `B` sale nodo a nodo |
| `PinVar`, `PinClause` | el tercer componente allí donde se escribe un id a mano: `path_facts`, `canon_of_path`, `selA`, `onA`, `glue_canon` |

Se añadió `GPathM.step_of_mem_newParents`, que tres de esos argumentos pedían.

**Lo que queda, y por qué no es mecánico: `PinDeath` + `ImprovesCima`.**

```lean
/-- El nodo top que un lado deja en la unión: la clave, sobre la clave del lado. -/
def topOf (p k : NodeId) : PathNodeId := { id := p, parent_id := some k }
```

`topOf` es el riesgo nº 2 de la lista de abajo materializado: compila por el
`:= none` del tercer campo, y significa ventana 2. La suposición que codifica —
**un lado deja un único nodo top en la unión, nombrado por (id de mapa, clave)** —
es justo la que rompe la fila: un lado deja ahora *un top por cada nodo
superviviente de su línea anterior*, y dos de ellos comparten `(p, kv.1)` y
difieren en el abuelo. Por eso `htopSent` (`PinDeath:666`) es hoy literalmente
falso, no mal tipado.

El puerto pide decidir qué es "el top de un lado" con la ventana, y propagarlo:
24 usos en `PinDeath`, 50 en `ImprovesCima`. Dos formas obvias:

1. `topOf` pasa a ser `shiftPid c p` y todo enunciado sobre *el* top de un lado
   pasa a ser sobre *un nodo de la fila del lado*. Es lo que hace la máquina, y
   es lo mismo que se hizo en `pin_send`.
2. `topOf p k` sobrevive como *clase*: el conjunto de tops de un lado, todos con
   `id = p` y `parent_id = some k`. Más barato de propagar, pero hay que
   comprobar que `famFix`/`restTest` de `ImprovesCima` aguantan un cono con
   varios anclajes — y el riesgo nº 1 del plan (`FamTopSingle`) volvería, esta
   vez de verdad.

No se eligió ninguna: es una decisión, no una reparación.

### F3. Puerta final

* `lake build AbsSat` verde (231 jobs). **Hoy: 226/231**, parado en `PinDeath`.
* Los `#print axioms` de los teoremas cabecera sin axiomas nuevos. **Atención**:
  varios `#guard_msgs` se rompen por sí solos cuando un teorema pasa a depender
  de `sorryAx` — sirven de alarma, no los quites.
* Diferencial de tres vías contra Julia con `WINDOW=3`: verdicto y número de
  soluciones por instancia. El harness de Julia ya existe
  (`test_window/compare.jl`); falta el lado Lean (`lake exe improves-diff`).

### F4. E5 — cobrar la ventana ⚠️ PARCIAL: la clase, hecha; el caso general, no

**Lo primero que hay que decir es que el plan miraba al sitio equivocado.** El
muro ya estaba medio demostrado en el repo, bajo una hipótesis que esta sección
no nombraba: `ParentWitness.par_witness_triple` cierra exactamente el paso de
pareja a terna —el `extend_triple` que se proponía enunciar— bajo
`SingleParent n`, *el nodo que se extiende tiene un solo padre*. Al lado,
`owners_below_unique` demuestra que con `SingleParents g` el pasado entero de un
nodo es un camino forzado. Ninguno de los dos lo consumía nadie.

**Hecho (`commonOwner_of_singleParents`, `sat_of_singleParents`, sin axiomas).**
Toda la ruta C cuelga de una sola hipótesis, `Descent.CommonOwner g`. Y:

> `SingleParents g` ⟹ `CommonOwner g`.

En ~30 líneas: el pick en `lo` no es raíz, luego tiene un padre `c`, y
`SingleParents` lo hace *el* padre; para cada pick de arriba la consistencia de
pares (`shared_owner`) da un owner común en el paso `lo-1`; y un owner **exacto­
mente un paso por debajo** de un nodo *es* un padre suyo
(`owners_below_iff_parents`), así que cada uno de esos testigos es `c`. La
intersección `k`-aria que pide el descenso es la binaria, leída `k` veces en el
mismo nodo. `NoDeadEndVerdict.sat_of_singleParents` cierra el veredicto para esa
clase sin ninguna hipótesis abierta.

**Qué compra la ventana, exactamente.** Un nodo tiene varios padres ⟺ dos nodos
de la línea anterior comparten `(id de mapa, id de mapa del padre)` y difieren en
el abuelo — es `parents_differ_below` leído al revés. Generalizando a ventana
`w`: dos padres coinciden en `w-1` componentes y difieren, como mucho, en el más
viejo. De ahí dos consecuencias:

* **Ensanchar `w` nunca convierte `SingleParents` en teorema.** El desacuerdo no
  desaparece, se muda al componente más antiguo. La pregunta de F5 —*¿basta
  `c=3` o hay que hablar de `c=4`?*— tiene por esta vía respuesta negativa para
  todo `c`.
* **Pero ensanchar `w` agranda la clase donde vale**, porque fusionar exige
  coincidir en `w-1` pasos de historia en vez de `w-2`. Eso, y no otra cosa, es
  lo que se compra con el +0…18 % de nodos medido en §0.

**Lo que sigue abierto** es el `extend_triple` *sin* `SingleParent`: elegir,
entre padres que solo difieren en el abuelo, uno que posea a los tres picks. La
ventana ancla dos de los tres componentes del candidato y deja libre justo el
tercero, que es donde los padres difieren. No lo cierra. El hermano en
`SpcSupport.SpcStable` (`SpcSupport.lean:53`) sigue igual: pide un owner común de
`x`, `y` **y** `v`, y `Spc` recorre parejas arbitrarias, no enlaces de padre, así
que la determinación por identificador no le llega.

### F5. Medición pendiente (era E0, se saltó)

No se midió y sigue mereciendo la pena:

* **grado de entrada real de la fila** (cuántos abuelos distintos por fila) — es
  el factor de crecimiento, y **es también la medición de F4**: el grado de
  entrada de la fila es exactamente el número de veces que `SingleParents` falla,
  o sea el tamaño del complemento de la clase que F4 ya cierra. Si sale 1 casi
  siempre, la clase es casi todo; si sale 3, es casi nada;
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
2. ~~**El default silencioso**~~ — **se materializó**, y es lo que queda de F2:
   `PinDeath.topOf` estaba escrito `{ id := p, parent_id := some k }`, compiló
   sin ruido y significa ventana 2. El test propuesto (recorrer un gpath de
   `W=3` y comprobar que ningún nodo por encima del paso 1 tiene
   `gparent_id = none`) lo habría cazado meses antes. **Sigue sin hacerse y
   sigue mereciendo la pena.**
3. **El coste de `c`** — pendiente de F5.
4. Lo que v130 avisó no aplica (ventana acotada, no camino), como ya decía v173 §5.
