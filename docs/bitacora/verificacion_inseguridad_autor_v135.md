# Verificación para el Autor v135: tablas exactas por construcción, y dónde vive el hueco

Ricardo, soy Claude (Opus 5). Formalicé la ruta por construcción que hablamos: tomar la **exactitud
de las tablas** como invariante y cerrarla operación a operación. Cerré tres de las cuatro (semilla,
UP y join) y una de las dos mitades es incluso un teorema incondicional.

Pero al escribirlo tuve que corregir algo que te dije en la conversación, y la corrección es el
contenido más útil de este informe: **la exactitud a nivel de entradas no implica `CommonOwner`**. No
es un detalle técnico; es exactamente el salto de 2-consistencia a k-consistencia, visto desde otro
ángulo. Lo explico en §4 y reorganizo todo el mapa a partir de ahí.

Rama `spaik`, build de `AbsSat` (192 jobs), sin `sorry`, `[propext, Quot.sound]`.

---

## 1. Qué es la exactitud, y por qué es el invariante natural

```lean
def Realizes (g : GPathM) (x q : PathNodeId) : Prop :=
  ∃ sel, ChainSound g sel ∧ sel x.id.step = x ∧ sel q.id.step = q
```

`Realizes g x q` dice: **hay un camino completo de `g` que pasa por `x` y elige `q`**. Con eso, la
exactitud es la igualdad entre lo que las tablas dicen y lo que los caminos hacen:

```lean
def TablesComplete (g) : Prop := realizable ⇒ está en la tabla
def TablesSound    (g) : Prop := está en la tabla ⇒ realizable
def Exact (g) : Prop := TablesComplete g ∧ TablesSound g
```

Por qué es el invariante natural y no `CommonOwner`: es **semántico** —habla de caminos, no de
patrones dentro de las tablas— y se puede atacar **operación a operación**, que es como tú construyes
la máquina. `CommonOwner`, en cambio, es una propiedad global de un estado ya construido.

## 2. La mitad fácil es gratis, y más de lo que creía

> `tablesComplete (g : GPathM) : TablesComplete g`

**Para todo estado, sin hipótesis y sin inducción.** La razón es corta: una cadena `ChainSound`
satisface pertenencia mutua por definición, así que lo que una cadena elige **ya está** en la tabla
del nodo por el que pasa.

En la conversación te dije que esta mitad era `ChainSound_filterAllAgg` ("no se pierde ninguna
solución"). Es más simple que eso: no hace falta ningún teorema de conservación. Y `ChainSound_filterAllAgg`
sí hace falta, pero en la **otra** mitad y solo en el filtro.

Significado: **la máquina nunca olvida**. Ninguna elección que un camino real realiza deja de estar
anotada. Esa dirección de la corrección no depende de nada.

## 3. La mitad difícil, cerrada en tres operaciones

`TablesSound` es la que pesa: **las tablas no mienten**, nada de lo anotado es irrealizable.

| operación | teorema | por qué sale |
|---|---|---|
| semilla | `tablesSound_initSeed` | un solo nodo, que se posee solo a sí mismo; la cadena constante lo realiza |
| **UP** | `tablesSound_addNode` | la cadena que realizaba una entrada vieja **se extiende** con el nodo nuevo (`ChainSound_addNode`); y la tabla del nodo nuevo son los owners globales del estado, cada uno realizado por la cadena que pasa por él mismo |
| **join** | `tablesSound_join` | **gratis**: toda entrada de un nodo unido viene de un lado (`join_owners_source`), y la cadena que la realiza allí **es** una cadena de la unión, por los mismos nodos |

**El join merece un comentario**, porque es el caso que me costó v128–v132 como problema combinatorio y
aquí es trivial. La diferencia está en la pregunta: combinatoriamente yo preguntaba *"¿esta cadena de la
unión vive en un solo lado?"*, que es dura y obligó a medir un millón de cadenas. Semánticamente solo
pregunto *"¿esta entrada es realizable en la unión?"*, y para eso basta el realizador del lado, porque
sus caminos son caminos de la unión. **La ruta semántica esquiva por completo la cuestión de las cadenas
mezcladas.** Es el mejor argumento a favor de atacar por construcción.

Queda **una operación y una dirección**: `FilterSound`, la mitad de solidez en el filtro. Una entrada
que sobrevive a las fijaciones y al review era realizable antes, pero su realizador puede romper la
fijación, y volver a realizarla es el descenso otra vez.

## 4. La corrección: exactitud de entradas ≠ `CommonOwner`

Te dije que `Exact` implicaba `CommonOwner` de forma inmediata. **No es así**, y vale la pena ver por
qué, porque es el hueco de siempre en su forma más nítida.

`Exact` habla de **entradas**: para cada par (nodo, elección anotada) hay *un* camino que lo realiza.
`CommonOwner` habla de **cadenas**: dada una cadena parcial —muchos picks a la vez— hace falta un nodo
del paso inferior que **todos** compartan, o sea *un* camino que pase por **todos** los picks.

Y de "cada entrada tiene su camino" no se sigue "hay un camino común a todos los picks": cada entrada
puede estar realizada por un camino **distinto**. Exactamente igual que la consistencia de pares no da
la consistencia del conjunto.

Así que hay **dos niveles** de exactitud, y la máquina vive entre ellos:

| nivel | enunciado | quién lo necesita | estado |
|---|---|---|---|
| **entradas** (pares) | cada entrada de una tabla está realizada por algún camino | — | semilla, UP y **join** cerrados; falta el **filtro** |
| **cadenas** (conjuntos) | cada cadena parcial se extiende a un camino completo | el veredicto (`CommonOwner`) | semilla y UP cerrados; el **join** necesita cadenas no mezcladas; falta el **filtro** |

**El hueco de la máquina es precisamente el salto de un nivel al otro.** Es la misma cosa que
"2-consistencia frente a k-consistencia" de v134, pero ahora se ve *dónde* está: no en una operación
concreta, sino en la diferencia entre lo que las tablas guardan (pares) y lo que el lector necesita
(conjuntos).

Nota la asimetría, que es informativa: **en el nivel de entradas el join es gratis y en el de cadenas
es duro**; en los dos niveles el filtro está abierto. Las tablas por pares son suficientes para que las
uniones no mientan, pero no para que las uniones no rompan cadenas.

## 5. Cómo queda todo

**Dos direcciones del veredicto:**

| dirección | estado |
|---|---|
| UNSAT: ejecución vacía ⟹ φ insatisfacible | **demostrado sin hipótesis** (`pureRunW_ne_nil`) |
| SAT con camino: el lector entrega un camino ⟹ φ satisfacible | **demostrado sin hipótesis** (`sat_of_denotS`), y el camino se verifica en tiempo lineal fuera de la máquina |
| SAT desde la validez: estado válido ⟹ φ satisfacible | **demostrado bajo `CommonOwner`** (`sat_of_commonOwner`) |

**Las dos rutas hacia `CommonOwner`, con su estado real:**

| ruta | qué pide | cerrado | abierto |
|---|---|---|---|
| **descenso** (nivel cadenas) | `CommonOwner` directamente | el escalón entero salvo el owner común (`extend_of_common_owner`: las otras seis condiciones salen de los invariantes); anclas (`topAnchor_of`); semilla y UP (`noDeadEnd_addNode`); join de un lado (`noDeadEnd_join`); seis de siete condiciones del join mezclado (`soundFrom_left_of_entries`) | el owner común; cadenas mezcladas (`JoinCoveredF`, medida vacía en 1.027.901 cadenas); el filtro |
| **exactitud** (nivel entradas) | `Exact` | la mitad `TablesComplete` **incondicional**; `TablesSound` en semilla, UP y **join** | `FilterSound`; y el salto de entradas a cadenas (§4) |

**Lo demostrado hoy, en una línea**: la ruta por construcción cierra la mitad fácil sin condiciones y
la difícil en tres de cuatro operaciones, incluido el join que era el caso duro por la otra ruta; y
queda identificado que ninguna de las dos rutas evita el salto entre niveles.

## 6. Qué haría falta en cada ruta

**Ruta descenso.** Falta el owner común. Cinco reducciones locales están refutadas por medida (v130,
v132), así que no queda atajo combinatorio; tendría que venir de la construcción, y por eso probé la
otra ruta.

**Ruta exactitud.** Falta `FilterSound` —el realizador que rompe la fijación— y, aunque se cerrara,
haría falta subir de entradas a cadenas. Ahí es donde la idea de **testigos** tiene sentido, y ahora se
puede plantear con precisión por niveles:

- **un testigo por entrada** (el camino que la realiza, o su proyección a nodos de mapa): cuesta un
  factor del número de pasos, **polinómico**. Hace `FilterSound` inmediato —una entrada sobrevive si y
  solo si su testigo sobrevive— pero **no** sube al nivel de cadenas, porque los testigos de entradas
  distintas siguen siendo caminos distintos.
- **un testigo por cadena parcial**: eso sí daría el nivel de cadenas, pero el número de cadenas
  parciales no está acotado polinómicamente, así que no cabe.

Esa asimetría es, creo, el resultado conceptual del tramo: **el nivel de entradas es asequible y
barato; el nivel de cadenas es el que el veredicto necesita y el que no cabe en un testigo por
entrada.** Si hubiera que apostar por un cambio de diseño, apostaría por guardar el testigo por entrada
y ver cuánto del nivel de cadenas se deduce de él con las invariantes que ya hay —esa es una pregunta
abierta concreta y, a diferencia de las cinco reglas refutadas, no la he medido todavía.

## 7. Pendiente, fuera de mi alcance

El `push` a `origin` sigue fallando con 403 (credenciales `ricautomation`); los commits están en local
sobre `spaik`. La URL de `origin` lleva un token personal en claro: conviene revocarlo.
