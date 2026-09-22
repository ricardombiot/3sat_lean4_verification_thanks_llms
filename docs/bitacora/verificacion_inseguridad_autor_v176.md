# Verificación para el Autor v176: tres de las cuatro operaciones cerradas, y el residuo reducido a una elección binaria

Ricardo, soy Claude (Opus 5). Este informe continúa el v175 del mismo día. Allí el frente era
`TablesSound` y no sabíamos por dónde entrarle; aquí se ataca por la **construcción** de la máquina
y caen tres de sus cuatro operaciones, más dos de las cuatro familias de pasos de la cuarta.

Rama `spaik-window3`. `lake build AbsSat` verde (239 jobs), `lake exe runTests` verde, sin `sorry`.
Todos los cierres `[propext, Quot.sound]`, con dos más estrictos anotados abajo.

Once commits: `f7c9a89`, `24aadda`, `417a948`, `95f6bcf`, `e79be32`, `94bf29a`, `187a334`,
`0d052cf`, `8fa5d6a`, más `0d2cba0` y `e6aa171` de medidas.

---

## 0. Resumen

* **`TablesSound` por la construcción**: `doJoin` y `up` cerrados (`TablesSoundBuild.lean`). Con la
  revisión, que ya estaba, son **tres de las cuatro** operaciones.
* **El filtro, la cuarta, se parte en cuatro familias de pasos**, y dos se cierran enteras: los
  pasos **sin requisitos** (`n + 2` de los `2n + m + 2`) y los pasos **impares**, donde el filtro no
  elige, solo comprueba.
* **El residuo se recortó por dentro dos veces**: primero al caso en que el nodo conserva las dos
  opciones (65–90 % de los casos quedan cerrados, medido), y después de un **par de nodos** a **un
  nodo y una elección binaria**.
* **Tus tres frases, escritas como teoremas**: la del filtro que limpia lo incompatible, la de que
  el review deja solo caminos, y la de que un nodo que sigue presente tiene camino. Las tres salen.
* **Una medida nueva sin excepción**: `PinKeepsOwnTable`, 205.091 entradas, 0 perdidas.

---

## 1. Por qué la construcción y no el punto fijo

El v175 terminaba con `TablesSound` como frente y con cinco reformulaciones suyas que volvían todas
al mismo sitio. La razón quedó escrita al probar la vuelta:

* `ReaderChain.ownTable_of_tablesSound` — `TablesSound P` da `PinKeepsOwnTable` en `P`.

Con las dos direcciones en la mano, el dato es este: **la única garantía de conservación que la
criba ofrece es «estar en una cadena»**. Por eso `PinPairSound`, `RootPinChained`,
`PinKeepsPartner` y `PinKeepsOwnTable` terminan todas pidiendo `TablesSound`. No es mala suerte: el
punto fijo de la criba no sabe conservar nada más.

De ahí la decisión: **atacar por la construcción**, que es donde `readerVerdictBT_iff` se cerró sin
hipótesis.

---

## 2. `doJoin` y `up`

`TablesSoundBuild.lean`.

### 2.1 El join no inventa nada

```lean
tablesSound_join (hok : okJoin g₁ g₂) : TablesSound g₁ → TablesSound g₂ → TablesSound (join g₁ g₂)
```

Toda entrada del nodo fusionado viene de uno de los dos lados (`join_owners_source`), y una cadena
de un lado **sigue siendo cadena de la unión** — el join solo añade: nodos, padres, hijos, owners y
owners globales, todos crecen. `ChainSound_join_left`/`_right` estaban escritos desde hace tiempo;
nadie los había apuntado a esto.

Confirma lo que dijiste de la unión: no pierde nada, y por eso no puede romper la sanidad.

### 2.2 El `up` es `rowOwners` leído literal

```lean
tablesSound_addNode : TablesSound g → TablesSound (addNode g d title)
```

Dos familias de entradas. Las **viejas** se extienden con `extend`. Las **nuevas** vienen de
`rowOwners`, o sea de un **padre de fila**, y la cadena que las realizaba en el estado de antes
entra en la fila justo por ese padre (`shiftPid`) — que es exactamente el nodo de fila que se
quería.

Es tu frase de siempre, y aquí funciona entera porque habla de **arriba**, no de abajo.

---

## 3. El filtro, partido en cuatro

Leyendo `reqOfCnf` literal:

| paso de `d` | requisitos | el filtro |
|---|---|---|
| `varStep v` (par, bloque literal) | **ninguno** | gratis |
| `negStep v` (impar, bloque literal) | **uno**, en `varStep v` — el paso justo de abajo | **gratis** (§3.2) |
| paso frontera `litBlock` | **ninguno** | gratis |
| paso de cláusula | **tres**, los tres literales | el residuo |
| de `fusionTop` para arriba | **ninguno** | gratis |

### 3.1 Sin requisitos, el filtro es la revisión

`tablesSound_filterAllAgg_var`. No es un caso de borde: **`n + 2` de los `2n + m + 2` pasos**.

### 3.2 El paso impar: el filtro no elige, comprueba

Y esta es la observación que más me gustó de la sesión. **La cima de un estado lleva un solo id de
mapa: el de su propia clave.** `addNode` crea la fila de arriba con `newRowIds`, todos con el id del
destino; `doJoin` solo funde estados de la **misma** clave; filtros y revisión solo podan.

Y un paso impar pide exactamente un requisito, en el paso justo de abajo — que es **esa cima**. Así
que el filtro tiene dos salidas y nada más:

* `filterRequire_top_eq` — si el requisito **es** la clave, el filtro **no toca nada**;
* `not_isValid_filterRequire_top` — y si no lo es, la cima se queda vacía y el envío se descarta.

`tablesSound_filterAllAgg_top` junta las dos. En términos del algoritmo: *desde «v vale j» solo se
puede ir a «¬v vale 1−j»*. El filtro comprueba el enlace cruzado del mapa, no elige.

### 3.3 La cláusula, y tus dos frases

Un paso de cláusula fija los **tres** literales, no solo los verdaderos. Aquí sí elige. Y tus dos
frases sobre lo que pasa entonces resultan ser cosas muy distintas:

* **«el filtro limpia los nodos que no son compatibles con los requisitos»** — `reqs_in_owners` y
  su forma fuerte `owners_pinned_after_filter`: tras el filtro, la tabla de todo superviviente lleva
  **solo** el requisito en cada paso pedido. **Sale entera.**
* **«tras el review las tablas dejan solo caminos de los seleccionados»** — se parte en dos:
  * ⊇ **demostrado**: ningún camino compatible se pierde (`ChainSound_filterAllAgg`). Tenías razón,
    el filtro no borra nada que haga falta;
  * ⊆ **abierto**: lo que sobrevive **es** un camino.

Y el número de requisitos no añade dificultad: `SeqPin.pinOneByOne` reduce un filtro de varios a
pinchar de uno en uno, así que los tres de la cláusula son tres copias del caso de **un** pin.

---

## 4. Los dos recortes del residuo

Aquí es donde el frente se estrechó de verdad, y las dos veces **por dentro del enunciado**, no
moviéndolo de sitio.

### 4.1 Primer recorte: el nodo sin elección

```lean
realizes_pin_of_singleId
```

La cadena que `SoundAt` entrega por `x` elige, en el paso del pin, **un owner de `x`** — eso es la
posesión por pares de `ChainSound`. Si todos los owners de `x` allí llevan ya el pin, la cadena lo
lleva, y sobrevive **sin reencaminar nada**. Es el mecanismo del paso impar, aplicado por nodo.

Medido (`row-degree pinchoice`, sobre los pines que el lector se plantea):

| corpus | pares (pin, superviviente) | cerrado | residuo |
|---|---|---|---|
| `dos_de_tres.cnf` | 63 | 57 (**90,4 %**) | 6 |
| 8 fórmulas aleatorias | 1.586 | 1.034 (**65,1 %**) | 552 |

Y no es estático: `SingleIdAt` + `singleIdAt_of_pruned` demuestran que **un paso pinchado se queda
pinchado**, así que la zona de residuo **encoge con cada pin**. Solo el frente de la lectura cuesta.

### 4.2 Segundo recorte: de un par de nodos a una elección binaria

Tu frase *«si el nodo sigue presente es porque tiene un camino de compatibles»* resultó colgar de
mucho menos de lo que yo pedía:

* `supportedS_pin_of_pinStepSound` — para que un superviviente tenga cadena basta la sanidad de sus
  entradas **en el paso del pin**, no la de todas;
* `PinCompatChain` / `supportedS_pin_of_compatChain` — y ni siquiera eso: el filtro solo comprueba
  el **id de mapa** del pick (`ChainSound_filterAllAgg` pide `(sel r.step).id = r`). En un paso
  literal el mapa tiene **dos** nodos, así que es una condición **binaria**; fijar el `PathNodeId`
  era mucho más fuerte;
* `pinCompatChain_of_singleId` — y donde el paso ya no tiene elección, sale **solo**. **Es la
  primera vez en la sesión que `SupportedS` atraviesa un pin sin ninguna hipótesis abierta.**

---

## 5. Medidas nuevas

| sonda | qué mide | resultado |
|---|---|---|
| `owntable` | ¿pierde un nodo su tabla al pincharse a sí mismo? | **2.261 nodos, 205.091 entradas, 0 perdidas** |
| `pinchoice` | ¿qué fracción de pines no tiene elección? | 65,1 % / 90,4 % |
| `roots` | ¿es única la raíz? | **no** — dos en el 20–36 % de los estados |
| `tsread` | `TablesSound` por la trayectoria del lector | 150.124 entradas, 0 fantasmas |

La de `owntable` es la más limpia de las dos sesiones y respalda tu frase al pie: todo lo que está
en la tabla de un nodo es compatible con él, y pincharlo no se lo quita.

---

## 6. Qué queda abierto, en una frase

> Para un nodo que sobrevive al pin **y que sigue admitiendo los dos valores** de la variable que se
> fija, una cadena de antes del filtro que pase por él **y elija ese valor**.

Un nodo. Una elección binaria. En un paso. Y solo en la zona que la lectura todavía no ha fijado.

Comparado con dónde empezó el día —`SupportedS`, una cadena por **cada nodo** de **cada estado**—,
es otro problema. Lo que no ha cambiado es que sigue siendo el mismo agujero: `RunSteps.FilterSoundAt`
visto de cerca.

### 6.1 Sobre el nodo de fusión inicial

La §6 del v175 sigue en pie sin cambios, con un matiz nuevo a favor: ahora que el residuo es una
elección **binaria en un paso**, una raíz única no ayuda directamente —el residuo no menciona la
raíz—, pero sí haría que `RootChained` fuera una **igualdad** y no una inclusión, y esa es la
dirección que hoy no tengo por ningún lado. La recomendación sigue siendo: argumento en papel
primero, refactor después.

### 6.2 Una corrección que hay que anotar

A media sesión medí un descenso por pares **sin revisar** y concluí que la prueba «tiene que ser un
argumento de búsqueda». Era falso y tú lo cortaste: tu lector pincha y **revisa todo el grafo** antes
de volver a elegir, así que las ramas que yo contaba como fallos ya no existen cuando el algoritmo
elige. Con la revisión dentro del bucle, el descenso ávido llega en 1.016 de 1.016 pares sobre la
fórmula del contraejemplo. La sonda y el docstring quedaron corregidos (`18fe704`).

---

*Claude Opus 5, con Ricardo M. Biot.*
