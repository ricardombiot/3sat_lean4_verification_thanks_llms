# Verificación para el Autor v155: las cimas distintas separan la unión

Ricardo, soy Claude (Opus 5). He seguido tu indicación. En `send_to_destine!`, `do_up_filtering!` añade el
nodo `(destino, origen)` antes de `impact!`, así que cada lado de una unión por clave tiene su **propia
cima** `(p, pᵢ)`, aunque todos lleguen al mismo destino. En Lean esto ya estaba: es `Separates` (la cima
separa los lados) y `JoinSide.part_of_anchor`.

Sonda nueva: `helly pinsplit`, sobre las uniones de la máquina con un valor de literal fijado (la forma de
`PinJoin`, v154). Commit de la sonda en esta misma entrega.

## Lo medido

Llamo **X** a la unión fijada y revisada. Una **cima común** de una entrada x→v es la cima de un lado,
poseída por x y por v en X. Una cima **lleva** la entrada si la tabla de su lado contiene x→v.

| propiedad | paridad k3 | Tseitin K4 |
|---|---|---|
| entradas de X (por debajo de la cima) | 139.414 | 314.750 |
| **cobertura**: alguna cima común lleva la entrada | **0 fallos** | **0 fallos** |
| toda cima común lleva la entrada | 144 no | 1.120 no |
| **triángulo anclado**: si la cima tᵢ lleva x→v, en cada paso hay un z de X con x↔z, v↔z, z→tᵢ, y x→z, v→z llevadas por el mismo lado | **0 fallos / 2,45 M** | **0 fallos / 7,19 M** |

La cobertura ya está demostrada a partir de lados exactos (`JoinSide.sideCover_of_sound`). El triángulo
anclado es la condición de nodo común del soporte de la parte de cada lado (`SupportSplit.Part`), la que
hacía falta para `PartSplit`, y con ella para `PinJoin`.

## Qué falta demostrar, en tus términos

El triángulo anclado se reduce a esto. Sea x→v una entrada que el lado i lleva y que sobrevive en X. El
lado i es exacto: x→v está sobre una solución parcial del lado i. Falta que haya una **que tome el valor
fijado r** (`PartSplitReal.SurvivorsRealized`, con una fijación). Con ese camino, todas las condiciones del
soporte de la parte salen de una vez (`partSplit_of_realized`).

Es el paso de pares a tríos, ahora dentro de **un solo lado** y con un tercer objeto muy concreto: el valor
fijado r.
