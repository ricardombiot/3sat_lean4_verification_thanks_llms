# Verificación para el Autor v120: el soporte de la rebanada es exactamente `PinExact`, y cómo se calcula

Ricardo, soy Claude (Opus 5). v119 redujo la validez del veredicto de *Improves* a que la rebanada de
cada fijación tenga una relación de soporte (`Supported`). Este tramo hace dos cosas: demuestra que
esa condición es **equivalente** a `PinExact` (no más fuerte), y mide ronda a ronda cómo se calcula
el soporte, lo que separa limpiamente los pasos interiores de los extremos.

Todo en la rama `spaik`, en el build de `AbsSat` (239 jobs), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. El recíproco, demostrado (`SliceExact.lean`)

**`supported_iff_pinExact`**: en los estados del lector, para una fijación válida,
`Supported g mid ↔ PinExact g mid`. Y **`supported_iff_pinExact_run`** lo enuncia a lo largo del
lector que parte de un estado final de la máquina.

La dirección nueva (`supported_of_pinExact`) toma como testigo **la tabla de owners que deja la
fijación**, restringida a la rebanada (`FinalRel`), y comprueba las condiciones de `Sup` en el estado
**antes** de fijar:

- **cobertura**: un miembro sobrevive (`PinExact`), su nodo es válido y tiene owner en cada paso;
  ese owner también sobrevive, así que está en la rebanada (`inSlice_of_survives`, v117);
- **padres e hijos**: el resultado de `filterAllAgg` es un resultado de `review`, cuyas tablas son
  coherentes con la unión de owners de padres e hijos (`review_owners_coherent_parents`/`_sons`, ya
  en `Fuel.lean`); los enlaces son owners (`Bridge.linksInOwners_review`); un padre lista a su hijo
  (`SMP`) y un hijo a su padre (`PMS`);
- **pares**: tu test se cumple en el resultado (`aggOk_reviewAgg`, v118).

Para esto `MInv` lleva ahora también `PMS` y `SN`. El nuevo `AggInvariants.inv_filterAllAgg` lo hace
en una línea: tu barrido solo reescribe listas de owners y elimina nodos, así que conserva todo
invariante que conserven las fijaciones, el review base, esas reescrituras y `removeNode`.

**Lo que significa**: la obligación abierta de v119 no es una condición suficiente más fuerte de la
cuenta. Es `PinExact` enunciado sin la cascada.

## 2. Las rondas del soporte (`helly rounds`)

La sonda repite, para cada fijación, el cálculo del mayor soporte de v119 y registra en cada ronda qué
pares caen, por qué condición y en qué pasos, y cuántos soportes le quedan a cada casilla
(nodo, paso), sin contar el paso propio ni el paso fijado.

| familia | fijaciones | rondas máx. | pares interiores caídos en la ronda 0 (todos por pares) | pares interiores caídos después | caídos por padres o hijos sin fallar pares | pares de borde caídos después de la ronda 0 | nodos perdidos | casillas con un solo soporte al final |
|---|---|---|---|---|---|---|---|---|
| Tseitin K4 par | 88 | 5 | 15.776 | **0** | **0** | 1.760 | **0** | 119.698 de 148.846 |
| `par_k3_direct_asc_fresh` | 73 | 3 | 2.956 | **0** | **0** | 251 | **0** | 101.525 de 198.305 |
| `par_k5_chain_asc_shared` | 114 | 5 | 56.304 | **0** | **0** | 2.452 | **0** | 223.654 de 483.179 |
| Tseitin prisma par | 132 | 9 | 112.912 | **0** | **0** | 7.600 | **0** | 368.190 de 634.712 |
| K4 menos una arista, 3 colores | 244 | 5 | 62.828 | **0** | **0** | 3.732 | **0** | 1.569.040 de 1.938.893 |
| aleatorias, 6–8 variables (semilla 1001) | 1.318 | 6 | 21.594 | **0** | **0** | 2.286 | **0** | 2.127.957 de 2.752.400 |
| **total** | **1.969** | | **272.370** | **0** | **0** | **18.081** | **0** | **4,5 M de 6,2 M** |

Tres regularidades, sin excepción:

1. **Los pares interiores** (los dos extremos en `1 … cs−2`) **caen solo en la ronda 0 y solo por la
   condición de pares.** Ninguno cae por padres o hijos, y ninguno cae después.
2. **Todo lo que cae desde la ronda 1 son pares con un extremo en el paso 0 o en el último**, y caen
   por padres o hijos: las zonas que tu barrido no recorre se limpian propagando por los enlaces.
3. **Ningún nodo pierde soporte**, y no por holgura: el 73 % de las casillas acaba con **un único**
   soporte.

**Consecuencia para los pasos interiores.** El soporte interior se obtiene con un único filtro
estático, **consistencia de pares dentro de la rebanada** (`SPC`): `v` es owner de `x`, los dos están
en la rebanada, y en cada paso tienen un owner común **que también está en la rebanada**. Después de
ese filtro, todo par interior vuelve a pasar las tres condiciones.

## 3. ¿Cualquier testigo sirve? No, pero siempre hay uno (`helly hered`)

Si `x`, `v` cumplen `SPC` y `z` es un owner común en la rebanada en el paso `l`, ¿cumplen `SPC` los
pares (`x`, `z`) y (`v`, `z`)?

| familia | pares interiores `SPC` | testigos | testigos que fallan | casillas sin ningún testigo bueno |
|---|---|---|---|---|
| Tseitin K4 par | 165.652 | 5.571.824 | 323.264 | **0** |
| `par_k3_direct_asc_fresh` | 387.587 | 17.110.597 | 143.416 | **0** |
| `par_k5_chain_asc_shared` | 848.664 | 47.756.672 | 2.633.912 | **0** |

La versión "todo testigo sirve" es **falsa** (3,1 M testigos malos de 70,4 M). La que se cumple es la
débil: **en cada paso hay algún testigo que es `SPC` con los dos extremos.** Es exactamente la
estabilidad que dice la sección 2, y no admite un atajo por herencia.

## 4. La cadena, tal como queda

```
estado final de pureRunW                           MInv (+ SMP, PMS, SN)        demostrado
  todo estado del lector es resultado de reviewAgg AggOk, simetría interior     demostrado (v118)
  simetría en los pasos 0 y cs−1                   BoundarySym                  medida, abierta
  la rebanada de cada fijación tiene soporte       Supported                    medida, abierta
    ⇔ la rebanada sobrevive a la cascada           PinExact                     equivalencia demostrada (v120)
    ⇒ toda fijación es válida ⇒ PickSomeAgg                                     demostrado
    ⇒ el lector acaba en un camino ⇒ modelo de φ                                demostrado (v116)
```

## 5. Lo que queda, y cómo lo partiría

`Supported` se parte en dos piezas que ahora se ven por separado:

1. **Interior: `SPC` es estable.** Para un par interior `SPC` y un paso `l`, algún testigo común en
   la rebanada es `SPC` con los dos extremos; y los pares `SPC` interiores cumplen padres e hijos
   dentro de `SPC`. Es una propiedad de las tablas del estado antes de fijar, sin cascada ni rondas.
   La sección 3 descarta la vía corta (todo testigo sirve); hace falta elegir el testigo.
2. **Borde: la limpieza de los pasos 0 y `cs−1`.** Aquí sí hay varias rondas (hasta 8 en el
   prisma), por padres e hijos. Va de la mano de `BoundarySym`: las dos cosas viven en las zonas que
   tu barrido no recorre.

Sobre la pieza 2 hay una decisión tuya pendiente desde v118: ampliar el barrido a todos los pasos. La
sonda indica que eliminaría la propagación de borde y dejaría una sola pieza, la estabilidad de `SPC`.
