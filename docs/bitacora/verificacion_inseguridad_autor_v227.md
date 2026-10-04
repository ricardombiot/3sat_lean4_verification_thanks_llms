# Verificación para el Autor v227: cadenas de cualquier longitud

4 de octubre de 2026, rama `reader-stuck`. Continúa el v226. En una frase: **para toda cadena de cualquier longitud con
las variables numeradas en el orden de la cadena y la variable de dentro de cada bloque como literal de en medio, la
máquina `:on` es exacta y el lector por separadores no se atasca, en cualquier orden de los separadores. Está demostrado
en Lean, sin hipótesis.**

> **Estado**: todo compila (`lake build`, 180 trabajos), sin `sorry`, y los teoremas solo dependen de `propext`,
> `Classical.choice` y `Quot.sound`. La sonda de la máquina en `chain8_order` estaba en curso al escribir esto, sin
> fallos en lo medido (§7).

## 0. Resumen

| | v226 | v227 |
|---|---|---|
| longitud | 6 y 7 bloques (clases `Chain6BC`, `Chain7BC`) | **cualquiera** (`ChainOrdN`) |
| orden de las cláusulas | bisección, fijo | el de la cadena |
| numeración | cualquiera | la variable de dentro entre sus dos separadores (`NumLocal`) |
| literales | dos cláusulas con orden fijo | la de dentro, literal de en medio (`LitLocal`) |
| máquina exacta | `machineExact_of_chain6BC`, `…7BC` | **`machineExact_of_chainOrd`** |
| lector sin atasco | en orden de bisección | **en cualquier orden** (`reader_sep_of_chainOrd`) |
| instancia | `chain6_bisect_lit`, `chain7_bisect_lit` | `chain12_order` (doce bloques, `decide`) |

## 1. De dónde partía

El v226 dejó un límite: un lado de la cadena se cerraba con un testigo por lado y una cara por bloque, y las caras solo
coinciden en lo que lee la ventana del testigo (dos separadores). Por eso los lados no pasaban de tres o cuatro bloques,
y el lector en bisección llegaba a siete. Para cualquier longitud propuse fijar el nodo del testigo y seguir dentro del
problema fijado.

## 2. La vía del enlace, formulada y descartada (`ForbidOnLink.lean`, `probe_link.jl`)

* **El enlace de un nodo `n`**: lo que forma triángulo con `n` (`LinkR`, `LinkTf`), sobre las ramas que pasan por `n`
  (`PinAt`). **`LinkClosedAt`**: el enlace de una estructura cerrada es una estructura cerrada.
* **`phantomFree_of_link`** (demostrado): con esa restricción, basta el problema fijado en cada nodo del paso.
* **`phStruct_link`** (demostrado): el enlace hereda siete de sus nueve campos; faltan dos de cuatro nodos (`LinkTrio`,
  `LinkB3`: todo tetraedro con `n` es de una rama).
* **Medido**: en las cadenas hay tetraedros con un nodo de separador que no son de ninguna rama (unos 3 800 de 18 millones
  en `chain4_cross`, 25 000 de 86 millones en `chain5_cross`), aunque la máquina sea exacta en triángulos. En `clause_mix`,
  ninguno.

**Conclusión**: la vía general tiene que quedarse en triángulos.

## 3. Contar lecturas, no variables (`ForbidOnChainReads.lean`)

El error de mi planteamiento anterior: los lemas de lado pedían cardinales a cada región (dos variables), pero una cara solo
tiene que coincidir con `a0` en lo que **leen** las ventanas del triángulo. `Agr` solo mira eso (`agr_reads`), así que las
elecciones de cara se aplican a «región ∩ leídas», y un tramo largo que no se lee no cuesta nada.

* **`side_two`**: el testigo de un separador sin leer `t_c`; dos regiones unidas en `t_c`.
* **`side_three`**: la ventana de la cláusula de un bloque; tres regiones.

## 4. El descenso de un lado de cualquier longitud (`ForbidOnChainAny.lean`, `probe_split.jl`)

* **`frN`**: el primer separador leído, sin tope (recursión con combustible).
* **`Bad3`**: una región es mala si tiene tres variables distintas leídas, una en cada ventana (es como falla `pick3`).
* **`SideSplit`**: con el primer separador leído en `r ≥ 2`, un corte `c` deja las dos regiones buenas. **Es estático**:
  lo que lee un triángulo depende solo de los pasos de sus nodos, así que es una propiedad de la fórmula.
* **`phantomFree_inner_any`**: un lado de cualquier longitud bajo `SideSplit`, con el testigo del paso de variable de
  `t_c`, que siempre existe.

`probe_split.jl` lo comprueba sin correr la máquina, en segundos: vale en **todos** los lados de todas las cadenas de hasta
seis bloques y de las numeradas en orden de 8, 10 y 12; con numeración cruzada al azar falla en algunos lados (37 de 45
con 10 bloques).

## 5. Lecturas locales: el corte es `c = 1` (`ForbidOnChainLocal.lean`)

* **`LocalReads`**: una ventana que lee la variable de dentro de un bloque de en medio lee también uno de sus
  separadores.
* **`localReads_of`**: la dan dos condiciones de la fórmula. **`NumLocal`**: la variable de dentro está numerada entre sus
  dos separadores (una ventana de paso de variable que lee `z` lee `z - 1` o `z + 1`). **`LitLocal`**: es el literal de en
  medio de sus cláusulas (una ventana de cláusula que lee el de en medio lee el primero o el último). El orden de las
  cláusulas no importa.
* **`sideSplit_of_local`**: con lecturas locales, el corte de cualquier lado es `c = 1`. Los bloques de dentro del tramo
  no se leen (leerlos sería leer un separador sin leer), la región de `v` es un bloque, y la otra solo tiene leídas dos
  variables, las del último bloque del tramo y `t_r`.

## 6. Dos lados, cualquier orden, las líneas (`ForbidOnChainBisectN.lean`, `ForbidOnChainOrd.lean`)

* **`phantomFree_bisectN`**: fijar un separador con los dos lados abiertos, de cualquier longitud. Con lecturas locales la
  región de `v` en cada lado es un solo bloque (una variable), y la sirven también las caras que conservan el nodo del
  otro lado: el rango es la suma de los dos primeros separadores leídos, sin pesos ni límites. Lo que pide es
  **`LocalReadsAway`**: lecturas locales salvo en los dos bloques pegados a `v`.
* **`sepPinFree_of_local`**: T2 en **cualquier orden** de los separadores, porque cada uno se puede fijar con los
  extremos de la cadena como extremos libres. **`reader_sep_local`**: el lector no se atasca, dadas las líneas.
* **Las líneas** (`phantomAt_ordLine`): en el prefijo de la cláusula `j`, se trunca en el separador `j + 1`
  (`chainN_truncS`); si `v` es un separador, `phantomFree_bisectN`; si es la de dentro, se intercambia con `s_{j+1}`
  (`chainN_swap`); en la última cláusula, la de dentro se **aísla** como un separador nuevo con un bloque vacío detrás
  (`chainN_isolate`). Intercambiar y aislar rompen las lecturas locales solo en los dos bloques pegados a `v`, que son las
  regiones de `v`: por eso basta `LocalReadsAway` (`away_swap`, `away_isolate`).
* **`ChainOrdN`**, **`phantomAt_of_chainOrd`**, **`machineExact_of_chainOrd`**, **`spineVerdictOn_iff_of_chainOrd`**,
  **`reader_sep_of_chainOrd`**. La instancia `chain12O` (`long/chain12_order.cnf`) está en la clase, comprobado con
  `decide` (`machineExact_chain12O`, `reader_sep_chain12O`).

## 7. Medidas

| sonda | qué mide | resultado |
|---|---|---|
| `probe_link.jl` | tetraedros con un nodo de separador que no son de ninguna rama (`LinkB3`) | cadenas: los hay (0,02–0,03 %); `clause_mix`: ninguno |
| `probe_split.jl` | el corte estático `SideSplit`, por lados | cadenas numeradas en orden: todos los lados (hasta 12 bloques); numeración cruzada: casi todos |
| `probe_exact3.jl` en `chain8_order` | la máquina, condición fuerte | en curso; sin fallos en lo medido (92 estados de llegada y sus filtros) |

`chain6_order` ya estaba medida exacta (v223).

## 8. Trucos técnicos de esta vuelta

1. **`Agr` solo mira lo que se lee**: las cotas van sobre variables leídas, no sobre cardinales.
2. **Lo que lee un triángulo es estático**: la hipótesis del corte es una propiedad de la fórmula y se comprueba sin la
   máquina.
3. **`Bad3` en vez de cardinales**: una región solo falla con tres variables, cada una leída en una ventana distinta.
4. **El testigo del paso de variable siempre existe**: no hacen falta condiciones de ventanas sobre las cláusulas.
5. **El primer separador leído sin tope**, con combustible.
6. **Con lecturas locales, el corte es `c = 1`**: no hay que buscarlo; lo que se lee se concentra en los dos extremos.
7. **La región de `v` es un bloque**: basta la cara que conserva el nodo del otro lado, y desaparecen los pesos.
8. **T2 en cualquier orden**: los extremos de la cadena sirven siempre como extremos libres.
9. **Romper las lecturas locales solo junto a `v`**: intercambiar y aislar convierten la de dentro en separador, y solo
   tocan las regiones de `v`.

## 9. Lo que queda abierto

1. **Numeración cruzada.** `ChainOrdN` pide la variable de dentro entre sus separadores y en medio de su cláusula. Con
   numeración cruzada no hay lecturas locales; `probe_split.jl` dice que el corte existe casi siempre, pero no siempre.
   Las clases `Chain6BC` y `Chain7BC` del v226 no están en `ChainOrdN` (su unión tiene la de dentro al final): para ellas
   valen sus propias pruebas.
2. **Un preproceso.** Renumerar las variables en el orden de la cadena y poner la de dentro en medio no cambia las
   soluciones, y lleva cualquier cadena a `ChainOrdN`. Haría falta calcular la cadena (los separadores y su orden) y
   añadirlo a la máquina en Julia y en Lean.
3. **Más allá de las cadenas.** Árboles de bloques (un bloque con tres separadores) o anchura mayor: las mismas piezas
   (lecturas locales, regiones por lecturas) son el punto de partida.
4. **`chain8_order` en la máquina**: terminar la sonda.

## 10. Plan

1. Terminar la sonda de `chain8_order` y anotarla aquí.
2. El preproceso de renumeración, con una sonda que compare la máquina antes y después en las cadenas cruzadas.
3. Las lecturas locales para numeración cruzada: medir con `probe_split.jl` qué patrones fallan y si `side_three`
   (tres regiones) los cubre.

## Ficheros

| fichero (`lean/improves_bingo/AbsSatBingo/Model/`) | qué es | commit |
|---|---|---|
| `ForbidOnLink.lean` | el enlace; `phantomFree_of_link`, `phStruct_link` | `f909149` |
| `ForbidOnChainReads.lean` | `side_two`, `side_three`, `agr_reads` | `ed7ddb3` |
| `ForbidOnChainAny.lean` | `frN`, `Bad3`, `SideSplit`, `phantomFree_inner_any` | `e477f13` |
| `ForbidOnChainLocal.lean` | `LocalReads`, `NumLocal`, `LitLocal`, `sideSplit_of_local` | `0653dad` |
| `ForbidOnChainBisectN.lean` | `phantomFree_bisectN`, `sepPinFree_of_local`, `reader_sep_local` | `443d990`, `5923d88` |
| `ForbidOnChainOrd.lean` | `ChainOrdN`, `phantomAt_of_chainOrd`, `machineExact_of_chainOrd`, `reader_sep_of_chainOrd` | `5923d88` |
| `ForbidOnChainOrdI.lean` | `chain12O` en la clase | `5923d88` |
| `julia/improves_bingo/test_3sat/probe_link.jl`, `probe_split.jl` | las sondas de §7 | `ccca961`, `49e53d5` |
| `lean/improves_bingo/scripts/cnf/long/` | las cadenas largas generadas | `49e53d5` |
