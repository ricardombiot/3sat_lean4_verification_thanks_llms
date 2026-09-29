# Verificación para el Autor v207: el lector sin retroceso, reducido a una sola propiedad de la unión

Ricardo, este informe cuenta una sesión larga (29-sept-2026, rama `reader-stuck`). Empezamos preguntando cómo demostrar
que el lector no retrocede. Terminamos con el veredicto del lector demostrado en Lean bajo **una sola hipótesis**, que
vive en los joins de la máquina y está medida sin fallos. Por el camino salieron dos cosas que corrigen lo que yo mismo
había dicho, y las cuento también.

**La conclusión, por adelantado.**
* **Demostrado en Lean** (sin `sorry`, solo los axiomas estándar), en `lean/improves_bingo`:
  `readerVerdict_iff_of_secIn`. El veredicto del lector es la satisfacibilidad si en cada join se cumple
  **`SecSplitIn`**: toda estructura cerrada no vacía de la unión contiene una estructura cerrada no vacía de uno de los
  dos lados.
* **Demostrado a mano, ya no son hipótesis:**
  * la separación por el origen (`SepAt`);
  * que cada join une dos estados de **un color cada uno** en el paso del remitente;
  * la fila nueva con ventana saltada. `AvoidSat` desaparece.
* **Medido:** `SecSplitIn` y sus piezas, 0 fallos en todas las sondas (§6), con instancias UNSAT incluidas.
* **Abierto:** `SecSplitIn` misma. Reducida a `SplitIn2` + `SideEdgesAt` (§5), es un reparto entre los dos colores
  dentro de una estructura de la unión. Ahí sigue el núcleo que tu memoria de trabajo ya señalaba: un Helly sobre dos
  clases.

---

## 1. El punto de partida: el contrapositivo (Solow)

La completitud del lector es $\forall$ estado alcanzable, $\forall$ paso con elección, $\exists$ pin que deja el
estado válido. En lugar de construir el pin, tomé el contrapositivo: *si el lector se atasca, hay un estado válido
sin soluciones* (`ReaderStuck.lean`).
* **`zombie_of_sat_of_readerFalse`**: con $\varphi$ satisfacible y el lector diciendo UNSAT, el lector se para en un
  estado válido sin ninguna camarilla.
* **`pinLoss_of_sat_of_readerFalse`**: la primera pérdida. Hay un pin válido que, desde un estado con camarilla, deja
  uno sin ninguna.
* Su negación, **`PinKeeps`**, basta para el veredicto. Es más débil que `NoZombie`.

Después (`PinKeeps.lean`): `PinKeeps` equivale a **`MapExact`** ("si fijar un nodo de mapa deja el estado válido,
alguna solución pasa por él"). Y queda por debajo de `PinFree`, la hipótesis del teorema principal anterior.

## 2. Llevar la hipótesis al arranque, y luego a la máquina

* **`SeqExact.lean`**: los estados del lector son pins sucesivos del arranque (`visited_pinSeq`). La hipótesis
  «ningún estado del lector es un zombi» equivale a una sola propiedad del arranque, **`SeqExact`**: si fijar $P$ deja
  el arranque válido, alguna camarilla concuerda con $P$ (`seqExact_iff_noZombie_visited`).
* **`SecExactLine.lean`**: para llevarla por la máquina sin demostrar `ClosedState` en cada estado intermedio, la
  formulé sobre estructuras cerradas. **`SecExact`**: toda estructura cerrada no vacía que concuerda con $P$ tiene
  **una** camarilla que concuerda. Es la versión de existencia de `KernelExact`, que pide una camarilla por pareja.
  Operación por operación: el pin, el filtro, el review y la fila nueva sin ventana saltada la conservan **sin
  hipótesis**. El join la conserva bajo `SecSplit`.

## 3. El join por partes, y lo que salió gratis

La descomposición vieja de `KernelUnion` (`SplitAt` + `SepAt` + `SideEdgesAt`) tiene versiones de existencia
(`SecSplitParts.lean`): `SplitSat` y `SideSat`. Dos piezas dejaron de ser hipótesis:

* **`SepAt` demostrado** (`SepLine.lean`): la inducción de la línea lleva de qué remitentes vienen los vivos del paso
  de origen (`OriginIn`). Cada remitente se procesa una vez (las claves son únicas) y envía una vez a cada hijo
  (`sonsOfMap_nodup`). Así, en cada join el estado acumulado solo tiene orígenes anteriores y la llegada solo el suyo.
* **Un color por lado** (tu observación, `612a918`): en el mapa bin hay como mucho dos nodos de mapa por paso, y las
  claves de la línea tienen índice 0 o 1 (`advance_index`). Así que **cada join une exactamente dos estados, uno de
  cada color** en el paso del remitente (`joinProv_two`). Y color = lado (`colour_side`): lo que toca un nodo del
  color de $e$ es de $e$.

## 4. `SecIn`: la camarilla dentro de la estructura

Este fue el paso que más simplificó (`SecIn.lean`, `61e9826`):

> **`SecIn g`**: toda estructura cerrada no vacía $V$ que concuerda con $P$ **contiene** una camarilla que concuerda.

* **Desaparece `AvoidSat`** (`secIn_addNode`). La camarilla está dentro de $V$, así que su cima está en $V$. La regla
  de enlaces de $V$ pone también en $V$ el hijo de esa cima, así que la ventana está permitida. Vale con ventana
  saltada o sin ella.
* El filtro, el review, `dirty` y la semilla la conservan **sin hipótesis**.
* El join, bajo **`SecSplitIn`**. Y como `SecIn` implica `SecExact`, el lector sale igual.

Para no duplicar código, la inducción de la línea quedó genérica en el invariante (`UpProv`, `JoinProv I`,
`run_prov`). Las versiones anteriores siguen demostradas como casos de ella.

## 5. Lo que queda, dicho con precisión

`SecSplitIn` se reduce a una propiedad **de la unión sola** (`SecSplitInParts.lean`, `22ec2cd`):
* **`secStruct_of_sideEdges`**: una estructura cerrada de la unión con nodos y parejas de un lado es una estructura
  de ese lado.
* **`SideSubIn`**: dentro de toda estructura cerrada no vacía de la unión hay otra, cerrada en la unión, con todas
  sus parejas de un mismo lado. `SideSubIn` ⟹ `SecSplitIn`.
* Y por colores: **`SplitIn2`** (dentro de $V$, fijar el color de $e$ o el de $g$ deja algo) + **`SideEdgesAt`**
  (fijada en un color, las parejas son de su lado) ⟹ `SideSubIn`.

La cadena demostrada:

$$\texttt{SplitIn2} + \texttt{SideEdgesAt} \Rightarrow \texttt{SideSubIn} \Rightarrow \texttt{SecSplitIn}
\Rightarrow \texttt{SecIn en toda la línea} \Rightarrow \text{veredicto del lector} \Leftrightarrow \text{SAT}$$

**Por qué no la cierro todavía.** Al intentar construir la estructura de un color dentro de $V$, la regla de parejas
en otro paso pide que el testigo de una pareja tenga, a su vez, testigos del mismo color con cada extremo. Las
estructuras **mixtas** existen y son frecuentes (§6). Así que no basta con quedarse con "las parejas de un color": la
limpieza del review encuentra una subestructura más pequeña, y la demostración tendrá que razonar sobre ese punto
fijo.

## 6. Lo medido (Julia, microframework de sondas)

Añadí dos puntos de sonda sin coste en `src`: `:up_done` y `:join_pre`/`:join_post`. Todo con el tope de memoria de
`run_capped.sh`.

| sonda | qué mide | resultado |
|---|---|---|
| `probe_mapexact` | zombis, `EdgeClique`, `MapExact` tras el UP, tras el join, en la línea final y en el lector | 31 instancias, 9 152 estados, 304 688 pins: **0 fallos** |
| `probe_secsplit` (muestreo) | `SecSplit` en forma de pins | 35 instancias, 500 912 pruebas: **0** (sigue en curso) |
| `probe_secsplit` (`SPLIT=1`) | `SecSplit` y `SplitSat` | 36 instancias (2 UNSAT), 254 110: **0 y 0** |
| `probe_mixed` | estructuras mixtas en la unión fijada | 48 instancias (7 UNSAT), 31 220 estados: **46 % mixtos**, y en todos sobreviven los dos colores; `SplitSat2`: **0 fallos** |
| `probe_secin` | `SecIn` tras el UP y en la unión; `SecSplitIn`; `SplitIn2` | 42 instancias (4 UNSAT): 22 417 / 10 518 / 10 518 / 10 518, **0 fallos**; los dos colores sobreviven en el 42 % |

## 7. Dos correcciones que te debo

1. **Los tríos muertos existen en el mapa bin.** Había dicho que, si `EdgeClique` no fallaba, el trío muerto de la
   semilla 11 no aparecería. Era falso: `EdgeClique` mira nodos y parejas, y en un trío muerto cada pareja está en una
   solución real. `dump_colour_helly.jl` los encontró. En `clause_mix` es justo el trío que la fórmula fabrica
   ($a=b=c=1$ fuerza $x=y=z=0$ contra $x\lor y\lor z$). Salen 49 de 49 estados fuera de toda camarilla, y sobreviven a
   la limpieza. **No rompen nada**: el estado conserva otras camarillas, y `SplitSat2` y `SecIn` siguen sin fallar.
2. **`SplitSat2` no pide Helly de tríos.** Lo sugerí y medí un Helly local por triángulos dentro de cada color
   (`probe_colour_helly`). Falla en 82 estados, siempre con clases de 3 o 4 ventanas. Pero el cierre de una estructura
   es por parejas, y el reparto no falla nunca. Era una condición suficiente, no necesaria. Tu matiz de que cada color
   agrupa varios nodos de camino fue lo que lo aclaró.

**La regla de tríos** (`TRIO_RULE`, apagada por defecto, commit `6676f6d`): la implementé porque la preguntaste. Pide
que el testigo de una pareja forme un trío consistente. Es correcta (no pierde soluciones) y entra en el registro de
deshacer del UP en sitio, porque corta con `remove_edge!`. Pero **no corta ninguna arista** en 26 instancias: toda
pareja viva tiene siempre otro testigo bueno. Los tríos solo se quitarían guardándolos como tríos, que es un cambio de
representación y no una regla. Cuesta de ×10 a ×30 en tiempo.

## 8. Lo que sigue

1. Atacar **`SplitIn2`** razonando sobre el punto fijo del review dentro de $V$, no sobre "las parejas de un color".
   Los datos dicen que en los estados mixtos sobreviven **los dos** colores. Probablemente es más fácil demostrar eso
   (fijar el color de un lado que tenga cimas dentro de $V$ deja algo) que el "o".
2. **`SideEdgesAt`** sigue siendo la otra pieza. Está medida sin fallos desde hace tiempo (`Absorb`), pero sin
   demostración.
3. Lo demostrado esta sesión queda como base firme. El lector, el arranque, la línea, la separación, los colores y la
   ventana ya no dependen de nada más que del join.

Lo que has construido es sólido en todo lo que no es el join. Y del join sabemos ahora exactamente qué propiedad hace
falta, de una sola unión y con dos lados de un color cada uno.

---

**Ficheros nuevos (Lean, `lean/improves_bingo/AbsSatBingo/Model/`):** `ReaderStuck`, `PinKeeps`, `SeqExact`,
`SeqMachine`, `SeqUp`, `SecExactLine`, `SecSplitParts`, `SepLine`, `AvoidSplit`, `SecIn`, `SecSplitInParts`.
**Julia (`julia/improves_bingo/test_3sat/`):** `probe_mapexact`, `probe_secsplit`, `probe_mixed`,
`probe_colour_helly`, `dump_colour_helly`, `probe_trio`, `probe_secin`; en `src`, los puntos `:up_done`, `:join_pre`
y `:join_post`, y `TRIO_RULE`.
**Commits:** de `7b97077` a `2fc37ff` en la rama `reader-stuck`.
