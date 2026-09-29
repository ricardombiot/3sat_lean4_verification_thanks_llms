# Verificación para el Autor v212: los requisitos detrás del hueco, el join de un solo lado y una corrección

Ricardo, este informe sigue al v211 en la misma sesión (29-sept-2026, rama `reader-stuck`). El v211 dejaba el
veredicto bajo B1 + `ArrHole` + `AbsHole`, y proponía atacar el "acuerdo entre ramas". Aquí cuento cuatro cosas:
* de qué está hecho el hueco de `ArrHole`: casi siempre, de los **requisitos del destino**;
* qué hace B1 en los estados del lector: allí **el join es de un solo lado**;
* un resultado nuevo en Lean, **`pinOneSide2`**: fijada la historia de dos generaciones de la cima, toda estructura
  de la unión usa aristas de un solo lado, sin hipótesis más allá de los huecos;
* **una corrección**: te dije que la hipótesis nueva del join, `PinKeeps2`, era más débil que B1. Es equivalente.

Al final (§9) hay una sección con las ideas siguientes planteadas con el método de demostraciones de Solow, como
pediste.

**La conclusión, por adelantado.**
* **Demostrado en Lean** (sin `sorry`, solo los axiomas estándar):
  * **`pinOneSide2`** (`PinSide.lean`), desde `ArrHole` y `AbsHole`;
  * `StarJoinDown` ⇐ `PinKeeps2` + `pinOneSide2` + B3 (`PinJoin.lean`), sin B1 ni `StarPure`.
* **El veredicto** (`readerVerdict_iff_of_pin`) depende de **`PinKeeps2` + `ArrHole` + `AbsHole`**. `PinKeeps2` es
  equivalente a `StarJoinDown`, y por tanto a B1 (§7). **El núcleo tipo Helly sigue abierto; ha cambiado de forma, no
  de tamaño.**
* **Medido:** `ArrHole` se explica por los requisitos del destino en el 99,4 % de las parejas; en los núcleos del
  lector el join es de un solo lado (1 122/1 122); `PinKeeps2` 2 527/0.

---

## 1. Qué rellena el hueco, y qué no (`b5f9ccf`)

En el v211 quedaban 79 parejas en las que la otra entrada del nivel tapaba algún paso del hueco de `ArrHole`. Un caso
concreto (`v5_c20_i1`) enseña el mecanismo:
* la arista $y$–$w$ se sostenía en el remitente por **un solo camino** de testigos, uno por paso, en muchos pasos (18
  de 35 en el ejemplo);
* la llegada mata ese camino entero, y la regla de parejas salta en todos esos pasos a la vez;
* el relleno es raro (1 de 18 pasos) y **mixto**: un superviviente vecino de $y$ por una entrada del nivel y de $w$ por
  la otra, que no es testigo común en ninguna de las dos por separado.

Tampoco depende de haber bajado demasiado de nivel: con las aristas del nivel siguiente los casos tapados son casi
los mismos (77 frente a 79).

## 2. Los requisitos del destino (`44855ff`, `ec8a178`)

Sobre 7 262 parejas quitadas de 5 instancias:
* **Los testigos que la llegada mata son incompatibles con la cláusula del destino** (99,4 %). A cada uno le falta, en
  algún paso requerido, un vecino con el valor exigido. El filtro solo los mata directamente en ~20 %; el resto muere
  por la regla de nodo, al quedarse sin vecinos en ese paso.
* **ReqHole** (7 129/7 262): hay un paso en el que todo vecino común de $y$ y $w$ en el nivel que vive en el
  remitente, **aristas mixtas incluidas**, es incompatible con los requisitos. Esto explica por qué la otra entrada
  no rellena: sus candidatos chocan con los mismos requisitos. Y ReqHole ⟹ `ArrHole` parece demostrable: los nodos
  incompatibles mueren en la purga, y lo que no vive en el remitente no llega.
* **El 0,6 % restante** (133 parejas) no lo explican ni las aristas incompatibles con los requisitos (0/121) ni las
  ventanas prohibidas (0/121). Son **cascadas largas** de la revisión: en un caso la arista cae en el evento 829 de 840.
* **El hueco es de camino, no de valor**: nunca hay un paso en el que $y$ y $w$ tengan vecinos de valores opuestos en
  todo el nivel (0/7 262).

*Una nota de método:* en la primera versión de esta sonda los requisitos incluían el paso del propio destino, que el
remitente no tiene. Eso hacía "incompatible" a cualquier nodo de la fila nueva. Lo detecté porque una columna salía
en 0 y lo corregí; las cifras de arriba son las buenas.

## 3. B1 con la lente de los requisitos (`probe_starcut.jl`, `1114348`)

Qué hace de verdad la restricción de una estructura $V$ a la estrella de una cima $t$ (5 instancias):
* las aristas **de fuera del lado** dentro de la estrella son rarísimas (30 en total), siempre se cortan, y en los
  núcleos fijados **no hay ninguna**;
* lo que se corta son **aristas del lado** (4 014 en los núcleos), y nunca se pierde un nodo;
* en los núcleos, los testigos que quedan fuera de la estrella son **siempre incompatibles con la historia de $t$**
  (4 183/4 183): ningún padre de $t$ los posee. En estructuras al azar hay de los dos tipos.

## 4. Los núcleos del lector son de un solo lado (`probe_kernelstar.jl`, `1cb3e46`)

En los núcleos fijados en el color del paso de los remitentes (1 122/1 122 cimas):
* la estrella de $t$ en $V$ es **exactamente** lo que poseen los padres de $t$ en su llegada;
* **todas** las aristas de la estrella son aristas del remitente $kv_A$ (1,8 M aristas, 0 excepciones).

La razón es sencilla. En bin las cimas de $kv_A$ tienen id $kv_A.1$ y las de $kv_B$ id $kv_B.1$, así que fijar ese
color **deja un solo lado**. En los estados que visita el lector, el join ya ha desaparecido.

## 5. Por qué eso no quita B1 de la cadena (`3230439`, `860cb42`)

* **Las estructuras "de grupo"** (cimas de un solo lado) son siempre de un solo lado: 1 789 estructuras, 1,87 M
  aristas, 0 del otro lado; B1 se cumple en todas.
* **Pero la inducción las necesita todas.** `chainInv_up` solo pide `StarInv` del remitente en estructuras de grupo.
  Sin embargo `starInv_up` baja al remitente estructuras **arbitrarias** (en una llegada toda estructura es de grupo),
  y `joinStep_ok` usa `StarJoinDown` también para `NodeIn` y `SInv`.
* **Restringir a lo que visita el lector no basta.** Los núcleos fijados solo en el paso de los remitentes **mezclan
  los dos valores** en algún nivel inferior en el 87 % de los casos (44 % ya en el siguiente). Cada bajada del paso UP
  pierde un nivel de fijación. Cuando usan un solo valor, sus aristas caben en esa entrada (0 fallos): una rama
  implica un lado.

## 6. Fijar la historia de la cima (`PinSide.lean`, `PinJoin.lean`, `7cb7217`)

Partí cada estructura por el valor del paso de los remitentes. Fijar el color de los padres de $t$ conserva la
estrella y $z$–$t$ (2 527/0), pero la prueba de "un solo lado" se atasca: las cimas de $kv_A$ fijadas pueden venir de
**dos llegadas**. Fijando también el color del **abuelo**, TopsApart deja todas esas cimas en **una sola llegada** $Y$,
y entonces el argumento de `StarHole` funciona.

**`pinOneSide2`** (demostrado): una estructura cerrada de la unión, fijada en el color del padre y en el del abuelo de
$t$, usa solo aristas del lado de $t$:
* todos sus nodos poseen una cima de $kv_A$, que no vive en la otra llegada, así que están vivos en el lado;
* esas cimas poseen un nodo del paso anterior del color del abuelo, que es su padre (TopsApart del remitente), así
  que son cimas de $Y$, y los nodos viejos de la estructura viven en $Y$;
* una pareja de la otra llegada que no es del lado: si $kv_A$ la tenía, `ArrHole` en el lado; si no, `ArrHole` o
  `AbsHole` en $Y$. El hueco choca con los testigos de la estructura.

Con la hipótesis **`PinKeeps2`** (fijar padre y abuelo de $t$ deja dentro una estructura cerrada con $z$, $t$ y
$z$–$t$; medido 2 527/0, 1 942 con estructuras que mezclan ramas), **`starJoinDown_of_pin`** da `StarJoinDown` sin B1
ni `StarPure`, y **`readerVerdict_iff_of_pin`** da el veredicto bajo `PinKeeps2` + `ArrHole` + `AbsHole`.

## 7. Una corrección: `PinKeeps2` es equivalente a B1

Al cerrar §6 te dije que `PinKeeps2` era más débil que B1. **No lo es**: es equivalente, dado lo demostrado.
* `PinKeeps2` ⟹ `StarJoinDown` (demostrado, §6) ⟹ `UnionTopClique` (demostrado en el v210) ⟹ B1. El último paso es
  razonado: una camarilla por $z$ y $t$ cabe en la estrella de $t$.
* B1 + B2 ⟹ `StarJoinDown` (B2 sale de los huecos) ⟹ `PinKeeps2`, con `StarInv` del lado: se toma la estructura del
  lado, se restringe a la estrella de $t$, y la estrella ya concuerda con los colores del padre y del abuelo.
  Razonado, no formalizado.

Así que cambiar B1 por `PinKeeps2` es una **reformulación**. Lo nuevo de verdad es `pinOneSide2`: la parte "de un
lado" del join está ahora demostrada en su forma más fuerte. Lo que queda es la **existencia** de la estructura
fijada con $z$–$t$ dentro de una estructura que mezcla ramas. Todas las variantes (un pin, dos, la historia entera de
$t$) forman una escalera cuyo último peldaño es `UnionTopClique`, y son equivalentes.

## 8. Dónde estamos

| hipótesis | qué dice | datos | qué se sabe |
|---|---|---|---|
| **PinKeeps2** (≡ `StarJoinDown` ≡ B1) | fijar padre y abuelo de la cima conserva $z$–$t$ en una estructura cerrada de la unión | 2 527 / 0 | es el núcleo Helly; la parte "de un lado" (`pinOneSide2`) está demostrada |
| **ArrHole** | una llegada que quita una arista deja un hueco, con las aristas de las dos entradas del nivel | 23 571 / 0 | 99,4 % explicado por los requisitos del destino (ReqHole); el resto, por cascadas de la revisión |
| **AbsHole** | lo mismo para una pareja ausente en el remitente y presente en la otra entrada del nivel siguiente | 3 908 / 0 | medido, sin mecanismo aún |

## 9. Las ideas siguientes, con el método de demostraciones

Planteo `PinKeeps2` como pide el método de Solow: enunciado como $A \Rightarrow B$, técnica según la forma de $B$ y
cadenas progresiva y regresiva. Cito capítulo y página de la edición en castellano (Limusa, 1993).

### 9.1 El enunciado

* **$A$**: $u$ es el join de las llegadas de $kv_A$ y $kv_B$ al destino $d$; $V$, $R$ es una estructura cerrada de
  $u$; $t$ es una cima de $V$; $z \in V$ y $R\,z\,t$. Sean $c$ el color de los padres de $t$ y $c'$ el de su abuelo.
* **$B$**: **existe** una estructura cerrada $W$, $R'$ de $u$ con $W \subseteq V$, $z, t \in W$, $R'\,z\,t$, y $W$
  concuerda con $c$ y con $c'$ en sus pasos.
* Cuantificadores visibles: $\forall u, V, R, t, z$ (en $A$) y $\exists W, R'$ (en $B$).

### 9.2 La técnica por la forma de $B$: construcción

$B$ empieza por "existe", así que la técnica es **construcción** (Solow cap. 4, págs. 47-52): producir el objeto y
comprobar que tiene la propiedad **y** que "sucede lo que hay que probar".

**Pregunta de abstracción** (cap. 2, págs. 23-36): *¿cómo se demuestra que un grafo contiene una subestructura
cerrada con una pareja dada?* Respuesta, ya demostrada: **basta exhibir una**. La revisión conserva toda estructura
cerrada (`secStruct_review`), así que la revisión fijada de $V$ contiene cualquier candidato cerrado y fijado.

Candidatos, y dónde falla cada uno:
1. **La estrella de $t$ en $V$.** Concuerda con $c$ y $c'$, pero su cierre es B1: círculo.
2. **Una camarilla por $z$ y $t$.** Cerrada y fijada, pero su existencia es `UnionTopClique`: círculo.
3. **La parte de $V$ compatible de primer orden** con $c$ y $c'$. Contiene la estrella, pero no es cerrada: parejas
   cuyos testigos en $V$ son del otro color.
4. **Candidato nuevo propuesto:** la estrella de $t$ más, para cada pareja de la estrella, sus testigos *del lado*
   tomados de la llegada $Y$ de los padres, donde `StarInv` de $Y$ ya está demostrado. Hay que comprobar que ese
   conjunto queda dentro de $V$; ahí está el riesgo.

### 9.3 Si la construcción se atasca: contradicción sobre el primer corte

$B$ es existencial, pero su negación es informativa, y eso sugiere **contradicción** (cap. 8, págs. 77-84):
* suponer $A$ y que la revisión fijada de $V$ **corta** $z$–$t$;
* la revisión es una sucesión finita de cortes, así que hay un **primer corte que toca la estrella de $t$**;
* ese corte quita una pareja de la estrella por falta de testigo en algún paso, y en ese momento todo lo anterior
  seguía en pie.

Tomar "el primer elemento" de una sucesión finita es el **principio del buen orden**. *Esta técnica no está en el
libro de Solow*: la uso avisando. La idea es repetir, para la estrella de $t$, el análisis que funcionó con `ArrHole`
(§1-2): identificar qué mata a los testigos en el primer corte y ver si choca con los requisitos del destino o con la
fijación del abuelo.

### 9.4 Por niveles: inducción reforzada

La afirmación es para todos los joins de la línea, lo que sugiere **inducción** en el nivel (cap. 6, págs. 63-70).
$P(n)$: `PinKeeps2` vale en todos los joins del nivel $n$. Lo disponible en el paso inductivo son los invariantes del
nivel anterior (`StarInv`, `ChainInv`) y los huecos.

El obstáculo ya medido (§5): al bajar, una estructura fijada pierde un nivel de fijación y en el 87 % acaba mezclando
ramas. Eso pide **reforzar la hipótesis**. En vez de "fijar padre y abuelo", usar $P_k$: "fijar $k$ generaciones de
la historia de $t$ conserva $z$–$t$", para todo $k$. Así la hipótesis de inducción tendría fijaciones de sobra al
bajar. Solow advierte que la dificultad de la inducción está en elegir bien $P(n)$ (cap. 6), y aquí es justo eso.

### 9.5 Comprobación antes de gastar esfuerzo

El método pide, antes de seguir empujando, probar casos pequeños o buscar un contraejemplo (cap. 12, págs. 105-111).
Las medidas cubren estructuras al azar y núcleos del lector. **No cubren estructuras cerradas construidas a propósito
para romper `PinKeeps2`**, que es lo que haría una búsqueda de contraejemplo. Por lo acordado, no la lanzo sin que me
lo digas. Si la autorizas, sería la forma más barata de saber si el enunciado es cierto antes de invertir en §9.2-9.4.

**Mi recomendación:** empezar por §9.3, el primer corte, sobre 3-4 instancias pequeñas. Es lo que mejor funcionó con
`ArrHole`. Tanto si aparece una razón uniforme como si no, dirá si merece la pena el candidato 4 de §9.2 o el refuerzo
de §9.4.

---

**Ficheros nuevos (Lean, `lean/improves_bingo/AbsSatBingo/Model/`):** `PinSide`, `PinJoin`.

**Julia (`julia/improves_bingo/test_3sat/`), sondas nuevas o ampliadas:** `probe_arrhole` (relleno, camino muerto,
requisitos), `probe_starcut`, `probe_kernelstar`, `probe_groupside`,
`probe_branch`, `probe_pinstar`.

**Commits:** de `b5f9ccf` a `7cb7217` en la rama `reader-stuck`.
