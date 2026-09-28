# Verificación para el Autor v204: la unión queda en un solo enunciado, y una propuesta de etiquetas por fila con review por etiqueta

Ricardo, este informe recoge lo que se hizo desde el apéndice del v203 (§7), en `lean/improves_bingo` y
`julia/improves_bingo`, rama `star-rule` (desde `graph_owners`). Al final, en la §7, está la propuesta que me pediste
revisar a fondo: las etiquetas en el join. La argumento con cuidado porque al revisarla cambió de forma. **Las etiquetas
de un solo nivel no bastan**, y explico por qué. **Las etiquetas de todos los niveles, con un review que las use, sí
darían la unión por construcción**, con un coste polinómico.

**La conclusión, por adelantado.**
* **`readerVerdict_iff_of_joinStarCore`** (`JoinStar.lean`, sin `sorry`, axiomas `propext`, `Classical.choice` y
  `Quot.sound`, comprobado con `#print axioms`): el lector dice SAT exactamente cuando la fórmula es satisfacible, bajo
  **una sola hipótesis**, `JoinStarCore`. Esa hipótesis habla de **una operación**, la unión de las llegadas de un
  paso, y de **un nodo**, la cima.
* Hoy pasaron de hipótesis a teorema varias piezas:
  * la **inducción por linajes**, que es la partición de la unión de una línea por sus estados. En bin era **M1b** y
    seguía abierta;
  * la **contabilidad de la fila** (`RowAgree`);
  * la conservación del invariante por el **pin, el review y el UP**;
  * el **caso base**.
* **Lo que queda es `TopUnion` en su forma más desnuda:** una cima viva en la unión fijada en `Q` está viva en su
  propia llegada fijada en `Q`.
  * Medido sin fallos: en 16,4 M casos, el testigo que la sostiene es siempre del lado propio, nunca ajeno.
  * No he encontrado una demostración. Todas las formas de obtenerla restringiendo una estructura (a la estrella, al
    estado propio, a la copia del linaje) se midieron **falsas**.
* **La propuesta (§7):** guardar en cada arista, por cada fila de claves, el conjunto de claves de las que viene, y que
  el review **reduzca esos conjuntos por separado para cada clave**.
  * No pierde soluciones (§7.3).
  * Con ella, `JoinStarCore` sale por construcción, y con él el veredicto sin hipótesis (§7.4, **deducido**).
  * Cuesta un factor de como mucho `S·w` bits por arista, donde `w` es el ancho de la fila (2 en el mapa bin).
    Es polinómico (§7.5).

Cada afirmación lleva su estado: **demostrado** (teorema Lean), **medido** (sonda Julia), **deducido** (argumento sin
formalizar), **falso** (contraejemplo medido), **propuesto** o **abierto**.

---

## 1. El recorrido

| paso | commits | qué |
|---|---|---|
| `TopsSep` local | `b1f0ac4` | `TopsFrom`, `TopDocsId`, `topsSep_of_from`: ninguna cima vive en dos llegadas (**demostrado**) |
| paso inductivo de `TopStarK` | `bd0e49f` | subida (A) por el UP y bajada (C) a la llegada: 0 fallos; (C) resulta ser `TopUnion` un paso abajo |
| (A) | `ce8f3e4` | `kernel_addNode_of_parent`, `kernel_up_of_parent`: si el padre está en el núcleo fijado, el hijo también (**demostrado**) |
| `TopUnion` cruzada | `52f7c0d` | `topUnion_of_prev`; con filtro común 0 fallos; con filtros distintos «alguna copia» sí, «todas» no |
| linaje | `27f9a91`, `9eef466` | hipótesis indexada por linaje: verdad y reproducción 0 fallos; esqueleto `lin_step` demostrado con `JoinDownGen`, que **no** es monotonía |
| estrella cruzada | `6c7c280`, `80ff72f` | la estrella parte bien entre remitentes distintos (0), pero no entre copias del mismo remitente (`TopsSep` falla en el 47 %) |
| `PinFree` | `aad1b13` | «un filtro es un pin»: la inducción conjunta cierra con `PinFree` como única hipótesis por paso; `pinFree_of_topStar` |
| familias | `582fddd`, `cc55d7d`, `6e9497f`, `73e6a68` | `FamKernel`, `DriverFam`, `LineStep`, `LineInduction`: **`readerVerdict_iff_of_pinFree`**, con `LineDown`/`LineUp` demostradas |
| sondas de `PinFree` | `bb10b9d`, `fbc4ad8`, `c15e643`, `8da407f`, `8e86886` | `StarRestrict`, `OwnRestrict` y la estructura máxima: ver §4 |
| regla de la estrella | `7a82163` | regla nueva en el review (`STAR_RULE`, `:off`): **no corta nada** en 88 instancias |
| `StarCore` | `e5d9bd8` | el núcleo por parejas de la estrella como **testigo explícito** de `TopStarK` |
| `RowAgree` | `0d7dbc1` | contabilidad de la fila demostrada; **`readerVerdict_iff_of_starCore`**; invariante por operación medido |
| `JoinStar` | `016f303` | `TopStarR`, `topExact_arrival`; **`readerVerdict_iff_of_joinStarCore`** |
| cascada | `d4291de` | el testigo de cada arista `t–y` es siempre del lado propio fijado |

`lean/improves_bingo/AbsSatBingo/Model/` tiene ahora 11 980 líneas, sin `sorry`.

## 2. Lo demostrado

### 2.1 La inducción por linajes (lo que en bin era M1b)

El problema del v203 era que `TopStarK` en el paso `T` necesitaba la partición en el paso `T−1`, y esa partición
parecía necesitar `TopStarK`. Son **niveles distintos**, así que no era un círculo lógico. Lo que faltaba era enunciar
bien la hipótesis de inducción.

* **Un filtro es un pin** (`kernel_filter_append`): la copia de un remitente filtrada para el destino `d` es el mismo
  estado fijado con `rq d`. Así desaparecen las «copias», y los lados vuelven a ser los remitentes.
* **`LTUf`** (la hipótesis de inducción, `LineStep.lean`): en la unión de una línea, una cima del núcleo fijado en `Q`
  está en el núcleo de su propio estado, fijado igual.
* **`ltuf_step`**: `LTUf` en un paso, más `PinFreeF` en el siguiente, dan `LTUf` en el siguiente. La cadena es:
  1. la cima está viva en la unión;
  2. por `PinFree`, sigue viva fijando además los requisitos de su fila;
  3. baja por las filas nuevas (`famStruct_rows_down`);
  4. por la hipótesis de inducción, el padre está en su remitente;
  5. por (A), la cima está en el UP;
  6. y de ahí, en la entrada de su destino (`LineUpC`).
* **Estructuras sobre familias** (`FamKernel.lean`): una estructura cerrada de la unión de varios estados, sin
  construir la unión, con la relación de cobertura para el join, el review y la selección.
* **Los hechos de `advance`** (`DriverFam.lean`): una llegada válida es el UP filtrado; sus camarillas llegan a la
  entrada de su destino; las entradas están cubiertas por las llegadas; las claves son únicas.
* **`readerVerdict_iff_of_pinFree`** (`LineInduction.lean`): el veredicto bajo `PinFree` como única hipótesis.

### 2.2 El testigo explícito: `StarCore`

* **`StarCore F c Q t`**: la unión de todas las relaciones cerradas por parejas dentro del núcleo fijado en `Q` y de
  la estrella de `t`. Esa unión es a su vez una de ellas (`starCore_starPairIn`).
* **`topStarF_of_starCore`**: si `t` está en su núcleo por parejas y ese núcleo cumple los enlaces, se cumple
  `TopStarK`.
* **`RowAgree`** (`RowAgree.lean`): los vivos de cada entrada de la línea cumplen los requisitos de su clave. Se
  conserva al llegar, al hacer join y en `advance`. De ahí sale `rowOwn_line`: lo que posee una cima cumple `rq t.id`.

### 2.3 La hipótesis reducida a una operación: `JoinStarCore`

* **`TopStarR`**: la cima está en una estructura cerrada que concuerda con `Q` y en la que está relacionada con todos
  sus nodos. A diferencia de «el núcleo por parejas máximo cumple los enlaces», es monótona por coberturas.
* **`topExact_arrival`**: el pin, la fila nueva y el review conservan `TopExact` sin hipótesis. De ahí,
  **`topStarR_of_topExact`**: toda llegada cumple `TopStarR`, porque la camarilla de la cima es la estructura.
* **`JoinStarCore φ`**: en cada paso, si todas las llegadas cumplen `TopStarR`, la unión de la línea siguiente lo
  cumple, fijada en cualquier `Q`.
* **`readerVerdict_iff_of_joinStarCore`**: la cadena `JoinStarCore` ⇒ `PinFreeF` (con `RowAgree`) ⇒ `LineInv` en cada
  paso ⇒ veredicto.

## 3. Lo medido sin fallos

| propiedad | sonda | alcance |
|---|---|---|
| (A) subida por el UP | `probe_star_step` | 9 192 cimas |
| (C) bajada a la llegada | `probe_star_step` | 6 961 cimas |
| linaje: verdad y reproducción con filtro compuesto | `probe_lineage` | 11 679 cimas / 15 660 casos |
| `TopsSep`, `TopStar`, `StarKinds` entre remitentes distintos | `probe_cross_star` | 5 779 cimas, 6 812 aristas |
| `PinFree` | `probe_pinfree` | 6 735 cimas |
| `StarCore`: el núcleo conserva `t` y todas las `t–y`, y cumple enlaces | `probe_starcore` | 12 699 cimas, 25 instancias |
| invariante por operación tras el review (pin, UP, join) | `probe_inv_ops` | 3 580 + 1 211 aplicaciones |
| cascada: testigo propio para cada `t–y` | `probe_star_cascade2` | 16,4 M tripletas, 10 354 cimas |

## 4. Lo falso (para no repetirlo)

| enunciado | qué dice | fallo medido |
|---|---|---|
| `TopsSep` entre copias del mismo remitente | la cima no vive en dos copias | 47 % de los casos |
| `StarKinds` con la copia del linaje | el orden A baja dentro de la copia | 3 085 aristas |
| pin del linaje completo | fijar los requisitos de todo el linaje | **mal definido**: el id solo recuerda tres pasos, así que el linaje no es función de la cima |
| `StarRestrict` | la estrella de una cima es cerrada por parejas | 4,9 % de las cimas tras UP; 13 % en uniones |
| estructura máxima ⊆ `rq` | la estructura máxima de la cima ya cumple los requisitos | 75 % discrepa; los nodos que discrepan son ajenos, a dos saltos, enganchados por un vecino compartido |
| `OwnClosed` con aristas ajenas | lo propio es cerrado | falla solo en parejas con arista ajena |
| `OwnRestrict` | la estructura máxima ∩ el estado propio, sin fijar, es una estructura | 9,4 % de las cimas (4,6 % con aristas de la unión fijada) |
| regla de la estrella como regla | cortar `t–y` fuera del núcleo de la estrella | **no corta nada**: es sólida pero vacía |

La escalera (`docs/context/escalera_reader.md` §2) ya tenía la lectura general: **ninguna propiedad local de un punto fijo
garantiza una cadena**. Cualquier prueba tiene que usar la historia de la máquina. Todo lo de esta tabla lo confirma:
cortar una estructura por un criterio local deja parejas que solo se sostenían con testigos de otro lado.

## 5. Dónde estamos

* **La cadena del lector está entera en Lean**, salvo un eslabón: la unión de las llegadas de un paso (`JoinStarCore`).
* **El eslabón es `TopUnion` en su forma más desnuda.** La sonda de la cascada lo muestra: todo depende de que la cima
  siga viva en su lado propio fijado en `Q`. Si lo está, su estructura propia queda entera en la unión y sostiene
  todas sus aristas. Si no, nada la sostiene.
* **Es el mismo enunciado con el que empezó el día** (`readerVerdict_iff_of_topUnion`, `1bdf816`). Pero la diferencia
  es grande:
  * antes, alrededor de `TopUnion` había varias hipótesis y ninguna pieza de la inducción;
  * ahora la inducción entera, la contabilidad y todas las demás operaciones son teorema, y `TopUnion` es lo único que
    queda.

## 6. Qué métodos funcionaron

Empezamos el día leyendo *Cómo entender y hacer demostraciones en matemáticas* (Solow). Así se reparten las técnicas
del libro en lo que salió:

* **Inducción con la hipótesis reforzada** (cap. 6): la inducción por linajes solo cerró cuando la hipótesis cuantificó
  sobre todos los pins y la partición se enunció para la familia entera.
* **Construcción** (cap. 4): `StarCore` da un objeto concreto como testigo de `TopStarK`, en lugar de un «existe».
* **Contraejemplo mínimo** (contradicción más mínimo, caps. 8 y 11): `noBad_of_descent` y el orden A. Hoy no hizo falta,
  porque la cascada mostró que el testigo propio nunca cae.
* **Progresivo-regresivo** (cap. 2): preguntar «¿qué necesito para cerrar este paso?» fue lo que separó el pin (que es
  contabilidad) del join (que tiene todo el contenido).

Lo que el libro no da es cómo demostrar que una unión de puntos fijos no fabrica nada nuevo. Para eso hace falta algo
de la máquina, y es lo que propone la §7.

---

## 7. La propuesta: etiquetas por fila con review por etiqueta

**Propuesto.** Me pediste revisar la idea de «tags de un solo nivel» y decir si se resuelve. La respuesta corta: **con
un nivel no; con todos los niveles y un review que las use, sí**, y el coste es polinómico. Lo desarrollo por partes.

### 7.1 Qué pide exactamente el eslabón que falta

`JoinStarCore` pide: si `t` está en el núcleo de la unión de la línea fijada en `Q`, entonces `t` está en el núcleo de
su propia llegada fijada en `Q`.

* El núcleo de la unión (`FamKernel`) admite estructuras cuyas parejas son aristas de **cualquier** llegada
  (`FamStruct.adj`: `∃ g, F g ∧ g.Adj y w`). Es exactamente lo que hace el join de la máquina: las tablas se unen.
* La dificultad no es la cima. La cima solo tiene aristas de su llegada (`TopsSep`, demostrado). La dificultad es que la
  estructura puede **apoyarse en aristas de otra llegada** para sostener parejas propias bajo un pin `Q`.
* `OwnRestrict` muestra que quitar a posteriori lo ajeno no deja algo cerrado. Hay que impedir que la mezcla se forme,
  no limpiarla después.

### 7.2 Por qué una etiqueta de un solo nivel no basta

Primero la idea tal como la planteamos: en el join del paso `T`, cada arista anota de qué llegadas viene, y el review de
la unión cierra cada llegada por separado.

**Lo que sí daría.** En el estado de ese paso, el núcleo fijado en `Q` sería la unión de los núcleos de las llegadas
fijados en `Q`. Tu observación es correcta y es clave: el lector selecciona cualquier nodo y aplica el review, así que
cualquier pin `Q` se trata con el mismo review etiquetado. El pin no es el problema.

**Lo que no daría (deducido, del código de `ltuf_core`).** La prueba no evalúa `JoinStarCore` solo en el estado final:
lo necesita en **cada paso de la línea**, con el pin que la inducción arrastra hacia abajo. El recorrido es:
1. el lector tiene una estructura en el estado final, fijada en `Q`;
2. la inducción la baja paso a paso por las filas nuevas (`famStruct_rows_down`) hasta la línea del paso `n+1`;
3. allí aplica la hipótesis de inducción `LTUf` a esa estructura bajada.

Si la hipótesis de inducción es «etiquetada», es decir, habla del núcleo cerrado por la etiqueta del paso `n+1`, la
estructura bajada tiene que respetar esa etiqueta. Pero la etiqueta del paso `n+1` se pierde en el join del paso `n+2`,
así que el review de los estados posteriores ya no la hace respetar. La estructura bajada puede mezclar lo que el paso
`n+1` separaba.

Es exactamente el fallo del v196 §4 en bin («la inducción baja a las fuentes, y ahí las etiquetas de un nivel ya no
están»), que aparece igual en bingo. **Una etiqueta de un nivel solo resuelve la unión del último paso.**

### 7.3 La propuesta: etiquetas de todas las filas, reducidas por el review

**Los datos.** Cada arista `y–w` lleva, por cada fila de claves `ℓ` (cada paso donde un join junta llegadas de
remitentes distintos), un conjunto `tag_ℓ(y–w)` de claves de esa fila. La clave es el nodo del mapa del remitente en
el paso `ℓ`. En el mapa bin son como mucho 2 por fila, así que son 2 bits.
* **En el UP**, una llegada del remitente de clave `k` hereda las etiquetas de su remitente y pone `{k}` en la fila
  nueva. El nodo nuevo hereda de sus padres.
* **En el join**, los conjuntos se unen fila a fila.
* **Con un pin**, los conjuntos no cambian; lo que cambia es qué nodos quedan vivos, y el review hace el resto.

Hasta aquí es el diseño del v197 §5. Allí el review **no miraba** las etiquetas, y por eso daban M1b pero no la unión.
**La novedad es la regla del review:**

> **Regla de la etiqueta.** Para cada fila `ℓ` y cada clave `a` de esa fila, la etiqueta `a` se quita de la arista
> `y–w` en la fila `ℓ` si, en algún paso `l`, no hay un testigo `r` con las aristas `y–r` y `w–r` vivas **y con `a` en
> su fila `ℓ`**. Lo mismo para los enlaces a padres e hijos. Una arista que se queda sin etiquetas en alguna fila
> muere.

Dicho de otra forma: en cada fila, el grafo se mira como la unión de sus piezas, una por clave, y cada pieza se revisa
por separado. Las piezas comparten nodos y aristas en memoria; solo el conjunto de etiquetas dice a qué pieza pertenece
cada arista.

**Solidez: no pierde soluciones (deducido).**
* Una solución pasa, en la fila `ℓ`, por una sola clave `a`.
* Su camarilla es un camino de la pieza `a` de esa línea, así que todas sus aristas llevan `a` en la fila `ℓ`. Es el
  argumento del v197 §5.5, y encaja con `run_carries`, ya demostrado.
* Para cada arista de la camarilla, los testigos de la propia camarilla llevan `a`. La regla nunca quita `a` de ellas.
* Por tanto la camarilla sobrevive, fila a fila, a toda aplicación de la regla. Es el mismo esquema que
  `carried_review`.

**No es la regla de tríos de §4.4, que perdía soluciones.** Aquella quitaba una arista `y–w` porque un tercer nodo
concreto no la acompañaba. Esta solo quita la etiqueta `a` de una arista cuando **ninguna** solución que pase por `a`
puede usarla.

### 7.4 Qué daría a la prueba (deducido)

1. **`JoinStarCore` por construcción.** En la fila del join del paso `T`, el núcleo fijado en `Q` es la unión de los
   núcleos de las piezas, cada una fijada en `Q`, porque la regla revisa cada pieza por separado.
   * La cima `t` solo tiene aristas con etiqueta `{k}`: su propia llegada (`TopsSep`).
   * Si `t` está viva, su pieza `k` fijada en `Q` la contiene.
   * La pieza `k` es la llegada, que cumple `TopExact` (`topExact_arrival`), así que hay una camarilla por `t`.
     Eso es `TopStarR`.
2. **La bajada respeta las etiquetas.** Las etiquetas de la fila `n` siguen en los estados de los pasos siguientes, y
   el review de esos estados sigue quitándolas por pieza. Así, una estructura del estado final bajada al paso `n+1` es
   cerrada pieza a pieza en la fila `n`. Es lo que la §7.2 echaba en falta.
3. **El resto no cambia.** La inducción por linajes (§2.1), `RowAgree`, (A), el pin y el UP son los mismos teoremas.
   Solo se reenuncian sobre el núcleo etiquetado (`FamStruct` con la condición de etiqueta por fila).
4. **Resultado esperado:** `readerVerdict φ = true ↔ Satisfiable φ` **sin hipótesis**, para la máquina con la regla de
   la etiqueta.

### 7.5 El coste

* **Memoria:** por arista, `w` bits por fila de claves. En bin, 2 bits por fila, como mucho `2·S` bits por arista.
  Con las aristas ya en un grafo aparte (`graph_owners`), es un vector de bits junto a cada arista.
* **Tiempo:** el review repite la regla de parejas por fila y por clave, un factor de como mucho `S·w` sobre el
  review actual. Unir y fijar pasan a ser operaciones sobre bits.
* **Sobre el rechazo anterior.** Me dijiste que ese camino se retiró porque escalaba exponencialmente. Lo he comprobado
  en el v197 §8.4, y lo que quedó escrito es otra cosa:
  * «crecimiento lineal en S, no exponencial». Se etiquetaban las filas por separado, nunca las combinaciones entre
    filas, que sí serían 2^S;
  * los 88,7 GB de `clause_mix_sep` venían de la **representación**: un diccionario por fila con claves de dos
    `PathNodeId`, unos 150 bytes por máscara, copiado entero en cada envío;
  * la información real eran unos 26 bytes por entrada, unas 500 veces menos.

  Si lo que recuerdas como exponencial es otra cosa (por ejemplo, que la mezcla casi total, 89 de 105 filas, hacía que
  nada se simplificara), es importante que me lo digas, porque cambia la recomendación. Aquí nunca se guardan
  combinaciones de claves entre filas.

### 7.6 Lo que no sé y los riesgos

* **Si la regla corta algo.** Si no corta nada en el corpus, como la regla de la estrella, los veredictos son idénticos
  y solo cuesta tiempo. La prueba seguiría valiendo, porque se apoya en la regla, no en que corte.
* **Que el review nunca baje de un kernel** tiene que reenunciarse para el núcleo etiquetado. Es el mismo riesgo que el
  v196 señalaba para la comprobación de claves. Aquí parece más sencillo, porque la regla es una regla de parejas por
  pieza, pero no está hecho.
* **Las filas con un solo remitente** no necesitan etiqueta. Si son la mayoría, el coste real baja mucho.
* **La mezcla por debajo de la cima** (filas en las que la pieza hereda tablas mezcladas del remitente). Es justo lo
  que la etiqueta por fila recuerda, pero hay que medirlo.

### 7.7 Plan, con criterio de parada

1. **Julia**, en una rama nueva desde `star-rule`, detrás de un flag (`ROW_TAGS=:off` por defecto):
   * vector de bits por arista en el grafo de owners;
   * herencia en el UP, unión en el join;
   * la regla de la etiqueta dentro del punto fijo del review.
2. **Medir** en el corpus de 88 instancias:
   * veredictos y soluciones iguales al exhaustivo, y al lector sin retroceso por todas sus ramas;
   * aristas y etiquetas cortadas;
   * tiempo y memoria frente a `:off`.
3. **Comprobar el efecto buscado:** con la regla, `TopUnion` en cada join fijado en `Q` tiene que salir sin
   excepciones, **y además por la razón buscada**: la cima vive en su pieza etiquetada.
4. **Solo si 2 y 3 salen bien, Lean:**
   * `TagStruct` (la condición de etiqueta en `FamStruct`);
   * la regla como `Rule` con `keepsSol`;
   * `topUnion_of_tags`;
   * reenunciar `ltuf_step` y `readerVerdict_iff` sobre el núcleo etiquetado.

**Criterios de parada.** Si en 2 cambia algún veredicto, la regla no es sólida tal como la escribí y hay que parar.
Si el coste en memoria supera un factor 10 en `clause_mix_sep`, hay que replantear la representación antes de seguir.

---

**Commits de esta sesión** (rama `star-rule`): `b1f0ac4` … `d4291de` (§1).
**Ficheros Lean nuevos:** `Lineage.lean`, `FamKernel.lean`, `LineStep.lean`, `DriverFam.lean`, `LineInduction.lean`,
`StarCore.lean`, `RowAgree.lean`, `JoinStar.lean`.
**Sondas nuevas** (`julia/improves_bingo/test_3sat/`): `probe_star_step`, `probe_crosstop`, `probe_lineage`,
`probe_cross_star`, `probe_lineage_frame`, `probe_pinfree`, `probe_star_restrict`, `probe_pinagree`,
`probe_pinagree_max`, `probe_ownclosed`, `probe_ownrestrict`, `probe_star_rule`, `probe_starcore`, `probe_inv_ops`,
`probe_star_cascade2`.
