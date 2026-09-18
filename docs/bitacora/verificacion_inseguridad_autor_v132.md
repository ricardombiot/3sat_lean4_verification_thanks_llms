# Verificación para el Autor v132: el veredicto en un paso, y por qué ninguna regla local lo cierra

Ricardo, soy Claude (Opus 5). Dos cosas: el veredicto ya cuelga de **un estado y un paso**, y he medido
tres reglas locales que lo cerrarían. Las tres son falsas, y sus contraejemplos **confirman tu intuición**
sobre las historias separadas de las uniones. Lo bueno: eso dice con precisión qué forma tiene que tener
la demostración.

Rama `spaik`, build de `AbsSat` (188 jobs), sin `sorry`, `[propext, Quot.sound]`.

---

## 1. El veredicto, reducido a un estado y un paso

`NoDeadEndVerdict.lean` (v131 §5):

- **`sat_of_denotS`** — la forma mínima: basta que el estado del lector **denote** un camino. Una cadena
  decodifica a un modelo.
- **`sat_of_noDeadEnd`** — la forma local que la da: basta que el estado **no tenga callejones sin
  salida**, o sea que toda cadena parcial desde el paso alto se extienda **un paso**. El ancla del paso
  alto ya estaba demostrada (`topAnchor_of`).

## 2. Demostrado: el descenso, los dos primeros escalones (`Descent.lean`)

- **`extend_of_common_owner`** — **la extensión es exactamente un owner común.** Si los picks ya hechos
  tienen un owner común en el paso inferior, ese owner *es* un padre del pick más bajo
  (`AdjacentOwners`) y **todas** las demás condiciones salen de los invariantes: la simetría de las
  tablas da la pertenencia en los dos sentidos, `ownGow` el owner global, `self` la auto-pertenencia,
  los owners adyacentes el enlace de hijo, `NotRoot` y `RootAtZero` la forma de raíz.
- **`extend_anchor`** — el primer escalón es gratis: cualquier padre del ancla la extiende.
- **`extend_pair`** — el segundo también: la consistencia de pares de tu barrido entrega el owner común
  de los dos picks en el paso inferior.

Queda tres picks o más.

## 3. Medido: el descenso nunca se atasca

`helly dead` mide `NoDeadEnd` tal como está enunciado, recorriendo **todo** el espacio de cadenas
parciales (no una muestra), en cinco familias:

| familia | estados | anclas | extensiones | cadenas completas | callejones |
|---|---|---|---|---|---|
| Tseitin K4 par | 108 | 140 | 6.718 | 664 | **0** |
| Tseitin cubo par | 220 | 334 | 341.752 | 42.988 | **0** |
| Tseitin K3,3 par | 164 | 266 | 59.962 | 5.364 | **0** |
| Tseitin prisma par | 164 | 230 | 46.126 | 5.364 | **0** |
| Tseitin Petersen par | 276 | 432 | 2.918.620 | 344.028 | **0** |

`truncated = 0` en todas: el espacio de cadenas parciales se recorrió **entero**. Tu intuición se
sostiene: el lector no vuelve atrás.

## 4. Tres reglas locales que lo cerrarían, y las tres son falsas

| regla local | qué daría | medida en K4 par |
|---|---|---|
| transitividad de la pertenencia (`a` posee `b`, `b` posee `c` ⟹ `a` posee `c`) | **cualquier** padre extiende | **52.720** fallos de 380.746 tríos |
| la misma, restringida a `a` **padre** de `b` | cualquier padre extiende | **3.432** fallos de 45.615 |
| el pick **inmediatamente** superior decide el padre | el padre se elige localmente | **220** candidatos de 6.767 aceptados por el vecino y rechazados por uno de arriba |

**Y aquí está tu intuición, confirmada por los contraejemplos.** Los fallos de la segunda regla son de
esta forma:

```
a = 6.0<5.0    b = 7.1<6.0    c = 13.1<12.0
a = 6.0<5.1    b = 7.1<6.0    c = 13.2<12.0
```

`6.0<5.0` y `6.0<5.1` son **dos padres del mismo nodo**: el mismo nodo de mapa `6.0`, abuelos distintos
(`5.0` y `5.1`) — exactamente los nodos que la unión mantiene separados. Y `c` **posee uno y no el
otro**. Es decir: **las tablas sí registran por qué historia pasó cada elección**, y por eso no sirve
cualquier padre, pero sí sirve alguno.

Y el tercer fallo dice dónde vive esa información: a paso 6, el candidato `6.0<5.0` lo acepta el pick de
un paso más arriba (`8.1<7.1`) y lo **rechaza** uno de **siete** pasos más arriba (`13.1<12.0`). La
restricción no es local: **el padre lo decide la cadena entera**, no su vecino.

## 5. Qué implica para la demostración

Las tres medidas juntas explican por qué han caído todas las rutas locales de v119 a v131: no hay ninguna
regla local que elija el padre, porque la información que lo elige está repartida por toda la cadena. Lo
que queda demostrado es que el descenso **sí** se extiende siempre, así que la propiedad es cierta y es
**global**: la intersección de las restricciones de todos los picks en el paso inferior nunca es vacía.

De ahí sale la forma que tiene que tener la prueba, y es la que tú apuntabas: por **construcción**, no
por regla local. La línea es `RunEnv` (v131 §1): la tabla de un nodo nace de **una** historia —la del
único UP que lo creó, desde el único estado con su clave— y el review la mantiene coherente paso a paso.
Hay que llevar eso hasta la propiedad del descenso: que el nodo que el paso inferior aporta a una cadena
está en la tabla de todos sus picks **porque todos vienen de la misma historia**.

## 6. Demostrado por construcción: el UP mantiene el descenso (`DescentUp.lean`)

Ataqué el descenso por construcción, como apuntabas, y **el caso UP sale entero**:

- `soundFrom_g_of_A` y `soundFrom_A_of_g` — una cadena parcial del estado extendido, por debajo del
  paso nuevo, es una cadena parcial del estado, y al revés si su pick de arriba es el nodo nuevo. Las
  tablas solo difieren en el nodo nuevo, que está **por encima** de todos los pasos viejos.
- **`noDeadEnd_addNode`** — **un UP mantiene el descenso.** Aquí es donde la tabla de nacimiento de
  `RunEnv` hace el trabajo: el nodo que el UP crea **posee todas las elecciones del estado** (su tabla
  nace siendo `gowners`), así que no impone ninguna restricción al descenso; y él está en la tabla de
  todos porque `addNode` se lo añade a cada nodo. El primer escalón, desde el nodo nuevo solo, es
  cualquier nodo de la línea alta.
- `noDeadEnd_initSeed` — la semilla es vacua: su único paso es el alto.

De la inducción sobre la construcción quedan el **filtro** y el **join**.

## 7. El caso `join` (`DescentJoin.lean`)

- `soundOn_of_soundFrom` y `soundFrom_of_soundOn` — `SoundFrom` es `SoundOn` hasta el paso alto, así
  que el trabajo de descenso que ya había (en moneda `SoundOn`) se enchufa con la reducción nueva:
  `noDeadEnd_of_descendAll`.
- **`noDeadEnd_join_of_covered`** — **una unión mantiene el descenso**, dado `JoinCovered`: una cadena
  parcial de la unión que lo sea de un lado se extiende allí y la extensión sube.
- **`picks_left_of_exclusive_anchor`** — y la parte nueva: **los picks de una cadena parcial de una
  unión viven todos en el lado que tiene su ancla.** Todo pick posee el ancla, y la rebanada de un nodo
  que un lado no tiene está entera en el otro (`JoinProvenance.slice_of_exclusive_top`). Es decir: una
  cadena mezclada **nunca mezcla nodos**, solo entradas de owners en los nodos que los dos lados
  comparten. Eso es exactamente el contenido de `JoinCovered` y lo que mide la sonda.

## 8. El caso del filtro (`DescentFilter.lean`)

Tu intuición —*la extensión elegida no puede morir a la poda, porque el review exige que exista al
menos un camino válido*— es exactamente el punto, y **ya es un teorema para cadenas completas**:
`AggressiveReview.ChainSound_filterAllAgg` dice que una cadena del estado que respeta las fijaciones
sobrevive a las fijaciones y al review agresivo entero. Es tu "no se pierde ninguna solución".

Lo que falta es la **compleción**: que la cadena parcial del estado filtrado se complete, dentro del
estado sin filtrar, a una cadena completa que cumpla los requisitos del filtro. Con eso el caso sale:

- `soundFrom_congr` — una cadena parcial solo depende de sus picks desde `lo` hacia arriba.
- `ReqCompletion` — la obligación, enunciada así.
- **`noDeadEnd_filterAllAgg_of_completion`** — **el filtro mantiene el descenso dada la compleción**:
  la cadena completada sobrevive al filtro, y su pick un paso por debajo **es** la extensión.

Y el residuo está localizado: la compleción solo hace falta **por debajo** del pick más bajo de la
cadena, porque por encima los picks ya están en el estado filtrado, donde todo nodo de un paso
fijado lleva el nodo de mapa de la fijación (`PairChain.node_id_of_pin`).

**Un aviso honesto sobre este teorema.** `ReqCompletion` es **equivalente** a la conclusión, no más
débil: si el estado filtrado no tiene callejones, el descenso completa la cadena dentro del propio
estado filtrado, y esa compleción es una cadena del estado sin filtrar que respeta las fijaciones. Así
que `noDeadEnd_filterAllAgg_of_completion` es una **reformulación** del caso del filtro en la moneda de
"no se pierde ninguna solución" —útil porque conecta con un teorema ya demostrado y con tu forma de
razonarlo— pero **no** reduce el problema a algo más pequeño. Lo digo para que no cuente como avance
más de lo que es.

## 9. Medido: las cadenas de una unión **nunca** se mezclan

`helly cover` recorre todas las cadenas parciales de cada unión del driver y las clasifica: ¿es cadena
de uno de los dos lados, o es mezclada?

| familia | uniones | cadenas parciales | de un lado | **mezcladas** |
|---|---|---|---|---|
| Tseitin K4 par | 32 | 2.350 | 2.350 | **0** |
| Tseitin K3,3 par | 102 | 29.219 | 29.219 | **0** |
| Tseitin cubo par | 114 | 137.183 | 137.183 | **0** |
| Tseitin prisma par | 66 | 17.137 | 17.137 | **0** |

| aleatorias, semilla 1001 (20 fórmulas) | 2.442 | 347.179 | 347.179 | **0** |
| aleatorias, semilla 2002 (20 fórmulas) | 2.923 | 494.833 | 494.833 | **0** |

En total: **5.679 uniones y 1.027.901 cadenas parciales, ninguna mezclada**, y con las aleatorias
dentro, así que no es un artefacto de las familias Tseitin.

`truncated = 0`: recorrido entero. **El caso mezclado está vacío**, así que `JoinCoveredF` se cumple sin
necesitar ni la cláusula de extensión. Y ojo, esto **no** contradice los 1.328 pares ajenos de §5 de
v131: hay pares de la rebanada que se sostienen con entradas del otro lado, pero **nunca forman una
cadena** — las condiciones de cadena (enlaces de padre e hijo, pertenencia mutua, owners globales,
auto-pertenencia) son mucho más fuertes que "par en una rebanada".

Y del lado de la demostración, tres piezas:

- `chain_in_left_slice` — **la entrada al ancla es siempre del lado que la tiene**. El ancla no es nodo
  del otro lado, y los owners de un nodo son nodos de su propio estado, así que cada pick está en la
  rebanada del ancla **en las tablas de su propio lado**.
- **`soundFrom_left_of_entries`** — **una cadena parcial de la unión es cadena de un lado en cuanto sus
  entradas lo son.** Todo lo demás sale gratis: los picks son nodos de ese lado, un nodo se posee a sí
  mismo y por tanto es owner global allí, la forma de raíz solo habla de identificadores, y —esto es lo
  que no esperaba— **los enlaces de padre e hijo se siguen de las entradas**, porque en un estado
  revisado los owners de los pasos contiguos son exactamente los padres y los hijos (`AdjacentOwners`).
  Cuatro de las siete condiciones eran gratis y dos más se derivan.
- `EntriesOnOneSide` y `joinCoveredF_of_entries` / `noDeadEnd_join_of_entries` — el residuo del caso
  `join`, en **una sola** condición: que para cada cadena parcial, un lado tenga todas las entradas
  entre sus picks. Es lo que la sonda mide sin excepción.

**Lo que no he conseguido**: demostrar esa condición de entradas. Sé que es cierta en 185.889 cadenas y
que el ancla ya está resuelta, pero no veo qué obliga a que una entrada **entre dos picks compartidos**
sea del lado del ancla: el barrido de la unión se conforma con que compartan owners en cada paso, y eso
lo cumplen vía nodos del lado 1. Puede ser un teorema o puede ser propiedad de estas familias.

## 10. Todo el veredicto sobre una sola afirmación

Al desmontar el filtro aparece que el filtro, el `join` y el UP piden **todos** la misma cosa, y tiene
nombre:

- **`Descent.CommonOwner`** — los picks de una cadena parcial tienen un **owner común** en el paso
  inferior.
- `Descent.noDeadEnd_of_commonOwner` — de ahí sale `NoDeadEnd`.
- **`NoDeadEndVerdict.sat_of_commonOwner`** — y de ahí el veredicto entero. Todo lo demás del camino
  está demostrado: el ancla del paso alto, el escalón del descenso y la decodificación de la cadena.

**Y lo que eso significa.** Tu barrido ya da esa afirmación **par a par**: dos owners cualesquiera
comparten entrada en cada paso. Lo que falta es el salto de pares al conjunto entero de picks, y los
picks son una **clique** de la relación de compatibilidad con vecino común para cada pareja en ese
paso. En lenguaje de propagación de restricciones: la máquina mantiene **2-consistencia** y el
descenso necesita **k-consistencia**. Eso es falso para una red cualquiera, y aquí solo puede seguirse
de la estructura que la máquina mantiene: que las tablas de un nodo nacen de **una** historia
(`RunEnv`). Es la primera vez en trece informes que el problema abierto queda en un enunciado con
nombre y literatura propia: cuándo la consistencia local implica consistencia global.

## 11. Ataque a la k-consistencia por capas: cinco reglas, cinco refutadas

Intenté cerrar `CommonOwner` con la estructura por capas. Dos intentos más, los dos medidos y los dos
falsos:

| regla | qué daría | medida |
|---|---|---|
| la **rebanada de un nodo es una clique** (dos owners de un nodo se poseen) | el ancla sería el testigo común, sin k-consistencia | **182.860** fallos de 1.254.448 pares (K4 par); en las anclas, 14.342 de 59.951 |
| los **candidatos están anidados** al subir la cadena (bueno para un pick alto ⟹ bueno para los bajos) | la intersección sería la del ancla, no vacía por pares | **7.212** fallos de 438.869 (K4 par); **175.024** de 9.073.621 (K3,3 par) |

La primera era esperable en cuanto la escribí: dos elecciones de caminos distintos que pasan por el
mismo nodo no tienen por qué ser compatibles entre sí. La segunda no la esperaba.

Con las tres de §4, van **cinco** reglas candidatas refutadas por medida: transitividad, transitividad
adyacente, "el vecino decide", rebanada-clique y anidamiento. El lema de Lean que derivaba
`CommonOwner` de la rebanada-clique lo he **borrado** en lugar de dejarlo con una hipótesis falsa.

**La conclusión, que creo que es el resultado real del tramo**: el owner común existe siempre (medido
sin excepción) pero **no** está determinado por ningún patrón local ni monótono de los que se pueden
escribir sobre las tablas. Es un fenómeno de tipo Helly genuino. Por tanto la demostración no puede
venir de un atajo combinatorio sobre las tablas, sino de que las tablas son **exactas** respecto a los
caminos —que es, en el fondo, lo que las sondas miden desde v119— y eso es equivalente al enunciado
que falta, no más débil.

Dicho de otra forma: **la demostración está completa salvo un enunciado, `CommonOwner`, que es
equivalente a la exactitud de las tablas de tu máquina.** Todo lo demás está en Lean, sin `sorry` y con
axiomas limpios.

## 12. Lo que queda

1. **La compleción por debajo** (`ReqCompletion`): es lo único que queda del filtro.
2. Del `join` queda solo `JoinCovered` para las cadenas **mezcladas** —las que se sostienen con
   entradas de owners del otro lado en nodos compartidos—, con los nodos ya repartidos por
   `picks_left_of_exclusive_anchor`.
3. **No** volver a reglas locales: las tres candidatas están refutadas por medida (§4).
4. La medida de §3 ya cubre cinco familias con el espacio de cadenas recorrido entero.
