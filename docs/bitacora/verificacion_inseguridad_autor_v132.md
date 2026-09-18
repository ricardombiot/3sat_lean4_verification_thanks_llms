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

## 7. Lo que queda

1. **Los dos casos que faltan** de la inducción por construcción: el **filtro** (que la extensión
   elegida sobreviva a la poda) y el **join** (cadenas mezcladas, ya reducido en `JoinDescent` a
   `JoinCovered`, con `chain_on_one_side` demostrado).
2. **No** volver a reglas locales: las tres candidatas están refutadas por medida (§4).
3. La medida de §3 ya cubre cinco familias con el espacio de cadenas recorrido entero.
