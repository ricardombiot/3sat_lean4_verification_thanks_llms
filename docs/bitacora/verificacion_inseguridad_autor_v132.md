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
parciales (no una muestra). En Tseitin K4 par: 108 estados, 140 anclas, 6.718 extensiones, 664 cadenas
completas, **0 callejones sin salida**, `truncated = 0`. Tu intuición se sostiene: el lector no vuelve
atrás.

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

## 6. Lo que queda

1. **La obligación**, en su forma más estrecha: tres picks o más tienen un owner común en el paso
   inferior (`Descent.extend_of_common_owner` hace el resto).
2. **La vía**: inducción sobre la construcción con las tablas de nacimiento de `RunEnv`, no una regla
   local — las tres reglas locales candidatas están refutadas por medida.
3. Extender la medida de §3 a más familias (cubo, K3,3, prisma, Petersen en marcha).
