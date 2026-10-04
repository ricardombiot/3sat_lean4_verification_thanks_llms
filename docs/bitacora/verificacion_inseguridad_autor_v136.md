# Verificación para el Autor v136: la máquina calcula el conjunto de certificados, exactamente

Ricardo, soy Claude (Opus 5). Me propusiste cambiar de nivel: tu máquina trabaja con **conjuntos** de
caminos parciales y el problema habla de **un** camino. ¿Y si redefinimos el problema a nivel de
conjuntos —*devolver un conjunto que contenga todos los certificados*, como hacía el oráculo— y luego
reducimos un problema al otro?

Lo he formalizado. Resultado en dos frases:

1. **El problema de conjuntos está resuelto, sin hipótesis.** El conjunto que representan las tablas
   del estado final es **exactamente** el conjunto de certificados de φ: contiene todos y no contiene
   nada que no certifique un modelo.
2. **La vuelta de conjuntos a SAT es la prueba de vacío**, y ahí es donde vive todo lo que falta. Queda
   aislada en un enunciado, `ValidDecidesEmpty`, que es **más débil** que `CommonOwner` y que basta para
   el veredicto.

Módulo nuevo `AbsSat/GraphPath/Model/CertificateSet.lean`. Build de `AbsSat` (193 jobs), sin `sorry`,
sin avisos, `[propext, Quot.sound]` en todos los teoremas.

---

## 1. El conjunto de la máquina

La máquina no guarda caminos: guarda tablas. Pero unas tablas **denotan** un conjunto de caminos, los
de sus cadenas `ChainSound` (`denotS`, que ya usábamos desde `SubsetSemantics`). Con eso:

```lean
/-- El estado de lector de un estado final: el review sin fijaciones. -/
abbrev reader (g : GPathM) : GPathM := filterAllAgg g []

/-- El conjunto que calcula la máquina: los caminos de los estados de lector de la última línea. -/
def MachineSet (p : List NodeId) : Prop :=
  ∃ kv ∈ pureRunW φ, denotS (reader kv.2) p

/-- El certificado de una asignación: el camino que sus elecciones trazan en el mapa. -/
def certPath (a : Assign) : List NodeId :=
  (intRange 0 (stepCount φ - 1)).reverse.map (selOfAssign φ a)
```

`MachineSet` es la **unión**, sobre los estados de la última línea (uno por clave final), de lo que
denota cada uno. Es exactamente la lectura de conjuntos que tú haces de la máquina.

## 2. Los tres teoremas: el conjunto es exacto

| teorema | enunciado | de dónde sale |
|---|---|---|
| `machineSet_complete` | toda asignación que satisface φ tiene su camino **en** el conjunto | la ley de conservación (`chainSound_alongW`) llevada a través del review del lector (`ChainSound_filterAllAgg`) |
| `machineSet_sound` | todo camino del conjunto **deletrea un modelo** de φ (la decodificación de su cadena) | los invariantes de la última línea (`pureRunW_state`) y la decodificación por prefijos |
| `machineSet_nonempty_iff` | el conjunto es **no vacío ⟺ φ es satisfacible** | los dos anteriores |

Sin hipótesis. Es la formalización de lo que dijiste: la máquina hace lo mismo que el oráculo, que
listaba el conjunto de certificados explícitamente; la diferencia es que tu máquina lo guarda
**comprimido** en tablas por pares, con uniones que evitan la explosión espacial.

Un matiz de precisión, para no sobrevender: `machineSet_sound` dice que cada camino deletrea **un**
modelo (el que se lee en los pasos de variable). No dice que el camino sea `certPath` de ese modelo:
en los pasos de cláusula el camino puede elegir otro literal satisfecho que el que elegiría
`selOfAssign`. Es decir, el conjunto contiene **los** certificados y además, posiblemente, **otras
formas** de certificar el mismo modelo —todas válidas—. Para la pregunta que nos ocupa (vacío o no)
es indiferente.

## 3. La reducción de vuelta: la prueba de vacío

Aquí está lo importante. "Devolver un conjunto que contenga todos los certificados" es **trivial por
sí solo**: el conjunto de todas las asignaciones los contiene. El problema de conjuntos solo dice algo
de SAT cuando se puede **consultar** el conjunto, y la consulta que SAT necesita es una sola:

> ¿el conjunto está vacío?

Con el conjunto explícito del oráculo esa consulta es inmediata (mirar si la lista está vacía), pero el
conjunto explícito es exponencial. Con el conjunto comprimido de tu máquina, la consulta hay que
hacerla **sobre las tablas**, y la máquina la hace con `isValid`. Así que la reducción se descompone
en dos direcciones:

| dirección | enunciado | estado |
|---|---|---|
| no vacío ⟹ válido | un estado que denota algún camino tiene tablas válidas | **gratis** (`isValid_of_denotS`) |
| válido ⟹ no vacío | tablas válidas ⟹ el estado denota algún camino | **`ValidDecidesEmpty`**, abierta |

```lean
def ValidDecidesEmpty : Prop :=
  ∀ kv ∈ pureRunW φ, isValid (reader kv.2) = true → ∃ p, denotS (reader kv.2) p
```

Y con ella el veredicto sale como **reducción literal** desde el problema de conjuntos:

| teorema | enunciado |
|---|---|
| `exists_valid_of_sat` | φ satisfacible ⟹ algún estado de lector de la última línea es válido — **sin hipótesis** |
| `valid_iff_nonempty` | bajo `ValidDecidesEmpty`, en cada estado: válido ⟺ no vacío |
| `verdict_iff` | bajo `ValidDecidesEmpty`: **algún estado de lector válido ⟺ φ satisfacible** |
| `validDecidesEmpty_of_commonOwner` | `CommonOwner` en los estados válidos ⟹ `ValidDecidesEmpty` |

## 4. Lo que gana la reformulación

**(a) La hipótesis se debilita.** `ValidDecidesEmpty` pide **un** camino por estado válido.
`CommonOwner` pide que **toda** cadena parcial se extienda, que es mucho más: es la forma que usa el
lector para *encontrar* el camino sin retroceder. Para el veredicto —decir SAT o UNSAT— basta
`ValidDecidesEmpty`; `CommonOwner` hace falta además para que la lectura sea voraz. Hasta ahora las
dos cosas iban juntas; ahora están separadas y demostradas por separado:

```
CommonOwner  ⟹  NoDeadEnd  ⟹  ValidDecidesEmpty  ⟹  veredicto correcto
 (lectura voraz)                (prueba de vacío)
```

**(b) El hueco tiene nombre fuera del proyecto.** Esto encaja exactamente en la teoría de la
**compilación de conocimiento**, que estudia representaciones compactas del conjunto de modelos de una
fórmula y qué consultas son baratas en cada una. En ese vocabulario:

| compilación de conocimiento | tu máquina |
|---|---|
| lenguaje de destino | las tablas de owners, con uniones por clave |
| compilar φ | ejecutar la máquina |
| la compilación es **equivalente** a φ | `machineSet_nonempty_iff` y sus dos mitades — **demostrado** |
| consulta de **consistencia** (¿es vacío?) | `isValid` |
| la consistencia es correcta en ese lenguaje | `ValidDecidesEmpty` — **abierto** |

Y la teoría tiene un ejemplo canónico de *por qué* la consulta de vacío puede ser local: en **DNNF**
(forma normal negada descomponible) la consistencia se decide en tiempo lineal porque cada conjunción
junta partes que **no comparten variables** —la **descomponibilidad**—, de modo que ninguna combinación
de elecciones locales consistentes puede chocar globalmente. `CommonOwner` juega en tu máquina el
papel que la descomponibilidad juega en DNNF: es la propiedad estructural que convertiría la validez
local en no-vacío global.

**(c) Se ve dónde encaja cada pieza de v129–v135.** Lo que las tablas guardan son **pares**
compatibles (2-consistencia, `aggOk_reviewAgg`); lo que la consulta de vacío necesita es **un conjunto**
compatible (k-consistencia). En compilación de conocimiento eso tiene una lectura directa: un lenguaje
que solo guarda compatibilidades por pares **no es descomponible por sí mismo**, porque los requisitos
de cláusula enlazan pasos lejanos. La pregunta abierta es si las **uniones por clave** de tu máquina
—la separación de historias por (destino, origen) que formalizamos en `RunEnv`— aportan una
descomponibilidad suficiente, aunque no sea la de DNNF.

## 5. Lo que la reformulación no gana

Con honestidad: **no hace desaparecer el hueco, lo traslada y lo nombra mejor**. Cambiar al problema
de conjuntos no vuelve fácil nada, porque:

- el problema de conjuntos **con conjunto explícito** es fácil de consultar pero exponencial de
  guardar;
- el problema de conjuntos **con conjunto comprimido** es barato de guardar, y toda la dificultad pasa
  a la consulta de vacío.

Esto no es un límite de tu máquina: es la forma general del problema en compilación de conocimiento,
donde cada lenguaje paga en algún sitio —en el tamaño de la compilación o en el coste de las
consultas—. Lo que tu máquina tiene de particular es que **la compilación está demostrada exacta** y
**el tamaño está bajo control por diseño** (las uniones por clave); lo que falta es la consulta.

Tampoco es una afirmación de coste: nada de lo que hay aquí habla de tiempo ni de espacio.

## 6. Cómo queda todo

| afirmación | estado |
|---|---|
| UNSAT: ejecución vacía ⟹ φ insatisfacible | **demostrado sin hipótesis** (`pureRunW_ne_nil`) |
| SAT con camino: un camino leído ⟹ φ satisfacible | **demostrado sin hipótesis** (`sat_of_denotS`) |
| **el conjunto de la máquina = los certificados** | **demostrado sin hipótesis** (`machineSet_complete`, `machineSet_sound`, `machineSet_nonempty_iff`) — **nuevo** |
| φ satisfacible ⟹ algún estado final válido | **demostrado sin hipótesis** (`exists_valid_of_sat`) — **nuevo** |
| estado final válido ⟹ φ satisfacible | **bajo `ValidDecidesEmpty`** (`verdict_iff`) — **nuevo, hipótesis más débil** |
| la lectura voraz nunca se atasca | bajo `CommonOwner` (`sat_of_commonOwner`) |

Las rutas por construcción de v135 (exactitud de tablas por entradas y por cadenas) siguen igual; lo que
cambia es el **objetivo mínimo**: basta demostrar `ValidDecidesEmpty`, no `CommonOwner`.

## 7. Qué haría ahora

`ValidDecidesEmpty` pide solo **un** camino por estado válido, así que la tentación es guardar **un
testigo por estado**. No funciona tal cual, y conviene decirlo antes de medir nada: el filtro fija los
requisitos del destino, y en cuanto el testigo no pasa por la fijación muere; encontrar otro camino
que sí pase es exactamente la prueba de vacío que queríamos evitar. Un testigo por estado se reduce,
en el filtro, a testigos por combinación de fijaciones, y eso vuelve al salto de pares a conjuntos.

Lo que sí veo prometedor es la comparación con la compilación **por capas**, que es la más cercana a
tu diseño. En un diagrama de decisión ordenado (OBDD/MDD), que también se construye paso a paso y
también **fusiona nodos**, el vacío es trivial porque solo se fusionan dos nodos cuando su **futuro** es
idéntico: el nodo representa exactamente la subfórmula que queda. Tu join fusiona por **clave**
(destino, origen), y el futuro de un estado **no** depende solo de la clave, porque las cláusulas miran
hacia atrás; esa dependencia del pasado es lo que llevan las tablas de owners, resumida por pares.

La pregunta que eso deja es concreta: **¿cuándo dos estados con la misma clave tienen el mismo
futuro?** Donde lo tengan, la unión es una fusión de OBDD y no pierde exactitud; donde no, es donde el
resumen por pares tiene que hacer el trabajo, y ahí vive el hueco. Es medible con las sondas que ya
tenemos (comparar, en cada join, los requisitos pendientes que ven los dos lados), y creo que
localizaría el problema mejor que cualquiera de las rutas anteriores.
