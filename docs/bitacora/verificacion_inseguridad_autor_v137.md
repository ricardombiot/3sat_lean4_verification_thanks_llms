# Verificación para el Autor v137: claves y futuros — el join no es una fusión de OBDD

Ricardo, soy Claude (Opus 5). En v136 dejé una pregunta abierta: tu join fusiona estados por **clave**
(destino, origen), y en un diagrama de decisión ordenado (OBDD) comprobar el vacío es trivial porque
solo se fusionan nodos con el **mismo futuro**. ¿Cuándo tienen el mismo futuro dos estados con la
misma clave?

Lo he medido. Resultado en una frase: **casi nunca; tu join une futuros distintos, y aun así las tablas
no inventan pasados.** La compresión de la máquina vive exactamente donde vive el hueco.

Sonda nueva: modo `helly futures` en `lean_project/Probes/Helly.lean` (commit `dd4390c`). No hay Lean
nuevo en este informe; es medida.

---

## 1. Qué es "el futuro" de un estado

Un estado de la máquina, en el paso `cs`, guarda un conjunto de **pasados** (sus cadenas completas,
de 0 a `cs - 1`). Lo que falta por construir está fijado por el mapa: los nodos alcanzables desde la
clave `d` en los pasos `≥ cs`. Cada uno de esos nodos futuros impone **requisitos hacia atrás** (duros
y débiles, `reqOfCnf` y `weakReqOfCnf`), y esos requisitos son lo único por lo que el futuro depende del
pasado.

Así que el futuro de un estado queda determinado por **qué nodos futuros admite cada uno de sus
pasados**. La sonda mide dos cosas en cada join:

- **Criterio estricto (proyecciones).** La proyección de cada pasado sobre los pasos que los requisitos
  futuros consultan. Dos lados con las mismas proyecciones tienen, con certeza, el mismo futuro.
- **Criterio fino (firmas).** La *firma* de un pasado es el conjunto de nodos futuros cuyos requisitos
  cumple. El futuro de un lado es la clausura hacia abajo de sus firmas **máximas**; dos lados con las
  mismas firmas máximas ven el mismo futuro.

Y además, para el join ya revisado, si alguna proyección suya **no está en ninguno de los dos lados**
(`JOIN_SPURIOUS`): un pasado fabricado por la unión.

## 2. Resultados

Todo exhaustivo, nada truncado.

| familia | joins | sin futuro | mismo futuro | anidado | distinto | `JOIN_SPURIOUS` |
|---|---|---|---|---|---|---|
| Tseitin K4 par | 32 | 3 | 7 | 0 | 25 | **0** / 241 |
| Tseitin K3,3 par | 102 | 3 | 15 | 0 | 87 | **0** / 2.446 |
| Tseitin prisma par | 66 | 3 | 7 | 14 | 45 | **0** / 2.041 |
| Tseitin cubo par | 114 | 3 | 7 | 28 | 79 | **0** / 17.317 |
| paridad k3 | 114 | 48 | 62 | 21 | 31 | **0** / 2.084 |
| aleatorias, semilla 1001 (30 fórmulas) | 4.047 | 207 | 284 | 133 | 3.630 | **0** / 40.472 |
| aleatorias, semilla 2002 (30 fórmulas) | 4.101 | 172 | 248 | 93 | 3.760 | **0** / 37.892 |

(Las columnas "mismo / anidado / distinto" son del criterio fino; "sin futuro" son joins cuyo futuro
no consulta el pasado en absoluto, y el criterio fino los cuenta como "mismo".)

Con el criterio **estricto** el resultado es aún más extremo: 0 joins con el mismo futuro en las cuatro
familias Tseitin. Pero ese criterio es trivialmente severo: entre los pasos consultados está el del
**origen**, que por construcción es distinto en los dos lados. El criterio fino es el que cuenta.

Y un dato que pesa más que la tabla:

| familia | pasados (E) | firmas máximas (E) |
|---|---|---|
| Tseitin K4 | 122 | 122 |
| Tseitin K3,3 | 1.367 | 1.355 |
| Tseitin cubo | 9.101 | 8.956 |
| aleatorias 1001 | 24.524 | 23.155 |

**Casi cada pasado tiene un futuro propio.**

## 3. Qué significa

**(a) Tu join no es una fusión de OBDD.** En un OBDD solo se fusionan nodos con futuro idéntico, y por
eso el nodo *es* su subfórmula y el vacío se lee directamente. En tu máquina, entre el 68 % y el 92 % de
los joins (fuera de paridad) unen lados con futuros **distintos**. La clave (destino, origen) no captura
el futuro, porque las cláusulas miran hacia atrás y el futuro depende del pasado entero.

**(b) Una fusión por futuro no comprimiría.** Como el número de firmas máximas es casi el número de
pasados, un diseño que solo fusionara estados con el mismo futuro necesitaría prácticamente un nodo
por pasado. Eso es la explosión que tu diseño evita. Así que **la compresión de la máquina consiste
precisamente en unir futuros distintos**.

**(c) Y las tablas mantienen la separación.** A pesar de unir futuros distintos, el join revisado no
contiene **ningún** pasado que no estuviera en uno de los lados (0 de unos 80.000 en total). Es la
confirmación, a nivel de caminos completos, de la medida de cadenas mezcladas de v132 (0 de 1.027.901
cadenas parciales). Lo que impide la mezcla son las tablas de owners por pares.

**(d) Dónde deja esto el hueco.** Juntando (b) y (c): la máquina comprime uniendo futuros distintos, y
confía la separación a un resumen **por pares**. Todo lo que queda abierto desde v133
(`CommonOwner`, `ValidDecidesEmpty`) es la afirmación de que ese resumen por pares basta. **El hueco
está en el mismo sitio que la compresión**: no se puede eliminar el uno sin perder la otra. Es la
versión medida de lo que v134 §7 llamaba "el precio de la abstracción".

Esto no dice que el resumen por pares **falle**: en todo lo medido basta. Dice que no hay un atajo de
tipo OBDD para demostrarlo, porque la propiedad que hace trivial el vacío en un OBDD (fusionar solo lo
equivalente) es justo la que tu máquina **no** tiene, a propósito.

## 4. La cautela de la medida

La firma **sobrecuenta** diferencias: dos lados con firmas máximas distintas pueden tener, aun así, el
mismo conjunto de **continuaciones reales**, si la forma del mapa impide las combinaciones de nodos
futuros que los distinguen (una firma es un conjunto de nodos, no de caminos). Así que "distinto" es una
**cota superior**. Afinarla exige enumerar las continuaciones reales desde la clave, que es exponencial
en la longitud del futuro; es factible en las familias pequeñas si se quiere cerrar la cifra.

La cautela afecta a (a) solo en cantidad. No afecta a (c), que es exacta, ni a la lectura de (d).

## 5. Cómo queda todo

Sin cambios en lo demostrado desde v136:

| afirmación | estado |
|---|---|
| UNSAT: ejecución vacía ⟹ φ insatisfacible | demostrado sin hipótesis |
| SAT con camino | demostrado sin hipótesis |
| el conjunto de la máquina = los certificados | demostrado sin hipótesis (v136) |
| estado final válido ⟹ φ satisfacible | bajo `ValidDecidesEmpty` (v136), implicada por `CommonOwner` |

Lo nuevo es de mapa, no de prueba: **queda descartada la ruta de tipo OBDD** (fusionar por futuro
equivalente) como explicación de por qué el vacío es local, y queda medido que la separación de futuros
distintos la hacen las tablas por pares sin un solo fallo.

## 6. Qué haría ahora

Dos opciones, de más barata a más informativa:

1. **Afinar §4**: enumerar las continuaciones reales en las familias pequeñas para convertir la cota en
   cifra exacta. Cambia números, probablemente no la lectura.
2. **Mirar el caso anidado**: en prisma, cubo y paridad hay joins donde el futuro de un lado **contiene**
   el del otro. Ahí la unión es, en términos de futuro, casi gratuita (el lado pequeño no añade futuro
   nuevo). Si los joins anidados y los distintos se comportaran diferente respecto a `CommonOwner` —y
   la sonda `dead` puede separarlos—, eso daría la primera **clase estructural** de joins inocuos
   probada por medida, que es el tipo de paso que sí se puede formalizar.
