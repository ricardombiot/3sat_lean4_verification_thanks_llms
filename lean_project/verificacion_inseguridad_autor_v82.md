# Verificación para el Autor v82: lo intenté en general — y encontré que P4 no reducía nada

Ricardo, soy Claude (Opus 5). Me pediste que confiara más en el diseño y que intentara demostrar `PinReaches`/`PinNonEmpty` **en general, sin clase y sin sesgos**. Lo he intentado de verdad, y el intento ha dado un resultado definido. No es el que yo quería, pero es mejor que una respuesta vaga.

---

## 1. El intento

La demostración natural de «el mayor tejido compatible con el pinchazo no está vacío» va así: ese tejido se calcula **borrando iterativamente todo nodo que no tenga un miembro-owner en algún paso**, hasta el punto fijo. Empecé a escribirlo y me paré, porque ese procedimiento **es literalmente tu `review` + `cleanInvalid`**.

Si eso es cierto, entonces `PinNonEmpty g q` —lo que ayer presenté como la obligación reducida— no es más débil que `isValid (filterAll g [q.id])`, que es lo que había que demostrar. Sería una reformulación, no una reducción.

## 2. Lo medido

Modo nuevo, `cnfmap --tauto`: para cada owner `q` en cada paso con elección de cada estado válido, comparo *el mayor tejido entre los nodos compatibles con pinchar `q` es no vacío* contra *la máquina dice que el estado pinzado es válido*.

| tres semillas | pinchazos | ambos sí | ambos no | tejido sí, válido no | **tejido no, válido sí** |
|---|---|---|---|---|---|
| | **9.926** | **9.926** | 0 | 0 | **0** |

**Coincidencia perfecta, en las dos direcciones, sin una sola excepción.** La implicación que demostré ayer (`PinNonEmpty → isValid`) tiene recíproca, y por tanto:

> **P4 es una reformulación, no una reducción.** La obligación que quedaba al final de la ruta es equivalente a la que había al principio.

Por eso pude empujarla tan deprisa en una sesión: no estaba pagando nada.

## 3. Qué se retira y qué no

Como en v74: **no se retira ningún teorema, se retira una afirmación mía sobre su alcance.**

Siguen en pie, y son correctos: `Fabric_initSeed`, `Fabric_addNode` (con su cláusula `up` resuelta por la simetría), `Fabric_of_grown` y los dos lados del `join`, `Fabric_core` sin axiomas, y todos los puentes. Lo que se cae es la frase «la ruta queda con una sola obligación **más simple**». La obligación es una, sí, pero no es más simple: es la misma.

## 4. El hallazgo que sí vale, y es sobre tu algoritmo

Lo interesante es el motivo del fracaso, porque es una **caracterización**:

> **Tu `review` + `cleanInvalid` calcula exactamente el mayor tejido.** No una aproximación suya: el punto fijo mayor.

Eso no es un consuelo, es el enunciado más limpio que hemos encontrado en ochenta informes de *qué es* tu máquina. Y explica de golpe varias cosas que veníamos observando sin entender del todo: por qué el tejido mayor dentro de `owners(r)` resultaba ser **todo** `owners(r)` (v65, 4.888 de 4.888), por qué cubría todos los pasos en los pasos de cláusula (v77, 124.246 nodos), y por qué nunca se rompía. No se rompía porque **es lo que la máquina ya mantiene**, medido contra sí mismo.

Y también explica, sin sesgo por mi parte, por qué el caso general no sale por aquí: pedirle al mayor tejido que implique «existe solución» es pedirle a la **consistencia local que decida**. El objeto que construí resultó ser el que tu máquina ya computa, luego no puede contener información que tu máquina no tenga. No es que yo me niegue a intentarlo: es que el intento, hecho, desemboca en la identidad.

## 5. Lo que queda vivo, dicho sin sesgo

Descartada la vía circular, quedan dos, y **una de ellas es tuya**:

1. **La clase** (v76): anchura acotada, que es la hipótesis que por Freuder convierte consistencia local en decisión. Demostrable, y ahora enunciable sobre el tejido, que es tu propio punto fijo.

2. **Subir el nivel de consistencia** — que es exactamente lo que hiciste en v69 con la pasada del triángulo. Y ahora se entiende mejor qué significa: **no es parchear, es cambiar el objeto**. Un tejido de nivel 3 es un punto fijo distinto y mayor poder de poda. v70 ya midió la escalera siguiente: 38 huecos de tríos, 7 genuinos. Ese es material real para un nivel 4, y cada nivel ensancha la clase de §1.

Lo que **no** queda vivo es esperar que reorganizar el mismo punto fijo dé más de lo que el punto fijo tiene. Eso es lo que acabo de comprobar, y prefiero habértelo comprobado a habértelo seguido vendiendo.

Build: `lake build AbsSat` verde, 100 módulos, 0 `sorry`, 0 axiomas de proyecto. Ningún teorema retirado.
