# Verificación para el Autor v107: la frontera, de regla a invariante de prueba

Ricardo, soy Claude (Opus 5). Tras v106 buscamos una regla que permitiera demostrar el vacío. Este tramo probó dos reglas
basadas en la frontera, las descartó con datos, y convirtió la frontera en lo que sí aporta: un invariante exacto y una
reducción del veredicto SAT a un único paso.

Todo en la rama `spaik`, en el build de `AbsSat`, sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. Las reglas que no aportan

- **Bloques de cláusula derivada** (`FrontierDerive`, `lake exe frontier-derive`). Al olvidar una variable se añaden sus
  resolventes de anchura ≤ 3 como bloques de cláusula. Son correctos (mismas soluciones que la fórmula, comprobado con
  fuerza bruta en 21 fórmulas), pero la línea se vacía en el mismo paso o después, los estados inútiles no bajan y el
  trabajo y el tiempo suben. Lo que dicen esas resolventes ya lo veía la maquinaria de dos en dos.
- **Regla del triángulo sobre la frontera**. No la implementé: en v102 medimos que las tablas de owners ya son las
  proyecciones de dos en dos exactas del conjunto de caminos y no hubo zombis, así que no eliminaría nada.

La lección es la misma en ambos casos: en lo medido la máquina ya se comporta de forma exacta. Lo que falta es la prueba.

## 2. El invariante exacto de la frontera (`FrontierDP`)

Recorriendo las cláusulas en orden, la frontera tras `j` cláusulas son las variables que aparecen antes y después.
`InT φ j τ` dice que los valores de frontera de `τ` se extienden a un modelo de las `j` primeras cláusulas.

- `inT_succ`: extender con la cláusula siguiente y olvidar lo que sale de la frontera es exacto, en los dos sentidos. La
  prueba es la propiedad de la frontera: una variable del prefijo que reaparece está en la frontera anterior, así que el
  modelo del prefijo y el de la cláusula nueva se pegan sobre ella.
- `inT_zero`, `inT_all_iff`, `unsat_of_empty`: la tabla empieza llena, acaba no vacía si y solo si la fórmula es
  satisfacible, y una tabla vacía en cualquier paso refuta.

## 3. La reducción del veredicto SAT (`FrontierReduction`)

- **`PrefixSound`**: tras la cláusula `j`, la fila clave de cada estado se extiende a un modelo de las cláusulas `0..j`.
  Solo mira claves, así que los joins no le afectan. Medido: 0 fallos en 232 líneas y 756 estados (7 fórmulas).
- **`FrontierSend`** (hipótesis abierta): un envío válido desde una línea `PrefixSound` a una fila `d` de la cláusula `j`
  tiene un modelo de las cláusulas anteriores cuya fila en `C_j` es `d`.
- **Demostrado**: `FrontierSend` conserva `PrefixSound` (`prefixSound_pureAdvance`); con él, línea final no vacía implica
  fórmula satisfacible (`sat_of_pureRun_ne_nil`) y, con la completitud, la máquina de referencia decide
  (`run_pure_decides_of_FrontierSend`).

## 4. Lo que queda

| Pieza | Estado |
|---|---|
| invariante exacto de la frontera | demostrado |
| veredicto SAT correcto si vale `FrontierSend` | demostrado |
| `FrontierSend` | abierto; el punto duro es que la fila nueva coincida a la vez en sus variables compartidas con un modelo del prefijo |
