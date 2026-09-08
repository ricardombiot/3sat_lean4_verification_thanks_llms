# Verificación para el Autor v15: Cómo comprobar la validez, y qué dice al hacerlo

Ricardo, soy Claude (Opus 5). Me corregiste dos cosas y las dos eran correcciones justas: la lentitud no era una anomalía sino tu `O(S⁴·78)` cumpliéndose, y lo que hace falta no es más análisis de complejidad sino **saber comprobar si el algoritmo es válido**. Va de eso.

## 1. Por qué `diffTest` no basta

Tu banda diferencial compara **veredicto** y **conjunto de soluciones** contra el oráculo de fuerza bruta. Es una comprobación de caja negra, y tiene un punto ciego concreto:

> Un zombi —un nodo que sobrevive sin pertenecer a ninguna cadena co-poseída completa— **solo se ve ahí si además cambia el veredicto o el conjunto de soluciones**.

Puede aparecer a mitad de la ejecución y ser podado después. El resultado final sale bien, y no te enteras. Y "sin zombis" es justo la propiedad abierta, la que sostiene la soundness de tus veredictos.

## 2. Lo que he construido: `lake exe validate`

Comprueba la propiedad **directamente, como invariante interno, en cada estado que la máquina sostiene**:

> todo nodo que sigue en el grafo pertenece a alguna cadena co-poseída completa.

Dos decisiones para que la comprobación no sea el algoritmo juzgándose a sí mismo:

- **La búsqueda de cadena es independiente del Reader.** Es un backtracking llano sobre el grafo. Si el Reader tuviera un fallo, esto no lo heredaría.
- **Toda cadena encontrada se re-verifica desde las definiciones** (`IsChain` y `PairwiseOwned`) antes de darla por buena. Un positivo no es "la búsqueda dijo que sí", es "y además cumple la definición".

Dos modos:

```
lake exe validate <fichero.cnf> ...
lake exe validate --random <casos> <semilla> [minVars] [rangoVars]
```

Sale con código 1 si encuentra un zombi, y vuelca la instancia culpable a `validate_failure_<k>.cnf`. Es decir: **es un falsador, no una demostración**. Si tu algoritmo es incorrecto, esto es lo que lo va a decir.

## 3. Qué dice al ejecutarlo

**Campaña aleatoria** (mismos regímenes de densidad que `diffTest`: mayoría infra-restringidas, cada tercer caso pasada la transición de fase para cubrir UNSAT):

| | |
|---|---|
| instancias | 60/60 limpias |
| estados válidos comprobados | 5.466 |
| **nodos verificados** | **161.839** |
| zombis | **0** |

**Familias adversarias**, elegidas por lo que fui encontrando estos días:

| familia | por qué | resultado |
|---|---|---|
| literal repetido (`x ∨ x ∨ y`) | **viola `hreqs_distinct`** — cae fuera de todo lo demostrado | limpia |
| cláusula tautológica (`x ∨ ¬x ∨ y`) | los dos literales caen en pasos distintos | limpia |
| UNSAT forzado (las 8 cláusulas sobre 3 vars) | cubre la ruta de invalidación | limpia |
| transición de fase (`m ≈ 4.26n`) | donde SAT y UNSAT se mezclan | limpia |
| cadena implicativa larga | fuerza propagación a distancia | limpia |

Y sobre mapas reales sueltos, otros ~7.000 nodos, todos limpios.

## 4. Cómo leer esto, sin inflarlo

Esto **no demuestra** "sin zombis". Es evidencia, y es evidencia de una clase mejor que la que teníamos:

- Es **la propiedad abierta**, no un proxy. `diffTest` verificaba veredictos; esto verifica el invariante.
- Es **por nodo, no por instancia**. 161.839 oportunidades de fallar, no 60.
- Es **independiente**: búsqueda propia, verificación desde las definiciones.
- Es **falsable y barato**: una sola instancia lo tumba, y te la deja en un fichero.

Lo que no cubre, y conviene tenerlo escrito:

- El rango sigue siendo pequeño (`n ∈ 3..7` por defecto). El coste `S⁴` lo limita, no el checker.
- Comprueba el **espejo puro**, no el ejecutable. El puente entre ambos sigue siendo la banda diferencial.
- Las instancias son aleatorias uniformes más cinco familias elegidas a mano. No son adversarias *contra el invariante*; son adversarias contra lo que a mí se me ocurrió.

## 5. Lo que yo haría con esto

1. **Dejarlo corriendo en grande.** `--random 2000 <semilla>` con varias semillas, y subiendo `minVars` hasta donde el `S⁴` lo permita. Es la mejor relación información/esfuerzo que tienes ahora mismo.
2. **Meterlo en CI** junto a `diffTest`. Es un invariante, no un test de humo: si alguien toca el filtro o las pasadas de coherencia, esto se entera antes que los veredictos.
3. **Si algún día falla**, tendrás el contraejemplo exacto que tu propio documento del puente decía que valía tanto como la demostración. Y sabrás en qué estado y en qué nodo.

---

*Lo que me llevo: llevábamos días comprobando la validez de forma indirecta. Lo que faltaba no era otra demostración, era mirar el invariante de frente. Ahora se mira solo, en cada nodo de cada estado, y de momento no ha parpadeado ni una vez en 161.839 oportunidades.*
