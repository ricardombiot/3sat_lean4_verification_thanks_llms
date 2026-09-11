# Verificación para el Autor v74: corrección — v71–v73 no toca tu máquina

Ricardo, soy Claude (Opus 5). Me preguntaste por qué habían desaparecido los `owners` y el proceso que tu máquina hace sobre el mapa, y si el modelo se ajusta de verdad a tu algoritmo. Fui a comprobarlo al código en vez de contestarte de memoria. **Tenías razón, y el fallo es mío.** Este informe corrige v71, v72 y v73.

---

## 1. Los hechos, medidos sobre el propio repositorio

**En los tres módulos de v71–v73 no hay una sola línea de código que mencione `owners`, `gowners`, `GPathM`, `PathNodeId`, `isValid`, `filterAll`, `review` ni `ChainSound`.**

| módulo | apariciones en **código** | apariciones en **comentarios míos** |
|---|---|---|
| `CnfHypergraph.lean` | 0 | 0 |
| `CnfReducer.lean` | 0 | 3 |
| `CnfSelection.lean` | 0 | 1 |

Y **no existe ningún teorema que conecte `reduce` o `NoBacktrack` con `FlipCore` o `ClauseStepExact`.** Las cuatro apariciones son prosa mía afirmando una correspondencia que nunca demostré.

Hay un segundo hecho, y es peor que el primero: **mis tres campañas tampoco ejecutan tu máquina.** `--flipscope`, `--reducer` y `--pickstep` trabajan sobre listas de cláusulas. Las campañas de v66–v70 llaman a `pureAdvance` veinte veces; las mías, ninguna. Así que los números que te di —0 atascos de 47.663, 39 de 39, 1.368 de 1.368— describen **mi** procedimiento, no tu algoritmo.

## 2. Las frases concretas que hay que retirar

- **v71:** «la correspondencia con la máquina es término a término (filas = nodos de cláusula, semi-joins = pasadas de `review`)». **No está demostrada.** Es una analogía de forma, no una identidad de objetos.
- **v72, §1:** «la fila que el reductor conserva **es** el índice del nodo de cláusula que la máquina mantiene vivo». **Esta es la peor.** Afirma que los supervivientes coinciden, que es justo lo que no se sabe.
- **v72, apertura:** «ya no es una analogía con tu máquina, es un teorema del modelo puro». Es un teorema, sí — **de mi reductor**. Respecto de tu máquina sigue siendo una analogía.
- **v72:** «es el mismo enunciado que `ArcConsistency.review_arcConsistent` ya demuestra de las tablas de owners». Misma *forma* de enunciado, objetos distintos.
- **v73** (y el docstring de `CnfSelection.lean`): «`NoBacktrack` es lo único que queda entre este fichero y `FlipCore` para la clase». **Falso.** Falta también el puente, y el puente es lo gordo.

He corregido esas frases en los docstrings de los módulos, porque el registro que una sesión futura va a leer primero es el código, no los informes.

## 3. Por qué se me fue, dicho con precisión

`ClauseFilter.lean` (v68) dejó `FlipCore` con una forma que **se lee** como una pregunta sobre fórmulas: ¿existe una solución de lo visto que respete estos pines? Y v69–v70 añadieron el diccionario cadena↔asignación. Eso legitima **enunciar** lo que falta sin grafo. Yo lo tomé como permiso para **trabajar** sin grafo, y no es el mismo permiso: el diccionario de v70 vale para cadenas de longitud completa en el estado de su propia rama, y `FlipCore` pide una cadena de **este** estado que pase por **este** nodo.

## 4. Por qué la simplificación es tan grande

Porque mi modelo se salta lo que cuesta. Mi `initRows` son las siete filas satisfactorias de la cláusula y mi `sweep` es un semi-join puro. Los nodos que sobreviven en **tu** máquina no los decide eso: los decide la poda de `owners`, con las pasadas de coherencia de padres e hijos sobre tablas indexadas por paso y por `PathNodeId`. Que las dos cosas coincidan **es exactamente la inclusión `owners ⊆ support`**, abierta desde v11 y nombrada en `ArcConsistency.lean`. Mi modelo la da por supuesta sin decirlo. Parece más simple porque lo es: asume la mitad difícil.

## 5. La consecuencia que importa

Si cerrara `NoBacktrack` bajo `BoundedScope` al completo, tendría demostrado que **3SAT es polinómico en fórmulas α-acíclicas**: Beeri–Fagin–Maier–Yannakakis, 1983. Un teorema conocido, y mudo sobre tu algoritmo.

Dicho de otro modo, y esto es lo que hay que apuntar en el registro: **esta ruta no rodea el muro; lo vuelve a encontrar en el puente.** Y el puente tiene la forma de la misma inclusión abierta desde v11. No es que v71–v73 esté mal: es que su valor para tu proyecto está **condicionado** a un enlace que no existe todavía, y yo se lo presenté como si ya estuviera.

## 6. Lo que sigue siendo válido

Los teoremas lo son, y sus cierres son limpios — solo que hablan de otro objeto:

- `CnfHypergraph.lean`: la clase, su decidibilidad, la clausura bajo prefijos y la medida acotada. Nunca afirmó tocar la máquina; queda intacto.
- `CnfReducer.lean`: conservación, terminación y arco-consistencia **del reductor de fórmulas**.
- `CnfSelection.lean`: la mitad de Helly, la equivalencia «el reductor no pierde nada» y el caso base **del reductor de fórmulas**.
- Las mediciones: válidas sobre ese procedimiento, y solo sobre ese.

Nada de esto hay que tirarlo. Hay que dejar de contarlo como si fuera tu máquina.

## 7. Qué queda por decidir

Dos caminos, y es tuya la decisión — no la tomo yo en este informe:

1. **Medir la banda que me salté**: comparar, sobre estados reales de tu máquina, las filas que sobreviven a tu filtro de cláusula contra las que deja mi `reduce`. Es barato y es el método del propio proyecto (`MirrorTest`, `CnfMapDiff`). Si coinciden, v71–v73 gana un enlace real; si no, queda como rama lateral y así se dirá.
2. **Rehacer el reductor sobre tus estructuras** (`owners`, `filterAll`, `review` en `GPathM`), para que no haya puente que demostrar. Más caro, sin deuda oculta.

Build: `lake build AbsSat` verde, 99 módulos, 0 `sorry`, 0 axiomas de proyecto. Ningún teorema retirado: lo retirado son afirmaciones mías sobre su alcance.
