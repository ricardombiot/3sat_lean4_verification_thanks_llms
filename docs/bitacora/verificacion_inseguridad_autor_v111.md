# Verificación para el Autor v111: fantasmas en el tope y la obligación llevada al estado final

Ricardo, soy Claude (Opus 5). Este tramo parte de la refutación de v108 y de una pregunta tuya:
¿importan los fantasmas si la lectura se puede hacer sin backtracking? La respuesta medida es que casi
nunca llegan a donde se lee, pero uno sí lo hizo, y ese basta para refutar la hipótesis de la que
colgaba la solidez. El resultado es una obligación nueva, más débil y sostenida por los datos, que
solo pide algo al estado final.

Todo en la rama `spaik`, en el build de `AbsSat` (158 módulos), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. Qué es un fantasma y por qué no se arregla con la tabla

Un **fantasma** es una selección que cumple todas las condiciones por parejas (nodos, enlaces, owners
globales, propiedad mutua) pero no es parte de ninguna cadena completa. Las tablas de owners son la
proyección por parejas del conjunto de cadenas, y reconstruir "hay una cadena que los recorre a todos"
a partir de pares es justo lo que Helly no garantiza.

Antes de este informe medí los 73 fallos de `SideCovered` de v108 contra la tabla ideal (pares que
co-ocurren en algún camino enlazado consistente): **73 de 73 usan solo pares ideales, y en ninguno el
candidato bloqueado co-ocurre con su bloqueador**. La tabla no sobra ni falta: ya es la ideal, y el
fallo persiste. Por eso ningún invariante sobre la tabla de owners, incluido el `I` de las tablas
ideales, puede eliminar estos fantasmas. La máquina es exacta; lo que tenía la forma equivocada era el
enunciado.

## 2. Solo cuentan los del tope (`TopPhantom`)

Un lector sin backtracking parte del paso superior y baja eligiendo en cada paso un pick compatible con
todo lo elegido. Lo que lleva elegido está siempre anclado al tope, así que solo puede atascarse en un
fantasma anclado al tope del estado que lee.

- `TopPhantom g sel lo` y su forma positiva `NoTopPhantom g`: todo segmento del tope tiene una cadena
  completa que lo contiene.
- **`noDeadEnd_iff_noTopPhantom`**: leer sin backtracking nunca se atasca ⟺ no hay fantasmas en el
  tope.

## 3. Cuántos hay donde se lee

El modo `top` de la sonda (`lake exe join-borrow top`) recorre el árbol completo del lector en cada
estado filtrado, en cada estado de línea y en los finales, y lanza cinco lectores por nodo del tope.

| | estados | segmentos del tope | fantasmas en el tope | lectores atascados |
|---|---|---|---|---|
| 6–8 variables, seed 31337 | 4.425 | 382.494 | 1 segmento (en 3 estados) | 0 |
| 6–8 variables, seed 90210 | 4.137 | 377.024 | 0 | 0 |
| 8–10 variables, seed 1001 | 5.519 | 1.190.278 | 0 | 0 |
| 8–10 variables, seed 7777 | 6.288 | 1.762.083 | 0 | 0 |
| **total** | **20.369** | **3,71 M** | **1** | **0 de 188.775** |

Ningún árbol se truncó. Ningún estado quedó sin pick en el tope. **Ningún estado final tiene
fantasmas.**

## 4. El único, y lo que refuta

Está guardado en `lean_project/Probes/cnf/top_phantom_s31337_4.cnf` (8 variables, 31 cláusulas; la
sonda lo reproduce en 1,4 s). Es un segmento de los pasos 25 a 29 en el estado filtrado que se envía a
la clave `(30,3)`. Aparece en el estado de línea, sobrevive al filtro, lo corona el `addNode`
siguiente, y el filtro posterior lo elimina.

- **Cumple las hipótesis de `FilterNoDeadEnd`**: el estado de origen es válido y tiene 8 cadenas
  completas, `d.step = current_step`, `d` está en el mapa, el filtrado es válido, y `MapReachable` se
  cumple por construcción. Aun así tiene un callejón en el tope. Así que **`FilterNoDeadEnd` es falsa
  para esa fórmula**, y la ruta `SendExact_of_FilterNoDeadEnd` pide algo falso.
- **Es Helly puro**: los cinco picks están en caminos consistentes, los 20 pares son ideales, y los dos
  candidatos del paso 24 están bloqueados cada uno por un pick distinto sin co-ocurrir con él. Todo
  nodo, entrada y enlace del fantasma pertenece a alguna cadena real, así que **ninguna regla correcta
  del review puede quitarlo**: cualquier cosa que borre rompería una cadena real.

Por eso no añadí reglas. El review no destruye cadenas reales (`ChainSound_review`), y este fantasma no
se puede quitar sin hacerlo.

## 5. La obligación nueva: solo el estado final (`FinalReadable`)

La solidez del veredicto solo necesita que un estado de la línea final contenga una cadena completa.
`SendExact` lo garantizaba exigiéndolo en todos los envíos, y eso es lo que el contraejemplo rompe.

- **`topAnchor_valid`** (demostrado): todo estado válido que construye la máquina tiene un pick en el
  tope. Es inducción sobre `MapReachable`: tras `up`, el nodo recién añadido sirve (es owner global y
  se posee a sí mismo, porque `addNode` lo hace owner de todos; `MachineOk` da la forma de raíz), y un
  `join` hace crecer su lado izquierdo, que es válido, y crecer conserva el pick.
- **`FinalReadable φ`**: ningún estado de la línea final tiene fantasmas en el tope. Nada más.
- **`final_nonempty`**, **`soundness_of_FinalReadable`** y **`run_pure_decides_of_FinalReadable`**:
  con esa obligación, todo estado final contiene una cadena completa y la máquina decide 3SAT (la
  completitud ya era incondicional).

La diferencia con lo anterior es que no pide nada a los estados intermedios: los fantasmas pueden
aparecer y morir durante la ejecución, como hizo el de la sección 4. Y el ancla del tope, que al
principio metí dentro de la obligación, ya está demostrada, así que la obligación queda reducida a
`NoTopPhantom` en el estado final.

## 6. Lo que queda abierto

- **`FinalReadable φ` para toda φ bien formada.** Es la única obligación de la solidez por esta ruta,
  y lo medido la acompaña: 0 fantasmas en el tope de los estados finales.
- Por qué los fantasmas mueren antes de la última línea. En el caso encontrado lo hace el filtro
  siguiente. Entender qué propiedad del final lo garantiza es el siguiente trabajo.
- `FilterNoDeadEnd`, `SendExact_of_FilterNoDeadEnd` y la inducción `DescendAll` siguen en el código
  como resultados condicionales correctos, pero su hipótesis es falsa en general y no deben usarse como
  ruta.
