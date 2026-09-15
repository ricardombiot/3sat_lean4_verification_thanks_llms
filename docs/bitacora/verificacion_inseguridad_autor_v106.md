# Verificación para el Autor v106: la poda por pines y la separación del trabajo del review

Ricardo, soy Claude (Opus 5). v105 dejó el filtro débil demostrado y medido, y una pregunta tuya: ¿se puede demostrar que
el review solo trabaja en lo que no se ve de dos en dos? Tal como estaba, no: el filtro débil solo toca los owners
globales, y casi todo el trabajo del review está en las tablas de owners de los nodos. Este tramo añade una poda que
actúa también sobre esas tablas, la mide y demuestra la separación.

Todo en la rama `spaik`, en el build de `AbsSat` (`lake build AbsSat` verde), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. La poda por pines

`FixAgree_reachable` ya decía que un nodo y sus owners nunca fijan una variable a valores distintos: las tablas no tienen
conflictos de dos en dos propios. El único conflicto de dos en dos que trae un envío es con los **pines** del nodo nuevo
`d`. `PureDriverPins.pinPrune` quita, antes de los requires duros y del review, todo lo cuyo id contradice un pin de `d`
(`IdContradicts`: el nodo de mapa del id, el de su padre y los dos pasos de cada variable):

1. los owners globales;
2. los nodos, con los enlaces que apuntan a ellos;
3. las entradas de las tablas de owners de los nodos que quedan.

## 2. Lo medido

`improves-diff` compara ahora tres máquinas (base, débil, débil + pines) en 26 ejecuciones aleatorias (5×40, 6×24,
7×30 y 8×34 en cuatro órdenes):

| Medida | Resultado |
|---|---|
| veredicto, última línea y resultado de cada review | idénticos en las tres, y veredicto igual al de la fuerza bruta |
| lo que elimina el review tras la poda | 0,1–8 % de lo que eliminaba el review base (la cascada) |
| lo que elimina la poda | casi lo mismo que eliminaba el review base: el trabajo se traslada |
| pasadas del review | −31 a −39 % |
| tiempo total, estados grandes (orden original, frecuencia, voraz) | −9 a −41 % |
| tiempo total, estados pequeños (5×40, y `minfront` en 8×34) | +3 a +35 % |

Lo más rápido sigue siendo `minfront` sin poda. La poda interesa sobre todo por lo que permite demostrar.

## 3. Lo demostrado (`SeparationPins`)

En cada envío de la máquina de referencia (estado alcanzable, destino en el paso siguiente, filtro válido):

- **Nada de dos en dos llega al review** (`noPinConflict_review_start`, `noPinConflict_of_pruned`). En el estado del que
  parte el review mejorado, y en todo estado recortado a partir de él —cada estado por el que pasa el review y su
  resultado—, ningún owner global, nodo ni entrada de tabla contradice un pin de `d`.
- **La poda solo hace trabajo del review** (`review_gowners_survive_pins`, `review_node_not_idContradicts`). El review
  base no conserva ningún owner global ni nodo que la poda quite, ni ninguna entrada de tabla dentro del rango de pasos
  que contradiga un pin.

Por tanto, **lo que el review mejorado todavía elimina nunca es un conflicto directo con un pin: es la cascada**.

La segunda parte reutiliza lo que ya había: un owner que contradice un pin está en el cierre de eliminación
(`IdDiesProof.idDies`) y el review elimina el cierre (`RemovalClosure.unsupported_removed`). Para pasar de owners
globales a nodos y tablas bastan dos hechos del punto fijo del review: un nodo que sobrevive se posee a sí mismo
(`SelfOwn.OOS`) y sus owners son owners globales (`Candidates.owner_mem_gowners`).

## 4. Lo que queda

| Pieza | Estado |
|---|---|
| nada de dos en dos con los pines llega al review | demostrado |
| la poda solo quita lo que quitaría el review | demostrado (owners globales, nodos, entradas en rango) |
| los dos reviews acaban en el mismo estado | medido en todas las ejecuciones, sin prueba |
| cuánta cascada queda | medido (0,1–8 %), sin cota |
| la máquina con poda no pierde soluciones | pendiente: la poda es un recorte (`pruned_pinPrune`); falta que la cadena de una solución nunca contradiga los pines |
| velocidad de la poda | recorre todo el estado; un índice por variable evitaría ese coste |
