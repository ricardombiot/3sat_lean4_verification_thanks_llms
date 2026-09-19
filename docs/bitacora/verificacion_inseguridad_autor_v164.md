# Verificación para el Autor v164: exactitud, trazas dirigidas, el testigo con cierre y el lector

Ricardo, soy Claude (Opus 5). Este informe recoge todo lo hecho desde v163, que fue el último informe
escrito. Rama `spaik`, build de `AbsSat` (230 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`. Los
casos y los scripts de las trazas están en `lean_project/Probes/cases_v164/`.

## 0. Resumen

* **La parte de la máquina está cerrada.** La unión es exacta (su tabla es exactamente la de pares de
  sus caminos reales). La muerte directa y la elección del lado por su cima están demostradas.
* **El veredicto depende ya de una sola propiedad de los caminos reales**, sin tablas ni review. La
  primera versión (`SemWitnessAt`, testigo de un nivel) es **falsa**: lo muestra un caso construido,
  comprobado por fuerza bruta. La versión con cierre (`ClosedWitnessAt`) se cumple en ese caso, igual
  que la máquina.
* **La máquina elimina el trío en todos los casos trazados**, también en el construido. En ese caso el
  review base no basta y lo elimina la revisión agresiva hasta su punto fijo.
* **El lector sin retroceso ya es un programa.** Su respuesta positiva es correcta sin ninguna
  hipótesis. Solo queda abierto que nunca se atasque.
* **Julia.** La regla 1 del triángulo, como regla de borrado, era incorrecta y la retiré. Tu
  integración de `filter_triangle_nodes!` es correcta y no cambia veredictos. Quedan dos detalles en
  `PathDocumentOwners`.

## 1. La unión es exacta (`union_complete`, `union_rel_iff`)

En una unión por clave ya exacta, x→v es una relación **si y solo si** existe un camino real que llega
a la clave, respeta los fijados y pasa por x y por v. La tabla de la unión es exactamente la tabla de
pares de sus caminos: no sobra nada (exactitud) y no falta nada (completitud).

Consecuencia: la inducción sobre la línea no cierra el trío por sí sola. Cada unión mezcla estados de
claves distintas que nunca estuvieron juntos en la línea anterior, y lo que da la inducción es por
estado.

## 2. Trazas dirigidas

Modos nuevos de sonda: `splittracef` (traza sobre un fichero DIMACS), `commonat` (nodos comunes de
x y v en un paso) y `rule1`.

### 2.1 Una incoherencia lejana (`cadena_lejana.cnf`)

Cadena `(x0 ∨ ¬x1 ∨ x3)`, `x3 → x4`, `x4 → ¬x2`. El trío x0=0, x1=1, x2=1 es imposible, pero cada par
es posible. Tomamos x = `3.0<2.1` (x1=1), v = `1.1<0.0` (x0=0) y fijamos r = `5.0` (x2=1).

En la unión, la única fila común a x y v en el paso de la primera cláusula es `13.1<12.0`
(x0=0, x1=1, x3=1), y **ya no es dueña de x2=1**. La cadena x3 → x4 → ¬x2 está guardada en la tabla de
pares, porque la unión es exacta. Al fijar, x→v muere de forma directa. Una incoherencia lejana llega al
review convertida en una cercana.

### 2.2 Contradicciones de elección

x = A=1 obliga a elegir una s, v = B obliga a elegir una t, y las cláusulas cruzadas
`(¬sᵢ ∨ ¬tⱼ ∨ ¬C)` impiden C=1. Cada fila por separado es compatible con los tres extremos.

| versión | órdenes trazados | x→v tras fijar | lado que lo conserva | cómo muere |
|---|---|---|---|---|
| 2 opciones | 12 | eliminado | ninguno | directa, fila + fila anterior |
| 3 opciones (con aux) | 6 | eliminado | ninguno | directa, pasos de cláusula |
| 4 opciones (con aux) | 5 | eliminado | ninguno | directa, pasos de cláusula |

**w4, paso 36** (fila de `(¬A ∨ s1 ∨ y1)`, fila padre `(¬s1 ∨ ¬t2 ∨ ¬C)`). Los seis nodos comunes a x y
v tienen C=0. El nodo fija s1 e y1, que es el **resumen** de la elección de A entre las otras opciones,
y además fija C. Con C=1 no hay nodo común posible. En w4 el orden de las cláusulas pone ese resumen
junto a C; el mecanismo depende del orden.

## 3. El testigo semántico (`SemWitnessAt`)

* `Compat P m p a b`: un camino real de la unión pasa por a y por b.
* **`SemWitnessAt`**: si x y v son compatibles y en cada paso hay un nodo compatible con x, con v y con
  un nodo de r, entonces un camino real pasa por los tres.
* `compat_of_rel`, `rowWitness_of_sem` y `sat_of_semWitness`: el veredicto bajo `SemWitnessAt`.
* `compat_pin_eq`, `semWitness_of_far` y `sat_of_semWitnessFar`: si x o v fija la variable de r, el
  testigo se cumple solo.

## 4. El caso construido: `SemWitnessAt` es falso (`construido.cnf`)

Hay tres grupos de cláusulas:

* **grupo de A:** A=1 obliga a alguna de s1…s4 (cadena y1, y2);
* **grupo de B:** B=1 obliga a todas las t a 0;
* **grupo de C:** C=1 obliga a sᵢ → tᵢ.

Los grupos van separados por cláusulas neutras, y A, B y C están separadas en el orden de variables, así
que ninguna ventana (nodo) mezcla dos grupos.

**Fuerza bruta** (23 variables, 1.338.288 soluciones): el trío no tiene solución, los tres pares sí, y
**todos los pasos** tienen un nodo compatible con x, v y r. `SemWitnessAt` falla en este caso.

**La máquina** (cima 64, x = A=1, v = B=1, fijando C=1):

| etapa | x→v |
|---|---|
| unión | sí |
| solo fijar | sí |
| fijar + review base | **sí** (no hay muerte directa) |
| fijar + review agresivo | **eliminada**: al final x y v no comparten nodo en ningún paso |

La máquina tiene un recurso que el testigo de un nivel no recogía: **el punto fijo de la revisión
agresiva**. En él, cada relación que queda tiene nodos comunes que también quedan, de forma encadenada.

## 5. El testigo con cierre (`ClosedWitnessAt`)

* **`ClosedAt`**: una familia R de pares que cumple cuatro condiciones. Sus pares son compatibles, es
  simétrica, es **cerrada** (cada par tiene en cada paso un nodo común *dentro de R*) y en el paso de r
  solo alcanza nodos de r.
* **`ClosedWitnessAt`**: todo par de una familia cerrada está en un solo camino real que pasa por r.
* **`sideKeep_of_closed`**: la relación de la unión fijada tras el review agresivo es una familia
  cerrada (por la exactitud, el punto fijo y el pin).
* **`sat_of_closedWitness`**: el veredicto bajo `ClosedWitnessAt`.

**Fuerza bruta** (`familia_cerrada.py`, versión reducida del caso construido, 17 variables, 23.898
soluciones): el testigo de un nivel vuelve a fallar, pero **la mayor familia cerrada no contiene x→v**
(se estabiliza en 4 rondas). Es la primera hipótesis que resiste este caso.

`ClosedAt` deja fuera las reglas de enlaces padre/hijo que la máquina sí usa. Si aparece un caso que el
cierre solo no atrapa, se pueden añadir.

## 6. El lector sin retroceso (`ReaderExec.lean`)

Sobre tu pregunta de si "tomar prestado" es un problema: para la **corrección** no lo es. Ya estaba
demostrado sin hipótesis (`certifiedVerdict_iff_oracle`) que, leída con un certificado comprobado, la
máquina nunca da una respuesta errónea. Tomar prestado solo afecta al **coste de leer** la solución.

Ahora el lector es un programa:

* `readLoop` / `readAgg`: en cada ronda toma el primer paso que aún tiene elección y fija el primer
  nodo que el review agresivo deja válido. **Nunca deshace un fijado**. Cada ronda cuesta como mucho
  un review por nodo del paso, y las rondas están acotadas por `measure`.
* **`readerVerdictW_sound`**, sin hipótesis: si el lector termina en algún estado de la última línea,
  la fórmula es satisfacible.
* `readerVerdictW_complete`: termina siempre que nunca se atasca (`ProgressAgg`).

## 7. Julia

* **Regla 1 (triángulo).** Tu revisión agresiva es consistencia de **pares**: en los estados revisados,
  176 de 5 millones de tríos de dueños mutuos no tienen nodo común. Pero la regla 1, como regla de
  borrado, perdería soluciones (el trío de v161 tiene los tres pares válidos), así que la retiré. Solo
  es correcta con el tercer nodo fijado, y en ese caso la máquina ya la cumple (`pinned_common`).
* **Tu integración** (`d71f908`, `filter_triangle_nodes!`) es correcta y no pierde soluciones. Pero
  no cambia ningún veredicto del modelo: solo detecta antes lo que el review detecta después. La
  corrección de `union!` (`max_step`, `empty_steps`) está bien aplicada. Quedan dos detalles:
  1. `intersect!` borra del `Set` mientras lo recorre (falta `collect(...)`);
  2. `intersect!` marca `valid = false` si `owners_b.max_step > owners_a.max_step`. Con nodos de
     `max_step` distinto, eso podría invalidar un grafo sin motivo.
* **Reglas 2 y 3** (código Julia en la conversación, no ejecutado):
  * **Regla 2 (testigo enlazado):** no pierde soluciones y exige una misma cadena para x y w, pero no
    garantiza que los nodos de la cadena sean compatibles entre sí.
  * **Regla 3 (prueba por fijación):** es correcta, pero cuesta pares × review.

## 8. Estado de la cadena del veredicto

| hipótesis | estado | reduce a |
|---|---|---|
| `SideKeepAt` | hipótesis | — |
| `RowWitnessAt` | hipótesis | `SideKeepAt` (`sideKeep_of_row`) |
| `TopSideAt` ∧ `TopKeepAt` | hipótesis, 0 fallos medidos | `SideKeepAt` (`sideKeep_of_top`) |
| `SemWitnessAt` | **falsa** (caso construido) | `RowWitnessAt` (`rowWitness_of_sem`) |
| `SemWitnessFarAt` | falsa (el mismo caso: x y v no fijan C) | `SemWitnessAt` (`semWitness_of_far`) |
| **`ClosedWitnessAt`** | **hipótesis vigente**, resiste el caso | `SideKeepAt` (`sideKeep_of_closed`) |
| `ProgressAgg` | hipótesis (el lector no se atasca) | `readerVerdictW_complete` |

Las reducciones siguen siendo correctas aunque una hipótesis sea falsa: solo quiere decir que esa
hipótesis no sirve como punto de llegada.

## 9. Lo que queda

1. **`ClosedWitnessAt`**: pasar de una familia cerrada de pares compatibles a un solo camino. Es el
   núcleo, y ya no habla de la máquina.
2. La traza del caso construido **por lados** (qué lado conserva cada par) seguía en marcha al
   escribir este informe.
3. Si el cierre no bastara en algún caso, añadir a `ClosedAt` las reglas de enlaces padre/hijo.

## 10. Reproducir

Desde `lean_project/`:

```bash
lake build helly
./.lake/build/bin/helly splittracef Probes/cases_v164/construido.cnf 64 64 0 1 0 0 1 5 0 4 1 9 0
python3 Probes/cases_v164/fuerza_bruta_ventanas.py Probes/cases_v164/construido.cnf
python3 Probes/cases_v164/familia_cerrada.py
```

Commits de esta etapa: `205b2de` (exactitud de la unión), `5901c0a` (`splittracef`), `5e7f450`
(testigo semántico), `d1d3f31` (extremos que fijan), `5c166b9` (lector), `e185644` (testigo con
cierre). Tu `d71f908` (reglas Julia).
