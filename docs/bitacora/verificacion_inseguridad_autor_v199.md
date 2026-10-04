# Verificación para el Autor v199: el grafo de owners (`improves_bingo`) y cinco reglas sobre aristas

Ricardo, este informe documenta la máquina nueva que montamos en la rama `graph_owners`: la misma máquina de
`improves_bin`, pero con los owners guardados en un grafo por gpath en vez de en una tabla por nodo. Al final
propongo cinco reglas que solo tienen sentido con aristas y que pueden servir de forma directa en Lean. Ninguna de las
cinco está implementada ni medida.

**La conclusión, por adelantado.**
* **Es la misma máquina.** En las 81 instancias del corpus da el mismo veredicto, las mismas soluciones del lector, el
  mismo estado final (nodos, global, tablas, padres e hijos) y el mismo número de vueltas del review que
  `improves_bin`, instancia a instancia.
* **Es más rápida:** 99,0 s frente a 40,1 s. La mayor parte de la ganancia no viene del grafo, sino de copiarlo campo a
  campo en cada UP: `improves_bin` con esa misma copia tarda 53,7 s. El grafo aporta el 25 % restante.
* **Ocupa más memoria viva:** un 35 % más en owners, como esperábamos. El diccionario de aristas es el 31 % del grafo;
  sin él, ocuparía un 7 % menos que las tablas de bin.
* **Un hallazgo:** en todo el corpus, las pasadas de padres e hijos **no cortan ninguna arista**, ni en bingo ni en bin.
  Solo eliminan nodos que se quedan sin padres o sin hijos. Puede ser un lema.
* **Siguiente:** elegir cuál de las cinco reglas de la §6 se implementa primero. Mi propuesta es la 1 (apoyo contado).

---

## 1. La idea

Cada nodo guardaba sus owners por pasos: con quién es compatible. Esa relación ya era simétrica (`SYM_MODE = :on`
escribía el espejo), así que en realidad era un grafo guardado dos veces y repartido por los nodos. La propuesta fue
sacarla a una estructura propia del gpath, `PathOwnersGraph.OwnersGraph`, con tres partes:

| campo | qué es | antes |
|---|---|---|
| `alive` | los nodos vivos, por paso | `gpath.owners` (la global) |
| `edges` | cada compatibilidad, una sola vez (`Edge`, con clave ordenada) | — |
| `inc` | los vecinos de cada nodo, por paso | `node.owners` (la tabla) |

La relación es simétrica por construcción (borrar una arista la quita de los dos lados) y reflexiva de forma
implícita (cada nodo se posee a sí mismo, sin objeto `Edge`).

Te avisé de entrada de dos cosas: que no iba a ahorrar memoria, porque la incidencia sigue guardando los dos sentidos
y las aristas se suman encima, y que la ganancia esperable era de tiempo y, sobre todo, de formalización.

## 2. Qué se hizo

Todo está en `julia/improves_bingo`, una copia de `improves_bin` en `0e2af47`. `improves_bin` no se tocó: es la
referencia del diferencial. El plan, con cada fase y sus resultados, está en `docs/plans/graph_owners.md`.

| fase | commit | qué |
|---|---|---|
| F0 | `1c93bd8`, `f63ce6a` | copia, borrador del módulo y plan |
| — | `3d3e829` | se quitan de bingo los filtros fuera del review (`agresive`, `witness`, `chain`, `triangle`) y las sondas |
| F1 | `23b41cd` | el grafo solo, con `check_invariants` y 267 tests (200 secuencias al azar contra un modelo de pares) |
| F2 | `0f9155d` | `GPath` sobre el grafo; `PathDocNode` sin owners |
| F3 | `f2421cf` | consultas (`is_owner`, `owners_table`, …) y tests adaptados; todo en verde |
| F4 | `36bf3df` | diferencial del estado final contra `improves_bin` |
| F5 | `87453da` | medida de tiempo y memoria |

## 3. Cómo quedó la máquina

| antes (`improves_bin`) | ahora (`improves_bingo`) |
|---|---|
| `create_node_from_parents!` + `its_owners_are_owned_by_me!` | `create_from_parents!`: vecinos de los padres, vivos y de pasos anteriores |
| `filter_require!` quita de la global | `remove_node!`: el nodo sale con todas sus aristas |
| `clean` en dos fases (purga + corte con la global) | una sola fase: al morir un nodo ya no queda rastro suyo |
| pasadas: `deepcopy` + `union!` de tablas + corte + espejo | `cut_by_support!`: se pregunta arista a arista, sin copiar |
| regla de parejas por nodos y tablas | por aristas, cada una una vez |
| enlace caducado: cada extremo posee al otro | `has_edge` |
| join: unión de tablas | `union!` de los dos grafos |

Desaparecen `PathDocumentOwners`, el espejo, `SYM_MODE`, `CLEAN_MODE` y la fase 2 de la limpieza.

**Dos detalles que salieron por el camino:**
* **Hermanos.** Al portar el UP vi que, si dos hijos comparten padre, el segundo recibía al primero como vecino a
  través de la tabla del padre. En la máquina de siempre eso no pasa, porque se creaban todos los nodos de la fila
  antes de registrar ninguno. Ahora `create_from_parents!` solo enlaza con pasos anteriores; hay un test para ello.
* **El desfase de ids muertos.** En bin, un nodo eliminado seguía en las tablas de los demás hasta la siguiente
  limpieza. En bingo desaparece al instante. Temía que eso cambiara la traza del review, pero no la cambia: las
  vueltas coinciden instancia a instancia.

## 4. Resultados

### 4.1 Equivalencia (F4)

Cada máquina vuelca su estado final en forma canónica (`test_3sat/dump_final.jl`) y un script compara los dos
volcados (`test_3sat/compare_bingo.jl`).

| | resultado |
|---|---|
| instancias comparadas | 81 (`simple_v3_c2.cnf` no es 3-SAT; da error en las dos) |
| mismo veredicto | 81/81 (y todos iguales al solver exhaustivo) |
| mismas soluciones del lector | 81/81 |
| mismo estado final | 81/81 |
| mismas vueltas del review | 81/81 |
| volumen comparado | 66 gpaths, 5.897 nodos, 265.303 entradas de owners |

Para ver que la comparación no es trivial, quité a mano una sola entrada de owners en una copia del volcado, y el
comparador la detectó. **Alcance:** se compara la última línea de la máquina, no cada paso intermedio; que las vueltas
coincidan sugiere que la traza también coincide, pero no lo he comprobado paso a paso. Las 15 instancias UNSAT terminan
sin gpaths, así que en ellas solo cuentan el veredicto y las vueltas.

### 4.2 Tiempo y memoria (F5)

`test_3sat/measure_bingo.jl`, cada máquina en su proceso. La columna «bin + copia» es `improves_bin` con la misma
copia campo a campo que usa bingo, inyectada desde el script sin tocar sus fuentes.

| 81 instancias | bin | bin + copia | bingo |
|---|---|---|---|
| tiempo (s) | 99,0 | 53,7 | 40,1 |
| memoria reservada en total (GB) | 274,2 | 163,0 | 148,2 |
| GC (s) | 16,0 | 8,7 | 8,8 |
| pico vivo de la línea, suma (MB) | 812,3 | 818,1 | 1.075,4 |
| pico vivo de la línea, máximo (MB) | 134,8 | 136,9 | 178,9 |
| pico de owners, suma (MB) | 735,6 | 741,4 | 997,7 |

Cómo leerlo:
* **El 77 % del tiempo era el `deepcopy` del gpath en cada UP** (`sat_machine.jl:110`); el review era un 13 %. La
  primera versión de bingo, con el `deepcopy` genérico, era un 20 % *más lenta* que bin. Copiar por estructura lo
  arregló, y es una mejora que bin también podría adoptar.
* **Descontada la copia, el grafo gana un 25 %** (53,7 → 40,1 s) porque el review ya no copia ni une tablas.
* **Memoria:** +35 % en owners. El diccionario de aristas son 308,6 MB de 997,7. Sin él (grafo = `alive` + `inc`),
  serían unos 689 MB, un 7 % menos que bin.

### 4.3 Qué quita cada regla

| regla | aristas quitadas |
|---|---|
| `clean` (muerte de nodos en la purga) | 5.090.266 |
| `require` (nodos descartados al fijar un requisito) | 4.484.763 |
| `pair` (regla de parejas) | 117.558 |
| `parents`, `sons` (pasadas) | **0** |

En bin pasa lo mismo: su contador del espejo de las pasadas da 0 (comprobado en `rand3sat_v8_c10` y `v6_c26_i1`), y
sus parejas son 880 frente a 440, porque bin cuenta cada pareja en los dos sentidos.

**No es un fallo.** Las pasadas siguen haciendo su trabajo de eliminar nodos sin padres o sin hijos; lo que nunca
hacen, en este corpus, es cortar una tabla. Mi explicación, sin demostrar:
* en el UP, la tabla de cada nodo nace como la unión de las de sus padres, así que toda arista nace con apoyo;
* después, una arista solo desaparece si muere uno de sus extremos (y entonces se van todas las suyas) o por la regla
  de parejas;
* parece que eso nunca deja una arista sin apoyo. La regla de parejas podría hacerlo en teoría; aquí no ha ocurrido,
  pero no está garantizado.

Si se demuestra, el review se simplifica: las pasadas se reducen a comprobar padres e hijos. La regla 1 de la §6 es
la herramienta natural para demostrarlo.

## 5. Qué da esto para Lean

El modelo Lean guarda hoy los owners por nodo (`PNodeM.owners : List`), como la Julia de antes. Con una relación E
simétrica:
1. **La simetría pasa a estar en el tipo** (por ejemplo, pares no ordenados `Sym2`): sobran los lemas del espejo, y
   todo razonamiento «x posee a w y w posee a x» se reduce a un caso.
2. **Cada regla del review es un operador que solo borra**. Basta un lema por regla («conserva las aristas de las
   soluciones»); la independencia del orden y el punto fijo salen de la teoría general, sin demostrarlos para cada
   modo (`clean` en dos fases, `pairSweep`…).
3. **Julia y Lean hablarían de lo mismo**: bingo ya no copia ni corta tablas, solo borra aristas.
4. **El puente es plausible.** Que las vueltas coincidan una a una apunta a que, en los estados alcanzables, cada
   tabla es exactamente el vecindario de una relación simétrica: `tabla(x) = {w | E x w}`. Con ese lema, lo ya
   demostrado (KFix, M1, la escalera del lector) se transportaría sin rehacerlo.

## 6. Cinco reglas que usan aristas

Todas se apoyan en el mismo invariante, que es la base de «no se pierde ninguna solución»: **las aristas de una
solución nunca se borran**. Una solución es un camino con un nodo por paso, en el que cada par de nodos tiene arista.
Así que cada regla pide un único lema en Lean: si la regla borra (x,w), ninguna solución pasa por x y w a la vez.

Van ordenadas por lo directo que es su paso a Lean.

### 6.1 Apoyo contado

* **Datos en `Edge`:** cuatro contadores. `par_a` = cuántos padres de a tienen arista con b; `son_a` = cuántos hijos
  de a la tienen; y `par_b`, `son_b` al revés.
* **Regla:** si un contador llega a 0 y ese extremo tiene padres (o hijos), la arista muere. Al morir (p,w), se restan
  los contadores de las aristas (s,w) de los hijos y los padres de p, y se sigue con una cola de trabajo, sin vueltas
  completas (el esquema de AC-4 en satisfacción de restricciones).
* **Por qué es correcta:** en una solución que pasa por a y b, el padre de a en esa solución también está en ella, así
  que tiene arista con b.
* **Lean:** el corte de las pasadas se convierte en un invariante local, `Supported E`: toda arista tiene apoyo por los
  cuatro lados. Es justo lo que hace falta para el lema de la §4.3: basta demostrar que la limpieza y la regla de
  parejas conservan `Supported`, o encontrar el caso que no lo conserva.
* **Coste:** cuatro enteros por arista; cada muerte cuesta O(grado · padres).

### 6.2 Testigo por paso

* **Datos:** `wit[k]`, un nodo del paso k con arista a x y a w.
* **Regla:** es la regla de parejas de hoy (`shares_every_step`), pero con certificado: solo se vuelve a comprobar el
  paso k cuando muere el testigo guardado, o pierde una de sus dos aristas (la idea de AC-2001).
* **Por qué es correcta:** la misma que la regla de parejas; el nodo de la solución en el paso k es un testigo.
* **Lean:** `PairOk` deja de ser un `∀ k, ∃ z` que se reconstruye en cada demostración y pasa a ser una función
  guardada, y los lemas sobre ella son locales: si el testigo sigue vivo y conserva sus aristas, la arista sigue
  cumpliendo la regla. Encaja con la forma de `KFix` (cada enlace tiene, en cada paso, un testigo enlazado con los dos
  extremos).
* **Coste:** un id por paso y arista, S veces más memoria en aristas que hoy. Es la más pesada en memoria de las cinco.

### 6.3 Coherencia de ventana

* **Datos:** ninguno nuevo; la regla usa solo los ids.
* **Regla:** si x (paso i) y w (paso j) están a menos de `WINDOW` pasos, sus ids tienen que coincidir en los ids de mapa
  que comparten. Con ventana 3 y x, w como `PathNodeId`: si j = i+1, `w.parent_id == x.id` y
  `w.gparent_id == x.parent_id`; si j = i+2, `w.gparent_id == x.id`. Además, entre pasos consecutivos, arista sin enlace padre–hijo muere.
* **Por qué es correcta:** en una solución, los nodos cercanos se solapan en su ventana, y los consecutivos están
  enlazados (un enlace solo se quita cuando ninguna solución lo usa).
* **Lean:** es decidible solo con los ids, y da un lema estructural: **una camarilla que toca cada paso y respeta las
  ventanas es un camino**. Es un puente directo entre «conjunto de nodos compatibles» y «camino», que es lo que pide
  el enfoque de subconjuntos de caminos parciales.
* **Coste:** casi nulo. Puede que no corte nada, porque las aristas nacen de los enlaces; incluso así, el invariante sirve.

### 6.4 Camino común

* **Datos:** un bit y, si se quiere, el camino testigo.
* **Regla:** la arista (x,w) sobrevive si, usando solo nodos con arista a x y a w, hay un camino de enlaces desde la
  raíz hasta la cima. Se calcula paso a paso:

  ```
  R = raíces con arista a x y a w
  para k = 1 .. cima:   R = hijos(R) ∩ N_k(x) ∩ N_k(w)
  sobrevive ⇔ R ≠ ∅
  ```

  En el paso de x, el único vecino de x es x mismo, así que el camino pasa forzosamente por x y por w.
* **Por qué es correcta:** el camino de la solución es ese camino.
* **Lean:** es exactamente una **prueba de vacío sobre el subconjunto de caminos compatibles con el par (x,w)**, el
  punto abierto del enfoque de subconjuntos. Engloba la regla de parejas y la del segmento de la que hablamos. Su
  límite es que solo mira pares: garantiza un camino compatible con x y con w, no uno compatible con tres nodos a la vez.
* **Coste:** O(S · 7²) por arista, en palabras si algún día se pasa a máscaras de bits.

### 6.5 Testigos que se conocen entre sí

* **Datos:** los testigos de la 6.2.
* **Regla:** para una arista (x,w) y dos pasos k y l, tiene que haber testigos z_k y z_l que además tengan arista
  entre ellos: un K4 alrededor de la arista.
* **Por qué es correcta:** los nodos de la solución en los pasos k y l son esos testigos, y tienen arista entre sí.
* **Lean:** es un paso hacia «la arista se extiende a una camarilla completa», la propiedad semántica que falta en la
  escalera. Su lema mide cuánto del hueco de Helly se cierra con cuatro nodos en vez de tres.
* **Coste:** O(S² · 7⁴) por arista. La más cara.

### 6.6 Cómo se relacionan

* La 6.4 implica la regla de parejas y la del segmento; la 6.2 es la regla de parejas con certificado.
* La 6.5 es independiente de la 6.4: una pide un camino de testigos, la otra que los testigos se conozcan entre sí.
  Juntas se acercan a «la arista está en una solución».
* La 6.1 y la 6.3 son invariantes de estructura más que filtros nuevos: probablemente corten poco, y lo que dan es
  un lema.

**Mi propuesta es empezar por la 6.1**: responde a lo que vimos en las medidas (§4.3), da el lema más limpio y exige
que las aristas guarden datos. Esto último zanja la otra decisión pendiente: si los `Edge` pasan a ser perezosos para
recuperar memoria (el grafo quedaría en `alive` + `inc`), no hay dónde guardar los contadores.

## 7. Decisiones pendientes

1. **Qué regla se implementa primero** (propuesta: 6.1), cada una detrás de un interruptor, medida con
   `REMOVED_BY` y comparada con `compare_bingo.jl`.
2. **`Edge` perezosos o no.** Si se implementa la 6.1 o la 6.2, no: las aristas llevan datos. Si no, pasar a
   `alive` + `inc` recupera un 31 % de memoria.
3. **Llevar la copia por estructura a `improves_bin`** (y al modelo de medida de la máquina de siempre): es la mitad
   larga de la ganancia de tiempo y no cambia nada de la semántica.

---

**Commits:** `1c93bd8`, `f63ce6a`, `3d3e829`, `23b41cd`, `0f9155d`, `f2421cf`, `36bf3df` y `87453da`, en la rama
`graph_owners`. Plan: `docs/plans/graph_owners.md`.
