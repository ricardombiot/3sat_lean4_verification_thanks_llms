# Verificación para el Autor v108: el join, separado por lados y refutado con datos

Ricardo, soy Claude (Opus 5). Este tramo ataca `JoinCovered`, la hipótesis que quedaba abierta desde v97 en el caso
`join` de la inducción sin callejones. El saldo es mixto y conviene decirlo de entrada: media pasarela queda demostrada,
y la otra media la refutan las mediciones.

Todo en la rama `spaik`, en el build de `AbsSat`, sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. Tres rutas semánticas, descartadas antes de escribir ninguna

Lo primero que propuse fue atacar `JoinCovered` con la maquinaria semántica de v100–v102. Al contrastarlo con el código,
las tres rutas se caen:

- **`FixAgree` no encaja de tipo.** Es `FixAgree (φ : Cnf) (g : GPathM)`: habla de todos los nodos de un estado y sus
  owners, no de una selección. Y `JoinCovered (g₁ g₂ : GPathM)` no menciona ninguna `φ`. La ruta semántica no es
  siquiera enunciable a ese tipo sin cambiar el enunciado.
- **El enunciado que propuse era falso.** `JoinCovered` cuantifica sobre estados arbitrarios con solo `okJoin`; el
  constructor `Reachable.join` lleva `Reachable` en ambos lados, que es justo lo que había tirado.
- **`SoundOn.owned` es un clique, no un camino.** Exige propiedad mutua entre *todo* par `i,j`. Extender pide un `c`
  mutuamente poseído con el segmento entero — que es exactamente el obstáculo de Helly que v99–v102 ya registran como
  fallido.

La ruta que sí es propia del `join` es estructural y sin `φ`.

## 2. Lo demostrado: una cadena del join vive en un solo lado

`JoinDescent.chain_on_one_side`: una cadena parcial de `join g₁ g₂` tiene **todas** sus elecciones en `g₁`, o todas en
`g₂`. Es la forma `Bool` de `no_chain_across_sides`, con el corte de casos sobre `intRange` para no invocar `Classical`
y no romper los `#print axioms`.

De ahí sale el residuo, `SideCovered gj gs`: una cadena del join cuyas elecciones están todas en `gs` o ya es cadena de
`gs`, o extiende un paso hacia abajo. Y el puente, `joinCovered_of_sideCovered`: las dos obligaciones por lado dan
`JoinCovered`.

El reparto queda así: una cadena mezclada no puede mezclar *nodos*, solo entradas de owners, enlaces y owners globales,
y solo en nodos que ambos estados comparten, donde `mergeNode` los une.

## 3. Lo refutado: `SideCovered` es falsa

Escribí la sonda `Probes/JoinBorrow.lean` para medirla. Rehace `insertPure` / `sendTo` / `sendAll` / `pureAdvance` para
quedarse con los dos operandos de cada join, enumera las cadenas parciales del join y, para las que **no** son cadena
del lado que las contiene («prestadas»), mira si extienden.

- **4–6 variables**: 1.355 joins, 548.193 cadenas parciales, 3.759 prestadas, 3.759 extienden, **0 fallos**.
- **6–8 variables**: falla en todos los seeds. 31337 da 31 fallos por `g1` y 6 por `g2` sobre 2.052.130 cadenas;
  90210 da 20 y 16 sobre 1.963.093.

La reserva que puse a los primeros ceros era correcta y saltó al primer escalón de tamaño: cumplirse en fórmulas
aleatorias pequeñas no es evidencia. Es el mismo patrón que precedió a la caída de S1 y de `LossInClosure`.

## 4. El diagnóstico: otra vez Helly

Relancé dos seeds con un diagnóstico por candidato. El resultado es unánime en los 73 fallos:

- **Siempre hay candidatos** en el paso `lo-1`; nunca ocurre que no haya ninguno.
- Todos pasan nodo, owner global, self-owned, forma de raíz y enlace de vuelta.
- Todos mueren por lo mismo: **propiedad mutua**. La forma típica son dos candidatos, cada uno bloqueado por un pick
  *distinto* del segmento.
- La rama de autocomprobación de la sonda (candidato que pasa todos los tests individuales y aun así es rechazado) no
  se disparó ni una vez, así que no es artefacto.

Los fallos son además menos fenómenos de los que sugieren los conteos: salen como prefijos anidados unos de otros, todos
bloqueados por los mismos dos candidatos. Una obstrucción raíz abajo se multiplica sobre las cadenas largas de encima.

Es la obstrucción de Helly de siempre — la información de dos en dos no da cadena común — reapareciendo ahora en el
caso `join`.

## 5. Qué queda en pie

`chain_on_one_side` está intacto, y la sonda lo contrastó sobre unos 8 millones de cadenas parciales sin una sola
violación de la dicotomía. `joinCovered_of_sideCovered` sigue siendo cierto y compila limpio, pero con `SideCovered`
falsa queda **vacío** como ruta a `JoinCovered` — el mismo modo de fallo que `LossInClosure` en v101.

## 6. La sonda vive ahora en el repo

Las sondas anteriores (`DepthCSP`, `IdealTables`, `Characterize`, `ForwardCheck`…) se escribieron en directorios
temporales de sesión y ya no son accesibles, junto con las fórmulas adversarias que refutaron varias conjeturas. A
partir de aquí van en `lean_project/Probes/` y se registran en el `lakefile.toml`: `lake exe join-borrow`.

Dos avisos para quien la use: la máquina es 3-SAT estricto (`clauseWfB` pide tres variables distintas por cláusula), así
que tseitin, pigeonhole y graph_coloring salen rechazados; y comprobar `parent_link` antes que `son_link` en el mismo
bucle enmascara todos los fallos de enlace por hijos — hay que hacerlo en dos pasadas.

## 7. Abierto

- `JoinCovered`, otra vez sin ruta: o se **repara** `SideCovered` — debilitarla a algo que esas 73 cadenas cumplan y que
  siga bastando — o se abandona la separación por lados y se vuelve al invariante `I` de las tablas ideales de v102.
- `PinnedCompletion`, `FrontierSend` y `OwnersAreNodes` siguen donde estaban.
