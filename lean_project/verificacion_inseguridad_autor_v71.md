# Verificación para el Autor v71: la clase de alcance acotado, y lo que la medición corrigió dos veces

Ricardo, soy Claude (Opus 5). Elegiste el camino (1) de v70: un teorema de `FlipCore` para una clase de fórmulas de alcance acotado. Me pediste además que el caso general no quede descartado, solo aplazado — así queda, y de hecho lo que ha salido de aquí apunta hacia él más de lo que yo esperaba.

El resumen, sin rodeos:

- **La clase está definida y demostrada estable**, en un módulo nuevo. No es trivial y no es «fórmulas pequeñas»: hay testigos con 12 variables y el mismo parámetro que con 3.
- **Los cinco controles de paridad quedan fuera**, por la razón correcta y medida.
- **Mi primera idea de demostración era falsa**, y la medición la tumbó antes de escribir una línea de Lean. La segunda también. La tercera aguanta: **0 fallos en 47.663 instancias** dentro de la clase, cinco semillas.
- **`FlipCore` para la clase no está demostrado todavía.** Lo que falta ya no es una idea, es trabajo de formalización, y te digo exactamente cuál.

---

## 1. La clase: el hipergrafo de la fórmula, y por qué sobre prefijos

La ruta E de v17 midió el hipergrafo de restricciones **del mapa** y salió cíclico, así que Beeri–Fagin–Maier–Yannakakis no aplica a 3SAT en general. Eso sigue igual, y tiene que seguir igual: un sí ahí habría *sido* la afirmación entera. La pregunta de v70 es estrictamente menor y sí se puede hacer: **¿para qué fórmulas aplica?**

El objeto correcto es el hipergrafo de la **fórmula** — una arista por cláusula, sobre las tres variables que nombra. El mapa añade un vértice por paso de cláusula, pero ningún otro lo menciona: ocurre en una sola arista, y la primera pasada de orejas lo quita. Es el propio ejemplo de `Hypergraph.lean` («el ciclo es la estructura de variables compartidas del CNF, no un artefacto de la construcción»).

Pero hay un detalle que casi se me escapa y que cambia la definición. **La α-aciclicidad no es hereditaria**: quitar una arista puede volver cíclico un hipergrafo acíclico. El testigo está en dos líneas de este mismo código —`{0,1},{1,2},{0,2},{0,1,2}` reduce (la arista grande subsume el triángulo), y `{0,1},{1,2},{0,2}` no—. Es la razón de ser de la β-aciclicidad.

Importa porque **la máquina procesa las cláusulas en orden**: en el paso de la cláusula `m` el estado ha visto `φ.clauses.take m` y nada más, y toda cadena suya es una solución de *ese* prefijo (`satUpTo_of_chain`, v70). Una hipótesis sobre φ entera no llegaría a los estados intermedios, que es donde el filtro de cláusula corre. Así que la clase pide la propiedad de **todos los prefijos**:

```lean
def BoundedScope (φ : Cnf) (K : Nat) : Prop :=
  PrefixAcyclic φ ∧ ∀ m ≤ φ.clauses.length, gyoRounds (prefixEdges φ m) ≤ K
```

Medido, la distinción no cuesta nada: de 800 fórmulas del generador de las campañas, 281 son α-acíclicas y **las mismas 281** son prefijo-acíclicas, ninguna cumple lo primero sin lo segundo. Es la demostración la que necesita la forma fuerte, no las instancias.

## 2. Lo demostrado (módulo nuevo `AbsSat/GraphMap/CnfHypergraph.lean`)

| teorema | qué dice |
|---|---|
| `gyoIter_gyoRounds` | el contador de rondas **es** el número de iteraciones: `K` rondas de `gyoStep` llegan adonde llega el punto fijo. Sin axiomas. |
| `boundedScopeB_iff` + `instance Decidable` | la clase es decidible, así que se puede `decide` y se puede medir con el mismo objeto que se demuestra |
| `gyoIter_eq_nil_of_BoundedScope` | en cada prefijo, `≤ K` rondas dejan el hipergrafo vacío — **la medida finita sobre la que una inducción de reparación desciende, y no menciona `φ.nVars`** |
| `BoundedScope_prefix` | **la clase es cerrada bajo prefijos**: si φ está dentro, cada estado intermedio de su ejecución también, con la misma `K` |
| `alphaAcyclic_of_BoundedScope` | la fórmula entera es el último prefijo |

Y cuatro ejemplos comprobados por el kernel (`decide`, sin `native_decide`), que son los que dicen que la clase no es una definición vacía:

- dos cláusulas compartiendo dos variables: dentro, `K = 2`;
- el triángulo `{0,1,2},{1,2,3},{0,2,3}`: **fuera, a cualquier `K`** — que es la forma que tiene la paridad;
- **tres gadgets disjuntos, 12 variables: dentro, con el mismo `K = 2`**;
- una estrella, una variable compartida por cuatro cláusulas, 9 variables: dentro, `K = 2`.

Los dos últimos son el punto: `K` acota **rondas**, no tamaño. Cada ronda pela todas las aristas a la vez, así que una unión disjunta de copias de un gadget tiene `nVars` sin cota y `K` constante. La clase no es «fórmulas pequeñas».

## 3. Los controles: las cinco familias de paridad quedan fuera

Con `tseitin` sobre los grafos 3-regulares que ya estaban en `SymCampaign.lean`, ambas paridades:

| grafo | variables | cláusulas | α-acíclico | núcleo cíclico |
|---|---|---|---|---|
| K4 | 6 | 16 | **no** | 4 aristas |
| K3,3 | 9 | 24 | **no** | 6 |
| prisma | 9 | 24 | **no** | 6 |
| cubo | 12 | 32 | **no** | 8 |
| Petersen | 15 | 40 | **no** | 10 |

El núcleo tiene exactamente una arista por vértice del grafo: el hipergrafo **es** el grafo. El detector no está ciego, y las familias que v70 señalaba como el sitio donde buscar el contraejemplo son precisamente las que la clase excluye.

## 4. La medición: dos ideas de demostración caídas, y la que aguanta

Aquí está el trabajo real de esta sesión. `FlipCore`, quitada la máquina, pide una **reparación**: dada una solución de las cláusulas vistas que respeta unos pines, y un literal más que satisfacer, producir otra solución que respete los pines *y* el literal nuevo. Lo que hay que medir antes de escribir Lean no es si la solución reparada **existe** (v68 ya midió eso: 0 fallos), sino si **la construcción que la demostración formalizaría la encuentra**.

Modo nuevo, `lake exe cnfmap --flipscope`. Cinco semillas, 400 fórmulas, 3–6 variables, todas las longitudes de prefijo, y solo se cuentan las instancias donde una solución reparada existe de verdad (comprobado por fuerza bruta). Los tres modos ven **las mismas** instancias.

| dentro de la clase — 134 fórmulas, 47.663 instancias | atascos |
|---|---|
| por **variable**, en orden de oreja GYO | **484** |
| por **variable**, la primera que sirva | 493 |
| por **fila** | 25 |
| por **fila, tras el reductor de semi-joins** | **0** |

| fuera de la clase — 266 fórmulas, 415.984 instancias | atascos |
|---|---|
| por fila, tras el reductor | **1.192** |

| control Tseitin — 111.547 instancias | atascos |
|---|---|
| por fila, tras el reductor | **607** |

**Y lo que vale no es la última fila, es cómo se llegó a ella.**

**Primera caída.** La reparación variable a variable —que es lo que yo había planeado como «Pieza 1»— se atasca **dentro de la clase**: 484 de 47.663. Falsa, y refutada antes de gastar una sesión en Lean.

**Por qué.** Volqué los casos atascados. Todos tienen **todas las cláusulas sobre el mismo conjunto de variables**: `(x2∨¬x0∨¬x1) ∧ (¬x2∨x0∨¬x1) ∧ …`. Como hipergrafo eso es **una sola arista**, trivialmente acíclica; como restricción es la intersección de varias relaciones sobre ese ámbito. Ninguna aciclicidad ayuda a un procedimiento que fija una variable cada vez y no reconsidera. **Y la máquina no trabaja así**: un nodo de cláusula codifica sus **tres literales a la vez** — la unidad que la máquina mueve es la *fila*, no la variable. Mi procedimiento era más débil que la máquina.

**Segunda caída.** Por filas: 25 atascos, mucho mejor, todavía no cero. Volqué esos también, y otra vez dicen por qué. Dos ámbitos que comparten dos variables, `[0,2,3]` y `[1,2,3]`: el goloso instala en el segundo una fila **localmente válida y globalmente muerta** —ninguna fila del primero concuerda con ella— y no hay vuelta atrás.

**Lo que quita esas filas es el semi-join.** Descartar de cada relación toda fila sin apoyo en una vecina, hasta el punto fijo: eso es **consistencia de arcos sobre las relaciones**, y es exactamente lo que hacen las pasadas de `review` con las tablas de owners. Con el reductor delante: **0 atascos en 47.663 instancias**, cinco semillas, dentro de la clase; 1.192 fuera y 607 en los controles — o sea, el procedimiento no es un sí-a-todo, falla donde debe.

## 5. Lo que esto significa, y lo que falta

El procedimiento que aguanta es, literalmente, el algoritmo clásico para CSP α-acíclicos (semi-joins hasta el punto fijo, luego elección golosa sin retroceso). Y la correspondencia con tu máquina no es una analogía, es una identidad término a término:

| el algoritmo clásico | tu máquina |
|---|---|
| relación de un ámbito | las filas del nodo de cláusula (los tres literales a la vez) |
| semi-join hasta el punto fijo | las pasadas de `review` |
| consistencia de arcos | `ArcConsistency.review_arcConsistent`, **ya demostrado sin hipótesis** |
| elección golosa sin retroceso | el lector (`PickSome`, v58–v59) |

Por eso creo que esta ruta vale más de lo que parece: la mitad «consistencia por pares» de BFMY ya la tienes demostrada desde v12–v59; lo que falta es la mitad de aciclicidad, y ahora está definida, es decidible, es cerrada bajo prefijos y tiene su medida acotada (`gyoIter_eq_nil_of_BoundedScope`).

**No demostrado:** `FlipCore` para la clase. Lo que falta es concreto y ya no es una idea sino formalización:

1. Las relaciones y el semi-join como objetos del modelo puro (no del ejecutable).
2. El teorema de no-retroceso: en un hipergrafo α-acíclico, tras el reductor la elección golosa no se atasca. Es la inducción sobre las `K` rondas, con `gyoIter_eq_nil_of_BoundedScope` como medida.
3. El puente de vuelta: de la asignación reparada a una cadena sonora de *ese* estado que pase por *ese* nodo. `chainSound_along_prefix` da la mitad; la otra mitad es que la cadena caiga en `g` y no en la rama de la asignación.

Y sobre el caso general, que dijiste que no quedara descartado: no lo está. Lo que esta sesión añade en esa dirección es que **el obstáculo tiene ahora una forma medible** — cuánto se puede ensanchar `K`, o debilitar la aciclicidad, antes de que la reparación empiece a atascarse. Los 1.192 atascos de fuera de la clase son justamente el material para esa pregunta, y son reproducibles.

Build: `lake build AbsSat` verde, **97 módulos**, 0 `sorry`, 0 axiomas de proyecto.
