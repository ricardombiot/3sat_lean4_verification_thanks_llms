# Verificación para el Autor v66: el muro, releído con tu definición de owners

Ricardo, soy Claude (Opus 5). Me recordaste qué son los owners: el grafo tiene su propio conjunto de owners, que mientras el grafo es válido contiene **todos** los nodos; y los owners de un nodo son los nodos **compatibles** con él, organizados por paso. Me pediste estudiar el muro de nuevo desde ahí. Lo he hecho, y hay una corrección a algo que yo mismo dije en v60.

---

## 1. Tu definición, formalizada, y lo que ya da

Leo «compatible» como **estar en una solución común**: una cadena sólida que pase por los dos nodos. Con eso tu definición se puede enunciar:

```lean
def OwnersExactAt (g) (r) : Prop :=
  ∀ rn, g.node? r = some rn → ∀ p, (g.node? p).isSome → p ∈ rn.owners →
    ∃ sel, ChainSound g sel ∧ Passes g sel r ∧ Passes g sel p
```

Y da exactamente lo que el lector necesita (todo `[propext, Quot.sound]`):

- **`Fabric_sol`**: las soluciones que pasan por `r` forman un tejido, en el sentido de v65. **`FabricAt_of_chain`**: cualquier nodo que esté en una solución tiene un tejido debajo, así que elegirlo es seguro.
- **`alive_readStepSym_of_OwnersExactAt`**: **con tu definición, elegir `r` no mata a ninguno de sus owners.** Es la medida `--pinexact` de v64, ahora deducida de tu definición.

Así que la pregunta se reduce a una sola: **¿la máquina cumple tu definición?**

## 2. A longitud completa, sí, al pie de la letra

Modo nuevo, `lake exe cnfmap --tableexact`. Para cada estado se toman las soluciones reales (fuerza bruta) que siguen vivas dentro de él, y para cada entrada `q ∈ owners(p)` se pregunta si alguna de esas soluciones pasa por los dos.

| cinco semillas | estados | nodos | no son owner global | nodos sin solución | entradas de owners | **espurias** |
|---|---|---|---|---|---|---|
| estados finales | 79 | 5.872 | 0 | 0 | 197.728 | **0** |
| a lo largo de las lecturas | 192 | 7.101 | 0 | 0 | 197.421 | **0** |

A longitud completa, **los owners son exactamente los nodos compatibles**, como dices. Los owners globales contienen todos los nodos (0 excepciones), y todo nodo está en una solución. Y después de cada elección de la lectura sigue siendo así: la limpieza deja otra vez un grafo cuyos owners son exactamente los compatibles con lo elegido. Es la autosemejanza que describes: elegir un nodo lleva a un grafo del mismo tipo.

## 3. La corrección a v60

En v60 medí los estados intermedios y concluí que la exactitud «es falsa hasta el último paso», así que no podía ser un invariante. **Estaba midiendo contra la noción equivocada.** Comparé con las soluciones de la fórmula **completa**, cuando en un estado intermedio la máquina aún no ha visto las cláusulas posteriores.

Tu forma de decirlo, compatibles con lo construido hasta ahora, es la correcta. Midiendo contra **las cláusulas vistas hasta ese paso**:

| estados intermedios, cinco semillas (7.790 estados, 188.435 nodos, 4.362.215 entradas) | nodos sin solución | entradas espurias |
|---|---|---|
| contra la fórmula completa (lo que hizo v60) | 108.356 | 2.688.676 (61,6 %) |
| **contra las cláusulas vistas hasta ahí** | **0** | **18** |

Así que **la propiedad sí se arrastra paso a paso**: casi entera en las tablas y entera en los nodos. El control de la primera fila muestra que el detector no está ciego.

## 4. Las 18 entradas: el hueco exacto, visto en la práctica

Las 18 están en **un único estado** (semilla 90210, caso 17, paso 18 de 40), y son nueve pares simétricos. Emparejan nodos de los pasos 0–2 (valores de x0 y x1) con nodos de los pasos 4–6 (valores de x2 y x3). Cada par es compatible **por separado**: hay soluciones vistas con x0=F, x1=F y soluciones con x2=V, x3=V. Pero **ninguna solución vista las tiene a la vez**.

Es el hueco entre compatibilidad **por pares** y compatibilidad **conjunta**, que es exactamente donde toda la teoría dice que puede fallar un método local. La máquina lo cierra más tarde: los estados finales de esa fórmula salen exactos.

Probé a **forzarlo**. `--hunt` toma esa fórmula y le añade cláusulas aleatorias, buscando que la máquina dé por válida una fórmula insatisfacible:

| | dos tandas (hasta 4 y hasta 7 cláusulas añadidas) |
|---|---|
| fórmulas probadas | 350, de ellas 115 insatisfacibles |
| **veredictos zombie** | **0** |
| nodos sin solución en estados finales | 0 |
| entradas inexactas en estados finales | 0 de 432.087 |

## 5. El muro, reformulado

Hay dos formas, y ahora sé cuál es la que se arrastra:

- **A nivel de nodo:** *todo nodo está en una solución de las cláusulas vistas hasta ese paso.* Se cumple en **todos** los estados medidos, intermedios, finales y de lectura. **Este es el invariante candidato para una inducción sobre la construcción.** A longitud completa es exactamente «no hay zombies», y con `FabricAt_of_chain` hace segura cada elección del lector.
- **A nivel de tabla, tu definición:** *todo owner es compatible.* Se cumple en todo estado de longitud completa, pero puede fallar **transitoriamente** a mitad de la construcción (las 18 entradas). No conviene inducir sobre ella; conviene recuperarla al final.

El paso inductivo difícil es **añadir una cláusula**. Hay que ver que todo nodo que sobrevive a la limpieza sigue en alguna solución que además satisface la nueva cláusula. La limpieza solo mira información por pares, y la cláusula pide compatibilidad conjunta. El caso 17 muestra que ese hueco existe en la práctica y que, en lo medido, la máquina siempre acaba cerrándolo.

Una advertencia, dicha una vez porque dice dónde buscar: los estados de la máquina son de tamaño polinómico, así que si el invariante de nodo valiera para toda fórmula, 3SAT se decidiría en tiempo polinómico. Si existe un contraejemplo, tiene que estar justo en ese paso inductivo, con la forma del caso 17: pares compatibles uno a uno que ninguna solución combina. Las fórmulas pequeñas aleatorias no lo encuentran; las familias estructuradas (Tseitin) y la búsqueda dirigida desde estados como el caso 17 son el sitio donde mirar.

## 6. Lo que queda en firme y lo que no

**Demostrado:** el tejido de soluciones; un nodo en una solución tiene un tejido debajo; tu definición implica que elegir un nodo no mata a ninguno de sus owners.

**Medido:**
- tu definición se cumple exacta en todo estado de longitud completa (0 de 395.149 entradas);
- los owners globales contienen todos los nodos;
- a mitad de construcción, contra las cláusulas vistas, 0 nodos zombie y 18 entradas espurias en un solo estado;
- la búsqueda dirigida desde ese estado no encontró ningún veredicto zombie.

**No demostrado:** el invariante de nodo como inducción sobre la construcción. Es el muro, ahora con su paso difícil identificado: añadir una cláusula.

Build: `lake build AbsSat` verde, 90 módulos, 0 `sorry`, 0 axiomas de proyecto.
