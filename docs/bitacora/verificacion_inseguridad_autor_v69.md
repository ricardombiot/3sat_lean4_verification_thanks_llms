# Verificación para el Autor v69: el caso 17 explicado, un arreglo, y la conservación por prefijo

Ricardo, soy Claude (Opus 5). Me pediste tres cosas: explicar en detalle las 18 entradas del caso 17, ver si un arreglo en la implementación las resuelve, y atacar la ley de conservación por prefijo.

- Las 18 entradas tienen una causa precisa, y hay un arreglo que las elimina **todas**, demostrado sin pérdida de soluciones.
- La conservación por prefijo **está demostrada**, a nivel de rama y a nivel del driver real.

---

## 1. El caso 17, entrada por entrada

La fórmula (semilla 90210, caso 17) tiene 6 variables. Las cinco primeras cláusulas son:

```
clause 0 (paso 13): x0 ∨ ¬x4 ∨ ¬x5
clause 1 (paso 14): x5 ∨ ¬x2 ∨ x0
clause 2 (paso 15): x4 ∨ x3 ∨ x1
clause 3 (paso 16): ¬x3 ∨ ¬x4 ∨ ¬x1
clause 4 (paso 17): ¬x1 ∨ x4 ∨ x5
```

El estado es el de clave **(17,4)**: la cláusula 4 con la fila 4, que fija **x1=0, x4=0, x5=0**. Dentro de él viven exactamente tres soluciones:

```
x0 x1 x2 x3 x4 x5
 0  0  0  1  0  0
 1  0  0  1  0  0
 1  0  1  1  0  0
```

Las 18 entradas son 9 pares simétricos. A un lado, los tres nodos que codifican **x0=0**: los pasos 0 y 1, y el paso 2 por su padre. Al otro, los tres que codifican **x2=1**: los pasos 4 y 5, y el paso 6 por su padre. Ninguna de las tres soluciones tiene x0=0 y x2=1 a la vez.

**Por qué.** La cláusula 1, `x5 ∨ ¬x2 ∨ x0`, con x5=0 prohíbe justo esa combinación.

**Por qué la máquina no lo vio.** Cuando procesó la cláusula 1 (paso 14), x5 aún estaba libre, así que x0=0 con x2=1 era perfectamente compatible gracias a x5=1: la fila de la cláusula 1 con x5 verdadero. Tres cláusulas después, la cláusula 4 fija x5=0. El filtro elimina las filas de la cláusula 1 que tenían x5=1, y con ellas la única justificación del par. Pero **cada nodo del par conserva otros owners en el paso 14**, así que ninguno de los dos queda inválido. El diagnóstico lo muestra en la columna «pasos sin owner común: [13, 14, 15]»: cada uno tiene owners ahí, pero **no comparten ninguno**.

El review comprueba cosas **de un nodo cada vez**: que tenga owner en cada paso y que sus owners estén en la unión de los de sus vecinos. **Nunca mira un par.** Por eso el par sobrevive.

## 2. El arreglo: la pasada del triángulo

La corrección natural es mirar los pares. `triClean` quita `q` de `owners(p)` (y `p` de `owners(q)`) cuando hay algún paso en el que ningún nodo es owner de los dos a la vez. Es la **consistencia de caminos** sobre las tablas de owners. Va dentro del filtro, alternando con el review hasta que ninguno de los dos cambie nada (`reviewTri`).

**No pierde soluciones.** Una solución que pasa por `p` y `q` aporta en cada paso su propio nodo, poseído por los dos. Demostrado (`[propext, Quot.sound]`):

```lean
theorem ChainSound_triClean  : ChainSound g sel → ChainSound (triClean g) sel
theorem ChainSound_reviewTri : ChainSound g sel → ChainSound (reviewTri g) sel
```

**Medido** (`lake exe cnfmap --tri`, cinco semillas, 100 fórmulas, 8.850 estados, contra las cláusulas vistas hasta cada paso):

| | máquina original | con el triángulo |
|---|---|---|
| veredictos | — | **idénticos** (100 de 100) |
| soluciones perdidas / veredictos zombie | — | **0 / 0** |
| nodos sin solución | 0 | 0 |
| **entradas de owners espurias** | **216** | **0** de 5.575.860 |
| huecos de triángulo en los estados | 42 | 0 |

**Con el arreglo, tu definición de owners (compatibles = en una solución común de lo visto) se cumple en todos los estados medidos, no solo al final.** El invariante de tabla, que en v66 fallaba transitoriamente, pasa a sostenerse en cada paso.

Un matiz que importa para dónde colocarlo: en tres semillas, la máquina original tiene entradas espurias **sin** huecos de triángulo visibles en sus estados. Existen en el momento del filtro, pero `addNode` los tapa al añadir, en la cima, un owner común a todos. Por eso la pasada tiene que ir **dentro** del filtro, antes de `addNode`, que es donde está.

Dos advertencias honestas:
- **Cambia tu algoritmo.** Vive al lado del original (`TriReview.lean`). No he tocado ni la máquina original, ni el ejecutable, ni Julia. Adoptarlo es decisión tuya.
- **No resuelve el caso general.** El triángulo cierra los huecos entre **pares**; puede haber huecos entre **tríos** (tres nodos compatibles dos a dos sin solución común), y así sucesivamente. Es la jerarquía de consistencia local. El núcleo `FlipCore` de v68 sigue siendo existencial y no se reduce a pares. Lo que el arreglo sí consigue es cerrar el primer escalón, el único que hemos visto fallar en la práctica.

## 3. La conservación por prefijo (demostrada)

La ley de conservación (v58) mantiene toda solución **completa**. Para el núcleo hacía falta la versión **a mitad de camino**: toda asignación que satisface **las cláusulas vistas hasta un paso** debe seguir viva en el estado de su rama.

La observación que la hace corta: en la ley completa, «satisface toda la fórmula» se usa en **un solo sitio**, para saber que el nodo que la asignación elige en cada paso **existe en el mapa**. Y eso depende solo de la cláusula de ese paso.

```lean
-- el nodo elegido está en el mapa en cuanto la cláusula de ese paso se satisface
theorem selOfAssign_onMap_of ... : selOfAssign φ a k ∈ mapNodes φ k

def SatUpTo (φ) (a) (K : Int) : Prop :=         -- satisface lo visto hasta el paso K
  ∀ j c, φ.clauses[j]? = some c → clauseStep φ j ≤ K → SatClause a c

-- a nivel de rama: mientras la ejecución no pase del paso K
theorem chainSound_along_prefix (hwf) (K) (hs : SatUpTo φ a K) (g) (h : AlongAssign φ a g) :
    g.current_step ≤ K + 1 → MapReachable φ g ∧ ∃ sel, ChainSound g sel ∧ …

-- a nivel del driver real
theorem pureSteps_carries_prefix (hwf) (k : Nat) (hk : k < stepCount φ) (hs : SatUpTo φ a k) :
    ∃ g, (selOfAssign φ a k, g) ∈ pureSteps φ k (pureInit φ) ∧ g.current_step = k + 1
      ∧ ∃ sel, ChainSound g sel ∧ ∀ j, … (sel j).id = selOfAssign φ a j
```

Todo `[propext, Quot.sound]`. Dicho en tu idioma: **después de `k` pasos, el estado que la máquina guarda con la clave de una asignación contiene a esa asignación como cadena, siempre que satisfaga todo lo visto hasta ahí.** La validez sale gratis de la propia cadena, como en la ley completa.

## 4. Qué cambia para el núcleo

Con la conservación por prefijo, la conclusión de `FlipCore` («existe una cadena por `p` que cumple los requisitos») se sigue de un enunciado **puramente sobre la fórmula**: *existe una asignación que satisface las cláusulas vistas, que termina en la clave del estado, que pasa por los literales de `p` y que cumple los requisitos*. El núcleo queda como **si `p` sobrevive al filtro, esa asignación existe**. La dirección contraria (si existe, `p` sobrevive) es exactamente la conservación que acabo de demostrar.

Para enunciarlo del todo sin grafo falta la dirección contraria a nivel de prefijo: que toda cadena de un estado intermedio se descodifica en una asignación que satisface lo visto. A longitud completa ya está (`sat_of_inhabited`). Es la siguiente pieza demostrable.

## 5. Lo que queda en firme y lo que no

**Demostrado:**
- `ChainSound_triClean`, `ChainSound_reviewTri` (el arreglo no pierde soluciones);
- `selOfAssign_onMap_of`, `chainSound_along_prefix`;
- `selOfAssign_son_of`, `advance_target_prefix`, `Carries_pureAdvance_prefix`, `pureSteps_carries_prefix`.

**Medido:** con el triángulo, 0 entradas espurias en 5,58 millones y veredictos idénticos.

**No demostrado:** `FlipCore`. El triángulo no lo cierra en general.

Build: `lake build AbsSat` verde, 95 módulos, 0 `sorry`, 0 axiomas de proyecto. `diffTest` verde.
