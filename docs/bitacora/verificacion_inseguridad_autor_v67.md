# Verificación para el Autor v67: el invariante de nodo, y el filtro de cláusulas

Ricardo, soy Claude (Opus 5). Me pediste demostrar el invariante de nodo y, a mitad, demostrar el filtro de cláusulas sin esperar a Tseitin. Primero lo que hay, sin rodeos:

- **El invariante de nodo está demostrado en toda la construcción salvo en un sitio: el filtro de los pasos de cláusula.** Ese sitio queda como una hipótesis única, con nombre y local, de un solo paso.
- **Ese filtro no lo he demostrado.** Lo intenté por la única vía que existe y señalo exactamente dónde se rompe. Y hay una razón de fondo por la que no lo va a demostrar nadie sin resolver P frente a NP. Te la explico en el apartado 4, porque te concierne directamente.
- **He intentado romperlo donde es más probable, y no se rompe.**

---

## 1. El invariante, en términos de grafo

Lo que v66 midió («todo nodo está en una solución de las cláusulas vistas hasta ese paso») es, en términos de la máquina, **`SupportedS`**: todo nodo del estado está en una cadena sólida.

```lean
def NodeInv (g : GPathM) : Prop := isValid g = true → SupportedS g
```

## 2. La inducción, caso a caso (todo `[propext, Quot.sound]`, 0 `sorry`)

| movimiento de la máquina | estado |
|---|---|
| `seed` | **demostrado** |
| `join` | **demostrado** (`SupportedS_join`) |
| `addNode` | **demostrado** (`SupportedS_addNode`) |
| el review dentro de cada filtro | **demostrado** (`SupportedS_review`) |
| filtro de literal positivo y de fusión (sin requisitos) | **demostrado** |
| filtro de negación (un requisito, sobre la cima) | **demostrado**: `TopKey_reachable` prueba que la cima de todo estado lleva un único id de mapa, el de su clave, así que ese filtro o no cambia nada o mata el estado |
| **filtro de cláusula (tres requisitos)** | **hipótesis `ClauseStepExact`** |

```lean
theorem NodeInv_of_ClauseStepExact (φ) (h : ClauseStepExact φ) (g)
    (hr : Reachable (reqOfCnf φ) g) : NodeInv g
```

Y, cerrando el círculo, **la máquina entera como procedimiento de decisión**:

```lean
theorem decides_of_ClauseStepExact (φ) (hwf : WF φ) (hzero : 0 < stepCount φ)
    (h : ClauseStepExact φ) :
    Satisfiable φ ↔ ∃ kv ∈ pureRun φ, isValid kv.2 = true
```

La ida (satisfacible ⇒ la máquina acaba con un estado válido) no necesita la hipótesis: es el teorema del driver. La vuelta usa el invariante de nodo y `sat_of_inhabited`, que decodifica la cadena en una asignación que satisface la fórmula.

## 3. El filtro de cláusula: el intento y dónde se rompe

Qué garantiza la limpieza. Lo he demostrado:

```lean
theorem owns_required ... :   -- un nodo que sobrevive al filtro de cláusula
    ∃ q ∈ n.owners, q.id = r     -- posee, en cada paso requerido, un nodo con el valor requerido
```

Es decir, **cada superviviente es compatible con cada uno de los tres literales de la cláusula, de uno en uno.**

Qué pide `ClauseStepExact`: que el superviviente esté en **una sola** solución que lleve los **tres** literales a la vez.

La única forma de pasar de lo primero a lo segundo es construir la cadena a mano: partir del nodo y bajar y subir eligiendo en cada paso un vecino compatible con todo lo ya elegido. En cada paso, la limpieza garantiza un vecino compatible con **cada** nodo elegido por separado. La construcción necesita **uno compatible con todos a la vez**. Esa es una propiedad de tipo Helly, y ya sabemos que en general falla: los 164 testigos de v13 y los 1.517 callejones sin salida de `ExtendUp`. El caso 17 de v66 la mostró fallando en un estado real, con pares compatibles uno a uno que ninguna solución combina.

## 4. Por qué no es cuestión de más tiempo

Con esta sesión, **todo** lo demás del argumento es teorema. Y la máquina trabaja en tiempo polinómico: los nodos son pares de nodos del mapa, las tablas están acotadas por los nodos, y hay unos pocos estados por paso.

Así que `decides_of_ClauseStepExact` dice, en limpio: **si el filtro de cláusula fuera exacto para toda fórmula, 3SAT estaría en P.** Demostrar `ClauseStepExact` en general *es* demostrar P = NP; no hay una demostración más modesta esperando detrás.

No te lo digo para restarle valor al trabajo, sino para situarlo bien. Tu afirmación entera cabe ahora en un lema local de un solo paso, con nombre, y con todo lo demás demostrado. Si es verdadero, este es su enunciado exacto. Si es falso, un contraejemplo tiene que caer justo aquí, y en ninguna otra parte.

## 5. Intentos de romperlo

**Inserción dirigida** (`--insert`): la fórmula del caso 17, con una cláusula insertada justo después del estado del hueco, sobre cada terna de variables y cada patrón de signos. Cuenta los estados con un nodo que no está en ninguna solución de lo visto, que es una violación directa de `ClauseStepExact`.

| | |
|---|---|
| fórmulas (4 posiciones × 20 ternas × 8 patrones) | 640 |
| **estados con un nodo sin solución** | **0** |
| veredictos zombie | 0 |

Justo donde el hueco de pares se vio en la práctica, una cláusula apuntada a él no consigue abrirlo.

**Fórmulas de Tseitin** (`--tseitin`), la familia clásica contra los métodos locales, ya en 3-CNF:

| grafo | variables | cláusulas | versiones insatisfacibles | **veredicto zombie** (original / simétrica) | versiones satisfacibles aceptadas |
|---|---|---|---|---|---|
| K4 | 6 | 16 | 4 | **0 / 0** | 4 de 4 |
| K3,3 | 9 | 24 | 4 | **0 / 0** | 4 de 4 |
| prisma | 9 | 24 | 4 | **0 / 0** | 4 de 4 |
| cubo | 12 | 32 | 1 | **0 / 0** | 1 de 1 |

Petersen (15 variables, 40 cláusulas) no terminó en más de 8 minutos con esta implementación en listas; lo detuve, como pediste no esperar. La máquina refuta las 13 versiones insatisfacibles probadas. Hay una advertencia honesta: estos grafos son pequeños y de anchura baja, donde también la resolución de anchura acotada los refuta. La prueba de fuego serían expansores más grandes, fuera del alcance de esta implementación.

## 6. Lo que queda en firme y lo que no

**Demostrado:**
- `TopKey_reachable`, `SupportedS_filterAll_easy`, `SupportedS_addNode`, `NodeInv_reachable`;
- `easy_of_not_clause` (en un mapa 3SAT, los pasos difíciles son exactamente los de cláusula);
- `NodeInv_of_ClauseStepExact`, `owns_required`, `decides_of_ClauseStepExact`.

**No demostrado:** `ClauseStepExact`. Es el muro entero, en un lema de un solo paso, y equivale a P = NP.

**Medido:**
- 0 nodos sin solución en 188.435 (v66);
- la inserción dirigida y Tseitin, arriba.

Build: `lake build AbsSat` verde, 92 módulos, 0 `sorry`, 0 axiomas de proyecto.
