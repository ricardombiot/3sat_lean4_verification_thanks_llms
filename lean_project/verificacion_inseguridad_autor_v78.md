# Verificación para el Autor v78: P1 cerrada — el tejido nace en `addNode`, y tu `all_previous_nodes_are_owners_of_me!` es quien lo teje

Ricardo, soy Claude (Opus 5). P1 está demostrada, y de paso encontré un error de contabilidad mío que corrijo abajo.

---

## 1. Lo demostrado (`AbsSat/GraphPath/Model/FabricAdd.lean`)

`Fabric.lean` (v65) demostró que el tejido **sobrevive** a las operaciones. Lo que nunca dijo es de dónde **sale** uno. Eso es lo que faltaba, y es lo que hay ahora:

| teorema | qué dice |
|---|---|
| `Fabric_initSeed` | **la semilla ya es un tejido** — un nodo que se posee a sí mismo; dos de las nueve cláusulas salen vacías |
| `Fabric_addNode` | **el tejido se extiende a través de `addNode`**: los miembros viejos conservan lo suyo y el nodo nuevo entra relacionado con todos |
| `FabricAt_addNode_new` | el tejido del nodo nuevo vive **dentro de sus propios owners** |
| `isValid_readStepSym_addNode_new` | y por tanto **elegir el nodo nuevo nunca atasca al lector** |

Los cuatro con cierre `[propext, Quot.sound]`. Build verde, 100 módulos, 0 `sorry`, 0 axiomas de proyecto.

## 2. La cláusula que necesitaba una idea, y por qué es tuya

Ocho de las nueve cláusulas son contabilidad. La novena, `up`, no.

El nodo nuevo tiene en su tabla a **todos** los miembros, y `up` exige que cada entrada esté respaldada por **un padre del nodo nuevo que esté también en la tabla**. Como los padres del nodo nuevo son **toda la línea anterior**, lo que hay que producir es un miembro en el paso `current_step - 1` relacionado con la entrada dada.

Está ahí, y lo entrega el propio tejido: `support` le da a `v` una entrada `w` justo en ese paso, `symm` la gira a `T w v`, `inS` hace de `w` un miembro, y como `w` es un nodo de ese paso, está en la línea anterior — o sea, **es padre del nodo nuevo**. El portador es el testigo de soporte de `v`, reflejado.

Dos cosas me parecen dignas de señalar:

- **La simetría es portante aquí, no decorativa.** Sin `symm` no hay portador. Por eso valió la pena que v64 la convirtiera en teorema (`OwnSymmetric_read`) antes de intentar esto.
- **Y lo que hace que la cláusula se pueda cumplir es tu diseño.** `addNode` le da al nodo nuevo todo `gowners` y le da el nodo nuevo a todos como owner — tu `all_previous_nodes_are_owners_of_me!` —, y le pone por padres la línea anterior entera. Las dos decisiones juntas son exactamente lo que una cláusula de tejido pide. No es que el tejido encaje por casualidad: es que el tejido **es** lo que tu construcción hace.

## 3. La corrección de contabilidad

En v77 escribí que v65 había demostrado que el tejido «sobrevive a las cuatro operaciones». Fui a comprobarlo: **`Fabric.lean` no menciona `join` ni una sola vez.** Cubre `updateAt`, `unlink`, `symmetrize`, `removeNode`, `cleanInvalid`, el review entero (original y simétrico), `filterRequire` y `filterAll` — pero no la fusión.

Así que el libro mayor de la inducción sobre `Reachable`, con lo de hoy, queda:

| caso | estado |
|---|---|
| semilla | **demostrado hoy** |
| `addNode` | **demostrado hoy** |
| review y filtros | demostrado (v65) |
| **`join`** | **abierto** — no estaba, y yo lo había dado por hecho |

Es un caso más de lo que v74 vino a corregir, y prefiero que aparezca en el registro nada más detectarlo.

## 4. Dónde queda la ruta de v77

| pieza | estado |
|---|---|
| **P1** el tejido nace en la semilla y en `addNode` | **cerrada hoy** |
| **P2** lo preservan review y filtros | cerrada (v65) — **salvo `join`** |
| **P3** lo preserva el filtro de cláusula con la cobertura intacta | abierta; medida en v77 (124.246 nodos, 0 fallos) |
| **P4** el puente `FabricAt ⟹ PickSome` | abierta, con el desajuste `readStepSym` / `filterAll g [q.id]` declarado |
| **P5** cierre con `L7.satisfiable_of_inhabited` | libre si caen las anteriores |

Lo siguiente por orden de rentabilidad: **`join`**, que es contabilidad y cierra P2 de verdad; y después **P4**, porque es la que decide si toda esta rama conecta con el veredicto o se queda a un paso.

Y el límite de siempre, que no cambia: si las cinco cerraran para toda fórmula, 3SAT estaría en P. Lo esperable sigue siendo que **P3 pida la hipótesis de clase**.
