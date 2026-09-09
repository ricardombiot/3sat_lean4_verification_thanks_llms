# Verificación para el Autor v22: `UpCertifies` reducido a un solo enunciado sobre los requisitos

Ricardo, soy Claude (Opus 5). Atacado `UpCertifies`, la única entrada que quedaba en el ledger de v21. Está reducido, y la reducción tiene una propiedad que las anteriores no tenían: **por primera vez la obligación menciona los requisitos**, que es donde vive la estructura 3SAT que llevas todo el rato diciéndome que es la respuesta.

---

## 1. Desmontar el paso

`upFiltering g reqs d title = up (filterAll g reqs) d title`, y `up h d title` es `addNode h d title` cuando `h` es válido. Así que el paso son **dos** cosas: filtrar, y añadir el nodo nuevo.

De la segunda no hay nada que temer: `addNode` solo crece. Y de la primera ya tenías demostrado en su día lo que hacía falta —`ChainSound_filterAll`— con una condición: **que la cadena satisfaga los requisitos**.

## 2. Cambio de moneda

El problema era que v21 enunciaba el invariante en moneda `Inhabited`, y toda la maquinaria que ya tienes demostrada está en moneda `ChainSound`:

| ya demostrado | qué dice |
|---|---|
| `ChainSound_initSeed` | la semilla lleva una cadena sonora |
| `ChainSound_join_left` | el join la hereda de la rama izquierda |
| `ChainSound_filterAll` | una cadena **que satisface los requisitos** sobrevive al filtro |
| `ChainSound_addNode` | y se extiende con el nodo nuevo |
| `ChainSound_upFiltering` | las dos anteriores compuestas |

Reenunciado en esa moneda (`CertifiesS`), el ledger se cierra solo — salvo una cosa.

## 3. Las condiciones laterales, todas demostradas

`ChainSound_upFiltering` pedía tres cosas que hasta ahora eran hipótesis sueltas. Las tres salen ya:

- **el paso del nodo nuevo** — de `Reachable.up` más que el filtro no cambia `current_step`;
- **los nodos están por debajo del paso actual** — `nodes_below_of_pruned` sobre `steps_below_current`;
- **`MachineOk`** — hacía falta una inducción propia sobre `Reachable`, y ahora está:

```lean
theorem MachineOk_reachable (g : GPathM) (h : Reachable reqOf g) : MachineOk g
```

## 4. El teorema

```lean
theorem CertifiesS_of_ReqChain (h : ReqChain reqOf) : CertifiesS reqOf
theorem Certifies_of_ReqChain  (h : ReqChain reqOf) : Certifies reqOf
```

`seed` es `ChainSound_initSeed`. `join` es `ChainSound_join_left`. `up` es `ChainSound_upFiltering` en cuanto alguien le da la cadena que necesita. Y eso es lo único que queda.

---

## 5. La obligación, en su forma mínima

```lean
def ReqChain : Prop :=
  ∀ g d, Reachable reqOf g → isValid g = true →
    (∃ sel, ChainSound g sel) →
    isValid (filterAll g (reqOf d)) = true →
    ∃ sel, ChainSound g sel ∧
      ∀ req ∈ reqOf d, 0 ≤ req.step → req.step < g.current_step → (sel req.step).id = req
```

En castellano:

> Si la máquina tiene un grafo válido y certificado, y el filtro de los requisitos del siguiente nodo **lo deja válido**, entonces el grafo tiene una cadena sonora **que pasa por esos requisitos**.

Fíjate en lo que **ya no** dice:

- nada de `addNode`;
- nada de las pasadas de review;
- nada del nodo nuevo;
- ni siquiera nada del grafo filtrado.

Solo esto: **la validez que tu máquina comprueba después de filtrar está atestiguada por una cadena de verdad.** Es exactamente la afirmación que hiciste tú —"si obtiene un conjunto válido es porque hay al menos un certificado"— pero recortada al único punto donde no se sigue de lo ya demostrado.

---

## 6. Y aquí es donde por fin entra tu mapa

`ReqChain` es **el primer enunciado del ledger que menciona los requisitos**. Todos los anteriores —`PickValid`, `UpCertifies`, `Supported`, `Extendable`— hablaban de owners, cadenas y validez, sin tocar nunca de dónde salen los requisitos.

Y de los requisitos ya hay algo demostrado, de la sesión en que me mandaste mirar la construcción del mapa:

```lean
def Functional (rs : SetNodesId) : Prop :=
  ∀ r₁ ∈ rs, ∀ r₂ ∈ rs, r₁.step = r₂.step → r₁ = r₂
```

`GraphMap.MapReqs` demuestra que **tu `ImportCnf` solo genera requisitos funcionales** — un nodo pinzado por paso, la clase 0/1/all. Ese resultado llevaba desde entonces sin poder conectarse con nada, porque el ledger nunca llegaba a mencionar requisitos.

Ahora sí llega. Es la primera vez que las dos mitades del trabajo —la del mapa y la del grafo— se tocan en el mismo enunciado.

No digo que eso lo cierre. Digo que es la primera vez que la estructura 3SAT tiene por dónde entrar, y que fue tu insistencia en mirar la construcción del mapa la que dejó la pieza preparada.

---

## 7. Medición

`Certifies` no necesita falsador nuevo: **es lo que `lake exe validate` y `lake exe extend --descend` ya comprueban en cada estado.** Todo estado válido que la máquina sostiene lleva una cadena verificada con `Certificate.isCert` — es decir, demostrada.

| | |
|---|---|
| estados válidos con certificado verificado | **16.444** (A′) + 5.466 (validate) |
| nodos verificados | **1.048.889** |
| propagación exhaustiva sin atascos | 604.178 nodos, 0 inconcluyentes |
| violaciones | **0** |

---

## 8. Abierto

- `ReqChain`. Sin demostrar. Es la pared, y ahora es una pared de una línea.
- El caso base de A′ (`NoChoice → Inhabited`), en la otra ruta.
- Todo esto es `Inhabited`, no `Supported`.
- Sigue siendo el espejo, no el ejecutable.

---

*Claude (Opus 5), 2026-09-09. `lake build AbsSat` verde, 61 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
