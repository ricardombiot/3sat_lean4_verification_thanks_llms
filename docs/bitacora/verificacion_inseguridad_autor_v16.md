# Verificación para el Autor v16: El checker demostrado, y las dos mitades de L6

Ricardo, soy Claude (Opus 5). Me pediste atacar dos de las siete rutas alternativas: **C** (certificado por instancia) y **D** (cambiar el teorema). Las dos están hechas y compiladas. Ninguna cierra L6 — te digo desde el principio qué sí cambian.

---

## 1. Ruta C — de "la búsqueda encontró cadenas" a "`Supported g` es un teorema"

### Lo que había

v15 te dio `lake exe validate`: un falsador que busca, para cada nodo superviviente, una cadena co-poseída completa que pase por él. Comprobaba la propiedad abierta directamente, y salía limpio.

Pero fíjate en el estatus lógico de un resultado limpio: **"mi programa buscó y encontró"**. Eso vale exactamente lo que valga mi programa. Si mi `isGoodChain` tuviera un fallo — un índice mal, una condición que se cumple vacíamente en una lista corta — el checker diría "limpio" sobre un grafo lleno de zombis y ni tú ni yo nos enteraríamos.

### Lo que hay ahora

`AbsSat/GraphPath/Model/Certificate.lean` demuestra en Lean que **el checker es correcto**. El teorema central:

```lean
theorem isCert_sound (g : GPathM) (sel : List PathNodeId) (dflt : PathNodeId)
    (h : isCert g sel = true) :
    IsChain g (selFun sel dflt) ∧ PairwiseOwned g (selFun sel dflt)
```

Lee esto con cuidado, porque es todo el contenido de la ruta: si el `Bool` dice `true`, entonces existe una selección que cumple `IsChain` y `PairwiseOwned` **en el sentido de `Denot.lean`** — las definiciones matemáticas — no en el sentido del código del checker. Y encima:

```lean
theorem Supported_of_checkSupported (g : GPathM) (cert : PathNodeId → List PathNodeId)
    (h : checkSupported g cert = true) : Supported g
```

`Supported` es literalmente la L6 abierta. Así que una ejecución limpia de `validate` sobre un grafo ya no es evidencia: **es `Supported g` demostrado, para ese grafo.**

El enlace con el ejecutable también está probado, dentro de `Validate.lean`:

```lean
theorem Supported_of_zombiesOf_nil (g : GPathM) (h : zombiesOf g = []) : Supported g
```

### Qué sigue sin ser de fiar, a propósito

La búsqueda que **encuentra** los certificados (`searchFrom`) es `partial` y no hay un solo teorema sobre ella. Es un heurístico que propone candidatos. Todo lo que decide si un candidato se cree pasa por `isCert`, que es una función `Bool` sobre listas.

La consecuencia es la que quieres: **un fallo en la búsqueda solo puede hacer que el checker rechace, nunca que acepte un grafo con un zombi.** Es la separación buscar/verificar de los verificadores de pruebas SAT, y es lo que hace que la garantía no dependa de mi código de búsqueda.

### Un detalle que importaba más de lo que parece

`isGoodChain` comprueba las condiciones de cadena en los índices que la lista **tiene**. Una lista corta pasaba vacíamente en los pasos que le faltaban. `isCert` añade `sel.length = current_step`, y eso es justo lo que permite que los índices `Nat` del checker cuadren con los pasos `Int` del modelo en todo el rango `[0, current_step)`. Sin esa comprobación el lema de reflexión no es cierto — y el `validate` de v15 no la hacía.

**Cierre de axiomas:** `[propext, Quot.sound]`. Cero axiomas de proyecto, fijado por `#guard_msgs`.

---

## 2. Ruta D — L6 son dos teoremas, y no valen lo mismo

`L6.lean` enuncia dos propiedades y las trata como un lema:

* `Supported g` — **todo** nodo está en una cadena completa ("sin zombis");
* `Inhabited g` — el grafo denota **algo**.

`AbsSat/GraphPath/Model/Verdict.lean` las separa.

### Qué compra cada una

| | lo consume |
|---|---|
| `Inhabited g` | el **veredicto SAT/UNSAT**: un grafo que sobrevive significa que hay solución |
| `Supported g` | el **lector**: leer una solución nunca entra en un callejón |

### Corrección: un zombi no ralentiza al lector, lo para

**Escribí que un zombi "hace que el lector tenga que retroceder". Es falso y me corregiste:** tu Reader no retrocede. He ido al código y lo confirma línea por línea.

`Reader/PathReader.lean` toma **cualquier** nodo superviviente del paso actual (`ids.toList.head?`), filtra por él, y si ese filtro invalida el grafo pone `error` y **para**. No prueba otro. `Reader/PathExpReader.lean` bifurca por candidato y **una sola rama con error aborta la enumeración entera**. El original en Julia lanza ahí `GRAVE ERROR READER... GPATH INVALID`, y su propio comentario enuncia el invariante de diseño: *todo nodo superviviente es extensible a una solución completa*.

Así que la consecuencia correcta es más grave que la que escribí:

> Un zombi es una **parada en seco**, y en el lector exponencial **destruye el conjunto de soluciones entero**, no un camino.

`Supported` no sostiene una cota de tiempo: es una **precondición de corrección del lector** — la completitud de la enumeración. Tu diseño ya lo decía; yo lo leí mal.

### Lo que sí sobrevive

```lean
theorem denot_has_no_zombies (g : GPathM) (p : List NodeId) (h : denot g p) :
    ∃ sel, IsChain g sel ∧ PairwiseOwned g sel ∧ p = pathOf sel g := h
```

`denot` está definido como el conjunto de cadenas co-poseídas completas, así que un nodo que no está en ninguna no aporta nada. Un zombi **no puede inventar** una solución. La soundness de lo que se lee sobrevive a un zombi; la completitud de la lectura, no.

Y el veredicto tampoco se ve afectado: `DiffTest.run_case` toma SAT/UNSAT de `have_solution` — la validez del grafo — **no del lector**. Así que `Inhabited` sigue siendo exactamente lo que consume el veredicto, y la localización de abajo se mantiene intacta.

### Un hallazgo que sale de tu corrección

Como el lector **re-filtra** después de cada selección, lo que necesita no es `Supported` en el grafo de partida sino `Supported` **preservado por ese filtro**. Lo he dejado enunciado en `Verdict.lean` como `ReadStable`.

Y eso resulta ser **el mismo enunciado abierto del puente** ("filtrar nunca mata una cadena que pasa por un nodo superviviente"), que es la última pieza de L6. Es decir: la corrección del lector y el hueco que queda del puente **no son dos obligaciones, son una**.

### La localización: `Inhabited` es L6 **en un solo nodo**

```lean
theorem Inhabited_iff_SupportedAt (g : GPathM) (hpos : 0 < g.current_step) :
    Inhabited g ↔ ∃ pid, (g.node? pid).isSome ∧ SupportedAt g pid
```

`Supported` es ese mismo `SupportedAt` cuantificado sobre **todos** los nodos. Así que la mitad del problema abierto que sostiene el veredicto no hay que resolverla en general: hay que resolverla **una vez, en un nodo que tú eliges**.

Y eso admite ataques que el enunciado universal no admite. En `Supported` el adversario elige el nodo y tú tienes que aguantar. En `Inhabited` eliges tú — el del paso más alto, o el de conjuntos de owners más pequeños, o el que la estructura del mapa te haga más cómodo.

### Y se certifica mucho más barato

Junto con la ruta C, la consecuencia práctica es concreta:

- certificar `Supported` cuesta **un certificado por nodo**;
- certificar `Inhabited` cuesta **un certificado**, y ya (`Certificate.Inhabited_of_isCert`).

Una ejecución que no pueda pagar lo primero puede pagar lo segundo.

**Cierre de axiomas:** `[propext]` y, en dos de los teoremas, **ningún axioma en absoluto**.

---

## 3. Los números, ahora con otro estatus

`lake exe validate` reporta las dos mitades por separado, y cada línea limpia es un teorema aplicado a ese estado, no un informe de búsqueda.

| campaña | instancias | estados válidos | nodos | `Inhabited` certificado | zombis |
|---|---|---|---|---|---|
| semilla 2026, 3–7 vars | 40/40 | 3.808 | 116.330 | 3.808/3.808 | **0** |
| semilla 31337, 3–9 vars | 200/200 | 23.479 | **1.048.889** | 23.479/23.479 | **0** |

Familias adversarias (las cinco de v15), todas limpias y todas con `Inhabited` certificado en el 100% de sus estados:

| familia | estados | nodos |
|---|---|---|
| literal repetido (`x ∨ x ∨ y`) — **viola `hreqs_distinct`** | 31 | 434 |
| cláusula tautológica | 37 | 626 |
| UNSAT forzado (8 cláusulas / 3 vars) | 41 | 380 |
| transición de fase `m ≈ 4.26n` | 133 | 4.269 |
| cadena implicativa larga | 41 | 1.017 |

---

## 4. Lo que esto NO es

Lo digo entero porque es donde se pierde la gente:

- **L6 sigue abierta.** Nada de esto demuestra que *todo* grafo alcanzable esté libre de zombis. Demuestra que cuando el checker dice que uno concreto lo está, lo está de verdad.
- **Sigue siendo el espejo, no el ejecutable.** El puente `GPath ↔ GPathM` sigue siendo empírico (`diffTest`).
- **Falta el enlace `denot` → asignación.** `Inhabited` te da *una cadena*. Convertir esa cadena en *una solución de la fórmula* es la otra mitad de la afirmación del veredicto, vive en el lado del mapa (L7), y no está demostrada.
- **Los rangos siguen siendo pequeños.** Lo limita tu `S⁴`, no el checker.
- **`ReadStable` está enunciado, no demostrado.** Es la misma diana abierta de siempre, ahora con un nombre y con la razón por la que le importa al lector.

---

## 5. Lo que haría ahora

1. **Meter `validate` en CI junto a `diffTest`.** Ahora ya no es un test de humo: cada ejecución verde es un lote de teoremas. Si alguien toca el filtro o las pasadas de coherencia, se entera antes que los veredictos.
2. **La ruta G** (falsador dirigido por SAT): codificar "grafo válido con un zombi" como instancia SAT y dársela a un solver. Es barato y decide si el esfuerzo debe ir a A (extensibilidad) o a E/F (aciclicidad, leer la asignación de los owners).
3. Si G sale UNSAT hasta tamaños decentes, **atacar `Inhabited` por la localización de §2** antes que `Supported`. Es estrictamente más débil, es lo que sostiene el veredicto, y ahora sabes que basta con un nodo.

---

*Claude (Opus 5), 2026-09-09. Rutas C y D de las siete alternativas discutidas. §2 corregida tras la corrección del autor: el Reader no retrocede. `lake build AbsSat` verde, 55 módulos, 0 `sorry`, todos los `#guard_msgs` de axiomas pasando.*
