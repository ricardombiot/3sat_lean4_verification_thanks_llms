# Verificación para el Autor v55: el veredicto, con la mitad refutada fuera

Ricardo, soy Claude (Opus 5). v54 localizó el residuo en el descenso. Este informe hace dos cosas con eso: **mide el enunciado exacto** (no la regla golosa, sino todas las cadenas) y **demuestra en Lean la reducción**, dejando fuera la mitad que estaba refutada.

---

## 1. El reparo que había que hacer antes de escribir Lean

`Extendable.lean` ya reducía «sin zombis» a que nada se atasque en **las dos direcciones**:

```lean
Supported_of_Extend : NodesInRange g → ExtendUp g → ExtendDown g → Supported g
```

y de esas dos, **ambas estaban refutadas**: 1.574 cadenas parciales sin continuación, de las cuales 1.517 subiendo y **57 bajando**. Así que mi medición golosa de v54 no bastaba: `ExtendDown` cuantifica sobre *toda* cadena parcial consistente, y el descenso goloso solo explora una por ancla.

Pero mirando cómo se usa `hdown` en la demostración compuesta, se ve algo: **solo se aplica a cadenas que ya llegan al paso más alto**, porque `extendUpTo` corrió antes. Ese es un subconjunto estricto, y es justo el que recorre el lector.

## 2. El enunciado correcto, medido exhaustivamente

```lean
def ExtendDownTop (g : GPathM) : Prop :=
  ∀ sel lo, 0 < lo → lo ≤ g.current_step - 1 →
    PartialChain g sel lo (g.current_step - 1) →
    PartialOwned g sel lo (g.current_step - 1) →
    ∃ c, PartialChain g (upd sel (lo - 1) c) (lo - 1) (g.current_step - 1) ∧
         PartialOwned g (upd sel (lo - 1) c) (lo - 1) (g.current_step - 1)
```

`lake exe extend --randomdowntop` explora, desde **cada** nodo del paso alto, **todas** las cadenas parciales hacia abajo — enlazadas padre→hijo y mutuamente poseídas con todo lo elegido — y cuenta las que se quedan sin continuación por encima del paso 0:

| campaña | estados válidos | anclas altas | cadenas hasta el paso 0 | búsquedas cortadas | **callejones** |
|---|---|---|---|---|---|
| 8 casos, 2026, 3..5 vars | 472 | 657 | 1.095 | 0 | **0** |
| 12 casos, 31337, 3..6 vars | 1.069 | 1.673 | 4.324 | 0 | **0** |
| 10 casos, 4242, 4..6 vars | 834 | 1.389 | 3.912 | 0 | **0** |
| 10 casos, 90210, 5..7 vars | 967 | 1.674 | 6.424 | 0 | **0** |
| **total** | **3.342** | **5.393** | **15.755** | **0** | **0** |

**15.755 cadenas, cero callejones, ninguna búsqueda cortada por presupuesto.** No es la regla golosa: es exhaustivo.

## 3. La reducción, demostrada

Y ahora la parte que sí es teorema. `Verdict.lean` ya había registrado que **`Inhabited` no necesita `Supported`**: necesita una cadena por **un** nodo a tu elección. Elige uno del paso más alto y `extendUpTo` se vuelve vacío.

```lean
theorem Inhabited_of_ExtendDownTop (g : GPathM) (hgn : GownersNodes.GN g)
    (hpos : 0 < g.current_step) (hval : isValid g = true) (hdown : ExtendDownTop g) :
    Inhabited g
```

> `isValid` pone un owner global en el paso alto, `GN` lo convierte en nodo, el descenso lo enhebra hasta el paso 0, y `Verdict.Inhabited_of_SupportedAt` convierte esa única cadena en la denotación.

Cierre `[propext, Quot.sound]`, 0 `sorry`. Y lo que importa: **`ExtendUp` no aparece**. La mitad refutada sale de la cuenta.

Módulo nuevo `Model/DownVerdict.lean` — vive aparte porque `PickInduction` importa `Extendable`, así que el ensamblaje no cabía en ninguno de los dos. Con `SupportedAt_top_of_ExtendDownTop` y `extendDownTopTo` en `Extendable.lean`.

## 4. Dónde queda el problema abierto

Antes de v54 el objetivo era `Supported`: *todo* nodo está en *alguna* cadena completa co-poseída, con las dos direcciones y las dos refutadas en su forma manejable.

Ahora es **una sola hipótesis, en una sola dirección, sobre un subconjunto estricto de cadenas**, y con una reducción al veredicto demostrada en Lean. Lo que falta para demostrarla se ve con precisión: `Threaded.hop_down` ya da, para **cada** owner `a` de un nodo, **algún** padre que posee `a`. `ExtendDownTop` pide intercambiar los cuantificadores: **algún** padre que posea **todos** los de la historia. Ese intercambio ∀∃ → ∃∀ es el residuo, ahora desnudo.

Un dato que orienta hacia dónde mirar: 5.393 anclas producen solo 15.755 cadenas — menos de tres por ancla. **El descenso es casi determinista**, y la razón es estructural: los padres de un nodo `p` comparten todos el mismo id de mapa, el que `p.parent_id` codifica. Solo se ramifica la decoración. Si esa ramificación resultara irrelevante para la posesión, el intercambio de cuantificadores sería inmediato.

## 5. Lo que esto **no** es

- **`ExtendDownTop` sigue sin demostrar.** Lo que hay es una hipótesis que sobrevivió la medición que mató a sus dos predecesoras, y una reducción al veredicto que sí es teorema.
- La reducción **no dice que la máquina mantenga `ExtendDownTop`** al filtrar: eso es la obligación del lector no-retrocedente (`Verdict.ReadStable`), y sigue siendo la misma pregunta.
- Instancias de 3 a 7 variables. No hay teoremas de complejidad.

## 6. Estado

| | |
|---|---|
| Mitad de completitud (ley de conservación + driver) | cerrada |
| S1 / S2 (camino leído es solución / vacío ⟹ UNSAT) | cerrados |
| `ExtendUp` | **refutado** (1.517 callejones) |
| `ExtendDown` general | **refutado** (57 callejones) |
| **`ExtendDownTop`** | **0 callejones en 15.755 cadenas** |
| `ExtendDownTop` ⟹ `Inhabited` | **demostrado** |
| `ExtendDownTop` en sí | abierto — el intercambio ∀∃ → ∃∀ sobre los padres |
| Complejidad | sin teoremas |

`lake build AbsSat` verde, **85 módulos**, 0 `sorry`, 0 axiomas de proyecto.

---

*Claude (Opus 5), 2026-09-11.*
