# Verificación para el Autor v20: `PickValid`, molida hasta una sola eliminación de nodo

Ricardo, soy Claude (Opus 5). Atacada `PickValid`, la única obligación que dejó A′. No la he demostrado. Lo que he hecho es **quitarle mitades demostrables hasta dejar el hueso**, y decirte exactamente cuál es el hueso y por qué no se puede rodear.

---

## 1. La mitad que era gratis: pinchar nunca invalida

`PickValid` dice: seleccionar un nodo de mapa permitido y propagar deja el grafo válido. Y `filterAll g [mid] = review (filterRequire g mid)` — son **dos** operaciones. Resulta que la primera es inofensiva:

```lean
theorem isValid_filterRequire (g : GPathM) (req : NodeId) (q₀ : PathNodeId)
    (hq₀ : q₀ ∈ g.gowners) (hq₀id : q₀.id = req) (hv : isValid g = true) :
    isValid (filterRequire g req) = true
```

La razón es sencilla cuando se mira el filtro: para los pasos distintos de `req.step` el predicado es verdadero de entrada, así que **no toca nada**; y en el paso de `req` sobrevive justo el owner que has elegido. Ningún paso se queda sin owner global.

> Consecuencia: **toda la dificultad de `PickValid` está en `review`**, no en el pinchazo.

## 2. Y la obligación se puede estrechar

El descenso de A′ solo elige en pasos donde los owners globales **todavía discrepan**. En un paso ya determinado, el filtro se lo queda todo:

```lean
theorem filterRequire_eq_self_of_pinned (g : GPathM) (req : NodeId)
    (h : ∀ q ∈ g.gowners, q.id.step = req.step → q.id = req) :
    filterRequire g req = g
```

Así que he metido la guarda `choiceAt` en la definición de `PickValid`. Obligación estrictamente menor, sin debilitar el teorema de A′.

---

## 3. De `review` a **una pasada**

```lean
theorem isValid_review_of_pass (Q : GPathM → Prop)
    (hQpass : ∀ g, Q g → Q (reviewPass g))
    (hQvalid : ∀ g, Q g → isValid g = true → isValid (reviewPass g) = true)
    (g : GPathM) (hQ : Q g) (hv : isValid g = true) : isValid (review g) = true
```

El bucle de fuel comprueba `isValid` antes de cada pasada y **para en cuanto el grafo se invalida**. Así que si una pasada preserva la validez dentro de una clase donde el bucle se queda, la review entera también.

*(Este sale sin ningún axioma. Ni `propext`.)*

## 4. De una pasada a **una eliminación**

La validez es una propiedad de `gowners`, y `gowners` solo mengua por `removeNode`, que quita exactamente un id:

```lean
theorem isValid_removeNode_of_other (g : GPathM) (id : PathNodeId)
    (h : ∀ k, 0 ≤ k → k < g.current_step → ∃ q ∈ g.gowners, q.id.step = k ∧ q ≠ id) :
    isValid (removeNode g id) = true
```

---

## 5. La escalera, entera

```
Inhabited g
  ⟸ Inhabited_of_pickValid       PickValid + caso base sin elección   (v19)
  ⟸ isValid_filterRequire        el pinchazo es inofensivo → solo queda review
  ⟸ isValid_review_of_pass       el bucle de fuel se reduce a una pasada
  ⟸ isValid_removeNode_of_other  una pasada se reduce a una eliminación
```

Y lo que queda debiendo, en una frase:

> **Ninguna eliminación que haga la review es el último owner global de su paso.**

---

## 6. El límite de esta ruta ⚠ **corregido por v21**

```lean
theorem not_isValid_removeNode_of_only (g : GPathM) (id : PathNodeId) (k : Int)
    (hlo : 0 ≤ k) (hhi : k < g.current_step)
    (h : ∀ q ∈ g.gowners, q.id.step = k → q = id) :
    isValid (removeNode g id) = false
```

Lo demostré para marcar la frontera: eliminar el último owner global de un paso invalida el grafo. Eso es cierto.

**Lo que escribí a continuación no lo era.** Dije que "la review tiene que poder invalidar — así reporta UNSAT tu máquina — así que `PickValid` no se puede demostrar haciendo imposibles las eliminaciones". Me corregiste, y con razón: **UNSAT se decide en la construcción**, en `upFiltering`. Una fórmula insatisfacible no llega nunca a producir un conjunto válido. Los picks de los que habla `PickValid` ocurren sobre un grafo **ya válido** — el régimen del Reader — y ahí una invalidación **no es un veredicto, es una violación del invariante**.

Mezclé los dos regímenes. La corrección está en [v21](./verificacion_inseguridad_autor_v21.md), y lo que queda de este §6 es solo la forma exacta del fallo a descartar: un paso dejado a cero.

## 7. La circularidad, contada antes de que la encuentres tú

Hay un camino corto a `PickValid`, y lo he demostrado también:

```lean
theorem isValid_filterAll_of_ChainSound (g : GPathM) (mid : NodeId)
    (sel : Int → PathNodeId) (h : ChainSound (filterRequire g mid) sel) :
    isValid (filterAll g [mid]) = true
```

Si el grafo pinchado todavía tiene una cadena sonora, `review` la preserva (`ChainSound_review`, ya demostrado en su día) y una cadena dentro de los owners globales hace válido el grafo. Perfecto — salvo que la hipótesis *es* L6 leída a nivel de mapa.

**Así que hay que decirlo sin adornos: A′ no reduce L6 a algo más débil. La reempaqueta en un enunciado de un paso.**

Lo que sí gana el reempaquetado, y no es poco:

1. Un enunciado de un paso es atacable por **combinatoria de `review`**, que es finita y explícita, en vez de por existencia de un objeto global.
2. La mitad del pinchazo ya está **fuera de la cuenta**, demostrada.
3. El bucle de fuel también.
4. Y queda una obligación sobre `removeNode`, que es una línea de código.

---

## 8. Lo que sigue abierto

- La obligación de §5. Sin demostrar.
- El caso base de A′ (`NoChoice → Inhabited`). Sin demostrar.
- Sigue siendo `Inhabited`, no `Supported`.
- Sigue siendo el espejo, no el ejecutable.

Nada de esto está refutado, y el falsador con propagación lleva 604.178 nodos y 16.444 estados sin encontrar una violación.

---

*Claude (Opus 5), 2026-09-09. **§6 corregida por v21** (mezclé el régimen de construcción con el de lectura). `lake build AbsSat` verde, 60 módulos, 0 `sorry`. Cierres: `[propext, Quot.sound]`, y `isValid_review_of_pass` sin ningún axioma.*
