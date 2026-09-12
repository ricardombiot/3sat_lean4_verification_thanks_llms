# Verificación para el Autor v51: la rama es un camino del mapa, y llega hasta el final

Ricardo, soy Claude (Opus 5). v50 dejó la ley de conservación demostrada pero con una salvedad honesta: `AlongAssign` describía **una rama**, y faltaba enlazarla con lo que el driver hace de verdad. Esta es esa pieza.

---

## 1. La relación de hijos del mapa, en dos líneas

Leyendo `add_var!`: los dos nodos positivos de una variable se enlazan al bloque de negación **cruzados** —`"v=0"` tiene por hijo `"!v=1"`, y `"v=1"` tiene `"!v=0"`— y en todo lo demás el mapa es **completo** entre pasos consecutivos: cada bloque nuevo se enlaza a *todos* los nodos del paso anterior.

```lean
def mapSons (φ : Cnf) (k : Int) (i : Int) : List NodeId :=
  if k < 0 then []
  else if k < litBlock φ then
    if k % 2 = 0 then [⟨k + 1, 1 - i⟩]      -- el cruce
    else mapNodes φ (k + 1)
  else mapNodes φ (k + 1)
```

## 2. La rama sigue las aristas del mapa

```lean
theorem selOfAssign_son (φ) (a) (hsat : Sat a φ) (k) (h0) (hk) :
    selOfAssign φ a (k + 1) ∈ mapSons φ k (selOfAssign φ a k).index
```

> La secuencia de nodos que nombra una asignación **no es una sucesión elegida a mano: es un camino a lo largo de las aristas del propio mapa**, y cada nodo es hijo del anterior.

Y el caso bonito es el cruce: en un paso de variable la selección está en `⟨2v, bit(a v)⟩`, y su único hijo es `⟨2v+1, 1 − bit(a v)⟩`, que es exactamente `⟨2v+1, bit(¬a v)⟩` — el nodo de negación que le corresponde. **El cruce del mapa y la negación de la asignación son la misma operación.** Eso no lo puse yo, estaba en `add_var!`.

## 3. Y la rama llega hasta el final

```lean
theorem alongAssign_exists (φ) (a) (hwf) (hsat) (hzero) :
    ∀ n, (n : Int) < stepCount φ → ∃ g, AlongAssign φ a g ∧ g.current_step = n + 1

theorem exists_full_valid_state (φ) (a) (hwf) (hsat) (hzero) :
    ∃ g, AlongAssign φ a g ∧ g.current_step = stepCount φ ∧ isValid g = true ∧ Inhabited g
```

> **Una fórmula satisfacible da un estado que las operaciones propias de la máquina alcanzan, que abarca el mapa entero, que sigue siendo válido y que denota una solución.**

Y hay un detalle que merece señalarse: la recursión necesita, en cada paso, saber que el grafo filtrado sigue siendo válido para que `up` tome la rama de `addNode`. Esa validez **la suministra la propia ley de conservación** (`isValid_filterAll_along`). La inducción se alimenta a sí misma: no hay ninguna hipótesis de validez metida a mano.

## 4. Comprobado contra el mapa real, no supuesto

`mapSons` es un modelo; que reproduzca el `sons` que `add_var!` y `add_gate_case!` construyen es una afirmación que hay que verificar. La banda `cnfmap` compara ahora, nodo a nodo, **pasos, conjuntos de nodos, requisitos e hijos**:

| campaña | resultado |
|---|---|
| 40 casos, semilla 2026, 3..7 vars | **40/40**, 0 desacuerdos |
| 120 casos, semilla 90210, 3..8 vars | **120/120**, 0 desacuerdos |
| 40 casos mal formados | 30 saltadas, 10 de acuerdo, **0 desacuerdos** |
| `diffTest` 150, semilla 4242 | **150/150** |

## 5. Qué queda

- **El driver como teorema.** `mirrorRun` está escrito sobre `GMap` (`Std.HashMap`), y razonar sobre él arrastraría `Classical.choice` a todos los cierres. Lo que hay ahora es: la rama es un camino del mapa (demostrado), el modelo de aristas coincide con el mapa real (medido), y las operaciones de la rama son las de la máquina (por construcción de `AlongAssign`). Cerrar el último tramo pediría un driver puro sobre el modelo aritmético, validado diferencialmente — el mismo patrón de siempre, y es trabajo acotado.
- **«Sin zombis»** sigue abierto; lo necesita el lector sin retroceso.
- **Complejidad**: sin un solo teorema.

---

*Claude (Opus 5), 2026-09-10. `lake build AbsSat` verde, 83 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
