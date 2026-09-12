# Verificación para el Autor v57: el ataque a `GoodParentOnCliques` — tres atajos caídos, dos teoremas

Ricardo, soy Claude (Opus 5). Fui a por la demostración de `GoodParentOnCliques`. **No cayó.** Lo que sí salió: tres atajos descartados con números, dos teoremas nuevos, y el residuo partido en tres trozos de tamaños muy distintos.

Te lo cuento en el orden en que ocurrió, incluidos los fallos, porque los fallos son la mitad del valor.

---

## 1. La estructura del problema

`GoodParentOnCliques` pide, para un nodo `p` y una exigencia coherente `S` de sus owners de arriba, **un padre `c`** con dos cosas para cada `a ∈ S`:

- **abajo** — `a ∈ owners c` (el padre ve la exigencia);
- **arriba** — `c ∈ owners a` (la exigencia ve al padre).

Y `Threaded.hop_down` ya da, vía la coherencia de padres `cpar`, que **cada** owner de `p` es owner de **algún** padre. Todo el problema es el intercambio ∀∃ → ∃∀.

## 2. Atajo 1: ¿los padres hermanos son comparables? — **no**

Si los owners de los padres estuvieran anidados por inclusión habría un padre **máximo**, y la mitad *abajo* saldría para toda exigencia de golpe.

| | |
|---|---|
| pares de padres hermanos con owners distintos | 4.274 / 4.980 (dos semillas) |
| de esos, **incomparables** (ni ⊆ ni ⊇) | **4.274 / 4.980 — todos** |

No hay máximo. Atajo muerto.

## 3. Atajo 2: ¿la mitad *arriba* se sigue de la de *abajo*? — **no, pero casi**

Si en esta configuración concreta —`c` padre de `p`, `a` mutuamente poseído con `p`, `a ∈ owners c`— siempre valiera `c ∈ owners a`, media hipótesis desaparecería.

| campaña | configuraciones | **falla arriba** |
|---|---|---|
| 10 casos, 2026, 3..6 vars | 175.294 | **0** |
| 10 casos, 31337, 4..7 vars | 594.332 | **38** |

La primera semilla lo habría dado por bueno. La segunda lo refuta: 38 fallos, 37 de ellos a distancia ≥ 2 por encima de `p`. Atajo muerto — **y es exactamente por qué hay que correr más de una semilla antes de escribir Lean.**

Pero el mismo dato trae la buena noticia:

| | |
|---|---|
| configuraciones en nodos con **un solo padre** | 473.730 |
| de esas, falla arriba | **0** |

**Los 38 fallos están todos en nodos que ramifican.** Sin ramificación, las dos mitades van juntas.

## 4. Teorema 1: el nodo que no ramifica entrega todo a su padre

```lean
theorem owners_subset_of_unique_parent (g : GPathM) (ctx : TCtx g)
    (p : PathNodeId) (d : PNodeM) (hd : g.node? p = some d)
    (hlo : 0 < p.id.step) (hhi : p.id.step < g.current_step)
    (c : PathNodeId) (hpar : d.parents = [c]) (m : PNodeM) (hm : g.node? c = some m)
    (q : PathNodeId) (hq : q ∈ d.owners)
    (hqlo : 0 ≤ q.id.step) (hqhi : q.id.step < g.current_step) :
    q ∈ m.owners
```

> `hop_down` dice que cada owner de `p` es owner de *algún* padre. Con **un** padre no hay nada que elegir: **`owners p ⊆ owners c`**, el conjunto entero de una vez.

Esa es la mitad *abajo* de `GoodParentOnCliques`, demostrada, en el 80 % de las configuraciones. Cierre `[propext, Quot.sound]`.

## 5. Atajo 3: ¿y si ningún nodo tiene más de dos padres? — **casi**

Si los padres fueran a lo sumo dos, la familia «padres buenos para `a`» viviría en un conjunto de dos elementos, donde **intersección dos a dos implica intersección global** (Helly, trivial). El caso general se reduciría a los **pares**.

| | |
|---|---|
| máximo de padres de un nodo | **4** |
| nodos con 3 o más padres | **19 de 19.931** y **27 de ~20.000** |

No es universal, pero es el **0,1 %**. Así que el atajo vale para el 99,9 % de los nodos que ramifican, y eso sí merecía un teorema.

## 6. Teorema 2: Helly sobre dos padres

```lean
theorem good_of_pairwise_two {α : Type} (good : PathNodeId → α → Bool)
    (c₁ c₂ : PathNodeId) (l : List α)
    (hpair : ∀ a ∈ l, ∀ b ∈ l,
      ((good c₁ a && good c₁ b) || (good c₂ a && good c₂ b)) = true) :
    (∀ a ∈ l, good c₁ a = true) ∨ (∀ a ∈ l, good c₂ a = true)
```

> Si **cada par** de la exigencia tiene un padre bueno para ambos, **un** padre es bueno para toda la exigencia.

La demostración es todo el contenido del caso de dos elementos: si `c₁` falla en algún punto, todo par que pase por ahí lo tiene que llevar `c₂`, luego `c₂` lo lleva todo. Cierre `[propext, Quot.sound]`.

## 7. Dónde queda el residuo, partido en tres

| trozo | tamaño medido | estado |
|---|---|---|
| nodos con **un** padre, mitad *abajo* | 80 % de las configuraciones | **demostrado** (teorema 1) |
| nodos con un padre, mitad *arriba* | 473.730 configuraciones | 0 fallos, sin demostrar |
| nodos con **dos** padres | 99,9 % de los que ramifican | reducido a **pares** (teorema 2) |
| nodos con **3 o 4** padres | **0,1 %** (19 y 27 nodos) | Helly de verdad, abierto |

Es decir: **el enunciado abierto ya no es «para toda exigencia», es «para cada par de owners»** en casi todos los nodos, más un residuo del 0,1 % donde hace falta una propiedad de Helly genuina.

## 8. Lo que esto no es

- **`GoodParentOnCliques` sigue sin demostrar.** Fui a por ella y no cayó.
- Los dos teoremas nuevos son piezas, no la demostración: uno cubre una mitad en los nodos que no ramifican, el otro reduce los que ramifican a pares.
- Los tres atajos están refutados con números, no descartados por intuición. Uno de ellos (el atajo 2) **habría pasado con la primera semilla**.
- Instancias de 3 a 7 variables. Complejidad, sin teoremas.

## 9. Estado

| | |
|---|---|
| Mitad de completitud (conservación + driver) | cerrada |
| S1 / S2 | cerrados |
| `GoodParentOnCliques` ⟹ `ExtendDownTop` ⟹ `Inhabited` | **demostrado** |
| Padres hermanos comparables | **refutado** (todos incomparables) |
| *Arriba* se sigue de *abajo* | **refutado** (38 de 594.332) |
| *Arriba* en nodos sin ramificación | 0 de 473.730 |
| Todo nodo tiene ≤ 2 padres | **refutado** (máximo 4; el 0,1 % tiene ≥3) |
| `owners p ⊆ owners c` con padre único | **demostrado** |
| Helly sobre dos padres | **demostrado** |
| `GoodParentOnCliques` | abierto — reducido a pares salvo el 0,1 % |
| Complejidad | sin teoremas |

`lake build AbsSat` verde, 85 módulos, 0 `sorry`, 0 axiomas de proyecto.

---

*Claude (Opus 5), 2026-09-11.*
