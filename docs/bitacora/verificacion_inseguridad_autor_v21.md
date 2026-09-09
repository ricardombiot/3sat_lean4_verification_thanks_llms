# Verificación para el Autor v21: El invariante va en la construcción — y ahí solo queda un caso

Ricardo, soy Claude (Opus 5). Me corregiste el régimen, y la corrección movía más de lo que parecía. Va primero lo que estaba mal, y después lo que ha salido de arreglarlo — que es la mejor forma que ha tenido el ledger hasta ahora.

---

## 1. La corrección

Dijiste tres cosas, y las tres cambian dónde va el argumento:

1. Si la máquina obtiene un **conjunto válido**, tras toda la construcción paso a paso con las revisiones, es porque **hay al menos un certificado** que el Reader podrá leer.
2. El caso **UNSAT se filtra antes de llegar al Reader**: la máquina directamente no puede construir un conjunto solución.
3. El `filter` durante la lectura está ahí porque al seleccionar un nodo válido **se filtran otros caminos válidos** — los que ese nodo no necesita.

En v20 §6 escribí que "la review tiene que poder invalidar, así reporta UNSAT tu máquina". **Eso mezcla dos regímenes distintos.** Es cierto en la **construcción** (`upFiltering`): ahí la invalidación *es* el veredicto. Es falso en la **lectura**: ahí el grafo ya es válido, y una invalidación no sería un veredicto sino **una violación del invariante**.

Retiro esa parte de §6 y la he marcado en el documento y en el código.

---

## 2. Lo que sale de arreglarlo: el invariante enunciado donde va

Tu afirmación (1) no es algo que el Reader tenga que reestablecer. Es un **invariante de la construcción**. Así, en Lean:

```lean
def Certifies : Prop :=
  ∀ g, Reachable reqOf g → isValid g = true → Inhabited g
```

Y enunciado así, se puede hacer la inducción sobre `Reachable` — que tiene tres constructores.

## 3. El ledger, con dos de tres casos cerrados

```lean
theorem Certifies_of_upStep (hup : UpCertifies reqOf) : Certifies reqOf
```

| caso | estado |
|---|---|
| `seed` | **demostrado** — la semilla tiene un nodo, y ese nodo es su propia cadena |
| `join` | **demostrado** — `okJoin` ya exige válidas las dos ramas, y el join solo crece |
| `up` | la obligación |

El caso `join` sale porque tu propio `okJoin` incluye `isValid g₁ && isValid g₂`. Eso es lo que hace usable la hipótesis de inducción en la rama izquierda; sin esa condición no habría salido.

Y para que la inducción pudiera usar su hipótesis en el caso `up` hizo falta un lema que también es tuyo, en el sentido de que sale de cómo está escrito `up`:

```lean
theorem isValid_of_upFiltering (g : GPathM) (reqs : List NodeId) (d : NodeId)
    (title : String) (h : isValid (upFiltering g reqs d title) = true) :
    isValid g = true
```

> **Un `upFiltering` válido solo pudo venir de un grafo válido.**

Porque si el filtro hubiera invalidado, `up` devuelve el grafo invalidado tal cual — no añade nodo. Y porque la validez **solo baja** al podar (`isValid_of_pruned`): quitar owners globales nunca hace válido lo que no lo era.

---

## 4. Qué queda, en una frase

```lean
def UpCertifies : Prop :=
  ∀ g d title, Reachable reqOf g → isValid g = true → Inhabited g →
    isValid (upFiltering g (reqOf d) d title) = true →
    Inhabited (upFiltering g (reqOf d) d title)
```

> Un grafo válido obtenido por `upFiltering` a partir de un grafo válido y certificado, está certificado.

Es la misma pared de siempre. Pero ahora es **la única entrada del ledger**, y está enunciada en el punto donde tu máquina decide UNSAT de verdad — no en la lectura, donde yo la había puesto.

---

## 5. Qué cambia respecto a A′ y a v20

No lo sustituye; lo **coloca**. Ahora hay dos formulaciones de la misma mitad de L6, y conviene ver qué hace cada una:

| | pregunta | dónde vive |
|---|---|---|
| `Certifies` (v21) | ¿por qué un grafo válido tiene certificado? | **construcción** — `upFiltering` |
| `PickValid` (A′, v19–v20) | ¿por qué seleccionar y propagar no lo rompe? | **lectura** |

Tu punto (3) dice que la segunda pregunta es más benigna de lo que yo la trataba: el filtro del Reader **debe** quitar caminos —los que no pasan por el nodo elegido— y eso es su función, no un riesgo. Lo único que no puede hacer es quitarlos **todos**. Y eso es consecuencia de (1) aplicado al nodo elegido.

Así que el orden correcto es: demostrar `UpCertifies` primero. `PickValid` viene detrás, no al revés.

---

## 6. Lo que sigue abierto, sin adornos

- `UpCertifies`. Sin demostrar. Es la pared.
- El caso base de A′ (`NoChoice → Inhabited`). Sin demostrar.
- Todo esto es `Inhabited`, no `Supported`.
- Sigue siendo el espejo, no el ejecutable.

Y lo que no ha cambiado: nada de esto está refutado, y los falsadores llevan 604.178 nodos con propagación y 16.444 estados de descenso sin encontrar una violación.

---

*Claude (Opus 5), 2026-09-09. Corrige la §6 de v20. `lake build AbsSat` verde, 61 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
