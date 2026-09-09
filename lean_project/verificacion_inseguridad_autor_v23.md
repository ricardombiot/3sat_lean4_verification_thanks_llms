# Verificación para el Autor v23: La obligación final, dicha en la moneda clásica

Ricardo, soy Claude (Opus 5). Atacado `ReqChain`. No está demostrado — pero se ha debilitado tres veces seguidas, y la última versión ya no contiene **nada** específico de tu máquina. Es el enunciado clásico de CSP, y creo que ese es el sitio donde por fin se puede pelear.

---

## 1. Se podía pedir menos

`ReqChain` pedía: una cadena sonora **de `g`** que satisfaga los requisitos.

Pero seguí qué hace `ChainSound_upFiltering` con esa cadena, y la respuesta es: la mete inmediatamente por `ChainSound_filterAll` y **solo usa el resultado**. La cadena en `g` nunca vuelve a aparecer.

Así que la obligación se puede enunciar un paso más tarde, sobre el grafo **filtrado**:

```lean
def FilteredChain : Prop :=
  ∀ g d, Reachable reqOf g → isValid g = true → (∃ sel, ChainSound g sel) →
    isValid (filterAll g (reqOf d)) = true →
    ∃ sel, ChainSound (filterAll g (reqOf d)) sel
```

Y es **estrictamente más débil**: `ReqChain_gives_FilteredChain` lo demuestra en una dirección, y la vuelta necesitaría transferir `ChainSound` hacia atrás a través de una poda, cosa que nada suministra. Es debilitamiento real, no reetiquetado.

## 2. Y entonces todo colapsa a un solo enunciado

Con eso, las seis obligaciones que he ido persiguiendo —`Supported`, `Extendable`, `PickValid`, `UpCertifies`, `ReqChain`, `FilteredChain`— resultan ser **el mismo enunciado sobre grafos distintos**:

```lean
def ValidHasChain (h : GPathM) : Prop := isValid h = true → ∃ sel, ChainSound h sel
```

> Un grafo válido lleva una cadena sonora.

Que es, palabra por palabra, lo que me dijiste tú: *"si la máquina obtiene un conjunto válido es porque hay al menos un certificado"*.

## 3. Y `FilteredChain` lo necesita en la clase más estrecha de todas

Los grafos de los que habla `FilteredChain` son los `filterAll g reqs`. Y esos son **puntos fijos de `review`**:

```lean
theorem filterAll_is_review_fixpoint (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAll g reqs) = true) :
    review (filterAll g reqs) = filterAll g reqs
```

Eso importa, porque el punto fijo es exactamente donde valen las propiedades de consistencia que ya estaban demostradas hace días — `review_node_valid`, `review_owners_within_gowners`, `review_owners_coherent_parents` / `_sons` en `Fuel.lean`, y la estructura `ArcConsistent` de `ArcConsistency.lean`.

---

## 4. La obligación final

```lean
def ArcImpliesChain : Prop :=
  ∀ h : GPathM, ArcConsistent reqOf h → isValid h = true → review h = h →
    ∃ sel, ChainSound h sel

theorem Certifies_of_ArcImpliesChain (h : ArcImpliesChain reqOf) : Certifies reqOf
```

Y las dos hipótesis nuevas **están demostradas** de todos los grafos a los que se aplica:

- `arcConsistent_filterAll` — los intermedios filtrados heredan `ReqFiltered` de `g` (lema L1 más `filterAll_preserves_ReqFiltered`), y el punto fijo pone el resto.
- `filterAll_is_review_fixpoint` — arriba.

Así que añadir hipótesis aquí es progreso de verdad: la obligación es más fácil, y su contexto está pagado.

### Lo que ya no queda dentro

Nada de `addNode`. Nada del bucle de fuel. Nada de `join`, ni de la semilla, ni de `MachineOk`, ni de rangos de nodos. **Ni siquiera `Reachable`.** Todo eso está demostrado.

Lo que queda es el enunciado clásico:

> **Consistencia local ⟹ solución global.**

---

## 5. Dónde deja esto el trabajo del mapa

Ese enunciado es **falso para redes de restricciones arbitrarias**. Por eso todo el proyecto se reduce a la *clase* de redes que construye tu `ImportCnf` — y de esa clase ya hay algo demostrado desde el 8 de septiembre:

```lean
def Functional (rs : SetNodesId) : Prop :=
  ∀ r₁ ∈ rs, ∀ r₂ ∈ rs, r₁.step = r₂.step → r₁ = r₂
```

`GraphMap.MapReqs` demuestra que tu construcción **solo genera requisitos 0/1/all**.

**Y aquí hay que ser preciso, porque v13 sigue en pie.** `ArcConsistent` tiene cuatro cláusulas: la cláusula `pinned` es `ReqFiltered` — la propiedad L1, que habla de los **requisitos**, donde el 0/1/all vive y está demostrado. Las otras tres (`supported`, `coherent_parents`, `coherent_sons`) hablan de las **tablas `owners`**, y de esas v13 demostró con 164 testigos que **no** heredan la forma 0/1/all.

Así que no digo que CCJ ya aplique. Digo esto, que es menos y es cierto:

> Es el primer enunciado del proyecto donde la estructura de los requisitos y la propagación de las tablas son hipótesis de **la misma proposición**. Antes vivían en módulos que no se tocaban.

---

## 6. La escalera de debilitamientos, entera

| obligación | implica la siguiente | estado |
|---|---|---|
| `Supported` (L6) | — | la original |
| `Inhabited` | mitad del veredicto (v16) | ✔ localizada |
| `UpCertifies` | invariante de construcción (v21) | ✔ seed y join saldados |
| `ReqChain` | v22 | ✔ condiciones laterales saldadas |
| `FilteredChain` | `ReqChain_gives_FilteredChain` | ✔ estrictamente más débil |
| **`ArcImpliesChain`** | hipótesis demostradas de su clase | **la que queda** |

Cada paso quita hipótesis del lado de la máquina y las mete en el lado demostrado. Lo que queda no se puede recortar más sin resolverlo.

---

## 7. Abierto

- `ArcImpliesChain`. Sin demostrar, y es la pared. Pero ahora es una pared con nombre clásico y con toda la fontanería descontada.
- Sigue siendo `Inhabited`, no `Supported`.
- Sigue siendo el espejo, no el ejecutable.
- Y sigue sin estar refutado: 1.048.889 nodos verificados, 604.178 con propagación exhaustiva, 0 violaciones.

---

*Claude (Opus 5), 2026-09-09. `lake build AbsSat` verde, 61 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
