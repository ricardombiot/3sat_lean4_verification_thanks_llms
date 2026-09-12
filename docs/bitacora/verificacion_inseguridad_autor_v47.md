# Verificación para el Autor v47: el espejo inverso, y con él dos huecos cerrados

Ricardo, soy Claude (Opus 5). El hueco estructural que llevaba tres documentos nombrado —el espejo inverso de la tabla de hijos— **está demostrado**. Con él caen los dos agujeros que dependían de él: el paso 0 del enhebrado y la cláusula `son`.

---

## 1. Dos invariantes nuevos

```lean
def SN (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ s ∈ n.sons, GownersNodes.HasNode h s

def PMS (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ s ∈ n.sons, ∀ m ∈ h.nodes, m.id = s → n.id ∈ m.parents

theorem SN_reachable  (g) (h : Reachable reqOf g) : SN g
theorem PMS_reachable (g) (h : Reachable reqOf g) : PMS g
```

`SN` es el espejo de `Parents.PN` (los hijos son nodos); `PMS` es el converso de `SMP` — *si `s` es hijo de `n`, entonces `n` es padre de `s`*. Cierres `[propext, Quot.sound]`.

**Y hay algo que merece contarse sobre cómo salió.** Toda la mitad de poda de `PMS` —`updateAt`, `removeNode`, **`unlinkIncompatible`**, las tres barridas de la review, el bucle de fuel, `filterAll`— es el calco literal de las demostraciones de `SMP` con `parents` y `sons` intercambiados. Compiló entera sin tocar una línea.

Eso no es casualidad ni suerte: **es tu arreglo del bug**. `unlinkIncompatible` desenlaza *por los dos lados* con los mismos owners decidiendo, así que la demostración es simétrica bajo el intercambio. Antes de v37 esa simetría no existía y el calco no habría compilado.

Lo único que hubo que escribir a mano fue `addNode` — la única operación que crea enlaces, y por tanto la única con contenido propio.

## 2. Hueco cerrado 1: el paso 0 del enhebrado

v42 dejó `threaded` con la hipótesis `1 ≤ a.id.step`, porque `reviewSons` barre los pasos `1 .. current_step-2` y nunca el 0, así que la subida no podía arrancar ahí. `PMS` hace el primer salto sin `coherent_sons`:

```lean
theorem hop_up_zero (g) (ctx) (a) (n) (hn) (hz : a.id.step = 0) (hpos : 1 < g.current_step) :
    ∃ c m, g.node? c = some m ∧ a ∈ m.owners ∧ c.id.step = 1
```

Un hijo del nodo del ancla tiene al ancla entre sus **padres** (`PMS`), y el puente de v39 convierte un padre en owner. `SAbove` pone el paso.

**Así que `threaded` pierde la hipótesis:**

```lean
theorem threaded (g) (ctx) (a) (n) (hn) (hself) (halo : 0 ≤ a.id.step) (hahi) :
    ∃ sel, IsChain g sel ∧ ∀ i en rango, a ∈ ownersOf g (sel i)
```

> **Todo** nodo está en un camino completo del paso 0 a la cima cuyos nodos lo poseen todos. Sin excepciones.

Y con ello `pinSet_covers` deja de tener la salvedad: el conjunto candidato cubre todos los pasos para **cualquier** elección permitida, incluidas las 3.090 de cada 63.314 que están en el paso 0.

## 3. Hueco cerrado 2: la cláusula `son`

```lean
theorem son_of_hop_up (g) (tctx) (k mid) … (p n) (hn) (hp : PinSet g k mid p)
    (hlo : 1 ≤ p.id.step) (hhi : p.id.step ≤ g.current_step - 2) :
    ∃ c m, PinSet g k mid c ∧ g.node? c = some m ∧ p ∈ m.parents
```

`hop_up` da un hijo que sigue siendo candidato; `PMS` da la vuelta a ese enlace de hijo y produce el enlace de padre que `Closed.son` pide. **Por encima del paso 0 la cláusula deja de ser hipótesis.**

Lo que no alcanza: un candidato en el **paso 0** con el pinchazo en otro sitio. Ahí `coherent_sons` sigue callado y nada obliga al hijo a seguir siendo candidato. Es un hueco mucho más pequeño que el de ayer, y está dicho con precisión.

## 4. Estado

| | |
|---|---|
| `SN`, `PMS` | **demostrados**, toda la máquina |
| Paso 0 del enhebrado | **cerrado** — `threaded` sin hipótesis de paso |
| `pinSet_covers` | ahora sin salvedad |
| Cláusula `son` para pasos ≥ 1 | **cerrada** (`son_of_hop_up`) |
| Cláusula `son` en el paso 0 con pinchazo en otro paso | abierto (hueco pequeño, nombrado) |
| `support` a distancia ≥ 2 | abierto — 0 fallos en 3,47 M |
| `CoreCovers`, `PickValid`, `PairwiseOwned` | abiertos, y son el mismo enunciado |

`lake exe diffTest 200` sigue en 200/200; el ejecutable no se ha tocado.

---

*Claude (Opus 5), 2026-09-10. `lake build AbsSat` verde, 74 módulos, 0 `sorry`, cierres `[propext, Quot.sound]` o más finos.*
