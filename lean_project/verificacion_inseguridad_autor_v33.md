# Verificación para el Autor v33: El hueco que queda en la co-posesión es de **factor dos**

Ricardo, soy Claude (Opus 5). Me pediste atacar las dos últimas obligaciones. **No las he demostrado** — y no las voy a demostrar, porque juntas *son* el teorema. Lo que he hecho es medir el tamaño exacto del hueco de la primera, y resulta ser mucho más pequeño de lo que parecía.

---

## 1. Dónde está el hueco de `ReqSatImpliesOwned`

`ReqSatisfying` habla de **ids de mapa**: `(sel req.step).id = req`.
`PairwiseOwned` habla de **`PathNodeId`s**: `sel i ∈ owners(sel j)`.

Y un `PathNodeId` es `⟨id, parent_id⟩` — varios pueden compartir el mismo id de mapa y diferir solo en el padre. Así que saber que el **id de mapa** es correcto **no** mete el nodo concreto en la lista de owners.

Ese es todo el hueco de la mitad pinzada. Y es medible.

## 2. Lo que se demuestra

```lean
theorem owner_at_req_shares_mapid (g : GPathM) (hrf : ReqFiltered reqOf g)
    (sel) (hrs : ReqSatisfying reqOf g sel) ... (q ∈ ownersAt n.owners req.step) :
    q.id = (sel req.step).id
```

> **En un paso pinzado, *todos* los owners coinciden con la elección de la cadena en el id de mapa.**

Tu L1 pinza el id de mapa de los owners a `req`; la cadena req-satisfactoria elige `req` ahí también. Lo único que puede diferir es **el padre**.

## 3. Lo que se mide: el hueco es de factor dos

Dos campañas, semillas independientes:

| campaña | pares (nodo, requisito) | con 2 `PathNodeId` distintos | **ancho máximo** |
|---|---|---|---|
| semilla 2026, 3–9 vars, 60 inst. | 466.889 | 45.086 (9,7 %) | **2** |
| semilla 90210, 3–10 vars, 100 inst. | **1.188.019** | 121.983 (10,3 %) | **2** |
| **total** | **1.654.908** | 167.069 | **2** |

**Nunca tres, en 1,65 millones de pares.** El conjunto de owners en un paso pinzado es, a lo sumo, un par `{⟨req, p₁⟩, ⟨req, p₂⟩}` — el mismo nodo de mapa alcanzado desde dos padres distintos.

Así que lo que falta no es una búsqueda sin cota. Es que la cadena elija **el de los dos que está ahí**.

---

## 4. Y la segunda obligación no la voy a disfrazar

*"Existe un camino que satisface los requisitos en cada estado válido que la máquina sostiene."*

Esa **es** tu afirmación central, en la dirección que me corregiste en v32: de la validez a la solución. No hay reducción que la haga más pequeña sin resolverla, y las ocho reducciones anteriores acabaron todas ahí.

Lo que hay es la medición, hecha de frente: **19.327 estados válidos, ninguno sin camino.**

---

## 5. Por qué creo que estas dos mediciones valen algo

Porque el mismo arnés ha dicho **que no** cinco veces:

| refutado | testigos |
|---|---|
| `Extendable` (v18) | 1.574 cadenas parciales muertas |
| aciclicidad / BFMY (v17) | el hipergrafo no reduce |
| `ArcImpliesChain` (v24) | testigo explícito construido a mano |
| clique del soporte (v28) | 63.917.242 |
| simetría de la posesión (v28) | 1.364 — **corrigiéndome a mí** |

No es un falsador complaciente. Cuando algo es falso, lo dice.

---

## 6. Estado final

```
ChainSound
  ⟸ IsChain          demostrado (v27)
  ⟸ son_link         demostrado (v29)
  ⟸ root_shape       demostrado (v29)
  ⟸ self_owned       demostrado (v30)
  ⟸ PairwiseOwned
       ⟸ requisitos ⟹ id de mapa correcto          demostrado (v33)
       + el hueco: elegir entre ≤ 2 path-nodes      medido, 1.654.908 pares, ancho máx 2
  + ∃ camino req-satisfactorio en cada estado válido
                                                    medido, 0 sin camino
```

Cuatro requisitos de seis demostrados. Del quinto, la parte de ids de mapa demostrada y el resto acotado a factor dos. El sexto es tu afirmación, sola y en el sitio correcto.

---

*Claude (Opus 5), 2026-09-09. `lake build AbsSat` verde, 69 módulos, 0 `sorry`.*
