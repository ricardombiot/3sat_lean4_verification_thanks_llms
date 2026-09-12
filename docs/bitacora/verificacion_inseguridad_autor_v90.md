# Verificación para el Autor v90: `CoherentParents` y `OwnersGlobal`, demostrados para el review simétrico

Ricardo, soy Claude (Opus 5). Hechos los dos campos que faltaban. Y de paso salieron cuatro más,
porque la pieza que había que construir —el punto fijo del review simétrico— los daba todos.

---

## 1. Lo que faltaba y por qué costaba

`Fuel.lean` demuestra, para tu `review` original, algo más fino que «la medida dejó de moverse»:
demuestra que el estado que el bucle deja válido es un **punto fijo de la pasada**. De ahí lee los
dos hechos por nodo que v88 necesitaba. Para el review simétrico no había nada de eso, porque el
paso espejo se mete entre la intersección y el desenlace y rompe todas las formas.

Así que la cadena hay que rehacerla con una junta nueva:

```lean
theorem symmetrize_eq_self (g) (h : measure (symmetrize g id) = measure g) :
    symmetrize g id = g
```

**El paso espejo, en el punto fijo, es la identidad.** Con eso, el resto repite las formas de
`Fuel.lean` con una operación más en medio: `symIntersectOrDrop` (intersecta, espeja, desenlaza, y
tira el nodo si quedó inválido), su rama válida, `cleanStepSym`, `cleanInvalidGoSym`,
`reviewNodeSym`, las líneas, los pasos, la pasada, y el bucle.

El corazón:

```lean
theorem reviewPassSym_reviewSym (g) (h : isValid (reviewSym g) = true) :
    reviewPassSym (reviewSym g) = reviewSym g
```

## 2. Los dos campos

```lean
theorem CoherentParents_reviewSymTri (g) (hv : isValid (reviewSymTri g) = true) :
    FabricAdd.CoherentParents (reviewSymTri g)          -- [propext, Quot.sound]

theorem OwnersGlobal_reviewSymTri (g) (hv : isValid (reviewSymTri g) = true) :
    FabricAdd.OwnersGlobal (reviewSymTri g)             -- [propext, Quot.sound]
```

Y el puente que los lleva de la máquina simétrica a la **unida** es una sola observación, y me
gustó encontrarla:

```lean
theorem reviewSymTriFuel_eq_reviewSym : ∀ fuel g, measure g < fuel →
    ∃ h, reviewSymTriFuel fuel g = reviewSym h
```

> **Todo estado que el bucle unido devuelve es `reviewSym h` para algún `h`.**

La rama del triángulo o recursa sobre un estado estrictamente menor, o **para sobre `reviewSym g`
mismo**; y el combustible —`measure g + 1`— no se agota nunca, porque cada vuelta pierde al menos
una unidad de medida. Luego todo hecho de punto fijo del review simétrico vale tal cual para la
máquina unida, sin volver a demostrar nada.

## 3. Y con ellos, cuatro campos más

Una vez construido el punto fijo, los demás salen casi solos:

| campo de `TableCtx` | estado sobre la máquina unida |
|---|---|
| `oos` — los owners de un nodo en su propio paso son sólo él | ✅ v89 |
| `sym` — tablas simétricas | ✅ v89 |
| `tri` — el triángulo | ✅ v89 |
| **`coh`** — coherencia con los padres | ✅ **hoy** |
| **`cohSons`** — coherencia con los hijos | ✅ **hoy** |
| **`selfown`** — cada nodo se posee | ✅ **hoy** (de `OOS` más validez de nodo) |
| `level`, `parnode`, `hasparent`, `sonlevel`, `sonnode`, `hasson`, `smp` | faltan |

Más, fuera de `TableCtx` pero necesarios para `Fabric_whole`: **`OwnersGlobal_reviewSymTri`** y
**`node_valid_reviewSymTri`** (*todo nodo que la máquina unida deja pasa `isValidNode`*), ambos
demostrados hoy.

**Lo que queda es de otra naturaleza, y conviene decirlo**: los siete campos pendientes no hablan
de owners, hablan de la **forma del grafo** — que los padres están un paso por debajo, que son
nodos, que un nodo no raíz tiene alguno, y los tres espejos para los hijos, más `smp`. Son hechos
estructurales, del tipo que `Sons.lean` y `Parents.lean` ya tratan, y ninguno toca el punto fijo.

## 4. Lo que esto deja montado

`Fabric_whole` (v88) dice: bajo `TableCtx`, **el estado válido es un tejido entero**, las nueve
cláusulas. De sus hipótesis, las que hablan de tablas y owners están ahora demostradas sobre una
máquina concreta —la unida de v89—, y lo que falta es la forma del grafo.

Sin cambios en lo demás: `up`/`down` sólo fallan **relativos al pinchazo** (v88), el estrechado del
candidato del lector nunca se vacía en 53.639 pinchazos medidos, y el muro de v70 sigue donde
estaba.

## 5. Estado

| pieza | estado |
|---|---|
| **P1** el tejido nace | ✅ v78 |
| **P2** lo preservan las operaciones y el `join` | ✅ v65 + v79 |
| **P3** el pinzado cubre y no se estrecha | ✅ cerrada (v83–v86) |
| **P4** el puente a `PickSome` | 7 cláusulas (v87), `up`/`down` de tabla (v88), la máquina unida (v89), **y hoy seis de los once campos de `TableCtx` sobre ella**; faltan los siete estructurales y el testigo **relativo** |
| **P5** cierre con `L7` | libre |

Build: `lake build AbsSat` verde, 101 módulos, 0 `sorry`, 0 axiomas de proyecto; los **ochenta y
nueve** teoremas de `SymTriReview.lean` cierran en `[propext, Quot.sound]`. La campaña `--joined`
sigue dando 0 perdidas, 0 zombis, 0 violaciones de simetría.
