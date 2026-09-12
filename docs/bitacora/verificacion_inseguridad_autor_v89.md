# Verificación para el Autor v89: las dos correcciones, unidas en una sola máquina

Ricardo, soy Claude (Opus 5). Hecho: `AbsSat/GraphPath/Model/SymTriReview.lean`, módulo nuevo,
registrado, 101 módulos en el build. **El review simétrico de v64 y la pasada del triángulo de v69
en la misma máquina**, en el modelo — no en el código de medición, como estaba en v87.

```
reviewSymTri = el review simétrico hasta su punto fijo, luego una barrida del
               triángulo, y otra vez, hasta que la barrida no quita nada
```

---

## 1. Se gana el sitio: las tres cosas demostradas

Una máquina nueva tiene que ganarse el sitio. Las tres que hacen falta están demostradas:

```lean
theorem ChainSound_reviewSymTri   … : ChainSound (reviewSymTri g) sel      -- no pierde soluciones
theorem OwnSymmetric_reviewSymTri … : Threaded.OwnSymmetric (reviewSymTri g) -- simetría
theorem TriProp_reviewSymTri      … : FabricAdd.TriProp (reviewSymTri g)     -- el triángulo
```

* **No pierde soluciones.** Las dos mitades ya lo tenían: v64 (`ChainSound_reviewSym`) y v69
  (`ChainSound_triClean`). Unirlas es una inducción sobre el combustible.
* **Mantiene la simetría.** v64 para el review, y `OwnSymmetric_triClean` de v86 para la barrida —
  cuyo test pide un nodo en **las dos** tablas y por eso no puede romperla.
* **Entrega el triángulo.** Misma lectura que v85: en un punto fijo de `triClean`, una entrada
  sobrevivió *porque* se cumplió el test, y ese test **es** `TriProp`.

Lo que costó fue la tercera, porque el bucle necesita **`measure_reviewSym_le`** —«el review
simétrico nunca hace crecer la medida»— y no existía. Ocho lemas nuevos para llegar a él, desde
`measure_symmetrize_le` (el paso espejo sólo filtra tablas) hasta `measure_reviewFuelSym_le`. La
misma historia que v85 con el review original.

Y de paso quedó la cadena `Pruned` para el review simétrico, que tampoco existía
(`pruned_symmetrize` … `pruned_reviewSym`, siete lemas), con dos consecuencias inmediatas:
**`OOS_reviewSymTri` sale gratis** —`OOS` sólo necesita que el estado encoja— y
`gowners_compat_filterAllSymTri`, que es una de las hipótesis del estrechado de P3.

## 2. Medida contra la fuerza bruta

Modo nuevo `--joined`: las cuatro máquinas en paralelo contra búsqueda exhaustiva.

| semilla | instancias | satisfacibles | `symtri` dice SAT | **pierde** | **zombi** | violaciones de simetría (orig → symtri) |
|---|---|---|---|---|---|---|
| 1001 | 40 | 38 | 38 | **0** | **0** | 63 → **0** |
| 7777 | 40 | 36 | 36 | **0** | **0** | 74 → **0** |
| 31337 | 30 | 25 | 25 | **0** | **0** | 330 → **0** |

**110 instancias, 0 soluciones perdidas, 0 veredictos zombi, 0 violaciones de simetría.**

Un detalle honesto: el número de nodos es **idéntico** en las cuatro máquinas (74.667 / 91.522 /
112.703). La máquina unida **no poda más nodos** en estas instancias; lo que cambia son las
**tablas de owners** — la simetría y el triángulo—, que es exactamente lo que los teoremas
necesitan. No es una máquina más agresiva, es una máquina con más estructura demostrable.

Y la banda de v87 sobre la máquina unida del modelo da lo mismo que daba la simulada: 38.398
pinchazos, `gow`/`self`/`symm`/`support` en **0** fallos, `up`/`down` en 791/721.

## 3. Qué compra esto para P4

`TableCtx` —la hipótesis de v88 bajo la cual el estado válido **es** un tejido entero— pedía
simetría **y** triángulo a la vez, y ninguna máquina las tenía. Ahora una las tiene, y con `OOS`
encima. Lo que queda de `TableCtx` en la máquina unida son **dos campos**:

* **`CoherentParents`** — que la pasada de coherencia llegó a su punto fijo;
* **`OwnersGlobal`** — que los owners de un superviviente son owners globales.

Los dos están demostrados para el `review` original en `Fuel.lean` (`review_owners_coherent_parents`,
`review_owners_within_gowners`) y **ninguno para el simétrico**: son el punto fijo del bucle, y esa
contabilidad —`reviewPassSym (reviewSym g) = reviewSym g` y las piezas de `cleanStep`— es lo único
que falta para que v88 se aplique a una máquina concreta en vez de a una hipótesis.

Es trabajo del tipo que `Fuel.lean` ya contiene, no hay nada abierto dentro, y es lo que haría
falta hacer a continuación por esta vía.

## 4. Estado

| pieza | estado |
|---|---|
| **P1** el tejido nace | ✅ v78 |
| **P2** lo preservan las operaciones y el `join` | ✅ v65 + v79 |
| **P3** el pinzado cubre y no se estrecha | ✅ cerrada (v83–v86) |
| **P4** el puente a `PickSome` | 7 cláusulas (v87), `up`/`down` de tabla (v88); **la máquina que `TableCtx` pide, construida y medida (hoy)**; faltan `CoherentParents` y `OwnersGlobal` para el review simétrico |
| **P5** cierre con `L7` | libre |

Build: `lake build AbsSat` verde, **101 módulos**, 0 `sorry`, 0 axiomas de proyecto; los treinta y
seis teoremas de `SymTriReview.lean` cierran en `[propext, Quot.sound]`.
