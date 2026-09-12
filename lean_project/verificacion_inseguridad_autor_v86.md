# Verificación para el Autor v86: el transporte — uno se hace, el otro era innecesario

Ricardo, soy Claude (Opus 5). Ataqué el transporte que v85 dejó pendiente. Los dos lemas se
separan del todo, y el resultado es mejor de lo que esperaba: **P3, el estrechado, queda cerrada
de punta a punta sobre `filterAllTri`, sin ninguna hipótesis salvo que el filtro deje un estado
válido.**

---

## 1. Primero, la corrección

v85 dijo: *«faltan dos lemas por transportar a `reviewTri`: owners ⊆ gowners y la simetría»*.
De los dos, **la simetría nunca hizo falta**.

Mira `TriProp` tal y como quedó demostrado:

```lean
def TriProp (g : GPathM) : Prop :=
  ∀ a na b nb, g.node? a = some na → g.node? b = some nb → b ∈ na.owners →
    ∀ l, 0 ≤ l → l < g.current_step →
      ∃ w, w ∈ na.owners ∧ w ∈ nb.owners ∧ w.id.step = l
```

En v84 yo tenía `p ∈ owners(r)`, giraba con la simetría a `r ∈ owners(p)`, y entonces aplicaba
el triángulo. Pero el triángulo aplicado **en la dirección que ya tiene** —con `a := r`, `b := p`,
que es exactamente `p ∈ owners(r)`— entrega el mismo nodo `w` en las dos tablas. El rodeo por la
simetría no añadía nada. `pinnedCandidate_selfSupporting` pide ahora **tres** hipótesis, no cuatro,
y sigue **sin depender de ningún axioma**.

No lo vi en v84 ni al revisarlo en v85. Lo digo porque cambia el balance de lo que hace falta.

## 2. Y menos mal, porque para `reviewTri` la simetría es **falsa**

Antes de intentar demostrarla, la medí, y el detector no está ciego:

```
lake exe cnfmap --symreview 40 1001 3 4
  states   original / symmetric             = 3070 / 3070
  SYMMETRY VIOLATIONS original / symmetric  =   63 / 0

lake exe cnfmap --symreview 40 7777 3 5
  states   original / symmetric             = 3544 / 3544
  SYMMETRY VIOLATIONS original / symmetric  =   74 / 0
```

El `review` original **rompe la simetría** durante la construcción —63 y 74 violaciones en dos
semillas—, y la máquina simétrica de v64 da 0 en los mismos estados. Es la misma observación que
hiciste tú en v63 y por la que construiste `reviewSym`. Como `reviewTri` está montado sobre
`review`, transportarle la simetría no es difícil: es **falso**. Si el rodeo de v84 hubiera sido
necesario, P3 habría exigido una tercera máquina (el triángulo sobre el review simétrico) y todo
el andamiaje del punto fijo de `reviewSym`, que no existe.

## 3. Lo que sí transporta, demostrado

```lean
theorem OwnersGlobal_reviewTri (g : GPathM) (hv : isValid (reviewTri g) = true) :
    OwnersGlobal (reviewTri g)                            -- [propext, Quot.sound]
```

*Todo owner en rango de un nodo superviviente es un owner global.* Sin más hipótesis que la
validez. El argumento es el que anuncié y esta vez sí es el que sirve: `triClean` encoge tablas y
no toca `gowners` ni `current_step` (`OwnersGlobal_triClean`), y **toda rama del bucle que
devuelve entrega un estado que un `review` acaba de limpiar** (`OwnersGlobal_review`, que es tu
`owner_mem_gowners` de v25 más F2.c). La inducción sobre el combustible cierra.

De paso quedó `pruned_reviewTri`: **el review con triángulo nunca inventa un owner global**.

## 4. Y lo que el triángulo sí debía por su cuenta

```lean
theorem OwnSymmetric_triClean (g : GPathM) (h : Threaded.OwnSymmetric g) :
    Threaded.OwnSymmetric (triClean g)                     -- [propext, Quot.sound]
```

Aunque ya no haga falta para P3, la pregunta que hiciste merece respuesta completa: **tu pasada
del triángulo no puede romper la simetría.** Su test —`commonAtAll`, «hay un nodo en las **dos**
tablas en cada paso»— es simétrico en los dos nodos, así que una barrida que quita `q` de la tabla
de `p` quita `p` de la de `q`. La simetría la rompe el review, no el triángulo.

## 5. El ensamblaje

```lean
theorem pinnedCandidate_selfSupporting_filterAllTri (g : GPathM) (reqs : List NodeId)
    (hv : isValid (filterAllTri g reqs) = true)
    (r n hn) (p hp) (np hnp) (l hl0 hl) :
    ∃ w, w ∈ np.owners ∧ w ∈ n.owners ∧ Compat reqs w ∧ w.id.step = l
```

Sobre **tu** filtro de cláusula con la pasada del triángulo, y con la validez como única hipótesis:
todo miembro del candidato pinzado tiene su soporte **dentro** del candidato, en cada paso. Las
tres hipótesis se descargan aquí: `OwnersGlobal_reviewTri` (§3), `gowners_compat_filterAllTri`
(los pines sobreviven al review con triángulo, vía `pruned_reviewTri`) y `TriProp_reviewTri` (v85).

Con `pinnedCandidate_covers` (v83) para la cobertura, **P3 está cerrada**.

**Regresión medida**, semilla nueva: `cnfmap --p3 30 4242 3 4` → 3.591 filtros válidos, **77.086
supervivientes, 0 pasos perdidos, 0 vacíos, 0 pérdidas de `r`**.

## 6. El aviso de siempre

Sigue valiendo, y aquí conviene repetirlo porque P3 ya no tiene piezas abiertas: esto **no**
demuestra de más. El argumento de cobertura se apoya en `owns_required`, teorema **del filtro de
cláusula**, que no vale para el pinchazo del lector; por eso no transfiere a `PinNonEmpty`, que
v82 midió equivalente a la validez misma. Y el estrechado se apoya en `TriProp` y en los owners
globales, ambos invariantes **de la construcción**, condicionados a que el filtro deje un estado
válido. P3 es un invariante de construcción, no un procedimiento de decisión. Nada choca con el
muro de v70.

## 7. Estado

| pieza | estado |
|---|---|
| **P1** el tejido nace | ✅ v78 |
| **P2** lo preservan las operaciones y el `join` | ✅ v65 + v79 |
| **P3** el pinzado cubre y no se estrecha | ✅ **cerrada** — cubre (v83), no borra (v84), `TriProp` (v85), transporte (hoy) |
| **P4** el puente a `PickSome` | formalmente ✅ (v81), medido equivalente a la validez (v82) |
| **P5** cierre con `L7` | libre |

Lo que queda entre esto y el veredicto es P4, y ahí v82 midió que la obligación del lector es
equivalente a la validez misma —es decir, que P4 es donde está el trabajo de verdad, no una pieza
de contabilidad—. Es el sitio al que hay que volver con calma, y sin las prisas con las que yo
cerré v81.

Build: `lake build AbsSat` verde, 100 módulos, 0 `sorry`, 0 axiomas de proyecto; los cuarenta y
ocho teoremas de `FabricAdd.lean` cierran en `[propext, Quot.sound]` o menos — dos de ellos,
`Fabric_core` y `pinnedCandidate_selfSupporting`, sin axiomas de ningún tipo.
