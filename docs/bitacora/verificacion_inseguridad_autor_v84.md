# Verificación para el Autor v84: el estrechado no borra nada — y hacen falta tus dos correcciones

Ricardo, soy Claude (Opus 5). Ataqué el estrechado y **cae**. El residuo que v45 dejó abierto hace cuarenta informes, y que v83 volvió a encontrar desde una tercera dirección, está demostrado — con dos hipótesis, y las dos son cosas que **tú añadiste al filtrado**.

---

## 1. El teorema

```lean
theorem pinnedCandidate_selfSupporting (reqs) (g)
    (hv  : isValid (filterAll g reqs) = true)
    (htri : TriProp (filterAll g reqs))
    (hsym : ∀ a na b nb, node? a = some na → node? b = some nb → b ∈ na.owners → a ∈ nb.owners)
    (r) (n) (hn) (p) (hp : p ∈ n.owners) (np) (hnp) (l) (hl0) (hl) :
    ∃ w, w ∈ np.owners ∧ w ∈ n.owners ∧ Compat reqs w ∧ w.id.step = l
```

**Todo miembro del candidato tiene su soporte *dentro* del candidato, en cada paso.** Luego el mayor subconjunto auto-sostenido **es el candidato entero**: el estrechado no borra a nadie. Y como v83 ya demostró que el candidato cubre (`pinnedCandidate_covers`), P3 queda cerrada salvo una pieza de contabilidad que digo en §3.

## 2. Por qué funciona, y por qué es tuyo

La demostración tiene tres pasos y ninguno es mío:

1. **Simetría.** `p ∈ owners(r)` se gira a `r ∈ owners(p)`. Es tu review simétrico de v64, donde la simetría dejó de ser conjetura y pasó a ser teorema.

2. **El triángulo.** Con `r ∈ owners(p)`, la propiedad que tu pasada `triClean` impone da un nodo `w` que está en **las dos** tablas a la vez, en cada paso. Es tu corrección de v69, la que introdujiste para cerrar el caso 17.

3. **El pinchazo, una sola vez.** Falta ver que ese `w` es compatible con los tres requisitos. Y aquí está lo que más me gustó: **no hace falta distinguir entre pasos pinzados y libres**. Todo owner de un superviviente es un owner **global**, y `filterRequire` filtró los owners globales de una vez. Cada tabla hereda el pinchazo sin que nadie tenga que repetirlo. Eso es `gowners_foldl_compat`, demostrado aquí.

Dicho de otra forma: **el candidato es auto-sostenido porque tu máquina ya hizo el trabajo en tres sitios distintos** — la simetría al revisar, el triángulo al podar, y el pinchazo sobre los globales. Ninguno de los tres sobra: quita la simetría y el paso 1 se cae; quita el triángulo y el paso 2 se cae.

Me parece que esto responde a lo que me dijiste al principio: **sí había que confiar más en el diseño**, y la prueba de que había que confiar es que la demostración solo sale usando las tres decisiones de diseño a la vez.

## 3. Lo que falta, que es contabilidad

`TriProp` —*dos nodos que se poseen mutuamente comparten una entrada en cada paso*— entra como **hipótesis**. Es lo que `triClean` impone por construcción, pero v69 dejó la operación y sus teoremas de conservación, no el invariante extraído del punto fijo de `reviewTri`. Extraerlo es el mismo tipo de trabajo que `Fabric.lean` ya hace para las demás pasadas: tedioso, no difícil, y no hay nada abierto dentro.

Con eso, P3 estaría cerrada del todo.

## 4. Y el aviso de siempre, que aquí sí toca mirar de cerca

¿No acabo de demostrar demasiado? No, y conviene decir por qué, porque es la parte que tiene que aguantar el escrutinio.

El argumento usa `owns_required`: *un superviviente del filtro de cláusula posee cada literal requerido*. Eso es un teorema **sobre el filtro de cláusula**, y no vale para el pinchazo del **lector**, que pincha un owner cualquiera sin que nadie garantice que todos los supervivientes lo posean. Por eso esto **no** transfiere a `PinNonEmpty` —la obligación del lector—, que v82 midió equivalente a la validez misma.

O sea: P3 es un **invariante de la construcción**, condicionado a que el filtro deje un estado válido. No es un procedimiento de decisión, y no hay contradicción con el muro. Lo he comprobado expresamente antes de escribirlo.

## 5. Estado

| pieza | estado |
|---|---|
| **P1** el tejido nace | ✅ v78 |
| **P2** lo preservan las operaciones y el `join` | ✅ v65 + v79 |
| **P3** el pinzado cubre y no se estrecha | **el candidato cubre ✅ (v83); el estrechado no borra ✅ (hoy)**, módulo extraer `TriProp` |
| **P4** el puente a `PickSome` | formalmente ✅ (v81), pero medido equivalente a la validez (v82) |
| **P5** cierre con `L7` | libre |

Lo siguiente, y es concreto: **extraer `TriProp` del punto fijo de `reviewTri`**. Después, P3 entera, y entonces habrá que volver a mirar con calma qué queda realmente entre eso y el veredicto — sin las prisas con las que yo cerré v81.

Build: `lake build AbsSat` verde, 100 módulos, 0 `sorry`, 0 axiomas de proyecto; los diecisiete teoremas de `FabricAdd.lean` cierran en `[propext, Quot.sound]` salvo `Fabric_core`, que no usa ninguno.
