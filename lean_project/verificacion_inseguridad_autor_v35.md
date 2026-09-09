# Verificación para el Autor v35: El lema que te propusieron es falso — y el correcto se reduce a una existencia

Ricardo, soy Claude (Opus 5). He revisado el análisis del otro agente contra el código. **La mayor parte es correcta y útil**, hay una cosa importante que corregir, y siguiendo su propia recomendación —medir antes de formalizar— la medición ha salido decisiva.

---

## 1. Lo que dice bien, y lo confirmo

- **`ReqSatImpliesOwned` es hoy un `def`, no un teorema.** Cierto, `MapChain.lean:106`.
- **`ChainSound_of_parts` ya está demostrado y listo para consumirlo.** Cierto.
- **`PMP` es sobre el grafo estructural (`n.parents`) y `owners` es otro libro de contabilidad.** Cierto, y es la observación más valiosa de su análisis. Que `q` sea owner de `n` no lo hace padre ni hijo de `n`, así que `parentId_coherent` **no** se le puede aplicar a un owner cualquiera. Eso corrige una frase de mi v34 §4 donde di por hecho que la cadena "selecciona cuál le toca" entre los dos owners; no estaba demostrado.
- **Medir antes de formalizar.** De acuerdo, y es lo que he hecho.

## 2. Lo que hay que corregir: el lema propuesto es falso

Propone:

```lean
theorem owner_at_req_eq_chain_pick ... (q ∈ ownersAt n.owners req.step) : q = sel req.step
```

O sea: **todo** owner en el paso pinzado es el nodo que elige la cadena. Eso **no puede ser cierto**, y lo dicen mis propios números — solo que v33 los midió sobre *todos* los nodos, no sobre nodos de cadena, así que había que rehacer la medición para estar seguro. Hecho:

| sobre caminos req-satisfactorios | pares (nodo **de cadena**, requisito) | **ancho ≥ 2** |
|---|---|---|
| semilla 2026, 3–9 vars, 60 inst. | 1.193.194 | 277.070 (23,2 %) |
| semilla 90210, 3–10 vars, 100 inst. | **3.236.018** | 758.210 (23,4 %) |
| **total** | **4.429.212** | **1.035.280** |

En más de un millón de sitios hay dos owners distintos y la cadena elige uno. `∀ q, q = sel` es falso ahí, y no por falta de demostración.

**Lo que `PairwiseOwned` necesita no es eso: es pertenencia.** `sel req.step ∈ ownersAt n.owners req.step`. Estrictamente más débil, y es lo que hay que atacar.

## 3. Y su pregunta empírica tiene respuesta, perfecta

Preguntaba: en cada par pinzado, ¿cuál de los dos owners tiene `parent_id` igual al predecesor de la cadena — siempre exactamente uno, nunca cero, nunca los dos?

| sobre los **4.429.212** pares, dos semillas | |
|---|---|
| **la elección de la cadena NO está en el conjunto de owners** | **0** |
| owners que casan con el predecesor: **ninguno** | **0** |
| owners que casan con el predecesor: **exactamente uno** | **4.429.212** |
| owners que casan con el predecesor: **dos o más** | **0** |

**Siempre exactamente uno. En 4,43 millones de casos.** Ni un cero, ni un dos.

---

## 4. Lo que eso permite demostrar hoy

Un `PathNodeId` son dos campos. De uno ya sabíamos:

- **`owner_at_req_shares_mapid`** (v33): todo owner en el paso pinzado comparte **id de mapa** con la elección de la cadena.

Y del otro, ahora:

```lean
theorem owner_eq_chain_pick ... (hpar : q.parent_id = (sel req.step).parent_id) :
    q = sel req.step
```

> Un owner del paso pinzado que lleve el `parent_id` de la cadena **es** la elección de la cadena.

De ahí:

```lean
theorem chain_pick_mem_owners ... (hmatch : OwnerMatchesPredecessor reqOf g sel) ... :
    sel req.step ∈ ownersAt n.owners req.step
```

## 5. La obligación que queda de la mitad pinzada

```lean
def OwnerMatchesPredecessor (reqOf) (g) (sel) : Prop :=
  ∀ j ... ∀ req ∈ reqOf (sel j).id, ...
    ∃ q ∈ ownersAt n.owners req.step, q.parent_id = (sel req.step).parent_id
```

> **Existe** un owner en el paso requerido que lleva el `parent_id` de la cadena.

Una **existencia**, sobre un elemento cuyos dos campos están determinados. No una búsqueda, no una elección. Medida: exactamente uno, **4.429.212** veces, dos semillas independientes.

Y ahí sí encaja lo que el otro agente señala como la pieza que falta: **un puente entre el libro de `owners` y el de `parents`**. Porque para demostrar esa existencia hay que saber que las pasadas de coherencia (`intersectOwners` contra `unionOwnersOf`) no expulsan justamente al owner que la rama estructural sí conserva. Eso sigue sin atacarse, y es el sitio correcto para atacarlo.

## 6. La mitad que nadie ha mirado

Honestidad, porque el análisis del otro agente tampoco lo menciona: `PairwiseOwned` pide **todos** los pares `(i, j)`, y esto solo cubre los pares donde `i` es un paso que un requisito de `sel j` nombra. Los pares **no pinzados** no tienen requisito en el que apoyarse, y para ellos no hay ninguna reducción — solo la medición global de v31 (350.243 caminos, 0 no co-poseídos).

---

## 7. Estado

```
PairwiseOwned
  ⟸ pares pinzados
       ⟸ id de mapa                  demostrado (v33)
       ⟸ parent_id ⟹ es la cadena    demostrado (v35)
       + ∃ owner con ese parent_id    medido: exactamente uno, 4.429.212 veces
  ⟸ pares NO pinzados                 sin reducción; solo medición global
```

---

*Claude (Opus 5), 2026-09-09. Corrige una frase de v34 §4 y el lema propuesto en la revisión externa. `lake build AbsSat` verde, 70 módulos, 0 `sorry`.*
