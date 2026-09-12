# Verificación para el Autor v56: el ∃∀ sí está al alcance — y el residuo es ahora local

Ricardo, soy Claude (Opus 5). La pregunta era si la posesión depende solo del id de mapa en el descenso. La respuesta tiene dos mitades, y la segunda abre la puerta.

---

## 1. La respuesta directa: el id sí, la posesión no

`lake exe extend --randomgoodparent`, dos semillas, 26.878 nodos por encima del paso 0:

| | |
|---|---|
| nodos cuyos padres abarcan **2 o más ids de mapa** | **0 de 26.878** |
| pares de padres hermanos con **owners distintos** | **5.182** |

La primera mitad confirma la intuición: **`parent_id` decide el nodo de mapa del padre, siempre.** Los padres de un nodo son todos el mismo nodo del mapa; solo difieren en su propia decoración (el id del abuelo).

La segunda la mata como atajo: **esa decoración sí cambia los owners.** Dos hermanos con el mismo id de mapa tienen conjuntos de owners distintos en 5.182 pares. Así que no: no puedes elegir el padre por su id de mapa y olvidarte.

## 2. El ∃∀ a lo bruto es falso — y por una razón que se puede nombrar

Lo que `ExtendDownTop` querría es: *algún* padre bueno para *todos* los owners de arriba. Medido:

| | |
|---|---|
| nodos sin ningún padre bueno para todos sus owners de arriba | **948 de 26.878** |

Falso. Pero mirando **qué** se le estaba pidiendo al padre, aparece el motivo: se le pedía cubrir un conjunto de owners que **ninguna cadena podría contener nunca** — dos owners en el mismo paso, o dos que no se poseen mutuamente. Una exigencia incoherente.

## 3. Restringido a exigencias coherentes: cero fallos

Llamo **transversal clique** a un conjunto que una cadena sí podría contener: como mucho un nodo por paso, y mutuamente poseídos dos a dos.

| | |
|---|---|
| nodos cuyos owners-de-arriba **son** una transversal clique | **18.760** |
| de esos, sin padre bueno | **0** |

Y esto no basta, porque la historia de una cadena es un **subconjunto** de los owners de arriba, y un subconjunto puede ser coherente aunque el total no lo sea. Así que la enumeración exhaustiva, `--randomclique`, recorre **todas** las sub-cliques de cada nodo:

| campaña | nodos > paso 0 | exigencias coherentes | enumeraciones cortadas | **sin padre bueno** |
|---|---|---|---|---|
| 8 casos, 2026, 3..5 vars | 6.947 | **154.635.941** | 315 | **0** |

**154 millones de exigencias coherentes, cero sin padre bueno.**

## 4. El enunciado, y la cadena de teoremas

```lean
def Coherent (g : GPathM) (S : PathNodeId → Prop) : Prop :=
  ∀ a b, S a → S b → a ≠ b →
    a.id.step ≠ b.id.step ∧ a ∈ ownersOf g b ∧ b ∈ ownersOf g a

def GoodParentOnCliques (g : GPathM) : Prop :=
  ∀ (p : PathNodeId) (n : PNodeM), g.node? p = some n → 0 < p.id.step →
    ∀ S : PathNodeId → Prop,
      (∀ a, S a → p.id.step < a.id.step ∧ a ∈ ownersOf g p ∧ p ∈ ownersOf g a) →
      Coherent g S →
      ∃ c ∈ n.parents, c.id.step = p.id.step - 1 ∧
        (p ∈ ownersOf g c ∧ c ∈ ownersOf g p) ∧
        ∀ a, S a → (a ∈ ownersOf g c ∧ c ∈ ownersOf g a)
```

> Todo nodo por encima del paso 0 tiene, para **toda exigencia coherente** hecha de sus propios owners de arriba, **un padre** mutuamente poseído con el nodo y con toda la exigencia.

Un nodo, sus padres, sus owners. **Sin cadenas, sin inducción sobre la construcción, sin existencial global.**

Y la cadena completa hasta el veredicto, toda demostrada:

```lean
ExtendDownTop_of_GoodParentOnCliques : GoodParentOnCliques g → ExtendDownTop g
SupportedAt_top_of_ExtendDownTop     : ExtendDownTop g → SupportedAt g (nodo alto)
Inhabited_of_GoodParentOnCliques     : GN g → 0 < current_step → isValid g →
                                       GoodParentOnCliques g → Inhabited g
```

Todas `[propext, Quot.sound]`, 0 `sorry`, 0 axiomas de proyecto. La demostración del primer eslabón es directa: la historia de una cadena parcial **es** una exigencia coherente hecha de los owners de `sel lo`, así que el padre que el enunciado local produce es exactamente la extensión que hace falta.

## 5. Dónde ha quedado el problema abierto

Compara con dónde estaba hace dos informes:

| | |
|---|---|
| v53 y antes | `Supported`: **todo** nodo está en **alguna** cadena completa co-poseída. Existencial anidado, global, dos direcciones, ambas refutadas en su forma manejable. |
| v55 | `ExtendDownTop`: nada se atasca bajando desde el techo. Una dirección, pero todavía sobre cadenas. |
| **v56** | **`GoodParentOnCliques`**: un nodo tiene un padre bueno para cada exigencia coherente. **Local, un paso, universal, sin cadenas.** |

Y lo que hay que demostrar se ve exactamente: `Threaded.hop_down` ya da, para **cada** owner, **algún** padre que lo posee — vía `cpar`, la coherencia de padres en el punto fijo. Falta intercambiar los cuantificadores **usando la coherencia de la exigencia**, que es la hipótesis que las mediciones dicen que marca la diferencia. Es la primera vez que el residuo no habla de caminos.

## 6. Lo que esto **no** es

- **`GoodParentOnCliques` sigue sin demostrar.** Es una conjetura local con 154 millones de instancias sin contraejemplo, y una reducción al veredicto que sí es teorema.
- **315 de 6.947 enumeraciones se cortaron por presupuesto** (nodos con conjuntos de owners grandes). El cero vale sobre lo explorado.
- La reducción **no dice que la máquina mantenga el enunciado al filtrar**: eso sigue siendo la obligación del lector no-retrocedente.
- Instancias de 3 a 6 variables. Complejidad, sin teoremas.

## 7. Estado

| | |
|---|---|
| Mitad de completitud (conservación + driver) | cerrada |
| S1 / S2 | cerrados |
| `ExtendUp`, `ExtendDown` general | refutados |
| `ExtendDownTop` | 0 callejones en 15.755 cadenas |
| Padres comparten id de mapa | **0 violaciones en 26.878** |
| Owners dependen de la decoración | sí — 5.182 pares de hermanos difieren |
| ∃∀ sobre todos los owners | **falso** (948 de 26.878) |
| **∃∀ sobre exigencias coherentes** | **0 de 154.635.941** |
| `GoodParentOnCliques` ⟹ `Inhabited` | **demostrado** |
| `GoodParentOnCliques` en sí | abierto — local, un paso |
| Complejidad | sin teoremas |

`lake build AbsSat` verde, 85 módulos, 0 `sorry`, 0 axiomas de proyecto.

---

*Claude (Opus 5), 2026-09-11.*
