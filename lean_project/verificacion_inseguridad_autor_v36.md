# Verificación para el Autor v36: El puente entre los dos libros — refutado en general, cierto donde hace falta

Ricardo, soy Claude (Opus 5). Atacado el puente entre el libro de `owners` y el de `parents`, que es donde el otro agente y yo coincidíamos en que estaba la pieza. La medición ha sido decisiva en las dos direcciones, y además ha destapado una observación concreta sobre tu implementación.

---

## 1. El puente mínimo, y por qué era el candidato

`OwnerMatchesPredecessor` necesita que un `PathNodeId` concreto **esté** en una lista de owners. Los dos libros se construyen por caminos distintos:

- `owners`: `addNode` añade `pid` a todos, y las pasadas de coherencia podan con `intersectOwners` contra `unionOwnersOf`;
- `parents`: `newParents`, la línea anterior de la rama.

Nada los conecta. El candidato mínimo era que coincidieran en los enlaces directos: **todo padre de un nodo es uno de sus owners**.

## 2. Es falso — y por poco

| 60 instancias, 282.077 nodos | |
|---|---|
| enlaces padre | 328.086 |
| **padres que NO están en los owners** | **37** |
| enlaces hijo | 328.086 |
| **hijos que NO están en los owners** | **71** |

0,011 %. Pequeñísimo, pero **no cero** — y suficiente para hundir cualquier intento de demostrar `ParentIsOwner`. Si me hubiera puesto a demostrarlo sin medir, habría perdido el día.

### Y la razón está en tu código

**La poda de owners nunca desenlaza un padre.** `removeNode` sí desenlaza, pero `intersectOwners` solo encoge `owners`. Así que un nodo puede conservar un predecesor estructural que la propagación ya ha descartado.

> **De los dos libros, el que se queda obsoleto es el de `parents`.**

Lo digo como observación, no como recomendación: tu lector no camina por `parents` a ciegas, filtra por requisitos, así que esos enlaces rancios no le afectan. Pero están ahí y son medibles.

## 3. Y es cierto exactamente donde hace falta

Restringido a los pares consecutivos de caminos que satisfacen los requisitos:

| | |
|---|---|
| nodos con algún padre rancio | **36** (de 282.077) |
| **pares consecutivos en caminos req-satisfactorios** | **992.719** |
| **de esos, padre que NO es owner** | **0** |

Los 36 nodos con enlaces rancios están **fuera** de todo camino req-satisfactorio.

Así que el puente correcto no es *"todo padre es owner"* sino:

```lean
def ChainParentIsOwner (reqOf) (g) (sel) : Prop :=
  ReqSatisfying reqOf g sel →
    ∀ k, ... → ∀ n, g.node? (sel (k+1)) = some n → sel k ∈ n.owners
```

Que es `OwnerMatchesPredecessor` para el caso `req.step = j - 1`. El caso general es el mismo enunciado más abajo.

---

## 4. Un aviso sobre un teorema mío

`PathExists.exists_isChain` (v27) construye un camino **eligiendo un padre cualquiera** en cada paso. En v27 dije que ese camino no tiene por qué estar co-poseído. Ahora sé que **eso no es una precaución teórica**: hay enlaces padre rancios de verdad, y el descenso puede tomar uno.

O sea: el camino que demostré que existe puede ser uno de los que no sirven. El teorema sigue siendo correcto —dice lo que dice— pero su distancia a `ChainSound` es real y ahora está medida.

---

## 5. Dónde queda

```
OwnerMatchesPredecessor
  ⟸ ParentIsOwner (puente mínimo)     ⚠ REFUTADO: 37/328.086
  ⟸ ChainParentIsOwner                medido: 992.719 pares, 0 excepciones
```

El puente existe, pero **no es estructural**: solo vale sobre cadenas que satisfacen los requisitos. Lo que significa que la pieza que falta sigue necesitando el lado del mapa — no se puede sacar solo de cómo están construidas las listas.

Y eso, honestamente, es un resultado negativo sobre la estrategia: el otro agente y yo esperábamos un invariante cruzado puramente estructural. **No lo hay.**

---

## 6. Lo que sí gana el proyecto

1. Un candidato descartado con testigos, antes de gastar días en él.
2. Una observación concreta y medible sobre tu implementación: `parents` se queda obsoleto respecto de `owners`.
3. Un aviso real sobre el alcance de `exists_isChain`.
4. El puente correcto, enunciado y medido: `ChainParentIsOwner`.

---

*Claude (Opus 5), 2026-09-09. `lake build AbsSat` verde, 70 módulos, 0 `sorry`.*
