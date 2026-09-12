# Verificación para el Autor v65: `Woven` generalizado — el tejido

Ricardo, soy Claude (Opus 5). Me pediste generalizar `Survive.Woven`. Está hecho y demostrado, y al usarlo pasa algo que creo que importa: **el muro del lector cambia de naturaleza**. Deja de ser una pregunta sobre lo que hará el review después de elegir y pasa a ser una propiedad estática del estado en el que eliges.

---

## 1. Por qué `Woven` no bastaba

`Woven g S` era lo que sobrevive al review completo, y pedía una cosa de más: que **todo miembro posea a todo miembro**. Eso convierte un conjunto tejido en una camarilla, que en la práctica son los nodos de una cadena co-poseída.

Pero v64 midió que elegir `r` conserva **todos** los owners de `r`, y `owners(r)` no es una camarilla: entre el 18 y el 31 % de los pares de owners no se poseen entre sí (v54). Así que `Woven` no podía ser la razón de que sobrevivan.

## 2. La generalización: el tejido (`Fabric`)

Si se mira lo que el review comprueba de verdad de un nodo, es esto: que tenga un owner en cada paso, un padre y un hijo entre sus owners, y que cada owner lo posea también algún padre y algún hijo. Nada de eso necesita la tabla **entera** del nodo; basta **alguna subtabla que se sostenga sola**.

```
Fabric g S T :  cada miembro p conserva una subtabla T p de sus owners, y
  · T es simétrica, se queda dentro de S, y contiene a p;
  · T p tiene una entrada en cada paso;
  · cada entrada v de T p está respaldada por un padre c de p con T p c y T c v,
    y por un hijo c de p con T p c y T c v;
  · los miembros son nodos reales y owners globales.
```

**`Woven` es el caso particular `T p v := S v`** (`Fabric_of_Woven`, demostrado).

Hay dos diferencias con `Woven`, y las dos son deliberadas:
- **Las tablas pueden encoger.** El review puede tirar entradas de fuera de `T p`; el tejido solo promete que nunca tira una de dentro. Es justo lo que midió `--selfsupport` en v64: tras elegir, las tablas encogen, pero los nodos no mueren.
- **La simetría de `T`** sustituye a la co-posesión de los enlaces, y es exactamente lo que necesita el paso espejo del review simétrico.

## 3. Lo demostrado (todo `[propext, Quot.sound]`, 0 `sorry`)

- **Las cuatro operaciones:** `Fabric_updateAt`, `Fabric_symmetrize`, `Fabric_unlink`, `Fabric_removeNode`. Y el corazón, `isValidNode_of_Fabric`: un miembro siempre pasa el test de validez, así que ninguna barrida puede quitarlo.
- **El bucle del review original, entero:** `FOk_review` e `isValid_filterAll_of_Fabric`, que es la generalización directa de `isValid_filterAll_of_Woven`. Ya no hace falta una hipótesis de cobertura aparte, porque la condición `support` alcanza todos los pasos por sí sola.
- **El bucle simétrico con tu pinchazo por owners:** `FOk_reviewSym`, `FOk_readStepSym` e `isValid_readStepSym_of_Fabric`.
- **El enunciado que nombra el muro:**

```lean
def FabricAt (g : GPathM) (r : PathNodeId) : Prop :=
  ∃ rn S T, g.node? r = some rn ∧ FOk g S T ∧ S r ∧ ∀ p, S p → p ∈ rn.owners

theorem isValid_readStepSym_of_FabricAt (g) (r) (h : FabricAt g r) :
    isValid (readStepSym g r) = true
```

Es decir: **si `owners(r)` contiene un tejido que pasa por `r`, elegir `r` nunca atasca al lector**, y todo miembro del tejido sigue vivo después (`alive_readStepSym_of_FabricAt`).

## 4. Lo medido: el tejido más grande dentro de `owners(r)`

Modo nuevo, `lake exe cnfmap --fabric`. Para cada elección `r` de cada estado final de la máquina simétrica, se calcula el mayor tejido dentro de `owners(r)`: se parte de `owners(p) ∩ owners(r)` y se recortan las condiciones hasta el punto fijo.

| | cinco semillas, 3 a 6 variables |
|---|---|
| elecciones examinadas | 4.888 |
| nodos en `owners(r)` | 159.621 |
| **de ellos, dentro del mayor tejido** | **159.621 (todos)** |
| elecciones en que el tejido es **todo** `owners(r)` | **4.888 de 4.888** |
| entradas de tabla de partida | 4.548.107 |
| recortadas hasta el tejido | 15.792 (0,35 %) |

**El tejido explica exactamente lo que medía v64.** Elegir `r` conserva todos sus owners porque `owners(r)` contiene un tejido que los cubre a todos, y eso ya es teorema. Lo que falta demostrar es que ese tejido existe.

## 5. Lo que eso cambia

El muro, dicho con precisión, es ahora:

> **en un estado del review simétrico, `owners(r)` contiene un tejido que pasa por `r`.**

Es una propiedad **estática** de un solo estado. Ya no hay que razonar sobre lo que hará el review a continuación (qué borra, en qué orden, cuántas pasadas); eso lo cubre el teorema de supervivencia de una vez para siempre.

Y el candidato natural está a la vista: `T p := owners(p) ∩ owners(r)` casi es un tejido, y solo le sobra el 0,35 % de las entradas. Lo que habría que demostrar es que **quitar ese 0,35 % nunca deja vacío un paso de ningún nodo**. Es un argumento de tipo Helly: en cada paso siempre queda un owner compatible con todo. Encaja con lo que midió `--triangle` en v64: 0 huecos a longitud completa.

## 6. Lo que queda en firme y lo que no

**Demostrado:** el tejido generaliza `Woven` y sobrevive a los dos reviews y a los dos pinchazos; un tejido bajo `r` basta para que elegir `r` sea seguro.

**Medido a 0:** el mayor tejido dentro de `owners(r)` es siempre todo `owners(r)`.

**No demostrado:**
- que ese tejido exista siempre. Es el muro, ahora estático;
- que la lectura completa, una elección tras otra, mantenga las condiciones estructurales en cada estado. La simetría ya está demostrada; que los owners globales sean nodos y los enlaces, no;
- complejidad: cero teoremas.

La máquina original, el ejecutable y Julia siguen sin tocar.

Build: `lake build AbsSat` verde, 90 módulos, 0 `sorry`, 0 axiomas de proyecto.
