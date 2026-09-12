# Verificación para el Autor v88: `up` y `down` no fallan en las tablas — el estado válido **es** un tejido entero

Ricardo, soy Claude (Opus 5). Tienes razón en la corrección y me hizo cambiar el método: antes de
declarar residuo una cláusula que falla, hay que preguntar **por qué** falla. Lo he medido, y la
respuesta parte P4 en dos mitades muy desiguales — una la he demostrado hoy, y la otra tiene nombre
y tamaño.

---

## 1. Por qué fallan `up` y `down`

Modo nuevo `--p4why`. Para cada pinchazo `q`, cada miembro `p` de `owners(q)` y cada entrada `v` de
su tabla, clasifico el fallo en dos:

* **tabla** — no hay *ningún* padre que lleve `v`, ni siquiera ignorando `owners(q)`;
* **relativo** — lo hay, pero nunca dentro de `owners(q)`.

Máquina del triángulo, tres semillas — **49,5 millones de pares `up` y 49,3 de `down`**:

| semilla | pares `up` | **sin padre, en ninguna tabla** | padre fuera de `owners(q)` |
|---|---|---|---|
| 1001 | 8.693.832 | **0** | 428 |
| 7777 (sim+tri) | 13.263.494 | **0** | 970 |
| 31337 | 27.564.473 | **0** | 4.047 |

Y sobre la máquina **original**, donde la simetría y el triángulo no valen: de los 674 fallos de
`up` y 527 de `down` en la semilla 1001, **todos** son relativos; ninguno de tabla.

> **La cláusula no falla nunca al nivel de las tablas. Falla sólo relativa al pinchazo.**

(Honestidad sobre el control: el contador «sin padre» no se dispara en ninguna de las corridas, así
que no puedo presentarlo como control positivo. Lo que sí muestra la medición es que la
clasificación es exhaustiva sobre los fallos, y que **todos** caen en el cubo relativo.)

## 2. Y la mitad de tablas, demostrada

```lean
theorem table_up   … : ∃ c ∈ n.parents, ∃ mc, g.node? c = some mc ∧ c ∈ n.owners ∧ v ∈ mc.owners
theorem table_down … : ∃ c ∈ n.sons,    ∃ mc, … ∧ p ∈ mc.parents ∧ c ∈ n.owners ∧ v ∈ mc.owners
```

La clave es un lema que no estaba y que me parece de los bonitos del proyecto:

```lean
theorem owner_pred_is_parent … (hv : v ∈ n.owners) (hvs : v.id.step = p.id.step - 1) :
    v ∈ n.parents
```

> **Un owner que está un paso por debajo de un nodo es un padre suyo.**

Sale de dos cosas tuyas juntas: la pasada de coherencia deja `owners(p)` dentro de la unión de las
tablas de los padres, y `OOS` dice que la tabla de un padre **en su propio paso** no contiene más
que a ese padre. Luego esa unión, en ese paso, **es exactamente el conjunto de padres**.

Con eso, `up` es inmediato: `p` y `v` se poseen mutuamente, el **triángulo de v69** les da una
entrada común `w` un paso por debajo de `p`, ese `w` es entonces un padre de `p`, está en la tabla
de `p`, y la **simetría de v64** pone `v` en la tabla de `w`. Las tres condiciones a la vez, y cada
paso es una decisión de diseño tuya.

## 3. Lo que sale de ahí: el estado válido **es** un tejido

```lean
theorem Fabric_whole (g : GPathM) (ctx : TableCtx g) … :
    Fabric g (nodos en rango) (sus propios owners)        -- [propext, Quot.sound]
```

**Las nueve cláusulas, sobre el estado entero, sin pinchazo.** No «existe algún tejido»: el estado
mismo lo es. Es el enunciado más fuerte que hemos podido escribir sobre lo que tu máquina mantiene,
y encaja con todo lo que veníamos midiendo sin entender del todo (v65: el tejido dentro de
`owners(r)` era **todo** `owners(r)`; v77: cubría siempre).

Y dice exactamente dónde vive la dificultad de P4: **no en las cláusulas, que valen a pelo, sino en
conservar un testigo de cada una *dentro de `owners(q)`*** cuando el pinchazo restringe los
miembros.

## 4. El paso de diseño que esto pide

`TableCtx` —la hipótesis de §3— pide **simetría** y **triángulo** a la vez. Y ahí está la cosa:

| | simetría (v64) | triángulo (v69) |
|---|---|---|
| `reviewSym` | ✅ teorema | ✗ |
| `reviewTri` | ✗ (falsa, medida en v86) | ✅ teorema (v85) |

**Ninguna de tus dos máquinas tiene las dos.** La combinación —review simétrico *y* pasada del
triángulo— no existe en el modelo; la definí sólo dentro del código de medición para v87, y ahí se
comporta (columna `symtri`: simetría 0, `support` 0). **Ese es el paso de diseño concreto que pide
este resultado**: unir tus dos correcciones en una sola máquina. No es un parche, es la hipótesis
del teorema de §3.

## 5. Y lo que queda de `PinNonEmpty`

Como el candidato falla `up`/`down` sólo relativamente y sólo en el 2% de los pinchazos, el tejido
que hay dentro es el candidato **estrechado**. Medido (`--p4narrow`, máquina del triángulo,
**53.639 pinchazos** en dos semillas):

```
  narrowed star is EMPTY          = 0
  COVERS every step               = 53.639   (todos)
  loses `q` itself                = 0
```

Cero vacíos, cero pasos perdidos, cero pérdidas de `q`. Así que `PinNonEmpty` es cierta en todo lo
medido, y el enunciado que hay que demostrar tiene ahora una forma conocida: **«el estrechado del
candidato del lector no vacía ningún paso»** — que es literalmente la forma de P3, un nivel más
arriba. P3 salió porque el triángulo daba el testigo; ésta pedirá el testigo **compartido con un
tercer nodo**, que es la cuarta grada de la escalera que v70 señaló.

Y lo digo una vez, sin insistir: si esa grada se sube y `PinNonEmpty` queda demostrada en general,
la ruta entera se cierra y eso es P=NP. No es razón para no intentarlo —tú has dicho que quieres
intentarlo progresivamente y estoy de acuerdo—, es razón para no sorprenderse cuando el último paso
resista. Hoy hemos pasado de «dos cláusulas fallan» a «fallan sólo relativas, el 0,015% de los
pares, y el estrechado nunca vacía nada».

## 6. Estado

| pieza | estado |
|---|---|
| **P1** el tejido nace | ✅ v78 |
| **P2** lo preservan las operaciones y el `join` | ✅ v65 + v79 |
| **P3** el pinzado cubre y no se estrecha | ✅ cerrada (v83–v86) |
| **P4** el puente a `PickSome` | 7 cláusulas (v87) + **`up`/`down` de tabla demostradas (hoy)**; residuo: el testigo **relativo**, 0,015% de pares; estrechado medido sin vacíos en 53.639 pinchazos |
| **P5** cierre con `L7` | libre |

Build: `lake build AbsSat` verde, 100 módulos, 0 `sorry`, 0 axiomas de proyecto. Nuevos:
`CoherentParents`, `TableCtx`, `exists_owner_of_mem_unionOwnersOf`, `owner_pred_is_parent`,
`owner_succ_is_son`, `table_up`, `table_down`, `Fabric_whole` — todos en `[propext, Quot.sound]`.
