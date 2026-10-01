# Verificación para el Autor v219: revisión a fondo de `PrevCut` y `Star4At`

1 de octubre de 2026, rama `reader-stuck`. Continúa el v218. Este informe no trae resultados nuevos grandes: ordena
los niveles de abstracción que se han ido apilando, fija los índices, y revisa las dos hipótesis de las que cuelga hoy
el veredicto, para poder seguir sin perderse.

## 0. Dónde estamos, en una frase

`spineVerdictOn_iff_of_prev4`: la espina con la regla activa decide la satisfacibilidad si valen **`PrevCut`** y
**`Star4At`**. Todo lo demás está demostrado en Lean, sin `sorry` y con los axiomas estándar. Las dos están medidas sin
fallos y ninguna está demostrada.

## 1. Los niveles, de abajo arriba

| nivel | objeto | qué es | dónde |
|---|---|---|---|
| 0 | **mapa** | grafo por pasos; en el mapa bin, como mucho dos nodos de mapa por paso (índice 0/1), cada uno con un requisito (un nodo de un paso anterior) o ninguno; ventanas prohibidas de tres pasos seguidos | `CnfMapBin` |
| 0 | **nodo de camino** | `(id, parent_id, gparent_id)`: una ventana de tres colores seguidos. Dos nodos de camino del mismo paso pueden compartir `id` y diferir en el padre o el abuelo | `PathNodeId` |
| 1 | **estado** | vivos, aristas («posesiones», `Adj`), documentos (padres e hijos de cada nodo) y la lista de **tríos** prohibidos | `GPathB` |
| 1 | **trío prohibido** | `TF g a b r`: la arista `a–b` existe y `{a,b,r}` está en la lista. `Sym (TF g)` lo mismo en cualquier orden | `ForbidOnSound` |
| 1 | **cortar** | `SideForbids g (TF g) a b r`: a `g` le falta una de las tres aristas, o tiene el trío prohibido | `ForbidSound` |
| 2 | **filtro** | matar, en el paso de un requisito, los nodos de otro color; después, review | `filterAllOn` |
| 2 | **review** | limpieza, parejas, **regla de tríos**, padres/hijos, hasta el punto fijo | `reviewOn` |
| 2 | **UP** | fila nueva (una cima por ventana permitida), sus aristas, y `up_forbid` | `upOn` |
| 2 | **join** | unión de vivos y aristas; los tríos **se reinician** | `joinOn` |
| 3 | **línea** | las entradas de un paso de la máquina, una por nodo de mapa (clave) | `stepsM .on φ n` |
| 3 | **llegada** | `arrOn φ a d = upOn (filterAllOn a.2 (reqOf φ d)) d`: la entrada `a` enviada al destino `d` | `ForbidOnDriver` |
| 4 | **estado fijado** | `pinOn g R`: filtrar por los pins `R` y revisar con la regla | `ForbidOnPin` |
| 4 | **pins reales** | `PinsFrom φ k R`: `R` son los requisitos de un camino del mapa desde `k` | `ForbidOnDriver` |
| 5 | **invariante** | `TopAt g R`: toda cima viva de `pinOn g R` está en una camarilla que esquiva sus tríos | `ForbidOnTop` |
| 6 | **familia de la cima** | la cima `t`, sus vecinos, y las parejas cuyo trío con `t` no está prohibido | `ForbidOnStar` |
| 7 | **hipótesis** | `PrevCut`, `Star4At` | `ForbidOnStar` |

### Dónde nacen los tríos (nivel 2), que es lo que importa para las dos hipótesis

| quién | cuándo prohíbe `(a, b, r)` | consecuencia |
|---|---|---|
| **regla** (en el review) | el triángulo no tiene, en algún paso, un **testigo bueno**: un nodo vecino de los tres con sus tres caras nuevas sin prohibir | en el punto fijo, todo triángulo sin prohibir tiene testigo bueno en cada paso (`trioGood_low`) |
| **`up_forbid`** (en el UP) | `(n, w, r)` con `n` cima nueva, si **todos** los padres de `n` cortan `(p, w, r)` | una cara viva de la cima viene de **algún** padre que no la corta; padres distintos pueden sostener caras distintas |
| **join** | reinicia la lista: guarda `(a, b, r)` si **los dos lados** lo cortan (`tF_joinOn_of_cut`) | un trío muerto en un solo lado **revive** en la unión |

En lo medido la regla casi no prohíbe nada nuevo: los tríos vienen de los joins y se heredan hacia arriba por
`up_forbid`.

## 2. Los índices, fijados

Para un join de dos llegadas, con `T` el paso actual de la línea `prev`:

| línea | estados | paso actual | sus cimas están en el paso |
|---|---|---|---|
| `prev` | entradas `e` | `T` | `T - 1` |
| `advanceM prev` | entradas `a`, `b` (claves `a.1 ≠ b.1`) | `T + 1` | `T` (id = su clave) |
| la siguiente | llegadas `S = arrOn a d`, `O = arrOn b d`; unión `J = joinOn S O`; fijada `u = pinOn J R` | `T + 2` | `T + 1` (id = `d`) |

* Una cima `t` de `S` tiene por padres cimas de `a` (paso `T`), como mucho dos, que solo difieren en su abuelo (el
  color del paso `T - 2`).
* Los nodos del paso `T` de `S` son **exclusivos** de `S`: en `O` ese paso tiene el color de `b`.
* Una **base** bajo `t` es un triángulo `(x, y, z)` entre vecinos de `t`, sin `t`. Es **baja** si sus tres nodos
  están por debajo del paso `T` (ya existían en `prev`), y **alta** si tiene un nodo en el paso `T`.

## 3. El argumento que usa las dos hipótesis (`star_core`)

Para que la cima `t` de `u` (del lado `S`) esté viva en `pinOn S R`, se lleva su familia al lado y se mira **lo primero
que moriría** en el review de `pinOn S R`. Todo lo que contiene a `t` tiene en `u` un testigo que aún no ha muerto. Las
bases no. `star_core` pide para ellas dos cosas:

| | condición | qué pasa si falla | de dónde sale hoy |
|---|---|---|---|
| `hlow1` | una base prohibida en `S` (sin fijar) está prohibida en `u` | la familia, tal como es en `u`, no cabe en `S` desde el principio | `CrossCut` ⟸ `PrevCut` |
| `hlow2` | una base viva en `u` tiene en cada paso un nodo que completa el tetraedro (o no está en los tríos de `pinOn S R`) | la regla del lado podría prohibir la base, y con ella cortar aristas de la familia | `Star4At` |

Lo que **no** es hipótesis: que los nodos, las aristas y los tríos con `t` de la familia sobrevivan (demostrado), que
los vecinos en pasos consecutivos sean padre e hijo (`AdjPar`, demostrado), y la llegada entera (sin hipótesis).

## 4. `Star4At`

### 4.1 Enunciado

    def Star4At (J : GPathB) (Rp : List NodeId) : Prop :=
      (J.pinOn Rp).isValid = true → ∀ t ∈ (J.pinOn Rp).alive, t.id.step = J.current_step - 1 →
        ∀ a b r, Tetra (J.pinOn Rp) t a b r → ¬ Sym (TF (J.pinOn Rp)) a b r → ∀ l, 0 ≤ l → l < J.current_step →
          ∃ s, s.id.step = l ∧ (s = a ∨ s = b ∨ s = r ∨ s = t ∨ Wit4 (J.pinOn Rp) t a b r s)

* `Tetra u t a b r`: `a, b, r` vecinos distintos de `t`, vecinos entre sí, con las tres caras con `t` sin prohibir.
* `Wit4 u t a b r s`: `s` vecino de los cuatro, con las seis caras nuevas sin prohibir.

En palabras: **todo tetraedro vivo con cima se alarga, en cada paso, a un 5-conjunto con todas sus caras vivas**. Se
pide para `J` la unión de las dos llegadas y `Rp` un pin de `PinsFrom`. Habla solo de la unión fijada.

### 4.2 Qué añade a lo que ya da la regla

En el punto fijo, cada una de las cuatro caras del tetraedro tiene **su** testigo bueno en el paso `l`. `Star4At` pide
que haya **uno común**. Es una propiedad de tipo Helly sobre los nodos del paso `l`, que son pocos (cada uno una
ventana de tres colores).

### 4.3 Lectura por pasos

| paso `l` | qué dice `Star4At` | comentario |
|---|---|---|
| el de la cima | `s = t` | trivial |
| el de `a`, `b` o `r` | `s` es ese nodo | trivial |
| **`T`, el de los padres** | un vecino de `t` en el paso anterior, o sea un **padre** de `t` (`AdjPar`), sostiene las tres caras y la base | es la afirmación «si las caras de `t` solo las sostienen padres distintos, la base está muerta». Es el reverso de `PrevCut` (§6) |
| los de más abajo | un nodo común, vecino también de `t` | es donde hay contenido de nivel cinco |

### 4.4 Medidas

`probe_tetra.jl`, `FORBID=:on`. La sonda recorre los vecinos de cada cima viva de `U = pin(join, R)` y, para cada
tetraedro vivo y cada paso por debajo de la cima que no sea el de `a`, `b`, `r`, busca `s`.

| modo | pins | instancias | tetraedros | pasos | sin `s` |
|---|---|---|---|---|---|
| sin muestreo (`TRI_CAP=0`) | reales | `clause_mix`, `xor3`, `v4_c12_i1`, `v5_c20_i2` | 2 825 118 | 80 578 105 | 0 |
| muestra de 150 por cima | al azar | `clause_mix`, `clause_mix_sep`, `v5_c20_i2`, `v5_c20_i3` | 200 250 | 4 495 500 | 0 |
| muestra de 150 por cima | reales | las mismas | 122 700 | 2 763 450 | 0 |

**La sonda mide el enunciado Lean**: mismos estados (`pin` = filtro + review con la regla), mismas condiciones, y los
pasos que la sonda salta son los que Lean resuelve con `s = a, b, r, t`.

### 4.5 Lo que no sabemos de `Star4At`

* **Quién es `s`.** No está medido si es único, ni si es siempre padre o hijo de alguno de los cuatro, ni si es el
  mismo nodo que sirve de testigo a las cuatro caras por separado.
* **Tamaño.** Lo más grande medido sin muestreo es `v5_c20_i2`. No hay medida en `v6`, `v7`.
* **Si hace falta entera.** El argumento solo la usa para que la regla del lado fijado no prohíba una base. Bastaría
  algo más débil: `StarTriAt` (la base no está en los tríos del lado fijado), que también está medida sin fallos (29 M).

### 4.6 Por dónde atacarla, y un aviso de circularidad

* **Subir desde un lado.** Si la familia de `t` en `u` es la misma que en `pinOn S R`, un `s` del lado sirve en la
  unión, porque el lado fijado vive entero en la unión (`downInv_side`). Pero que la familia de `u` quepa en el lado es
  justo lo que `star_core` demuestra **usando** `Star4At`. Cualquier inducción tiene que romper ese círculo: demostrar
  el cierre a nivel cuatro del **lado** primero, y de ahí el de la unión, sin pasar por la familia.
* **Heredar por el padre.** Si un padre `p` de `t` sostiene el tetraedro entero, `(p; a, b, r)` es un tetraedro vivo
  con cima un nivel más abajo, y su `s` es vecino de `t` en el momento del UP. Falta que esa vecindad y sus caras
  sobrevivan al review fijado; hoy la dirección 1 solo sube camarillas enteras, no 5-conjuntos.
* **Lo nuevo en cada UP** es el paso de los padres (§4.3): que haya un padre que lo sostenga todo.

## 5. `PrevCut`

### 5.1 Enunciado

    def HPrevCut (φ : Cnf) (prev : Line) (T : Int) : Prop :=
      ∀ a ∈ advanceM .on φ prev, ∀ d, SendsOn φ a d → ∀ t x y z, t ∈ (arrOn φ a d).alive →
        t.id.step = (arrOn φ a d).current_step - 1 → x ≠ t → y ≠ t → z ≠ t → x ≠ y → x ≠ z → y ≠ z →
        (arrOn φ a d).Adj t x → … → (arrOn φ a d).Adj y z →
        ¬ Sym (TF (arrOn φ a d)) x y t → ¬ Sym (TF (arrOn φ a d)) x z t → ¬ Sym (TF (arrOn φ a d)) y z t →
        TF (arrOn φ a d) x y z → x.id.step < T → y.id.step < T → z.id.step < T →
        ∀ e ∈ prev, SideForbids e.2 (TF e.2) x y z

En palabras: en una llegada `S`, **una base baja prohibida bajo una cima con sus tres caras sin prohibir ya la cortaban
todas las entradas de la línea de dos pasos atrás**. Habla de un triángulo y una línea. No hay segundo lado, ni pins,
ni review.

### 5.2 La cadena que la convierte en `hlow1`

| paso | lema | estado |
|---|---|---|
| todas las entradas de `prev` cortan la base ⟹ todas las de la línea siguiente la cortan | `lineCut_advance` (`sideForbids_arrivalOn` + `sideForbids_joinOn`) | demostrado |
| las bases **altas** las corta la otra entrada sin más: su nodo del paso `T` no está en `b` | dentro de `crossCut_of_prevCut`, por `TopDocsId` | demostrado |
| ⟹ `CrossCut S b.2` (contra la entrada que envía la otra llegada) | `crossCut_of_prevCut` | demostrado |
| ⟹ `CrossCut S O` (contra la otra llegada) | `crossCut_of_sender` | demostrado |
| ⟹ el join guarda la base ⟹ está prohibida en `u` | `tF_joinOn_of_cut`, `star_alive4` | demostrado |

### 5.3 Medidas

`probe_linecut.jl`, columnas `pc_*`, sobre **todas** las llegadas válidas (con uno o dos remitentes):

| instancia | bases bajas | alguna entrada de `prev` no la corta | bases altas |
|---|---|---|---|
| `clause_mix` | 300 | 0 | 54 |
| `clause_mix_sep` | 1 688 | 0 | 246 |
| `v5_c20_i1` | 584 | 0 | 116 |
| `v5_c20_i2` (UNSAT) | 144 | 0 | 48 |
| `v5_c20_i4` | 72 | 0 | 24 |
| `v6_c26_i1` (UNSAT) | 520 | 0 | 79 |
| `v6_c26_i2` | 563 | 0 | 55 |

`v7_c30_i1` no se pudo medir: la sonda guarda una copia de cada envío y el guardián la cortó al pasar de 4 GB.

### 5.4 Lo que se sabe por dentro

`probe_crosscut.jl`, 4 108 bases en 7 instancias (`clause_mix`, `clause_mix_sep`, `v5_c20_i1`, `i2`, `i4`,
`v6_c26_i1`, `v6_c26_i2`), solo en las llegadas que entran en un join:

| hecho | cuenta |
|---|---|
| la otra llegada no corta la base | 0 |
| la base **ya estaba prohibida en el remitente** de su llegada | 4 108 de 4 108 |
| la base ya estaba cortada en el remitente de la otra | 4 108 de 4 108 |
| bases bajas / altas | 3 538 / 570 |
| **nacimiento**: la cima tiene dos padres complementarios | 3 816 |
| **herencia**: un solo padre tiene las tres caras vivas | 292 |

**El patrón de nacimiento es siempre el mismo.** Con las caras escritas (12, 13, 23), `o` viva, `D` prohibida, `-`
falta una arista:

| padre que ve los tres nodos | el otro padre | casos |
|---|---|---|
| `Doo` | `o--` | 2 169 |
| `oDo` | `-o-` | 1 103 |
| `ooD` | `--o` | 544 |

Un padre es vecino de los tres nodos y tiene **una** cara prohibida. El otro tiene viva justo esa cara y **no es
vecino del tercer nodo**. Los dos padres solo difieren en el color del paso `T - 2`. Leído así: el tercer nodo es
incompatible con un color de ese paso, y la pareja de los otros dos lo es con el otro color.

**Historia** (`probe_linecut.jl`, 3 instancias): en torno al 70 % de las bases están cortadas en todas las entradas
desde la línea en que existe su nodo más alto; el resto pasa a estarlo más tarde, y en lo medido siempre lo está ya
en `prev`.

### 5.5 Descomposición propuesta: herencia, nacimiento, y un tercer caso que no se ve

Una base `B` de `PrevCut`, bajo la cima `t` de `S = arrOn a d`, cae en uno de tres casos:

| caso | qué pasa | cómo se cierra |
|---|---|---|
| **A. herencia** | `B` prohibida en `a`, y un padre `p` de `t` tiene las tres caras vivas en `a` | **por inducción**: `(p; B)` es la misma situación una línea más abajo. Si `a` es una unión, `p` es de un solo lado, sus caras viven en esa llegada y el join guardó `B` porque esa llegada la cortaba: es `PrevCut` del nivel anterior, y `lineCut_advance` lo sube |
| **B. nacimiento** | `B` prohibida en `a`, ningún padre con las tres caras vivas: dos padres complementarios | **abierto**. Es el contenido de `PrevCut` |
| **C.** | `B` no estaba prohibida en `a`: la prohíbe la regla en el review del filtro o del UP | **no observado** (0 de 4 108). Hay que demostrar que no pasa, o dejarlo como hipótesis aparte |

Para formalizar A hacen falta dos lemas que hoy no existen y parecen demostrables:

1. **`up_forbid` es completo**: si una cara `(t, x, y)` de una cima nueva no está prohibida en la llegada, algún padre
   de `t` no cortaba `(p, x, y)`. Es el análogo para el UP de `tF_joinOn_of_cut`.
2. **El tetraedro de una unión es el de una llegada**: si `p` es cima de `a = joinOn A₁ A₂` con sus tres caras vivas y
   `B` prohibida en `a`, entonces `p` es de un lado, sus caras viven en él, y `B` está prohibida en él.

Con eso `PrevCut` quedaría reducida a **B + C**: una afirmación sobre el UP con dos padres, y otra sobre la regla.

**Una salvedad sobre A.** La inducción cierra el caso en que la base también es baja un nivel más abajo. Si la base
tiene un nodo en la cima de `prev` (paso `T - 1`), el nivel anterior la ve como base alta: la entrada de `prev` que no
tiene ese nodo la corta sin más, pero para la que sí lo tiene hace falta que la base ya viniera cortada de ella, y eso
es otra vez el caso C, un nivel abajo. No está resuelto en el papel.

### 5.6 Un aviso

`PrevCut` no es forzosa por lógica. Tres nodos compatibles dos a dos con un color pueden, juntos, forzar el otro. Vale
en lo medido porque la máquina **ya detectó** la muerte de esas bases a nivel de tríos dos líneas atrás. La prueba
tiene que salir de cómo se construyen los tríos (join, `up_forbid`), no de la semántica de las soluciones.

## 6. Cómo encajan las dos

Miran el mismo objeto, una base bajo una cima con sus tres caras vivas, desde dos lados:

| | base **viva** en la unión fijada | base **prohibida** en la llegada |
|---|---|---|
| hipótesis | `Star4At` | `PrevCut` |
| qué dice | hay un nodo, en cada paso, que sostiene el tetraedro entero | la base ya estaba cortada en toda la línea anterior |
| en el paso de los padres | **un** padre sostiene las tres caras y la base | si las caras las sostienen padres **distintos**, la base viene muerta de atrás |
| caso de herencia | el tetraedro baja al padre | el tetraedro baja al padre |
| caso de nacimiento | no puede haber (lo excluye `Star4At`) | es lo abierto |

Es decir: **dos padres complementarios solo aparecen sobre bases muertas**. Esa frase es la intersección de las dos
hipótesis, y es lo que habría que entender.

## 7. Lo que es falso (para no volver)

| afirmación | medida |
|---|---|
| `TopFace`: en un lado, un triángulo prohibido no tiene una cima vecina con sus tres caras vivas | falso: 300 de 2 775 (`clause_mix`), 1 688 de 13 671 (`clause_mix_sep`), 144 de 764 (`v5_c20_i2`) |
| `LineCut`: prohibido en una entrada ⟹ cortado en la otra entrada de la línea | falso: 184 en `clause_mix_sep`, todos con dos caras vivas |
| los dos lados de un join coinciden en sus tríos | falso (los mismos 184) |
| la cima de una base de `PrevCut` tiene siempre dos padres complementarios | falso: 292 casos de herencia con un solo padre |
| un triángulo prohibido bajo una cima tiene 0 o 1 caras vivas | no se ve nunca: siempre 2 o 3 |

## 8. Huecos de medida

* Ninguna de las dos está medida en `v7` ni mayores.
* `Star4At` sin muestreo, solo en 4 instancias pequeñas.
* `PrevCut` en 7 instancias; los casos B y C de §5.5 no están contados por separado sobre todas las llegadas (el
  patrón de padres se midió solo en las llegadas que entran en un join).
* No está medido quién es el nodo `s` de `Star4At`.

## 9. Plan

1. **Formalizar la herencia de `PrevCut`** (§5.5, lemas 1 y 2 y la inducción). Reduce `PrevCut` a nacimiento + caso C.
   Es trabajo demostrable con lo que hay.
2. **Medir el nacimiento por dentro**: en los 3 816 casos, desde qué línea está cortada la base en todas las entradas,
   y si la incompatibilidad con cada color del paso `T - 2` ya se ve en la línea donde ese paso es la cima.
3. **Medir quién es `s`** en `Star4At`, empezando por el paso de los padres: ¿es siempre un padre de `t` que además
   sirve de testigo a las cuatro caras por separado?
4. **Decidir** con 2 y 3 si las dos hipótesis se pueden fundir en la frase de §6.
5. Solo después, tamaño (`v6`, `v7`) y, si procede, acotar la clase portando `PreClause`.

## Ficheros y teoremas

| fichero | qué tiene |
|---|---|
| `ForbidOnArr`, `ForbidOnGood`, `ForbidOnDriver`, `ForbidOnSide` | llegada, join con pins, inducción de línea, recíproco |
| `ForbidOnTop` | `TopAt`, `TopSideAt`, `spineVerdictOn_iff_of_topOn`, `verdictOn_certified` |
| `ForbidOnParts` | `sideGraph`, `tF_joinOn_of_cut`, `TopsFrom`/`TopDocsId` en `:on` |
| `ForbidOnKeep` | `TrioGoodK`, `downInv_pinOnK` |
| `ForbidOnStar` | `AdjPar`, `star_core`, `StarTriAt`, `CrossCut`, `Star4At`, `lineCut_advance`, `HPrevCut`, los veredictos |

| veredicto | hipótesis |
|---|---|
| `spineVerdictOn_iff_of_topOn` | `TopSideAt` |
| `spineVerdictOn_iff_of_starTri` | `StarTriAt` |
| `spineVerdictOn_iff_of_cross4` | `CrossCut` + `Star4At` |
| `spineVerdictOn_iff_of_sender4` | `CrossCut` contra el remitente + `Star4At` |
| `spineVerdictOn_iff_of_prev4` | `PrevCut` + `Star4At` |

Sondas: `probe_tetra.jl` (`Star4At`, `CrossCut`), `probe_linecut.jl` (`PrevCut`, `LineCut`, historia),
`probe_crosscut.jl` (clases y patrones de padres), `probe_startri.jl` (`StarTriAt`). Commits desde el v218:
`0a9f129`, `f4f2084`, `6cb97ca`.
