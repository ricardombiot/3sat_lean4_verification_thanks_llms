# Verificación para el Autor v73: la pieza 2, partida — el caso base demostrado y la diana medida

Ricardo, soy Claude (Opus 5). Fui a por la pieza 2, el no-retroceso bajo `BoundedScope`. **No la he cerrado**, y lo digo antes de nada. Lo que sí traigo es lo que este proyecto suele obtener de un asalto así: la obligación partida en dos, una mitad demostrada, la otra reducida a una frase, y una medición que corrigió mi idea de cuál era la frase.

---

## 1. Lo que queda a decidir, después del reductor

`CnfSelection.lean`. Una **selección** es una fila por cláusula; *concuerda* cuando sus filas nunca dan dos valores a la misma variable.

**Demostrado — una selección que concuerda es una solución** (`sat_of_agreeing`). Es el contenido de Helly en la moneda de las fórmulas: una fila pincha una variable o calla sobre ella, que es exactamente la forma 0/1/all de `ZeroOneAll.helly`. No necesita aciclicidad ni reductor.

**Demostrado — el reductor no pierde nada:**

```lean
theorem satisfiable_iff_agreeing_in_reduce (C : List Clause) :
    (∃ a, ∀ c ∈ C, SatClause a c) ↔
    (∃ sel, sel.map (·.1) = C ∧ Agreeing sel ∧
      ∀ p ∈ sel, ∃ cr ∈ reduce (initRels C), cr.1 = p.1 ∧ p.2 ∈ cr.2)
```

El `→` es la conservación de v72; el `←` es lo anterior. Buscar **dentro del punto fijo** no es más débil que buscar en todas partes. Por eso lo que queda es una sola frase, sin pasadas y sin grafo: *tras el reductor, si ninguna relación está vacía, las filas supervivientes admiten una selección que concuerda* — `NoBacktrack`. Con ella, `satisfiable_iff_nonempty_of_NoBacktrack`: una relación vacía **es** la insatisfacibilidad.

## 2. El caso base, demostrado — y es tu propio patrón otra vez

Donde el reductor deja **una sola fila por relación**, la selección forzada concuerda: la arco-consistencia tiene que apuntar a esa fila porque no hay otra a la que apuntar.

```lean
theorem NoBacktrack_of_singletons (C : List Clause)
    (hsingle : ∀ cr ∈ reduce (initRels C), ∀ r ∈ cr.2, ∀ r' ∈ cr.2, r = r') :
    NoBacktrack C                                            -- [propext, Quot.sound]
```

Es, línea por línea, lo que v19 y v40 hicieron con la máquina: el caso `NoChoice`, y `pairwiseOwned_of_fullyPinned` — en un estado totalmente pinzado hay un nodo por paso y la co-posesión sale sola. Aquí hay una fila por relación y la concordancia sale sola. Me pareció que valía la pena decirlo: el argumento de las fórmulas y el de tu máquina se están partiendo por el mismo sitio.

Y no es un caso raro: **el reductor pinza todo él solo en el 20 % de los prefijos de la clase** (275 de 1.368).

## 3. La medición corrigió la diana

Mi plan era reducir lo que falta a un paso local: *pinchar una relación en una de sus filas, volver a reducir, no vaciar nada*. Lo medí (`cnfmap --pickstep`), y el paso de una elección resulta ser **la obligación equivocada**:

| cinco semillas, 600 fórmulas | elecciones | alguna fila vale | **todas** valen |
|---|---|---|---|
| dentro de la clase | 5.690 | 5.690 | **5.690** |
| fuera | 77.111 | 76.888 | 45.925 |
| control Tseitin (paridad **impar**, UNSAT) | 736 | **736** | **736** |

Dentro de la clase aguanta incluso la forma fuerte —toda fila vale, no solo alguna—, que es la distinción que v41 ya trazó para la máquina entre `PickSome` y `PickValid`. Pero mira la última fila: **en Tseitin impar todas las elecciones valen también, y esas fórmulas no tienen ni una solución.** Un paso local no puede implicar lo que hace falta, porque se cumple en fórmulas insatisfacibles. Es la lección de v18 y de v60 repetida: aquí no hay invariante local que arrastrar; la propiedad es del recorrido entero.

## 4. La diana correcta, medida

Así que la obligación es el **descenso completo**: pinchar la primera fila de la primera relación que aún ofrece elección, volver a reducir, repetir hasta que quede una fila por relación. Goloso, sin retroceso, sin búsqueda.

| cinco semillas | descensos | llegaron a una selección | **fallaron en un prefijo satisfacible** | tuvieron éxito en uno UNSAT |
|---|---|---|---|---|
| **dentro de la clase** | **1.368** | **1.368** | **0** | **0** |
| fuera | 8.186 | 7.574 | 603 | 0 |
| control Tseitin impar | 67 | 58 | 6 | **0** |

Tres lecturas:

- **Dentro de la clase el descenso goloso nunca se atasca**, 1.368 de 1.368. Eso es `NoBacktrack` medido, y en su forma más exigente: sin retroceder y sin elegir bien.
- **Fuera falla de verdad**: 603 prefijos satisfacibles en los que el goloso se queda sin salida. La clase no está decorando.
- **La última columna es cero en todas partes**, y esa es la banda del teorema del §2: llegar a una selección implica satisfacibilidad, así que nunca puede pasar sobre un prefijo insatisfacible. Está demostrado y se cumple.

## 5. Lo que falta, dicho con precisión

`NoBacktrack` para la clase sigue **sin demostrar**. Lo que esta sesión cambia es que ya no es «formalizar BFMY» a bulto, sino un enunciado con diana medida:

> Bajo `BoundedScope φ K`, si el reductor deja toda relación no vacía, el descenso goloso alcanza una fila por relación sin vaciar ninguna.

y la inducción tiene que descender sobre las `K` rondas de `gyoIter_eq_nil_of_BoundedScope` (v71), con el caso base ya pagado (§2). El obstáculo honesto es que la aciclicidad hay que gastarla en el **recorrido**, no en un paso: la medición del §3 cierra esa puerta con números.

No te lo voy a vender como si estuviera cerca. Formalizar el argumento de Beeri–Fagin–Maier–Yannakakis sin Mathlib —árbol de unión, conectividad de las variables, la recursión que lo recorre— es un proyecto en sí mismo, y es la parte cara de todo este camino. Lo que hay ahora es el andamio entero montado a su alrededor: las definiciones, el caso base, la equivalencia que dice que no falta nada más, y la medición que dice que el enunciado es cierto donde lo vamos a demostrar.

Sobre el caso general: sigue aplazado, no descartado, y esta pieza lo deja algo mejor situado. Los 603 fallos de fuera de la clase son material reproducible para la pregunta de cuánto se puede ensanchar `BoundedScope` antes de que el descenso empiece a atascarse.

Build: `lake build AbsSat` verde, **99 módulos**, 0 `sorry`, 0 axiomas de proyecto, cierres en `[propext, Quot.sound]`.
