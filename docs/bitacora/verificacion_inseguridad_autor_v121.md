# Verificación para el Autor v121: tu barrido en todos los pasos, con filtro simétrico, cierra el borde

Ricardo, soy Claude (Opus 5). Este tramo tiene dos partes. La primera fue buscando la estabilidad de
`SPC` (v120) y encontró que la reducción de v117–v120 tenía una hipótesis **falsa** con el barrido de
entonces: la fijación exacta fallaba en los pasos extremos. La segunda incorpora tu cambio del
14-sept (barrido en todos los pasos y filtro de entradas asimétricas) al espejo en Lean. Con él, las
pruebas se simplifican: la simetría sale de la regla de parada, `BoundarySym` desaparece como
obligación, y las excepciones medidas desaparecen.

Todo en la rama `spaik`, en el build de `AbsSat` (171 jobs), sin `sorry`, en `[propext, Quot.sound]`.

---

## 1. Lo que salió mal con el barrido anterior (pasos `cs−2 … 1`, sin filtro simétrico)

### 1.1 `SPC` no tiene estructura local (`helly spc`, `helly hered`)

En Tseitin K4 par y `par_k3`:

- **Cierre de triángulos, falso**: `SPC(x,v)`, `SPC(x,z)` y `z` owner de `v` no implican `SPC(v,z)`
  (114.688 fallos de 4,5 M en K4 par; 63.014 de 14,6 M en `par_k3`).
- **Mitad débil, cierta**: en cada casilla hay un testigo `SPC` con `x` (0 casillas sin él).
- **Dónde fallan los testigos malos**: en cualquier paso, la mayoría a 7 o más pasos de distancia. No
  hay argumento local por padres e hijos.

### 1.2 La rebanada doble del estado base no se conserva (`helly pins2`)

En `par_k3` (2.523 pares de fijaciones): el orden no importa (fijar `a` y luego `b` da lo mismo que
fijar los dos a la vez, en las 2.043 válidas), pero la cascada elimina 2.026 nodos de la rebanada
"owner de un portador de `a` y de uno de `b`". Formalicé una reducción de todo el lector al estado
base basada en esa rebanada (`SliceChain`) y **la borré sin añadirla al build**: su hipótesis es
falsa.

### 1.3 `PinExact` fallaba a profundidad 2 del lector (`helly depth2`, `helly walk`)

v117 y v118 midieron fijaciones simples en estados de la máquina, nunca en estados del lector ya
fijados. Al medirlo:

| sonda | familia | fijaciones | inválidas | nodos de rebanada eliminados | en fijaciones del paso 0 o `cs−1` | en pasos interiores |
|---|---|---|---|---|---|---|
| `depth2` | Tseitin K4 par | 3.936 | 0 | **32** | **32** | 0 |
| `walk` (6 paseos) | Tseitin K4 par | 960 | 0 | 2 fijaciones inexactas | **2** | 0 |

**Todas las excepciones eran fijaciones en un paso extremo**, justo los que tu barrido no recorría.
Consecuencia: `sat_of_pinExact` pedía `PinExact` en *todas* las fijaciones de *todos* los estados del
lector, y eso era falso con aquel barrido. Lo demostrado seguía siendo correcto; esa vía no podía
cerrarse.

## 2. Tu cambio, en el espejo de Lean (`AggressiveReview.lean`)

`agressive_consistence_filter!` (Julia, 14-sept) hace ahora, para cada `w` owner válido de `x`:

- **asimétrica** (`symmetric_entry`): si `x` no está en los owners de `w`, se borra `w` de `x`, solo
  en esa dirección;
- **inconsistente**: si la entrada es simétrica pero las tablas no comparten algún paso, se borra el
  par en los dos sentidos.

`aggPair` hace exactamente eso, y `aggNode`/`aggSweep` recorren **todos** los pasos,
`current_step − 1 … 0`.

**Un detalle del rango.** En tu Julia los dos bucles van `current_step-1:-1:1`: el paso 0 sigue fuera.
Me dijiste que el barrido debe recorrer todos los pasos, así que el espejo baja hasta 0. Es la misma
situación que `review_owners_sons_parents!` en v48, donde saltarse el paso 0 era un error. Para que
Julia y Lean coincidan, en Julia basta cambiar el `1` final por `0` en los dos bucles.

Todo lo que dependía del barrido se ha adaptado y compila: conservación de cadenas
(`ChainSound_aggPair`, nada de una solución se pierde), `Keeps`, `AggInvariants`, `AnchoredSurvive`,
`AggFixpoint`, `SliceSupport`, `SliceExact`. Los `#guard` de veredicto siguen pasando.

## 3. Lo demostrado con el barrido nuevo

- **`AggFixpoint.AggOk`**, ahora en **todos** los pasos y con las dos pruebas: todo par de owners de
  nodos válidos es **simétrico** y comparte cada paso. `aggOk_reviewAgg`: todo resultado válido de
  `reviewAgg` lo cumple. La prueba es la de v118 con una rama más: un par asimétrico también baja la
  medida (`measure_aggPair_lt`).
- **`PinExactBoundary.ownSymmetric_of_aggOk`**: simetría completa en todo estado del lector.
  **`BoundarySym` deja de existir como obligación.**
- **`AnchoredSurvive.Sup`** incorpora `sym` (la relación de soporte es simétrica), y la condición de
  pares cubre todos los pasos. Toda operación del review y del barrido la conserva, incluida la rama
  asimétrica: un `R`-enlace nunca es asimétrico.
- **`SliceExact.supported_iff_pinExact_run`** se mantiene: `Supported ↔ PinExact` en los estados del
  lector (la simetría del testigo sale de `AggOk`).
- **Veredicto**, sin hipótesis de borde:
  - `PinExactBoundary.sat_of_pinExactAgg`: basta `PinExact` en los estados del lector;
  - `SliceSupport.sat_of_supported`: basta `Supported`;
  - nuevo **`PinExactSome.sat_of_someSupported`**: basta **una** fijación con soporte por estado con
    elección, que es lo único que usa el bucle del lector.

## 4. Medido con el barrido nuevo

| sonda | familia | fijaciones | inválidas | nodos de rebanada eliminados / fijaciones inexactas |
|---|---|---|---|---|
| `depth2` | Tseitin K4 par | 3.936 | 0 | **0** (antes 32) |
| `walk` (6 paseos) | Tseitin K4 par | 960 | 0 | **0** (antes 2) |
| `walk` (6 paseos) | `par_k3_direct_asc_fresh` | 1.198 | 0 | **0** |
| `walk` (2 paseos por estado final) | aleatorias, 6–8 variables (semilla 1001, 20 fórmulas; 36 paseos, 110 estados) | 3.677 | 0 | **0** |

En los paseos, todos los estados con elección tienen una fijación exacta, y ninguno tiene elección
solo en los pasos extremos.

Las medidas de v117–v120 (rondas, puntos fijos, testigos) se hicieron con el barrido anterior. Hay
que repetirlas con el nuevo; espero que el borde deje de aportar rondas.

## 5. La cadena, tal como queda

```
estado final de pureRunW                           MInv (+ SMP, PMS, SN)         demostrado
  todo estado del lector es resultado de reviewAgg AggOk: simetría y pares,     demostrado (v121)
                                                   en todos los pasos
  en cada estado con elección, alguna fijación     Supported (⇔ PinExact)        medido, abierto
  con rebanada con soporte
    ⇒ esa fijación es válida ⇒ PickSomeAgg                                       demostrado
    ⇒ el lector acaba en un camino ⇒ modelo de φ                                 demostrado (v116)
```

## 6. Lo que queda

1. **`Supported` en los estados del lector**, ahora con una sola fijación por estado y sin borde. Es
   la única obligación abierta de la cadena.
2. **Repetir las sondas con el barrido nuevo**: `rounds`, `gfpE`, `hered`, `walk` en aleatorias y en
   familias mayores. Si el borde deja de hacer rondas, `SPC` en todos los pasos sería el soporte entero
   y la pregunta de v120 queda en una sola pieza.
3. **Alinear el rango en Julia** (paso 0), si estás de acuerdo.
