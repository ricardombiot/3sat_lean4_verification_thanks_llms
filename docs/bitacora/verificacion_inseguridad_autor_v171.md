# Verificación para el Autor v171: la conservación de `ImprovesCima` — el suelo puesto, y lo que falta con nombre y apellidos

Ricardo, soy Claude (Opus 5). Este informe sigue a v170 y cubre una etapa corta pero que cambia dos
cosas: **encontré que dos piezas que yo daba por difíciles ya estaban demostradas**, y **cambié una
definición de la máquina** — quiero que lo veas antes de seguir. Rama `spaik`, módulo
`ImprovesCima.lean`. Build de `AbsSat` (232 jobs), sin `sorry`, axiomas `[propext, Quot.sound]`.

## 0. Resumen

* Las dos piezas que llamé fases C y D —que el camino genuino es una cadena del estado, y que vive en
  un lado— **ya eran teoremas** (`line_complete`, `send_complete`). Lo comprobé compilándolos, no de
  memoria. Mi estimación de riesgo para D era mala.
* **Cambié `advanceCima`**: ahora tira las claves cuyo estado la regla deja muerto, como hace el driver
  de `Improves`. Sin eso ninguna invariante de línea se sostiene.
* Demostrado: **toda línea de `ImprovesCima` es una línea de la máquina** (`LineInv_stepsCima`), y
  **todo estado vivo suyo es un estado de máquina** (`MInv_reviewCima`).
* Generalicé `send_complete` a cualquier estado (`send_complete_of`), que es lo que permite que una
  máquina con otra línea lo use.
* **No cerré la conservación.** Falta un teorema, `cima_chain_below`, con base, paso y dependencias
  localizadas. La sección 5 las lista por nombre y fichero.

## 1. El hallazgo

Al explorar la fase D —"el camino genuino vive en un solo lado"— fui a buscar qué había en el
repositorio antes de ponerme a demostrarla, y estaba hecha:

```
RunNoBorrow.send_complete  — un envío contiene todo camino genuino que pasa por su fuente
RunNoBorrow.line_complete  — todo estado de una línea contiene todo camino genuino que acaba en su clave
```

Y **un lado es un envío**: `sidesOf` no hace otra cosa que recoger los envíos válidos de la línea. Así
que `send_complete` dice literalmente la fase D. Lo verifiqué compilando las dos como una línea cada
una, para no fiarme de mi lectura.

Dicho claro: el riesgo que yo veía en D no estaba en la matemática, estaba en mi memoria del
repositorio. Conviene que quede escrito, porque es el tipo de error que hace perder semanas.

## 2. La corrección que sí importa

Esos dos teoremas hablan de las líneas de **`Improves`**. Las de `ImprovesCima` **divergen** a partir de
la primera unión: la regla estrecha cada estado, así que no son los mismos objetos.

Hace falta la versión Cima. Y ahí la buena noticia vuelve, porque el eslabón que la hace posible también
está demostrado:

> camino genuino → cadena del estado → cadena de un lado → **sobrevive a la regla**
> (`ChainSound_reviewCima_of_side`)

## 3. El cambio en la máquina

`advanceCima` mapeaba cada estado por el review con la regla y lo **dejaba en la línea aunque la regla
lo matara**. El driver de `Improves` no hace eso: un envío que no sobrevive no se inserta.

Ahora las tira. Dos razones:

* **Técnica**: `StateOkF` exige que el estado esté vivo. Una línea con un cadáver dentro no cumple
  ninguna invariante, y sin invariantes de línea no hay inducción.
* **De diseño**: un estado muerto es la respuesta UNSAT para esa clave. No pinta nada en la línea, y
  dejarlo dentro hacía que `runCima` no vacío dejara de significar lo que significa en `Improves`.

Era una asimetría mía al escribir `advanceCima`, no algo de tu diseño. Lo señalo por si en tu
implementación estuviera igual.

## 4. Lo demostrado en esta etapa

* **`send_complete_of`** — el envío contiene todo camino genuino que contenga su fuente, **para
  cualquier estado**. Al abrir la demostración vi que de la línea solo usaba dos cosas: las invariantes
  del estado y la cadena. Se las pido directamente y el teorema se suelta de `Improves`.
  `send_complete` queda como corolario suyo.
* **`MInv_reviewCima`** — un estado vivo de `ImprovesCima` es un estado de máquina. Todo menos una
  cláusula sale de `MInv_of_keeps`; la que no es *"los dueños de un nodo son nodos"*, que **no se hereda
  al estrechar** —si un nodo muere, alguien puede quedarse apuntándolo—. Sale de la forma del propio
  review: el resultado es un punto fijo de la revisión agresiva, donde un dueño es dueño global y un
  dueño global es un nodo.
* **`LineInv_advanceCima`, `LineInv_stepsCima`** — toda línea de la ejecución con la regla es una línea
  de la máquina: claves sin repetir, forma, paso y padre heredados del estrechamiento, `MInv` de lo
  anterior, y todas vivas.
* Andamiaje: `stepsCima_succ`, `mem_advanceCima`, `valid_of_mem_advanceCima`.

Con eso, **un estado de una línea Cima ya se le puede entregar a `send_complete_of`**. Antes no.

## 5. Lo que falta, con nombre y fichero

Un solo teorema:

```
cima_chain_below :  para todo camino genuino que acaba en el paso m,
                    la línea m de runCima tiene, en su nodo, un estado que lo contiene
```

Base (m = 0): la línea 0 es `pureInit`, y vale `pureStepsW_chain_below`.

Paso (m → m+1), con todas sus dependencias ya localizadas:

| lo que hace falta | dónde está |
|---|---|
| el hijo es hijo del nodo anterior | `advance_targetF` (`ConservationFilter`) |
| el camino cumple los requisitos débiles | `weakReqOfCnf_sound_below` (`ConservationPrefix`) |
| …y los duros | `reqSat_selOfAssign` (`CnfSel`) |
| la cadena sobrevive al fijado del envío | `keepsBranch_Fsac_below` (`ConservationPrefix`) |
| la cadena del envío, **sin pedir validez** | `chainSound_up_of_prunedR` (`ConservationCore`) |
| **una cadena hace válido a su estado** | `PickInduction.isValid_of_ChainG` |
| la cadena pasa a la unión por clave | `CarriesF` / `outer_fold_monoF` (`ConservationFilter`) |
| la cadena sobrevive a la regla | `ChainSound_reviewCima_of_side` (`ImprovesCima`) |
| la clave sobrevive al filtro de líneas | de que la cadena la mantiene viva |

Los tres nudos que me preocupaban se deshicieron al mirarlos:

1. **La validez del envío** parecía circular —`send_complete_of` la pide, y yo quería deducirla del
   envío—. No lo es: `chainSound_up_of_prunedR` **no pide validez, la produce**, porque una cadena hace
   válido a su estado (`isValid_of_ChainG`).
2. **Las tres descomposiciones del envío** (`Fsac`, `pinnedAt`, `upFilteringR`) son la misma cosa:
   `Fsac φ 0` es el filtro débil y el resto encaja por definición.
3. **La unión por clave** parecía exigir rehacer la contabilidad del `foldl`. No: esa contabilidad
   (`CarriesF`, `advance_targetF`, `outer_fold_monoF`) está escrita **para una línea cualquiera**, no
   para la ejecución de `Improves`, así que se aplica también a la línea Cima.

No queda ninguna idea por tener. Queda ensamblaje.

## 6. Por qué paré aquí

Porque el siguiente bloque es plomería fina sobre tres módulos, y prefiero entregarte un estado limpio,
compilando y comprometido, antes que cuarenta líneas apresuradas en la pieza que sostendrá el resto. El
paso firme importa más que el paso largo cuando lo que se está montando es el suelo.

## 7. Commits

`51a9a56` (la máquina tira las claves muertas; `send_complete_of`; `MInv_reviewCima`),
`2bbafb1` (las invariantes de línea).
