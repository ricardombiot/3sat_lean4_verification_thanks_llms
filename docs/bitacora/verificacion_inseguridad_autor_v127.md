# Verificación para el Autor v127: el veredicto, reducido a una propiedad global de la construcción

Ricardo, soy Claude (Opus 5). En v126 demostré que toda rama de la máquina vive, línea a línea, dentro de
la máquina completa. Este tramo demuestra que la rama **es compatible con sus fijaciones**, y con eso
cierra la cadena del lector desde el lado global: la validez del veredicto de *Improves* queda reducida a
**una única propiedad de la construcción**, la ausencia de préstamos entre ramas.

Todo en la rama `spaik`, en el build de `AbsSat` (248 jobs con la sonda), sin `sorry`, en
`[propext, Quot.sound]`.

---

## 1. El invariante de compatibilidad (`BranchCompat.lean`)

**`branchRun_compat`**: en todo estado de la rama de `P`, cada nodo situado en el paso de una fijación
`r ∈ P` lleva el identificador `r`.

La prueba sigue la construcción paso a paso:

- **un envío a `d`** añade exactamente un nodo nuevo, con identificador `d`, en el paso siguiente, y
  conserva nodos del estado que envía, que están por debajo (`keyShape_sent`);
- **las uniones** solo juntan nodos (`keyShape_doJoin`);
- así, antes de restringir la línea, cada entrada de clave `d` tiene la **forma de su clave**
  (`KeyShape`): sus nodos del paso de `d` llevan `d`, y en los pasos de las demás fijaciones ya son
  compatibles (`advance_keyShape`; la semilla, `init_keyShape`);
- **la restricción de la línea** solo deja las claves que coinciden con la fijación de ese paso, y eso
  convierte la forma de la clave en compatibilidad (`compat_restrict`).

## 2. La rama atraviesa las fijaciones del lector

- **`embedded_pin`**: un estado válido de tipo lector, compatible con las fijaciones y dentro de `G`,
  sigue dentro de `G` fijado (y con enlaces).
- **`inside_pinOneByOne`**: lo mismo a lo largo de una secuencia de fijaciones aplicadas una a una,
  como hace el lector, y el estado fijado queda válido.
- **`reader_pins_valid_of_branch`**: si un estado final de la rama de `P` es válido tras un review
  agresivo, el estado final de la **máquina completa** con la misma clave **sigue válido bajo cualquier
  secuencia de fijaciones tomadas de `P`**.

## 3. El veredicto desde lo global (`BranchReader.lean`)

- **`BranchValid φ P K`**: la rama de `P` llega válida al nodo del mapa `K`.
- **`NoBorrow φ K`** (sin préstamos): si la rama de `P` llega válida a `K` y el estado del lector tras
  fijar `P` todavía tiene elección, hay una elección `q`, en un paso con elección, cuya rama `P + q`
  también llega válida a `K`. Con tus palabras: todo nodo que el lector aún puede elegir pertenece a un
  camino construido paso a paso que sobrevive por sí mismo, no solo porque un `join` con otra rama lo
  sostenga.
- **`sat_of_noBorrow`** (**demostrado**): **con `NoBorrow`, un estado final válido de la máquina
  *Improves* da un modelo de φ.** El lector fija, una a una, las elecciones que da `NoBorrow`; cada
  fijación es válida porque su rama lo es (sección 2); la medida baja en cada fijación; cuando no queda
  elección, el estado denota un camino, que se decodifica en un modelo.

## 4. La cadena completa

```
initSeed, UP, filtros, review agresivo, join     conservan MInv (+ own)          demostrado
rama de P  (branchRun φ P)                       MInv en todos sus estados        demostrado (v126)
  dentro de la máquina completa, clave a clave   branchRun_embedded               demostrado (v126)
  compatible con sus fijaciones                  branchRun_compat                 demostrado (v127)
  ⇒ fijar P en el estado final es válido         reader_pins_valid_of_branch      demostrado (v127)
sin préstamos: en cada estado del lector, alguna elección tiene rama válida
                                                 NoBorrow                         abierto
  ⇒ el lector acaba en un camino ⇒ modelo de φ   sat_of_noBorrow                  demostrado (v127)
```

Todo el trabajo local de v117–v123 (soportes, `SPC`, cadenas por pares) queda como herramienta: la
supervivencia de la rama dentro de la construcción completa usa `AnchoredSurvive` y la adyacencia exacta.
Pero la obligación abierta ya no es local: es una propiedad de cómo la máquina construye y une ramas.

## 5. Lo que queda

1. **Medir `NoBorrow` a profundidad mayor.** v124 lo respalda en profundidad 1 (1.725 fijaciones, todas
   las ramas válidas). Falta recorrer el árbol de fijaciones del lector y comprobar, en cada estado con
   elección, que alguna elección tiene rama válida (y cuántas no la tienen).
2. **Demostrar `NoBorrow`.** La forma natural es por inducción sobre la construcción: una rama válida en
   la línea `k + 1` viene de envíos válidos desde la línea `k`, y un `join` de estados válidos de la misma
   clave es válido. Lo que hay que ver es que la validez de una rama restringida no depende de lo que
   aportan las ramas descartadas; la conmutación exacta medida en v124 indica que así es.
