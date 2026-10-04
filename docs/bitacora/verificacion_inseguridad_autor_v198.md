# Verificación para el Autor v198: se retiran las reglas de la fila de claves; se vuelve a la máquina de siempre

Ricardo, este informe es corto: deja constancia de la marcha atrás que decidiste y de dónde queda cada cosa. Lo
aprendido con las reglas está en los informes v196 y v197, y el código sigue recuperable en la historia de git.

**La conclusión, por adelantado.**
* **Se retiran** la etiqueta de clave de un nivel, la comprobación de claves y las etiquetas de todos los niveles.
  El Julia de `src/` vuelve a ser exactamente el de antes de las reglas, y `KeyRules.lean` sale del proyecto Lean.
* **Nada se pierde:** la rama `julia_key_rules` se fusionó en `lean_improves_bin` antes de revertir (merge `e0be7a3`),
  así que todos sus commits están en la historia.
* **Se mantiene** todo lo que habla de la máquina actual: `M1Parts.lean`, `M1bOwn.lean` y el trabajo de la otra
  sesión (`KeyExact`, `KeySplit`, …).
* **Siguiente:** verificar la máquina sin cambiarla. Empiezo por la inducción de `KFix` (§4).

---

## 1. Por qué se retiran

* **Las reglas de un nivel** (v196) dan M1 en el join donde actúan (`m1_keyRules`, demostrado), pero **no cierran la
  inducción del lector**: la inducción baja a las fuentes de las piezas, que también son estados unidos, y ahí las
  etiquetas de un nivel ya no están (v197 §4). La comprobación de claves, además, no quitó ninguna clave en las 76
  instancias medidas.
* **Las etiquetas de todos los niveles** (v197 §5) son correctas en todo lo medido: etiquetas exactas en 1,1 M + 696 k
  casos, mismos veredictos y soluciones, y M1b-entradas por construcción. Pero **no son sostenibles**:
  * la mezcla es casi total, hasta 89 filas mezcladas de 105;
  * con la representación actual llegan a 88,7 GB en `clause_mix_sep` y son ×12,8 más lentas (v197 §8).

  Una representación compacta (2 bits por fila dentro de la tabla de owners) bajaría la constante unas 500 veces,
  pero seguiría siendo un factor S en memoria y un cambio de la máquina. Decidiste no seguir por ahí y buscar otras
  vías para verificar la máquina tal como es.

## 2. Qué se hizo

En `lean_improves_bin`:
1. **Merge `e0be7a3`** (`--no-ff`, sin reescribir historia) de `julia_key_rules`. Trae los siete commits de la rama:
   * `aeeb001`, `cac23ff` y `98923f0`: las reglas de un nivel;
   * `a7b3dd7`: las quita;
   * `f218230`, `47d00be` y `cfc92c9`: las etiquetas de todos los niveles y su desactivación.
2. **Reversión `92b4b61`:**
   * `graph_path.jl`, `graph_path_constructor.jl`, `graph_path_filter.jl`, `graph_path_join.jl` y `graph_path_up.jl`
     vuelven a su versión de `f439a9c`, anterior a las reglas. Comprobado: `src/` no tiene ninguna diferencia con
     aquel punto.
   * Se borran `graph_path_keytags.jl`, `test_3sat/compare_keytags.jl` y `test_3sat/probes/keytags_all_probe.jl`, que
     dependían de la regla.
   * Se borra `lean/improves_bin/AbsSatBin/GraphPath/Model/KeyRules.lean`. Ningún otro módulo lo importaba; el
     proyecto sigue compilando.
   * `docs/context/escalera_reader.md` marca `KeyRules` como retirado, con los commits donde está.
3. **Se borraron la rama `julia_key_rules` y su worktree.** Sus commits siguen accesibles a través del merge.

**Qué no se tocó:** `keysplit_probe.jl` y el resto del trabajo de la otra sesión; los informes v196 y v197; y los
módulos Lean sobre la máquina actual.

## 3. Cómo recuperar algo si hace falta

| qué | dónde |
|---|---|
| etiquetas de todos los niveles (Julia) | commit `cfc92c9` (`graph_path_keytags.jl` y sus enganches) |
| reglas de un nivel (Julia) | commit `98923f0` (`graph_path_key.jl`) |
| reglas formalizadas (Lean) | commit `82c121f` (`KeyRules.lean`: `m1_keyRules`, `below_reviewKC`, `isValid_filterKC_of_kernel`) |
| diseño, resultados y alcance | informes v196 y v197 |

Por ejemplo, `git show cfc92c9:julia/improves_bin/src/graph_path/graph_path_keytags.jl`.

## 4. Lo que sigue: la máquina de siempre

El lector decide `φ` bajo M1 en cada join, y M1 se parte en dos:
* **`M1aAll`**: fijar una clave viva no invalida. La lleva la otra sesión, por `KeyTri₁` ⇐ `KeyExact` / `KeySplit`.
* **`M1bLowOwn`**: con la clave fijada, las tablas de abajo son de la pieza. Demostrado: `M1bLowOwn ⇐ KFix`
  (`M1bOwn.lean`).

**`KFix`** dice que todo conjunto de enlaces del estado unido fijado que sea cerrado para la clave k (cada enlace tiene,
en cada paso, un testigo que posee un nodo de k y está enlazado con los dos extremos dentro del conjunto) está
dentro de la pieza k. Está medido sin fallos en 24,7 M enlaces. La traza del v196 dice que los enlaces que no son de la
pieza caen siempre en la ronda 2 de la regla de parejas. Es la vía sin cambios de máquina con la que sigo: primero los
hechos estructurales de un conjunto cerrado, y después la inducción sobre las líneas.

---

**Commits:** `e0be7a3` (merge) y `92b4b61` (reversión), en `lean_improves_bin`.
