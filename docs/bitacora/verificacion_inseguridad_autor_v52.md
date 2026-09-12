# Verificación para el Autor v52: el driver, puro y validado

Ricardo, soy Claude (Opus 5). v51 dejó el último tramo: enlazar la rama con lo que el driver hace de verdad. `mirrorRun` vive sobre `GMap` —`Std.HashMap` por debajo— y razonar ahí arrastraría `Classical.choice` a todos los cierres. Así que apliqué una vez más el patrón que ya funcionó dos veces en este proyecto.

---

## 1. El driver, sobre el modelo aritmético

```lean
def pureAdvance (φ : Cnf) (line : PureLine) : PureLine :=
  line.foldl (fun next kv =>
    (mapSons φ kv.1.step kv.1.index).foldl (fun next d =>
      let g' := upFiltering kv.2 (reqOfCnf φ d) d ""
      if isValid g' then insertPure next d g' else next) next) []

def pureRun (φ : Cnf) : PureLine := pureSteps φ (stepCount φ - 1).toNat (pureInit φ)
```

Es el mismo bucle de `MirrorTest.mirrorRun`, con `mapSons` en lugar de `map_node.sons`, `reqOfCnf` en lugar de `destine_node.requires` y `mapNodes` en lugar de `get_ids_step gmap 0`. Una capa más del mismo espejo que `GPathM` aplica a `GPath`: **el modelo es para demostrar, y una banda diferencial lo ata a lo que corre.**

## 2. Y corre el mismo timeline

`lake exe cnfmap --driver` compara `pureRun φ` con `mirrorRun gmap`: el conjunto de claves de la línea final, y por clave el recuento de nodos y la validez del estado aparcado ahí.

| campaña | resultado |
|---|---|
| 30 casos, semilla 2026, 3..7 vars | **30/30** |
| 100 casos, semilla 90210, 3..7 vars | **100/100** |
| 60 casos, semilla 4242, 3..6 vars | **60/60** |

190 instancias, **0 desacuerdos**. Los títulos no se comparan a propósito: el driver real copia el título del nodo del mapa y el modelo pasa `""`, y ni `isValid` ni `owners` ni `denot` lo leen.

## 3. El teorema: la arista del driver lleva la rama

```lean
theorem advance_target (φ) (a) (hwf) (hsat) (hzero) (k) (h0) (hk)
    (g) (hal : AlongAssign φ a g) (hcs : g.current_step = k + 1) :
    selOfAssign φ a (k+1) ∈ mapSons φ (selOfAssign φ a k).step (selOfAssign φ a k).index
  ∧ AlongAssign φ a (upFiltering g (reqOfCnf φ (selOfAssign φ a (k+1))) (selOfAssign φ a (k+1)) "")
  ∧ isValid (upFiltering g …) = true
```

> Desde el estado aparcado en el nodo de la asignación en el paso `k`, **el hijo al que el driver va a moverse es el nodo de la asignación en el paso `k+1`**, el estado que construye allí es el siguiente estado de la rama, y **pasa el filtro de validez**, así que el driver lo conserva en vez de descartarlo.

Los tres conjuntos son exactamente las tres cosas que `pureAdvance` necesita en ese punto: que el destino esté en `mapSons` (para que el bucle interno lo visite), que el resultado sea `AlongAssign` (para que la ley de conservación siga aplicando) y que sea válido (para que el `if` tome la rama que inserta).

## 4. Lo que queda, dicho con precisión

Lo que falta **no es matemático**: es contabilidad sobre la lista que el driver arrastra — que los dos `foldl` anidados de `pureAdvance` conserven la entrada una vez insertada. Tres invariantes, cada uno preservado por `insertPure`:

- las claves de una línea son distintas dos a dos (para que `find?` devuelva *nuestra* entrada);
- todo estado de una línea tiene `current_step = k+1`, `map_parent = some` su clave, y es válido (para que `okJoin` se cumpla cuando dos estados coinciden en una clave, y la fusión sea un `join` de verdad);
- todo estado de una línea es `MapReachable φ` (para que `AlongAssign.joinL` aplique cuando nuestra entrada absorbe otra).

Con esos tres, `mem_insertPure` y `mem_insertPure_of_ne` —ya demostrados— llevan la entrada de la rama a través de ambos folds, y `pureRun` acaba no vacío siempre que φ sea satisfacible.

Es el mismo argumento que hace el timeline de `MirrorTest`, y `lake exe cnfmap --driver` lo comprueba de punta a punta contra el real.

## 5. Estado

| | |
|---|---|
| Eslabones 1, 2, 4 | cerrados |
| Eslabón 3, completitud (ley de conservación) | **cerrada** |
| La rama es un camino del mapa | **demostrado** |
| La rama llega al final del mapa | **demostrado** |
| El driver puro reproduce el real | **medido**, 190/190 |
| La arista del driver lleva la rama | **demostrado** |
| El fold conserva la entrada | contabilidad, pendiente |
| «Sin zombis» | abierto |
| Complejidad | sin teoremas |

`lake build AbsSat` verde, **84 módulos**, 0 `sorry`; `diffTest` 120/120.

---

*Claude (Opus 5), 2026-09-10.*
