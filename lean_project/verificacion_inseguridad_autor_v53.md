# Verificación para el Autor v53: el driver conserva la rama — teorema

Ricardo, soy Claude (Opus 5). v52 dejó el driver puro validado contra el real y `advance_target` demostrado, y dijo que lo que faltaba «no es matemático, es contabilidad sobre la lista». Ya está hecha. **El teorema del driver está cerrado.**

---

## 1. El enunciado

```lean
theorem pureRun_full_state (φ : Cnf) (a : Assign) (hwf : WF φ) (hsat : Sat a φ)
    (hzero : (0 : Int) < stepCount φ) :
    ∃ g, (selOfAssign φ a (stepCount φ - 1), g) ∈ pureRun φ
      ∧ g.current_step = stepCount φ
      ∧ isValid g = true
      ∧ Inhabited g
```

> Para **toda** asignación que satisface φ, la última línea del driver tiene una entrada **en el nodo que esa asignación nombra**, y el estado aparcado ahí **abarca el mapa entero, es válido y denota algo**.

Y su corolario inmediato:

```lean
theorem pureRun_ne_nil (φ) (hwf) (hzero) (h : Satisfiable φ) : pureRun φ ≠ []
```

Cierre `[propext, Quot.sound]` en los dos. Cero axiomas de proyecto, cero `sorry`, sin `native_decide`.

Fíjate en el cuantificador: no es *hay una asignación cuyo camino sobrevive*, es **para toda**. Cada solución de φ tiene su propia entrada en la línea final. Eso es exactamente lo que me dijiste que hacía tu conjunto válido —contener de forma abstracta no una solución sino todas— y ahora es un teorema sobre el bucle que corre.

## 2. Cómo se demuestra: dos mitades, y ninguna busca nada

**La mitad matemática ya estaba** (v52, `advance_target`): desde el estado de la rama en el paso `k`, la arista que el driver va a tomar lleva al nodo de la asignación en `k+1`, el estado que construye allí sigue siendo de la rama, y **pasa el filtro de validez**. La ley de conservación de v50 hace todo el trabajo: el testigo viene de la asignación, la máquina solo tiene que no destruirlo.

**La mitad nueva es contabilidad**, y son los tres invariantes que v52 nombró, ahora demostrados:

```lean
structure StateOk (φ : Cnf) (k : Int) (kv : NodeId × GPathM) : Prop where
  onMap : kv.1 ∈ mapNodes φ k          -- la clave es un nodo del mapa en ese paso
  reach : MapReachable φ kv.2          -- para que los `join` de AlongAssign apliquen
  step  : kv.2.current_step = k + 1    -- ┐
  par   : kv.2.map_parent = some kv.1  -- ├ exactamente lo que pide `okJoin`
  valid : isValid kv.2 = true          -- ┘

def LineOk (φ) (k) (line) : Prop := (line.map (·.1)).Nodup ∧ ∀ kv ∈ line, StateOk φ k kv

def Carries (φ) (a) (k) (line) : Prop :=
  ∃ g, (selOfAssign φ a k, g) ∈ line ∧ AlongAssign φ a g ∧ g.current_step = k + 1
```

El lema que lo sostiene todo es **`Carries_insertPure`**: una inserción en otra clave deja la entrada de la rama intacta; una inserción **sobre** ella la fusiona con `join`, y `AlongAssign.joinL` cubre justo ese caso. Es decir: **ninguna de las dos cosas que el driver sabe hacer con una entrada puede perderla.** Insertar en otro sitio no la toca; fusionar sobre ella solo la hace crecer.

Con eso, la cadena de arriba abajo:

| lema | qué dice |
|---|---|
| `StateOk_sent` | lo que el driver conserva tras enviar cumple el invariante en el paso siguiente — la pieza nueva es `mapSons_subset`: un hijo de un nodo del mapa es un nodo del mapa un paso arriba |
| `LineOk_sendTo` / `LineOk_sendAll` / `LineOk_pureAdvance` | el invariante de línea sobrevive los dos `foldl` anidados |
| `sons_fold_establish` | el fold interno **crea** la entrada de la rama cuando llega al hijo correcto |
| `outer_fold_mono` | el fold externo, una vez creada, no la pierde |
| `Carries_pureAdvance` | **un paso del driver conserva la rama** |
| `init_ok` | la primera línea es una línea, y ya lleva la rama (`AlongAssign.seed`) |
| `run_ok` | inducción sobre el número de pasos |

Una trampa que hubo que sortear: `isValid_initSeed` salía con `Classical.choice` por un `simp` demasiado ancho. Reescrito vía `isValid_of_gowner` vuelve a `[propext, Quot.sound]`. Es el mismo cuidado de siempre — un `simp` cómodo puede contaminar un cierre sin avisar.

## 3. Las bandas, después del cambio

`pureAdvance` se refactorizó en pasos con nombre (`sendTo` / `sendAll`) para poder razonar sobre cada fold por separado. Es un cambio que preserva la semántica, y la banda lo confirma:

| campaña | resultado |
|---|---|
| `cnfmap --driver` 30, semilla 2026 | **30/30** |
| `cnfmap --driver` 100, semilla 31337 | **100/100** |
| `cnfmap` (mapa aritmético vs. mapa construido) 200, semilla 7 | **200/200** |
| `diffTest` 300, semilla 2026 | **300/300** (264 SAT, 36 UNSAT) |

0 desacuerdos, 0 saltos por mal formadas.

## 4. Qué **no** dice, dicho claro

- **No dice que el recorrido sea corto.** `pureAdvance` es un fold sobre toda la línea, y la línea puede ser tan ancha como `mapNodes` en ese paso. **Complejidad sigue sin un solo teorema.**
- **No dice la recíproca.** Que la última línea no esté vacía no implica todavía `Satisfiable φ`: esa dirección pasa por `Inhabited` de un estado **cualquiera** del recorrido, y eso es el problema abierto («sin zombis», `Supported`), no algo que el driver resuelva.
- **El driver real sigue atado por medición, no por demostración.** `mirrorRun` vive sobre `GMap`/`HashMap`; el puente son las 130 instancias de `--driver` de arriba más las 190 de v52.

## 5. Estado

| | |
|---|---|
| Eslabones 1, 2, 4 | cerrados |
| Eslabón 3, completitud (ley de conservación) | cerrada |
| La rama es un camino del mapa | demostrado |
| La rama llega al final del mapa | demostrado |
| La arista del driver lleva la rama | demostrado |
| **El bucle completo del driver conserva la rama** | **demostrado** |
| El driver puro reproduce el real | medido, 320/320 |
| «Sin zombis» (eslabón 3, soundness) | abierto |
| Complejidad | sin teoremas |

`lake build AbsSat` verde, **84 módulos**, 0 `sorry`, 0 axiomas de proyecto.

Lo que queda del muro es **uno solo** de los cinco eslabones, y por un solo lado: leer una solución de un estado válido **arbitrario**. La mitad de completitud —que si hay solución la máquina la conserva— está cerrada de punta a punta, desde la fórmula hasta el bucle.

---

*Claude (Opus 5), 2026-09-11.*
