# Verificación para el Autor v91: los siete campos estructurales — y el estado válido **es** un tejido, sobre una máquina concreta

Ricardo, soy Claude (Opus 5). Hechos los siete. `TableCtx` está **completa** sobre la máquina
unida, y con ella `Fabric_whole` deja de hablar de una hipótesis y habla de tu máquina.

---

## 1. Los siete ya existían con otro nombre

Ninguno de los siete era nuevo: el proyecto ya tenía cada uno como propiedad con nombre.

| campo | propiedad del proyecto |
|---|---|
| `level` — un padre está un paso por debajo | `Parents.PBelow` |
| `parnode` — y es un nodo | `Parents.PN` |
| `hasparent` — un nodo por encima del paso 0 tiene alguno | `Parents.NotRoot` + `isValidNode` |
| `sonlevel` — un hijo está un paso por encima | `Sons.SAbove` |
| `sonnode` — y es un nodo | `Sons.SN` |
| `hasson` — un nodo que no está arriba del todo tiene alguno | `isValidNode` |
| `smp` — la tabla de padres del hijo devuelve el enlace | `Sons.PMS` |

Dos salen **gratis** de `pruned_reviewSymTri` (`PBelow`, `NotRoot`). Dos salen de `isValidNode`,
que la máquina unida ya garantiza por nodo (v90). Y cuatro necesitaban su cadena llevada por el
review simétrico.

## 2. Y las cuatro cadenas se colapsaron en una

Aquí está lo que hizo el trabajo corto, y me gustó verlo:

> **El paso espejo es un reetiquetado de la lista de nodos que conserva ids, padres e hijos — y la
> barrida del triángulo es exactamente lo mismo.**

Así que en vez de cuatro cadenas de ocho lemas cada una, hay **un solo combinador**:

```lean
structure LinkStable (P : GPathM → Prop) : Prop where
  map : ∀ g F, (ids fijos) → (padres fijos) → (hijos fijos) → P g → P (g con nodos reetiquetados)
  upd : ∀ g id b, P g → P (intersección de owners)
  unl : ∀ g id, P g → P (desenlace)
  rem : ∀ g id, P g → P (borrado de nodo)

theorem LinkStable.reviewSymTri' (hs : LinkStable P) (g) (h : P g) : P (reviewSymTri g)
```

Y cada propiedad cuesta **cuatro lemas cortos**, tres de los cuales ya existían. Instanciado cinco
veces: `PN`, `SN`, `PMS`, `SAbove` y `GN` (los owners globales son nodos, v25).

## 3. El resultado

```lean
theorem TableCtx_reviewSymTri (g) (hv : isValid (reviewSymTri g) = true)
    (hoos) (hsym) (hpn) (hpb) (hnr) (hsn) (hsa) (hpms) :
    FabricAdd.TableCtx (reviewSymTri g)                 -- [propext, Quot.sound]
```

**Los once campos.** Y con él:

```lean
theorem Fabric_whole_reviewSymTri (g) (hv) … :
    Fabric (reviewSymTri g) (los nodos en rango) (sus propios owners)
```

> **En un punto fijo válido del review simétrico con el triángulo, el estado *es* un tejido — las
> nueve cláusulas.** Sobre una máquina concreta, no bajo una hipótesis.

Esto es lo que v88 enunció y v89–v91 han ido pagando. Explica lo que veníamos midiendo desde v65
sin entender del todo: el tejido dentro de `owners(r)` era **todo** `owners(r)` porque el estado
entero ya lo es.

## 4. Lo que queda, dicho con precisión

* **Las hipótesis de entrada** (`OOS`, simetría, `PN`, `PBelow`, `NotRoot`, `SN`, `SAbove`, `PMS`,
  `GN`) son sobre el estado **de partida**, y todas tienen ya sus teoremas de `initSeed`, `addNode`,
  `up` y `join` en el proyecto para las operaciones compartidas. Enhebrarlas por el conductor de la
  máquina unida es contabilidad, no hay nada abierto dentro.
* **`hrootstep`** —*un id que lleva padre está en paso ≥ 1*— sigue siendo hipótesis explícita. No es
  una propiedad del grafo sino de **la codificación de los ids**, y la cumple la construcción; es
  pequeña y va aparte.
* **El residuo de P4 no cambia**: `up`/`down` valen a nivel de tablas (v88, demostrado) y fallan
  sólo **relativos al pinchazo** — el testigo existe pero fuera de `owners(q)`, el 0,015% de los
  pares. Ése es el único sitio donde sigue habiendo algo.

## 5. Estado

| pieza | estado |
|---|---|
| **P1** el tejido nace | ✅ v78 |
| **P2** lo preservan las operaciones y el `join` | ✅ v65 + v79 |
| **P3** el pinzado cubre y no se estrecha | ✅ cerrada (v83–v86) |
| **P4** el puente a `PickSome` | 7 cláusulas (v87), `up`/`down` de tabla (v88), la máquina unida (v89), `TableCtx` **completa** y `Fabric_whole` sobre ella (v90 + hoy); residuo: el testigo **relativo** |
| **P5** cierre con `L7` | libre |

Build: `lake build AbsSat` verde, 101 módulos, 0 `sorry`, 0 axiomas de proyecto; **114 teoremas** en
`SymTriReview.lean`, todos en `[propext, Quot.sound]`. La campaña `--joined` sigue en 0 perdidas,
0 zombis, 0 violaciones de simetría.
