# Verificación para el Autor v92: las hipótesis enhebradas por el conductor — y `NodesAreGowners` deja de ser medida

Ricardo, soy Claude (Opus 5). Enhebradas. Y por el camino cayó algo que el proyecto llevaba desde
el principio marcado como *medido pero no demostrado*.

---

## 1. El paquete

```lean
structure Woven (g : GPathM) : Prop where
  oos, sym, pn, pbelow, notroot, sn, sabove, pms, gn, below, mok
```

Once campos: los nueve que pide `TableCtx_reviewSymTri`, más `Below` (*cada nodo está en un paso
que el estado tiene*) y `MachineOk` (la forma de `current_step`/`map_parent`), que son lo que
`addNode` necesita. Y con él:

```lean
theorem Woven_initSeed         (d) (title) (hstep : d.step = 0) : Woven (initSeed d title)
theorem Woven_upFilteringSymTri (g) (reqs) (d) (title) (hv) (hd) : Woven g →
    Woven (upFilteringSymTri g reqs d title)
theorem TableCtx_of_Woven      (g) (hv) : Woven g → TableCtx (reviewSymTri g)
```

**La semilla y el paso.** Cada estado que tu conductor construye satisface `TableCtx`, y por tanto
—con `Fabric_whole`— **es un tejido entero**.

## 2. Y esto es lo que me gustó encontrar

Había un problema aparente: **`filterRequire` encoge `gowners`**, así que no puede conservar
`NodesAreGowners` (*todo nodo es owner global*). Un nodo cuyo id deja de ser owner global rompe la
propiedad en el acto. Por eso `Ownership.lean` la deja definida y `Reader.lean` la arrastra como
hipótesis, y `Sons.lean` anota: *«la campaña la respalda —0 violaciones sobre 259.187 nodos— pero no
está demostrada»*.

No hace falta conservarla, porque **el review la devuelve**:

```lean
theorem NG_reviewSymTri (g) (hv : isValid (reviewSymTri g) = true) (hoos) (hbel) :
    Ownership.NodesAreGowners (reviewSymTri g)          -- [propext, Quot.sound]
```

Y sale de dos cosas que ya estaban demostradas aquí: **un nodo se posee a sí mismo**
(`selfOwn_reviewSymTri`, v90) y **los owners de un superviviente son owners globales**
(`OwnersGlobal_reviewSymTri`, v90). Juntas: el nodo está en su propia tabla, luego está en los
owners globales. Tres líneas, después de dos informes de preparación.

> **`NodesAreGowners` pasa de medida a teorema**, sobre la máquina unida.

Eso es lo que permite cerrar el paso hacia arriba: `OwnSymmetric_addNode` la pedía, y ahora se le
da demostrada.

## 3. El `join`: diez de once

El conductor también funde dos estados que llegan al mismo nodo del mapa (`insertPure` → `doJoin`).
De los once campos, **diez** tienen su teorema de `join` (nueve ya existían; `MachineOk_join` y
`Below_join` se añaden hoy).

El que falta es **la simetría**, y la razón es precisa, no técnica:

> `q ∈ owners₁(p)` da `p ∈ owners₁(q)` **sólo si `q` es un nodo de `g₁`**. Y la fusión puede tener
> un `q` que es nodo de un lado y mera entrada de tabla del otro.

Lo que lo cierra es `OwnersGlobal` y `GN` en los dos lados —todo owner en rango es owner global, y
todo owner global es nodo—, que es justo lo que §2 acaba de poner en circulación. Es la pieza
siguiente, no una escondida; la digo con nombre para que no se pierda.

## 4. Estado

| pieza | estado |
|---|---|
| **P1** el tejido nace | ✅ v78 |
| **P2** lo preservan las operaciones y el `join` | ✅ v65 + v79 |
| **P3** el pinzado cubre y no se estrecha | ✅ cerrada (v83–v86) |
| **P4** el puente a `PickSome` | 7 cláusulas (v87), `up`/`down` de tabla (v88), la máquina unida (v89), `TableCtx` completa (v90–v91), **enhebrada por la semilla y el paso del conductor (hoy)**; falta la simetría en el `join`, y el testigo **relativo** |
| **P5** cierre con `L7` | libre |

Sin cambios en el aviso de siempre: el residuo real de P4 sigue siendo el testigo **relativo**
—`up`/`down` valen en las tablas y fallan sólo dentro de `owners(q)`, el 0,015% de los pares—, y el
muro de v70 donde estaba.

Build: `lake build AbsSat` verde, 101 módulos, 0 `sorry`, 0 axiomas de proyecto; **134 teoremas** en
`SymTriReview.lean`, todos en `[propext, Quot.sound]`. `--joined` sigue en 0 perdidas, 0 zombis,
0 violaciones de simetría.
