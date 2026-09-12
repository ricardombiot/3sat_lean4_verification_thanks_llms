# Verificación para el Autor v79: `join` cerrado — y P3, dicha por fin con precisión

Ricardo, soy Claude (Opus 5). Cerrado el caso que v78 encontró que faltaba, y de paso he ido a leer la letra pequeña de lo que v65 dejó hecho. Esa letra pequeña cambia lo que hay que demostrar en P3 — para mejor, porque ahora se sabe exactamente qué es.

---

## 1. `join`, cerrado en un lema

No hizo falta pelearlo. La razón es bonita y conviene decirla, porque explica por qué el tejido es el objeto correcto:

> **Un tejido solo pide que las cosas *estén*.** Todas sus cláusulas son una pertenencia o una existencia — una entrada en cada paso, un portador entre los padres, un owner en una tabla. Ninguna dice «y nada más». Así que **ningún crecimiento puede romperlo**.

`Join.lean` ya tenía la abstracción exacta para eso, `Grown`, así que el lema es uno solo y sirve para todo:

```lean
theorem Fabric_of_grown {g g' : GPathM} (hgr : Grown g g') (S T) (h : Fabric g S T) :
    Fabric g' S T                                          -- [propext, Quot.sound]
```

y de ahí `Fabric_join_left` y `Fabric_join_right`, con `okJoin` para el lado derecho. El libro mayor de v78 queda así:

| caso de la inducción | estado |
|---|---|
| semilla | ✅ v78 |
| `addNode` | ✅ v78 |
| **`join`** | ✅ **hoy** |
| review y filtros de literal | ✅ v65 |

## 2. La letra pequeña de v65, y qué es P3 de verdad

Fui a leer `FOk_filterAll`, que es el lema de v65 para los filtros. Lleva una hipótesis que yo no había mirado:

```lean
(hpin : ∀ r ∈ reqs, ∀ p, S p → p.id.step = r.step → p.id = r)
```

Es decir: **el filtro conserva el tejido solo si los miembros del tejido ya concuerdan con todos los pines.** Y eso, en el paso de cláusula, **falla de entrada**: el tejido que `addNode` fabrica contiene *todos* los owners globales, así que en un paso pinzado contiene los dos valores, y la hipótesis se cae al primer requisito.

Así que P3 no es lo que yo venía diciendo. No es «el filtro de cláusula preserva el tejido». Es:

> **P3, dicho bien.** Al pinzar una cláusula hay que **estrechar** el tejido a los miembros que concuerdan con los tres requisitos, y la obligación es que el estrechado **siga teniendo una entrada en cada paso**.

Que es, literalmente, el `CoreCovers` de v44 — el mismo enunciado que aquel informe aisló cuando redujo `Closed` a una sola frase. Han hecho falta treinta y cinco informes para volver al mismo sitio por otro camino, y eso me parece buena señal y no mala: dos rutas independientes desembocan en la misma obligación.

Y es **exactamente lo que medí en v77**: el mayor tejido dentro de `owners(n)` en los pasos de cláusula, y si cubre todos los pasos. 124.246 nodos, cero fallos, controles Tseitin incluidos. La medición estaba bien apuntada aunque yo describiera mal la diana.

## 3. Dónde queda la ruta

| pieza | estado |
|---|---|
| **P1** el tejido nace (semilla, `addNode`) | ✅ v78 |
| **P2** lo preservan las operaciones | ✅ v65 + **`join` hoy** |
| **P3** el estrechado a los pines sigue cubriendo | **abierta — y ahora bien enunciada**; medida en v77 |
| **P4** el puente `FabricAt ⟹ PickSome` | abierta, con su desajuste declarado |
| **P5** cierre con `L7.satisfiable_of_inhabited` | libre si caen las anteriores |

Siguiente: **P3**, que ya no es una intuición sino un enunciado — *el tejido estrechado a los pines de una cláusula conserva una entrada en cada paso* — con su medición hecha y su antecedente (`CoreCovers`) documentado desde v44. Y la expectativa honesta sigue siendo la de v76: **ahí es donde la hipótesis de clase tendrá que entrar**, porque si P3 valiera para toda fórmula tendríamos 3SAT en P.

Build: `lake build AbsSat` verde, 100 módulos, 0 `sorry`, 0 axiomas de proyecto; los siete teoremas de `FabricAdd.lean` cierran en `[propext, Quot.sound]`.
