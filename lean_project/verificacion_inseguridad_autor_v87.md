# Verificación para el Autor v87: P4, cláusula por cláusula — el residuo tiene nombre

Ricardo, soy Claude (Opus 5). Seguí con P4. v82 la había dejado en el peor sitio posible: **una
reformulación**, `PinNonEmpty` equivalente a la validez misma, sin contenido. Hoy baja un nivel y
sale con algo concreto: **de las nueve cláusulas del tejido, siete están demostradas y el residuo
son exactamente dos, `up` y `down`.**

---

## 1. La idea

`PinNonEmpty g q` pide **algún** tejido no vacío dentro del pinchazo. Hay un candidato obvio y es
**el tuyo**: `owners(q)`, la tabla del nodo que el lector va a pinchar. La pregunta deja de ser
existencial y se vuelve concreta: *¿qué cláusulas del tejido cumple esa tabla?*

## 2. Medido primero, modo nuevo `--p4clause`

Para cada estado válido con elección, cada paso con elección y cada owner `q` de ese paso, tomo el
candidato `owners(q)` y compruebo las nueve cláusulas **antes de estrechar nada** (`inS` y `sub`
valen por construcción; las otras siete se miden). Semilla 31337, 20 casos, 4..7 variables —
**1.835 estados válidos con elección, 38.398 pinchazos**:

| cláusula | original | simétrica (v64) | **triángulo (v69)** | sim+tri |
|---|---|---|---|---|
| `gow` los miembros son owners globales | 0 | 0 | **0** | 0 |
| `self` cada miembro se conserva | 0 | 0 | **0** | 0 |
| `symm` tablas simétricas | 236 | 0 | **0** | 0 |
| `support` una entrada en cada paso | 144 | 82 | **0** | 0 |
| `up` toda entrada la lleva un **padre** de la tabla | 938 | 876 | **791** | 791 |
| `down` … un **hijo** | 870 | 806 | **721** | 721 |
| **las siete valen — tejido exhibido** | 37.216 | 37.402 | **37.489** | 37.489 |

Otras dos semillas, mismo dibujo: 1001 (15.241 pinchazos) y 7777 (22.085), con `up`/`down` en
85/71 y 216/225 sobre la máquina del triángulo y todo lo demás en 0.

**El detector no está ciego**: sobre la máquina original `symm` falla 236 veces y `support` 144.

**Y hay una predicción que se cumple.** En la semilla 31337 la máquina simétrica deja 82 fallos de
`support`; la del triángulo los deja en **0**. Eso es exactamente lo que dice la demostración: mi
prueba de `support` usa `TriProp`, que sólo garantiza tu pasada de v69. No es coincidencia, es la
hipótesis midiéndose sola.

## 3. Lo demostrado

```lean
theorem PreFabric_star (g : GPathM) (q : PathNodeId) (qn : PNodeM)
    (hq : g.node? q = some qn)
    (hown : OwnersGlobal g) (hgn : GN g) (hoos : SelfOwn.OOS g)
    (hsym : Threaded.OwnSymmetric g) (htri : TriProp g)
    (hnodeval : ∀ p n, g.node? p = some n → isValidNode g n = true) :
    PreFabric g (StarS g qn) (StarT g qn)          -- [propext, Quot.sound]
```

Siete cláusulas, y **cada una sale de un invariante tuyo**:

* `gow` — los owners de un superviviente son owners globales (v25, F2.c; y ayer, `OwnersGlobal`);
* `node` — y los owners globales son nodos (v25);
* `symm` — el review simétrico de **v64**;
* `self` — `OOS` más la validez del nodo;
* `support` — **el triángulo de v69**, aplicado a la pareja `q` y el miembro;
* `inS`, `sub` — por construcción.

Y un detalle que me gustó: **el candidato respeta el pinchazo gratis**. No hay que imponerlo:
`OOS` dice que los owners de `q` en el paso de `q` son `q` y nada más, luego todo miembro de
`owners(q)` es compatible con pinchar `q`. Es `StarS_compat`, y depende sólo de `propext`.

El cierre:

```lean
theorem PinNonEmpty_of_star … (hup : …) (hdown : …) : PinNonEmpty g q
```

Con `up` y `down` dadas, el candidato del lector **es** un tejido dentro del pinchazo, y el pick
deja el estado válido. Es una reducción, no una prueba de `PickSome`.

## 4. Qué significa el residuo, y por qué tiene que estar ahí

`up` dice: *toda entrada de la tabla de un miembro la lleva un **padre** del miembro que también
está en su tabla*. `down`, lo mismo con un hijo. Son las dos cláusulas **de camino** — las únicas
que hablan de los enlaces y no de las tablas.

Que fallen **tiene que pasar**. Si no fallaran, el candidato sería siempre un tejido, `PinNonEmpty`
sería teorema, `PickSome` seguiría, y con él la decisión de 3SAT. El muro de v70 sigue en su sitio:
lo que hoy cambia es que ahora está **localizado en dos cláusulas nombradas**, medidas al ~2% de
los pinchazos, en vez de repartido por un enunciado equivalente a la validez.

Dicho de otra forma: v82 dejó P4 como *«esta obligación es la misma que la de partida»*. Hoy P4 es
*«siete novenas partes de la obligación están pagadas; lo que falta es que las entradas de la tabla
se encaminen por padres e hijos dentro de la propia tabla»*. Eso ya es un objetivo, no una tautología.

## 5. Una nota sobre las máquinas

La medición usa cuatro conductores: el original, el simétrico (v64), el del triángulo (v69) y la
combinación de los dos últimos. Los tres primeros son tuyos; **la combinación simétrico+triángulo
no existe en el modelo** y la definí sólo dentro del código de medición, para ver qué hacen tus dos
correcciones juntas. La respuesta, en estas semillas: lo mismo que el triángulo solo — el triángulo
ya restaura la simetría por su cuenta en estos estados.

## 6. Estado

| pieza | estado |
|---|---|
| **P1** el tejido nace | ✅ v78 |
| **P2** lo preservan las operaciones y el `join` | ✅ v65 + v79 |
| **P3** el pinzado cubre y no se estrecha | ✅ cerrada (v83, v84, v85, v86) |
| **P4** el puente a `PickSome` | **7 de 9 cláusulas demostradas (hoy); residuo `up`/`down`, medido al ~2%** |
| **P5** cierre con `L7` | libre |

Lo siguiente, si quieres seguir por aquí, es atacar `up`/`down` — no en general (ahí está el muro),
sino viendo **qué estados los cumplen**: los 37.489 de 38.398 que sí los cumplen son el 97,6%, y
caracterizar esa clase es un objetivo honesto y del tamaño de una sesión.

Build: `lake build AbsSat` verde, 100 módulos, 0 `sorry`, 0 axiomas de proyecto; los teoremas
nuevos cierran en `[propext, Quot.sound]` o menos — `StarS_compat` sólo en `propext`.
