# Verificación para el Autor v49: recap del estado de validación, y qué falta para cerrarla

Ricardo, soy Claude (Opus 5). Aquí está el estado real, auditado contra el código y no contra mi memoria, más los siguientes pasos. Empiezo por lo que creo que es la corrección más importante de encuadre.

---

## 0. La validación completa tiene cinco eslabones, no uno

Es fácil pensar que «solo falta L6». No es así. Para poder decir *«este algoritmo decide 3SAT correctamente»* con respaldo formal hacen falta cinco eslabones, y **solo uno de los cinco es el problema matemático abierto**. Otros dos no tienen todavía ningún teorema.

| # | eslabón | qué afirma | estado |
|---|---|---|---|
| 1 | **CNF → GMap** | el mapa representa fielmente la fórmula | **sin verificar** — `ImportCnf` es código `IO` sin teoremas; no hay semántica booleana formalizada |
| 2 | **GMap → estados** | todo estado alcanzable cumple los invariantes (L1 y compañía) | **verificado en Lean**, sin axiomas |
| 3 | **estado válido → cadena** | un conjunto válido contiene una cadena co-poseída (L6 / `Inhabited`) | **abierto** — un enunciado, ver §4 |
| 4 | **cadena → asignación** | una cadena del grafo da una asignación que satisface la fórmula (L7) | **sin verificar** |
| 5 | **ejecutable ↔ espejo** | el espejo puro y el ejecutable `IO` deciden lo mismo (F6) | **empírico**, no teorema |

Los eslabones 1 y 4 son los que convierten «hay una cadena» en «la fórmula es satisfacible». Sin ellos, todo el trabajo de los eslabones 2 y 3 habla de un grafo, no de 3SAT. **Son trabajo acotado y hacedero** —a diferencia del 3— y hoy no están empezados.

---

## 1. Lo que está verificado a máquina

**Higiene**, comprobada ahora mismo:

| | |
|---|---|
| Módulos | 74, `lake build AbsSat` verde |
| `sorry` | **0** (las tres apariciones del texto están en comentarios) |
| Axiomas de proyecto | **0** |
| `native_decide` | **0** |
| Pines `#print axioms` que rompen el build | **106** |
| Cierres | `[propext, Quot.sound]` o más finos, **salvo tres** |

Las tres excepciones son del lado del mapa y arrastran `Classical.choice`: `MapReqs.addVar_negBlock_ok`, `MapReqs.addGateCase_ok`, `MapReqs.repeated_literal_not_functional`. Están pinadas como tales, así que no se pueden colar más sin que el build lo diga.

**La pila de invariantes** — todos demostrados para *toda* la máquina (`Reachable`: semilla, `upFiltering`, `join`):

| invariante | qué dice |
|---|---|
| `L1` / `L1_cor` | los requisitos filtran los owners (fase F5) |
| `GN` | todo owner global es un nodo |
| `PN`, `PBelow`, `NotRoot` | los padres son nodos, un paso por debajo; nada sobre el 0 es raíz |
| `SN`, `SAbove`, `RootAtZero` | los hijos son nodos, un paso por encima; el paso 0 es raíz |
| `SMP`, `PMS` | las tablas de padres e hijos se reflejan **en los dos sentidos** |
| `OOS`, `SNN` | en su propio paso el único owner de un nodo es él mismo; los pasos son ≥ 0 |
| `TL`, `PMP` | `parent_id` nombra el id de mapa de los padres |
| `LinksInOwners` | **todo padre y todo hijo es owner** (el puente) |

**Terminación y preservación:**

- F2.a/F2.b/F2.c: la review termina, y en su punto fijo cada nodo pasa `isValidNode`, con owners ya coherentes con padres e hijos (arco-consistencia).
- `ChainSound_*`: una cadena sonora **sobrevive** a la review entera — limpieza, desenlace, las dos pasadas de coherencia y el bucle de fuel.

**Resultados estructurales sobre las cadenas:**

| teorema | qué da |
|---|---|
| `exists_isChain` (v27) | todo estado válido tiene un **camino** de 0 a la cima |
| `threaded` (v42/v47) | **todo nodo** está en un camino completo **cuyos nodos lo poseen todos** |
| `owner_below_on_descent` (v46) | los owners por debajo de un nodo son **ancestros** alcanzados por descensos que los arrastran |
| `pid_unique` + `pairwiseOwned_of_fullyPinned` (v40) | en un estado totalmente pinzado hay **un solo nodo por paso**, y la co-posesión sale sola |
| `Inhabited_of_pickSome` (v19/v40) | la inducción del descenso, **con el caso base demostrado** |
| `Closed_cleanInvalidGo`, `Closed_Core` (v43/v44) | un conjunto auto-sostenido sobrevive a la poda, y el **núcleo** lo es por construcción |
| `isValid_cleanInvalid_pin` (v45/v48) | del pinchazo a la validez, con **una sola hipótesis** |

---

## 2. Lo que está validado empíricamente

| banda | qué compara | resultado |
|---|---|---|
| `lake exe diffTest` | fuerza bruta ↔ ejecutable ↔ espejo, veredicto **y** conjunto de soluciones | 400/400 y 300/300 tras el último cambio; >2.000 acumuladas |
| `lake exe validate` | «sin zombis» como invariante interno, con certificado por estado | 50/50 limpias, 4.835 estados, `Inhabited` certificado en todos |
| `extend --pickvalid` | ninguna elección permitida invalida | **0** de 63.314 |
| `extend --core` | el núcleo arco-consistente cubre todos los pasos | **0** fallos en 24.877 pinchazos |
| `extend --closed` | el residuo `support` a distancia ≥ 2 | **0** de 3.473.942 |
| `extend --randombridge`, `--stale` | el puente owners/parents | **0** tras el arreglo (antes 277) |
| `extend --zerosons` | soporte rancio en el paso 0 | **0** tras el arreglo (antes 3 y 51) |

---

## 3. Lo que está refutado (y por qué eso vale)

Cada refutación cerró una ruta y evitó meses de trabajo en ella. Van con números porque los números son el argumento.

| propiedad | refutada con |
|---|---|
| `Extendable` (la máquina no necesita retroceder, sin propagación) | 1.574 cadenas parciales muertas |
| α-aciclicidad del hipergrafo del mapa | ciclo estructural, `lake exe hyper` |
| `ArcImpliesChain` | testigo explícito en Lean (`degenerate`) |
| `SupportClique` | 63,9 M violaciones |
| `OwnersSymmetric` | 1.364 |
| `OwnersTransitive` (global y por enlace) | 2.950.784 de 22.521.728; 15.240 y 18.919 por dirección |
| `PinSetDownClosed` | 722.851 de 3.723.185 y 1.418.285 de 6.271.084 |
| `AnchoredDescentStaysInSupport` | 6.371 de 125.528 descensos |
| el lema de la revisión externa | 1.035.280 de 4.429.212 pares |

Dos que **dejaron** de estar refutadas porque eran bugs, no conjeturas: `ParentIsOwner` y `SonIsOwner` (v36 → v39, tras tu arreglo del desenlace).

---

## 4. El residuo: un enunciado con cinco caras

Todo lo abierto del eslabón 3 es **un solo enunciado**, que aparece con cinco formas distintas según desde dónde se mire:

| desde | forma |
|---|---|
| la cadena | `PairwiseOwned` — todo par de la cadena se posee |
| la elección | `PickValid` / `PickSome` — alguna elección permitida mantiene la validez |
| el testigo | `support` — un candidato tiene owner candidato **a distancia ≥ 2** |
| el núcleo | `CoreCovers` — el núcleo arco-consistente llega a todos los pasos |
| las pasadas de coherencia | `share` — un miembro y su padre-miembro poseen un miembro común |

Lo que sabemos de él, medido y demostrado:

- **Es cierto** en todo lo medido: 0 de 3,47 M de comprobaciones lejanas, 0 de 24.877 pinchazos.
- **Es estrictamente existencial**: la versión ∀ (`PinSetDownClosed`) es falsa, con un 19–23 % de contraejemplos.
- **No lo produce la construcción obvia**: el descenso anclado se sale del soporte en un 5–8 % de los casos.
- **Está libre en cuatro pasos**: el pinzado, el propio y los dos vecinos — gracias a tu arreglo del puente.

Es decir: sabemos que el testigo existe, sabemos que no vale cualquiera, y sabemos que la receta natural no lo encuentra. **Lo que falta es una regla de elección**, y es la primera vez en esta serie que la diana tiene forma de algoritmo en vez de forma de propiedad.

---

## 5. Siguientes pasos, por orden de rentabilidad

### Paso 1 — Cerrar los eslabones 1 y 4 (semántica de 3SAT)

**Es lo más rentable y no depende del problema abierto.** Hoy nada en el desarrollo dice qué es una fórmula 3SAT ni qué es satisfacerla; el `denot` habla de caminos, no de asignaciones.

Qué hay que hacer:

1. Definir en Lean `CNF`, `Assignment` y `satisfies : Assignment → CNF → Prop`.
2. Definir `buildMap : CNF → GMap` como función **pura** (hoy `ImportCnf` es `IO`) y demostrar `NodeOk` de todo lo que construye — la parte de `MapReqs` ya está hecha, falta enchufarla.
3. Demostrar **L7**: de un camino de `denot` sale una asignación, y esa asignación satisface la fórmula.
4. Demostrar la vuelta que hace falta para UNSAT: si la fórmula es satisfacible, el mapa admite un camino.

**Criterio de hecho:** `theorem sound : Inhabited (machine (buildMap φ)) → ∃ a, satisfies a φ`, sin axiomas. Con eso, el día que caiga el eslabón 3 el teorema final se ensambla solo; sin eso, no.

**Tamaño:** mediano. Es trabajo de definición y de inducción sobre la construcción del mapa, sin obstrucciones conocidas.

### Paso 2 — Atacar el residuo con la información nueva

Tres frentes, en este orden:

**(a) La regla de elección.** v46 dejó la diana: entre los descensos que arrastran el pinchazo, hace falta uno que se quede dentro del soporte del candidato. La medición siguiente es concreta: **en los 6.371 descensos que fallan, ¿existe otra elección de padre que funcione?** Si siempre existe, hay una regla que descubrir; si no, el enunciado necesita otra ruta y lo sabremos.

**(b) Buscar contraejemplo sin `Reachable`.** Es el patrón que funcionó en v24 y no se ha probado aquí. Si `CoreCovers` es falso para grafos arco-consistentes arbitrarios, la refutación **nombra** el invariante específico de la máquina que tiene que entrar en la demostración. Es información valiosa aunque salga que no.

**(c) La estructura 0/1/all del mapa.** v13 refutó que las tablas de owners hereden la forma implicacional. Pero **el conjunto candidato tras un pinchazo** no se ha mirado con esa lupa. Es una hipótesis barata de medir.

### Paso 3 — Convertir el eslabón 5 en teorema

Hoy el espejo y el ejecutable coinciden por medición (>2.000 instancias, cero desacuerdos). Convertirlo en un teorema de refinamiento es un trabajo grande pero bien definido: cada operación del ejecutable simula la del espejo módulo el orden de iteración. El plan lo puso fuera de alcance y sigue siendo la decisión correcta **hasta** que el eslabón 3 caiga — antes de eso, formalizar el refinamiento no compra nada que la banda diferencial no dé ya.

### Paso 4 — Higiene

Quitar `Classical.choice` de los tres lemas de `MapReqs`, o dejar constancia de por qué se queda. Es media hora y cierra la afirmación «cero clásico» sin asteriscos.

### Lo que *no* recomiendo hacer todavía

**La complejidad.** No hay un solo teorema sobre tiempo ni tamaño en todo el desarrollo, y la afirmación fuerte de v14 —«sin zombis, más una cota de tiempo, es P = NP»— tiene los dos factores sin formalizar. Meterse ahí antes de cerrar el eslabón 3 sería construir sobre el hueco.

---

## 6. Resumen honesto

Lo que hay es **una máquina cuyos invariantes estructurales están completamente demostrados**, con una banda diferencial que no ha encontrado un desacuerdo en más de dos mil instancias, y **una obligación matemática abierta**, reducida a lo largo de treinta documentos desde «no hay zombis» hasta «un candidato tiene soporte candidato a distancia dos».

Lo que no hay, y conviene decirlo claro, es **el puente con 3SAT**: nada en Lean dice todavía que un camino del grafo sea una asignación que satisface la fórmula. Ese es el trabajo que más acerca el resultado final y el único de la lista que no depende de resolver el problema difícil.

---

*Claude (Opus 5), 2026-09-10. Estado auditado contra el árbol: `lake build AbsSat` verde, 74 módulos, 0 `sorry`, 0 axiomas de proyecto, 106 pines de axiomas.*
