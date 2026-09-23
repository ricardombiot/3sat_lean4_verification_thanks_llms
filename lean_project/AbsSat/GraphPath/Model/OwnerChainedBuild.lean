-- lean_project/AbsSat/GraphPath/Model/OwnerChainedBuild.lean
import AbsSat.GraphPath.Model.ReaderChain
import AbsSat.GraphPath.Model.TablesSoundBuild
import AbsSat.GraphPath.Model.PinExactBoundary

/-!
# La semilla de `OwnerChained`: la frase del autor en el estado de la línea final

`ReaderChain.readerVerdictW_of_pinPairChained` deja la lectura sin retroceso colgando de dos cosas:
el paso (`PinPairChained`) y **la semilla** —que la frase del autor valga en el estado que la
máquina aparca en la línea final—. Este módulo ataca la semilla.

Y lo primero que hay que decir es lo que la une con lo demás:

* **`ownerChained_of_tablesSound`** — la frase es **consecuencia** de `TablesSound`. Un owner global
  es un nodo, un nodo se posee a sí mismo, y `TablesSound` convierte esa entrada en una cadena que
  pasa por él. Así que **todo lo que `TablesSoundBuild` cierra, la semilla lo hereda**: `up`,
  `doJoin`, la revisión, los pasos pares y los impares.
* Y por debajo de `TablesSound` la frase se cierra además **por su cuenta**, con pruebas más cortas
  y sin las hipótesis de contexto: `ReaderChain.ownerChained_addNode`, `ownerChained_join`,
  `ownerChained_reviewAgg`, y aquí los dos casos del filtro del bloque de literales.

El saldo es que la semilla y `TablesSound` chocan contra **la misma** pared —los pasos de
cláusula— y que la frase pide allí estrictamente menos: `Steerable` tiene que dirigir una cadena
por **un par y tres requisitos**; `OwnerChained` solo por **una entrada y tres requisitos**.
-/

namespace AbsSat.GraphPath.Model.OwnerChainedBuild

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderChain
open AbsSat.GraphPath.Model.TablesSoundBuild
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes)

-- ============================================================
-- El puente: la frase sale de `TablesSound`
-- ============================================================

/-- **`TablesSound` implica la frase del autor.**

Un owner global es un nodo (`RCtx.gn`), y un nodo válido **se posee a sí mismo**
(`FabricAdd.self_mem_owners`: la validez le pone un owner en su propio paso, y `OOS` dice que ese
owner es él). Así que `q` es una entrada de su propia tabla, y `TablesSound` la convierte en una
cadena que pasa por `q`.

Esto ordena las dos rutas de una vez: **`OwnerChained` es más débil que `TablesSound`**, y por
tanto todo lo que `TablesSoundBuild` cierra vale también aquí. Lo que gana la ruta de la frase es
que además se cierra **sin pasar por `TablesSound`** en tres de las cuatro operaciones, con menos
hipótesis. -/
theorem ownerChained_of_tablesSound (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true)
    (ht : TablesSound g) : OwnerChained g := by
  intro q hq h0 h1
  have ctx := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hR) hv
  have rcg := RCtx_of_readableAgg g hR
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g q).mp (rcg.gn q hq))
  have hself := FabricAdd.self_mem_owners g rcg.oos q n hn (ctx.nodeval q n hn) h0 h1
  obtain ⟨sel, hsc, hsq, _⟩ := ht q n hn h0 h1 q h0 h1 hself
  exact ⟨sel, hsc, by rw [hsq]⟩

-- ============================================================
-- Y por su cuenta: los dos casos del filtro del bloque de literales
-- ============================================================

/-- **Un filtro sin requisitos es la revisión sola**, y la revisión ya estaba cerrada. -/
theorem ownerChained_filter_nil (g : GPathM) (reqs : List NodeId) (hnil : reqs = [])
    (ho : OwnerChained g) : OwnerChained (filterAllAgg g reqs) := by
  subst hnil; exact ownerChained_reviewAgg g ho

/-- **El envío a un nodo de VARIABLE sale gratis.** `reqOfCnf_var`: un paso par del bloque de
literales no pide nada, así que su filtro es la revisión. Es un paso por variable, la mitad del
bloque. -/
theorem ownerChained_filterAllAgg_var (φ : Cnf) (g : GPathM) (d : NodeId) (v : Nat)
    (hv : v < φ.nVars) (hd : d.step = varStep v) (ho : OwnerChained g) :
    OwnerChained (filterAllAgg g (reqOfCnf φ d)) :=
  ownerChained_filter_nil g _ (reqOfCnf_var φ d v hv hd) ho

/-- **Y el paso IMPAR: o el filtro no hace nada, o mata el estado.**

Un paso impar pide un solo requisito, en el paso justo de abajo, que es la **cima** del estado de
partida — y la cima lleva un solo id de mapa (`TopSingleId`). Si el requisito es esa clave, el
filtro no borra ni una entrada y se reduce a la revisión; si no lo es, la cima se queda vacía y el
envío se descarta por inválido, de modo que la hipótesis de validez es imposible.

El filtro no elige nada aquí: solo comprueba. Misma forma que
`TablesSoundBuild.tablesSound_filterAllAgg_top`, y con una hipótesis menos —no hace falta
`NodupIds`, porque la frase no pasa por la revisión nodo a nodo—. -/
theorem ownerChained_filterAllAgg_top (g : GPathM) (k : NodeId) (htop : TopSingleId g k)
    (r : NodeId) (hrs : r.step = g.current_step - 1) (hpos : 0 < g.current_step)
    (hv : isValid (filterAllAgg g [r]) = true) (ho : OwnerChained g) :
    OwnerChained (filterAllAgg g [r]) := by
  have hfold : [r].foldl filterRequire g = filterRequire g r := rfl
  if hrk : r = k then
    have heq : filterAllAgg g [r] = filterAllAgg g [] := by
      simp only [filterAllAgg, hfold, filterRequire_top_eq g k htop r hrs hrk]
      rfl
    rw [heq]
    exact ownerChained_reviewAgg g ho
  else
    exfalso
    have hdead := not_isValid_filterRequire_top g k htop r hrs hrk hpos
    have hpr : Pruned (filterRequire g r) (filterAllAgg g [r]) := by
      simp only [filterAllAgg, hfold]; exact pruned_reviewAgg _
    have hgood : isValid (filterRequire g r) = true := by
      simp only [isValid, List.all_eq_true] at hv ⊢
      intro kk hkk
      have hkk' : kk ∈ intRange 0 ((filterAllAgg g [r]).current_step - 1) := by
        rwa [hpr.step_eq]
      have hx := hv kk hkk'
      simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hx ⊢
      obtain ⟨q, hq, hqs⟩ := hx
      exact ⟨q, hpr.gowners_sub q hq, hqs⟩
    rw [hdead] at hgood
    exact Bool.noConfusion hgood

/-! ## Lo que queda de la semilla, y cuánto menos es

Con esto la semilla tiene el mismo mapa que `TablesSound`, operación por operación:

| operación de la máquina | `TablesSound` | `OwnerChained` |
|---|---|---|
| `initSeed` | cerrado | cerrado (por el puente) |
| `up` / `addNode` | cerrado | **cerrado aparte**, `ownerChained_addNode` |
| `doJoin` / `join` | cerrado | **cerrado aparte**, sin condiciones entre los lados |
| revisión | cerrado | **cerrado aparte**, `ownerChained_reviewAgg` |
| filtro, pasos pares / frontera / sobre `fusionTop` | cerrado | **cerrado aparte** |
| filtro, pasos impares | cerrado | **cerrado aparte** |
| filtro, pasos de **cláusula** | abierto (`Steerable`) | abierto |

Y la diferencia entre las dos casillas abiertas es exactamente una cosa, que conviene mirar de
cerca porque es donde esta línea de trabajo tiene su frontera:

* `TablesSoundBuild.Steerable` pide una cadena que pase por **el par `(x,q)`** y además elija los
  **tres** requisitos: cinco cosas a la vez.
* La semilla de `OwnerChained` pide una cadena que pase por **la entrada `q`** y elija los tres
  requisitos: cuatro.

Y `SeqPin.pinOneByOne` / `RunSteps.full_seq` reducen los tres requisitos a pincharlos **de uno en
uno** con revisión entre medias, así que la obligación real es, cada vez, *una entrada y un pin* —
que es `ReaderChain.PinPairChained`, el paso. **La semilla y el paso son la misma frase**, y por
eso cerrar uno cierra el otro.
-/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.ownerChained_of_tablesSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownerChained_of_tablesSound

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.ownerChained_filterAllAgg_var' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownerChained_filterAllAgg_var

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.ownerChained_filterAllAgg_top' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownerChained_filterAllAgg_top

-- ============================================================
-- `Steerable`, con los tres recortes a la vez
-- ============================================================

/-- **El residuo del pin, recortado por los tres lados a la vez.**

Tres cosas quedan fuera de la obligación, y cada una por su propio motivo:

* **`q.id.step = r.step`** — la entrada al paso pinchado lleva el pin, y la cadena de antes ya pasa
  por ella (`ReaderChain.tablesSound_pin_of_pairs`);
* **`x.id.step = r.step`** — el nodo que sobrevive en el paso pinchado **es** el pin, así que
  cualquier cadena que pase por él lo satisface (`ReaderChain.pinPairSound_of_off`);
* **la tabla de `x` sin alternativa en `r.step`** — si todos los owners de `x` en ese paso llevan ya
  el pin, la posesión por pares de `ChainSound` obliga a la cadena a llevarlo
  (`TablesSoundBuild.realizes_pin_of_singleId`).

Lo que queda es el par `(x,q)` con **los dos extremos fuera del paso del pin** y con la tabla de
`x` conservando de verdad las dos opciones. Tres pasos distintos y elección en el de en medio. -/
def PinResidue (g : GPathM) (r : NodeId) : Prop :=
  ∀ x n, (filterAllAgg g [r]).node? x = some n → 0 ≤ x.id.step →
    x.id.step < (filterAllAgg g [r]).current_step → x.id.step ≠ r.step →
    (∀ nx, g.node? x = some nx → ∃ u ∈ nx.owners, u.id.step = r.step ∧ u.id ≠ r) →
    ∀ q ∈ n.owners, 0 ≤ q.id.step → q.id.step < (filterAllAgg g [r]).current_step →
      q.id.step ≠ r.step → Realizes (filterAllAgg g [r]) x q

/-- **Y basta: con el residuo, el pin conserva `TablesSound` entero.**

Cuatro ramas, y tres se cierran aquí mismo sin hipótesis. Es `Steerable` para un pin, con todo lo
que se sabe metido dentro. -/
theorem tablesSound_pin_of_residue (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true)
    (ht : TablesSound g) (r : NodeId) (hr0 : 0 ≤ r.step) (hrs : r.step < g.current_step)
    (hvr : isValid (filterAllAgg g [r]) = true) (h : PinResidue g r) :
    TablesSound (filterAllAgg g [r]) := by
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  have hRr := ReadableAgg_filterAllAgg g hR [r]
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
  have rcR := RCtx_of_readableAgg _ hRr
  have rcg := RCtx_of_readableAgg g hR
  have ctxg := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hR) hv
  have hpr := pruned_filterAllAgg g [r]
  have hcs := hpr.step_eq
  obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
  have hxn := node?_id_eq _ x n hx
  have hx₀ : g.node? x = some n₀ := by rw [← hxn, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
  have hx1g : x.id.step < g.current_step := by rw [← hcs]; exact hx1
  have hq1g : q.id.step < g.current_step := by rw [← hcs]; exact hq1
  obtain ⟨sel, hsc, hsx, hsq⟩ := ht x n₀ hx₀ hx0 hx1g q hq0 hq1g (hown q hqn)
  rcases int_eq_or_ne q.id.step r.step with hqr | hqr
  · -- la entrada vive en el paso pinchado: lleva el pin
    have hqid : q.id = r :=
      ReaderComplete.pin_id g r q (ctxR.ownGow x n hx q hqn hq0 hq1) hqr
    exact ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => by
      rw [List.mem_singleton.mp hreq, ← hqr, hsq, hqid]), hsx, hsq⟩
  · rcases int_eq_or_ne x.id.step r.step with hxr | hxr
    · -- el nodo vive en el paso pinchado: ES el pin
      have hself := FabricAdd.self_mem_owners _ rcR.oos x n hx (ctxR.nodeval x n hx) hx0 hx1
      have hxid : x.id = r :=
        ReaderComplete.pin_id g r x (ctxR.ownGow x n hx x hself hx0 hx1) hxr
      exact ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => by
        rw [List.mem_singleton.mp hreq, ← hxr, hsx, hxid]), hsx, hsq⟩
    · by_cases hch : ∃ u ∈ n₀.owners, u.id.step = r.step ∧ u.id ≠ r
      · refine h x n hx hx0 hx1 hxr (fun nx' hx' => ?_) q hqn hq0 hq1 hqr
        rw [← Option.some.inj (hx₀.symm.trans hx')]; exact hch
      · -- la tabla de `x` ya no tenía elección en el paso del pin
        have hsingle : ∀ u ∈ n₀.owners, u.id.step = r.step → u.id = r := by
          intro u hu hus
          by_cases hur : u.id = r
          · exact hur
          · exact absurd ⟨u, hu, hus, hur⟩ hch
        have hselfg :=
          FabricAdd.self_mem_owners g rcg.oos x n₀ hx₀ (ctxg.nodeval x n₀ hx₀) hx0 hx1g
        exact realizes_pin_of_singleId g r hr0 hrs x q n₀ hx₀ hx0 hx1g hselfg hsingle sel hsc hsx hsq

/-! ## Lo que queda de `Steerable`, dicho entero

    x, q y r en tres pasos distintos, y la tabla de x con las dos opciones en el paso de r.

Ni una condición más. Y las dos medidas que hay sobre eso apuntan en la misma dirección:

* `row-degree pinchoice` — el caso **sin** elección, que aquí se cierra, cubre el 90,4 % de los
  pines en `dos_de_tres.cnf` y el 65,1 % en ocho fórmulas aleatorias;
* `row-degree pairdesc`, columna «como lo hace el lector» —pinchar y **revisar** en cada paso, que
  es lo que el algoritmo hace— : 1.016/1.016 pares en `dos_de_tres.cnf` y 12.602/12.602 en el
  corpus aleatorio, **sin un solo retroceso**.

Lo que falta no es evidencia. -/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.tablesSound_pin_of_residue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_pin_of_residue

-- ============================================================
-- Y el requisito deja de ser un id: pasa a ser un nodo de las dos tablas
-- ============================================================

/-- **La terna, con el tercero COMPARTIDO.**

El residuo pedía una cadena por `x` y `q` que además *eligiera el id `r`* en su paso. Esto pide
menos trabajo de búsqueda y más información: que la cadena pase por `x`, por `q` y por un **nodo
concreto `z`** que las tablas de los dos contienen y que **es** el valor pinchado.

La diferencia no es cosmética. `z ∈ nx.owners` es algo que la posesión por pares de `ChainSound`
sabe usar —una cadena por `x` elige, en cada paso, un owner de `x`—, mientras que «elegir el id
`r`» no dice nada de las tablas. El tercer punto pasa de ser una condición sobre identificadores a
ser un **dato de la estructura**. -/
def SharedTripleChain (g : GPathM) (r : NodeId) : Prop :=
  ∀ x nx q nq z, g.node? x = some nx → g.node? q = some nq →
    0 ≤ x.id.step → x.id.step < g.current_step →
    0 ≤ q.id.step → q.id.step < g.current_step →
    q ∈ nx.owners → z.id = r → z ∈ nx.owners → z ∈ nq.owners →
      ∃ sel, ChainSound g sel ∧ sel x.id.step = x ∧ sel q.id.step = q ∧ sel z.id.step = z

/-- **Y el testigo lo pone la supervivencia, no la hipótesis.**

`SupportedRun.shared_pin_witness`: si `x` y `q` sobreviven al pin y `q` sigue en la tabla de `x`,
el punto fijo de la criba en el estado **pinchado** (`AggOk`) los obliga a compartir un owner en
todos los pasos, y en el paso del pin ese owner común lleva el pin. Así que `z` existe siempre; no
hay que suponerlo.

Con eso el residuo del filtro queda enteramente dentro de `SharedTripleChain`. -/
theorem pinResidue_of_sharedTriple (g : GPathM) (hR : ReadableAgg g)
    (r : NodeId) (hr0 : 0 ≤ r.step) (hvr : isValid (filterAllAgg g [r]) = true)
    (hrs : r.step < (filterAllAgg g [r]).current_step)
    (hpms : Sons.PMS (filterAllAgg g [r])) (hsn : Sons.SN (filterAllAgg g [r]))
    (h : SharedTripleChain g r) : PinResidue g r := by
  intro x n hx hx0 hx1 _ _ q hqn hq0 hq1 _
  have hRr := ReadableAgg_filterAllAgg g hR [r]
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
  have rcR := RCtx_of_readableAgg _ hRr
  have rcg := RCtx_of_readableAgg g hR
  have hpr := pruned_filterAllAgg g [r]
  have hcs := hpr.step_eq
  -- `q` es un nodo del estado pinchado
  obtain ⟨mq, hmq⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff _ q).mp (rcR.gn q (ctxR.ownGow x n hx q hqn hq0 hq1)))
  -- el testigo compartido, del punto fijo de la criba en el estado pinchado
  obtain ⟨z, hzid, hzx, hzq⟩ := SupportedRun.shared_pin_witness g hR r hvr hr0 hrs hpms hsn
    x q n mq hx hmq hx0 hx1 hq0 hq1 hqn
  -- las dos tablas de antes del pin
  obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
  have hxn := node?_id_eq _ x n hx
  have hx₀ : g.node? x = some n₀ := by rw [← hxn, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
  obtain ⟨m₀, hm₀, hidq, hownq, _⟩ := hpr.nodes_derived mq (List.mem_of_find?_eq_some hmq)
  have hqn' := node?_id_eq _ q mq hmq
  have hq₀ : g.node? q = some m₀ := by rw [← hqn', hidq]; exact node?_of_mem rcg.nodup m₀ hm₀
  obtain ⟨sel, hsc, hsx, hsq, hsz⟩ := h x n₀ q m₀ z hx₀ hq₀ hx0 (by rw [← hcs]; exact hx1)
    hq0 (by rw [← hcs]; exact hq1) (hown q hqn) hzid (hown z hzx) (hownq z hzq)
  refine ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => ?_), hsx, hsq⟩
  have hzs : z.id.step = r.step := by rw [hzid]
  rw [List.mem_singleton.mp hreq, ← hzs, hsz, hzid]

/-! ## El residuo, en su forma más débil hasta ahora

    x, q y un tercero z que las tablas de los dos contienen, en una misma cadena.

Y conviene tener presente **por dónde no sale**, que está medido y escrito en
`SupportedRun.triple_data_of_survival`: las tres parejas `(x,q)`, `(x,z)`, `(q,z)` tienen cadena
—eso es `TablesSound` del estado de antes, gratis— y **pegarlas es falso** en general. Con
soluciones `{110, 101, 011}` cada pareja tiene su testigo y la terna necesitaría `111`.

Lo que ese contraejemplo también dice es dónde está la salida: en ese caso, tras pinchar, la criba
del estado pinchado compara `x` y `q` y **no comparten owner** en el paso del tercer bit, así que
`aggPair` borra el par y la obligación ni llega a plantearse. Por eso `SharedTripleChain` se
alimenta de `shared_pin_witness` y no de las tres parejas: el testigo `z` **existe porque el par
sobrevivió al punto fijo**, y ése es justamente el dato que el contraejemplo no tiene. -/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.pinResidue_of_sharedTriple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinResidue_of_sharedTriple

-- ============================================================
-- Los pasos de cláusula, con `ReqSatisfying`: el filtro no elige, propaga
-- ============================================================

/-- **Una cadena de un estado de la máquina satisface, por sí sola, los requisitos del nodo al que
se está enviando.**

Y eso cierra los pasos de cláusula, que era la casilla que quedaba.

El argumento, en tres frases:

1. la **cima** del estado lleva un solo id de mapa, el del envío (`TopSingleId`), así que toda cadena
   del estado elige `d` allí — no hay elección en la cima;
2. `MapChain.reqSatisfying_of_pairwiseOwned` dice que una cadena **satisface los requisitos de todo
   nodo que elige**: la posesión por pares mete `sel req.step` en la tabla de `sel k`, y
   `ReqFiltered` dice que esa tabla, en el paso del requisito, solo contiene el requisito;
3. luego la cadena satisface `reqOf d`, y `ChainSound_filterAllAgg` la pasa al otro lado entera.

Dicho en el lenguaje del algoritmo, y es la frase del autor: **el filtro de un envío no elige nada,
propaga lo que la cima ya fijó.** Los tres requisitos de una cláusula son consecuencia del nodo de
cláusula al que se envía, y cualquier camino que llegue a ese nodo los cumple ya. -/
theorem ownerChained_filterAllAgg_of_reqSatisfying (P : GPathM) (reqOf : NodeId → List NodeId)
    (d : NodeId) (htop : TopSingleId P d) (hpos : 0 < P.current_step)
    (hrf : ReqFiltered reqOf P)
    (hback : ∀ n ∈ P.nodes, ∀ req ∈ reqOf n.id.id, req.step < n.id.id.step)
    (ho : ReaderChain.OwnerChained P) :
    ReaderChain.OwnerChained (filterAllAgg P (reqOf d)) := by
  intro q hq h0 h1
  have hpr := pruned_filterAllAgg P (reqOf d)
  have h1' : q.id.step < P.current_step := by rw [← hpr.step_eq]; exact h1
  obtain ⟨sel, hsc, hsel⟩ := ho q (hpr.gowners_sub q hq) h0 h1'
  have hstepTop := (hsc.chain.1.1 (P.current_step - 1) (by omega) (by omega)).2
  have htopsel : (sel (P.current_step - 1)).id = d :=
    htop (sel (P.current_step - 1)) (hsc.chain.2.2 _ (by omega) (by omega)) hstepTop
  have hrs := MapChain.reqSatisfying_of_pairwiseOwned reqOf P hrf hback sel
    hsc.chain.1 hsc.chain.2.1
  refine ⟨sel, ChainSound_filterAllAgg P (reqOf d) sel hsc (fun req hreq hr0 hr1 => ?_), hsel⟩
  exact hrs (P.current_step - 1) (by omega) (by omega) req (by rw [htopsel]; exact hreq) hr0 hr1

/--
info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.ownerChained_filterAllAgg_of_reqSatisfying' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms ownerChained_filterAllAgg_of_reqSatisfying

-- ============================================================
-- El pin del LECTOR: reducido a la exactitud de las tablas
-- ============================================================

/-- **El pin del lector sale de `TablesSound` del estado que se pincha.**

Y la clave es no pedirle a la cadena que pase por el pin, sino **elegir el testigo del pin dentro de
la tabla del superviviente**:

1. si `q` sobrevive al pin, su tabla **lleva el requisito**: tiene una entrada en ese paso —lo exige
   `isValidNode`— y esa entrada es el requisito, porque el filtro no deja otra cosa allí
   (`reqs_in_owners`, que no necesita nada del punto fijo);
2. esa entrada `w` estaba ya en la tabla de `q` antes del pin, porque las tablas solo encogen;
3. y `TablesSound` convierte el par `(q, w)` en una cadena que pasa por los dos — que es
   exactamente lo que el pin pide, porque `w.id` **es** el requisito.

Nótese lo que esto evita: no hay que dirigir ninguna cadena ni juntar tres cosas. El testigo del pin
lo pone la propia supervivencia, y la cadena que hace falta es la de un **par**. -/
theorem pinPairChained_of_tablesSound (g : GPathM) (hR : ReadableAgg g)
    (ht : TablesSound g) : ReaderChain.PinPairChained g := by
  intro req hv hr0 hr1 q hq h0 h1 _
  have hRr := ReadableAgg_filterAllAgg g hR [req]
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hv
  have rcR := RCtx_of_readableAgg _ hRr
  have rcg := RCtx_of_readableAgg g hR
  have hpr := pruned_filterAllAgg g [req]
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff _ q).mp (rcR.gn q hq))
  obtain ⟨w, hwm, hwid⟩ := reqs_in_owners g [req] ctxR q nq hnq req List.mem_cons_self hr0
    (by rw [hpr.step_eq]; exact hr1)
  obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived nq (List.mem_of_find?_eq_some hnq)
  have hqid := node?_id_eq _ q nq hnq
  have hq₀ : g.node? q = some n₀ := by rw [← hqid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
  have hws : w.id.step = req.step := by rw [hwid]
  obtain ⟨sel, hsc, hsq, hsw⟩ := ht q n₀ hq₀ h0 h1 w (by rw [hws]; exact hr0)
    (by rw [hws]; exact hr1) (hown w hwm)
  exact ⟨sel, hsc, by rw [hsq], by rw [← hws, hsw, hwid]⟩

/-! ## Lo que queda, tras esto

El pin del lector ya no es un enunciado suelto: es `TablesSound` del estado que se pincha.

    ReaderChain.PinPairChained g   ⟸   Exactness.TablesSound g

Y `TablesSound` es el invariante más antiguo del repositorio, con toda la maquinaria de
construcción detrás: `up`, `doJoin` y la revisión lo conservan, y desde
`ownerChained_filterAllAgg_of_reqSatisfying` el argumento de la cima cubre también los filtros de
envío. Es además el que la sonda `tsread` mide sobre las trayectorias reales del lector:
**150.124 entradas, cero fantasmas.**

Lo que falta, por tanto, es propagarlo por **el pin del lector** —`RunSteps.PinPairSoundAt` /
`ReaderChain.PinPairSound`—, que es donde estaba el muro desde el principio. Pero el hueco ya no se
multiplica: **una sola frase, sobre un solo invariante.** -/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.pinPairChained_of_tablesSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinPairChained_of_tablesSound

-- ============================================================
-- La unificación: el hueco del lector ES el residuo de `Threaded`
-- ============================================================

/-- **La cadena que vive dentro de la tabla de un nodo está poseída por pares.**

`Threaded` demuestra que la tabla de todo nodo vivo **contiene una cadena entera** —enlazada de
padre a hijo, del paso 0 a la cima, y que pasa por el propio nodo
(`Threaded.chain_through_of_symmetric`)—. Lo único que esa cadena no trae demostrado es que sus
nodos **se posean entre sí**, y su propio docstring lo dice: *«That is now the whole of the
residue.»*

Esto le pone nombre.

**Y por primera vez está medido, y sale limpio.** La sonda `row-degree tablechain` construye esa
cadena —descenso ávido por enlaces de padre sin salir de la tabla— y comprueba sus pares:

| corpus | tablas | el descenso llega al paso 0 | pares | fallos |
|---|---|---|---|---|
| `dos_de_tres.cnf` | 73 | **73 (100 %)** | 11.388 | **0** |
| 3 aleatorias, 4+ vars | 347 | **347 (100 %)** | 183.462 | **0** |

194.850 pares y ni una excepción. Y conviene contrastarlo con lo que sí se midió falso: la tabla de
un nodo **no** es una clique (`row-degree clique`: 7,9 % de pares no se poseen), así que el
enunciado no es trivial — depende de que la cadena esté **enlazada por padres**, y eso es
exactamente lo que `Threaded` construye. -/
def TableChainOwned (g : GPathM) : Prop :=
  ∀ a n, g.node? a = some n → ∀ sel, IsChain g sel →
    (∀ i, 0 ≤ i → i < g.current_step → sel i ∈ n.owners) → PairwiseOwned g sel

/-- **Y con ella, la frase del autor sale entera.**

Un owner global es un nodo, un nodo válido se posee a sí mismo, `Threaded` le da la cadena que vive
en su tabla y que pasa por él, y `SupportedRun.chainSound_of_chain` la eleva a `ChainSound` en
cuanto está poseída por pares.

Y esto **unifica las dos líneas de ataque del repositorio**: el hueco que le queda al lector sin
retroceso y el residuo que `Threaded` dejó anotado hace mucho son **el mismo enunciado**. No son dos
frentes.

Nótese además que es mejor que pasar por `TablesSound`: no pide cadena por un **par**, solo por el
nodo. -/
theorem ownerChained_of_tableChainOwned (g : GPathM)
    (adj : AdjacentOwners.Adj g) (hsmp : Sons.SMP g) (hpos : 0 < g.current_step)
    (ctx : Threaded.TCtx g) (hsym : Threaded.OwnSymmetric g) (hoos : SelfOwn.OOS g)
    (hgn : GownersNodes.GN g) (hpo : TableChainOwned g) :
    ReaderChain.OwnerChained g := by
  intro q hq h0 h1
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g q).mp (hgn q hq))
  have hself := FabricAdd.self_mem_owners g hoos q n hn (ctx.nodeval q n hn) h0 h1
  obtain ⟨sel, hchain, hsx, hin⟩ :=
    Threaded.chain_through_of_symmetric g ctx hsym hoos q n hn hself h0 h1
  exact ⟨sel,
    SupportedRun.chainSound_of_chain g adj hsmp hpos sel hchain (hpo q n hn sel hchain hin),
    by rw [hsx]⟩

/-- **Y la simetría de tablas no es una hipótesis: la da el punto fijo de la criba.**

`AggFixpoint.AggOk` —los dos tests del autor sobre cada par de owners— implica
`Threaded.OwnSymmetric`, y `AggOk` vale en todo estado que sale de `reviewAgg`
(`AggFixpoint.aggOk_reviewAgg`). Así que de las dos hipótesis que `Threaded` dejaba, **una se paga
con el barrido agresivo** y solo queda la otra. -/
theorem ownSymmetric_of_reviewed (g : GPathM) (hok : AggFixpoint.AggOk g) (hsnn : SelfOwn.SNN g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hval : ∀ pid n, g.node? pid = some n → isValidNode g n = true) :
    Threaded.OwnSymmetric g :=
  PinExactBoundary.ownSymmetric_of_aggOk g hok hsnn hbelow hval

/-! ## El hueco, unificado

    readerVerdictW  ⟸  PinAlive  ≡  OwnerChained  ⟸  TableChainOwned

y `TableChainOwned` es, palabra por palabra, el residuo que `Threaded` dejó anotado: **que la cadena
que vive dentro de la tabla de un nodo esté poseída por pares.**

Lo que esto cambia no es el tamaño del hueco sino su número: las dos líneas —la del lector sin
retroceso y la de `Threaded`— apuntaban al mismo sitio sin saberlo. Y la simetría, que `Threaded`
dejaba como hipótesis medida, la paga `AggOk`: es uno de los dos tests que el barrido agresivo del
autor aplica a cada par de owners. -/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.ownerChained_of_tableChainOwned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownerChained_of_tableChainOwned

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.ownSymmetric_of_reviewed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ownSymmetric_of_reviewed

-- ============================================================
-- Dentro de `TableChainOwned`: los pares CONTIGUOS son gratis
-- ============================================================

/-- **Los pares distantes de una cadena, lo único que no sale de los enlaces.** -/
def DistantOwned (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  ∀ i j, 0 ≤ i → 0 ≤ j → i < g.current_step → j < g.current_step →
    j ≠ i + 1 → i ≠ j + 1 → i ≠ j → ∀ m, g.node? (sel j) = some m → sel i ∈ m.owners

/-- **Y entonces la posesión por pares se reduce a los pares distantes.**

Los contiguos salen de lo que ya hay, en las dos direcciones:

* **hacia arriba**: `IsChain` dice que `sel i` es **padre** de `sel (i+1)`, y `Bridge.LinksInOwners`
  dice que los padres están en la tabla. Un paso.
* **hacia abajo**: la simetría de tablas lo devuelve — y la simetría la paga `AggOk`
  (`ownSymmetric_of_reviewed`).

Así que de la posesión por pares no queda nada que probar salvo los pares a distancia ≥ 2. Y ésa es
la forma más nítida que ha tomado la frontera de esta línea de trabajo: **los nodos consecutivos de
la cadena se poseen entre sí, demostrado; la pregunta es si eso se propaga a distancia.** -/
theorem pairwiseOwned_of_distant (g : GPathM) (links : Bridge.LinksInOwners g)
    (hsym : Threaded.OwnSymmetric g) (sel : Int → PathNodeId) (hchain : IsChain g sel)
    (hdist : DistantOwned g sel) : PairwiseOwned g sel := by
  intro i j hi0 hj0 hi1 hj1 hij
  obtain ⟨hsi, hstepi⟩ := hchain.1 i hi0 hi1
  obtain ⟨mj, hmj⟩ := Option.isSome_iff_exists.mp (hchain.1 j hj0 hj1).1
  refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hstepi⟩
  simp only [ownersOf, hmj]
  by_cases h1 : j = i + 1
  · subst h1
    have hlink := hchain.2 i hi0 (by omega)
    rw [hmj] at hlink
    simp only [Option.map_some, Option.getD_some] at hlink
    exact (links _ mj hmj).1 _ hlink
  · by_cases h2 : i = j + 1
    · obtain ⟨mi, hmi⟩ := Option.isSome_iff_exists.mp hsi
      have hlink := hchain.2 j hj0 (by omega)
      rw [show j + 1 = i from h2.symm, hmi] at hlink
      simp only [Option.map_some, Option.getD_some] at hlink
      exact hsym (sel i) mi (sel j) mj hmi hmj ((links _ mi hmi).1 _ hlink)
    · exact hdist i j hi0 hj0 hi1 hj1 h1 h2 hij mj hmj

/-- **Y `TableChainOwned` con ello.** -/
theorem tableChainOwned_of_distant (g : GPathM) (links : Bridge.LinksInOwners g)
    (hsym : Threaded.OwnSymmetric g)
    (hdist : ∀ sel, IsChain g sel → DistantOwned g sel) : TableChainOwned g :=
  fun _ _ _ sel hchain _ => pairwiseOwned_of_distant g links hsym sel hchain (hdist sel hchain)

/-! ## El hueco, en su forma más pequeña hasta ahora

    readerVerdictW  ⟸  PinAlive  ≡  OwnerChained  ⟸  TableChainOwned  ⟸  DistantOwned

y `DistantOwned` dice solo esto:

> en la cadena que vive dentro de la tabla de un nodo, dos nodos **a distancia ≥ 2** se poseen.

Los contiguos están demostrados —el enlace de padre más `LinksInOwners` en un sentido, la simetría
de `AggOk` en el otro—, y todo lo demás de la escalera también. Lo que queda es exactamente la
propagación de la posesión **a distancia**: la transitividad que v40 midió que no vale en general,
aquí restringida a una cadena cuyos nodos están todos en la tabla de un mismo nodo.

Ésa es la frontera, y ya no hay nada más entre ella y el teorema. -/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.pairwiseOwned_of_distant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairwiseOwned_of_distant

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.tableChainOwned_of_distant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tableChainOwned_of_distant

-- ============================================================
-- De la distancia a UN SALTO
-- ============================================================

/-- **Un salto: lo que un nodo de la cadena posee por debajo, lo posee el siguiente.**

Es la versión local de la posesión a distancia, y basta un salto: el resto lo hace la inducción.

**MEDIDO FALSO. No construir sobre esto.** La sonda `row-degree hopdown` la niega en
`dos_de_tres.cnf`: **16 de 484** celdas `(hijo, padre, owner del padre por debajo)` sobre 3 estados,
y la versión restringida —los tres nodos en la tabla de un mismo `a`, que es como el teorema la
usa— falla en los **mismos 16 casos** de 6.100 (`row-degree hopdown2`). El primero:
`a@6, hijo@7, padre@6, owner@0`.

Y el diagnóstico es instructivo, porque el fallo **no es un defecto**: la regla del `up` da al hijo
la unión de los owners de sus padres, pero el **barrido agresivo** después le quita entradas que el
padre conserva —`aggPair` borra lo que no comparte paso a paso—. Así que la tabla del hijo es
**más pequeña, es decir más exacta**, que la unión de las de sus padres. La inclusión falla en la
dirección buena.

Lo que eso dice del camino: no hay que empujar owners **hacia abajo** desde los padres, porque el
barrido los poda; hay que construir la cadena **dentro** de la tabla del hijo, que es precisamente
lo que hace `Threaded`. -/
def HopDown (g : GPathM) (sel : Int → PathNodeId) : Prop :=
  ∀ k, 0 ≤ k → k + 1 < g.current_step → ∀ mk mk1, g.node? (sel k) = some mk →
    g.node? (sel (k + 1)) = some mk1 → ∀ w ∈ mk.owners, w.id.step < k → w ∈ mk1.owners

/-- **Y de un salto sale cualquier distancia, subiendo.** Inducción sobre la separación.

La implicación es cierta; su hipótesis **no** (véase `HopDown`). Se deja escrita porque delimita
exactamente qué haría falta, y porque la inducción sobre la separación es reutilizable con cualquier
regla local que sí valga. -/
theorem mem_owners_up (g : GPathM) (links : Bridge.LinksInOwners g) (sel : Int → PathNodeId)
    (hchain : IsChain g sel) (hhop : HopDown g sel) :
    ∀ (d : Nat) (i : Int), 0 ≤ i → i + (d : Int) + 1 < g.current_step →
      ∀ m, g.node? (sel (i + (d : Int) + 1)) = some m → sel i ∈ m.owners := by
  intro d
  induction d with
  | zero =>
    intro i hi0 hi1 m hm
    have harith : i + ((0 : Nat) : Int) + 1 = i + 1 := by push_cast; omega
    rw [harith] at hi1 hm
    have hlink := hchain.2 i hi0 hi1
    rw [hm] at hlink
    simp only [Option.map_some, Option.getD_some] at hlink
    exact (links _ m hm).1 _ hlink
  | succ n ih =>
    intro i hi0 hi1 m hm
    have harith : i + ((n + 1 : Nat) : Int) + 1 = (i + (n : Int) + 1) + 1 := by push_cast; omega
    rw [harith] at hi1 hm
    have hj1 : i + (n : Int) + 1 < g.current_step := by omega
    obtain ⟨mj, hmj⟩ := Option.isSome_iff_exists.mp (hchain.1 (i + (n : Int) + 1) (by omega) hj1).1
    have hprev := ih i hi0 hj1 mj hmj
    have hstepi := (hchain.1 i hi0 (by omega)).2
    exact hhop (i + (n : Int) + 1) (by omega) (by omega) mj m hmj hm (sel i) hprev
      (by rw [hstepi]; omega)

/-- **Y entonces la posesión a distancia sale de un solo salto.**

Hacia arriba por la inducción; hacia abajo por la simetría de tablas, que `AggOk` paga. -/
theorem distantOwned_of_hopDown (g : GPathM) (links : Bridge.LinksInOwners g)
    (hsym : Threaded.OwnSymmetric g) (sel : Int → PathNodeId) (hchain : IsChain g sel)
    (hhop : HopDown g sel) : DistantOwned g sel := by
  intro i j hi0 hj0 hi1 hj1 _ _ hij m hm
  by_cases h : i < j
  · obtain ⟨d, hd⟩ : ∃ d : Nat, j = i + (d : Int) + 1 := ⟨(j - i - 1).toNat, by omega⟩
    exact mem_owners_up g links sel hchain hhop d i hi0 (by rw [← hd]; exact hj1) m
      (by rw [← hd]; exact hm)
  · have hji : j < i := by omega
    obtain ⟨mi, hmi⟩ := Option.isSome_iff_exists.mp (hchain.1 i hi0 hi1).1
    obtain ⟨d, hd⟩ : ∃ d : Nat, i = j + (d : Int) + 1 := ⟨(i - j - 1).toNat, by omega⟩
    exact hsym (sel i) mi (sel j) m hmi hm
      (mem_owners_up g links sel hchain hhop d j hj0 (by rw [← hd]; exact hi1) mi
        (by rw [← hd]; exact hmi))

/-! ## El hueco: hasta `DistantOwned`, y el salto NO sirve

    readerVerdictW ⟸ PinAlive ≡ OwnerChained ⟸ TableChainOwned ⟸ DistantOwned   ⟸̸  HopDown

Y `HopDown` es una frase local, sobre **dos nodos contiguos de una cadena**:

> lo que `sel k` posee por debajo de `k`, lo posee también `sel (k+1)`.

Que es, dicho en el lenguaje del algoritmo, la regla del `up`: **los owners de un nodo nuevo son la
unión de los de sus padres** (intersecada con la tabla global). Un owner de un padre que siga vivo
está en la tabla del hijo por construcción.

**Y aquí hay que ser cuidadoso, porque es el mismo terreno donde `AncOwned` se rompió.** Aquel
enunciado pedía lo mismo para **todos los ancestros** y la medida lo negó en el 22,8 % de las
fusiones: tras un `doJoin` la relación *padre* sobreaproxima. Pero la medida también dijo dónde:
**los fallos nunca eran padres directos.** `HopDown` habla solo de padres directos y solo a lo largo
de una cadena, que es estrictamente menos que `AncOwned`.

Medida y **negada**: `row-degree hopdown` da 16 fallos de 484 celdas, y la versión restringida a los
tres nodos en la tabla de un mismo `a` falla en los mismos 16 de 6.100. Así que esta vía queda
cerrada, y la razón es la buena: **el barrido agresivo hace la tabla del hijo más exacta que la
unión de las de sus padres.**

La frontera sigue siendo `DistantOwned` —la posesión a distancia ≥ 2 dentro de la cadena que vive en
la tabla de un nodo—, y lo que esta medida descarta es alcanzarla empujando desde los padres. -/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.mem_owners_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_owners_up

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.distantOwned_of_hopDown' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms distantOwned_of_hopDown

-- ============================================================
-- `TableChainOwned` donde la tabla anfitriona no ofrece elección
-- ============================================================

/-- **Y ahí `AggOk` lo paga entero.**

Si la tabla del anfitrión `a` tiene **una sola** entrada en el paso `i`, entonces cualquier nodo de
esa tabla posee a la entrada de `i` — sin pedir nada más:

1. `sel j` está en la tabla de `a`, así que `AggOk` da `sharesEveryStep` entre las dos tablas;
2. `sel j` es válido, luego su tabla **tiene** una entrada en el paso `i`, y por tanto el cruce
   obliga a que **algún** owner de `a` en el paso `i` esté también en la de `sel j`;
3. y si en `i` solo hay uno, ese alguno **es** `sel i`.

Es el mismo mecanismo que `TablesSoundBuild.realizes_pin_of_singleId`, pero una planta más arriba:
allí la unicidad estaba en el paso del pin, aquí en el paso del par. Y cierra `TableChainOwned` en
todos los pasos donde la tabla anfitriona ya no elige. -/
theorem mem_owners_of_singleAt (g : GPathM) (hok : AggFixpoint.AggOk g) (ctx : Pinned.Ctx g)
    (a : PathNodeId) (na : PNodeM) (hna : g.node? a = some na)
    (ha0 : 0 ≤ a.id.step) (ha1 : a.id.step < g.current_step)
    (i : Int) (hi0 : 0 ≤ i) (hi1 : i < g.current_step)
    (u : PathNodeId) (_hu : u ∈ na.owners) (hus : u.id.step = i)
    (hsingle : ∀ v ∈ na.owners, v.id.step = i → v = u)
    (y : PathNodeId) (ny : PNodeM) (hny : g.node? y = some ny)
    (hy0 : 0 ≤ y.id.step) (hy1 : y.id.step < g.current_step)
    (hyn : y ∈ na.owners) : u ∈ ny.owners := by
  obtain ⟨_, hshare⟩ := hok a na y ny hna hny ha0 ha1 hy0 hy1 hyn
    (ctx.nodeval a na hna) (ctx.nodeval y ny hny)
  simp only [sharesEveryStep, List.all_eq_true] at hshare
  have hk := hshare i (mem_intRange hi0 (by omega))
  have hye : hasStepEntry ny.owners i = true := by
    have hok' := owners_ok_of_isValidNode g ny (ctx.nodeval y ny hny)
    simp only [List.all_eq_true] at hok'
    exact hok' i (mem_intRange hi0 (by omega))
  rw [hye] at hk
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at hk
  obtain ⟨z, hz, hzc⟩ := hk
  obtain ⟨hzn, hzs⟩ := List.mem_filter.mp hz
  rw [hsingle z hzn (eq_of_beq hzs)] at hzc
  exact List.mem_of_elem_eq_true hzc

/-- **Y la forma en que `TableChainOwned` lo consume.** -/
theorem tableChainOwned_of_singleSteps (g : GPathM) (hok : AggFixpoint.AggOk g)
    (ctx : Pinned.Ctx g) (hrange : ∀ p n, g.node? p = some n → 0 ≤ p.id.step ∧
      p.id.step < g.current_step)
    (hsingle : ∀ a na, g.node? a = some na → ∀ i, 0 ≤ i → i < g.current_step →
      ∀ u ∈ na.owners, u.id.step = i → ∀ v ∈ na.owners, v.id.step = i → v = u) :
    TableChainOwned g := by
  intro a na hna sel hchain hin i j hi0 hj0 hi1 hj1 _
  obtain ⟨hsi, hstepi⟩ := hchain.1 i hi0 hi1
  obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp (hchain.1 j hj0 hj1).1
  refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hstepi⟩
  simp only [ownersOf, hnj]
  exact mem_owners_of_singleAt g hok ctx a na hna (hrange a na hna).1 (hrange a na hna).2
    i hi0 hi1 (sel i) (hin i hi0 hi1) hstepi
    (fun v hv hvs => hsingle a na hna i hi0 hi1 (sel i) (hin i hi0 hi1) hstepi v hv hvs)
    (sel j) nj hnj (hrange _ nj hnj).1 (hrange _ nj hnj).2 (hin j hj0 hj1)

/-! ## Qué queda de `TableChainOwned`

Los pasos en los que la tabla del anfitrión **todavía ofrece dos valores**. En los demás
—`mem_owners_of_singleAt`— `AggOk` lo paga entero, y el mecanismo es el mismo que cerró el 90,4 % de
los pines en `realizes_pin_of_singleId`, una planta más arriba.

Y nótese lo que esto **no** pide: ni empujar owners desde los padres (medido falso), ni que la tabla
sea clique (medido falso), ni ternas. Pide que el cruce `sharesEveryStep` —el segundo test del
barrido del autor— tenga un único destino posible. -/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.mem_owners_of_singleAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_owners_of_singleAt

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.tableChainOwned_of_singleSteps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tableChainOwned_of_singleSteps

-- ============================================================
-- La ventana está determinada: de ids de mapa a `PathNodeId`
-- ============================================================

/-- **Si los ids de mapa están decididos hasta el paso `i`, los `PathNodeId` también.**

`mem_owners_of_singleAt` pide unicidad de **`PathNodeId`**, y lo que el lector fija al pinchar es el
**id de mapa**. La diferencia no es vacía: medido, el 1,1 % (`dos_de_tres`) y el 5,4 % (aleatorias)
de los pares tienen el mismo id de mapa y **ventana distinta**.

Pero la ventana no es libre. Un `PathNodeId` es `(id, parent_id, gparent_id)` y las dos últimas
coordenadas son ids de mapa de los dos pasos de abajo:

* `ParentId.PMP` — el `parent_id` que el identificador declara **es** el id de mapa de cada padre;
* `ParentId.GPMP` — y el `gparent_id` es el `parent_id` de cada padre.

Así que si en los pasos `i-1` e `i-2` ya no hay elección de id de mapa, la ventana de un nodo del
paso `i` queda determinada por su id. Y como el lector pincha **de abajo arriba**
(`ReaderExec.firstChoice` toma el paso más bajo con elección), eso es exactamente la situación en la
que trabaja.

La inducción va sobre el paso: en el 0 los dos son raíces y las dos coordenadas de ventana son
`none`; y arriba, los padres son iguales por la hipótesis de inducción, luego las ventanas
coinciden. -/
theorem path_eq_of_mapSingle (g : GPathM) (ctx : Pinned.Ctx g) (links : Bridge.LinksInOwners g) :
    ∀ (d : Nat),
      (∀ k, 0 ≤ k → k ≤ (d : Int) → ∀ p ∈ g.gowners, ∀ q ∈ g.gowners,
        p.id.step = k → q.id.step = k → p.id = q.id) →
      ∀ (u v : PathNodeId), u ∈ g.gowners → v ∈ g.gowners →
      u.id.step = (d : Int) → v.id.step = (d : Int) → (d : Int) < g.current_step → u = v := by
  intro d
  induction d with
  | zero =>
    intro hsingle u v hu hv hus hvs hcs
    have hmap := hsingle 0 (Int.le_refl 0) (by exact_mod_cast (Int.le_refl (0:Int))) u hu v hv
      (by exact_mod_cast hus) (by exact_mod_cast hvs)
    obtain ⟨nu, hnu⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g u).mp (ctx.gn u hu))
    obtain ⟨nv, hnv⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g v).mp (ctx.gn v hv))
    have hiu := node?_id_eq g u nu hnu
    have hiv := node?_id_eq g v nv hnv
    have hpu : u.parent_id = none := by
      rw [← hiu]; exact ctx.rootz nu (List.mem_of_find?_eq_some hnu) (by rw [hiu]; exact_mod_cast hus)
    have hpv : v.parent_id = none := by
      rw [← hiv]; exact ctx.rootz nv (List.mem_of_find?_eq_some hnv) (by rw [hiv]; exact_mod_cast hvs)
    have hgu : u.gparent_id = none := by
      rw [← hiu]; exact ctx.gpmp.2 nu (List.mem_of_find?_eq_some hnu) (by rw [hiu]; exact hpu)
    have hgv : v.gparent_id = none := by
      rw [← hiv]; exact ctx.gpmp.2 nv (List.mem_of_find?_eq_some hnv) (by rw [hiv]; exact hpv)
    cases u; cases v; simp_all
  | succ n ih =>
    intro hsingle u v hu hv hus hvs hcs
    have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by push_cast; omega
    rw [hcast] at hus hvs hcs
    have hsingle' : ∀ k, 0 ≤ k → k ≤ (n : Int) → ∀ p ∈ g.gowners, ∀ q ∈ g.gowners,
        p.id.step = k → q.id.step = k → p.id = q.id :=
      fun k hk0 hkn => hsingle k hk0 (by omega)
    have hmap := hsingle ((n : Int) + 1) (by omega) (by omega) u hu v hv hus hvs
    obtain ⟨nu, hnu⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g u).mp (ctx.gn u hu))
    obtain ⟨nv, hnv⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g v).mp (ctx.gn v hv))
    have hiu := node?_id_eq g u nu hnu
    have hiv := node?_id_eq g v nv hnv
    have hmu := List.mem_of_find?_eq_some hnu
    have hmv := List.mem_of_find?_eq_some hnv
    have hrootu : nu.id.parent_id.isNone = false := by
      cases hp : nu.id.parent_id with
      | none => exact absurd hp (ctx.shape.notroot nu hmu (by rw [hiu]; omega))
      | some _ => rfl
    have hrootv : nv.id.parent_id.isNone = false := by
      cases hp : nv.id.parent_id with
      | none => exact absurd hp (ctx.shape.notroot nv hmv (by rw [hiv]; omega))
      | some _ => rfl
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _
      (SelfOwn.have_parents_of_isValidNode g nu (ctx.nodeval u nu hnu) hrootu)
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _
      (SelfOwn.have_parents_of_isValidNode g nv (ctx.nodeval v nv hnv) hrootv)
    have hps : p.id.step = (n : Int) := by
      have := ctx.shape.pbelow nu hmu p hp
      rw [hiu, hus] at this; omega
    have hqs : q.id.step = (n : Int) := by
      have := ctx.shape.pbelow nv hmv q hq
      rw [hiv, hvs] at this; omega
    have hpg : p ∈ g.gowners :=
      ctx.ownGow u nu hnu p ((links u nu hnu).1 p hp) (by rw [hps]; omega) (by rw [hps]; omega)
    have hqg : q ∈ g.gowners :=
      ctx.ownGow v nv hnv q ((links v nv hnv).1 q hq) (by rw [hqs]; omega) (by rw [hqs]; omega)
    have hpq : p = q := ih hsingle' p q hpg hqg hps hqs (by omega)
    have hpu : u.parent_id = some p.id := by
      rw [← hiu]; exact (ctx.pmp nu hmu p hp).symm
    have hpv : v.parent_id = some q.id := by
      rw [← hiv]; exact (ctx.pmp nv hmv q hq).symm
    have hgu : u.gparent_id = p.parent_id := by rw [← hiu]; exact ctx.gpmp.1 nu hmu p hp
    have hgv : v.gparent_id = q.parent_id := by rw [← hiv]; exact ctx.gpmp.1 nv hmv q hq
    subst hpq
    cases u; cases v; simp_all

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.path_eq_of_mapSingle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms path_eq_of_mapSingle

-- ============================================================
-- El residuo vive en la zona SIN PINCHAR
-- ============================================================

/-- **Si la tabla global no elige en un paso, ninguna tabla de nodo elige ahí.**

Las tablas de los nodos están dentro de la tabla global (`Pinned.Ctx.ownGow`), así que la elección
que un nodo pueda tener en un paso es un subconjunto de la que tiene el estado. Un paso ya pinchado
no ofrece elección a nadie.

Es la observación que sitúa el residuo: **el 4,7 % / 11,9 % que queda vive enteramente en los pasos
que el lector todavía no ha fijado**, y esa zona encoge en cada pin. -/
theorem hostSingle_of_globalSingle (g : GPathM) (ctx : Pinned.Ctx g)
    (a : PathNodeId) (na : PNodeM) (hna : g.node? a = some na)
    (i : Int) (hi0 : 0 ≤ i) (hi1 : i < g.current_step)
    (hglob : ∀ p ∈ g.gowners, ∀ q ∈ g.gowners, p.id.step = i → q.id.step = i → p = q) :
    ∀ u ∈ na.owners, u.id.step = i → ∀ v ∈ na.owners, v.id.step = i → v = u := by
  intro u hu hus v hv hvs
  exact hglob v (ctx.ownGow a na hna v hv (by rw [hvs]; exact hi0) (by rw [hvs]; exact hi1))
    u (ctx.ownGow a na hna u hu (by rw [hus]; exact hi0) (by rw [hus]; exact hi1)) hvs hus

/-- **Y entonces, donde el estado ya no elige ids de mapa, `TableChainOwned` sale entero.**

Las tres piezas encadenadas:

1. unicidad de id de mapa en la tabla global ⟹ unicidad de `PathNodeId` (`path_eq_of_mapSingle`);
2. unicidad en la tabla global ⟹ unicidad en la tabla de cada nodo (`hostSingle_of_globalSingle`);
3. y ahí `AggOk` lo paga (`tableChainOwned_of_singleSteps`).

Éste es el **caso base** de la inducción que cerraría el resto: el lector pincha de abajo arriba y
cada pin quita un paso de la zona con elección, así que el residuo se consume. -/
theorem tableChainOwned_of_globalMapSingle (g : GPathM) (hok : AggFixpoint.AggOk g)
    (ctx : Pinned.Ctx g) (links : Bridge.LinksInOwners g)
    (hrange : ∀ p n, g.node? p = some n → 0 ≤ p.id.step ∧ p.id.step < g.current_step)
    (hmap : ∀ k, 0 ≤ k → k < g.current_step → ∀ p ∈ g.gowners, ∀ q ∈ g.gowners,
      p.id.step = k → q.id.step = k → p.id = q.id) :
    TableChainOwned g := by
  -- de ids de mapa a `PathNodeId`, paso a paso
  have hpath : ∀ k, 0 ≤ k → k < g.current_step → ∀ p ∈ g.gowners, ∀ q ∈ g.gowners,
      p.id.step = k → q.id.step = k → p = q := by
    intro k hk0 hk1 p hp q hq hps hqs
    have hcast : ((k.toNat : Nat) : Int) = k := by omega
    exact path_eq_of_mapSingle g ctx links k.toNat
      (fun j hj0 hjk => hmap j hj0 (by omega)) p q hp hq
      (by rw [hcast]; exact hps) (by rw [hcast]; exact hqs) (by rw [hcast]; exact hk1)
  refine tableChainOwned_of_singleSteps g hok ctx hrange (fun a na hna i hi0 hi1 => ?_)
  intro u hu hus v hv hvs
  exact hostSingle_of_globalSingle g ctx a na hna i hi0 hi1
    (fun p hp q hq hps hqs => hpath i hi0 hi1 p hp q hq hps hqs) u hu hus v hv hvs

/-! ## Lo que queda de la ruta 1

El caso base está cerrado. El paso de la inducción es:

> si el paso más bajo con elección es `k`, pinchar un id de mapa de `k` deja un estado con **una
> zona con elección estrictamente menor**, y las tablas de ese estado están dentro de las de éste,
> así que la posesión que allí se demuestre vale aquí.

Las dos mitades de ese paso son:

* **que el estado pinchado siga teniendo el nodo anfitrión y los dos nodos del par** — que es lo que
  `PinExact.PinExact` da, y que `ReaderChain.partner_survives_pin` ya usa;
* **que la medida decrezca** — que es `ReaderAgg.measure_lt_of_choiceAt`, ya demostrado y ya usado en
  `PinAliveChain.chained_of_pinAlive`.

O sea: la misma inducción que cerró `PinAlive`, ahora dentro de una tabla. -/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.hostSingle_of_globalSingle' does not depend on any axioms -/
#guard_msgs in
#print axioms hostSingle_of_globalSingle

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.tableChainOwned_of_globalMapSingle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tableChainOwned_of_globalMapSingle

-- ============================================================
-- Por debajo de la frontera de lectura, cerrado
-- ============================================================

/-- **Todo par cuyo extremo bajo esté en la zona ya pinchada está cerrado.**

No hace falta que el estado entero haya perdido la elección: basta que la haya perdido **por debajo
del paso del par**. Las tres piezas se encadenan solas:

* `path_eq_of_mapSingle` con la hipótesis acotada al prefijo —la ventana de un nodo del paso `i`
  queda determinada por los ids de mapa de los pasos `≤ i`, no por los de arriba—;
* `hostSingle_of_globalSingle` la baja de la tabla global a la del anfitrión;
* y `mem_owners_of_singleAt` la cobra con `AggOk`.

Y esto encaja con **cómo lee tu lector**: `ReaderExec.firstChoice` toma el paso **más bajo** con
elección, así que la zona pinchada es siempre un prefijo `0 … m-1` y crece de uno en uno. Cada pin
cierra un paso más de pares.

Nótese además dónde se necesita `OwnerChained`: `ReaderChain.pinReachable_of_ownerChained` la usa
**solo en el paso del pin**, que es justo el paso más bajo con elección. Es decir, el pin que el
lector está a punto de hacer siempre está en la frontera, con todo lo de abajo ya fijado. -/
theorem mem_owners_of_pinnedPrefix (g : GPathM) (hok : AggFixpoint.AggOk g) (ctx : Pinned.Ctx g)
    (links : Bridge.LinksInOwners g) (m : Int)
    (hpref : ∀ k, 0 ≤ k → k < m → ∀ p ∈ g.gowners, ∀ q ∈ g.gowners,
      p.id.step = k → q.id.step = k → p.id = q.id)
    (a : PathNodeId) (na : PNodeM) (hna : g.node? a = some na)
    (ha0 : 0 ≤ a.id.step) (ha1 : a.id.step < g.current_step)
    (i : Int) (hi0 : 0 ≤ i) (him : i < m) (hi1 : i < g.current_step)
    (u : PathNodeId) (hu : u ∈ na.owners) (hus : u.id.step = i)
    (y : PathNodeId) (ny : PNodeM) (hny : g.node? y = some ny)
    (hy0 : 0 ≤ y.id.step) (hy1 : y.id.step < g.current_step)
    (hyn : y ∈ na.owners) : u ∈ ny.owners := by
  have hcast : ((i.toNat : Nat) : Int) = i := by omega
  have hpath : ∀ p ∈ g.gowners, ∀ q ∈ g.gowners, p.id.step = i → q.id.step = i → p = q := by
    intro p hp q hq hps hqs
    exact path_eq_of_mapSingle g ctx links i.toNat
      (fun j hj0 hji => hpref j hj0 (by rw [hcast] at hji; omega)) p q hp hq
      (by rw [hcast]; exact hps) (by rw [hcast]; exact hqs) (by rw [hcast]; exact hi1)
  exact mem_owners_of_singleAt g hok ctx a na hna ha0 ha1 i hi0 hi1 u hu hus
    (fun v hv hvs => hostSingle_of_globalSingle g ctx a na hna i hi0 hi1 hpath u hu hus v hv hvs)
    y ny hny hy0 hy1 hyn

/-! ## El hueco, ya solo por encima de la frontera

Lo que queda de `TableChainOwned` es:

> los pares de la cadena cuyo extremo bajo está **por encima** del paso más bajo con elección.

Y hay dos cosas que conviene anotar de ese enunciado:

* **la mitad de abajo ya no vuelve a aparecer**: un paso, una vez pinchado, se queda pinchado
  (`TablesSoundBuild.singleIdAt_of_pruned`), así que la frontera solo sube y el residuo solo
  encoge;
* **y el lector solo necesita `OwnerChained` en la frontera**, no en todo el estado
  (`pinReachable_of_ownerChained` la usa solo en el paso del pin). Así que lo que falta no es la
  posesión entre pares arbitrarios de la tabla: es la posesión entre el nodo de la frontera y los
  de arriba.

Medido, ese residuo es el 4,7 % (`dos_de_tres`) y el 11,9 % (aleatorias) de los pares. -/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.mem_owners_of_pinnedPrefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_owners_of_pinnedPrefix

-- ============================================================
-- La frase del autor, escrita: la posesión hacia arriba
-- ============================================================

/-- **«La posesión entre el nodo de la frontera y los de arriba está garantizada por el review
agresivo.»**

Escrita sobre la cadena que vive dentro de la tabla de un nodo: si `sel` es la cadena y `i < j`,
entonces el nodo de abajo está en la tabla del de arriba. -/
def OwnedFromAbove (g : GPathM) : Prop :=
  ∀ a na, g.node? a = some na → ∀ sel, IsChain g sel →
    (∀ k, 0 ≤ k → k < g.current_step → sel k ∈ na.owners) →
    ∀ i j, 0 ≤ i → i < j → j < g.current_step →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners

/-- **Y con ella, `TableChainOwned` entero.** La dirección de bajada la devuelve la simetría de
tablas, que `AggOk` paga (`ownSymmetric_of_reviewed`). -/
theorem tableChainOwned_of_ownedFromAbove (g : GPathM) (hsym : Threaded.OwnSymmetric g)
    (h : OwnedFromAbove g) : TableChainOwned g := by
  intro a na hna sel hchain hin i j hi0 hj0 hi1 hj1 hij
  obtain ⟨hsi, hstepi⟩ := hchain.1 i hi0 hi1
  obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp (hchain.1 j hj0 hj1).1
  refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hstepi⟩
  simp only [ownersOf, hnj]
  by_cases hlt : i < j
  · exact h a na hna sel hchain hin i j hi0 hlt hj1 nj hnj
  · obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp hsi
    exact hsym (sel i) ni (sel j) nj hni hnj
      (h a na hna sel hchain hin j i hj0 (by omega) hi1 ni hni)

/-- **Y el teorema entero desde tu frase.**

    OwnedFromAbove  →  OwnerChained  →  PinAlive  →  (readerVerdictW φ = true ↔ Satisfiable φ)

Todo lo demás de la escalera está cerrado. -/
theorem ownerChained_of_ownedFromAbove (g : GPathM)
    (adj : AdjacentOwners.Adj g) (hsmp : Sons.SMP g) (hpos : 0 < g.current_step)
    (ctx : Threaded.TCtx g) (hsym : Threaded.OwnSymmetric g) (hoos : SelfOwn.OOS g)
    (hgn : GownersNodes.GN g) (h : OwnedFromAbove g) : ReaderChain.OwnerChained g :=
  ownerChained_of_tableChainOwned g adj hsmp hpos ctx hsym hoos hgn
    (tableChainOwned_of_ownedFromAbove g hsym h)

/-! ## Qué he podido y qué no de esa frase

**Lo que sí.** La he escrito, y con ella cae todo: `TableChainOwned`, `OwnerChained`, `PinAlive` y el
veredicto. También su dirección de bajada, que sale sola de la simetría de tablas — y **la simetría
sí la paga el barrido**: es la primera componente de `AggFixpoint.AggOk`
(`ownSymmetric_of_reviewed`, cierre `[propext]`).

**Lo que no, todavía.** No he conseguido derivarla de `AggOk`, y conviene decir exactamente dónde se
me para el argumento, porque puede que sea solo que me falta una pieza:

* la segunda componente de `AggOk` es `sharesEveryStep na.owners nj.owners`: al paso `i` las dos
  tablas comparten **alguna** entrada. Eso da un `z ∈ ownersAt na.owners i` con `z ∈ nj.owners`;
* para concluir hace falta `z = sel i`, y eso lo da la unicidad —`mem_owners_of_singleAt`—, que es
  justo lo que falla en el 4,7 % / 11,9 % de los pares;
* la ruta alternativa, empujar la posesión desde los padres (`PinAliveChain.HopDown`), está **medida
  falsa**: el barrido hace la tabla del hijo más exacta que la unión de las de sus padres.

Así que lo que le falta al argumento es cerrar el hueco entre «comparten alguna entrada» y
«comparten **esa** entrada». Si el barrido lo garantiza, tiene que ser por algo que `aggPair` hace y
que yo no he sabido leer todavía: sus dos tests son la simetría y el cruce, y el cruce es existencial.

**Y la medida está de tu lado**: la cadena de la tabla, construida por descenso de padres, sale
poseída por pares en **194.850 de 194.850 pares** (`row-degree tablechain`), y la tabla **no** es
clique (7,9 % de pares cualesquiera fallan), así que lo que se cumple es precisamente el enunciado
restringido a la cadena, no una propiedad gratuita de las tablas. -/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.tableChainOwned_of_ownedFromAbove' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tableChainOwned_of_ownedFromAbove

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.ownerChained_of_ownedFromAbove' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownerChained_of_ownedFromAbove

-- ============================================================
-- Y la forma correcta del enunciado: EXISTENCIAL
-- ============================================================

/-! **Corrección del autor (y tenía razón): el review garantiza que dos tablas comparten *algún*
camino, no uno concreto.** `sharesEveryStep` es existencial.

Eso cambia el enunciado que hay que perseguir, y lo **debilita**. `TableChainOwned` pedía que
**toda** cadena de la tabla estuviera poseída por pares — demasiado, y además no es lo que hace
falta: `OwnerChained` solo necesita **una** cadena por el nodo. Así que el enunciado correcto es
existencial de los dos lados. -/

/-- **Existe una cadena poseída por pares dentro de la tabla de cada nodo, y pasa por él.**

Ni «toda cadena», ni «la que construye `Threaded`»: **alguna**. Es la forma que encaja con lo que el
barrido garantiza, y es estrictamente más débil que `TableChainOwned`. -/
def TableHasOwnedChain (g : GPathM) : Prop :=
  ∀ a na, g.node? a = some na → 0 ≤ a.id.step → a.id.step < g.current_step →
    ∃ sel, IsChain g sel ∧ PairwiseOwned g sel ∧ sel a.id.step = a ∧
      ∀ k, 0 ≤ k → k < g.current_step → sel k ∈ na.owners

/-- **Y basta, con muchas menos hipótesis que la versión universal.**

No hace hace falta `Threaded`, ni `OwnSymmetric`, ni `OOS`: la cadena viene dada, y
`SupportedRun.chainSound_of_chain` la eleva. Compárese con
`ownerChained_of_tableChainOwned`, que necesitaba las tres para **construirla**. -/
theorem ownerChained_of_tableHasOwnedChain (g : GPathM)
    (adj : AdjacentOwners.Adj g) (hsmp : Sons.SMP g) (hpos : 0 < g.current_step)
    (hgn : GownersNodes.GN g) (h : TableHasOwnedChain g) : ReaderChain.OwnerChained g := by
  intro q hq h0 h1
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g q).mp (hgn q hq))
  obtain ⟨sel, hchain, howned, hsq, _⟩ := h q n hn h0 h1
  exact ⟨sel, SupportedRun.chainSound_of_chain g adj hsmp hpos sel hchain howned, by rw [hsq]⟩

/-- **Y la versión universal la implica**, vía `Threaded`: la cadena existe y `TableChainOwned` la
hace poseída por pares. Se deja para dejar constancia de que el enunciado nuevo es **más débil**. -/
theorem tableHasOwnedChain_of_tableChainOwned (g : GPathM) (ctx : Threaded.TCtx g)
    (hsym : Threaded.OwnSymmetric g) (hoos : SelfOwn.OOS g) (h : TableChainOwned g) :
    TableHasOwnedChain g := by
  intro a na hna ha0 ha1
  have hself := FabricAdd.self_mem_owners g hoos a na hna (ctx.nodeval a na hna) ha0 ha1
  obtain ⟨sel, hchain, hsa, hin⟩ :=
    Threaded.chain_through_of_symmetric g ctx hsym hoos a na hna hself ha0 ha1
  exact ⟨sel, hchain, h a na hna sel hchain hin, hsa, hin⟩

/-! ## Y entonces lo que falta es una CONSTRUCCIÓN, no una propiedad

Con el enunciado existencial, el trabajo cambia de naturaleza: no hay que demostrar que una cadena
dada cumple algo, hay que **elegirla**. Y el material para elegirla es justo lo que el barrido da:

* `AggOk` asegura que la tabla de `a` y la de cualquier `w ∈ na.owners` **comparten una entrada en
  cada paso**;
* así que se puede descender manteniendo el invariante «lo construido está poseído por pares»,
  eligiendo en cada paso una entrada compartida por todos los ya elegidos.

La obligación de ese descenso es una sola, y está abajo. Y es exactamente lo que la sonda
`row-degree pairdesc`, columna «como lo hace el lector» —pinchar y **revisar** en cada paso— mide al
**100 %**: 1.016/1.016 en `dos_de_tres.cnf` y 12.602/12.602 en el corpus aleatorio, sin un solo
retroceso.

Y también corrige lo que yo había dicho de la sonda `tablechain`: mide **una** cadena, la del
descenso ávido por padres, y sale poseída por pares en 194.850/194.850 pares. Eso es evidencia del
enunciado **existencial**, no del universal. -/

/-- **La única obligación del descenso, en su forma existencial.**

Dado lo ya elegido por encima del paso `k` —una cadena parcial dentro de la tabla de `a`, poseída por
pares—, hay una entrada de la tabla de `a` en el paso `k` que es **padre** de la de `k+1` y está
**poseída por todas** las de arriba.

Un solo paso. El resto es la recursión, y `AggOk` da el material en cada paso.

**Corrección (v179): lo de arriba es una CADENA.** La primera redacción —`DescentStepAny`, abajo—
no pedía que `sel` fuera cadena por encima de `k`, y así es **falsa** en cuanto hay un nodo en el
paso 2 (`not_descentStepAny`). La recursión (`step_down_O`) siempre la tiene, así que añadirla no
cuesta nada. -/
def DescentStepOwned (g : GPathM) : Prop :=
  ∀ a na, g.node? a = some na → ∀ (k : Int) (sel : Int → PathNodeId), 0 ≤ k →
    k + 1 < g.current_step →
    Extendable.PartialChain g sel (k + 1) (g.current_step - 1) →
    (∀ j, k < j → j < g.current_step → sel j ∈ na.owners) →
    (∀ i j, k < i → k < j → i < g.current_step → j < g.current_step → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners) →
    ∃ u ∈ na.owners, u.id.step = k ∧
      (∀ nk1, g.node? (sel (k + 1)) = some nk1 → u ∈ nk1.parents) ∧
      (∀ j, k < j → j < g.current_step → ∀ nj, g.node? (sel j) = some nj → u ∈ nj.owners)

/-- **La primera redacción, sin la cadena. MEDIDO — DEMOSTRADO — FALSO.** -/
def DescentStepAny (g : GPathM) : Prop :=
  ∀ a na, g.node? a = some na → ∀ (k : Int) (sel : Int → PathNodeId), 0 ≤ k →
    k + 1 < g.current_step →
    (∀ j, k < j → j < g.current_step → sel j ∈ na.owners) →
    (∀ i j, k < i → k < j → i < g.current_step → j < g.current_step → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners) →
    ∃ u ∈ na.owners, u.id.step = k ∧
      (∀ nk1, g.node? (sel (k + 1)) = some nk1 → u ∈ nk1.parents) ∧
      (∀ j, k < j → j < g.current_step → ∀ nj, g.node? (sel j) = some nj → u ∈ nj.owners)

/-- **Y por qué es falsa: `sel` constante en `a`.** Un nodo se posee a sí mismo, así que la lista
constante cumple las dos hipótesis; la conclusión con `k = 0` pide un padre de `a` en el paso 0, y
los padres de `a` viven en `a.id.step - 1 ≥ 1`. -/
theorem not_descentStepAny (g : GPathM) (ctx : Threaded.TCtx g) (hoos : SelfOwn.OOS g)
    (a : PathNodeId) (na : PNodeM) (hna : g.node? a = some na)
    (ha2 : 2 ≤ a.id.step) (ha1 : a.id.step < g.current_step) : ¬ DescentStepAny g := by
  intro hds
  have hself := FabricAdd.self_mem_owners g hoos a na hna (ctx.nodeval a na hna) (by omega) ha1
  obtain ⟨u, _, hus, hpar, _⟩ := hds a na hna 0 (fun _ => a) (Int.le_refl 0) (by omega)
    (fun _ _ _ => hself)
    (fun _ _ _ _ _ _ _ nj hnj => by rw [← Option.some.inj (hna.symm.trans hnj)]; exact hself)
  have hup := hpar na hna
  have hstep := ctx.shape.pbelow na (List.mem_of_find?_eq_some hna) u hup
  rw [node?_id_eq g a na hna] at hstep
  omega

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.not_descentStepAny' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_descentStepAny

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.ownerChained_of_tableHasOwnedChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownerChained_of_tableHasOwnedChain

/--
info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.tableHasOwnedChain_of_tableChainOwned' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms tableHasOwnedChain_of_tableChainOwned

-- ============================================================
-- La recursión del descenso, hecha
-- ============================================================

open AbsSat.GraphPath.Model.Extendable (PartialChain PartialOwned upd upd_self upd_other
  isChain_of_partial pairwiseOwned_of_partial)

/-- **Lo construido hasta el paso `lo`**: una cadena parcial dentro de la tabla de `a`, poseída por
pares. Es el invariante del descenso. -/
structure OPart (g : GPathM) (na : PNodeM) (sel : Int → PathNodeId) (lo : Int) : Prop where
  chain : PartialChain g sel lo (g.current_step - 1)
  inTable : ∀ i, lo ≤ i → i ≤ g.current_step - 1 → sel i ∈ na.owners
  owned : PartialOwned g sel lo (g.current_step - 1)

/-- **Un paso del descenso**, con la obligación del autor como única entrada. -/
theorem step_down_O (g : GPathM) (ctx : Threaded.TCtx g) (hsym : Threaded.OwnSymmetric g)
    (hds : DescentStepOwned g) (a : PathNodeId) (na : PNodeM) (hna : g.node? a = some na)
    (sel : Int → PathNodeId) (lo : Int) (hpos : 0 < lo) (hhi : lo ≤ g.current_step - 1)
    (hp : OPart g na sel lo) : ∃ c, OPart g na (upd sel (lo - 1) c) (lo - 1) := by
  obtain ⟨u, hun, hus, hupar, huown⟩ := hds a na hna (lo - 1) sel (by omega) (by omega)
    (by rw [show lo - 1 + 1 = lo from by omega]; exact hp.chain)
    (fun j hj1 hj2 => hp.inTable j (by omega) (by omega))
    (fun i j hi1 hj1 hi2 hj2 hij nj hnj => by
      have := hp.owned i j (by omega) (by omega) (by omega) (by omega) hij
      simp only [ownersAt, List.mem_filter, ownersOf, hnj] at this
      exact this.1)
  obtain ⟨nu, hnu⟩ := Option.isSome_iff_exists.mp
    (ctx.ownerNode a na hna u hun (by rw [hus]; omega) (by rw [hus]; omega))
  refine ⟨u, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i hi1 hi2
      rcases int_eq_or_ne i (lo - 1) with he | he
      · subst he; rw [upd_self]; exact ⟨by rw [hnu]; rfl, hus⟩
      · rw [upd_other sel (lo - 1) u he]; exact hp.chain.1 i (by omega) hi2
    · intro i hi1 hi2
      rcases int_eq_or_ne i (lo - 1) with he | he
      · subst he
        rw [upd_self, upd_other sel (lo - 1) u (by omega),
          show lo - 1 + 1 = lo from by omega]
        obtain ⟨hsome, _⟩ := hp.chain.1 lo (Int.le_refl _) hhi
        obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp hsome
        rw [hnl]
        simp only [Option.map_some, Option.getD_some]
        exact hupar nl (by rw [show lo - 1 + 1 = lo from by omega]; exact hnl)
      · rw [upd_other sel (lo - 1) u he,
          upd_other sel (lo - 1) u (by omega)]
        exact hp.chain.2 i (by omega) hi2
  · intro i hi1 hi2
    rcases int_eq_or_ne i (lo - 1) with he | he
    · subst he; rw [upd_self]; exact hun
    · rw [upd_other sel (lo - 1) u he]; exact hp.inTable i (by omega) hi2
  · intro i j hi1 hj1 hi2 hj2 hij
    rcases int_eq_or_ne i (lo - 1) with hei | hei
    · subst hei
      rw [upd_self, upd_other sel (lo - 1) u (fun h => hij h.symm)]
      obtain ⟨hsome, hstep⟩ := hp.chain.1 j (by omega) hj2
      obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp hsome
      refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hus⟩
      simp only [ownersOf, hnj]
      exact huown j (by omega) (by omega) nj hnj
    · rcases int_eq_or_ne j (lo - 1) with hej | hej
      · subst hej
        rw [upd_self, upd_other sel (lo - 1) u hei]
        obtain ⟨hsome, hstep⟩ := hp.chain.1 i (by omega) hi2
        obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp hsome
        refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hstep⟩
        simp only [ownersOf, hnu]
        exact hsym (sel i) ni u nu hni hnu (huown i (by omega) (by omega) ni hni)
      · rw [upd_other sel (lo - 1) u hei, upd_other sel (lo - 1) u hej]
        exact hp.owned i j (by omega) (by omega) hi2 hj2 hij

/-- **Y el descenso entero**, por recursión sobre el paso. -/
theorem descend_O (g : GPathM) (ctx : Threaded.TCtx g) (hsym : Threaded.OwnSymmetric g)
    (hds : DescentStepOwned g) (a : PathNodeId) (na : PNodeM) (hna : g.node? a = some na) :
    ∀ (fuel : Nat) (sel : Int → PathNodeId) (lo : Int), lo.toNat ≤ fuel → 0 ≤ lo →
      lo ≤ g.current_step - 1 → OPart g na sel lo → ∃ sel', OPart g na sel' 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro sel lo hm hlo _ hp
    have : lo = 0 := by omega
    subst this; exact ⟨sel, hp⟩
  | succ fuel ih =>
    intro sel lo hm hlo hhi hp
    if hpos : 0 < lo then
      obtain ⟨c, hp'⟩ := step_down_O g ctx hsym hds a na hna sel lo hpos hhi hp
      exact ih _ (lo - 1) (by omega) (by omega) (by omega) hp'
    else
      have : lo = 0 := by omega
      subst this; exact ⟨sel, hp⟩

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.step_down_O' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_down_O

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.descend_O' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms descend_O

/-- **Y con la semilla, `TableHasOwnedChain` entero desde la obligación de un paso.**

La semilla es un owner de `a` en el paso de arriba —`isValidNode` lo da— y el descenso lo baja al
paso 0 manteniendo la posesión por pares. Al final, `isChain_of_partial` y
`pairwiseOwned_of_partial` convierten el tramo completo en una cadena de verdad, y `OOS` dice que en
el paso de `a` la cadena elige `a`.

Así que la escalera entera queda:

    DescentStepOwned  →  TableHasOwnedChain  →  OwnerChained  →  PinAlive  →  el veredicto -/
theorem tableHasOwnedChain_of_descentStep (g : GPathM) (ctx : Threaded.TCtx g)
    (hsym : Threaded.OwnSymmetric g) (hoos : SelfOwn.OOS g) (hpos : 0 < g.current_step)
    (hds : DescentStepOwned g) : TableHasOwnedChain g := by
  intro a na hna ha0 ha1
  have hok := owners_ok_of_isValidNode g na (ctx.nodeval a na hna)
  simp only [List.all_eq_true] at hok
  obtain ⟨t, ht, hts⟩ := List.any_eq_true.mp
    (hok (g.current_step - 1) (mem_intRange (by omega) (by omega)))
  have htstep : t.id.step = g.current_step - 1 := eq_of_beq hts
  obtain ⟨nt, hnt⟩ := Option.isSome_iff_exists.mp
    (ctx.ownerNode a na hna t ht (by rw [htstep]; omega) (by rw [htstep]; omega))
  have hseed : OPart g na (fun _ => t) (g.current_step - 1) := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro i hi1 hi2
      have hie : i = g.current_step - 1 := by omega
      subst hie
      exact ⟨by rw [hnt]; rfl, htstep⟩
    · intro i hi1 hi2; exfalso; omega
    · intro i _ _; exact ht
    · intro i j hi1 hj1 hi2 hj2 hij; exfalso; omega
  obtain ⟨sel, hp⟩ := descend_O g ctx hsym hds a na hna (g.current_step - 1).toNat
    (fun _ => t) (g.current_step - 1) (Nat.le_refl _) (by omega) (by omega) hseed
  refine ⟨sel, isChain_of_partial g sel hp.chain, pairwiseOwned_of_partial g sel hp.owned, ?_,
    fun k hk0 hk1 => hp.inTable k hk0 (by omega)⟩
  have hmem := hp.inTable a.id.step ha0 (by omega)
  obtain ⟨_, hstep⟩ := hp.chain.1 a.id.step ha0 (by omega)
  have hid : na.id = a := node?_id_eq g a na hna
  have heq := hoos na (List.mem_of_find?_eq_some hna) (sel a.id.step) hmem
    (by rw [hstep, hid])
  rw [heq, hid]

/-- **Y de ahí, la frase del autor cierra el teorema.** -/
theorem ownerChained_of_descentStep (g : GPathM)
    (adj : AdjacentOwners.Adj g) (hsmp : Sons.SMP g) (hpos : 0 < g.current_step)
    (ctx : Threaded.TCtx g) (hsym : Threaded.OwnSymmetric g) (hoos : SelfOwn.OOS g)
    (hgn : GownersNodes.GN g) (hds : DescentStepOwned g) : ReaderChain.OwnerChained g :=
  ownerChained_of_tableHasOwnedChain g adj hsmp hpos hgn
    (tableHasOwnedChain_of_descentStep g ctx hsym hoos hpos hds)

/-! ## El hueco, en un paso de descenso

    readerVerdictW ⟸ PinAlive ≡ OwnerChained ⟸ TableHasOwnedChain ⟸ DescentStepOwned

Y `DescentStepOwned` es una frase sobre **un paso**:

> dado lo ya elegido por encima de `k` dentro de la tabla de `a`, hay una entrada de esa tabla en el
> paso `k` que es **padre** de la de `k+1` y está **poseída por todas** las de arriba.

Todo lo demás está cerrado: la recursión (`descend_O`), la semilla, el paso a `ChainSound`, la
escalera del lector, los cinco bucles del review, los filtros de envío y el pin del lector.

Medido: `row-degree pairdesc`, columna «como lo hace el lector» —pinchar y **revisar** en cada
paso—, **1.016/1.016** pares en `dos_de_tres.cnf` y **12.602/12.602** en el corpus aleatorio, **sin
un solo retroceso**. Y `row-degree tablechain`, que construye ese descenso hasta el final:
**194.850/194.850** pares poseídos, y el descenso **no se atasca nunca**. -/

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.tableHasOwnedChain_of_descentStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tableHasOwnedChain_of_descentStep

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.ownerChained_of_descentStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownerChained_of_descentStep

-- ============================================================
-- El paso `k` no elige id de mapa: lo fija el hijo
-- ============================================================

/-- **Toda tabla que posee a `b` le comparte un PADRE en el paso de abajo.**

`AggOk` da el cruce `sharesEveryStep` entre la tabla de `x` y la de `b`; la tabla de `b` tiene
entrada en el paso de abajo (es válido), así que alguna entrada de `x` en ese paso está en la de
`b`, y en el paso de abajo **los owners de `b` son sus padres** (`owners_below_iff_parents`). -/
theorem shared_parent (g : GPathM) (hok : AggFixpoint.AggOk g) (adj : AdjacentOwners.Adj g)
    (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < g.current_step)
    (b : PathNodeId) (nb : PNodeM) (hb : g.node? b = some nb)
    (hb1 : 1 ≤ b.id.step) (hbc : b.id.step < g.current_step) (hbx : b ∈ nx.owners) :
    ∃ r ∈ nx.owners, r.id.step = b.id.step - 1 ∧ r ∈ nb.parents := by
  obtain ⟨_, hshare⟩ := hok x nx b nb hx hb hx0 hx1 (by omega) hbc hbx
    (adj.ctx.nodeval x nx hx) (adj.ctx.nodeval b nb hb)
  simp only [sharesEveryStep, List.all_eq_true] at hshare
  have hk := hshare (b.id.step - 1) (mem_intRange (by omega) (by omega))
  have hbe : hasStepEntry nb.owners (b.id.step - 1) = true := by
    have hok' := owners_ok_of_isValidNode g nb (adj.ctx.nodeval b nb hb)
    simp only [List.all_eq_true] at hok'
    exact hok' _ (mem_intRange (by omega) (by omega))
  rw [hbe] at hk
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at hk
  obtain ⟨r, hr, hrc⟩ := hk
  obtain ⟨hrn, hrs⟩ := List.mem_filter.mp hr
  have hrs' : r.id.step = b.id.step - 1 := eq_of_beq hrs
  exact ⟨r, hrn, hrs',
    (AdjacentOwners.owners_below_iff_parents g adj b nb hb hb1 r hrs').mp
      (List.mem_of_elem_eq_true hrc)⟩

/-- **Los padres de un nodo llevan todos el mismo id de mapa y el mismo `parent_id`.**

`PMP`: el id del padre es el `parent_id` del hijo; `GPMP`: el `parent_id` del padre es el
`gparent_id` del hijo. Así que dos padres solo pueden diferir en `gparent_id` — el id de mapa del
paso `k - 2`. -/
theorem parents_same_window (g : GPathM) (ctx : Pinned.Ctx g)
    (b : PathNodeId) (nb : PNodeM) (hb : g.node? b = some nb)
    (p q : PathNodeId) (hp : p ∈ nb.parents) (hq : q ∈ nb.parents) :
    p.id = q.id ∧ p.parent_id = q.parent_id := by
  have hm := List.mem_of_find?_eq_some hb
  have h1 := ctx.pmp nb hm p hp
  have h2 := ctx.pmp nb hm q hq
  have h3 := ctx.gpmp.1 nb hm p hp
  have h4 := ctx.gpmp.1 nb hm q hq
  exact ⟨Option.some.inj (h1.trans h2.symm), h3.symm.trans h4⟩

/-- **El paso del descenso, cuando el hijo tiene un solo padre.**

No pide nada de la tabla de `a` en el paso `k`: **ni una sola entrada, ni un solo id de mapa**. El
padre de `b = sel (k+1)` que comparte la tabla de `a` (`shared_parent`) sirve para todos los de
arriba, porque cada uno de ellos comparte con `b` un padre (`shared_parent` otra vez) y `b` no tiene
otro.

Y por `parents_same_window` la hipótesis es solo sobre la **ventana**: los padres de `b` ya
coinciden en id de mapa y en `parent_id`. El caso «la tabla de `a` ofrece dos ids de mapa en `k`» no
es una elección del descenso — el hijo ya la hizo. -/
theorem descentStep_of_parentSingle (g : GPathM) (hok : AggFixpoint.AggOk g)
    (adj : AdjacentOwners.Adj g) (a : PathNodeId) (na : PNodeM) (hna : g.node? a = some na)
    (ha0 : 0 ≤ a.id.step) (ha1 : a.id.step < g.current_step)
    (k : Int) (sel : Int → PathNodeId) (hk0 : 0 ≤ k) (hk1 : k + 1 < g.current_step)
    (hch : Extendable.PartialChain g sel (k + 1) (g.current_step - 1))
    (hin : ∀ j, k < j → j < g.current_step → sel j ∈ na.owners)
    (hown : ∀ i j, k < i → k < j → i < g.current_step → j < g.current_step → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners)
    (hsingle : ∀ nb, g.node? (sel (k + 1)) = some nb →
      ∀ p ∈ nb.parents, ∀ q ∈ nb.parents, p = q) :
    ∃ u ∈ na.owners, u.id.step = k ∧
      (∀ nk1, g.node? (sel (k + 1)) = some nk1 → u ∈ nk1.parents) ∧
      (∀ j, k < j → j < g.current_step → ∀ nj, g.node? (sel j) = some nj → u ∈ nj.owners) := by
  obtain ⟨hbsome, hbs⟩ := hch.1 (k + 1) (Int.le_refl _) (by omega)
  obtain ⟨nb, hnb⟩ := Option.isSome_iff_exists.mp hbsome
  obtain ⟨u, hun, hus, hup⟩ := shared_parent g hok adj a na hna ha0 ha1 (sel (k + 1)) nb hnb
    (by omega) (by omega) (hin (k + 1) (by omega) (by omega))
  refine ⟨u, hun, by rw [hus, hbs]; omega, fun nk1 hk => ?_, fun j hj1 hj2 nj hnj => ?_⟩
  · rw [← Option.some.inj (hnb.symm.trans hk)]; exact hup
  · rcases int_eq_or_ne j (k + 1) with he | he
    · subst he
      rw [← Option.some.inj (hnb.symm.trans hnj)]
      exact (adj.links _ nb hnb).1 u hup
    · obtain ⟨_, hjs⟩ := hch.1 j (by omega) (by omega)
      obtain ⟨r, hrn, _, hrp⟩ := shared_parent g hok adj (sel j) nj hnj (by omega) (by omega)
        (sel (k + 1)) nb hnb (by omega) (by omega)
        (hown (k + 1) j (by omega) hj1 (by omega) hj2 (fun h => he h.symm) nj hnj)
      rw [hsingle nb hnb u hup r hrp]; exact hrn

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.shared_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms shared_parent

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.parents_same_window' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parents_same_window

/-- info: 'AbsSat.GraphPath.Model.OwnerChainedBuild.descentStep_of_parentSingle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms descentStep_of_parentSingle

end AbsSat.GraphPath.Model.OwnerChainedBuild
