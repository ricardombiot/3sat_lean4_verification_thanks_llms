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

Esto le pone nombre. -/
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

end AbsSat.GraphPath.Model.OwnerChainedBuild
