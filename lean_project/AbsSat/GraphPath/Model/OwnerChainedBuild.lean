-- lean_project/AbsSat/GraphPath/Model/OwnerChainedBuild.lean
import AbsSat.GraphPath.Model.ReaderChain
import AbsSat.GraphPath.Model.TablesSoundBuild

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

end AbsSat.GraphPath.Model.OwnerChainedBuild
