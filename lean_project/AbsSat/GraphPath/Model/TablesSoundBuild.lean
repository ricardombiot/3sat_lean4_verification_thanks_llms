-- lean_project/AbsSat/GraphPath/Model/TablesSoundBuild.lean
import AbsSat.GraphPath.Model.AddNode
import AbsSat.GraphPath.Model.JoinSound
import AbsSat.GraphPath.Model.DescentUp
import AbsSat.GraphPath.Model.RunInhabited
import AbsSat.GraphPath.Model.FabricAdd

/-!
# `TablesSound` por la construcción de la máquina

`ReaderChain.ownTable_of_tablesSound` deja el dato que ordena el ataque: **la única garantía de
conservación que la criba ofrece es «estar en una cadena»**, así que ninguna reformulación de
`TablesSound` en términos del punto fijo escapa de `TablesSound`. La prueba tiene que venir de la
**construcción**.

La máquina construye con cuatro operaciones. Este módulo hace dos de ellas, y con la revisión ya
hecha en otro sitio quedan tres de cuatro:

| operación | estado |
|---|---|
| revisión sin pin | `RunInhabited.soundAt_review` — hecho |
| **`doJoin`** | **`tablesSound_join`** — aquí |
| **`up` (`addNode`)** | **`tablesSound_addNode`** — aquí |
| filtro (el pin) | `RunSteps.FilterSoundAt` — abierto |

Y las dos que salen aquí no son casualidad, salen de lo que el diseño dice de cada una:

* **el join no inventa nada** (`join_owners_source`): toda entrada del nodo fusionado viene de uno
  de los dos lados, y una cadena de un lado sigue siéndolo en la unión
  (`ChainSound_join_left`/`_right`), porque el join solo **añade** — nodos, padres, hijos, owners y
  owners globales—;
* **la fila nueva hereda la tabla de sus padres** (`rowOwners`): una entrada nueva viene de un
  padre de fila, la cadena que la realizaba en el estado de antes se extiende con `extend`, y la
  extensión entra justo por ese padre (`shiftPid`), que es el nodo de fila que se quería.

Así que el filtro no solo es «lo que queda»: es **lo único que puede perder una cadena**, porque es
la única de las cuatro que corta.
-/

namespace AbsSat.GraphPath.Model.TablesSoundBuild

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes)
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap

-- ============================================================
-- El join: no inventa nada
-- ============================================================

/-- **`doJoin` conserva `TablesSound`.**

Toda entrada del nodo fusionado viene de uno de los dos lados (`join_owners_source`), la cadena que
la realizaba allí sigue siendo cadena de la unión (`ChainSound_join_left` / `_right`), y ya está: el
join solo añade. -/
theorem tablesSound_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : TablesSound g₁) (h₂ : TablesSound g₂) : TablesSound (join g₁ g₂) := by
  have hcs : g₂.current_step = g₁.current_step := by
    simp only [okJoin, Bool.and_eq_true] at hok
    exact (beq_iff_eq.mp hok.1.1.1).symm
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  rcases join_owners_source g₁ g₂ x n hx q hqn with ⟨m, hm, hw⟩ | ⟨m, hm, hw⟩
  · obtain ⟨sel, hsc, hsx, hsq⟩ := h₁ x m hm hx0 hx1 q hq0 hq1 hw
    exact ⟨sel, ChainSound_join_left g₁ g₂ sel hsc, hsx, hsq⟩
  · obtain ⟨sel, hsc, hsx, hsq⟩ :=
      h₂ x m hm hx0 (by rw [hcs]; exact hx1) q hq0 (by rw [hcs]; exact hq1) hw
    exact ⟨sel, ChainSound_join_right g₁ g₂ hok sel hsc, hsx, hsq⟩

theorem tablesSound_doJoin (g₁ g₂ : GPathM) (h₁ : TablesSound g₁) (h₂ : TablesSound g₂) :
    TablesSound (doJoin g₁ g₂) := by
  unfold doJoin
  split
  · exact tablesSound_join g₁ g₂ (by assumption) h₁ h₂
  · exact h₁

-- ============================================================
-- El `up`: la fila nueva hereda la tabla de sus padres
-- ============================================================

/-- **`addNode` conserva `TablesSound`.**

Las entradas viejas se extienden con `extend`. Las nuevas —las que tocan la fila— vienen de
`rowOwners`, o sea de **un padre de fila**, y la cadena que las realizaba en el estado de antes
entra en la fila justo por ese padre (`shiftPid`), que es el nodo de fila que se quería.

No hace falta nada del punto fijo de la criba: es `rowOwners` leído literal. -/
theorem tablesSound_addNode (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (hpos : 0 < g.current_step)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hmok : MachineOk g) (hnd : NodupIds g)
    (hso : ∀ pid n, g.node? pid = some n → pid ∈ n.owners)
    (hob : SelfOwn.OwnBelow g)
    (ht : TablesSound g) : TablesSound (addNode g d title) := by
  have hcsA : (addNode g d title).current_step = g.current_step + 1 := addNode_current g d title
  -- una cadena de `g` por un padre de fila y por `v` sube a la fila, y entra por ese padre
  have hchainRow : ∀ (pid p v : PathNodeId) (sel : Int → PathNodeId),
      p ∈ rowParents g d pid → ChainSound g sel → sel p.id.step = p →
      v.id.step < g.current_step → sel v.id.step = v →
      ∃ σ, ChainSound (addNode g d title) σ ∧ σ v.id.step = v ∧ σ pid.id.step = pid := by
    intro pid p v sel hp hsc hsp hv hsv
    have hpn : p ∈ newParents g := rowParents_subset g d pid p hp
    have hshift : shiftPid p d = pid := shiftPid_of_mem_rowParents g d pid p hp
    have hrow : pid ∈ newRowIds g d := by
      rw [← hshift]; exact mem_newRowIds_of_mem_newParents g d p hpos hpn
    have hpstep : p.id.step = g.current_step - 1 := (rowParent_node g d hpos hp).2
    have hselp : sel (g.current_step - 1) = p := by rw [← hpstep]; exact hsp
    refine ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hsc, ?_, ?_⟩
    · rw [extend_below g d sel v.id.step hv]; exact hsv
    · rw [DescentUp.row_step g d hd hrow, extend_top]
      unfold extendPid
      rw [if_pos hpos, hselp]
      exact hshift
  -- y una cadena por dos nodos viejos sube sin tocar la fila
  have hlow : ∀ (u v : PathNodeId) (sel : Int → PathNodeId), ChainSound g sel →
      u.id.step < g.current_step → sel u.id.step = u →
      v.id.step < g.current_step → sel v.id.step = v →
      Realizes (addNode g d title) u v :=
    fun u v sel hsc hu hsu hv hsv =>
      ⟨extend g d sel, ChainSound_addNode g d title hd hbelow hmok sel hsc,
        by rw [extend_below g d sel u.id.step hu]; exact hsu,
        by rw [extend_below g d sel v.id.step hv]; exact hsv⟩
  -- el padre de fila de donde sale una entrada nueva
  have hsource : ∀ (pid v : PathNodeId), pid ∈ newRowIds g d → v.id.step < g.current_step →
      v ∈ rowOwners g d pid →
      ∃ p ∈ rowParents g d pid, ∃ mp, g.node? p = some mp ∧ v ∈ mp.owners := by
    intro pid v hrow hv hmem
    simp only [rowOwners, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hl | hr
    · obtain ⟨hu, _⟩ := List.mem_filter.mp hl
      exact exists_owner_of_mem_unionOwnersOf g _ v hu
    · exfalso
      have hps := DescentUp.row_step g d hd hrow
      rw [hr] at hv
      omega
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  rcases DescentUp.node_addNode_cases g d title hnd hx with ⟨hrow, hn⟩ | ⟨m, hm, hn⟩
  · -- `x` es un nodo de la fila nueva
    subst hn
    rw [rowNode_owners] at hqn
    have hxs : x.id.step = g.current_step := DescentUp.row_step g d hd hrow
    rcases int_eq_or_ne q.id.step g.current_step with hqs | hqs
    · -- un owner al propio paso de la fila: es `x` (y basta una cadena por `x`)
      obtain ⟨p, hp⟩ := exists_rowParent g d hpos hrow
      obtain ⟨hps, hpstep⟩ := rowParent_node g d hpos hp
      obtain ⟨mp, hmp⟩ := Option.isSome_iff_exists.mp hps
      obtain ⟨sel, hsc, hsp, _⟩ :=
        ht p mp hmp (by omega) (by omega) p (by omega) (by omega) (hso p mp hmp)
      obtain ⟨σ, hσ, _, hσx⟩ := hchainRow x p p sel hp hsc hsp (by omega) hsp
      refine ⟨σ, hσ, hσx, ?_⟩
      -- `q` y `x` están los dos en el paso de arriba, y `rowOwners` solo tiene a `x` allí
      have : q = x := by
        simp only [rowOwners, List.mem_append, List.mem_singleton] at hqn
        rcases hqn with hl | hr
        · exfalso
          obtain ⟨hu, _⟩ := List.mem_filter.mp hl
          obtain ⟨p', hp', mp', hmp', hq'⟩ := exists_owner_of_mem_unionOwnersOf g _ q hu
          have := hob mp' (List.mem_of_find?_eq_some hmp') q hq'
          omega
        · exact hr
      rw [this, hxs, ← hxs]; exact hσx
    · -- una entrada nueva hacia abajo: viene de un padre de fila
      have hqlt : q.id.step < g.current_step := by rw [hcsA] at hq1; omega
      obtain ⟨p, hp, mp, hmp, hqmp⟩ := hsource x q hrow hqlt hqn
      obtain ⟨_, hpstep⟩ := rowParent_node g d hpos hp
      obtain ⟨sel, hsc, hsp, hsq⟩ :=
        ht p mp hmp (by omega) (by omega) q hq0 hqlt hqmp
      obtain ⟨σ, hσ, hσq, hσx⟩ := hchainRow x p q sel hp hsc hsp hqlt hsq
      exact ⟨σ, hσ, hσx, hσq⟩
  · -- `x` es un nodo viejo
    subst hn
    have hxlt : x.id.step < g.current_step := by
      have := hbelow m (List.mem_of_find?_eq_some hm)
      rwa [node?_id_eq g x m hm] at this
    rw [upMap_owners] at hqn
    rcases List.mem_append.mp hqn with hl | hr
    · -- entrada vieja
      have hqlt : q.id.step < g.current_step := hob m (List.mem_of_find?_eq_some hm) q hl
      obtain ⟨sel, hsc, hsx, hsq⟩ := ht x m hm hx0 hxlt q hq0 hqlt hl
      exact hlow x q sel hsc hxlt hsx hqlt hsq
    · -- entrada ganada: `q` es un nodo de fila que posee a `x`
      obtain ⟨hqrow, hqown⟩ := List.mem_filter.mp hr
      have hxin : x ∈ rowOwners g d q := by
        have := List.mem_of_elem_eq_true hqown
        rwa [node?_id_eq g x m hm] at this
      obtain ⟨p, hp, mp, hmp, hxmp⟩ := hsource q x hqrow hxlt hxin
      obtain ⟨_, hpstep⟩ := rowParent_node g d hpos hp
      obtain ⟨sel, hsc, hsp, hsx⟩ :=
        ht p mp hmp (by omega) (by omega) x hx0 hxlt hxmp
      obtain ⟨σ, hσ, hσx, hσq⟩ := hchainRow q p x sel hp hsc hsp hxlt hsx
      exact ⟨σ, hσ, hσx, hσq⟩

-- ============================================================
-- El filtro: lo que el autor dice que hace, dicho como teorema
-- ============================================================

/-! El autor lo describe así:

> *durante la lectura, al seleccionar aplicamos un filtrado muy ligero que borra los nodos que no
> vamos a seleccionar; tras el review, todas las tablas de owners se actualizan para dejar solo
> caminos de los nodos seleccionados*

Las dos mitades, separadas, son dos cosas muy distintas de demostrar. La primera **sale entera**. -/

/-- **El filtrado ligero: todo lo que sobrevive lleva el requisito.**

`filterRequire` solo toca `gowners`, y deja allí exclusivamente lo que coincide con el requisito en
su paso (`FabricAdd.gowners_foldl_compat`). La revisión solo poda. Así que **todo nodo que sobrevive
lleva cada requisito dentro de su propia tabla**: tiene una entrada en ese paso —`isValidNode` lo
exige— y esa entrada es el requisito.

Es la primera mitad de la frase del autor, y no necesita nada del punto fijo: sale del filtro. -/
theorem reqs_in_owners (P : GPathM) (reqs : List NodeId)
    (ctx : Pinned.Ctx (filterAllAgg P reqs))
    (x : PathNodeId) (nx : PNodeM) (hx : (filterAllAgg P reqs).node? x = some nx)
    (r : NodeId) (hr : r ∈ reqs) (hr0 : 0 ≤ r.step)
    (hrs : r.step < (filterAllAgg P reqs).current_step) :
    ∃ w ∈ nx.owners, w.id = r := by
  have hok := owners_ok_of_isValidNode _ nx (ctx.nodeval x nx hx)
  simp only [List.all_eq_true] at hok
  have hent := hok r.step (mem_intRange hr0 (by omega))
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
  obtain ⟨w, hw, hws⟩ := hent
  refine ⟨w, hw, ?_⟩
  have hg : w ∈ (filterAllAgg P reqs).gowners :=
    ctx.ownGow x nx hx w hw (by omega) (by omega)
  have hg' : w ∈ (reqs.foldl filterRequire P).gowners :=
    (pruned_reviewAgg _).gowners_sub w hg
  exact FabricAdd.gowners_foldl_compat reqs P w hg' r hr hws

/-- **Y la segunda mitad es la que queda abierta.**

*«Tras el review, las tablas dejan solo caminos de los nodos seleccionados»* dice dos cosas:

* **⊇, demostrado**: ningún camino que respete los requisitos se pierde — `ChainSound_filterAllAgg`.
  El filtro no borra nada que haga falta, exactamente como el autor dice.
* **⊆, abierto**: lo que queda en las tablas **es** un camino. Esa es `RunSteps.FilterSoundAt`, y es
  la única de las cuatro operaciones que puede fallarla, porque es la única que corta.

`reqs_in_owners` acerca las dos: da, para cada requisito, un testigo dentro de la tabla de cada
superviviente. Con `SupportedRun.shared_pin_witness` esos testigos son además **compartidos** por
cada par que sobrevive. Lo que falta es una cadena que pase por el par **y** por los testigos, que
es la misma frase que `PinPairSound`. -/
def FilterLeavesOnlyPaths (P : GPathM) (reqs : List NodeId) : Prop :=
  ∀ x nx, (filterAllAgg P reqs).node? x = some nx →
    0 ≤ x.id.step → x.id.step < (filterAllAgg P reqs).current_step →
    ∀ q ∈ nx.owners, 0 ≤ q.id.step → q.id.step < (filterAllAgg P reqs).current_step →
      Realizes (filterAllAgg P reqs) x q

theorem filterLeavesOnlyPaths_iff_tablesSound (P : GPathM) (reqs : List NodeId) :
    FilterLeavesOnlyPaths P reqs ↔ TablesSound (filterAllAgg P reqs) :=
  ⟨fun h x nx hx h0 h1 q hq0 hq1 hqn => h x nx hx h0 h1 q hqn hq0 hq1,
   fun h x nx hx h0 h1 q hqn hq0 hq1 => h x nx hx h0 h1 q hq0 hq1 hqn⟩

-- ============================================================
-- Y la mitad del bloque de literales sale gratis
-- ============================================================

/-- **La revisión sin pin conserva `TablesSound`.** Es `RunInhabited.soundAt_review` en esta
moneda: ningún camino se pierde cuando no se fija nada. -/
theorem tablesSound_review (g : GPathM) (hnd : NodupIds g) (ht : TablesSound g) :
    TablesSound (filterAllAgg g []) := fun x n hx hx0 hx1 q hq0 hq1 hqn =>
  RunInhabited.soundAt_review (fun _ => True) g hnd (RunInhabited.soundAt_of_tablesSound ht)
    x n hx hx0 hx1 q hq0 hq1 trivial hqn

/-- **Un filtro sin requisitos es la revisión sola.** -/
theorem tablesSound_filter_nil (g : GPathM) (hnd : NodupIds g) (reqs : List NodeId)
    (hnil : reqs = []) (ht : TablesSound g) : TablesSound (filterAllAgg g reqs) := by
  subst hnil; exact tablesSound_review g hnd ht

/-- **El envío a un nodo de VARIABLE no pide nada, así que su filtro sale gratis.**

`reqOfCnf_var`: un paso par del bloque de literales no tiene requisitos duros. El filtro se reduce
entonces a la revisión, y la revisión conserva `TablesSound` sin hipótesis.

Esto no es un caso de borde: **es la mitad del bloque de literales**, un paso por variable. Sumado
al paso frontera y a los que están por encima de `fusionTop` —que tampoco piden nada—, el muro se
queda solo en dos sitios. -/
theorem tablesSound_filterAllAgg_var (φ : Cnf) (g : GPathM) (hnd : NodupIds g)
    (d : NodeId) (v : Nat) (hv : v < φ.nVars) (hd : d.step = varStep v)
    (ht : TablesSound g) : TablesSound (filterAllAgg g (reqOfCnf φ d)) := by
  rw [reqOfCnf_var φ d v hv hd]
  exact tablesSound_review g hnd ht

/-! **Dónde queda el muro, con los pasos contados.** `reqOfCnf` leído literal:

| paso de `d` | requisitos | el filtro |
|---|---|---|
| `varStep v` (par, bloque literal) | **ninguno** | gratis (`tablesSound_filterAllAgg_var`) |
| `negStep v` (impar, bloque literal) | **uno**, en `varStep v` — el paso justo de abajo | abierto |
| el paso frontera `litBlock` | **ninguno** | gratis |
| paso de cláusula | **tres**, los tres literales | abierto |
| de `fusionTop` para arriba | **ninguno** | gratis |

Así que de los `2n + m + 2` pasos de la corrida, **`n + 2` no cuestan nada**, y el muro vive en los
`n` pasos impares —con un solo requisito, y **adyacente**: el paso de arriba del estado, que es
justo donde toda cadena termina— y en los `m` de cláusula, con tres.

El caso impar es el más prometedor de los dos que quedan: un requisito, en el paso donde la cadena
acaba, y `SupportedRun.shared_pin_witness` ya entrega allí un testigo **compartido** por el par. -/

-- ============================================================
-- Y el paso IMPAR también: o el filtro no hace nada, o mata el estado
-- ============================================================

/-- **La cima de un estado lleva un solo id de mapa: el de su propia clave.**

`addNode` crea la fila de arriba con `newRowIds`, y todos sus identificadores llevan el id del nodo
de mapa al que se está subiendo (`mapId_of_mem_newRowIds`). El `doJoin` solo funde estados de la
**misma** clave, y los filtros y la revisión solo podan. Así que el paso de arriba de un estado de
la corrida no tiene más que un id de mapa. -/
def TopSingleId (g : GPathM) (k : NodeId) : Prop :=
  ∀ q ∈ g.gowners, q.id.step = g.current_step - 1 → q.id = k

theorem topSingleId_addNode (g : GPathM) (d : NodeId) (title : String)
    (hgb : ∀ q ∈ g.gowners, q.id.step < g.current_step) :
    TopSingleId (addNode g d title) d := by
  intro q hq hqs
  rw [addNode_current] at hqs
  rw [addNode_gowners] at hq
  rcases List.mem_append.mp hq with hl | hr
  · exact absurd (hgb q hl) (by omega)
  · exact mapId_of_mem_newRowIds g d q hr

/-- Podar no puede añadir identificadores a la cima. -/
theorem topSingleId_of_pruned {g g' : GPathM} (hpr : Pruned g g') (k : NodeId)
    (h : TopSingleId g k) : TopSingleId g' k := by
  intro q hq hqs
  exact h q (hpr.gowners_sub q hq) (by rw [← hpr.step_eq]; exact hqs)

/-- **Si el requisito coincide con la clave, el filtro no toca nada.** -/
theorem filterRequire_top_eq (g : GPathM) (k : NodeId) (htop : TopSingleId g k)
    (r : NodeId) (hrs : r.step = g.current_step - 1) (hrk : r = k) :
    filterRequire g r = g := by
  have hkeep : g.gowners.filter (fun q => q.id.step != r.step || q.id == r) = g.gowners := by
    refine List.filter_eq_self.mpr (fun q hq => ?_)
    rcases int_eq_or_ne q.id.step r.step with hs | hs
    · have : q.id = r := by rw [hrk]; exact htop q hq (by rw [← hrs]; exact hs)
      simp only [this, beq_self_eq_true, Bool.or_true]
    · have hne : (q.id.step != r.step) = true := bne_iff_ne.mpr hs
      simp only [hne, Bool.true_or]
  show { g with gowners := g.gowners.filter (fun q => q.id.step != r.step || q.id == r) } = g
  rw [hkeep]

/-- **Y si no coincide, el paso de arriba se queda sin nadie: el estado muere.** -/
theorem not_isValid_filterRequire_top (g : GPathM) (k : NodeId) (htop : TopSingleId g k)
    (r : NodeId) (hrs : r.step = g.current_step - 1) (hrk : r ≠ k) (hpos : 0 < g.current_step) :
    isValid (filterRequire g r) = false := by
  cases hc : isValid (filterRequire g r) with
  | false => rfl
  | true =>
    exfalso
    have hcs : (filterRequire g r).current_step = g.current_step := rfl
    have hent := hasStepEntry_of_isValid _ hc r.step (by omega) (by rw [hcs]; omega)
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
    obtain ⟨q, hq, hqs⟩ := hent
    simp only [filterRequire, List.mem_filter] at hq
    obtain ⟨hqg, hqp⟩ := hq
    have hqr : q.id = r := by
      rcases Bool.or_eq_true_iff.mp hqp with h | h
      · exact absurd hqs (by simpa using h)
      · exact eq_of_beq h
    have hqk : q.id = k := htop q hqg (by rw [← hrs]; exact hqs)
    exact hrk (hqr ▸ hqk)

/-- **El filtro en el paso de arriba: o no hace nada, o mata el estado.**

Y esto cierra el caso **impar** del bloque de literales, que era uno de los dos que quedaban.

Un paso impar `negStep v` pide exactamente un requisito, `⟨varStep v, 1 - d.index⟩`, en el paso
**justo de abajo** — que es la cima del estado de partida. Y la cima lleva un solo id de mapa. Así
que el filtro solo tiene dos salidas: si el requisito es la clave, no borra nada y el filtro es la
revisión sola; y si no lo es, la cima se queda vacía y el envío se descarta por inválido.

En términos del algoritmo: *desde «v vale j» solo se puede ir a «¬v vale 1−j»*, que es lo que el
enlace cruzado del mapa dice. El filtro no elige nada, solo comprueba. -/
theorem tablesSound_filterAllAgg_top (g : GPathM) (hnd : NodupIds g) (k : NodeId)
    (htop : TopSingleId g k) (r : NodeId) (hrs : r.step = g.current_step - 1)
    (hpos : 0 < g.current_step) (hv : isValid (filterAllAgg g [r]) = true)
    (ht : TablesSound g) : TablesSound (filterAllAgg g [r]) := by
  have hfold : [r].foldl filterRequire g = filterRequire g r := rfl
  if hrk : r = k then
    -- el requisito es la clave: el filtro no toca nada
    have : filterAllAgg g [r] = filterAllAgg g [] := by
      simp only [filterAllAgg, hfold, filterRequire_top_eq g k htop r hrs hrk]
      rfl
    rw [this]
    exact tablesSound_review g hnd ht
  else
    -- el requisito no es la clave: el estado muere, así que la hipótesis es imposible
    exfalso
    have hdead := not_isValid_filterRequire_top g k htop r hrs hrk hpos
    have hpr : Pruned (filterRequire g r) (filterAllAgg g [r]) := by
      simp only [filterAllAgg, hfold]; exact pruned_reviewAgg _
    have : isValid (filterRequire g r) = true := by
      simp only [isValid, List.all_eq_true] at hv ⊢
      intro kk hkk
      have hkk' : kk ∈ intRange 0 ((filterAllAgg g [r]).current_step - 1) := by
        rwa [hpr.step_eq]
      have := hv kk hkk'
      simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at this ⊢
      obtain ⟨q, hq, hqs⟩ := this
      exact ⟨q, hpr.gowners_sub q hq, hqs⟩
    rw [hdead] at this
    exact Bool.noConfusion this

/-- info: 'AbsSat.GraphPath.Model.TablesSoundBuild.tablesSound_filterAllAgg_top' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_filterAllAgg_top

/-- info: 'AbsSat.GraphPath.Model.TablesSoundBuild.tablesSound_filterAllAgg_var' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_filterAllAgg_var

/-- info: 'AbsSat.GraphPath.Model.TablesSoundBuild.reqs_in_owners' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reqs_in_owners

/-- info: 'AbsSat.GraphPath.Model.TablesSoundBuild.tablesSound_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_addNode

/-- info: 'AbsSat.GraphPath.Model.TablesSoundBuild.tablesSound_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_join

end AbsSat.GraphPath.Model.TablesSoundBuild
