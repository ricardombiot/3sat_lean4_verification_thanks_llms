-- lean_project/AbsSat/GraphPath/Model/PinDoomed.lean
import AbsSat.GraphPath.Model.SymInvariant
import AbsSat.GraphPath.Model.SegExactAdm
import AbsSat.GraphPath.Model.ReadyInv

/-!
# El lector, por el invariante de las pasadas (review simétrico)

Con el review simétrico, las dos pasadas de una vuelta conservan `PStateG` y la simetría sin
hipótesis (`SymInvariant.pstateG_reviewPass'`). Lo que la medición `row-degree cleanpin` enseña del
review de un pin del lector (semillas 1 y 7, 86 pines):

* la **primera** limpieza tras el pin deja tramos sin entrada común (616 casos) —el pin quita de la
  global nodos que eran la única entrada común de algunos tramos—, y **las pasadas de esa misma vuelta
  los rompen todos**: a la entrada de la vuelta siguiente, 0;
* las limpiezas **siguientes** no cambian nada: a su entrada todo nodo es válido, está en la global y
  tiene sus enlaces en la tabla (0 fallos), y ninguna vuelta siguiente progresa;
* el barrido agresivo **no actúa** en ningún pin del lector.

Aquí se nombran esas tres cosas y se demuestra que bastan: con ellas, `SegGood` llega al punto fijo del
pin, y `SegGood` en todos los estados del lector da el veredicto
(`TopGoodLadder.readerVerdictW_iff_of_readerSegGood`).

* `PinFirstRound X` — **los tramos condenados mueren en la primera vuelta**: si el estado pinchado
  `X` cumple `PStateG`, la primera vuelta termina en `PStateG`;
* `LaterValid X` — las vueltas siguientes que aún progresan empiezan con todo nodo válido; como
  estar en la global y tener los enlaces en la tabla lo deja la vuelta anterior (`ReadyInv`), su
  limpieza no cambia nada (`cleanInvalid₂_eq_self_of_ready`); la vuelta final es la identidad por el
  punto fijo;
* `AggInactive X` — el barrido agresivo no quita nada tras el review base.

`PStateG` del estado pinchado sale de `SegGood` del estado del lector anterior
(`pstateG_of_reader`): lo demás lo da el punto fijo del review agresivo.
-/

namespace AbsSat.GraphPath.Model.PinDoomed

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Threaded (OwnSymmetric)
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PassPlain (PStateG)
open AbsSat.GraphPath.Model.SymInvariant
open AbsSat.GraphPath.Model.TopGoodUp (SegGood)
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeak)

-- ============================================================
-- Las hipótesis del pin
-- ============================================================

/-- La `j`-ésima vuelta del review base. -/
def iterPass : Nat → GPathM → GPathM
  | 0, g => g
  | n + 1, g => reviewPass (iterPass n g)

/-- **Los tramos condenados mueren en la primera vuelta**: si el estado pinchado cumple `PStateG`, la
primera vuelta (limpieza y pasadas) termina en `PStateG`. -/
def PinFirstRound (X : GPathM) : Prop :=
  PStateG X → isValid (reviewPass X) = true → PStateG (reviewPass X)

/-- **Un estado listo para una limpieza que no cambia nada**: todo nodo válido, todo nodo en la
global, todo enlace dentro de la tabla. -/
structure Ready (g : GPathM) : Prop where
  valid : ∀ n ∈ g.nodes, isValidNode g n = true
  gow : Ownership.NodesAreGowners g
  links : Bridge.LinksInOwners g

/-- **Las vueltas siguientes que aún progresan empiezan con todo nodo válido.** Es lo único de `Ready`
que queda como hipótesis: estar en la global y tener los enlaces en la tabla son invariantes de la
vuelta anterior (`ReadyInv.nodesGow_reviewPass`, `ReadyInv.links_reviewPass`). La última vuelta no
lo necesita: en el punto fijo la vuelta entera es la identidad. Medido (`row-degree cleanpin`): a la
entrada de toda limpieza siguiente, 0 nodos inválidos; y ninguna vuelta siguiente progresa. -/
def LaterValid (X : GPathM) : Prop :=
  ∀ j, 1 ≤ j → measure (reviewPass (iterPass j X)) < measure (iterPass j X) →
    (∀ n ∈ (iterPass j X).nodes, isValidNode (iterPass j X) n = true) ∧
    -- con la regla de parejas (plan `pair_mode`, B4): la regla tampoco quita nada al empezar
    pairSweep (iterPass j X) = iterPass j X

/-- **El barrido agresivo no quita nada tras el review base.** -/
def AggInactive (X : GPathM) : Prop :=
  isValid (review X) = true → ¬ measure (aggSweep (review X)) < measure (review X)

-- ============================================================
-- Una limpieza sobre un estado listo no cambia nada
-- ============================================================

/-- Con tablas vivas y todo nodo en la global, cortar una tabla contra la global no quita nada. -/
theorem intersect_gowners_eq (g : GPathM) (h : PStateG g) (hgn : GownersNodes.GN g)
    (hgow : Ownership.NodesAreGowners g) (n : PNodeM) (hn : n ∈ g.nodes) :
    intersectOwners n.owners g.gowners = n.owners := by
  refine List.filter_eq_self.mpr (fun q hq => ?_)
  have hnode : g.node? n.id = some n := node?_of_mem h.nd n hn
  rcases Int.lt_or_le q.id.step 0 with hlt | h0
  · -- out of range: the global has no entry there
    have hse : hasStepEntry g.gowners q.id.step = false := by
      cases hs : hasStepEntry g.gowners q.id.step with
      | false => rfl
      | true =>
        obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp hs
        obtain ⟨m, hm, hmid⟩ := hgn r hr
        have := h.snn m hm
        rw [hmid, eq_of_beq hrs] at this
        omega
    rw [hse]; rfl
  · rcases Int.lt_or_le q.id.step g.current_step with hlt2 | hge
    · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.ol n.id n hnode q hq h0 (by omega))
      have hmid : m.id = q := node?_id_eq g q m hm
      have hqg : q ∈ g.gowners := by
        rw [← hmid]; exact hgow m (List.mem_of_find?_eq_some hm)
      rw [List.contains_iff_mem.mpr hqg, Bool.or_true]
    · have hse : hasStepEntry g.gowners q.id.step = false := by
        cases hs : hasStepEntry g.gowners q.id.step with
        | false => rfl
        | true =>
          obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp hs
          obtain ⟨m, hm, hmid⟩ := hgn r hr
          have := h.below m hm
          rw [hmid, eq_of_beq hrs] at this
          omega
      rw [hse]; rfl

/-- **Sobre un estado listo, el corte de un nodo es el propio nodo.** -/
theorem cutNode_eq_self_of_ready (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g)
    (hgn : GownersNodes.GN g) (hr : Ready g) (n : PNodeM) (hn : n ∈ g.nodes) :
    cutNode g.gowners g n = n := by
  have hnode : g.node? n.id = some n := node?_of_mem h.nd n hn
  have hown := intersect_gowners_eq g h hgn hr.gow n hn
  have hlinks := hr.links n.id n hnode
  -- `m` admits `x` exactly when `x` is in its table
  have adm : ∀ m x (nm : PNodeM), g.node? m = some nm → admits g.gowners g m x = nm.owners.contains x := by
    intro m x nm hm
    unfold admits cutOwners
    rw [hm]
    simp only
    rw [intersect_gowners_eq g h hgn hr.gow nm (List.mem_of_find?_eq_some hm)]
  have link : ∀ p (m : PNodeM), g.node? p = some m → p ∈ n.owners →
      (admits g.gowners g n.id p && admits g.gowners g p n.id) = true := by
    intro p m hm hp
    rw [adm n.id p n hnode, adm p n.id m hm, List.contains_iff_mem.mpr hp,
      List.contains_iff_mem.mpr (hs n.id n p m hnode hm hp)]
    rfl
  have hpar : n.parents.filter (fun p => admits g.gowners g n.id p && admits g.gowners g p n.id)
      = n.parents := by
    refine List.filter_eq_self.mpr (fun p hp => ?_)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.plive n.id n hnode p hp)
    exact link p m hm (hlinks.1 p hp)
  have hson : n.sons.filter (fun q => admits g.gowners g n.id q && admits g.gowners g q n.id)
      = n.sons := by
    refine List.filter_eq_self.mpr (fun q hq => ?_)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h.slive n.id n hnode q hq)
    exact link q m hm (hlinks.2 q hq)
  unfold cutNode cutOwners
  rw [hown, hpar, hson]

/-- **Sobre un estado listo, `cleanInvalid₂` no cambia nada**: ningún corte quita nada y ningún nodo
es inválido, así que la purga no elimina y el corte final es la identidad. -/
theorem cleanInvalid₂_eq_self_of_ready (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g)
    (hgn : GownersNodes.GN g) (hr : Ready g) : cleanInvalid₂ g = g := by
  have hcut := cutNode_eq_self_of_ready g h hs hgn hr
  have hstep : ∀ id, purgeStep g id = g := by
    intro id
    unfold purgeStep
    cases hn : g.node? id with
    | none => rfl
    | some n =>
      simp only
      rw [hcut n (List.mem_of_find?_eq_some hn), if_pos (hr.valid n (List.mem_of_find?_eq_some hn))]
  have hround : purgeRound g = g := by
    unfold purgeRound
    generalize g.nodes.map (·.id) = ids
    induction ids with
    | nil => rfl
    | cons id ids ih => simp only [List.foldl_cons, hstep, ih]
  have hfuel : purgeFuel (g.nodes.length + 1) g = g := by
    simp only [purgeFuel, hround, Nat.lt_irrefl, if_false]
    split <;> rfl
  unfold cleanInvalid₂
  rw [hfuel]
  unfold cutAll
  have hmap : g.nodes.map (cutNode g.gowners g) = g.nodes :=
    (List.map_congr_left (fun n hn => hcut n hn)).trans (List.map_id _)
  rw [hmap]

/-- **Y la limpieza con parejas tampoco**, si además la regla no quita nada. -/
theorem cleanPair_eq_self_of_ready (g : GPathM) (h : PStateG g) (hs : OwnSymmetric g)
    (hgn : GownersNodes.GN g) (hr : Ready g) (hp : pairSweep g = g) : cleanPair g = g := by
  have hc := cleanInvalid₂_eq_self_of_ready g h hs hgn hr
  unfold cleanPair
  simp only [hc]
  simp only [pairFuel, hp, Nat.lt_irrefl, if_false]
  split <;> rfl

-- ============================================================
-- `SegGood` llega al punto fijo
-- ============================================================

theorem shapeOk_of_pstateG {g : GPathM} (h : PStateG g) : ShapeOk g := ⟨h.oos, h.snn, h.below⟩

theorem gn_iterPass (X : GPathM) (h : GownersNodes.GN X) : ∀ j, GownersNodes.GN (iterPass j X) := by
  intro j
  induction j with
  | zero => exact h
  | succ n ih => exact GownersNodes.GN_reviewPass _ ih

theorem nodup_shape_iterPass (X : GPathM) (hr : RevOk X) :
    ∀ j, NodupIds (iterPass j X) ∧ ShapeOk (iterPass j X) := by
  intro j
  induction j with
  | zero => exact ⟨hr.nd, hr.sh⟩
  | succ n ih =>
    exact ⟨PinAliveChain.NodupIds_reviewPass _ ih.1, ih.2.of_pruned (pruned_reviewPass _)⟩

/-- **Una vuelta siguiente, válida, empieza lista** si sus nodos son válidos: lo demás lo deja la
vuelta anterior. -/
theorem ready_iterPass (X : GPathM) (hr : RevOk X) (i : Nat)
    (hv : isValid (iterPass (i + 1) X) = true)
    (hval : ∀ n ∈ (iterPass (i + 1) X).nodes, isValidNode (iterPass (i + 1) X) n = true) :
    Ready (iterPass (i + 1) X) := by
  obtain ⟨hnd, hsh⟩ := nodup_shape_iterPass X hr i
  have hpr : Pruned (cleanPair (iterPass i X)) (reviewPass (iterPass i X)) :=
    Pruned.trans (pruned_reviewParents _) (pruned_reviewSons _)
  have hvc : isValid (cleanPair (iterPass i X)) = true := Certifies.isValid_of_pruned hpr hv
  exact ⟨hval, ReadyInv.nodesGow_reviewPass _ hnd hsh hvc, ReadyInv.links_reviewPass _ hnd⟩

/-- **Las vueltas siguientes conservan `PStateG` y la simetría**, con `LaterValid`: si la vuelta
progresa, empieza lista y su limpieza no cambia nada (`cleanInvalid₂_eq_self_of_ready`); si no
progresa, la vuelta entera es la identidad. -/
theorem pstateG_reviewFuel (X : GPathM) (hr : RevOk X) (hL : LaterValid X) (hgn : GownersNodes.GN X) :
    ∀ (n j : Nat), 1 ≤ j → PStateG (iterPass j X) → OwnSymmetric (iterPass j X) →
      isValid (reviewFuel n (iterPass j X)) = true → PStateG (reviewFuel n (iterPass j X)) := by
  intro n
  induction n with
  | zero => intro j _ hP _ _; exact hP
  | succ n ih =>
    intro j hj hP hS hv
    simp only [reviewFuel] at hv ⊢
    split
    · next hg =>
      rw [if_pos hg] at hv
      split
      · next hlt =>
        rw [if_pos hlt] at hv
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have hLj := hL (i + 1) hj hlt
        have hrd := ready_iterPass X hr i hg hLj.1
        have hce := cleanPair_eq_self_of_ready _ hP hS (gn_iterPass X hgn (i + 1)) hrd hLj.2
        obtain ⟨hP1, hS1⟩ := pstateG_reviewPass' (iterPass (i + 1) X) (by rw [hce]; exact hP)
          (by rw [hce]; exact hS)
        exact ih (i + 1 + 1) (by omega) hP1 hS1 hv
      · next hlt =>
        have hfix : reviewPass (iterPass j X) = iterPass j X :=
          reviewPass_eq_self _ (Nat.le_antisymm (measure_reviewPass_le _) (Nat.not_lt.mp hlt))
        rw [hfix]; exact hP
    · exact hP

/-- **`SegGood` en el punto fijo del pin**, con las tres hipótesis del pin. -/
theorem segGood_pinReview (X : GPathM) (hr : RevOk X) (hP0 : PStateG X) (hgn : GownersNodes.GN X)
    (hF : PinFirstRound X) (hL : LaterValid X) (hA : AggInactive X)
    (hv : isValid (reviewAgg X) = true) :
    SegGood (reviewAgg X) := by
  have hRA : reviewAgg X = review X := by
    show reviewAggFuel (measure X + 1) X = review X
    simp only [reviewAggFuel]
    split
    · next hv1 => rw [if_neg (hA hv1)]
    · rfl
  rw [hRA] at hv ⊢
  have hrev : review X = reviewFuel (measure X + 1) X := rfl
  rw [hrev] at hv ⊢
  simp only [reviewFuel] at hv ⊢
  split
  · next hg =>
    rw [if_pos hg] at hv
    split
    · next hlt =>
      rw [if_pos hlt] at hv
      have hv1 : isValid (reviewPass X) = true :=
        Certifies.isValid_of_pruned (pruned_reviewFuel _ _) hv
      have hP1 := hF hP0 hv1
      have hS1 := OwnSymmetric_reviewPass X hr hv1
      exact (pstateG_reviewFuel X hr hL hgn (measure X) 1 (Nat.le_refl 1) hP1 hS1 hv).sg
    · next hlt =>
      rw [if_neg hlt] at hv
      exact (hF hP0 hv).sg
  · next hg =>
    rw [if_neg hg] at hv
    exact absurd hv hg

/-- info: 'AbsSat.GraphPath.Model.PinDoomed.segGood_pinReview' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segGood_pinReview

-- ============================================================
-- `PStateG` en los estados del lector
-- ============================================================

/-- **Un estado del lector con `SegGood` cumple `PStateG`**: lo demás lo da el punto fijo del review
agresivo —posesión en los pasos vecinos igual a los enlaces (`AdjacentOwners`), simetría
(`ownSymmetric_of_aggOk`), tablas vivas (la global son nodos)—. -/
theorem pstateG_of_reader (g : GPathM) (ctx : PinAliveChain.DCtx g) (hv : isValid g = true)
    (hsg : SegGood g) : PStateG g ∧ OwnSymmetric g := by
  have rc := ReaderAgg.RCtx_of_readableAgg g ctx.rd
  have adj := AdjacentOwners.adj_of_readable g ctx.rd hv ctx.pms ctx.sn
  have hok : AggFixpoint.AggOk g := by
    obtain ⟨g₀, reqs, _, hg⟩ := ctx.rd
    rw [hg] at hv ⊢
    exact AggFixpoint.aggOk_reviewAgg _ hv
  have hsym := PinExactBoundary.ownSymmetric_of_aggOk g hok rc.snn rc.below adj.ctx.nodeval
  have live : ∀ q, GownersNodes.HasNode g q → (g.node? q).isSome := fun q h =>
    (GownersNodes.hasNode_iff g q).mp h
  have hi1 : PassPlain.I1 g := by
    intro y ny hy w hw hw0 _ hws
    exact (AdjacentOwners.owners_below_iff_parents g adj y ny hy (by omega) w (by omega)).mp hw
  have hi1s : PassPlain.I1s g := by
    intro y ny hy w hw _ hw1 hws
    exact (AdjacentOwners.owners_above_iff_sons g adj y ny hy (by omega) w hws).mp hw
  have hol : PassPlain.OwnLive g := by
    intro y ny hy w hw hw0 hw1
    exact live w (adj.ctx.gn w (adj.ctx.ownGow y ny hy w hw hw0 (by omega)))
  have hpl : PassCtx.PLive g := by
    intro y ny hy p hp
    exact live p (rc.shape.pn ny (List.mem_of_find?_eq_some hy) p hp)
  have hsl : PassCtx.SLive g := by
    intro y ny hy s hs
    exact live s (ctx.sn ny (List.mem_of_find?_eq_some hy) s hs)
  exact ⟨{ nd := rc.nodup, sg := hsg, i1 := hi1, i1s := hi1s, ol := hol, plive := hpl,
           slive := hsl, self := adj.ctx.self, lsym := LocSym_of_ownSymmetric g hsym,
           lsymU := LocSymUp_of_ownSymmetric g hsym, nr := rc.shape.notroot, below := rc.below,
           oos := rc.oos, snn := rc.snn, rootz := rc.rootz }, hsym⟩

-- ============================================================
-- La escalera
-- ============================================================

/-- El filtro débil solo toca la global: `PStateG` y la simetría pasan tal cual. -/
theorem pstateG_filterWeak (g : GPathM) (e : Int × List NodeId) (h : PStateG g) :
    PStateG (filterWeak g e) where
  nd := h.nd
  sg := h.sg
  i1 := h.i1
  i1s := h.i1s
  ol := h.ol
  plive := h.plive
  slive := h.slive
  self := h.self
  lsym := h.lsym
  lsymU := h.lsymU
  nr := h.nr
  below := h.below
  oos := h.oos
  snn := h.snn
  rootz := h.rootz

theorem ownSymmetric_filterWeak (g : GPathM) (e : Int × List NodeId) (h : OwnSymmetric g) :
    OwnSymmetric (filterWeak g e) := h

/-- **El lector sin retroceso decide 3-SAT**, con: `SegExact` en la línea final revisada (su primer
estado, medido: 0 tramos sin cadena), y en cada pin del lector, sobre el estado pinchado
`X = filterWeak g (paso de q, [q])`, las tres hipótesis medidas de `row-degree cleanpin`:
**los tramos condenados mueren en la primera vuelta** (`PinFirstRound`), las vueltas siguientes que
progresan empiezan con todo nodo válido (`LaterValid`) y el barrido agresivo no actúa
(`AggInactive`). -/
theorem readerVerdictW_iff_of_pinDoomed
    (hStart : ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ,
      isValid (filterAllAgg kv.2 []) = true → SegExact.SegExact (filterAllAgg kv.2 []))
    (hPin : ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      PinFirstRound (filterWeak g (q.id.step, [q.id])) ∧
        LaterValid (filterWeak g (q.id.step, [q.id])) ∧
        AggInactive (filterWeak g (q.id.step, [q.id])))
    (φ : Cnf) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine TopGoodLadder.readerVerdictW_iff_of_readerSegGood ?_ φ hwf
  intro φ' hwf' kv hkv g hR hv
  obtain ⟨hm, hcs, _⟩ := ReaderAggRun.pureRunW_state φ' hwf' kv hkv
  have hpos : 0 < kv.2.current_step := by rw [hcs]; exact ConservationCore.stepCount_pos φ'
  have ctx₀ : PinAliveChain.DCtx (filterAllAgg kv.2 []) :=
    { rd := ⟨kv.2, [], hm.rctx, rfl⟩
      pms := AggInvariants.PMS_filterAllAgg kv.2 [] hm.pms
      sn := AggInvariants.SN_filterAllAgg kv.2 [] hm.sn
      smp := AnchoredSurvive.SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot []
      pos := by rw [(pruned_filterAllAgg kv.2 []).step_eq]; exact hpos }
  revert hv
  induction hR with
  | start => exact fun hv => SegExact.segGood_of_segExact _ (hStart φ' hwf' kv hkv hv)
  | pin g k q hR hv hk hq ih =>
    intro hv'
    have ctx := TopGoodLadder.dctx_of_readFromR _ ctx₀ g hR
    obtain ⟨hP, hS⟩ := pstateG_of_reader g ctx hv (ih hv)
    obtain ⟨hF, hL, hA⟩ := hPin φ' hwf' kv hkv g k q hR hv hk hq
    have hPX := pstateG_filterWeak g (q.id.step, [q.id]) hP
    have hr : RevOk (filterWeak g (q.id.step, [q.id])) :=
      ⟨hPX.nd, shapeOk_of_pstateG hPX, ownSymmetric_filterWeak g _ hS⟩
    have hgnX : GownersNodes.GN (filterWeak g (q.id.step, [q.id])) := fun r hr =>
      (ReaderAgg.RCtx_of_readableAgg g ctx.rd).gn r (List.mem_filter.mp hr).1
    rw [SegExactFilter.filterAllAgg_pin] at hv' ⊢
    exact segGood_pinReview _ hr hPX hgnX hF hL hA hv'

/-- info: 'AbsSat.GraphPath.Model.PinDoomed.readerVerdictW_iff_of_pinDoomed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_pinDoomed

end AbsSat.GraphPath.Model.PinDoomed
