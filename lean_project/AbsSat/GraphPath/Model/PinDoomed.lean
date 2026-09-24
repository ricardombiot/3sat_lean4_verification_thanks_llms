-- lean_project/AbsSat/GraphPath/Model/PinDoomed.lean
import AbsSat.GraphPath.Model.SymInvariant
import AbsSat.GraphPath.Model.SegExactAdm

/-!
# El lector, por el invariante de las pasadas (review simétrico)

Con el review simétrico, las dos pasadas de una vuelta conservan `PStateG` y la simetría sin
hipótesis (`SymInvariant.pstateG_reviewPass'`). Lo que la medición `row-degree cleanpin` enseña del
review de un pin del lector (semillas 1 y 7, 86 pines):

* la **primera** limpieza tras el pin deja tramos sin entrada común (616 casos) —el pin quita de la
  global nodos que eran la única entrada común de algunos tramos—, y **las pasadas de esa misma vuelta
  los rompen todos**: a la entrada de la vuelta siguiente, 0;
* las limpiezas **siguientes** conservan todo `PStateG` (0 fallos);
* el barrido agresivo **no actúa** en ningún pin del lector.

Aquí se nombran esas tres cosas y se demuestra que bastan: con ellas, `SegGood` llega al punto fijo del
pin, y `SegGood` en todos los estados del lector da el veredicto
(`TopGoodLadder.readerVerdictW_iff_of_readerSegGood`).

* `PinFirstRound X` — **los tramos condenados mueren en la primera vuelta**: si el estado pinchado
  `X` cumple `PStateG`, la primera vuelta termina en `PStateG`;
* `LaterCleans X` — las limpiezas de las vueltas siguientes conservan `PStateG`;
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

/-- **Las limpiezas siguientes conservan `PStateG`.** -/
def LaterCleans (X : GPathM) : Prop :=
  ∀ j, 1 ≤ j → PStateG (iterPass j X) → OwnSymmetric (iterPass j X) →
    isValid (cleanInvalid₂ (iterPass j X)) = true → PStateG (cleanInvalid₂ (iterPass j X))

/-- **El barrido agresivo no quita nada tras el review base.** -/
def AggInactive (X : GPathM) : Prop :=
  isValid (review X) = true → ¬ measure (aggSweep (review X)) < measure (review X)

-- ============================================================
-- `SegGood` llega al punto fijo
-- ============================================================

theorem shapeOk_of_pstateG {g : GPathM} (h : PStateG g) : ShapeOk g := ⟨h.oos, h.snn, h.below⟩

/-- **Las vueltas siguientes conservan `PStateG` y la simetría**, con `LaterCleans`. -/
theorem pstateG_reviewFuel (X : GPathM) (hL : LaterCleans X) :
    ∀ (n j : Nat), 1 ≤ j → PStateG (iterPass j X) → OwnSymmetric (iterPass j X) →
      isValid (reviewFuel n (iterPass j X)) = true → PStateG (reviewFuel n (iterPass j X)) := by
  intro n
  induction n with
  | zero => intro j _ hP _ _; exact hP
  | succ n ih =>
    intro j hj hP hS hv
    -- one round from `iterPass j X`, if the final state is valid
    have step : isValid (reviewPass (iterPass j X)) = true →
        PStateG (reviewPass (iterPass j X)) ∧ OwnSymmetric (reviewPass (iterPass j X)) := by
      intro hv1
      have hpr : Pruned (cleanInvalid₂ (iterPass j X)) (reviewPass (iterPass j X)) :=
        Pruned.trans (pruned_reviewParents _) (pruned_reviewSons _)
      have hvc := Certifies.isValid_of_pruned hpr hv1
      have hc := hL j hj hP hS hvc
      have hsc := OwnSymmetric_cleanInvalid₂ _ hP.nd (shapeOk_of_pstateG hP) hS hvc
      exact pstateG_reviewPass' _ hc hsc
    simp only [reviewFuel] at hv ⊢
    split
    · next hg =>
      rw [if_pos hg] at hv
      split
      · next hlt =>
        rw [if_pos hlt] at hv
        have hv1 : isValid (reviewPass (iterPass j X)) = true :=
          Certifies.isValid_of_pruned (pruned_reviewFuel n _) hv
        obtain ⟨hP1, hS1⟩ := step hv1
        exact ih (j + 1) (by omega) hP1 hS1 hv
      · next hlt =>
        rw [if_neg hlt] at hv
        exact (step hv).1
    · exact hP

/-- **`SegGood` en el punto fijo del pin**, con las tres hipótesis del pin. -/
theorem segGood_pinReview (X : GPathM) (hr : RevOk X) (hP0 : PStateG X) (hF : PinFirstRound X)
    (hL : LaterCleans X) (hA : AggInactive X) (hv : isValid (reviewAgg X) = true) :
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
      exact (pstateG_reviewFuel X hL (measure X) 1 (Nat.le_refl 1) hP1 hS1 hv).sg
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
**los tramos condenados mueren en la primera vuelta** (`PinFirstRound`), las limpiezas siguientes
conservan `PStateG` (`LaterCleans`) y el barrido agresivo no actúa (`AggInactive`). -/
theorem readerVerdictW_iff_of_pinDoomed
    (hStart : ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ,
      isValid (filterAllAgg kv.2 []) = true → SegExact.SegExact (filterAllAgg kv.2 []))
    (hPin : ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      PinFirstRound (filterWeak g (q.id.step, [q.id])) ∧
        LaterCleans (filterWeak g (q.id.step, [q.id])) ∧
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
    rw [SegExactFilter.filterAllAgg_pin] at hv' ⊢
    exact segGood_pinReview _ hr hPX hF hL hA hv'

/-- info: 'AbsSat.GraphPath.Model.PinDoomed.readerVerdictW_iff_of_pinDoomed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_pinDoomed

end AbsSat.GraphPath.Model.PinDoomed
