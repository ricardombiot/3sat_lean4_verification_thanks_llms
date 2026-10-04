-- lean_project/AbsSat/GraphPath/Model/PairHelly.lean
import AbsSat.GraphPath.Model.PinDoomed

/-!
# La regla de parejas: `PairOk`, el barrido agresivo inactivo y el lector por `PairHelly`

Plan `docs/plans/pair_mode.md`, B5 y B6. Con la regla de parejas dentro de la limpieza
(`cleanPair`, B0–B4), toda pareja de nodos vivos que se poseen comparte entrada en cada paso
—en cuanto el estado es válido— (`pairFixed_cleanPair`). Dos consecuencias:

* **el barrido agresivo no actúa en el punto fijo del review** (`aggSweep_eq_self`): su rama
  «asimétrica» la cierra la simetría y su rama «inconsistente» la cierra la regla, que ya quitó esas
  parejas. La hipótesis `AggInactive` de `PinDoomed` pasa a ser un teorema (`aggInactive_of_revOk`);
* la hipótesis de fondo del lector ya no es dinámica: en lugar de «la primera vuelta deja cada tramo
  en una cadena completa» (`RoundExact`), **un estado con parejas compatibles tiene entrada común en
  cada tramo** (`PairHelly`), sobre el estado tras la limpieza con parejas, sin pasadas.

La escalera (`readerVerdictW_iff_of_pairHelly`) queda con `hStart` y, en cada pin:

* `PairHelly (cleanPair X)` — Helly de parejas, estático;
* `CleanRest X` — tras la limpieza con parejas valen las demás piezas de `PStateG` (todo salvo
  `SegGood`: I1, tablas vivas, simetría local…); medido para la limpieza sola en el v184 (0 fallos);
* `LaterValid X` — como en `PinDoomed`, ahora pidiendo también que la regla no quite nada al
  empezar una vuelta siguiente que progresa.
-/

namespace AbsSat.GraphPath.Model.PairHelly

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Threaded (OwnSymmetric)
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PassPlain (PStateG)
open AbsSat.GraphPath.Model.SymInvariant
open AbsSat.GraphPath.Model.PinDoomed
open AbsSat.GraphPath.Model.TopGoodUp (SegGood)
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeak)

-- ============================================================
-- B5. `PairOk`: tras la limpieza con parejas, la regla ya no quita nada
-- ============================================================

/-- **La regla no quita nada**: toda pareja de nodos vivos que se poseen comparte entrada en cada paso
común. -/
def PairFixed (g : GPathM) : Prop := pairSweep g = g

/-- Lo mismo, dicho pareja a pareja. -/
def PairOk (g : GPathM) : Prop :=
  ∀ x n w, g.node? x = some n → w ∈ n.owners → w ≠ x → ∀ nw, g.node? w = some nw →
    pairShares g.current_step n.owners nw.owners = true

theorem pairBad_false_of_fixed (g : GPathM) (h : PairFixed g) (n : PNodeM) (hn : n ∈ g.nodes)
    (w : PathNodeId) (hw : w ∈ n.owners) : pairBad g n w = false := by
  have hmap : g.nodes.map (pairMap g) = g.nodes := congrArg GPathM.nodes h
  have hn' := map_fixed_pointwise (pairMap g) g.nodes hmap n hn
  have hw' : w ∈ (pairMap g n).owners := by rw [hn']; exact hw
  exact ((mem_pairMap_owners g n w).mp hw').2

theorem pairOk_of_fixed (g : GPathM) (h : PairFixed g) : PairOk g := by
  intro x n w hn hw hwx nw hnw
  have hb := pairBad_false_of_fixed g h n (List.mem_of_find?_eq_some hn) w hw
  have hnid : n.id = x := node?_id_eq g x n hn
  unfold pairBad at hb
  rw [hnw] at hb
  have hne : (w != n.id) = true := by rw [hnid]; exact bne_iff_ne.mpr hwx
  rw [hne, Bool.true_and] at hb
  cases hs : pairShares g.current_step n.owners nw.owners
  · simp only [hs, Bool.not_false] at hb; exact absurd hb (by decide)
  · rfl

/-- El bucle de la regla, con combustible de sobra, termina en un estado que la regla no toca, si es
válido. -/
theorem pairFixed_pairFuel : ∀ (fuel : Nat) (g : GPathM), measure g < fuel →
    isValid (pairFuel fuel g) = true → PairFixed (pairFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro g hlt hv
    by_cases hg : isValid g = true
    · by_cases hdec : measure (pairSweep g) < measure g
      · have he : pairFuel (f + 1) g = pairFuel f (cleanInvalid₂ (pairSweep g)) := by
          simp only [pairFuel, hg, if_true, hdec]
        rw [he] at hv ⊢
        have hm := measure_cleanInvalid₂_le (pairSweep g)
        exact ih _ (by omega) hv
      · have he : pairFuel (f + 1) g = g := by
          simp only [pairFuel, hg, if_true, hdec, if_false]
        rw [he]
        exact pairSweep_eq_self g (Nat.le_antisymm (measure_pairSweep_le g) (Nat.not_lt.mp hdec))
    · have he : pairFuel (f + 1) g = g := by simp only [pairFuel, hg, Bool.false_eq_true, if_false]
      rw [he] at hv
      exact absurd hv hg

/-- **Tras la limpieza con parejas, si el estado es válido, la regla ya no quita nada.** -/
theorem pairFixed_cleanPair (g : GPathM) (hv : isValid (cleanPair g) = true) :
    PairFixed (cleanPair g) :=
  pairFixed_pairFuel _ _ (Nat.lt_succ_self _) hv

theorem pairOk_cleanPair (g : GPathM) (hv : isValid (cleanPair g) = true) : PairOk (cleanPair g) :=
  pairOk_of_fixed _ (pairFixed_cleanPair g hv)

/-- info: 'AbsSat.GraphPath.Model.PairHelly.pairOk_cleanPair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairOk_cleanPair

-- ============================================================
-- B6a. El barrido agresivo no actúa en el punto fijo del review
-- ============================================================

/-- En el punto fijo de una vuelta, la limpieza con parejas es la identidad, y por tanto la regla. -/
theorem pairFixed_of_reviewPass_eq (g : GPathM) (hv : isValid g = true) (h : reviewPass g = g) :
    PairFixed g := by
  have h₁ := measure_cleanPair_le g
  have h₂ := measure_reviewParents_le (cleanPair g)
  have h₃ := measure_reviewSons_le (reviewParents (cleanPair g))
  have hm : measure (reviewPass g) = measure g := by rw [h]
  simp only [reviewPass] at hm
  have hcp := cleanPair_eq_self g (by omega)
  have hfix := pairFixed_cleanPair g (by rw [hcp.2]; exact hv)
  rw [hcp.2] at hfix
  exact hfix

/-- Con la tabla entera en cada paso (nodo válido), el test de pareja es el del filtro agresivo. -/
theorem sharesEveryStep_of_pairShares (g : GPathM) (nx : PNodeM) (hvx : isValidNode g nx = true)
    (wo : List PathNodeId) (h : pairShares g.current_step nx.owners wo = true) :
    sharesEveryStep g.current_step nx.owners wo = true := by
  have hok := owners_ok_of_isValidNode g nx hvx
  unfold sharesEveryStep
  unfold pairShares at h
  rw [List.all_eq_true] at h hok ⊢
  intro k hk
  have h1 := h k hk
  have h2 := hok k hk
  rw [h2] at h1
  simpa using h1

/-- **Un par del barrido no hace nada** en un estado simétrico, con la regla en su punto fijo y todo
nodo válido. -/
theorem aggPair_eq_self (g : GPathM) (hs : OwnSymmetric g) (hp : PairFixed g)
    (hval : ∀ n ∈ g.nodes, isValidNode g n = true) (x : PathNodeId) (nx : PNodeM)
    (hx : g.node? x = some nx) (w : PathNodeId) (hw : w ∈ nx.owners) : aggPair g x w = g := by
  unfold aggPair
  rw [hx]
  cases hnw : g.node? w with
  | none => rfl
  | some nw =>
    simp only
    have hxw : x ∈ nw.owners := hs x nx w nw hx hnw hw
    have hvx := hval nx (List.mem_of_find?_eq_some hx)
    have hsh : sharesEveryStep g.current_step nx.owners nw.owners = true := by
      by_cases hwx : w = x
      · subst hwx
        rw [hx] at hnw
        obtain rfl := Option.some.inj hnw
        exact sharesEveryStep_self _ _
      · exact sharesEveryStep_of_pairShares g nx hvx _
          (pairOk_of_fixed g hp x nx w hx hw hwx nw hnw)
    simp [hsh]
    intro _ _ hn; exact absurd hxw hn

theorem foldl_eq_self {β : Type} (f : GPathM → β → GPathM) (g : GPathM) :
    ∀ (l : List β), (∀ b ∈ l, f g b = g) → l.foldl f g = g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro h
    simp only [List.foldl_cons, h b List.mem_cons_self]
    exact ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

/-- **Un nodo del barrido no hace nada.** -/
theorem aggNode_eq_self (g : GPathM) (hs : OwnSymmetric g) (hp : PairFixed g)
    (hval : ∀ n ∈ g.nodes, isValidNode g n = true) (x : PathNodeId) : aggNode g x = g := by
  unfold aggNode
  cases hx : g.node? x with
  | none => rfl
  | some nx =>
    simp only
    have hvx := hval nx (List.mem_of_find?_eq_some hx)
    have hin : (intRange 0 (g.current_step - 1)).reverse.foldl
        (fun g kw => (ownersAtNow g x kw).foldl (fun g w => aggPair g x w) g) g = g := by
      refine foldl_eq_self _ g _ (fun kw _ => ?_)
      refine foldl_eq_self _ g _ (fun w hw => ?_)
      have hw' : w ∈ nx.owners := by
        simp only [ownersAtNow, ownersOf, hx, ownersAt, List.mem_filter] at hw
        exact hw.1
      exact aggPair_eq_self g hs hp hval x nx hx w hw'
    simp only [hvx, if_true, hin, hx]

/-- **El barrido agresivo no hace nada** en un estado simétrico, con la regla en su punto fijo y todo
nodo válido. -/
theorem aggSweep_eq_self (g : GPathM) (hs : OwnSymmetric g) (hp : PairFixed g)
    (hval : ∀ n ∈ g.nodes, isValidNode g n = true) : aggSweep g = g := by
  unfold aggSweep
  split
  · refine foldl_eq_self _ g _ (fun k _ => ?_)
    exact foldl_eq_self _ g _ (fun x _ => aggNode_eq_self g hs hp hval x)
  · rfl

/-- **`AggInactive` es un teorema** con la regla de parejas: en el punto fijo del review base, válido,
el barrido agresivo es la identidad. -/
theorem aggInactive_of_revOk (X : GPathM) (hr : RevOk X) : AggInactive X := by
  intro hv hlt
  have hs := OwnSymmetric_review X hr hv
  have hfix := reviewPass_review X hv
  have hp := pairFixed_of_reviewPass_eq (review X) hv hfix
  have hval : ∀ n ∈ (review X).nodes, isValidNode (review X) n = true := by
    intro n hn
    have hnd := PinAliveChain.NodupIds_review X hr.nd
    exact review_node_valid X hv n.id n (node?_of_mem hnd n hn)
  rw [aggSweep_eq_self _ hs hp hval] at hlt
  exact Nat.lt_irrefl _ hlt

/-- info: 'AbsSat.GraphPath.Model.PairHelly.aggInactive_of_revOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms aggInactive_of_revOk

-- ============================================================
-- B6b. El lector por `PairHelly`
-- ============================================================

/-- **Helly de parejas**: en un estado válido donde la regla no quita nada, todo tramo tiene entrada
común en cada paso. Estático: un solo estado, sin pasadas. -/
def PairHelly (C : GPathM) : Prop := isValid C = true → PairFixed C → SegGood C

/-- **Lo demás de `PStateG` tras la limpieza con parejas**: si allí vale `SegGood`, vale `PStateG`
entero. -/
def CleanRest (X : GPathM) : Prop :=
  isValid (cleanPair X) = true → SegGood (cleanPair X) → PStateG (cleanPair X)

/-- **La primera vuelta, desde `PairHelly`**: la limpieza con parejas deja `PairFixed`, `PairHelly`
da `SegGood`, `CleanRest` el resto de `PStateG`, y las dos pasadas lo conservan. -/
theorem pinFirstRound_of_pairHelly (X : GPathM) (hr : RevOk X) (hC : CleanRest X)
    (hH : PairHelly (cleanPair X)) : PinFirstRound X := by
  intro _ hv
  have hpr : Pruned (cleanPair X) (reviewPass X) :=
    Pruned.trans (pruned_reviewParents _) (pruned_reviewSons _)
  have hvc : isValid (cleanPair X) = true := Certifies.isValid_of_pruned hpr hv
  have hsg := hH hvc (pairFixed_cleanPair X hvc)
  exact (pstateG_reviewPass_of X hr (hC hvc hsg) hvc).1

/-- **El lector sin retroceso decide 3-SAT**, con `SegExact` en la línea final revisada (`hStart`) y,
en cada pin del lector, sobre el estado pinchado `X`: **Helly de parejas** tras la limpieza con
parejas (`PairHelly`), el resto de `PStateG` allí (`CleanRest`) y las vueltas siguientes listas
(`LaterValid`). `AggInactive` ya no es hipótesis (`aggInactive_of_revOk`). -/
theorem readerVerdictW_iff_of_pairHelly
    (hStart : ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ,
      isValid (filterAllAgg kv.2 []) = true → SegExact.SegExact (filterAllAgg kv.2 []))
    (hPin : ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      PairHelly (cleanPair (filterWeak g (q.id.step, [q.id]))) ∧
        CleanRest (filterWeak g (q.id.step, [q.id])) ∧
        LaterValid (filterWeak g (q.id.step, [q.id])))
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
    obtain ⟨hH, hC, hL⟩ := hPin φ' hwf' kv hkv g k q hR hv hk hq
    have hPX := pstateG_filterWeak g (q.id.step, [q.id]) hP
    have hr : RevOk (filterWeak g (q.id.step, [q.id])) :=
      ⟨hPX.nd, shapeOk_of_pstateG hPX, ownSymmetric_filterWeak g _ hS⟩
    have hgnX : GownersNodes.GN (filterWeak g (q.id.step, [q.id])) := fun r hr =>
      (ReaderAgg.RCtx_of_readableAgg g ctx.rd).gn r (List.mem_filter.mp hr).1
    rw [SegExactFilter.filterAllAgg_pin] at hv' ⊢
    exact segGood_pinReview _ hr hPX hgnX (pinFirstRound_of_pairHelly _ hr hC hH) hL
      (aggInactive_of_revOk _ hr) hv'

/-- info: 'AbsSat.GraphPath.Model.PairHelly.readerVerdictW_iff_of_pairHelly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_pairHelly


-- ============================================================
-- B7. Hacia `PairHelly`: la reducción a una cadena por el tramo y por el pin
-- ============================================================

/-- **El pin débil conserva las cadenas que pasan por el nodo pinchado**: solo quita de la global los
nodos de ese paso con otro nodo del mapa. -/
theorem chainSound_filterWeak (g : GPathM) (k : Int) (qid : NodeId) (sel : Int → PathNodeId)
    (h : ChainSound g sel) (hq : 0 ≤ k → k < g.current_step → (sel k).id = qid) :
    ChainSound (filterWeak g (k, [qid])) sel := by
  obtain ⟨⟨hchain, howned, hgow⟩, hself, hson, hroot⟩ := h
  refine ⟨⟨hchain, howned, ?_⟩, hself, hson, hroot⟩
  intro j hlo hhi
  simp only [filterWeak, List.mem_filter]
  refine ⟨hgow j hlo hhi, ?_⟩
  have hstepj := (hchain.1 j hlo hhi).2
  rcases int_eq_or_ne j k with hjk | hjk
  · subst hjk
    have hid : (sel j).id = qid := hq hlo hhi
    simp [hid]
  · simp only [Bool.or_eq_true]
    refine Or.inl ?_
    simp only [bne_iff_ne, hstepj]
    exact hjk

/-- **Un tramo de `C` que se extiende a una cadena sana de `X`**: la hipótesis que queda. -/
def SegThrough (X : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi ≤ (cleanPair X).current_step - 1 →
    Extendable.PartialChain (cleanPair X) sel lo hi →
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, (cleanPair X).node? (sel j) = some nj → sel i ∈ nj.owners) →
    ∃ s, ChainSound X s ∧ ∀ j, lo ≤ j → j ≤ hi → s j = sel j

/-- **`SegThrough` da `SegGood` tras la limpieza con parejas**: la cadena sana de `X` sigue sana en
`cleanPair X` (`ChainSound_cleanPair`), y su nodo en cada paso es la entrada común del tramo. -/
theorem segGood_of_segThrough (X : GPathM) (h : SegThrough X) : SegGood (cleanPair X) := by
  intro sel lo hi hlo hlh hhi hpc hpo i hi0 hi1 _
  obtain ⟨s, hs, hagree⟩ := h sel lo hi hlo hlh hhi hpc hpo
  have hC : ChainSound (cleanPair X) s := ChainSound_cleanPair X s hs
  have hstep : (cleanPair X).current_step = X.current_step := (pruned_cleanPair X).step_eq
  refine ⟨s i, (hC.chain.1.1 i hi0 (by omega)).2, ?_⟩
  intro j hj0 hj1 nj hnj
  rw [← hagree j hj0 hj1] at hnj
  exact chain_mem_owners (cleanPair X) s hC j (by omega) (by omega) nj hnj i hi0 (by omega)

/-- Y por tanto `PairHelly`. -/
theorem pairHelly_of_segThrough (X : GPathM) (h : SegThrough X) : PairHelly (cleanPair X) :=
  fun _ _ => segGood_of_segThrough X h

/-- **La forma sobre el estado del lector**: el tramo se extiende a una cadena sana de `g` **que pasa
por el nodo pinchado**. Es la afirmación abierta: sobre `g`, que ya cumple `SegExact`, y la regla. -/
def SegThroughPin (g : GPathM) (k : Int) (qid : NodeId) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi →
    hi ≤ (cleanPair (filterWeak g (k, [qid]))).current_step - 1 →
    Extendable.PartialChain (cleanPair (filterWeak g (k, [qid]))) sel lo hi →
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, (cleanPair (filterWeak g (k, [qid]))).node? (sel j) = some nj → sel i ∈ nj.owners) →
    ∃ s, ChainSound g s ∧ (0 ≤ k → k < g.current_step → (s k).id = qid) ∧
      ∀ j, lo ≤ j → j ≤ hi → s j = sel j

theorem segThrough_of_pin (g : GPathM) (k : Int) (qid : NodeId) (h : SegThroughPin g k qid) :
    SegThrough (filterWeak g (k, [qid])) := by
  intro sel lo hi hlo hlh hhi hpc hpo
  obtain ⟨s, hs, hk, hagree⟩ := h sel lo hi hlo hlh hhi hpc hpo
  exact ⟨s, chainSound_filterWeak g k qid s hs hk, hagree⟩

/-- **`PairHelly` en cada pin, desde `SegThroughPin`.** -/
theorem pairHelly_of_segThroughPin (g : GPathM) (k : Int) (qid : NodeId)
    (h : SegThroughPin g k qid) : PairHelly (cleanPair (filterWeak g (k, [qid]))) :=
  pairHelly_of_segThrough _ (segThrough_of_pin g k qid h)

/-- info: 'AbsSat.GraphPath.Model.PairHelly.pairHelly_of_segThroughPin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairHelly_of_segThroughPin

end AbsSat.GraphPath.Model.PairHelly
