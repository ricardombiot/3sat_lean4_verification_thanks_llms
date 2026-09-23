-- lean_project/AbsSat/GraphPath/Model/StepFilter.lean
import AbsSat.GraphPath.Model.PinPairs

/-!
# Un filtro de un paso, desde las parejas

`PinPairs.fullExt1_pin` para cualquier filtro que toca **un solo paso**: `filterWeak T (k, A)` deja en
el paso `k` solo las entradas cuyo id está en `A`. Un requisito duro es el caso `A = [req]`, y el
filtro débil de un envío es una sucesión de ellos.

El argumento es el mismo: una entrada `r` que sobrevive al review es válida, así que su tabla tiene
una entrada `q'` del paso `k`, y en la global ese paso solo guarda ids de `A`. La cadena común de `r`
y `q'` pasa el filtro, es `ChainSound` y sobrevive al review.
-/

namespace AbsSat.GraphPath.Model.StepFilter

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeak)
open AbsSat.GraphPath.Model.TopGoodUp (Seg)
open AbsSat.GraphPath.Model.FullExt (FullChainG chainSound_of_fullChain fullChain_of_chainSound)
open AbsSat.GraphPath.Model.FullExt1
open AbsSat.GraphPath.Model.PinPairs (FrontierPairs)

theorem mem_filterWeak (T : GPathM) (e : Int × List NodeId) (y : PathNodeId) :
    y ∈ (filterWeak T e).gowners ↔ y ∈ T.gowners ∧ (y.id.step = e.1 → y.id ∈ e.2) := by
  simp only [filterWeak, List.mem_filter, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.contains_iff_mem]
  constructor
  · rintro ⟨h, h2⟩
    refine ⟨h, fun hs => ?_⟩
    rcases h2 with h2 | h2
    · exact absurd hs h2
    · exact h2
  · rintro ⟨h, h2⟩
    refine ⟨h, ?_⟩
    if hs : y.id.step = e.1 then exact Or.inr (h2 hs) else exact Or.inl hs

/-- **Una cadena completa que en el paso filtrado lleva un id admitido sobrevive al filtro y al
review.** -/
theorem fullChain_stepFilter (T : GPathM) (e : Int × List NodeId) (hself : Ownership.SelfOwned T)
    (hsmp : Sons.SMP T) (hroot : Sons.RootAtZero T) (hnr : Parents.NotRoot T)
    (hpos : 0 < T.current_step) (s : Int → PathNodeId) (hs : FullChainG T s)
    (hse : (s e.1).id ∈ e.2) : FullChainG (reviewAgg (filterWeak T e)) s := by
  let X := filterWeak T e
  have hnode : ∀ y, X.node? y = T.node? y := fun _ => rfl
  have hcs : X.current_step = T.current_step := rfl
  have hX : FullChainG X s := by
    refine ⟨hs.1, fun j hj0 hj1 => (mem_filterWeak T e (s j)).mpr ⟨hs.2 j hj0 hj1, fun hjs => ?_⟩⟩
    have hj := (hs.1.1.1 j hj0 hj1).2
    rw [hj] at hjs
    rw [hjs]
    exact hse
  have hself' : ∀ pid n, X.node? pid = some n → pid ∈ n.owners :=
    fun pid n h => hself pid n (by rw [← hnode]; exact h)
  exact fullChain_of_chainSound _ s (ChainSound_reviewAgg X s
    (chainSound_of_fullChain X hself' hsmp hroot hnr (by rw [hcs]; exact hpos) s hX))

/-- **Un filtro de un paso conserva `FullExt1`, desde las parejas de ese paso.** -/
theorem fullExt1_stepFilter (T : GPathM) (e : Int × List NodeId) (rc : Reader.RCtx T)
    (hsmp : Sons.SMP T) (hself : Ownership.SelfOwned T) (hpos : 0 < T.current_step)
    (hF : FullExt1 T) (he0 : 0 ≤ e.1) (he1 : e.1 < T.current_step) (hP : FrontierPairs T e.1)
    (hv' : isValid (reviewAgg (filterWeak T e)) = true) :
    FullExt1 (reviewAgg (filterWeak T e)) := by
  let R := reviewAgg (filterWeak T e)
  have hprX : Pruned (filterWeak T e) R := pruned_reviewAgg _
  have hprR : Pruned T R := Pruned.trans (ConservationCore.pruned_filterWeak T e) hprX
  have rcX : Reader.RCtx (filterWeak T e) := RCtx_of_keeps (ReaderAggRun.keeps_filterWeak T e) rc
  have hRd : ReadableAgg R := ⟨filterWeak T e, [], rcX, rfl⟩
  have cR := Reader.Ctx_of_readable R (readable_of_readableAgg R hRd) hv'
  have hcsR : R.current_step = T.current_step := hprR.step_eq
  have keep := fullChain_stepFilter T e hself hsmp rc.rootz rc.shape.notroot hpos
  have clean : ∀ y ∈ R.gowners, y.id.step = e.1 → y.id ∈ e.2 :=
    fun y hy hys => ((mem_filterWeak T e y).mp (hprX.gowners_sub y hy)).2 hys
  intro r hr hr0 hr1
  rw [hcsR] at hr1
  have hrg : r ∈ T.gowners := hprR.gowners_sub r hr
  rcases int_eq_or_ne r.id.step e.1 with hk | hk
  · obtain ⟨s, hs, hsr⟩ := hF r hrg hr0 hr1
    exact ⟨s, keep s hs (by rw [← hk, hsr]; exact clean r hr hk), hsr⟩
  · obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp
      ((GownersNodes.hasNode_iff R r).mp (cR.gn r hr))
    have hall := owners_ok_of_isValidNode R nr (cR.nodeval r nr hnr)
    have hent : hasStepEntry nr.owners e.1 = true :=
      List.all_eq_true.mp hall e.1 (mem_intRange he0 (by rw [hcsR]; omega))
    obtain ⟨q', hq', hq's⟩ := List.any_eq_true.mp hent
    have hq's' : q'.id.step = e.1 := eq_of_beq hq's
    have hq'R : q' ∈ R.gowners :=
      cR.ownGow r nr hnr q' hq' (by rw [hq's']; exact he0) (by rw [hq's', hcsR]; exact he1)
    obtain ⟨n0, hn0, hid, hown, _⟩ := hprR.nodes_derived nr (List.mem_of_find?_eq_some hnr)
    have hn0g : T.node? r = some n0 := by
      have := node?_of_mem rc.nodup n0 hn0
      rw [← hid, node?_id_eq R r nr hnr] at this
      exact this
    obtain ⟨s, hs, hsr, hsk⟩ := hP r hrg q' (hprR.gowners_sub q' hq'R) hq's' hk hr0 hr1
      ⟨n0, hn0g, hown q' hq'⟩
    exact ⟨s, keep s hs (by rw [hsk]; exact clean q' hq'R hq's'), hsr⟩

/-- info: 'AbsSat.GraphPath.Model.StepFilter.fullExt1_stepFilter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullExt1_stepFilter

-- ============================================================
-- Una sucesión de filtros de un paso
-- ============================================================

/-- Un filtro de un paso y su review. -/
def seqStep (T : GPathM) (e : Int × List NodeId) : GPathM := reviewAgg (filterWeak T e)

/-- **El envío hecho paso a paso**: cada filtro de un paso seguido de su review. -/
def seqSend (T : GPathM) (es : List (Int × List NodeId)) : GPathM := es.foldl seqStep T

theorem pruned_seqStep (T : GPathM) (e : Int × List NodeId) : Pruned T (seqStep T e) :=
  Pruned.trans (ConservationCore.pruned_filterWeak T e) (pruned_reviewAgg _)

theorem pruned_seqSend : ∀ (es : List (Int × List NodeId)) (T : GPathM), Pruned T (seqSend T es)
  | [], T => Pruned.refl T
  | e :: es, T => Pruned.trans (pruned_seqStep T e) (pruned_seqSend es (seqStep T e))

/-- Lo que el argumento necesita del estado de partida de cada filtro. -/
structure SCtx (T : GPathM) : Prop where
  rc : Reader.RCtx T
  smp : Sons.SMP T
  self : Ownership.SelfOwned T
  pos : 0 < T.current_step

theorem sctx_seqStep (T : GPathM) (e : Int × List NodeId) (c : SCtx T)
    (hv : isValid (seqStep T e) = true) : SCtx (seqStep T e) := by
  have rcX : Reader.RCtx (filterWeak T e) := RCtx_of_keeps (ReaderAggRun.keeps_filterWeak T e) c.rc
  have hRd : ReadableAgg (seqStep T e) := ⟨filterWeak T e, [], rcX, rfl⟩
  exact ⟨RCtx_of_readableAgg _ hRd,
    AnchoredSurvive.SMP_filterAllAgg (filterWeak T e) c.smp c.rc.shape.notroot [],
    ReaderLadder.selfOwned_of_readable _ hRd hv,
    by rw [(pruned_seqStep T e).step_eq]; exact c.pos⟩

/-- **Las parejas a lo largo de la sucesión**: en cada estado intermedio, las del paso que se va a
filtrar. -/
def StepsPairs : GPathM → List (Int × List NodeId) → Prop
  | _, [] => True
  | T, e :: es => 0 ≤ e.1 ∧ e.1 < T.current_step ∧ FrontierPairs T e.1 ∧ StepsPairs (seqStep T e) es

/-- **La sucesión conserva `FullExt1`**, filtro a filtro, desde las parejas de cada paso. -/
theorem fullExt1_seqSend : ∀ (es : List (Int × List NodeId)) (T : GPathM), SCtx T → FullExt1 T →
    StepsPairs T es → isValid (seqSend T es) = true → FullExt1 (seqSend T es)
  | [], _, _, hF, _, _ => hF
  | e :: es, T, c, hF, ⟨he0, he1, hP, hrest⟩, hv => by
    have hv1 : isValid (seqStep T e) = true :=
      Certifies.isValid_of_pruned (pruned_seqSend es (seqStep T e)) hv
    exact fullExt1_seqSend es (seqStep T e) (sctx_seqStep T e c hv1)
      (fullExt1_stepFilter T e c.rc c.smp c.self c.pos hF he0 he1 hP hv1) hrest hv

/-- info: 'AbsSat.GraphPath.Model.StepFilter.fullExt1_seqSend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullExt1_seqSend

end AbsSat.GraphPath.Model.StepFilter
