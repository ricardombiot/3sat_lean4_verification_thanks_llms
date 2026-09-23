-- lean_project/AbsSat/GraphPath/Model/PinPairs.lean
import AbsSat.GraphPath.Model.Ladder1

/-!
# El pin del lector, desde las parejas con la frontera

`Ladder1.PinExt1` pide que el pin en `k = firstChoice` deje un revisado con `FullExt1`. Se reduce a
una frase sobre el estado **antes** del pin:

    FrontierPairs g k  :=  si q' (paso k) está en la tabla de r, ambos en la global,
                           hay una cadena completa dentro de la global por r y por q'

La razón: una entrada `r` que sobrevive al pin es válida, así que su tabla tiene una entrada `q'` en
el paso `k`, y en la global solo queda el id pinchado. La cadena por `r` y `q'` pasa el filtro, es
`ChainSound` y sobrevive al review. Una entrada del propio paso `k` sale de `FullExt1`.

Medido (`row-degree pairext`, en la dirección que el review da): 0 fallos, 83 parejas en
`dos_de_tres.cnf`, 3.232 en la semilla 1 y 3.256 en la 7.
-/

namespace AbsSat.GraphPath.Model.PinPairs

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.TopGoodUp (Seg)
open AbsSat.GraphPath.Model.FullExt (FullChainG chainSound_of_fullChain fullChain_of_chainSound)
open AbsSat.GraphPath.Model.FullExt1

/-- **Las parejas con la frontera tienen cadena común.** -/
def FrontierPairs (g : GPathM) (k : Int) : Prop :=
  ∀ r ∈ g.gowners, ∀ q' ∈ g.gowners, q'.id.step = k → r.id.step ≠ k →
    0 ≤ r.id.step → r.id.step < g.current_step →
    (∃ nr, g.node? r = some nr ∧ q' ∈ nr.owners) →
    ∃ s, FullChainG g s ∧ s r.id.step = r ∧ s k = q'

/-- **Una cadena completa del estado que en el paso pinchado lleva el id pinchado sobrevive al pin.** -/
theorem fullChain_pin (g : GPathM) (hself : Ownership.SelfOwned g) (hsmp : Sons.SMP g)
    (hroot : Sons.RootAtZero g) (hnr : Parents.NotRoot g) (hpos : 0 < g.current_step)
    (q : PathNodeId) (s : Int → PathNodeId) (hs : FullChainG g s) (hsq : (s q.id.step).id = q.id) :
    FullChainG (filterAllAgg g [q.id]) s := by
  obtain ⟨hnodes, hcs⟩ := ReaderLadder.foldl_filterRequire_nodes [q.id] g
  let X := [q.id].foldl filterRequire g
  have hnode : ∀ y, X.node? y = g.node? y := by intro y; simp only [node?, X, hnodes]
  have hX : FullChainG X s := by
    refine ⟨?_, fun j hj0 hj1 => ?_⟩
    · have h1 := hs.1
      simp only [Seg, Extendable.PartialChain] at h1 ⊢
      simp only [hnode, X, hcs]
      exact h1
    · rw [show X.current_step = g.current_step from hcs] at hj1
      refine ReaderLadder.mem_gowners_foldl_filterRequire [q.id] g (s j) (hs.2 j hj0 hj1)
        (fun r hr hrs => ?_)
      rw [List.mem_singleton.mp hr] at hrs ⊢
      have hjs := (hs.1.1.1 j hj0 hj1).2
      rw [← hsq, ← hrs, hjs]
  have hself' : ∀ pid n, X.node? pid = some n → pid ∈ n.owners :=
    fun pid n h => hself pid n (by rw [← hnode]; exact h)
  have hsmp' : Sons.SMP X := by intro n hn; rw [hnodes] at hn ⊢; exact hsmp n hn
  have hroot' : Sons.RootAtZero X := by intro n hn; rw [hnodes] at hn; exact hroot n hn
  have hnr' : Parents.NotRoot X := by intro n hn; rw [hnodes] at hn; exact hnr n hn
  exact fullChain_of_chainSound _ s (ChainSound_reviewAgg X s
    (chainSound_of_fullChain X hself' hsmp' hroot' hnr' (by rw [hcs]; exact hpos) s hX))

/-- **El pin conserva `FullExt1`, desde las parejas con la frontera.** -/
theorem fullExt1_pin (g : GPathM) (ctx : PinAliveChain.DCtx g) (hv : isValid g = true)
    (hF : FullExt1 g) (q : PathNodeId) (hq0 : 0 ≤ q.id.step) (hq1 : q.id.step < g.current_step)
    (hP : FrontierPairs g q.id.step)
    (hv' : isValid (filterAllAgg g [q.id]) = true) : FullExt1 (filterAllAgg g [q.id]) := by
  have rc := RCtx_of_readableAgg g ctx.rd
  have hself := ReaderLadder.selfOwned_of_readable g ctx.rd hv
  let R := filterAllAgg g [q.id]
  have hprR : Pruned g R := pruned_filterAllAgg g [q.id]
  have ctxR := PinAliveChain.DCtx_filterAllAgg g ctx [q.id]
  have cR := Reader.Ctx_of_readable R (readable_of_readableAgg R ctxR.rd) hv'
  have hcsR : R.current_step = g.current_step := hprR.step_eq
  have keep := fullChain_pin g hself ctx.smp rc.rootz rc.shape.notroot ctx.pos q
  have clean : ∀ y ∈ R.gowners, y.id.step = q.id.step → y.id = q.id :=
    fun y hy hys => ReaderAggRun.filterAllAgg_cleans g [q.id] q.id List.mem_cons_self y hy hys
  intro r hr hr0 hr1
  rw [hcsR] at hr1
  have hrg : r ∈ g.gowners := hprR.gowners_sub r hr
  rcases int_eq_or_ne r.id.step q.id.step with hk | hk
  · -- una entrada del paso pinchado: su propia cadena
    obtain ⟨s, hs, hsr⟩ := hF r hrg hr0 hr1
    exact ⟨s, keep s hs (by rw [← hk, hsr]; exact clean r hr hk), hsr⟩
  · -- la tabla de `r` en el revisado tiene una entrada `q'` en el paso pinchado
    obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp
      ((GownersNodes.hasNode_iff R r).mp (cR.gn r hr))
    have hall := owners_ok_of_isValidNode R nr (cR.nodeval r nr hnr)
    have hent : hasStepEntry nr.owners q.id.step = true :=
      List.all_eq_true.mp hall q.id.step (mem_intRange hq0 (by rw [hcsR]; omega))
    obtain ⟨q', hq', hq's⟩ := List.any_eq_true.mp hent
    have hq's' : q'.id.step = q.id.step := eq_of_beq hq's
    have hq'R : q' ∈ R.gowners :=
      cR.ownGow r nr hnr q' hq' (by rw [hq's']; exact hq0) (by rw [hq's', hcsR]; exact hq1)
    -- y la misma relación en el estado de antes
    obtain ⟨n0, hn0, hid, hown, _⟩ := hprR.nodes_derived nr (List.mem_of_find?_eq_some hnr)
    have hn0g : g.node? r = some n0 := by
      have := node?_of_mem rc.nodup n0 hn0
      rw [← hid, node?_id_eq R r nr hnr] at this
      exact this
    obtain ⟨s, hs, hsr, hsk⟩ := hP r hrg q' (hprR.gowners_sub q' hq'R) hq's' hk hr0 hr1
      ⟨n0, hn0g, hown q' hq'⟩
    exact ⟨s, keep s hs (by rw [hsk]; exact clean q' hq'R hq's'), hsr⟩

/-- info: 'AbsSat.GraphPath.Model.PinPairs.fullExt1_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullExt1_pin

/-- **Lo que el lector debe dar**: en cada estado que visita, las parejas con su frontera tienen
cadena común. -/
def PinPairs : Prop :=
  ∀ g : GPathM, PinAliveChain.DCtx g → isValid g = true → FullExt1 g →
    ∀ k, ReaderExec.firstChoice g = some k → FrontierPairs g k

theorem pinExt1_of_pinPairs (h : PinPairs) : Ladder1.PinExt1 := by
  intro g ctx hv hF q _ hq0 hq1 hfc hv'
  exact fullExt1_pin g ctx hv hF q hq0 hq1 (h g ctx hv hF _ hfc) hv'

/-- **El lector sin retroceso decide 3-SAT**: el revisado de cada envío cumple `FullExt1`
(`SendExt1`), y en cada estado del lector las parejas con la frontera tienen cadena común
(`PinPairs`). -/
theorem readerVerdictW_iff_of_pairs (hS : ∀ ψ : Cnf, WF ψ → Ladder1.SendExt1 ψ) (hP : PinPairs)
    (φ : Cnf) (hwf : WF φ) : ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  Ladder1.readerVerdictW_iff_of_ext1 φ hS (pinExt1_of_pinPairs hP) hwf

/-- info: 'AbsSat.GraphPath.Model.PinPairs.readerVerdictW_iff_of_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_pairs

end AbsSat.GraphPath.Model.PinPairs
