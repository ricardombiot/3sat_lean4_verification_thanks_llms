-- lean_project/AbsSat/GraphPath/Model/TablesExact.lean
import AbsSat.GraphPath.Model.SendSeq

/-!
# Las tablas dicen la verdad

`q'` en la tabla de `r` (los dos en la tabla global) significa que hay una cadena completa dentro de
la global que pasa por los dos. Es lo que la tabla de owners **quiere decir**, y es lo que las parejas
de `PinPairs` y `SendPairs` piden en un solo paso.

Medido (`row-degree pairall`, `pairline`): 0 fallos en los estados del lector (293.377 parejas,
semilla 1), en la línea y en los estados intermedios del envío paso a paso.
-/

namespace AbsSat.GraphPath.Model.TablesExact

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.FullExt (FullChainG chainSound_of_fullChain fullChain_of_chainSound)
open AbsSat.GraphPath.Model.PinPairs (FrontierPairs)

/-- **Las tablas dicen la verdad**: cada pareja de la tabla de un nodo está en una cadena completa
dentro de la global. -/
def TablesExact (T : GPathM) : Prop :=
  ∀ r ∈ T.gowners, ∀ q' ∈ T.gowners, q'.id.step ≠ r.id.step →
    0 ≤ r.id.step → r.id.step < T.current_step →
    (∃ nr, T.node? r = some nr ∧ q' ∈ nr.owners) →
    ∃ s, FullChainG T s ∧ s r.id.step = r ∧ s q'.id.step = q'

/-- Las parejas de cualquier paso son un caso. -/
theorem frontierPairs_of_tablesExact (T : GPathM) (h : TablesExact T) (k : Int) :
    FrontierPairs T k := by
  intro r hr q' hq' hq's hne h0 h1 hown
  obtain ⟨s, hs, hsr, hsq⟩ := h r hr q' hq' (by rw [hq's]; exact fun e => hne e.symm) h0 h1 hown
  rw [hq's] at hsq
  exact ⟨s, hs, hsr, hsq⟩

/-- **El review sin filtro conserva la verdad de las tablas**: sus tablas son más pequeñas, y la
cadena del estado de antes es `ChainSound` y sobrevive. -/
theorem tablesExact_reviewAgg (g : GPathM) (hnd : NodupIds g)
    (hself : ∀ pid n, g.node? pid = some n → pid ∈ n.owners)
    (hsmp : Sons.SMP g) (hroot : Sons.RootAtZero g) (hnr : Parents.NotRoot g)
    (hpos : 0 < g.current_step) (h : TablesExact g) : TablesExact (reviewAgg g) := by
  have hpr := pruned_reviewAgg g
  rintro r hr q' hq' hne h0 h1 ⟨nr, hnrR, hown⟩
  obtain ⟨n0, hn0, hid, ho, _⟩ := hpr.nodes_derived nr (List.mem_of_find?_eq_some hnrR)
  have hn0g : g.node? r = some n0 := by
    have := node?_of_mem hnd n0 hn0
    rw [← hid, node?_id_eq _ r nr hnrR] at this
    exact this
  obtain ⟨s, hs, hsr, hsq⟩ := h r (hpr.gowners_sub r hr) q' (hpr.gowners_sub q' hq') hne h0
    (by rw [← hpr.step_eq]; exact h1) ⟨n0, hn0g, ho q' hown⟩
  exact ⟨s, fullChain_of_chainSound _ s (ChainSound_reviewAgg g s
    (chainSound_of_fullChain g hself hsmp hroot hnr hpos s hs)), hsr, hsq⟩

/-- info: 'AbsSat.GraphPath.Model.TablesExact.tablesExact_reviewAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesExact_reviewAgg

end AbsSat.GraphPath.Model.TablesExact
