-- lean_project/AbsSat/GraphPath/Model/NodeLevel.lean
import AbsSat.GraphPath.Model.ReaderComplete

/-!
# The review, split in two levels: nodes (proved) and pairs (open)

The author's decomposition of the base review (v142): the **global clean** removes the nodes with which no
path can be built any more; the **coherence with parents and sons** cleans the owner tables of the entries
with which no path can be formed any more. Measured (probe `helly ghosts`, every map pin of every exact
state of K4 and parity): after the clean **no ghost node is left** (0 of 143,791 live nodes), and parents
and sons remove **no** node — they only clean entries.

This module proves the node level, and reduces the reader's hypothesis to the pair level:

* **`node_sound_of_pin`** — *pinning one map node on a valid exact reader's state and reviewing leaves
  only nodes that lie on a surviving path.* A surviving node is valid, so it owns something at the
  pinned step; that owner carries the pin; the state was exact, so a path goes through the node and that
  owner — and it passes the pin.
* **`PairPinExact`** — the pair level: every entry between two **distinct** nodes of the pinned, reviewed
  state lies on a surviving path.
* **`readerPinExact_of_pairs`** — the node level and the pair level together are `ReaderPinExact`: what is
  left open of the reader's hypothesis is **only the pairs**.
-/

namespace AbsSat.GraphPath.Model.NodeLevel

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes)
open AbsSat.GraphPath.Model.ReaderComplete (ReaderPinExact pin_id)

/-- **The node level.** Pinning one map node on a valid exact reader's state and reviewing leaves only
nodes that lie on a surviving path. -/
theorem node_sound_of_pin (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true)
    (ht : TablesSound g) (r : NodeId) (hvr : isValid (filterAllAgg g [r]) = true)
    (x : PathNodeId) (n : PNodeM) (hx : (filterAllAgg g [r]).node? x = some n)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < (filterAllAgg g [r]).current_step) :
    Realizes (filterAllAgg g [r]) x x := by
  have hRr : ReadableAgg (filterAllAgg g [r]) := ReadableAgg_filterAllAgg g hR [r]
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
  have rcg := RCtx_of_readableAgg g hR
  have ctxg := Reader.Ctx_of_readable g (readable_of_readableAgg g hR) hv
  have hpr := pruned_filterAllAgg g [r]
  have hcs : (filterAllAgg g [r]).current_step = g.current_step := hpr.step_eq
  -- `x` is a node of `g` too, with a larger table
  have hmem := List.mem_of_find?_eq_some hx
  obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n hmem
  have hxid := node?_id_eq _ x n hx
  have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
  -- a chain of `g` through `x` and a node carrying the pin survives the pin
  have lift : ∀ sel, ChainSound g sel → sel x.id.step = x →
      (0 ≤ r.step → r.step < g.current_step → (sel r.step).id = r) → Realizes (filterAllAgg g [r]) x x := by
    intro sel hsc hsx hpin
    refine ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq h0 h1 => ?_), hsx, hsx⟩
    rw [List.mem_singleton.mp hreq] at h0 h1 ⊢
    exact hpin h0 h1
  by_cases hin : 0 ≤ r.step ∧ r.step < g.current_step
  · -- the node owns something at the pinned step, and that owner carries the pin
    have hok := owners_ok_of_isValidNode _ n (ctxR.nodeval x n hx)
    simp only [List.all_eq_true] at hok
    have hent := hok r.step (mem_intRange hin.1 (by rw [hcs]; omega))
    obtain ⟨z, hz, hzs⟩ := List.any_eq_true.mp hent
    have hzs' : z.id.step = r.step := eq_of_beq hzs
    have hzg := ctxR.ownGow x n hx z hz (by omega) (by rw [hcs]; omega)
    have hzr : z.id = r := pin_id g r z hzg hzs'
    obtain ⟨sel, hsc, hsx, hsz⟩ := ht x n₀ hx₀ hx0 (by rw [← hcs]; exact hx1) z (by omega) (by omega)
      (hown z hz)
    refine lift sel hsc hsx (fun _ _ => ?_)
    rw [← hzs', hsz, hzr]
  · -- the pin is outside the steps: the chain through `x` alone survives
    obtain ⟨sel, hsc, hsx, _⟩ := ht x n₀ hx₀ hx0 (by rw [← hcs]; exact hx1) x hx0 (by rw [← hcs]; exact hx1)
      (ctxg.self x n₀ hx₀)
    exact lift sel hsc hsx (fun h0 h1 => absurd ⟨h0, h1⟩ hin)

/-- **The pair level**: every entry between two distinct nodes of the pinned, reviewed state lies on a
surviving path. -/
def PairPinExact : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → TablesSound g →
    ∀ r : NodeId, isValid (filterAllAgg g [r]) = true →
      ∀ x n, (filterAllAgg g [r]).node? x = some n → 0 ≤ x.id.step →
        x.id.step < (filterAllAgg g [r]).current_step →
        ∀ q, 0 ≤ q.id.step → q.id.step < (filterAllAgg g [r]).current_step → q ∈ n.owners → q ≠ x →
          Realizes (filterAllAgg g [r]) x q

/-- **What is open of the reader's hypothesis is only the pairs.** -/
theorem readerPinExact_of_pairs (h : PairPinExact) : ReaderPinExact := by
  intro g hR hv ht r hvr x n hx hx0 hx1 q hq0 hq1 hqn
  by_cases hqx : q = x
  · rw [hqx]
    exact node_sound_of_pin g hR hv ht r hvr x n hx hx0 hx1
  · exact h g hR hv ht r hvr x n hx hx0 hx1 q hq0 hq1 hqn hqx

/-- info: 'AbsSat.GraphPath.Model.NodeLevel.node_sound_of_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms node_sound_of_pin

/-- info: 'AbsSat.GraphPath.Model.NodeLevel.readerPinExact_of_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerPinExact_of_pairs

end AbsSat.GraphPath.Model.NodeLevel
