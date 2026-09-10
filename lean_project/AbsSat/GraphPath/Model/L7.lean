-- lean_project/AbsSat/GraphPath/Model/L7.lean
import AbsSat.GraphPath.Model.CnfChain
import AbsSat.GraphMap.CnfSel

/-!
# L7 — the bridge between the machine and 3SAT

`Verdict.lean` said what was missing:

> Nothing here connects `denot` to satisfying assignments of the original CNF.
> That link — "every chain decodes to a model of the formula" — is a separate
> obligation, and it lives on the map side, and phase L7.

This module is that link.

    sat_of_inhabited : MapReachable φ g → Inhabited g → ∃ a, Sat a φ

Everything it needs was already there or is proved in the four modules below
it: `L1_cor` turns a co-owned chain into a requirement-satisfying one (that
theorem *is* `ReqSatisfying`, pointwise, and it was proved for phase F5);
`CnfMap.reqOfCnf_backward` and `reqOfCnf_functional` discharge what
`Reachable.up` asks of the map; `MapReachable` supplies the invariant
`Reachable` does not; and `CnfChain.sat_of_reqSatisfying` does the decode.

## What this does **not** close

`sat_of_inhabited` says: *if* the machine holds a valid graph that denotes
something, *then* `φ` is satisfiable. `Inhabited g` is the open half — link 3
of the five, the one the whole `PairwiseOwned` / `PickValid` / `support` family
is about. This closes links 1 and 4, so the day link 3 falls the final theorem
assembles; it does not close the verdict on its own.

The completeness direction stops at the map, deliberately: `reqSatisfying_of_sat`
says every satisfying assignment yields a selection that satisfies the map's
requirements and lands on nodes the map builds, and `decode_selOfAssign` says
the two directions agree. Neither claims that selection is an `IsChain` in any
particular `g` — lifting it through the machine's filtering is L2⊇, and that is
the open problem again.
-/

namespace AbsSat.GraphPath.Model.L7

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.CnfChain

/-- **Soundness: a chain the machine holds decodes to a model of the formula.** -/
theorem sat_of_inhabited (φ : Cnf) (hwf : WF φ) (g : GPathM)
    (hmr : MapReachable φ g) (hcs : g.current_step = stepCount φ)
    (hinh : AbsSat.GraphPath.Model.Inhabited g) :
    ∃ a : Assign, Sat a φ := by
  obtain ⟨_, sel, hchain, howned, _⟩ := hinh
  have hreach : Reachable (reqOfCnf φ) g := reachable_of_mapReachable φ hwf g hmr
  have hrs : MapChain.ReqSatisfying (reqOfCnf φ) g sel := by
    intro k hk0 hk req hreq hr0 hr1
    exact L1_cor (reqOfCnf φ) hreach hchain howned k hk0 hk req hreq hr0 hr1
  have hcm : ChainOnMap φ g sel :=
    chainOnMap_of_nodesOnMap φ g (nodesOnMap_of_mapReachable φ g hmr) sel hchain
  exact ⟨decode sel, sat_of_reqSatisfying φ g sel hwf hcs hchain hrs hcm⟩

/-- The same, stated as `Satisfiable`. -/
theorem satisfiable_of_inhabited (φ : Cnf) (hwf : WF φ) (g : GPathM)
    (hmr : MapReachable φ g) (hcs : g.current_step = stepCount φ)
    (hinh : AbsSat.GraphPath.Model.Inhabited g) : Satisfiable φ :=
  sat_of_inhabited φ hwf g hmr hcs hinh

-- ============================================================
-- The other direction, as far as it goes without the open problem
-- ============================================================

/-- **The map-level half of completeness.** Every satisfying assignment names a
selection that satisfies the map's requirements *and* lands on nodes the map
actually builds.

The two halves are proved separately on purpose: the requirement bookkeeping
(`reqSat_selOfAssign`) needs no satisfiability at all, and `Sat` enters in
exactly one place (`selOfAssign_onMap`) — a satisfied clause names a row other
than `000`, the one row the map omits.

**This is not a chain in `g`.** Nothing here claims the selection is parent
linked or that it survives the machine's filtering; that lifting is L2⊇, which
is the open problem. What it does give is the map-side obligation phase L7
owed, discharged. -/
theorem reqSatisfying_of_sat (φ : Cnf) (hwf : WF φ) (a : Assign) (hsat : Sat a φ)
    (g : GPathM) (hcs : g.current_step = stepCount φ) :
    MapChain.ReqSatisfying (reqOfCnf φ) g (fun k => ⟨selOfAssign φ a k, none⟩)
      ∧ ChainOnMap φ g (fun k => ⟨selOfAssign φ a k, none⟩) := by
  constructor
  · intro k hk0 hk req hreq _ _
    exact reqSat_selOfAssign φ hwf a k req hreq
  · intro k hk0 hk
    exact selOfAssign_onMap φ a hsat k hk0 (by rw [← hcs]; exact hk)

/-- **The two directions agree.** Decoding the selection an assignment names
gives that assignment back, on every variable the formula has. -/
theorem decode_selOfAssign (φ : Cnf) (a : Assign) (v : Nat) (hv : v < φ.nVars) :
    decode (fun k => ⟨selOfAssign φ a k, none⟩) v = a v := by
  have hsel : (selOfAssign φ a (2 * (v : Int))).index = bit (a v) := by
    have h := selOfAssign_var φ a v hv
    simp only [varStep] at h
    rw [h]
  simp only [decode]
  rw [hsel]
  exact bit_eq_one_iff (a v)

/-- info: 'AbsSat.GraphPath.Model.L7.sat_of_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_inhabited

/-- info: 'AbsSat.GraphPath.Model.L7.reqSatisfying_of_sat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reqSatisfying_of_sat

/-- info: 'AbsSat.GraphPath.Model.L7.decode_selOfAssign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decode_selOfAssign

end AbsSat.GraphPath.Model.L7
