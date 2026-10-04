-- lean/improves_bin/AbsSatBin/GraphPath/Model/L7.lean
import AbsSatBin.GraphPath.Model.CnfChain
import AbsSatBin.GraphMap.CnfSelBin

/-!
# L7 — the bridge between the machine and 3SAT, on the bin map — **rewritten**

    sat_of_inhabited : MapReachable φ g → Inhabited g → ∃ a, Sat a φ

As in `lean_project`: `L1_cor` turns a co-owned chain into a requirement-satisfying one,
`MapReachable` supplies the map-side invariants, and `CnfChain.sat_of_reqSatisfying` decodes.
The bin map adds two ingredients the decode now needs: `NoForb` (no node of the graph is a
prohibited window) and the parent coherence of `ParentId` (`PMP`, `GPMP`), which lets the decode
read the window a chain carries at the third literal of a clause.

The completeness direction stops at the map, as in `lean_project`: `reqSatisfying_of_sat` gives
a selection that satisfies the requirements and lands on the map — **for any assignment** now —
and `pidOfAssign_not_prohibited` (in `CnfSelBin`) is where `Sat` enters.
-/

namespace AbsSatBin.GraphPath.Model.L7

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.MapReachable
open AbsSatBin.GraphPath.Model.CnfChain

/-- **Soundness: a chain the machine holds decodes to a model of the formula.** -/
theorem sat_of_inhabited (φ : Cnf) (hbd : Bounded φ) (g : GPathM)
    (hmr : MapReachable φ g) (hcs : g.current_step = stepCount φ)
    (hinh : AbsSatBin.GraphPath.Model.Inhabited g) :
    ∃ a : Assign, Sat a φ := by
  obtain ⟨_, sel, hchain, howned, _⟩ := hinh
  have hreach : Reachable (reqOf φ) (isProhibited φ) g := reachable_of_mapReachable φ hbd g hmr
  have hrs : MapChain.ReqSatisfying (reqOf φ) g sel := by
    intro k hk0 hk req hreq hr0 hr1
    exact L1_cor (reqOf φ) (isProhibited φ) hreach hchain howned k hk0 hk req hreq hr0 hr1
  have hcm : ChainOnMap φ g sel :=
    chainOnMap_of_nodesOnMap φ g (nodesOnMap_of_mapReachable φ g hmr) sel hchain
  exact ⟨decode sel, sat_of_reqSatisfying φ g sel hbd hcs hchain hrs hcm
    (noForb_of_mapReachable φ g hmr)
    (ParentId.PMP_reachable (reqOf φ) (isProhibited φ) g hreach)
    (ParentId.GPMP_reachable (reqOf φ) (isProhibited φ) g hreach)⟩

/-- The same, stated as `Satisfiable`. -/
theorem satisfiable_of_inhabited (φ : Cnf) (hbd : Bounded φ) (g : GPathM)
    (hmr : MapReachable φ g) (hcs : g.current_step = stepCount φ)
    (hinh : AbsSatBin.GraphPath.Model.Inhabited g) : Satisfiable φ :=
  sat_of_inhabited φ hbd g hmr hcs hinh

-- ============================================================
-- The other direction, at the map
-- ============================================================

/-- **The map-level half of completeness.** Every assignment's selection satisfies the map's
requirements and lands on nodes the map builds — no `Sat` on the bin map. -/
theorem reqSatisfying_of_assign (φ : Cnf) (hbd : Bounded φ) (a : Assign)
    (g : GPathM) (hcs : g.current_step = stepCount φ) :
    MapChain.ReqSatisfying (reqOf φ) g (fun k => ⟨selOfAssign φ a k, none, none⟩)
      ∧ ChainOnMap φ g (fun k => ⟨selOfAssign φ a k, none, none⟩) := by
  constructor
  · intro k hk0 hk req hreq _ _
    exact reqSat_selOfAssign φ hbd a k req hreq
  · intro k hk0 hk
    exact selOfAssign_onMap φ a k hk0 (by rw [← hcs]; exact hk)

/-- **The two directions agree.** Decoding the selection an assignment names gives that
assignment back, on every variable the formula has. -/
theorem decode_selOfAssign (φ : Cnf) (a : Assign) (v : Nat) (hv : v < φ.nVars) :
    decode (fun k => ⟨selOfAssign φ a k, none, none⟩) v = a v := by
  simp only [decode, selOfAssign_var φ a v hv]
  cases a v <;> rfl

/-- info: 'AbsSatBin.GraphPath.Model.L7.sat_of_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_inhabited

/-- info: 'AbsSatBin.GraphPath.Model.L7.decode_selOfAssign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decode_selOfAssign

end AbsSatBin.GraphPath.Model.L7
