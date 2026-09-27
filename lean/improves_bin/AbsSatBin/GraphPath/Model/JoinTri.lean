-- lean/improves_bin/AbsSatBin/GraphPath/Model/JoinTri.lean
import AbsSatBin.GraphPath.Model.Splice

/-!
# `CliqueTri` through the join

Measured (`julia/improves_bin/test_3sat/probes/cliquetri*_probe.jl`, `docs/context/ambfar.md` §4.2ν): `CliqueTri` (the
pair rule relative to a clique, with one round of cuts) holds at every stage of the machine — filtered sources, pieces
and joined states — for cliques of 1 to 4 nodes, with the corrected review. The joined state is the union of its pieces
with **no review after it**, so there `CliqueTri` must come from the pieces.

* **`cxP_grown`**: a `P`-compatible link climbs to a state the first one grows into.
* **`cliqueTri_of_joinChoice`**: if states that all grow into `J` have `CliqueTri`, and every `P`-compatible link of `J`
  (with `P` a clique of `J`) is already one of a single such state, with `P` a clique there (`JoinChoiceP`), then `J` has
  `CliqueTri`: the witness the state gives climbs to `J`.
* **`cliqueTri_line_of_pieces`**: the instance for a state of line `n+1` and its pieces.
-/

namespace AbsSatBin.GraphPath.Model.JoinTri

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.CliqueTri

/-- A `P`-compatible link climbs to a state the first one grows into. -/
theorem cxP_grown {X J : GPathM} (hgr : Grown X J) {P : List PathNodeId} {ny nyJ : PNodeM} {w : PathNodeId}
    (hsub : ∀ q ∈ ny.owners, q ∈ nyJ.owners) (h : CxP X P ny w) : CxP J P nyJ w := by
  obtain ⟨nw, hnw, hwy, hl⟩ := h
  obtain ⟨nwJ, hnwJ, hownw, _, _⟩ := hgr.node?_grown w nw hnw
  refine ⟨nwJ, hnwJ, hsub w hwy, fun l h0 h1 => ?_⟩
  obtain ⟨r, hr, hrw, hrs, nr, hnr, hrP⟩ := hl l h0 (by rw [← hgr.step_eq]; exact h1)
  obtain ⟨nrJ, hnrJ, hownr, _, _⟩ := hgr.node?_grown r nr hnr
  exact ⟨r, hsub r hr, hownw r hrw, hrs, nrJ, hnrJ, fun p hp => hownr p (hrP p hp)⟩

/-- **`JoinChoiceP`**: every `P`-compatible link of `J`, with `P` a clique of `J` and both ends owning `P`, is already a
`P`-compatible link of one of the states `Side`, with `P` a clique there and both ends owning `P` there. -/
def JoinChoiceP (J : GPathM) (Side : GPathM → Prop) : Prop :=
  ∀ P, Clique J P → ∀ y ny w nw, J.node? y = some ny → J.node? w = some nw → OwnsAll P ny → OwnsAll P nw →
    CxP J P ny w → ∃ X, Side X ∧ Clique X P ∧ ∃ nyX nwX, X.node? y = some nyX ∧ X.node? w = some nwX ∧
      OwnsAll P nyX ∧ OwnsAll P nwX ∧ CxP X P nyX w

/-- **`CliqueTri` through the join**: states that grow into `J`, each with `CliqueTri`, and `JoinChoiceP`, give
`CliqueTri J`. The witness `r` the chosen state gives, with its compatible links, climbs to `J` (`cxP_grown`). -/
theorem cliqueTri_of_joinChoice (J : GPathM) (Side : GPathM → Prop) (hgr : ∀ X, Side X → Grown X J)
    (htri : ∀ X, Side X → CliqueTri X) (hch : JoinChoiceP J Side) : CliqueTri J := by
  intro P hP y ny w nw hy hw hyP hwP hC l h0 h1
  obtain ⟨X, hX, hPX, nyX, nwX, hyX, hwX, hyPX, hwPX, hCX⟩ := hch P hP y ny w nw hy hw hyP hwP hC
  have g := hgr X hX
  obtain ⟨ny', hny', hsuby, _, _⟩ := g.node?_grown y nyX hyX
  rw [hy] at hny'; cases hny'
  obtain ⟨nw', hnw', hsubw, _, _⟩ := g.node?_grown w nwX hwX
  rw [hw] at hnw'; cases hnw'
  obtain ⟨r, hr, hrw, hrs, ⟨nr, hnr, hrP⟩, hCyr, hCwr⟩ :=
    htri X hX P hPX y nyX w nwX hyX hwX hyPX hwPX hCX l h0 (by rw [← g.step_eq]; exact h1)
  obtain ⟨nrJ, hnrJ, hownr, _, _⟩ := g.node?_grown r nr hnr
  exact ⟨r, hsuby r hr, hsubw r hrw, hrs, ⟨nrJ, hnrJ, fun p hp => hownr p (hrP p hp)⟩,
    cxP_grown g hsuby hCyr, cxP_grown g hsubw hCwr⟩

/-- info: 'AbsSatBin.GraphPath.Model.JoinTri.cliqueTri_of_joinChoice' does not depend on any axioms -/
#guard_msgs in
#print axioms cliqueTri_of_joinChoice

variable (φ : Cnf)

/-- **A state of line `n+1` has `CliqueTri`** when its pieces have it and `JoinChoiceP` holds for them. -/
theorem cliqueTri_line_of_pieces (n : Nat) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1))
    (htri : ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true →
      CliqueTri (upF φ kv.2 kv'.1))
    (hch : JoinChoiceP kv'.2 (fun X => ∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧
      isValid (upF φ kv.2 kv'.1) = true ∧ X = upF φ kv.2 kv'.1)) :
    CliqueTri kv'.2 := by
  refine cliqueTri_of_joinChoice kv'.2 _ (fun X ⟨kv, hkv, hd, hv, hX⟩ => ?_)
    (fun X ⟨kv, hkv, hd, hv, hX⟩ => hX ▸ htri kv hkv hd hv) hch
  obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hv
  have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
  rw [hX, ← he]; exact hgr

/-- info: 'AbsSatBin.GraphPath.Model.JoinTri.cliqueTri_line_of_pieces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cliqueTri_line_of_pieces

end AbsSatBin.GraphPath.Model.JoinTri
