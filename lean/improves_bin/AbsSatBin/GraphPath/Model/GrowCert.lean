-- lean/improves_bin/AbsSatBin/GraphPath/Model/GrowCert.lean
import AbsSatBin.GraphPath.Model.PieceFilter

/-!
# Growing one node at a time is `MapCert`

Measured (`julia/improves_bin/test_3sat/probes/grow_step_probe.jl`, `docs/context/ambfar.md` §4.2κ): a clique
with witnesses always gains a node at any free step (X1, 55 M tests, 0 failures), and completing it top-down
with **any** valid extension never gets stuck (X3).

`StateGrow.certClique_of_grow` already turns growth into certificates without map constraints. This module
carries the map constraints `R` of `MapCert` through the growth:

* **`GrowR g`**: a clique with witnesses that also own the map nodes `R` gains a node at any step, keeping
  them.
* **`mapCert_of_growR`**: on a kernel with the reader's context, `GrowR ⇒ MapCert`. The clique is grown to a
  node at every step (`cover_of_growR`), which is a certificate (`CertDescent.chain_of_cover`); at the step
  of a map node `m ∈ R`, the witness owns both the member and a node named `m`, and a table holds only its
  own node at its own step, so the member is named `m`.
* **`growR_of_mapCert`**: the converse — the certificate's node at the step is the extension.
* **`growR_iff_mapCert`**: so on those states **X1 is exactly `MapCert`**: adding one node is the whole
  open core, in its smallest form.
-/

namespace AbsSatBin.GraphPath.Model.GrowCert

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.CliqueTri (Clique OwnsAll)
open AbsSatBin.GraphPath.Model.MapCert (MapCert WitR CertR)
open AbsSatBin.GraphPath.Model.CertDescent (pick chain_of_cover)

/-- **Growth with map constraints**: a clique with witnesses owning `R` gains a node at any step. -/
def GrowR (g : GPathM) : Prop :=
  ∀ Q R, Clique g Q → WitR g Q R → ∀ l, 0 ≤ l → l < g.current_step →
    ∃ r, r.id.step = l ∧ Clique g (r :: Q) ∧ WitR g (r :: Q) R

theorem cover_of_growR {g : GPathM} (hG : GrowR g) (Q : List PathNodeId) (R : List NodeId)
    (hQ : Clique g Q) (hW : WitR g Q R) :
    ∀ m : Nat, ∃ Q', (∀ p ∈ Q, p ∈ Q') ∧ Clique g Q' ∧ WitR g Q' R ∧
      ∀ l, 0 ≤ l → l < (m : Int) → l < g.current_step → ∃ p ∈ Q', p.id.step = l := by
  intro m
  induction m with
  | zero => exact ⟨Q, fun p hp => hp, hQ, hW, fun l h0 h1 _ => absurd h1 (by omega)⟩
  | succ m ih =>
    obtain ⟨Q', hsub, hQ', hW', hcov⟩ := ih
    by_cases hm : (m : Int) < g.current_step
    · obtain ⟨r, hrs, hQr, hWr⟩ := hG Q' R hQ' hW' m (by omega) hm
      refine ⟨r :: Q', fun p hp => List.mem_cons_of_mem _ (hsub p hp), hQr, hWr, fun l h0 h1 h2 => ?_⟩
      rcases Int.lt_or_le l m with hl | hl
      · obtain ⟨p, hp, hps⟩ := hcov l h0 hl h2
        exact ⟨p, List.mem_cons_of_mem _ hp, hps⟩
      · exact ⟨r, List.mem_cons_self, by rw [hrs]; omega⟩
    · exact ⟨Q', hsub, hQ', hW', fun l h0 h1 h2 => hcov l h0 (by omega) h2⟩

/-- Two nodes of a certificate own each other (and each owns itself). -/
theorem chain_owns {g : GPathM} {sel : Int → PathNodeId} (hs : ChainSound g sel) (i j : Int)
    (hi0 : 0 ≤ i) (hi1 : i < g.current_step) (hj0 : 0 ≤ j) (hj1 : j < g.current_step) :
    ∃ n, g.node? (sel i) = some n ∧ sel j ∈ n.owners := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hs.chain.1.1 i hi0 hi1).1
  refine ⟨n, hn, ?_⟩
  by_cases hij : j = i
  · subst hij
    have := hs.self_owned j hj0 hj1
    simp only [ownersOf, hn] at this; exact this
  · have := hs.chain.2.1 j i hj0 hi0 hj1 hi1 hij
    simp only [ownersAt, ownersOf, hn] at this
    exact (List.mem_filter.mp this).1

section
variable {g : GPathM} (c : AmbTriCore.ACtx g)
include c

/-- **`GrowR ⇒ MapCert`** on a kernel with the reader's context. -/
theorem mapCert_of_growR (hG : GrowR g) : MapCert g := by
  intro Q R hQ hW
  obtain ⟨Q', hsub, hQ', hW', hcov⟩ := cover_of_growR hG Q R hQ hW g.current_step.toNat
  obtain ⟨hs, hon⟩ := chain_of_cover c Q' hQ' (fun l h0 h1 => hcov l h0 (by omega) h1)
  refine ⟨pick Q', hs, fun p hp => hon p (hsub p hp), fun m hm h0 h1 => ?_⟩
  -- the member at the step of `m` is the witness there, which owns a node named `m`
  obtain ⟨p, hp, hps⟩ := hcov m.step h0 (by omega) h1
  have hpk : pick Q' m.step = p := by rw [← hps]; exact hon p hp
  obtain ⟨r, nr, hnr, hrs, hrQ, hrR⟩ := hW' m.step h0 h1
  obtain ⟨x, hx, hxm⟩ := hrR m hm
  have hmem := List.mem_of_find?_eq_some hnr
  have hid : nr.id = r := node?_id_eq g r nr hnr
  have hpr : p = nr.id := c.pc.oos nr hmem p (hrQ p hp) (by rw [hid, hps, hrs])
  have hxr : x = nr.id := c.pc.oos nr hmem x hx (by rw [hid, hrs, hxm])
  rw [hpk, hpr, ← hxr, hxm]

/-- **`MapCert ⇒ GrowR`**: the certificate's node at the step extends the clique. -/
theorem growR_of_mapCert (hM : MapCert g) : GrowR g := by
  intro Q R hQ hW l h0 h1
  obtain ⟨sel, hs, hon, hR⟩ := hM Q R hQ hW
  have hQs : ∀ q ∈ Q, 0 ≤ q.id.step ∧ q.id.step < g.current_step ∧ sel q.id.step = q := by
    intro q hq
    obtain ⟨nq, hnq, _⟩ := hQ q hq
    have hr := CertFix.step_range c.pc q nq hnq
    exact ⟨hr.1, hr.2, hon q hq⟩
  -- every member of `sel l :: Q` is a chain node
  have hmem : ∀ p ∈ sel l :: Q, ∃ i, 0 ≤ i ∧ i < g.current_step ∧ sel i = p := by
    intro p hp
    rcases List.mem_cons.mp hp with e | hp
    · exact ⟨l, h0, h1, e.symm⟩
    · obtain ⟨a, b, e⟩ := hQs p hp; exact ⟨p.id.step, a, b, e⟩
  have hsl : (sel l).id.step = l := (hs.chain.1.1 l h0 h1).2
  refine ⟨sel l, hsl, fun p hp => ?_, fun l' h0' h1' => ?_⟩
  · obtain ⟨i, hi0, hi1, rfl⟩ := hmem p hp
    obtain ⟨n, hn, _⟩ := chain_owns hs i i hi0 hi1 hi0 hi1
    refine ⟨n, hn, fun s hs' => ?_⟩
    obtain ⟨j, hj0, hj1, rfl⟩ := hmem s hs'
    obtain ⟨n', hn', hown⟩ := chain_owns hs i j hi0 hi1 hj0 hj1
    rw [hn] at hn'; cases hn'; exact hown
  · obtain ⟨n, hn, _⟩ := chain_owns hs l' l' h0' h1' h0' h1'
    refine ⟨sel l', n, hn, (hs.chain.1.1 l' h0' h1').2, fun s hs' => ?_, fun m hm => ?_⟩
    · obtain ⟨j, hj0, hj1, rfl⟩ := hmem s hs'
      obtain ⟨n', hn', hown⟩ := chain_owns hs l' j h0' h1' hj0 hj1
      rw [hn] at hn'; cases hn'; exact hown
    · -- the step of `m` lies in the state: a witness owns a node named `m`
      obtain ⟨r, nr, hnr, _, _, hrR⟩ := hW l' h0' h1'
      obtain ⟨x, hx, hxm⟩ := hrR m hm
      obtain ⟨nx, hnx⟩ := c.pc.ker.isNode_owner r nr hnr x hx
      have hxr := CertFix.step_range c.pc x nx hnx
      rw [hxm] at hxr
      obtain ⟨n', hn', hown⟩ := chain_owns hs l' m.step h0' h1' hxr.1 hxr.2
      rw [hn] at hn'; cases hn'
      exact ⟨sel m.step, hown, hR m hm hxr.1 hxr.2⟩

/-- **On a kernel with the reader's context, growing one node at a time is exactly `MapCert`.** -/
theorem growR_iff_mapCert : GrowR g ↔ MapCert g :=
  ⟨mapCert_of_growR c, growR_of_mapCert c⟩

end

/-- info: 'AbsSatBin.GraphPath.Model.GrowCert.growR_iff_mapCert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms growR_iff_mapCert

-- ============================================================
-- The join: growth in the good piece (measured X4)
-- ============================================================

theorem clique_of_grown {g g' : GPathM} (h : Grown g g') (Q : List PathNodeId) (hQ : Clique g Q) : Clique g' Q := by
  intro p hp
  obtain ⟨n, hn, hnQ⟩ := hQ p hp
  obtain ⟨n', hn', ho, _, _⟩ := h.node?_grown p n hn
  exact ⟨n', hn', fun s hs => ho s (hnQ s hs)⟩

theorem witR_of_grown {g g' : GPathM} (h : Grown g g') (Q : List PathNodeId) (R : List NodeId)
    (hW : WitR g Q R) : WitR g' Q R := by
  intro l h0 h1
  obtain ⟨r, nr, hnr, hrs, hrQ, hrR⟩ := hW l h0 (by rw [← h.step_eq]; exact h1)
  obtain ⟨n', hn', ho, _, _⟩ := h.node?_grown r nr hnr
  refine ⟨r, n', hn', hrs, fun s hs => ho s (hrQ s hs), fun m hm => ?_⟩
  obtain ⟨p, hp, hpm⟩ := hrR m hm
  exact ⟨p, ho p hp, hpm⟩

open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem

variable (φ : Cnf)

/-- **The joined state grows when its pieces grow** and its cliques with witnesses live in one piece (X4:
the extension is taken in the good piece and stays good there; the piece grows into the joined state). -/
theorem growR_join (n : Nat) (hPL : PieceJoin.PieceLocal φ n)
    (hP : ∀ kv ∈ line φ n, ∀ d ∈ sonsOfMap φ kv.1, isValid (upF φ kv.2 d) = true → GrowR (upF φ kv.2 d)) :
    ∀ kv' ∈ line φ (n + 1), GrowR kv'.2 := by
  intro kv' hkv' Q R hQ hW l h0 h1
  obtain ⟨kv, hkv, hd, hv, hQP, hWP⟩ := hPL kv' hkv' Q R hQ hW
  obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hv
  have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
  rw [← he] at h1 ⊢
  obtain ⟨r, hrs, hQr, hWr⟩ := hP kv hkv kv'.1 hd hv Q R hQP hWP l h0 (by rw [← hgr.step_eq]; exact h1)
  exact ⟨r, hrs, clique_of_grown hgr _ hQr, witR_of_grown hgr _ _ hWr⟩

/-- info: 'AbsSatBin.GraphPath.Model.GrowCert.growR_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms growR_join

end AbsSatBin.GraphPath.Model.GrowCert
