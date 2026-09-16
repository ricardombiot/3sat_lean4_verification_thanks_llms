-- lean_project/AbsSat/GraphPath/Model/TopPhantom.lean
import AbsSat.GraphPath.Model.NoDeadEnd

/-!
# Phantoms at the top, and reading without backtracking

A **phantom** is a partial chain that satisfies every pairwise condition (`SoundFrom`: nodes,
links, global owners, mutual ownership) but is the prefix of no full chain. Owner tables are
pairwise projections of the chain set, so pairwise-consistent selections need not come from a real
chain (a Helly gap). Phantoms of this kind were measured in the states built by `join` (v108).

A reader without backtracking starts at the top step and goes down, picking at each step a node
compatible with everything picked so far. Everything it has picked is anchored at the top. It gets
stuck exactly when what it has picked is a phantom anchored at the top; phantoms in intermediate
states, or ending below the top, do not affect it.

* `TopPhantom g sel lo` — a partial chain from the top down to `lo` with no full chain extending it.
* `NoTopPhantom g` — the positive form: every partial chain from the top has a full-chain witness
  agreeing with it from `lo` up.
* `noDeadEnd_iff_noTopPhantom` — **reading without backtracking never gets stuck iff there are no
  phantoms at the top**: `NoDeadEnd g ↔ NoTopPhantom g`.
* `not_topPhantom` — `NoTopPhantom` rules out every `TopPhantom`. The converse (from `∀ sel lo,
  ¬ TopPhantom g sel lo` back to the witnesses) needs classical logic, so the equivalence is stated
  with the positive form.

Open, and the target for later: `NoTopPhantom` for the states the reader actually reads — i.e. that
the review leaves no phantoms at the top. The opposite worry does not arise: the review never
destroys a real chain (`Coherence.ChainSound_review`).
-/

namespace AbsSat.GraphPath.Model.TopPhantom

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.NoDeadEnd

/-- **A phantom at the top**: a partial chain from the top step down to `lo` that is the prefix of
no full chain. -/
def TopPhantom (g : GPathM) (sel : Int → PathNodeId) (lo : Int) : Prop :=
  0 ≤ lo ∧ lo ≤ g.current_step - 1 ∧ SoundFrom g sel lo ∧
    ¬ ∃ sel', (∀ k, lo ≤ k → sel' k = sel k) ∧ SoundFrom g sel' 0

/-- **No phantoms at the top**, positive form: every partial chain from the top has a full chain
agreeing with it on `lo` and above. -/
def NoTopPhantom (g : GPathM) : Prop :=
  ∀ sel lo, 0 ≤ lo → lo ≤ g.current_step - 1 → SoundFrom g sel lo →
    ∃ sel', (∀ k, lo ≤ k → sel' k = sel k) ∧ SoundFrom g sel' 0

theorem not_topPhantom {g : GPathM} (h : NoTopPhantom g) (sel : Int → PathNodeId) (lo : Int) :
    ¬ TopPhantom g sel lo :=
  fun ⟨h0, h1, hs, hn⟩ => hn (h sel lo h0 h1 hs)

/-- A partial chain stays one when its lower end moves up and its picks change only below it. -/
theorem soundFrom_congr_mono {g : GPathM} {sel sel' : Int → PathNodeId} {lo lo' : Int}
    (h : SoundFrom g sel' lo') (hle : lo' ≤ lo) (hag : ∀ k, lo ≤ k → sel k = sel' k) :
    SoundFrom g sel lo where
  node := fun k h1 h2 => by rw [hag k h1]; exact h.node k (by omega) h2
  parent_link := fun k h1 h2 => by
    rw [hag k h1, hag (k + 1) (by omega)]; exact h.parent_link k (by omega) h2
  owned := fun i j hi hj hi2 hj2 hne => by
    rw [hag i hi, hag j hj]; exact h.owned i j (by omega) (by omega) hi2 hj2 hne
  gowner := fun k h1 h2 => by rw [hag k h1]; exact h.gowner k (by omega) h2
  self_owned := fun k h1 h2 => by rw [hag k h1]; exact h.self_owned k (by omega) h2
  son_link := fun k h1 h2 => by
    rw [hag k h1, hag (k + 1) (by omega)]; exact h.son_link k (by omega) h2
  root_shape := fun k h1 h2 => by rw [hag k h1]; exact h.root_shape k (by omega) h2

/-- No dead ends give every top partial chain its witness (`NoDeadEnd.descend`). -/
theorem noTopPhantom_of_noDeadEnd {g : GPathM} (h : NoDeadEnd g) : NoTopPhantom g :=
  fun sel lo hlo hlohi hs => descend g h lo.toNat sel lo (Nat.le_refl _) hlo hlohi hs

/-- A witness gives the next pick down: take the witness's own pick at `lo - 1`. -/
theorem noDeadEnd_of_noTopPhantom {g : GPathM} (h : NoTopPhantom g) : NoDeadEnd g := by
  intro sel lo hpos hlo hs
  obtain ⟨sel', hag, hs'⟩ := h sel lo (by omega) hlo hs
  refine ⟨sel' (lo - 1), soundFrom_congr_mono hs' (by omega) (fun k hk => ?_)⟩
  unfold upd
  split
  · next hk' => rw [hk']
  · next hk' => exact (hag k (by omega)).symm

/-- **Reading without backtracking never gets stuck iff there are no phantoms at the top.** -/
theorem noDeadEnd_iff_noTopPhantom (g : GPathM) : NoDeadEnd g ↔ NoTopPhantom g :=
  ⟨noTopPhantom_of_noDeadEnd, noDeadEnd_of_noTopPhantom⟩

/-- info: 'AbsSat.GraphPath.Model.TopPhantom.not_topPhantom' does not depend on any axioms -/
#guard_msgs in
#print axioms not_topPhantom

/-- info: 'AbsSat.GraphPath.Model.TopPhantom.noDeadEnd_iff_noTopPhantom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_iff_noTopPhantom

end AbsSat.GraphPath.Model.TopPhantom
