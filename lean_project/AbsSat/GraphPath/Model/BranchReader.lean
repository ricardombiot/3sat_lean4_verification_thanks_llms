-- lean_project/AbsSat/GraphPath/Model/BranchReader.lean
import AbsSat.GraphPath.Model.BranchCompat

/-!
# The Improves verdict from one global property: no borrowing between branches

The global picture of reports v124–v127: the machine builds the set of partial paths line by line; the
branch of a set of pins `P` is the machine built on the paths that agree with `P`; a valid branch sits
inside the whole machine, agrees with its pins, and keeps the whole final state valid under every
one-by-one pinning by pins of `P` (`BranchCompat.reader_pins_valid_of_branch`).

What is left is one property of the construction, stated here:

* **`NoBorrow φ K`** — whenever the branch of `P` reaches the map node `K` valid, and the state the
  reader reaches by pinning `P` still has a choice, some choice `q` at a step with a choice has a branch
  `P + q` that also reaches `K` valid. In the author's words: every node the reader can still choose
  belongs to a path built step by step that survives on its own, not only because a join with another
  branch holds it.

* **`sat_of_noBorrow`** — with `NoBorrow`, a valid final state of the Improves machine gives a model of
  `φ`: the reader pins, one at a time, the choices `NoBorrow` provides; each pin is valid because its
  branch is (`reader_pins_valid_of_branch`); the measure falls at every pin; when no choice is left the
  state denotes a path, which decodes to a model.
-/

namespace AbsSat.GraphPath.Model.BranchReader

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.BranchRun
open AbsSat.GraphPath.Model.BranchLines
open AbsSat.GraphPath.Model.BranchCompat
open AbsSat.GraphPath.Model.PickInduction (choiceAt hasChoice)

variable (φ : Cnf)

/-- The branch of `P` reaches the map node `K` valid. -/
def BranchValid (P : List NodeId) (K : NodeId) : Prop :=
  ∃ kvb ∈ branchRun φ P, kvb.1 = K ∧ isValid (filterAllAgg kvb.2 []) = true

/-- **No borrowing between branches.** At the reader's state of a valid branch, some choice has a
valid branch. -/
def NoBorrow (K : NodeId) : Prop :=
  ∀ (P : List NodeId) (G : GPathM), (K, G) ∈ pureRunW φ → BranchValid φ P K →
    hasChoice (pinOneByOne (filterAllAgg G []) P) = true →
      ∃ k, 0 ≤ k ∧ k < (pinOneByOne (filterAllAgg G []) P).current_step ∧
        choiceAt (pinOneByOne (filterAllAgg G []) P) k = true ∧
        ∃ q ∈ ownersAt (pinOneByOne (filterAllAgg G []) P).gowners k, BranchValid φ (P ++ [q.id]) K

theorem pinOneByOne_append (g : GPathM) (P : List NodeId) (q : NodeId) :
    pinOneByOne g (P ++ [q]) = filterAllAgg (pinOneByOne g P) [q] := by
  simp [pinOneByOne, List.foldl_append]

theorem readable_pinOneByOne (g : GPathM) (hR : ReadableAgg g) :
    ∀ P, ReadableAgg (pinOneByOne g P) := by
  have main : ∀ (P : List NodeId) (g : GPathM), ReadableAgg g → ReadableAgg (pinOneByOne g P) := by
    intro P
    induction P with
    | nil => intro g h; exact h
    | cons q rest ih => intro g h; exact ih _ (ReadableAgg_filterAllAgg g h [q])
  exact fun P => main P g hR

/-- Two entries of the machine's final line with the same key are the same state. -/
theorem pureRunW_key_unique (hwf : WF φ) (a b : NodeId × GPathM) (ha : a ∈ pureRunW φ)
    (hb : b ∈ pureRunW φ) (hab : a.1 = b.1) : a.2 = b.2 := by
  have hinv := (branchRun_embedded φ hwf []).1
  rw [branchRun_nil] at hinv
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only at hab ⊢
  subst hab
  exact key_unique _ hinv.1.1 a1 a2 b2 ha hb

/-- A valid branch keeps the reader's state valid, for the whole state of its key. -/
theorem valid_of_branchValid (hwf : WF φ) (K : NodeId) (G : GPathM) (hG : (K, G) ∈ pureRunW φ)
    (P : List NodeId) (h : BranchValid φ P K) : isValid (pinOneByOne (filterAllAgg G []) P) = true := by
  obtain ⟨kvb, hkvb, hkey, hv⟩ := h
  obtain ⟨kv', hkv', hkey', hall⟩ := reader_pins_valid_of_branch φ hwf P kvb hkvb hv
  have hG' : kv'.2 = G := pureRunW_key_unique φ hwf kv' (K, G) hkv' hG (hkey'.trans hkey)
  rw [← hG']
  exact hall P (fun q hq => hq)

/-- **Soundness of the Improves verdict from no borrowing between branches.** -/
theorem sat_of_noBorrow (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) (hnb : NoBorrow φ kv.1) : Satisfiable φ := by
  have hG : (kv.1, kv.2) ∈ pureRunW φ := hkv
  have hm := (ReaderAggRun.pureRunW_state φ hwf kv hkv).1
  have hR₀ : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
  have main : ∀ (m : Nat) (P : List NodeId), measure (pinOneByOne (filterAllAgg kv.2 []) P) ≤ m →
      BranchValid φ P kv.1 → Inhabited (pinOneByOne (filterAllAgg kv.2 []) P) := by
    intro m
    induction m with
    | zero =>
      intro P hmeas hb
      have hvP := valid_of_branchValid φ hwf kv.1 kv.2 hG P hb
      have hRP := readable_pinOneByOne _ hR₀ P
      match hch : hasChoice (pinOneByOne (filterAllAgg kv.2 []) P) with
      | false => exact Reader.inhabited_of_noChoice_readable _ (readable_of_readableAgg _ hRP) hvP hch
      | true =>
        obtain ⟨k, _, _, hck, q, hq, _⟩ := hnb P kv.2 hG hb hch
        exact absurd (measure_lt_of_choiceAt _ k hck q hq) (by omega)
    | succ m ih =>
      intro P hmeas hb
      have hvP := valid_of_branchValid φ hwf kv.1 kv.2 hG P hb
      have hRP := readable_pinOneByOne _ hR₀ P
      match hch : hasChoice (pinOneByOne (filterAllAgg kv.2 []) P) with
      | false => exact Reader.inhabited_of_noChoice_readable _ (readable_of_readableAgg _ hRP) hvP hch
      | true =>
        obtain ⟨k, _, _, hck, q, hq, hbq⟩ := hnb P kv.2 hG hb hch
        have hlt := measure_lt_of_choiceAt _ k hck q hq
        have hm' : measure (pinOneByOne (filterAllAgg kv.2 []) (P ++ [q.id])) ≤ m := by
          rw [pinOneByOne_append]; omega
        obtain ⟨p, hp⟩ := ih (P ++ [q.id]) hm' hbq
        rw [pinOneByOne_append] at hp
        exact ⟨p, denot_of_pruned (pruned_filterAllAgg _ [q.id]) (RCtx_of_readableAgg _ hRP).nodup p hp⟩
  have hb₀ : BranchValid φ [] kv.1 := ⟨kv, by rw [branchRun_nil]; exact hkv, rfl, hv⟩
  obtain ⟨p, hp⟩ := main _ [] (Nat.le_refl _) hb₀
  exact ReaderAggRun.sat_of_denot_final φ hwf kv hkv p
    (denot_of_pruned (pruned_filterAllAgg kv.2 []) hm.rctx.nodup p hp)

/-- info: 'AbsSat.GraphPath.Model.BranchReader.sat_of_noBorrow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_noBorrow

end AbsSat.GraphPath.Model.BranchReader
