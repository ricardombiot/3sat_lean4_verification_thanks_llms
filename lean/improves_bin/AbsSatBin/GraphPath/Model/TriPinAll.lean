-- lean/improves_bin/AbsSatBin/GraphPath/Model/TriPinAll.lean
import AbsSatBin.GraphPath.Model.TriPinCut

/-!
# The invariant: `TriPin₁` for every live node

The measurements say more than the reader needs: on every state the reader visited, **every** pin at
the first choice survived, and `TriPin₁` held for every node of the first choice. The machine keeps
the set of certificates exactly, and the tables record it pair by pair; one round of cuts of the links
that are not compatible with `x` is enough to read off the certificates through `x`.

* **`AllTriPin₁ g`**: `TriPin₁ g x` for every live node `x`. A statement about one state, uniform in
  `x`: the form a machine invariant can take.
* **`allPinsAlive_of_allTriPin₁`**: under it, **every** pin at the first choice survives — not only
  one (`AllPinsAlive`, stronger than `NoDeadEnd`).
* **`readerVerdictW_iff_of_allTriPin₁`**: if every valid state the reader visits satisfies it, the reader
  decides `φ`.

What is left is the invariant itself: that `AllTriPin₁` holds on every valid state the reader visits
(`AllTriPin₁Reader`). Since the reader's states are pinned states of the machine's, the natural route is
to show that the machine builds it (`addNode`, `join`) and that the review and the pin keep it.
-/

namespace AbsSatBin.GraphPath.Model.TriPinAll

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.TriPinCut
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.PickInduction (choiceAt)

/-- **The invariant**: the pair rule holds inside the cut sub-kernel of every live node. -/
def AllTriPin₁ (g : GPathM) : Prop := ∀ x nx, g.node? x = some nx → TriPin₁ g x

/-- Every pin at the first choice survives. -/
def AllPinsAlive (g : GPathM) : Prop :=
  ∀ k, firstChoice g = some k → ∀ q ∈ ownersAt g.gowners k, isValid (filterAll g [q.id]) = true

/-- A step with a choice has a live entry. -/
theorem exists_owner_of_choiceAt (g : GPathM) (k : Int) (h : choiceAt g k = true) :
    ∃ q, q ∈ ownersAt g.gowners k := by
  obtain ⟨q, hq, _⟩ := List.any_eq_true.mp h
  exact ⟨q, hq⟩

/-- **Under the invariant, every pin at the first choice survives.** -/
theorem allPinsAlive_of_allTriPin₁ {g : GPathM} (c : PinCtx g) (h : AllTriPin₁ g) : AllPinsAlive g := by
  intro k _ q hq
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (c.ker.gn q (List.mem_filter.mp hq).1)
  exact pin_survives_of_triPin₁ c q nq hnq (h q nq hnq)

-- ============================================================
-- With the reader
-- ============================================================

variable (φ : Cnf)

/-- The invariant on every valid state the reader visits. -/
def AllTriPin₁Reader (g₀ : GPathM) : Prop :=
  ∀ g, ReadFirst g₀ g → isValid g = true → AllTriPin₁ g

theorem triPin₁Reader_of_all (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (ha : AllTriPin₁Reader (filterAll kv.2 [])) : TriPin₁Reader (filterAll kv.2 []) := by
  intro g hF hv k hf
  obtain ⟨ps, hp⟩ := OtherBitSem.readPins_of_readFirst _ g hF
  have c := pinCtx_readPins φ hbd kv hkv ps g hp hv
  obtain ⟨q, hq⟩ := exists_owner_of_choiceAt g k (choiceAt_of_firstChoice g k hf)
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (c.ker.gn q (List.mem_filter.mp hq).1)
  exact ⟨q, hq, ha g hF hv q nq hnq⟩

/-- **Every pin survives on every valid state the reader visits.** -/
theorem allPinsAlive_reader (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (ha : AllTriPin₁Reader (filterAll kv.2 [])) :
    ∀ g, ReadFirst (filterAll kv.2 []) g → isValid g = true → AllPinsAlive g := by
  intro g hF hv
  obtain ⟨ps, hp⟩ := OtherBitSem.readPins_of_readFirst _ g hF
  exact allPinsAlive_of_allTriPin₁ (pinCtx_readPins φ hbd kv hkv ps g hp hv) (ha g hF hv)

/-- **The reader decides `φ` when every valid state it visits satisfies the invariant.** -/
theorem readerVerdictW_iff_of_allTriPin₁ (hbd : Bounded φ)
    (ha : ∀ kv ∈ pureRun φ, AllTriPin₁Reader (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_triPin₁ φ hbd (fun kv hkv => triPin₁Reader_of_all φ hbd kv hkv (ha kv hkv))

/-- info: 'AbsSatBin.GraphPath.Model.TriPinAll.allPinsAlive_reader' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms allPinsAlive_reader

/-- info: 'AbsSatBin.GraphPath.Model.TriPinAll.readerVerdictW_iff_of_allTriPin₁' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_allTriPin₁

end AbsSatBin.GraphPath.Model.TriPinAll
