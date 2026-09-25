-- lean/improves_bin/AbsSatBin/GraphPath/Model/KernelIff.lean
import AbsSatBin.GraphPath.Model.KernelSplit

/-!
# `KernelSplit ⇔ NoDeadEnd`

`KernelReader.noDeadEnd_of_kernelSplit` gives one direction. This module gives the other: a pin that
survives leaves, below the state, a valid kernel that fixes it — the pinned state itself.

* **The review never adds a son** (`sonsSub_review`, `sonsSub_filterAll`): every operation keeps the
  ids and only shrinks the son tables (`Sons.SonsSub`, the clause `Pruned` is missing).
* So **a filtered state sits below its input** (`below_filterAll_self`), and a valid pinned state of
  the reader is a kernel (`KernelReader.kernel_readPins`) whose global owners at the pinned step are
  the pinned map node.

Hence `KernelSplit` is exactly `NoDeadEnd` on the reader's states: the open core has not been made
stronger by restating it on kernels.
-/

namespace AbsSatBin.GraphPath.Model.KernelIff

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Sons (SonsSub SonsSub_refl SonsSub_trans)
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

-- ============================================================
-- The review never adds a son
-- ============================================================

theorem sonsSub_reviewNode (g : GPathM) (nb : PNodeM → List PathNodeId) (id : PathNodeId) :
    SonsSub g (reviewNode g nb id) := by
  simp only [reviewNode]
  split
  · exact SonsSub_refl g
  · next d _ =>
    split
    · have h₁ : SonsSub g (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) :=
        Sons.SonsSub_updateAt g id _ (fun _ => rfl) (fun _ _ hs => hs)
      have h₂ := SonsSub_trans h₁ (SonsSub_trans
        (Sons.SonsSub_mirrorDrop _ id (cutRemoved d (unionOwnersOf g (nb d))))
        (Sons.SonsSub_unlinkIncompatible _ id))
      split
      · exact h₂
      · exact SonsSub_trans h₂ (Sons.SonsSub_removeNode _ id)
    · exact Sons.SonsSub_removeNode g id

theorem sonsSub_foldl {β : Type} (g₀ : GPathM) (f : GPathM → β → GPathM)
    (hf : ∀ g b, SonsSub g (f g b)) :
    ∀ (l : List β) (g : GPathM), SonsSub g₀ g → SonsSub g₀ (l.foldl f g) := by
  intro l
  induction l with
  | nil => intro g h; exact h
  | cons b bs ih => intro g h; exact ih _ (SonsSub_trans h (hf g b))

theorem sonsSub_reviewSteps (g₀ : GPathM) (nb : PNodeM → List PathNodeId) :
    ∀ (ks : List Int) (g : GPathM), SonsSub g₀ g → SonsSub g₀ (reviewSteps g nb ks) := by
  intro ks
  induction ks with
  | nil => intro g h; exact h
  | cons k ks ih =>
    intro g h
    simp only [reviewSteps]
    split
    · exact ih _ (sonsSub_foldl g₀ (fun g id => reviewNode g nb id)
        (fun g id => sonsSub_reviewNode g nb id) _ g h)
    · exact h

theorem sonsSub_pairSweep (g : GPathM) : SonsSub g (pairSweep g) := by
  intro n' hn'
  obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hn'
  exact ⟨n, hn, by rw [← hEq], fun s hs => by rw [← hEq] at hs; exact hs⟩

theorem sonsSub_cleanInvalid₂ (g : GPathM) : SonsSub g (cleanInvalid₂ g) :=
  SonsSub_trans (purgeFuel_inv (SonsSub g)
      (fun h id hh => SonsSub_trans hh (Sons.SonsSub_removeNode h id)) _ g (SonsSub_refl g))
    (Sons.SonsSub_cutAll _)

theorem sonsSub_cleanPair (g : GPathM) : SonsSub g (cleanPair g) :=
  cleanPair_inv (SonsSub g) g (sonsSub_cleanInvalid₂ g)
    (fun x _ hx => SonsSub_trans hx (SonsSub_trans (sonsSub_pairSweep x) (sonsSub_cleanInvalid₂ _)))

theorem sonsSub_reviewPass (g : GPathM) : SonsSub g (reviewPass g) := by
  simp only [reviewPass, reviewParents, reviewSons]
  exact sonsSub_reviewSteps g _ _ _ (sonsSub_reviewSteps g _ _ _ (sonsSub_cleanPair g))

theorem sonsSub_reviewFuel : ∀ (fuel : Nat) (g : GPathM), SonsSub g (reviewFuel fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g; exact SonsSub_refl g
  | succ n ih =>
    intro g
    simp only [reviewFuel]
    split
    · split
      · exact SonsSub_trans (sonsSub_reviewPass g) (ih _)
      · exact sonsSub_reviewPass g
    · exact SonsSub_refl g

/-- **The review never adds a son.** -/
theorem sonsSub_review (g : GPathM) : SonsSub g (review g) := sonsSub_reviewFuel _ g

theorem sonsSub_filterAll (g : GPathM) (reqs : List NodeId) : SonsSub g (filterAll g reqs) := by
  refine SonsSub_trans ?_ (sonsSub_review _)
  intro n hn
  rw [SymMachine.foldl_filterRequire_nodes] at hn
  exact ⟨n, hn, rfl, fun _ h => h⟩

-- ============================================================
-- A filtered state sits below its input
-- ============================================================

/-- **A filtered state sits below its input.** -/
theorem below_filterAll_self (g : GPathM) (hnd : NodupIds g) (reqs : List NodeId) :
    Below g (filterAll g reqs) := by
  have hpr := pruned_filterAll g reqs
  have hss := sonsSub_filterAll g reqs
  refine ⟨hpr.step_eq.symm, hpr.gowners_sub, fun p nh hnh => ?_⟩
  have hm := List.mem_of_find?_eq_some hnh
  have hid : nh.id = p := node?_id_eq _ p nh hnh
  obtain ⟨n, hn, hid1, ho, hp⟩ := hpr.nodes_derived nh hm
  obtain ⟨n2, hn2, hid2, hs⟩ := hss nh hm
  have e1 : g.node? p = some n := by rw [← hid, hid1]; exact node?_of_mem hnd n hn
  have e2 : g.node? p = some n2 := by rw [← hid, hid2]; exact node?_of_mem hnd n2 hn2
  rw [e1] at e2; cases e2
  exact ⟨n, e1, ho, hp, hs⟩

-- ============================================================
-- `NoDeadEnd ⇒ KernelSplit`
-- ============================================================

variable (φ : Cnf)

/-- **`NoDeadEnd ⇒ KernelSplit`**: the pinned state is the kernel. -/
theorem kernelSplit_of_noDeadEnd (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (hnd : NoDeadEnd.NoDeadEnd (filterAll kv.2 [])) : KernelReader.KernelSplit (filterAll kv.2 []) := by
  intro g hF hv k hf
  obtain ⟨q, hq, hvq⟩ := hnd g hF hv k hf
  obtain ⟨ps, hp⟩ := OtherBitSem.readPins_of_readFirst _ g hF
  have c := KernelSplit.pinCtx_readPins φ hbd kv hkv ps g hp hv
  have hpk := KernelReader.kernel_readPins φ hbd kv hkv (q.id :: ps) _
    (ReadPins.pin g k q ps hp hv hf hq hvq) hvq
  refine ⟨q, hq, filterAll g [q.id], hpk, hvq, below_filterAll_self g c.nd [q.id], ?_⟩
  intro x hx hxs
  have hx' := (pruned_review (filterRequire g q.id)).gowners_sub x hx
  have hkeep := (List.mem_filter.mp hx').2
  simp only [hxs, bne_self_eq_false, Bool.false_or] at hkeep
  exact eq_of_beq hkeep

/-- **`KernelSplit ⇔ NoDeadEnd`** on the reader's starting states. -/
theorem kernelSplit_iff_noDeadEnd (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ) :
    KernelReader.KernelSplit (filterAll kv.2 []) ↔ NoDeadEnd.NoDeadEnd (filterAll kv.2 []) :=
  ⟨KernelReader.noDeadEnd_of_kernelSplit _, kernelSplit_of_noDeadEnd φ hbd kv hkv⟩

/-- info: 'AbsSatBin.GraphPath.Model.KernelIff.kernelSplit_iff_noDeadEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kernelSplit_iff_noDeadEnd

end AbsSatBin.GraphPath.Model.KernelIff
