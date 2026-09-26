-- lean/improves_bin/AbsSatBin/GraphPath/Model/CertInvariant.lean
import AbsSatBin.GraphPath.Model.CertDescent

/-!
# `CertClique`: the certificate statement as an invariant of states

**`CertClique g`**: every clique with witnesses (`Wit`: at every step a live node owns all of it) lies
on a certificate. On the reader's states it is `CertLink` again (`certClique_iff_certLink`), but it is
stated on any state and it does not mention compatibility, so it can be followed along the machine.

* **The review keeps it** (`certClique_filterAll_nil`): a clique with witnesses after the review has
  them before (tables only shrink), and the certificate it lies on survives the review.
* So **`CertClique` on the machine's raw output is enough** (`readerVerdictW_iff_of_certClique`).

What each other operation of the machine would need is in `docs/context/ambfar.md` §4.2g: the
requirement filter, `addNode` at a merge node, and `join` all mix witnesses of different steps.
-/

namespace AbsSatBin.GraphPath.Model.CertInvariant

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.CliqueTri
open AbsSatBin.GraphPath.Model.CertFix
open AbsSatBin.GraphPath.Model.CertDescent
open AbsSatBin.GraphPath.Model.AmbTriCore
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

/-- **Every clique with witnesses lies on a certificate.** -/
def CertClique (g : GPathM) : Prop := ∀ Q, Clique g Q → Wit g Q → CertThrough g Q

section
variable {g : GPathM} (c : ACtx g)
include c

theorem certClique_of_cliqueTri (hT : CliqueTri g) : CertClique g := by
  intro Q hQ hW
  cases Q with
  | nil =>
    -- the empty clique: any certificate will do; grow one from a witness at step 0 if there is a step
    by_cases h0 : (0 : Int) < g.current_step
    · obtain ⟨r, nr, hnr, _, _⟩ := hW 0 (Int.le_refl 0) h0
      have hQr : Clique g [r] := fun p hp => by
        rw [List.mem_singleton.mp hp]
        exact ⟨nr, hnr, fun s hs => by rw [List.mem_singleton.mp hs]; exact TriPinCut.self_own_pc c.pc r nr hnr⟩
      have hWr : Wit g [r] := by
        intro l h0' h1'
        obtain ⟨s, hs, hss⟩ := entry_at c r nr hnr l h0' h1'
        obtain ⟨ns, hns⟩ := c.pc.ker.isNode_owner r nr hnr s hs
        exact ⟨s, ns, hns, hss, fun p hp => by
          rw [List.mem_singleton.mp hp]; exact c.pc.ker.sym r nr s ns hnr hns hs⟩
      obtain ⟨Q', _, hQ', _, hcov⟩ := cover c hT [r] hQr hWr r List.mem_cons_self g.current_step.toNat
      obtain ⟨hs, _⟩ := chain_of_cover c Q' hQ' (fun l h0 h1 => hcov l h0 (by omega) h1)
      exact ⟨pick Q', hs, fun _ h => absurd h List.not_mem_nil⟩
    · refine ⟨fun l => ⟨⟨l, 0⟩, none, none⟩, ⟨⟨⟨fun k h0 h1 => absurd h1 (by omega),
        fun k h0 h1 => absurd h1 (by omega)⟩, fun i j _ _ hi _ _ => absurd hi (by omega),
        fun k h0 h1 => absurd h1 (by omega)⟩, fun k h0 h1 => absurd h1 (by omega),
        fun k h0 h1 => absurd h1 (by omega), ⟨rfl, fun k h0 h1 => absurd h1 (by omega)⟩⟩,
        fun _ h => absurd h List.not_mem_nil⟩
  | cons q Q =>
    obtain ⟨Q', hsub, hQ', _, hcov⟩ := cover c hT (q :: Q) hQ hW q List.mem_cons_self g.current_step.toNat
    obtain ⟨hs, hon⟩ := chain_of_cover c Q' hQ' (fun l h0 h1 => hcov l h0 (by omega) h1)
    exact ⟨pick Q', hs, fun p hp => hon p (hsub p hp)⟩

theorem certLink_of_certClique (h : CertClique g) : CertLink g :=
  certLink_of_cliqueTri c (cliqueTri_of_certLink c.pc (fun P hP y ny w nw hy hw hyP hwP hC =>
    h _ (clique_start c P hP y ny w nw hy hw hyP hwP hC).1 (clique_start c P hP y ny w nw hy hw hyP hwP hC).2))

/-- **On the reader's states, `CertClique` is `CertLink`.** -/
theorem certClique_iff_certLink : CertClique g ↔ CertLink g :=
  ⟨certLink_of_certClique c, fun h => certClique_of_cliqueTri c (cliqueTri_of_certLink c.pc h)⟩
end

/-- **The review keeps `CertClique`.** -/
theorem certClique_filterAll_nil (X : GPathM) (hnd : NodupIds X) (h : CertClique X) :
    CertClique (filterAll X []) := by
  have hb := KernelIff.below_filterAll_self X hnd []
  intro Q hQ hW
  have hQX : Clique X Q := fun p hp => by
    obtain ⟨np, hnp, hpQ⟩ := hQ p hp
    obtain ⟨nx, hnx, ho, _, _⟩ := hb.node p np hnp
    exact ⟨nx, hnx, fun s hs => ho s (hpQ s hs)⟩
  have hWX : Wit X Q := fun l h0 h1 => by
    obtain ⟨r, nr, hnr, hrs, hrQ⟩ := hW l h0 (by rw [← hb.step]; exact h1)
    obtain ⟨nx, hnx, ho, _, _⟩ := hb.node r nr hnr
    exact ⟨r, nx, hnx, hrs, fun s hs => ho s (hrQ s hs)⟩
  obtain ⟨sel, hs, hon⟩ := h Q hQX hWX
  exact ⟨sel, ChainSound_filterAll X [] sel hs (fun _ h => absurd h List.not_mem_nil), hon⟩

variable (φ : Cnf)

/-- **The reader decides `φ` when the machine's raw output satisfies `CertClique`.** -/
theorem readerVerdictW_iff_of_certClique (hbd : Bounded φ)
    (h0 : ∀ kv ∈ pureRun φ, CertClique kv.2) : readerVerdictW φ = true ↔ Satisfiable φ := by
  refine readerVerdictW_iff_of_certLink φ hbd (fun kv hkv hv => ?_)
  have c := aCtx_readPins φ hbd kv hkv [] _ ReadPins.start hv
  obtain ⟨cm, _⟩ := SymMachine.machine_ctx φ hbd kv hkv
  exact certLink_of_certClique c (certClique_filterAll_nil kv.2 cm.nodup (h0 kv hkv))

/-- info: 'AbsSatBin.GraphPath.Model.CertInvariant.readerVerdictW_iff_of_certClique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_certClique

end AbsSatBin.GraphPath.Model.CertInvariant
