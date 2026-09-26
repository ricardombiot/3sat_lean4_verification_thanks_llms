-- lean/improves_bin/AbsSatBin/GraphPath/Model/CertFix.lean
import AbsSatBin.GraphPath.Model.CliqueTri

/-!
# The review's fixpoint, characterized by certificates

A **certificate** of a state is a chain `ChainSound g sel`: one live node per step, linked by parents
and sons, all owning each other. On the machine's final line the certificates are the solutions; at an
intermediate state they are the partial paths that satisfy every requirement seen so far.

The machine keeps the set of certificates, and the tables record it pair by pair. The cuts of
`CliqueTri` say how to read it back:

* **`cxP_of_cert`** (always true): if a certificate goes through a clique `P` and through `y` and `w`,
  the link `y–w` is `P`-compatible — the certificate's own nodes are the witnesses.
* **`CertLink g`** (the characterization): the converse. Every `P`-compatible link lies, with `P`, on a
  certificate. So **the cut table of `y` relative to `P` is exactly what the certificates through `y`
  and `P` project** (`cutTable_iff_cert`).
* **`cliqueTri_of_certLink`**: the characterization gives `CliqueTri` — the witness at each step is the
  certificate's node, and its links are compatible for the same reason.

With `CliqueTri.readerVerdictW_iff_of_cliqueTri`: **if the machine's starting states satisfy
`CertLink`, the reader decides `φ`** (`readerVerdictW_iff_of_certLink`). `CertLink` at `P = []` is
pairwise exactness: every link that passes the pair rule lies on a certificate.
-/

namespace AbsSatBin.GraphPath.Model.CertFix

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.CliqueTri
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

/-- A certificate goes through every node of `Q`. -/
def CertThrough (g : GPathM) (Q : List PathNodeId) : Prop :=
  ∃ sel, ChainSound g sel ∧ ∀ q ∈ Q, sel q.id.step = q

/-- **The characterization**: every link compatible relative to a clique lies, with the clique, on a
certificate. -/
def CertLink (g : GPathM) : Prop :=
  ∀ P, Clique g P → ∀ y ny w nw, g.node? y = some ny → g.node? w = some nw → OwnsAll P ny →
    OwnsAll P nw → CxP g P ny w → CertThrough g (y :: w :: P)

section
variable {g : GPathM} (c : PinCtx g)
include c

theorem step_range (q : PathNodeId) (nq : PNodeM) (hq : g.node? q = some nq) :
    0 ≤ q.id.step ∧ q.id.step < g.current_step := by
  have hm := List.mem_of_find?_eq_some hq
  have hid : nq.id = q := node?_id_eq g q nq hq
  exact ⟨by have := c.snn nq hm; rw [hid] at this; exact this,
    by have := c.below nq hm; rw [hid] at this; exact this⟩

omit c in
/-- Two nodes of a certificate own each other. -/
theorem cert_owns {sel : Int → PathNodeId} (hs : ChainSound g sel) (i j : Int) (hi0 : 0 ≤ i)
    (hi1 : i < g.current_step) (hj0 : 0 ≤ j) (hj1 : j < g.current_step) (nj : PNodeM)
    (hnj : g.node? (sel j) = some nj) : sel i ∈ nj.owners := by
  have h : sel i ∈ ownersOf g (sel j) := by
    cases e : decide (i = j) with
    | true =>
      have hij : i = j := of_decide_eq_true e
      rw [hij]; exact hs.self_owned j hj0 hj1
    | false =>
      have hij : i ≠ j := of_decide_eq_false e
      exact (List.mem_filter.mp (hs.chain.2.1 i j hi0 hj0 hi1 hj1 hij)).1
  unfold ownersOf at h; rw [hnj] at h; exact h

omit c in
theorem cert_node {sel : Int → PathNodeId} (hs : ChainSound g sel) (l : Int) (h0 : 0 ≤ l)
    (h1 : l < g.current_step) : ∃ nr, g.node? (sel l) = some nr :=
  Option.isSome_iff_exists.mp (hs.chain.1.1 l h0 h1).1

/-- **A certificate through `P`, `y` and `w` makes the link `P`-compatible.** -/
theorem cxP_of_cert (P : List PathNodeId) (hP : Clique g P) (y : PathNodeId) (ny : PNodeM)
    (hy : g.node? y = some ny) (w : PathNodeId) (nw : PNodeM) (hw : g.node? w = some nw)
    (hc : CertThrough g (y :: w :: P)) : CxP g P ny w := by
  obtain ⟨sel, hs, hon⟩ := hc
  have hyo : sel y.id.step = y := hon y List.mem_cons_self
  have hwo : sel w.id.step = w := hon w (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨hy0, hy1⟩ := step_range c y ny hy
  obtain ⟨hw0, hw1⟩ := step_range c w nw hw
  have hny : g.node? (sel y.id.step) = some ny := by rw [hyo]; exact hy
  have hnw : g.node? (sel w.id.step) = some nw := by rw [hwo]; exact hw
  refine ⟨nw, hw, ?_, fun l h0 h1 => ?_⟩
  · have := cert_owns hs w.id.step y.id.step hw0 hw1 hy0 hy1 ny hny
    rw [hwo] at this; exact this
  · obtain ⟨nr, hnr⟩ := cert_node hs l h0 h1
    refine ⟨sel l, cert_owns hs l y.id.step h0 h1 hy0 hy1 ny hny,
      cert_owns hs l w.id.step h0 h1 hw0 hw1 nw hnw, (hs.chain.1.1 l h0 h1).2, nr, hnr, fun p hp => ?_⟩
    have hpo : sel p.id.step = p := hon p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
    obtain ⟨np, hnp, _⟩ := hP p hp
    obtain ⟨hp0, hp1⟩ := step_range c p np hnp
    have := cert_owns hs p.id.step l hp0 hp1 h0 h1 nr hnr
    rw [hpo] at this; exact this

/-- **The characterization gives `CliqueTri`.** -/
theorem cliqueTri_of_certLink (h : CertLink g) : CliqueTri g := by
  intro P hP y ny w nw hy hw hyP hwP hC l h0 h1
  obtain ⟨sel, hs, hon⟩ := h P hP y ny w nw hy hw hyP hwP hC
  have hyo : sel y.id.step = y := hon y List.mem_cons_self
  have hwo : sel w.id.step = w := hon w (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨hy0, hy1⟩ := step_range c y ny hy
  obtain ⟨hw0, hw1⟩ := step_range c w nw hw
  have hny : g.node? (sel y.id.step) = some ny := by rw [hyo]; exact hy
  have hnw : g.node? (sel w.id.step) = some nw := by rw [hwo]; exact hw
  obtain ⟨nr, hnr⟩ := cert_node hs l h0 h1
  have hrs : (sel l).id.step = l := (hs.chain.1.1 l h0 h1).2
  have hro : sel (sel l).id.step = sel l := by rw [hrs]
  have hrP : OwnsAll P nr := fun p hp => by
    have hpo : sel p.id.step = p := hon p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
    obtain ⟨np, hnp, _⟩ := hP p hp
    obtain ⟨hp0, hp1⟩ := step_range c p np hnp
    have := cert_owns hs p.id.step l hp0 hp1 h0 h1 nr hnr
    rw [hpo] at this; exact this
  -- the certificate also goes through `y`, `sel l` and `P` (and `w`, `sel l` and `P`)
  have cy : CertThrough g (y :: sel l :: P) := ⟨sel, hs, fun q hq => by
    rcases List.mem_cons.mp hq with e | hq
    · rw [e]; exact hyo
    rcases List.mem_cons.mp hq with e | hq
    · rw [e]; exact hro
    · exact hon q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))⟩
  have cw : CertThrough g (w :: sel l :: P) := ⟨sel, hs, fun q hq => by
    rcases List.mem_cons.mp hq with e | hq
    · rw [e]; exact hwo
    rcases List.mem_cons.mp hq with e | hq
    · rw [e]; exact hro
    · exact hon q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))⟩
  exact ⟨sel l, cert_owns hs l y.id.step h0 h1 hy0 hy1 ny hny,
    cert_owns hs l w.id.step h0 h1 hw0 hw1 nw hnw, hrs, ⟨nr, hnr, hrP⟩,
    cxP_of_cert c P hP y ny hy (sel l) nr hnr cy, cxP_of_cert c P hP w nw hw (sel l) nr hnr cw⟩

/-- **The cut table of `y` relative to a clique is what the certificates through `y` and the clique
project.** -/
theorem cutTable_iff_cert (h : CertLink g) (P : List PathNodeId) (hP : Clique g P) (y : PathNodeId)
    (ny : PNodeM) (hy : g.node? y = some ny) (hyP : OwnsAll P ny) (r : PathNodeId) (nr : PNodeM)
    (hr : g.node? r = some nr) (hrP : OwnsAll P nr) :
    CxP g P ny r ↔ CertThrough g (y :: r :: P) :=
  ⟨h P hP y ny r nr hy hr hyP hrP, cxP_of_cert c P hP y ny hy r nr hr⟩
end

-- ============================================================
-- With the reader
-- ============================================================

variable (φ : Cnf)

/-- **The reader decides `φ` when every valid starting state satisfies the characterization.** -/
theorem readerVerdictW_iff_of_certLink (hbd : Bounded φ)
    (h0 : ∀ kv ∈ pureRun φ, isValid (filterAll kv.2 []) = true → CertLink (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ := by
  refine readerVerdictW_iff_of_cliqueTri φ hbd (fun kv hkv hv => ?_)
  have c := pinCtx_readPins φ hbd kv hkv [] _ ReadPins.start hv
  exact cliqueTri_of_certLink c (h0 kv hkv hv)

/-- info: 'AbsSatBin.GraphPath.Model.CertFix.cliqueTri_of_certLink' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cliqueTri_of_certLink

/-- info: 'AbsSatBin.GraphPath.Model.CertFix.readerVerdictW_iff_of_certLink' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_certLink

end AbsSatBin.GraphPath.Model.CertFix
