-- lean/improves_bin/AbsSatBin/GraphPath/Model/CertDescent.lean
import AbsSatBin.GraphPath.Model.CertFix

/-!
# `CliqueTri ⇒ CertLink`: growing a clique into a certificate

`CertFix.cliqueTri_of_certLink` gives one direction. This module gives the other, so on the reader's
states **`CliqueTri` and `CertLink` are the same statement** (`certLink_iff_cliqueTri`).

No pin and no restriction are needed: the certificate is grown as a clique.

* **Invariant** (`Wit g Q`): `Q` is a clique and, at every step, some live node owns all of `Q`.
* **Start**: for a `P`-compatible link `y–w`, the clique `y :: w :: P` has the invariant — the witnesses
  of the link own `P`, `y` and `w`.
* **Growth** (`grow`): at a step `l`, `TriP g Q` on the pair `(q, q)` gives a node `r` at step `l` with a
  `Q`-compatible link from `q`; its witnesses own `Q` and `r`, so `r :: Q` keeps the invariant.
* **End** (`chain_of_cover`): a clique with a node at every step has exactly one (a table holds only its
  node at its own step), and it is a certificate: the table entry one step below is the parent, one
  step above the son (`parent_of_owner`, `son_of_owner`), the step-0 node is the root.
-/

namespace AbsSatBin.GraphPath.Model.CertDescent

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.CliqueTri
open AbsSatBin.GraphPath.Model.TriPinCut (self_own_pc)
open AbsSatBin.GraphPath.Model.CertFix
open AbsSatBin.GraphPath.Model.AmbTriCore
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

/-- At every step, some live node owns all of `Q`. -/
def Wit (g : GPathM) (Q : List PathNodeId) : Prop :=
  ∀ l, 0 ≤ l → l < g.current_step → ∃ r nr, g.node? r = some nr ∧ r.id.step = l ∧ OwnsAll Q nr

section
variable {g : GPathM} (c : ACtx g)
include c

/-- **Growth**: a clique with witnesses gains a node at any step. -/
theorem grow (hT : CliqueTri g) (Q : List PathNodeId) (hQ : Clique g Q) (hW : Wit g Q)
    (q : PathNodeId) (hq : q ∈ Q) (l : Int) (h0 : 0 ≤ l) (h1 : l < g.current_step) :
    ∃ r, r.id.step = l ∧ Clique g (r :: Q) ∧ Wit g (r :: Q) := by
  have hk := c.pc.ker
  obtain ⟨nq, hnq, hqQ⟩ := hQ q hq
  -- `q` has a `Q`-compatible link to itself
  have hqq : CxP g Q nq q := ⟨nq, hnq, self_own_pc c.pc q nq hnq, fun l' h0' h1' => by
    obtain ⟨r, nr, hnr, hrs, hrQ⟩ := hW l' h0' h1'
    have hrq : r ∈ nq.owners := hk.sym r nr q nq hnr hnq (hrQ q hq)
    exact ⟨r, hrq, hrq, hrs, nr, hnr, hrQ⟩⟩
  obtain ⟨r, _, _, hrs, ⟨nr, hnr, hrQ⟩, cqr, _⟩ := hT Q hQ q nq q nq hnq hnq hqQ hqQ hqq l h0 h1
  refine ⟨r, hrs, fun p hp => ?_, fun l' h0' h1' => ?_⟩
  · rcases List.mem_cons.mp hp with e | hp
    · rw [e]
      refine ⟨nr, hnr, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact self_own_pc c.pc r nr hnr
      · exact hrQ s hs
    · obtain ⟨np, hnp, hpQ⟩ := hQ p hp
      refine ⟨np, hnp, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact hk.sym r nr p np hnr hnp (hrQ p hp)
      · exact hpQ s hs
  · -- the witnesses of the link `q–r` own `Q` and `r`
    obtain ⟨nr', hnr', _, hl⟩ := cqr
    rw [hnr] at hnr'; cases hnr'
    obtain ⟨s, _, hsr, hss, ns, hns, hsQ⟩ := hl l' h0' h1'
    refine ⟨s, ns, hns, hss, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with e | hp
    · rw [e]; exact hk.sym r nr s ns hnr hns hsr
    · exact hsQ p hp

/-- **Covering**: a clique with witnesses grows into one with a node at every step. -/
theorem cover (hT : CliqueTri g) (Q : List PathNodeId) (hQ : Clique g Q) (hW : Wit g Q) (q : PathNodeId)
    (hq : q ∈ Q) : ∀ m : Nat, ∃ Q', (∀ p ∈ Q, p ∈ Q') ∧ Clique g Q' ∧ Wit g Q' ∧
      ∀ l, 0 ≤ l → l < (m : Int) → l < g.current_step → ∃ p ∈ Q', p.id.step = l := by
  intro m
  induction m with
  | zero => exact ⟨Q, fun p hp => hp, hQ, hW, fun l h0 h1 _ => absurd h1 (by omega)⟩
  | succ m ih =>
    obtain ⟨Q', hsub, hQ', hW', hcov⟩ := ih
    by_cases hm : (m : Int) < g.current_step
    · obtain ⟨r, hrs, hQr, hWr⟩ := grow c hT Q' hQ' hW' q (hsub q hq) m (by omega) hm
      refine ⟨r :: Q', fun p hp => List.mem_cons_of_mem _ (hsub p hp), hQr, hWr, fun l h0 h1 h2 => ?_⟩
      rcases Int.lt_or_le l m with hl | hl
      · obtain ⟨p, hp, hps⟩ := hcov l h0 hl h2
        exact ⟨p, List.mem_cons_of_mem _ hp, hps⟩
      · exact ⟨r, List.mem_cons_self, by rw [hrs]; omega⟩
    · exact ⟨Q', hsub, hQ', hW', fun l h0 h1 h2 => hcov l h0 (by omega) h2⟩

/-- Two members of a clique at the same step are the same node. -/
theorem clique_step_eq (Q : List PathNodeId) (hQ : Clique g Q) (p q : PathNodeId) (hp : p ∈ Q)
    (hq : q ∈ Q) (hs : p.id.step = q.id.step) : p = q := by
  obtain ⟨nq, hnq, hqQ⟩ := hQ q hq
  have hid : nq.id = q := node?_id_eq g q nq hnq
  have := c.pc.oos nq (List.mem_of_find?_eq_some hnq) p (hqQ p hp) (by rw [hid, hs])
  rw [hid] at this; exact this

/-- The member of a clique at step `l`. -/
def pick (Q : List PathNodeId) (l : Int) : PathNodeId :=
  (Q.find? (fun q => q.id.step == l)).getD ⟨⟨l, 0⟩, none, none⟩

omit c in
theorem pick_spec (Q : List PathNodeId) (l : Int) (p : PathNodeId) (hp : p ∈ Q) (hps : p.id.step = l) :
    pick Q l ∈ Q ∧ (pick Q l).id.step = l := by
  unfold pick
  cases e : Q.find? (fun q => q.id.step == l) with
  | none =>
    have := List.find?_eq_none.mp e p hp
    rw [beq_iff_eq.mpr hps] at this
    exact absurd rfl this
  | some q => exact ⟨List.mem_of_find?_eq_some e, eq_of_beq (List.find?_some (p := fun q : PathNodeId => q.id.step == l) e)⟩

/-- **A clique with a node at every step is a certificate.** -/
theorem chain_of_cover (Q : List PathNodeId) (hQ : Clique g Q)
    (hcov : ∀ l, 0 ≤ l → l < g.current_step → ∃ p ∈ Q, p.id.step = l) :
    ChainSound g (pick Q) ∧ ∀ q ∈ Q, pick Q q.id.step = q := by
  have hk := c.pc.ker
  have spec : ∀ l, 0 ≤ l → l < g.current_step → pick Q l ∈ Q ∧ (pick Q l).id.step = l := by
    intro l h0 h1
    obtain ⟨p, hp, hps⟩ := hcov l h0 h1
    exact pick_spec Q l p hp hps
  have node : ∀ l, 0 ≤ l → l < g.current_step → ∃ n, g.node? (pick Q l) = some n ∧ OwnsAll Q n := by
    intro l h0 h1
    obtain ⟨n, hn, hnQ⟩ := hQ _ (spec l h0 h1).1
    exact ⟨n, hn, hnQ⟩
  have hon : ∀ q ∈ Q, pick Q q.id.step = q := by
    intro q hq
    obtain ⟨nq, hnq, _⟩ := hQ q hq
    have hr := step_range c.pc q nq hnq
    obtain ⟨hm, hs⟩ := spec q.id.step hr.1 hr.2
    exact clique_step_eq c Q hQ _ q hm hq hs
  refine ⟨⟨⟨⟨fun k h0 h1 => ?_, fun k h0 h1 => ?_⟩, fun i j hi0 hj0 hi1 hj1 _ => ?_,
    fun k h0 h1 => ?_⟩, fun k h0 h1 => ?_, fun k h0 h1 => ?_, ?_, fun k h0 h1 => ?_⟩, hon⟩
  · obtain ⟨n, hn, _⟩ := node k h0 h1
    exact ⟨by rw [hn]; rfl, (spec k h0 h1).2⟩
  · -- the parent link
    obtain ⟨n, hn, hnQ⟩ := node (k + 1) (by omega) h1
    have hs1 := (spec (k + 1) (by omega) h1).2
    have hs0 := (spec k h0 (by omega)).2
    obtain ⟨hpar, _⟩ := parent_of_owner c.pc (pick Q (k + 1)) n hn (by rw [hs1]; omega) (pick Q k)
      (hnQ _ (spec k h0 (by omega)).1) (by rw [hs0, hs1]; omega)
    rw [hn]; exact hpar
  · obtain ⟨n, hn, hnQ⟩ := node j hj0 hj1
    refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr (spec i hi0 hi1).2⟩
    unfold ownersOf; rw [hn]; exact hnQ _ (spec i hi0 hi1).1
  · obtain ⟨n, hn, _⟩ := node k h0 h1
    exact hk.gow _ n hn
  · obtain ⟨n, hn, hnQ⟩ := node k h0 h1
    unfold ownersOf; rw [hn]; exact hnQ _ (spec k h0 h1).1
  · -- the son link
    obtain ⟨n, hn, hnQ⟩ := node k h0 (by omega)
    have hs1 := (spec (k + 1) (by omega) h1).2
    have hs0 := (spec k h0 (by omega)).2
    obtain ⟨hson, _⟩ := son_of_owner c.pc (pick Q k) n hn (by rw [hs0]; omega) (pick Q (k + 1))
      (hnQ _ (spec (k + 1) (by omega) h1).1) (by rw [hs0, hs1])
    unfold sonsOf; rw [hn]; exact hson
  · -- the root
    unfold pick
    cases e : Q.find? (fun q => q.id.step == (0 : Int)) with
    | none => rfl
    | some q =>
      have hq := List.mem_of_find?_eq_some e
      have hqs : q.id.step = 0 := eq_of_beq (List.find?_some (p := fun q : PathNodeId => q.id.step == (0 : Int)) e)
      obtain ⟨nq, hnq, _⟩ := hQ q hq
      have hid : nq.id = q := node?_id_eq g q nq hnq
      have := c.rc.rootz nq (List.mem_of_find?_eq_some hnq) (by rw [hid, hqs])
      rw [hid] at this; exact this
  · obtain ⟨n, hn, _⟩ := node k (by omega) h1
    have hm := List.mem_of_find?_eq_some hn
    have hid : n.id = pick Q k := node?_id_eq g _ n hn
    have := c.rc.shape.notroot n hm (by rw [hid, (spec k (by omega) h1).2]; exact h0)
    rw [hid] at this; exact this
/-- **`CliqueTri ⇒ CertLink`.** -/
theorem certLink_of_cliqueTri (hT : CliqueTri g) : CertLink g := by
  have hk := c.pc.ker
  intro P hP y ny w nw hy hw hyP hwP hC
  have hwy : w ∈ ny.owners := by obtain ⟨_, _, h, _⟩ := hC; exact h
  -- `y :: w :: P` is a clique with witnesses
  have hQ0 : Clique g (y :: w :: P) := by
    intro q hq
    rcases List.mem_cons.mp hq with e | hq
    · rw [e]
      refine ⟨ny, hy, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact self_own_pc c.pc y ny hy
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact hwy
      · exact hyP s hs
    rcases List.mem_cons.mp hq with e | hq
    · rw [e]
      refine ⟨nw, hw, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact hk.sym y ny w nw hy hw hwy
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact self_own_pc c.pc w nw hw
      · exact hwP s hs
    · obtain ⟨np, hnp, hpP⟩ := hP q hq
      refine ⟨np, hnp, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact hk.sym y ny q np hy hnp (hyP q hq)
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact hk.sym w nw q np hw hnp (hwP q hq)
      · exact hpP s hs
  have hW0 : Wit g (y :: w :: P) := by
    intro l h0 h1
    obtain ⟨nw', hnw', _, hl⟩ := hC
    rw [hw] at hnw'; cases hnw'
    obtain ⟨r, hr, hrw, hrs, nr, hnr, hrP⟩ := hl l h0 h1
    refine ⟨r, nr, hnr, hrs, fun s hs => ?_⟩
    rcases List.mem_cons.mp hs with e | hs
    · rw [e]; exact hk.sym y ny r nr hy hnr hr
    rcases List.mem_cons.mp hs with e | hs
    · rw [e]; exact hk.sym w nw r nr hw hnr hrw
    · exact hrP s hs
  obtain ⟨Q, hsub, hQ, _, hcov⟩ := cover c hT _ hQ0 hW0 y List.mem_cons_self g.current_step.toNat
  obtain ⟨hs, hon⟩ := chain_of_cover c Q hQ (fun l h0 h1 => hcov l h0 (by omega) h1)
  exact ⟨pick Q, hs, fun q hq => hon q (hsub q hq)⟩

/-- **On the reader's states, `CertLink` and `CliqueTri` are the same statement.** -/
theorem certLink_iff_cliqueTri : CertLink g ↔ CliqueTri g :=
  ⟨cliqueTri_of_certLink c.pc, certLink_of_cliqueTri c⟩
end

/-- info: 'AbsSatBin.GraphPath.Model.CertDescent.certLink_iff_cliqueTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certLink_iff_cliqueTri

end AbsSatBin.GraphPath.Model.CertDescent
