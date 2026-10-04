-- lean_project/AbsSat/GraphPath/Model/SeqPin.lean
import AbsSat.GraphPath.Model.NodeLevel
import AbsSat.GraphPath.Model.SupportSplit
import AbsSat.GraphPath.Model.OraclePath

/-!
# Pinning all at once is pinning one by one

The author's reading of the pins (v143): each requirement forces every partially built path the set
represents through one node — the literal's required value. Forcing through `x`, then `y`, then `z` is
then the same as forcing through all three at once. Measured (probe `helly seqpin`, every send of the
run with at least two pins, K4, parity, prism, K3,3): **identical tables in all 614 valid sends, same
validity in all 2,534**.

This module proves it, as a fixpoint fact:

* **`seq_eq_all`** — from a reader-context state, pinning a list of map nodes at once and reviewing
  (`filterAllAgg g rs`), and pinning them one by one with a review after each (`pinOneByOne g rs`), give
  states that sit inside each other (`Embedded` both ways); if the first is valid, so is the second. Each
  one's tables are a support relation inside the start that carries every pin, so they survive the
  other's pins and reviews (`AOk_filterAllAgg`, the greatest-fixpoint property).
* **`chainSound_of_embedded`, `tablesSound_of_embedded`** — chains move across an embedding, so exactness
  moves across a double embedding.
* **`multiPinExact`** — on a valid exact reader's state, pinning several map nodes at once keeps it exact
  under `ReaderPinExact` (one pin) alone; with `NodeLevel`, under the pair level alone
  (**`multiPinExact_of_pairs`**). Several pins cost nothing beyond one.
-/

namespace AbsSat.GraphPath.Model.SeqPin

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup AOk AOk_filterAllAgg SMP_filterAllAgg)
open AbsSat.GraphPath.Model.BranchRun (embedded_of_pruned isValid_of_embedded)
open AbsSat.GraphPath.Model.AggFixpoint (aggOk_reviewAgg)
open AbsSat.GraphPath.Model.BranchCompat (pinOneByOne)
open AbsSat.GraphPath.Model.BranchLines (embedded_refl)
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes)
open AbsSat.GraphPath.Model.ReaderComplete (ReaderPinExact)
open AbsSat.GraphPath.Model.SupportSplit (embedded_of_cover)

-- ============================================================
-- Carrying facts along one-by-one pinning
-- ============================================================

theorem pruned_pinOneByOne : ∀ (rs : List NodeId) (g : GPathM), Pruned g (pinOneByOne g rs) := by
  intro rs
  induction rs with
  | nil => intro g; exact Pruned.refl g
  | cons r rest ih =>
    intro g
    exact Pruned.trans (pruned_filterAllAgg g [r]) (ih (filterAllAgg g [r]))

/-- Along one-by-one pinning, a state keeps the reader's context and the parent/son facts. -/
theorem facts_pinOneByOne : ∀ (rs : List NodeId) (g : GPathM), Reader.RCtx g → Sons.SMP g → Sons.PMS g →
    Sons.SN g → Reader.RCtx (pinOneByOne g rs) ∧ Sons.SMP (pinOneByOne g rs) ∧
      Sons.PMS (pinOneByOne g rs) ∧ Sons.SN (pinOneByOne g rs) := by
  intro rs
  induction rs with
  | nil => intro g hc hs hp hn; exact ⟨hc, hs, hp, hn⟩
  | cons r rest ih =>
    intro g hc hs hp hn
    exact ih (filterAllAgg g [r]) (RCtx_of_readableAgg _ ⟨g, [r], hc, rfl⟩)
      (AnchoredSurvive.SMP_filterAllAgg g hs hc.shape.notroot [r])
      (AggInvariants.PMS_filterAllAgg g [r] hp) (AggInvariants.SN_filterAllAgg g [r] hn)

/-- A support relation that respects every pin survives one-by-one pinning. -/
theorem AOk_pinOneByOne {S : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop} :
    ∀ (rs : List NodeId) (g : GPathM), AOk g S R →
      (∀ r ∈ rs, ∀ p, S p → p.id.step = r.step → p.id = r) → AOk (pinOneByOne g rs) S R := by
  intro rs
  induction rs with
  | nil => intro g h _; exact h
  | cons r rest ih =>
    intro g h hpin
    exact ih (filterAllAgg g [r])
      (AOk_filterAllAgg g h [r] (fun r' hr' => by
        rw [List.mem_singleton.mp hr']; exact hpin r List.mem_cons_self))
      (fun r' hr' => hpin r' (List.mem_cons_of_mem _ hr'))

/-- The global owners left by a list of pins carry every pin. -/
theorem gowners_foldl_pin : ∀ (rs : List NodeId) (g : GPathM) (q : PathNodeId),
    q ∈ (rs.foldl filterRequire g).gowners → q ∈ g.gowners ∧
      ∀ r ∈ rs, q.id.step = r.step → q.id = r := by
  intro rs
  induction rs with
  | nil => intro g q hq; exact ⟨hq, fun r hr => absurd hr List.not_mem_nil⟩
  | cons r rest ih =>
    intro g q hq
    obtain ⟨h1, h2⟩ := ih (filterRequire g r) q hq
    have h1' := List.mem_filter.mp h1
    refine ⟨h1'.1, fun r' hr' hs => ?_⟩
    rcases List.mem_cons.mp hr' with rfl | hr''
    · have h3 := h1'.2
      have hne : (q.id.step != r'.step) = false := by rw [hs]; exact bne_self_eq_false _
      rw [hne, Bool.false_or] at h3
      exact eq_of_beq h3
    · exact h2 r' hr'' hs

-- ============================================================
-- Chains move across an embedding
-- ============================================================

/-- **A chain of `B` is a chain of any state `G` that contains `B`.** Every node of the chain is a node
of `B`, so the embedding keeps its owners and parents among them; the son links come back from the
parents (`SMP`). -/
theorem chainSound_of_embedded {B G : GPathM} (e : Embedded B G) (hs : Sons.SMP G)
    (sel : Int → PathNodeId) (h : ChainSound B sel) : ChainSound G sel := by
  obtain ⟨⟨⟨hnode, hpar⟩, hpw, hgow⟩, hself, _, hroot⟩ := h
  have hstep := e.step
  have mem : ∀ k, 0 ≤ k → k < G.current_step → Mem B (sel k) := by
    intro k h0 h1
    have := (hnode k h0 (by rw [hstep]; exact h1)).1
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp this
    exact ⟨m, hm⟩
  -- owners of chain nodes carry over
  have own : ∀ j, 0 ≤ j → j < G.current_step → ∀ q, q ∈ ownersOf B (sel j) → Mem B q →
      q ∈ ownersOf G (sel j) := by
    intro j h0 h1 q hq hqm
    obtain ⟨m, hm⟩ := mem j h0 h1
    obtain ⟨n, hn, ho, _⟩ := e.node _ m hm
    unfold ownersOf at hq ⊢
    rw [hm] at hq
    rw [hn]
    exact ho q hq hqm
  -- parents of chain nodes carry over
  have par : ∀ k, 0 ≤ k → k + 1 < G.current_step →
      sel k ∈ ((G.node? (sel (k + 1))).map PNodeM.parents).getD [] := by
    intro k h0 h1
    have hp := hpar k h0 (by rw [hstep]; exact h1)
    obtain ⟨m, hm⟩ := mem (k + 1) (by omega) h1
    obtain ⟨n, hn, _, hpp⟩ := e.node _ m hm
    rw [hm] at hp
    rw [hn]
    exact hpp _ hp (mem k h0 (by omega))
  refine ⟨⟨⟨fun k h0 h1 => ?_, par⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := mem k h0 h1
    obtain ⟨n, hn, _⟩ := e.node _ m hm
    exact ⟨by rw [hn]; rfl, (hnode k h0 (by rw [hstep]; exact h1)).2⟩
  · intro i j hi hj hi1 hj1 hij
    have hq := hpw i j hi hj (by rw [hstep]; exact hi1) (by rw [hstep]; exact hj1) hij
    obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
    exact List.mem_filter.mpr ⟨own j hj hj1 _ hq1 (mem i hi hi1), hq2⟩
  · intro k h0 h1
    exact e.gow _ (hgow k h0 (by rw [hstep]; exact h1))
  · intro k h0 h1
    exact own k h0 h1 _ (hself k h0 (by rw [hstep]; exact h1)) (mem k h0 h1)
  · intro k h0 h1
    have hp := par k h0 h1
    obtain ⟨m, hm⟩ := mem (k + 1) (by omega) h1
    obtain ⟨n, hn, _⟩ := e.node _ m hm
    obtain ⟨m0, hm0⟩ := mem k h0 (by omega)
    obtain ⟨n0, hn0, _⟩ := e.node _ m0 hm0
    rw [hn] at hp
    have hnid := node?_id_eq G _ n hn
    have hn0id := node?_id_eq G _ n0 hn0
    have := hs n (List.mem_of_find?_eq_some hn) (sel k) hp n0 (List.mem_of_find?_eq_some hn0) hn0id
    unfold sonsOf
    rw [hn0, ← hnid]
    exact this
  · exact ⟨hroot.1, fun k h0 h1 => hroot.2 k h0 (by rw [hstep]; exact h1)⟩

/-- Exactness moves down an embedding that goes both ways: if `S` is exact and `A` sits inside `S` and
`S` inside `A`, then `A` is exact. -/
theorem tablesSound_of_embedded {A S : GPathM} (eAS : Embedded A S) (eSA : Embedded S A)
    (adA : AdjacentOwners.Adj A) (hsA : Sons.SMP A) (ht : TablesSound S) : TablesSound A := by
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  obtain ⟨n', hn', ho, _⟩ := eAS.node x n hx
  have hqm : Mem A q := by
    have hg := adA.ctx.ownGow x n hx q hqn hq0 hq1
    obtain ⟨m, hm, hid⟩ := adA.ctx.gn q hg
    exact ⟨m, by rw [← hid]; exact node?_of_mem adA.rc.nodup m hm⟩
  obtain ⟨sel, hsc, h1, h2⟩ := ht x n' hn' hx0 (by rw [← eAS.step]; exact hx1) q hq0
    (by rw [← eAS.step]; exact hq1) (ho q hqn hqm)
  exact ⟨sel, chainSound_of_embedded eSA hsA sel hsc, h1, h2⟩

-- ============================================================
-- All at once versus one by one
-- ============================================================

/-- **Pinning all at once is pinning one by one**: from a reader-context state, if the simultaneous pin
is valid, the sequential one is valid too, and the two results sit inside each other. -/
theorem seq_eq_all (g : GPathM) (hc : Reader.RCtx g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g)
    (hsn : Sons.SN g) (r : NodeId) (rest : List NodeId)
    (hvA : isValid (filterAllAgg g (r :: rest)) = true) :
    isValid (pinOneByOne g (r :: rest)) = true ∧
    Embedded (filterAllAgg g (r :: rest)) (pinOneByOne g (r :: rest)) ∧
    Embedded (pinOneByOne g (r :: rest)) (filterAllAgg g (r :: rest)) := by
  have hnr := hc.shape.notroot
  -- facts on the simultaneous pin
  have hRA : ReadableAgg (filterAllAgg g (r :: rest)) := ⟨g, r :: rest, hc, rfl⟩
  have hprA := pruned_filterAllAgg g (r :: rest)
  have hsA := SMP_filterAllAgg g hsmp hnr (r :: rest)
  have adA := AdjacentOwners.adj_of_readable _ hRA hvA
    (AggInvariants.PMS_filterAllAgg g (r :: rest) hpms) (AggInvariants.SN_filterAllAgg g (r :: rest) hsn)
  have okA : AggFixpoint.AggOk (filterAllAgg g (r :: rest)) := aggOk_reviewAgg _ hvA
  -- facts on the sequential pin
  have hprS := pruned_pinOneByOne (r :: rest) g
  obtain ⟨_, hsS, hpS, hnS⟩ := facts_pinOneByOne (r :: rest) g hc hsmp hpms hsn
  have hRS : ReadableAgg (pinOneByOne g (r :: rest)) :=
    BranchReader.readable_pinOneByOne (filterAllAgg g [r]) ⟨g, [r], hc, rfl⟩ rest
  have hstep : (filterAllAgg g (r :: rest)).current_step = (pinOneByOne g (r :: rest)).current_step :=
    hprA.step_eq.trans hprS.step_eq.symm
  -- the simultaneous pin's tables: a support inside `g` carrying every pin
  have supA : Sup g (Mem (filterAllAgg g (r :: rest))) (Rel (filterAllAgg g (r :: rest))) :=
    sup_of_embedded _ g adA okA hsA (embedded_of_pruned hprA hc.nodup (embedded_refl g))
  have selfA := sup_of_embedded _ _ adA okA hsA (embedded_refl _)
  have pinA : ∀ r' ∈ r :: rest, ∀ p, Mem (filterAllAgg g (r :: rest)) p → p.id.step = r'.step →
      p.id = r' := by
    intro r' hr' p hp hs
    have hg' := (pruned_reviewAgg ((r :: rest).foldl filterRequire g)).gowners_sub p (selfA.gow p hp)
    exact (gowners_foldl_pin (r :: rest) g p hg').2 r' hr' hs
  have hAS := (AOk_pinOneByOne (r :: rest) g ⟨supA, hsmp, hnr⟩ pinA).sup
  have eAS := embedded_of_cover _ adA _ _ _ hAS hstep (fun _ _ h => h)
  have hvS : isValid (pinOneByOne g (r :: rest)) = true := isValid_of_embedded eAS hvA
  -- the sequential pin's tables: a support inside `g` carrying every pin
  have adS := AdjacentOwners.adj_of_readable _ hRS hvS hpS hnS
  have okS : AggFixpoint.AggOk (pinOneByOne g (r :: rest)) := by
    obtain ⟨g₀, rq, _, heq⟩ := hRS
    rw [heq] at hvS ⊢
    exact aggOk_reviewAgg _ hvS
  have supS : Sup g (Mem (pinOneByOne g (r :: rest))) (Rel (pinOneByOne g (r :: rest))) :=
    sup_of_embedded _ g adS okS hsS (embedded_of_pruned hprS hc.nodup (embedded_refl g))
  have selfS := sup_of_embedded _ _ adS okS hsS (embedded_refl _)
  have pinS : ∀ r' ∈ r :: rest, ∀ p, Mem (pinOneByOne g (r :: rest)) p → p.id.step = r'.step →
      p.id = r' := fun r' hr' p hp hs =>
    OraclePath.pinned_ids (r :: rest) g r' hr' p (selfS.gow p hp) hs
  have hSA := (AOk_filterAllAgg g ⟨supS, hsmp, hnr⟩ (r :: rest) pinS).sup
  have eSA := embedded_of_cover _ adS _ _ _ hSA hstep.symm (fun _ _ h => h)
  exact ⟨hvS, eAS, eSA⟩

/-- info: 'AbsSat.GraphPath.Model.SeqPin.seq_eq_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seq_eq_all

-- ============================================================
-- Several pins cost nothing beyond one
-- ============================================================

/-- One-by-one pinning keeps a readable state exact as long as each single pin does. -/
theorem tablesSound_pinOneByOne (hRP : ReaderPinExact) : ∀ (rs : List NodeId) (h : GPathM),
    ReadableAgg h → isValid h = true → TablesSound h → isValid (pinOneByOne h rs) = true →
      TablesSound (pinOneByOne h rs) := by
  intro rs
  induction rs with
  | nil => intro h _ _ ht _; exact ht
  | cons q rest ih =>
    intro h hR hv ht hvS
    have hR' := ReadableAgg_filterAllAgg h hR [q]
    have hv' : isValid (filterAllAgg h [q]) = true :=
      isValid_of_embedded (Hereditary.embedded_of_pruned_self (pruned_pinOneByOne rest _)
        (RCtx_of_readableAgg _ hR').nodup) hvS
    exact ih _ hR' hv' (hRP h hR hv ht q hv') hvS

/-- **Several pins at once keep a readable state exact, as soon as one pin does.** On a valid exact
reader's state, pinning any list of map nodes at once and reviewing leaves it exact under `ReaderPinExact`
alone: the simultaneous pin is the sequential one (`seq_eq_all`), the sequential one is single pins, and
exactness moves across the double embedding. -/
theorem multiPinExact (hRP : ReaderPinExact) (g : GPathM) (hR : ReadableAgg g) (hv : isValid g = true)
    (ht : TablesSound g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g) (hsn : Sons.SN g)
    (r : NodeId) (rest : List NodeId) (hvA : isValid (filterAllAgg g (r :: rest)) = true) :
    TablesSound (filterAllAgg g (r :: rest)) := by
  have hc := RCtx_of_readableAgg g hR
  obtain ⟨hvS, eAS, eSA⟩ := seq_eq_all g hc hsmp hpms hsn r rest hvA
  have hRA : ReadableAgg (filterAllAgg g (r :: rest)) := ⟨g, r :: rest, hc, rfl⟩
  have adA := AdjacentOwners.adj_of_readable _ hRA hvA
    (AggInvariants.PMS_filterAllAgg g (r :: rest) hpms) (AggInvariants.SN_filterAllAgg g (r :: rest) hsn)
  exact tablesSound_of_embedded eAS eSA adA (SMP_filterAllAgg g hsmp hc.shape.notroot (r :: rest))
    (tablesSound_pinOneByOne hRP (r :: rest) g hR hv ht hvS)

/-- **And the pairs are all that is left**: several pins at once keep a valid exact reader's state exact
under the pair level alone. -/
theorem multiPinExact_of_pairs (h : NodeLevel.PairPinExact) (g : GPathM) (hR : ReadableAgg g)
    (hv : isValid g = true) (ht : TablesSound g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g)
    (hsn : Sons.SN g) (r : NodeId) (rest : List NodeId)
    (hvA : isValid (filterAllAgg g (r :: rest)) = true) : TablesSound (filterAllAgg g (r :: rest)) :=
  multiPinExact (NodeLevel.readerPinExact_of_pairs h) g hR hv ht hsmp hpms hsn r rest hvA

/-- info: 'AbsSat.GraphPath.Model.SeqPin.tablesSound_of_embedded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_of_embedded

/-- info: 'AbsSat.GraphPath.Model.SeqPin.multiPinExact_of_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms multiPinExact_of_pairs

end AbsSat.GraphPath.Model.SeqPin
