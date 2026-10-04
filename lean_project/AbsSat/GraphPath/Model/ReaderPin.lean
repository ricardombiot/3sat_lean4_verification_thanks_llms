-- lean_project/AbsSat/GraphPath/Model/ReaderPin.lean
import AbsSat.GraphPath.Model.AuthorReader
import AbsSat.GraphPath.Model.RemovalClosure

/-!
# Attacking `AuthorReadable`: one pin at a time

`AuthorReader.authorRead_final` leaves one hypothesis, `AuthorReadable`: every value the author's
reader picks lies on a chain of the state it is standing in. That is existential and global. This
module trades it for a condition on owner entries, checked one pinned step at a time.

* `unsupported_removed_rctx` — the review removes every unsupported node in any state of the reader's
  class `Reader.RCtx`, not only in reachable ones (the proof of `unsupported_removed` only used
  unique ids, global owners being nodes and the parent shape, all carried by `RCtx`).
* `pin_survivor_owns` — after pinning `d`, a surviving node has, in its owner table, an entry named
  `d` that is a global owner. Otherwise it would have no support at `d`'s step.
* `OwnersSoundAt g k` — every owner entry at step `k` that is a global owner is backed by a real
  chain through both nodes. A statement about pairs, one step at a time.
* `pin_exact` — **with `OwnersSoundAt` at the pinned step, every node that survives the pin lies on
  a chain of the pinned state.** No Helly argument: the chain comes from the entry, and a chain
  through the pinned node survives the pin.
* `authorChoice_spec` — in a valid state the author's pick is a node at the value step.
* `PinsSound` and `authorReadable_of_pinsSound` — **`AuthorReadable` follows from the first pick
  lying on a chain and `OwnersSoundAt` holding at every step the reader pins.**
* `authorRead_of_pinsSound` — so the author's reader reads a model under those hypotheses.

Where the difficulty went: `OwnersSoundAt` at the first pinned step is a property of the machine's
final state (no stale entries toward that step). At later steps it is asked of pinned states, where
an entry can be backed by chains that do not go through the earlier pins; that is where a Helly gap
could reappear, and it is what to measure and to attack next.
-/

namespace AbsSat.GraphPath.Model.ReaderPin

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PureDriver
open AbsSat.GraphPath.Model.PartialPaths
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.RemovalClosure
open AbsSat.GraphPath.Model.AuthorReader

-- ============================================================
-- The review removes the unsupported, in the reader's class
-- ============================================================

theorem unsupported_removed_rctx (g : GPathM) (hc : Reader.RCtx g)
    (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true) {x : PathNodeId}
    (hx : Unsupported (reqs.foldl filterRequire g) x) : (filterAll g reqs).node? x = none := by
  have hpr : Pruned (reqs.foldl filterRequire g) (filterAll g reqs) := pruned_review _
  have hs := hpr.step_eq
  have hnd : NodupIds (reqs.foldl filterRequire g) := by
    unfold NodupIds
    rw [RemovalClosure.foldl_filterRequire_nodes]
    exact hc.nodup
  have hgn := GownersNodes.GN_filterAll g reqs hc.gn
  have hshape := Parents.Shape_of_pruned_pn (pruned_filterAll g reqs)
    (Parents.PN_filterAll g reqs hc.shape.pn) hc.shape
  have hlift : ∀ y d, (filterAll g reqs).node? y = some d →
      ∃ n, (reqs.foldl filterRequire g).node? y = some n ∧ (∀ q ∈ d.owners, q ∈ n.owners) ∧
        (∀ p ∈ d.parents, p ∈ n.parents) := by
    intro y d hd
    obtain ⟨n, hn, hid, ho, hp⟩ := hpr.nodes_derived d (List.mem_of_find?_eq_some hd)
    have hdid : d.id = y := node?_id_eq _ y d hd
    refine ⟨n, ?_, ho, hp⟩
    rw [← hdid, hid]
    exact node?_of_mem hnd n hn
  induction hx with
  | noSupport x n hn k h0 hk hprem ih =>
    cases hd : (filterAll g reqs).node? x with
    | none => rfl
    | some d =>
      exfalso
      obtain ⟨n', hn', ho, _⟩ := hlift x d hd
      have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
      have hval := review_node_valid (reqs.foldl filterRequire g) hv x d hd
      have hk' : k < (filterAll g reqs).current_step := by rw [hs]; exact hk
      have hent := LocalContradiction.ownersOk_of_isValidNode _ d hval k h0 hk'
      simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
      obtain ⟨q, hq, hqs⟩ := hent
      have hqg : q ∈ (filterAll g reqs).gowners :=
        owners_mem_gowners _ d (review_owners_within_gowners (reqs.foldl filterRequire g) hv x d hd)
          q hq (hasStepEntry_of_isValid _ hv _ (by rw [hqs]; exact h0) (by rw [hqs]; exact hk'))
      have hqn : q ∈ ownersAt n.owners k := by
        refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hqs⟩
        rw [← hnn]
        exact ho q hq
      have hnone := ih q hqn (hpr.gowners_sub q hqg)
      obtain ⟨m, hm⟩ :=
        Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff _ q).mp (hgn q hqg))
      rw [hnone] at hm
      cases hm
  | noParent x n hn hstep hprem ih =>
    cases hd : (filterAll g reqs).node? x with
    | none => rfl
    | some d =>
      exfalso
      obtain ⟨n', hn', _, hp⟩ := hlift x d hd
      have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
      have hdmem : d ∈ (filterAll g reqs).nodes := List.mem_of_find?_eq_some hd
      have hdid : d.id = x := node?_id_eq _ x d hd
      have hval := review_node_valid (reqs.foldl filterRequire g) hv x d hd
      have hroot : d.id.parent_id ≠ none := hshape.notroot d hdmem (by rw [hdid]; exact hstep)
      have hne := PathExists.parents_ne_nil_of_isValidNode _ d hval hroot
      obtain ⟨p, rest, hcons⟩ : ∃ p rest, d.parents = p :: rest := by
        cases hl : d.parents with
        | nil => exact absurd hl hne
        | cons a b => exact ⟨a, b, rfl⟩
      have hpmem : p ∈ d.parents := by rw [hcons]; exact List.mem_cons_self ..
      obtain ⟨m, hm, hmid⟩ := hshape.pn d hdmem p hpmem
      have hsomeh : ((filterAll g reqs).node? p).isSome = true :=
        (GownersNodes.hasNode_iff _ p).mp ⟨m, hm, hmid⟩
      obtain ⟨m0, hm0⟩ := Option.isSome_iff_exists.mp hsomeh
      obtain ⟨np, hnp, _, _⟩ := hlift p m0 hm0
      have hsomeP : ((reqs.foldl filterRequire g).node? p).isSome = true := by rw [hnp]; rfl
      have hpn : p ∈ n.parents := by rw [← hnn]; exact hp p hpmem
      have hnone := ih p hpn hsomeP
      rw [hnone] at hm0
      cases hm0

-- ============================================================
-- One pin
-- ============================================================

/-- After pinning `d`, a surviving node has an owner entry named `d` that is a global owner. -/
theorem pin_survivor_owns (g : GPathM) (hc : Reader.RCtx g) (d : NodeId)
    (hv : isValid (filterAll g [d]) = true) (x : PathNodeId)
    (hx : ((filterAll g [d]).node? x).isSome = true) (n : PNodeM) (hn : g.node? x = some n)
    (h0 : 0 ≤ d.step) (hk : d.step < g.current_step) :
    ∃ q ∈ ownersAt n.owners d.step, q.id = d ∧ q ∈ g.gowners := by
  cases hb : (ownersAt n.owners d.step).any (fun q => q.id == d && g.gowners.contains q) with
  | true =>
    obtain ⟨q, hq, hq2⟩ := List.any_eq_true.mp hb
    rw [Bool.and_eq_true] at hq2
    exact ⟨q, hq, eq_of_beq hq2.1, List.mem_of_elem_eq_true hq2.2⟩
  | false =>
    exfalso
    have hU : Unsupported ([d].foldl filterRequire g) x := by
      refine Unsupported.noSupport x n hn d.step h0 hk ?_
      intro q hq hqg
      exfalso
      have hqg' := List.mem_filter.mp hqg
      have hqs : q.id.step = d.step := eq_of_beq (List.mem_filter.mp hq).2
      have h2 := hqg'.2
      rw [hqs] at h2
      simp only [bne_self_eq_false, Bool.false_or] at h2
      have hany : (ownersAt n.owners d.step).any (fun q => q.id == d && g.gowners.contains q) = true :=
        List.any_eq_true.mpr ⟨q, hq, by
          rw [Bool.and_eq_true]
          exact ⟨h2, List.elem_eq_true_of_mem hqg'.1⟩⟩
      rw [hb] at hany
      exact Bool.noConfusion hany
    have hnone := unsupported_removed_rctx g hc [d] hv hU
    rw [hnone] at hx
    exact Bool.noConfusion hx

/-- **Owner entries toward step `k` are backed by chains.** -/
def OwnersSoundAt (g : GPathM) (k : Int) : Prop :=
  ∀ x n, g.node? x = some n → ∀ q ∈ ownersAt n.owners k, q ∈ g.gowners →
    ∃ sel, ChainSound g sel ∧ sel x.id.step = x ∧ sel k = q

/-- **One pin is exact** when the owner entries toward the pinned step are backed by chains: every
node that survives lies on a chain of the pinned state. -/
theorem pin_exact (g : GPathM) (hc : Reader.RCtx g) (d : NodeId) (h0 : 0 ≤ d.step)
    (hk : d.step < g.current_step) (hsound : OwnersSoundAt g d.step)
    (hv : isValid (filterAll g [d]) = true) (x : PathNodeId)
    (hx : ((filterAll g [d]).node? x).isSome = true) :
    ∃ sel, ChainSound (filterAll g [d]) sel ∧ sel x.id.step = x := by
  obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨n, hn, hid, _, _⟩ := (pruned_filterAll g [d]).nodes_derived d' (List.mem_of_find?_eq_some hd')
  have hdid : d'.id = x := node?_id_eq _ x d' hd'
  have hnx : g.node? x = some n := by
    rw [← hdid, hid]
    exact node?_of_mem hc.nodup n hn
  obtain ⟨q, hq, hqd, hqg⟩ := pin_survivor_owns g hc d hv x hx n hnx h0 hk
  obtain ⟨sel, hs, hsx, hsq⟩ := hsound x n hnx q hq hqg
  refine ⟨sel, ChainSound_filterAll g [d] sel hs ?_, hsx⟩
  intro req hreq _ _
  rw [List.mem_singleton.mp hreq, hsq, hqd]

-- ============================================================
-- The author's pick, and the reduction
-- ============================================================

/-- In a valid state of the class, the author's pick at a value step names a node of that step. -/
theorem authorChoice_spec (g : GPathM) (hc : Reader.RCtx g) (hv : isValid g = true) (w : Nat)
    (h0 : 0 ≤ 2 * (w : Int)) (hk : 2 * (w : Int) < g.current_step) :
    ∃ p, (g.node? p).isSome = true ∧ p.id = authorChoice g w ∧ p.id.step = 2 * (w : Int) := by
  have hent := hasStepEntry_of_isValid g hv _ h0 hk
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
  obtain ⟨q, hq, hqs⟩ := hent
  obtain ⟨m, hm, hmid⟩ := hc.gn q hq
  cases hf : (g.nodes.map (·.id)).find?
      (fun p => p.id.step == 2 * (w : Int) && g.gowners.contains p) with
  | none =>
    have hpred : (q.id.step == 2 * (w : Int) && g.gowners.contains q) = true := by
      rw [Bool.and_eq_true]
      exact ⟨beq_iff_eq.mpr hqs, List.elem_eq_true_of_mem hq⟩
    exact absurd hpred (List.find?_eq_none.mp hf q (List.mem_map.mpr ⟨m, hm, hmid⟩))
  | some p =>
    have hpp := List.find?_some hf
    obtain ⟨n', hn', hnid⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
    refine ⟨p, (GownersNodes.hasNode_iff g p).mp ⟨n', hn', hnid⟩, ?_, ?_⟩
    · unfold authorChoice
      rw [hf]
    · rw [Bool.and_eq_true] at hpp
      exact eq_of_beq hpp.1

/-- `OwnersSoundAt` at every step the author's reader pins. -/
def PinsSound : Nat → Nat → GPathM → Prop
  | 0, _, _ => True
  | n + 1, v, g =>
    OwnersSoundAt g (2 * (v : Int)) ∧ PinsSound n (v + 1) (filterAll g [authorChoice g v])

private theorem steps_ok (v m : Nat) (c : Int) (h : 2 * ((v + (m + 1 + 1) : Nat) : Int) ≤ c) :
    0 ≤ 2 * ((v + 1 : Nat) : Int) ∧ 2 * ((v + 1 : Nat) : Int) < c ∧
      2 * ((v + 1 + (m + 1) : Nat) : Int) ≤ c ∧ 0 ≤ 2 * (v : Int) ∧ 2 * (v : Int) < c :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

private theorem steps_one (v : Nat) (c : Int) (h : 2 * ((v + (0 + 1) : Nat) : Int) ≤ c) :
    0 ≤ 2 * (v : Int) ∧ 2 * (v : Int) < c :=
  ⟨by omega, by omega⟩

/-- **The reduction.** If the first pick lies on a chain and the owner entries toward every pinned
step are backed by chains, the author's reading is `AuthorReadable`. -/
theorem authorReadable_of_pinsSound :
    ∀ (n v : Nat) (g : GPathM), Reader.RCtx g → PinsSound n v g → ValueOnChain g v →
      2 * ((v + n : Nat) : Int) ≤ g.current_step → AuthorReadable n v g := by
  intro n
  induction n with
  | zero =>
    intro v g _ _ hvoc _
    obtain ⟨sel, hs, _⟩ := hvoc
    exact ⟨sel, hs⟩
  | succ n ih =>
    intro v g hc hps hvoc hb
    refine ⟨hvoc, ?_⟩
    obtain ⟨sel0, hs0, hc0⟩ := hvoc
    cases n with
    | zero =>
      obtain ⟨h0, hlt⟩ := steps_one v g.current_step hb
      have hstep : (sel0 (2 * (v : Int))).id.step = 2 * (v : Int) := (hs0.chain.1.1 _ h0 hlt).2
      refine ⟨sel0, ChainSound_filterAll g _ sel0 hs0 ?_⟩
      intro req hreq _ _
      rw [List.mem_singleton.mp hreq, ← hc0, hstep]
    | succ m =>
      obtain ⟨h0', hlt', hb', h0, hlt⟩ := steps_ok v m g.current_step hb
      have hstep : (sel0 (2 * (v : Int))).id.step = 2 * (v : Int) := (hs0.chain.1.1 _ h0 hlt).2
      have hdstep : (authorChoice g v).step = 2 * (v : Int) := by rw [← hc0, hstep]
      have hs0' : ChainSound (filterAll g [authorChoice g v]) sel0 := by
        refine ChainSound_filterAll g _ sel0 hs0 ?_
        intro req hreq _ _
        rw [List.mem_singleton.mp hreq, hdstep, hc0]
      have hv' := PickInduction.isValid_of_ChainG _ sel0 hs0'.chain
      have hcs := (pruned_filterAll g [authorChoice g v]).step_eq
      have hc' := Reader.RCtx_filterAll g hc [authorChoice g v]
      obtain ⟨p, hp, hpid, hpstep⟩ := authorChoice_spec _ hc' hv' (v + 1) h0'
        (by rw [hcs]; exact hlt')
      obtain ⟨sel, hs, hsp⟩ := pin_exact g hc (authorChoice g v) (by rw [hdstep]; exact h0)
        (by rw [hdstep]; exact hlt) (by rw [hdstep]; exact hps.1) hv' p hp
      have hvoc' : ValueOnChain (filterAll g [authorChoice g v]) (v + 1) := by
        refine ⟨sel, hs, ?_⟩
        rw [← hpid, ← hpstep, hsp]
      exact ih (v + 1) _ hc' hps.2 hvoc' (by rw [hcs]; exact hb')

private theorem stepCount_pos' (φ : Cnf) : (0 : Int) < stepCount φ := by
  simp only [stepCount]
  omega

private theorem cast_pred' (s : Int) (h : 0 < s) : (((s - 1).toNat : Nat) : Int) = s - 1 := by
  omega

private theorem final_cs (g : GPathM) (n : Nat) (s : Int) (hn : (n : Int) = s - 1)
    (h : g.current_step = (n : Int) + 1) : g.current_step = s := by
  omega

private theorem nVars_bound' (φ : Cnf) (c : Int) (h : c = stepCount φ) :
    2 * ((0 + φ.nVars : Nat) : Int) ≤ c := by
  subst h
  simp only [stepCount]
  omega

/-- **The author's reader on a final state**, under the reduced hypotheses: its first pick lies on a
chain, and owner entries toward each pinned step are backed by chains. -/
theorem authorRead_of_pinsSound (φ : Cnf) (hwf : WF φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ pureRun φ) (hfirst : ValueOnChain kv.2 0) (hpins : PinsSound φ.nVars 0 kv.2) :
    ∃ ids, readFrom authorChoice φ.nVars 0 kv.2 = some ids ∧ Sat (readAssign ids) φ := by
  have hkv' : kv ∈ lineAt φ (stepCount φ - 1).toNat := hkv
  have hok := (lineAt_ok φ _).2 kv hkv'
  have hreach := reachable_of_mapReachable φ hwf kv.2 hok.reach
  have hc := Reader.RCtx_reachable (reqOfCnf φ) kv.2
    (Reader.NodupIds_reachable (reqOfCnf φ) kv.2 hreach) hreach
  have hb := nVars_bound' φ kv.2.current_step
    (final_cs kv.2 _ _ (cast_pred' _ (stepCount_pos' φ)) hok.step)
  exact authorRead_final φ hwf kv hkv
    (authorReadable_of_pinsSound φ.nVars 0 kv.2 hc hpins hfirst hb)

/-- info: 'AbsSat.GraphPath.Model.ReaderPin.pin_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pin_exact

/-- info: 'AbsSat.GraphPath.Model.ReaderPin.authorReadable_of_pinsSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms authorReadable_of_pinsSound

/-- info: 'AbsSat.GraphPath.Model.ReaderPin.authorRead_of_pinsSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms authorRead_of_pinsSound

end AbsSat.GraphPath.Model.ReaderPin
