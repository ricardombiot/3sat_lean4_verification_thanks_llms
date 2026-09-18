-- lean_project/AbsSat/GraphPath/Model/TripleA.lean
import AbsSat.GraphPath.Model.PinUp

/-!
# Attacking `LivePinUp`: the nodes that own the live value

`LivePinUp` (v145) asks that pinning a live value `a` of the next variable keep the state valid. A support
relation that carries the pin gives it at once (it survives the pin and the review). The natural one is
**the nodes that own `a`**, with the tables restricted to them:

  `Sa p := Rel S p a`,  `Ra x y := Rel S x y ∧ Rel S x a ∧ Rel S y a`.

Most of the support conditions come free from the reviewed state itself; **coverage** too (the review's
common-owner rule for the pair `(x, a)`). What is left is the same rule for **triples containing `a`**:

* **`TripleA S a`** — two nodes that own `a` and each other have, at every step, a common owned node
  that owns `a` too; and likewise through a parent and through a son.
* **`sup_of_triple`**, **`pin_valid_of_triple`** (no hypothesis beyond `TripleA`) — then `(Sa, Ra)` is a
  support carrying the pin, and pinning `a` keeps the state valid.
* **`livePinUp_of_triple`** — `LivePinUp` from `TripleA` at the live values the reader meets; so the
  verdict and the answers hold under it (`verdict_iff_triple`, `answer_unsat_triple`,
  `answer_ne_unknown_triple`).

The general three-node rule (Helly-3) fails on exact states (v139); this one is restricted to triples
through the live value on top of a decided prefix.

**Measured (probe `triplea`, v146): the triple rule through `a` fails too** — K4: 12 of 27 live values,
parity: 10 of 45, prism: 18 of 39, already at the first variable (empty prefix). So `Sa` is **not** a
support by itself: the review has to remove more before the pinned state settles. The reduction below is
correct but its hypothesis is false; it is kept as the record of this route.
-/

namespace AbsSat.GraphPath.Model.TripleA

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup AOk AOk_filterAllAgg)
open AbsSat.GraphPath.Model.SupportSplit (valid_of_sup rel_self)
open AbsSat.GraphPath.Model.LinkedChain (sup_self)
open AbsSat.GraphPath.Model.PinExtends
open AbsSat.GraphPath.Model.PinUp

/-- **The rule for triples through `a`.** -/
structure TripleA (S : GPathM) (a : PathNodeId) : Prop where
  agg : ∀ x y, Rel S x y → Rel S x a → Rel S y a → ∀ l, 0 ≤ l → l < S.current_step →
    ∃ z, Rel S x z ∧ Rel S y z ∧ Rel S z a ∧ z.id.step = l
  par : ∀ x d, Rel S x a → S.node? x = some d → x.parent_id ≠ none → ∀ y, Rel S x y → Rel S y a →
    ∃ c ∈ d.parents, Rel S x c ∧ Rel S c x ∧ Rel S c y ∧ Rel S c a
  son : ∀ x, Rel S x a → x.id.step ≠ S.current_step - 1 → ∀ y, Rel S x y → Rel S y a →
    ∃ c m, S.node? c = some m ∧ x ∈ m.parents ∧ Rel S x c ∧ Rel S c x ∧ Rel S c y ∧ Rel S c a

theorem mem_of_rel {S : GPathM} {x y : PathNodeId} (h : Rel S x y) : Mem S x := by
  obtain ⟨m, hm, _, _⟩ := h
  exact ⟨m, hm⟩

/-- **The nodes that own `a` are a support**, under the triple rule. -/
theorem sup_of_triple (S : GPathM) (ad : AdjacentOwners.Adj S) (hok : AggFixpoint.AggOk S)
    (hsmp : Sons.SMP S) (a : PathNodeId) (T : TripleA S a) :
    Sup S (fun p => Rel S p a) (fun x y => Rel S x y ∧ Rel S x a ∧ Rel S y a) := by
  have sup := sup_self S ad hok hsmp
  refine ⟨fun p hp => sup.gow p (mem_of_rel hp), fun p hp => sup.node p (mem_of_rel hp),
    fun p hp => sup.step p (mem_of_rel hp), fun x v h => ⟨h.2.1, h.2.2⟩,
    fun x v n h hn => sup.own x v n h.1 hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- coverage: the review's common owner for the pair `(x, a)`
    intro x hxa l h0 h1
    obtain ⟨z, hxz, haz, hzs⟩ := sup.agg x a hxa l h0 h1
    exact ⟨z, ⟨hxz, hxa, sup.sym a z haz⟩, hzs⟩
  · intro x d hxa hd hne v hv
    obtain ⟨c, hc, hxc, hcx, hcv, hca⟩ := T.par x d hxa hd hne v hv.1 hv.2.2
    exact ⟨c, hc, ⟨hxc, hxa, hca⟩, ⟨hcx, hca, hxa⟩, ⟨hcv, hca, hv.2.2⟩⟩
  · intro x hxa hs v hv
    obtain ⟨c, m, hm, hxm, hxc, hcx, hcv, hca⟩ := T.son x hxa hs v hv.1 hv.2.2
    exact ⟨c, m, hm, hxm, ⟨hxc, hxa, hca⟩, ⟨hcx, hca, hxa⟩, ⟨hcv, hca, hv.2.2⟩⟩
  · intro x v hv l h0 h1
    obtain ⟨z, hxz, hvz, hza, hzs⟩ := T.agg x v hv.1 hv.2.1 hv.2.2 l h0 h1
    exact ⟨z, ⟨hxz, hv.2.1, hza⟩, ⟨hvz, hv.2.2, hza⟩, hzs⟩
  · intro x v hv
    exact ⟨sup.sym x v hv.1, hv.2.2, hv.2.1⟩
  · intro x c d hxc hcx hs hd
    exact sup.link x c d hxc.1 hcx.1 hs hd

/-- **Pinning `a` keeps the state valid**, under the triple rule through `a`. -/
theorem pin_valid_of_triple (S : GPathM) (hrf : RF S) (hv : isValid S = true) (a : PathNodeId)
    (ha : Mem S a) (T : TripleA S a) : isValid (filterAllAgg S [a.id]) = true := by
  have ad := adj_rf hrf hv
  have hok := aggOk_rf hrf hv
  have hsup := sup_of_triple S ad hok hrf.smp a T
  have aok : AOk S (fun p => Rel S p a) (fun x y => Rel S x y ∧ Rel S x a ∧ Rel S y a) :=
    ⟨hsup, hrf.smp, (RCtx_of_readableAgg S hrf.readable).shape.notroot⟩
  have hF := (AOk_filterAllAgg S aok [a.id] (fun r hr p hp hps => by
    rw [List.mem_singleton.mp hr] at hps ⊢
    obtain ⟨m, hm, hin, _⟩ := hp
    have hid := node?_id_eq S p m hm
    have := ad.rc.oos m (List.mem_of_find?_eq_some hm) a hin (by rw [hid, hps])
    rw [this, hid])).sup
  exact valid_of_sup _ _ _ hF a (rel_self S ad ha)

-- ============================================================
-- The verdict under the triple rule
-- ============================================================

variable (φ : Cnf)

/-- The triple rule at every live value the reader meets bottom-up. -/
def TripleUp (g₀ : GPathM) : Prop :=
  ∀ S, ReadFrom g₀ S → isValid S = true → ∀ v : Nat, v < φ.nVars →
    (∀ k, 0 ≤ k → k < 2 * (v : Int) → Decided S k) →
    ∀ a, Mem S a → a.id.step = 2 * (v : Int) → TripleA S a

theorem livePinUp_of_triple {g₀ : GPathM} (hB : Base φ g₀) (h : TripleUp φ g₀) : LivePinUp φ g₀ :=
  fun S hS hv v hvn hpre a ha has =>
    pin_valid_of_triple S (facts_of_readFrom φ hB hS).1 hv a ha (h S hS hv v hvn hpre a ha has)

def RunTripleUp : Prop := ∀ kv ∈ pureRunW φ, TripleUp φ (filterAllAgg kv.2 [])

theorem runLivePinUp_of_triple (hwf : WF φ) (h : RunTripleUp φ) : RunLivePinUp φ :=
  fun kv hkv => livePinUp_of_triple φ (base_final φ hwf kv hkv) (h kv hkv)

theorem verdict_iff_triple (hwf : WF φ) (h : RunTripleUp φ) :
    (∃ kv ∈ pureRunW φ, isValid (filterAllAgg kv.2 []) = true) ↔ Satisfiable φ :=
  verdict_iff_up φ hwf (runLivePinUp_of_triple φ hwf h)

theorem answer_unsat_triple (hwf : WF φ) (h : RunTripleUp φ) (hns : ¬ Satisfiable φ) :
    Answer.answer φ = .unsat :=
  answer_unsat_up φ hwf (runLivePinUp_of_triple φ hwf h) hns

theorem answer_ne_unknown_triple (hwf : WF φ) (h : RunTripleUp φ) : Answer.answer φ ≠ .unknown :=
  answer_ne_unknown_up φ hwf (runLivePinUp_of_triple φ hwf h)

/-- info: 'AbsSat.GraphPath.Model.TripleA.pin_valid_of_triple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pin_valid_of_triple

/-- info: 'AbsSat.GraphPath.Model.TripleA.answer_ne_unknown_triple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answer_ne_unknown_triple

end AbsSat.GraphPath.Model.TripleA
