-- lean_project/AbsSat/GraphPath/Model/ReviewWorkImproves.lean
import AbsSat.GraphPath.Model.ConservationImproves
import AbsSat.GraphPath.Model.IdDiesProof
import AbsSat.GraphPath.Model.LocalContradiction

/-!
# The weak filter only does work the review would do

`ConservationImproves` says the weak filter never removes a solution. This
module says the other half of what the filter is for: **it never removes
anything the review would have kept.** At every send of the reference machine
(a reachable state `g`, a destination `d` at the next step, a valid filter),
every global owner the base review keeps also survives the weak filter
(`review_gowners_survive_weak`), so the improved review starts from a state that
still contains everything the base review ends with
(`review_gowners_sub_startW`).

In words: the weak filter's removals are a subset of the base review's removals.
It anticipates part of the review's work; it adds none.

## Why

A global owner `q` the weak filter removes sits at an earlier clause step and
disagrees with `d`'s row on some shared variable (`CnfMapImproves`). That
variable is one of `d`'s literals, so `d` pins it: `q`'s id **contradicts a pin**
(`idContradicts_of_weak_removed`, a statement about the map only). A global
owner whose id contradicts a pin is in the removal closure
(`IdDiesProof.idDies`), and the review removes the closure
(`RemovalClosure.unsupported_removed`).

## What is measured, not proved

Per send, on random formulas (1,569 sends): the improved review never takes more
passes and never removes more than the base review, and the removed owners are
already gone after the base review's first `cleanInvalid`. Those are stronger
than the theorem here — they compare the two reviews' *work*, which depends on
the order in which the review visits nodes — and they stay measurements.
-/

namespace AbsSat.GraphPath.Model.ReviewWorkImproves

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfReducer (rowPairs pairsAgree allRows varOfLit bitOf)
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf weakRows mem_weakBefore)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MapReachable
open AbsSat.GraphPath.Model.IdSeparator (IdContradicts fixes fixesMap varVal)
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeakAll mem_filterWeakAll)

variable (φ : Cnf)

-- ============================================================
-- The map side
-- ============================================================

theorem mem_weakReqOfCnf (d : NodeId) (e : Int × List NodeId) (he : e ∈ weakReqOfCnf φ d) :
    ∃ j c j' c', j < φ.clauses.length ∧ φ.clauses[j]? = some c ∧ d.step = clauseStep φ j ∧
      j' < j ∧ φ.clauses[j']? = some c' ∧
      e = (clauseStep φ j', (weakRows c d.index c').map (fun w => ⟨clauseStep φ j', w⟩)) := by
  by_cases hlo : d.step ≤ litBlock φ
  · simp [weakReqOfCnf, hlo] at he
  by_cases htop : fusionTop φ ≤ d.step
  · simp [weakReqOfCnf, hlo, htop] at he
  cases hc : clauseAt φ d.step with
  | none => simp [weakReqOfCnf, hlo, htop, hc] at he
  | some c =>
    simp only [weakReqOfCnf, if_neg hlo, if_neg htop, hc] at he
    obtain ⟨j', c', hj', hc', _, rfl⟩ := mem_weakBefore φ c d.index _ e he
    have hjc : φ.clauses[(d.step - litBlock φ - 1).toNat]? = some c := by
      simpa only [clauseAt, litBlock] using hc
    have hjlt : (d.step - litBlock φ - 1).toNat < φ.clauses.length := by
      cases Nat.lt_or_ge (d.step - litBlock φ - 1).toNat φ.clauses.length with
      | inl h => exact h
      | inr h => rw [List.getElem?_eq_none h] at hjc; simp at hjc
    exact ⟨_, c, j', c', hjlt, hjc,
      by simp only [clauseStep, litBlock] at hlo ⊢; omega, hj', hc', rfl⟩

/-- The value a literal node stands for, read the way `CnfReducer` reads a row. -/
theorem varVal_litReq (l : Lit) (hl : l.v < φ.nVars) (b : Int) (hb : b = 0 ∨ b = 1) :
    varVal φ (litReq l b) = some ((l.v : Int), bitOf (varOfLit l b)) := by
  have hlb : l.step < litBlock φ := lit_step_lt φ l hl
  have h0 : 0 ≤ l.step := by simp only [Lit.step]; split <;> omega
  have hc1 : ¬ ((litReq l b).step < 0 ∨ litBlock φ ≤ (litReq l b).step) := by
    show ¬ (l.step < 0 ∨ litBlock φ ≤ l.step); omega
  unfold varVal
  rw [if_neg hc1]
  cases hp : l.pos with
  | true =>
    have hs : l.step = 2 * (l.v : Int) := by
      show 2 * (l.v : Int) + (if l.pos then 0 else 1) = _
      rw [hp, if_pos rfl]; omega
    have hc2 : (litReq l b).step % 2 = 0 := by show l.step % 2 = 0; omega
    rw [if_pos hc2]
    show some (l.step / 2, b) = _
    have hdiv : l.step / 2 = (l.v : Int) := by omega
    rw [hdiv]
    unfold varOfLit
    rw [hp, if_pos rfl]
    rcases hb with rfl | rfl <;> rfl
  | false =>
    have hs : l.step = 2 * (l.v : Int) + 1 := by
      show 2 * (l.v : Int) + (if l.pos then 0 else 1) = _
      rw [hp, if_neg Bool.false_ne_true]
    have hc2 : ¬ ((litReq l b).step % 2 = 0) := by show ¬ (l.step % 2 = 0); omega
    rw [if_neg hc2]
    have hreq : reqOfCnf φ (litReq l b) = [{ step := varStep l.v, index := 1 - b }] :=
      reqOfCnf_neg φ (litReq l b) l.v hl (by show l.step = negStep l.v; simp only [negStep]; exact hs)
    rw [hreq]
    have hv2 : varStep l.v % 2 = 0 := by simp only [varStep]; omega
    show (if varStep l.v % 2 = 0 then some (varStep l.v / 2, 1 - b) else none) = _
    rw [if_pos hv2]
    have hdiv : varStep l.v / 2 = (l.v : Int) := by simp only [varStep]; omega
    rw [hdiv]
    unfold varOfLit
    rw [hp, if_neg Bool.false_ne_true]
    rcases hb with rfl | rfl <;> rfl

/-- Every variable/value pair a clause row names is pinned by that row's node. -/
theorem mem_pins_clause (hwf : WF φ) (d : NodeId) (j : Nat) (c : Clause)
    (hj : j < φ.clauses.length) (hc : φ.clauses[j]? = some c) (hd : d.step = clauseStep φ j) :
    ∀ x ∈ rowPairs c d.index, ∃ r ∈ reqOfCnf φ d, varVal φ r = some ((x.1 : Int), bitOf x.2) := by
  obtain ⟨⟨hv1, hv2, hv3⟩, _⟩ := hwf c (List.mem_of_getElem? hc)
  rw [reqOfCnf_clause φ d j c hj hc hd]
  intro x hx
  simp only [rowPairs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, varVal_litReq φ c.l1 hv1 _ (by simp only [b1]; omega)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
      varVal_litReq φ c.l2 hv2 _ (by simp only [b2]; omega)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      varVal_litReq φ c.l3 hv3 _ (by simp only [b3]; omega)⟩

/-- ... and fixed by the id of any path node standing on it. -/
theorem mem_fixes_clause (hwf : WF φ) (q : PathNodeId) (j : Nat) (c : Clause)
    (hj : j < φ.clauses.length) (hc : φ.clauses[j]? = some c) (hq : q.id.step = clauseStep φ j) :
    ∀ y ∈ rowPairs c q.id.index, ((y.1 : Int), bitOf y.2) ∈ fixes φ q := by
  intro y hy
  have h1 : ¬ (q.id.step < litBlock φ) := by rw [hq]; simp only [clauseStep, litBlock]; omega
  have h2 : ¬ (q.id.step = litBlock φ) := by rw [hq]; simp only [clauseStep, litBlock]; omega
  have hfm : fixesMap φ q.id = (reqOfCnf φ q.id).filterMap (varVal φ) := by
    unfold fixesMap
    rw [if_neg h1, if_neg h2]
  unfold fixes
  refine List.mem_append_left _ ?_
  rw [hfm, List.mem_filterMap]
  exact mem_pins_clause φ hwf q.id j c hj hc hq y hy

theorem exists_of_all_false {α : Type} {f : α → Bool} :
    ∀ {l : List α}, l.all f = false → ∃ x ∈ l, f x = false
  | [], h => by cases h
  | a :: as, h => by
    cases ha : f a with
    | false => exact ⟨a, List.mem_cons_self, ha⟩
    | true =>
      rw [List.all_cons, ha, Bool.true_and] at h
      obtain ⟨x, hx, hfx⟩ := exists_of_all_false h
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

theorem exists_disagree {p q : List (Nat × Bool)} (h : pairsAgree p q = false) :
    ∃ x ∈ p, ∃ y ∈ q, x.1 = y.1 ∧ x.2 ≠ y.2 := by
  have h' : p.all (fun x : Nat × Bool => q.all (fun y : Nat × Bool => x.1 != y.1 || x.2 == y.2))
      = false := h
  obtain ⟨x, hx, hnx⟩ := exists_of_all_false h'
  have hnx' : q.all (fun y : Nat × Bool => x.1 != y.1 || x.2 == y.2) = false := hnx
  obtain ⟨y, hy, hny⟩ := exists_of_all_false hnx'
  have hor : (x.1 != y.1 || x.2 == y.2) = false := hny
  cases h3 : (x.1 == y.1) with
  | false =>
    have : (x.1 != y.1) = true := by unfold bne; rw [h3]; rfl
    rw [this, Bool.true_or] at hor
    cases hor
  | true =>
    cases h2 : (x.2 == y.2) with
    | true =>
      rw [h2, Bool.or_true] at hor
      cases hor
    | false =>
      refine ⟨x, hx, y, hy, eq_of_beq h3, fun heq => ?_⟩
      rw [heq, beq_self_eq_true] at h2
      cases h2

theorem bitOf_inj {a b : Bool} (h : bitOf a = bitOf b) : a = b := by
  cases a <;> cases b <;> simp [bitOf] at h ⊢

/-- **What the weak filter removes contradicts a pin.** A map node at the step of
a weak entry of `d` that is not among the entry's nodes fixes some variable
against the value `d` pins. Pure map arithmetic. -/
theorem idContradicts_of_weak_removed (hwf : WF φ) (d : NodeId) (q : PathNodeId)
    (e : Int × List NodeId) (he : e ∈ weakReqOfCnf φ d)
    (hs : q.id.step = e.1) (hmap : q.id ∈ mapNodes φ q.id.step) (hn : q.id ∉ e.2) :
    IdContradicts φ (reqOfCnf φ d) q := by
  obtain ⟨j, c, j', c', hj, hc, hd, hj', hc', rfl⟩ := mem_weakReqOfCnf φ d e he
  have hj'lt : j' < φ.clauses.length := by omega
  have hqs : q.id.step = clauseStep φ j' := hs
  have hrange := index_range_of_clauseNode φ j' hj'lt q.id (by rw [← hqs]; exact hmap)
  have hrow : q.id.index ∈ allRows := by
    have : q.id.index = 1 ∨ q.id.index = 2 ∨ q.id.index = 3 ∨ q.id.index = 4 ∨
        q.id.index = 5 ∨ q.id.index = 6 ∨ q.id.index = 7 := by omega
    rcases this with h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hnot : pairsAgree (rowPairs c d.index) (rowPairs c' q.id.index) = false := by
    cases hpa : pairsAgree (rowPairs c d.index) (rowPairs c' q.id.index) with
    | false => rfl
    | true =>
      exfalso
      apply hn
      refine List.mem_map.mpr ⟨q.id.index, List.mem_filter.mpr ⟨hrow, hpa⟩, ?_⟩
      show ({ step := clauseStep φ j', index := q.id.index } : NodeId) = q.id
      rw [← hqs]
  obtain ⟨x, hx, y, hy, hxy1, hxy2⟩ := exists_disagree hnot
  obtain ⟨r, hr, hvr⟩ := mem_pins_clause φ hwf d j c hj hc hd x hx
  refine ⟨((y.1 : Int), bitOf y.2), mem_fixes_clause φ hwf q j' c' hj'lt hc' hqs y hy,
    r, hr, _, hvr, ?_, ?_⟩
  · show (x.1 : Int) = (y.1 : Int)
    rw [hxy1]
  · show bitOf x.2 ≠ bitOf y.2
    exact fun heq => hxy2 (bitOf_inj heq)

-- ============================================================
-- The machine side
-- ============================================================

theorem mem_foldl_filterRequire_of (reqs : List NodeId) : ∀ (g : GPathM) (q : PathNodeId),
    q ∈ g.gowners → (∀ req ∈ reqs, q.id.step ≠ req.step ∨ q.id = req) →
    q ∈ (reqs.foldl filterRequire g).gowners := by
  induction reqs with
  | nil => intro g q hq _; exact hq
  | cons r rs ih =>
    intro g q hq hall
    simp only [List.foldl_cons]
    refine ih (filterRequire g r) q ?_ (fun req hreq => hall req (List.mem_cons_of_mem _ hreq))
    simp only [filterRequire, List.mem_filter, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    exact ⟨hq, hall r List.mem_cons_self⟩

/-- **The weak filter removes nothing the review keeps.** At a send of the
reference machine, every global owner that survives the base filter and review
also survives the weak filter. -/
theorem review_gowners_survive_weak (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g)
    (d : NodeId) (hd : d.step = g.current_step)
    (hv : isValid (filterAll g (reqOfCnf φ d)) = true) :
    ∀ q ∈ (filterAll g (reqOfCnf φ d)).gowners,
      q ∈ (filterWeakAll g (weakReqOfCnf φ d)).gowners := by
  have hr := reachable_of_mapReachable φ hwf g hmr
  intro q hq
  have hq0 : q ∈ ((reqOfCnf φ d).foldl filterRequire g).gowners :=
    (pruned_review _).gowners_sub q hq
  have hqg : q ∈ g.gowners := (LocalContradiction.mem_foldl_filterRequire _ g q hq0).1
  have hmap : q.id ∈ mapNodes φ q.id.step := by
    obtain ⟨n, hn, hid⟩ := GownersNodes.GN_reachable (reqOfCnf φ) g hr q hqg
    have := nodesOnMap_of_mapReachable φ g hmr n hn
    rw [hid] at this
    exact this
  refine (mem_filterWeakAll _ g q).mpr ⟨hqg, fun e he hs => ?_⟩
  exact Decidable.byContradiction fun hn => by
    have hc := idContradicts_of_weak_removed φ hwf d q e he hs hmap hn
    have hu := IdDiesProof.idDies φ hwf g hr d hd q hc hq0
    have hnone := RemovalClosure.unsupported_removed (reqOfCnf φ) g hr (reqOfCnf φ d) hv hu
    obtain ⟨n, hn', hid⟩ :=
      GownersNodes.GN_filterAll g _ (GownersNodes.GN_reachable (reqOfCnf φ) g hr) q hq
    have hfind := List.find?_eq_none.mp hnone n hn'
    exact hfind (by simp [hid])

/-- **The improved review starts above the base review's end.** The pinned,
weakly filtered state still holds every global owner the base review keeps: the
weak filter's removals are a subset of the base review's removals. -/
theorem review_gowners_sub_startW (hwf : WF φ) (g : GPathM) (hmr : MapReachable φ g)
    (d : NodeId) (hd : d.step = g.current_step)
    (hv : isValid (filterAll g (reqOfCnf φ d)) = true) :
    ∀ q ∈ (filterAll g (reqOfCnf φ d)).gowners,
      q ∈ ((reqOfCnf φ d).foldl filterRequire (filterWeakAll g (weakReqOfCnf φ d))).gowners := by
  intro q hq
  have hq0 : q ∈ ((reqOfCnf φ d).foldl filterRequire g).gowners :=
    (pruned_review _).gowners_sub q hq
  exact mem_foldl_filterRequire_of _ _ q (review_gowners_survive_weak φ hwf g hmr d hd hv q hq)
    (LocalContradiction.mem_foldl_filterRequire _ g q hq0).2

-- ============================================================
-- Axiom guards
-- ============================================================

/-- info: 'AbsSat.GraphPath.Model.ReviewWorkImproves.idContradicts_of_weak_removed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms idContradicts_of_weak_removed

/-- info: 'AbsSat.GraphPath.Model.ReviewWorkImproves.review_gowners_survive_weak' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_gowners_survive_weak

/-- info: 'AbsSat.GraphPath.Model.ReviewWorkImproves.review_gowners_sub_startW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms review_gowners_sub_startW

end AbsSat.GraphPath.Model.ReviewWorkImproves
