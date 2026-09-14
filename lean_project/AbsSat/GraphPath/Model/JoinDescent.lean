-- lean_project/AbsSat/GraphPath/Model/JoinDescent.lean
import AbsSat.GraphPath.Model.DescentInvariant
import AbsSat.GraphPath.Model.JoinSound

/-!
# No dead ends through a join

The second case of the induction for `DescentInvariant.DescendAll`. What is proved here:

* `soundOn_of_grown` — a partial chain of a state is a partial chain of any state that grows it
  (`Grown`), so a partial chain of either side is one of the join.
* `descendAll_join` — **the reduction**: if every partial chain of `join g₁ g₂` is a partial
  chain of one side or extends, then the join keeps `DescendAll`. A chain of one side extends on
  that side, and the extension lifts.
* `no_chain_across_sides` — a partial chain of the join never contains both a node only `g₁`
  has and a node only `g₂` has, as long as `g₁`'s owners are nodes of `g₁`.
* `descendOn` — with `DescendAll`, every partial chain on `lo .. hi` descends to step 0 keeping
  its picks.

What is not proved is `JoinCovered` for the joins the driver performs. Its content is the
**mixed** chains: partial chains of the join that are chains of neither side, because their
ownership facts come from different incoming states. On `SatMachinePure` (seed 1001) they are
36 of 267,630 partial chains of joins, and every one above step 0 extends.
-/

namespace AbsSat.GraphPath.Model.JoinDescent

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.NoDeadEnd
open AbsSat.GraphPath.Model.DescentInvariant

/-- **Growth keeps partial chains.** -/
theorem soundOn_of_grown {g g' : GPathM} (hgr : Grown g g') {sel : Int → PathNodeId}
    {lo hi : Int} (h : SoundOn g sel lo hi) : SoundOn g' sel lo hi := by
  have hlook : ∀ k, lo ≤ k → k ≤ hi → ∃ n n', g.node? (sel k) = some n ∧
      g'.node? (sel k) = some n' ∧ (∀ q ∈ n.owners, q ∈ n'.owners) ∧
      (∀ p ∈ n.parents, p ∈ n'.parents) ∧ (∀ s ∈ n.sons, s ∈ n'.sons) := by
    intro k h1 h2
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.node k h1 h2).1
    obtain ⟨n', hn', ho, hp, hs⟩ := hgr.node?_grown _ n hn
    exact ⟨n, n', hn, hn', ho, hp, hs⟩
  refine ⟨fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun i j hi1 hj1 hi2 hj2 hij => ?_,
    fun k h1 h2 => hgr.gowners_grown _ (h.gowner k h1 h2), fun k h1 h2 => ?_,
    fun k h1 h2 => ?_, fun k h1 h2 => h.root_shape k h1 h2⟩
  · obtain ⟨_, _, _, hn', _⟩ := hlook k h1 h2
    exact ⟨by rw [hn']; rfl, (h.node k h1 h2).2⟩
  · obtain ⟨n, n', hn, hn', _, hp, _⟩ := hlook (k + 1) (by omega) h2
    have hpl := h.parent_link k h1 h2
    rw [hn] at hpl
    rw [hn']
    exact hp _ hpl
  · obtain ⟨n, n', hn, hn', ho, _, _⟩ := hlook j hj1 hj2
    have hoj := h.owned i j hi1 hj1 hi2 hj2 hij
    simp only [ownersOf, hn, ownersAt, List.mem_filter] at hoj
    simp only [ownersOf, hn', ownersAt, List.mem_filter]
    exact ⟨ho _ hoj.1, hoj.2⟩
  · obtain ⟨n, n', hn, hn', ho, _, _⟩ := hlook k h1 h2
    have hso := h.self_owned k h1 h2
    simp only [ownersOf, hn] at hso
    simp only [ownersOf, hn']
    exact ho _ hso
  · obtain ⟨n, n', hn, hn', _, _, hs⟩ := hlook k h1 (by omega)
    have hsl := h.son_link k h1 h2
    simp only [sonsOf, hn] at hsl
    simp only [sonsOf, hn']
    exact hs _ hsl

-- ============================================================
-- The reduction
-- ============================================================

/-- Every partial chain of the join is a partial chain of one side, or it extends. -/
def JoinCovered (g₁ g₂ : GPathM) : Prop :=
  ∀ sel lo hi, 0 < lo → lo ≤ hi → hi < (join g₁ g₂).current_step →
    SoundOn (join g₁ g₂) sel lo hi →
    SoundOn g₁ sel lo hi ∨ SoundOn g₂ sel lo hi ∨
      ∃ c, SoundOn (join g₁ g₂) (upd sel (lo - 1) c) (lo - 1) hi

/-- **`join` keeps `DescendAll`, given `JoinCovered`.** -/
theorem descendAll_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true)
    (h₁ : DescendAll g₁) (h₂ : DescendAll g₂) (hcov : JoinCovered g₁ g₂) :
    DescendAll (join g₁ g₂) := by
  intro sel lo hi hlo hlohi hhi hs
  rcases hcov sel lo hi hlo hlohi hhi hs with hs1 | hs2 | hext
  · have hstep := (grown_join_left g₁ g₂).step_eq
    obtain ⟨c, hc⟩ := h₁ sel lo hi hlo hlohi (by rw [← hstep]; exact hhi) hs1
    exact ⟨c, soundOn_of_grown (grown_join_left g₁ g₂) hc⟩
  · have hstep := (grown_join_right g₁ g₂ hok).step_eq
    obtain ⟨c, hc⟩ := h₂ sel lo hi hlo hlohi (by rw [← hstep]; exact hhi) hs2
    exact ⟨c, soundOn_of_grown (grown_join_right g₁ g₂ hok) hc⟩
  · exact hext

-- ============================================================
-- What a mixed chain can look like
-- ============================================================

/-- A node only `g₁` has keeps its `g₁` record in the join. -/
theorem join_node?_only_left (g₁ g₂ : GPathM) (p : PathNodeId) (n : PNodeM)
    (hn : g₁.node? p = some n) (h2 : g₂.node? p = none) : (join g₁ g₂).node? p = some n := by
  have h := join_node?_left g₁ g₂ p n hn
  have hid : n.id = p := node?_id_eq g₁ p n hn
  rw [h]
  show some (match g₂.node? n.id with | some m => mergeNode n m | none => n) = some n
  rw [hid, h2]

/-- Every owner in range of a node is a node of the same state. -/
def OwnersAreNodes (g : GPathM) : Prop :=
  ∀ p n, g.node? p = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step → q.id.step < g.current_step →
    (g.node? q).isSome = true

/-- **A chain of the join does not cross sides.** It never contains a node only `g₁` has
together with a node only `g₂` has. -/
theorem no_chain_across_sides (g₁ g₂ : GPathM) (hon : OwnersAreNodes g₁)
    {sel : Int → PathNodeId} {lo hi : Int} (hs : SoundOn (join g₁ g₂) sel lo hi)
    (hlo : 0 ≤ lo) (hhi : hi < g₁.current_step) {i j : Int}
    (hi1 : lo ≤ i) (hi2 : i ≤ hi) (hj1 : lo ≤ j) (hj2 : j ≤ hi)
    (honly1 : g₂.node? (sel j) = none) (honly2 : g₁.node? (sel i) = none) : False := by
  obtain ⟨hsomej, _⟩ := hs.node j hj1 hj2
  obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp hsomej
  rcases join_node?_source g₁ g₂ (sel j) nj hnj with h1 | h2
  · obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h1
    rcases int_eq_or_ne i j with hij | hij
    · subst hij
      rw [hn] at honly2
      cases honly2
    · have ho := hs.owned i j hi1 hj1 hi2 hj2 hij
      have hstep := (hs.node i hi1 hi2).2
      simp only [ownersOf, join_node?_only_left g₁ g₂ (sel j) n hn honly1, ownersAt,
        List.mem_filter] at ho
      have hnode := hon (sel j) n hn (sel i) ho.1 (by rw [hstep]; omega) (by rw [hstep]; omega)
      rw [honly2] at hnode
      exact Bool.noConfusion hnode
  · rw [honly1] at h2
    exact Bool.noConfusion h2

-- ============================================================
-- Descending a segment
-- ============================================================

/-- **With `DescendAll`, every partial chain descends to step 0**, keeping its picks. -/
theorem descendOn (g : GPathM) (h : DescendAll g) (m : Nat) :
    ∀ (sel : Int → PathNodeId) (lo hi : Int), lo.toNat ≤ m → 0 ≤ lo → lo ≤ hi →
      hi < g.current_step → SoundOn g sel lo hi →
      ∃ sel', (∀ k, lo ≤ k → sel' k = sel k) ∧ SoundOn g sel' 0 hi := by
  induction m with
  | zero =>
    intro sel lo hi hm hlo _ _ hs
    have hEq : lo = 0 := by omega
    subst hEq
    exact ⟨sel, fun _ _ => rfl, hs⟩
  | succ m ih =>
    intro sel lo hi hm hlo hlohi hhi hs
    if hpos : 0 < lo then
      obtain ⟨c, hc⟩ := h sel lo hi hpos hlohi hhi hs
      obtain ⟨sel', hagree, hs'⟩ :=
        ih (upd sel (lo - 1) c) (lo - 1) hi (by omega) (by omega) (by omega) hhi hc
      refine ⟨sel', fun k hk => ?_, hs'⟩
      rw [hagree k (by omega)]
      unfold upd
      rw [if_neg (by omega)]
    else
      have hEq : lo = 0 := by omega
      subst hEq
      exact ⟨sel, fun _ _ => rfl, hs⟩

/-- info: 'AbsSat.GraphPath.Model.JoinDescent.soundOn_of_grown' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms soundOn_of_grown

/-- info: 'AbsSat.GraphPath.Model.JoinDescent.descendAll_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms descendAll_join

/-- info: 'AbsSat.GraphPath.Model.JoinDescent.no_chain_across_sides' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms no_chain_across_sides

/-- info: 'AbsSat.GraphPath.Model.JoinDescent.descendOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms descendOn

end AbsSat.GraphPath.Model.JoinDescent
