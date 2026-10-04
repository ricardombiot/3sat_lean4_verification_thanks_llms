import AbsSat.GraphPath.Model.SacClosure
import AbsSat.GraphPath.Model.Pruned

/-!
# The conditioned filter: one pass of arc consistency on the global owners

`SacClosure` proves the conditioned rule sound and shows it subsumes the review's removal closure,
which also shows the review cannot be made to derive it: `Unsupported` quantifies over all of a
node's owners, `DeadFor` only over those compatible with the node it is conditioned on. So the extra
strength has to be *added to the machine*, the way `CnfMapImproves` added the weak requirements.

This is that operation, in the shape the driver already uses — it rewrites `gowners` and nothing
else:

* `filterAC` — keep a global owner only when every step still has a global owner compatible with it;
* `pruned_filterAC` — so the state is a `Pruned` narrowing, and every shape fact survives;
* `ChainSound_filterAC` — **every sound chain survives it**, with no side condition: two members of a
  chain are compatible (`compat_of_chainSound`), so each member supports the others at every step.
  `ChainSound_filterWeak` needs the chain to lie inside the weak sets; this one needs nothing;
* `sacDead_of_removed` — what it drops is `SacDead`, hence on no chain (`not_chainS_of_sacDead`);
* `filterACn` — the pass iterated, with the same two properties.

The measurement this comes from: on `altchain_m1..m7` the first pass already removes about 97% of
the nodes with no chain, and `⌈k/2⌉ + 1` passes remove all of them.
-/

namespace AbsSat.GraphPath.Model.SacFilter

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.ChainFabric
open AbsSat.GraphPath.Model.SacClosure

-- ============================================================
-- Compatibility, as a test
-- ============================================================

/-- `Compat` as a `Bool`: the two nodes own each other. -/
def compatB (g : GPathM) (x y : PathNodeId) : Bool :=
  (ownersOf g y).contains x && (ownersOf g x).contains y

theorem compatB_of_compat {g : GPathM} {x y : PathNodeId} (h : Compat g x y) :
    compatB g x y = true := by
  simp only [compatB, Bool.and_eq_true, List.contains_iff_mem]
  exact ⟨h.1, h.2⟩

theorem compat_of_compatB {g : GPathM} {x y : PathNodeId} (h : compatB g x y = true) :
    Compat g x y := by
  simp only [compatB, Bool.and_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1, h.2⟩

-- ============================================================
-- The filter
-- ============================================================

/-- Every step below the current one still has a global owner compatible with `q`. -/
def acOk (g : GPathM) (q : PathNodeId) : Bool :=
  (intRange 0 (g.current_step - 1)).all
    (fun j => g.gowners.any (fun z => z.id.step == j && compatB g q z))

/-- **One pass of arc consistency on the global owners.** Like `filterWeak`, it rewrites `gowners`
and nothing else; unlike it, the test is conditioned on the owner being kept. -/
def filterAC (g : GPathM) : GPathM :=
  { g with gowners := g.gowners.filter (acOk g) }

theorem pruned_filterAC (g : GPathM) : Pruned g (filterAC g) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := (List.mem_filter.mp hq).1
  nodes_derived n hn := ⟨n, hn, rfl, fun _ hq => hq, fun _ hp => hp⟩

-- ============================================================
-- It loses no chain
-- ============================================================

/-- **Every sound chain survives the pass.** At any step the chain's own node is a global owner
compatible with every other member, so no member can fail the test. -/
theorem ChainSound_filterAC (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel) :
    ChainSound (filterAC g) sel := by
  refine ⟨⟨h.chain.1, h.chain.2.1, ?_⟩, h.self_owned, h.son_link, h.root_shape⟩
  intro k hlo hhi
  refine List.mem_filter.mpr ⟨h.chain.2.2 k hlo hhi, ?_⟩
  refine List.all_eq_true.mpr (fun j hj => ?_)
  obtain ⟨hj0, hj1⟩ := PickInduction.intRange_bounds hj
  have hjlt : j < g.current_step := by omega
  exact List.any_eq_true.mpr ⟨sel j, h.chain.2.2 j hj0 hjlt,
    Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr ((h.chain.1.1 j hj0 hjlt).2),
      compatB_of_compat (compat_of_chainSound h hlo hhi hj0 hjlt)⟩⟩

-- ============================================================
-- What it drops had no chain
-- ============================================================

/-- Witness of a failing `all`, by induction on the list: core's `List.all_eq_false` carries
`Classical.choice`, and the closures here stay at `[propext, Quot.sound]`. -/
theorem exists_of_all_eq_false {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.all p = false → ∃ x ∈ l, p x = false
  | [], h => Bool.noConfusion h
  | a :: as, h => by
    cases hp : p a with
    | false => exact ⟨a, List.mem_cons_self, hp⟩
    | true =>
      rw [List.all_cons, hp] at h
      obtain ⟨x, hx, hpx⟩ := exists_of_all_eq_false h
      exact ⟨x, List.mem_cons_of_mem _ hx, hpx⟩

/-- A node with no compatible global owner at some step is killed by its own conditioned closure. -/
theorem sacDead_of_empty_step {g : GPathM} {q : PathNodeId} {j : Int} (h0 : 0 ≤ j)
    (hj : j < g.current_step) (h : ∀ z ∈ g.gowners, z.id.step = j → ¬ Compat g q z) :
    SacDead g q :=
  DeadFor.noSupport q j h0 hj (fun z hz hstep hqz _ => absurd hqz (h z hz hstep))

/-- **The pass drops only `SacDead` nodes**, which by `not_chainS_of_sacDead` lie on no chain. -/
theorem sacDead_of_removed {g : GPathM} {q : PathNodeId} (hq : q ∈ g.gowners)
    (hout : q ∉ (filterAC g).gowners) : SacDead g q := by
  have hfalse : acOk g q = false := by
    cases hb : acOk g q with
    | false => rfl
    | true => exact absurd (List.mem_filter.mpr ⟨hq, hb⟩) hout
  obtain ⟨j, hjmem, hjf⟩ := exists_of_all_eq_false hfalse
  obtain ⟨hj0, hj1⟩ := PickInduction.intRange_bounds hjmem
  refine sacDead_of_empty_step hj0 (by omega) (fun z hz hstep hc => ?_)
  have hany : (g.gowners.any (fun z => z.id.step == j && compatB g q z)) = true :=
    List.any_eq_true.mpr ⟨z, hz, Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr hstep, compatB_of_compat hc⟩⟩
  rw [hany] at hjf
  exact Bool.noConfusion hjf

/-- What the pass drops carries no chain of the state it was dropped from. -/
theorem not_chainS_of_removed {g : GPathM} {q : PathNodeId} (hq : q ∈ g.gowners)
    (hout : q ∉ (filterAC g).gowners) : ¬ ChainS g q :=
  not_chainS_of_sacDead g q (sacDead_of_removed hq hout)

-- ============================================================
-- The pass, iterated
-- ============================================================

/-- The pass run `n` times. The measurement needs `⌈k/2⌉ + 1` of them on the chain family. -/
def filterACn : Nat → GPathM → GPathM
  | 0, g => g
  | n + 1, g => filterACn n (filterAC g)

theorem pruned_refl (g : GPathM) : Pruned g g where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := hq
  nodes_derived n hn := ⟨n, hn, rfl, fun _ hq => hq, fun _ hp => hp⟩

theorem pruned_filterACn : ∀ (n : Nat) (g : GPathM), Pruned g (filterACn n g)
  | 0, g => pruned_refl g
  | n + 1, g => Pruned.trans (pruned_filterAC g) (pruned_filterACn n (filterAC g))

/-- **Iterating loses no chain either.** -/
theorem ChainSound_filterACn : ∀ (n : Nat) (g : GPathM) (sel : Int → PathNodeId),
    ChainSound g sel → ChainSound (filterACn n g) sel
  | 0, _, _, h => h
  | n + 1, g, sel, h => ChainSound_filterACn n (filterAC g) sel (ChainSound_filterAC g sel h)

/-- **The filter keeps every solution**: a state with a sound chain still has one after any number
of passes. This is what a driver built on it needs for the conservation law. -/
theorem inhabited_filterACn (n : Nat) (g : GPathM) (h : ∃ sel, ChainSound g sel) :
    ∃ sel, ChainSound (filterACn n g) sel :=
  match h with
  | ⟨sel, hs⟩ => ⟨sel, ChainSound_filterACn n g sel hs⟩

/-- info: 'AbsSat.GraphPath.Model.SacFilter.ChainSound_filterAC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ChainSound_filterAC

/-- info: 'AbsSat.GraphPath.Model.SacFilter.sacDead_of_removed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sacDead_of_removed

/-- info: 'AbsSat.GraphPath.Model.SacFilter.not_chainS_of_removed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_chainS_of_removed

/-- info: 'AbsSat.GraphPath.Model.SacFilter.inhabited_filterACn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inhabited_filterACn

end AbsSat.GraphPath.Model.SacFilter
