-- lean_project/AbsSat/GraphPath/Model/Descent.lean
import AbsSat.GraphPath.Model.NoDeadEnd
import AbsSat.GraphPath.Model.AdjacentOwners
import AbsSat.GraphPath.Model.AggFixpoint
import AbsSat.GraphPath.Model.ParentWitness

/-!
# The descent, step by step

`NoDeadEndVerdict.sat_of_noDeadEnd` leaves the whole verdict resting on one step: a partial chain
from the top step down extends by one pick. This file attacks that step head on.

* `extend_of_common_owner` — **the extension is exactly a common owner.** If the picks already
  made have an owner in common on the step below, that owner *is* a parent of the lowest pick
  (`AdjacentOwners.owners_below_iff_parents`) and every other condition of `SoundFrom` follows from
  the invariants: symmetry of the tables gives ownership both ways, `ownGow` gives the global
  owner, `self` gives self-ownership, the adjacent owners give the son link, and `NotRoot` with
  `RootAtZero` give the root shape.
* `extend_anchor` — so the **first** descent step is free: any parent of the anchor extends it.
* `extend_pair` — and the **second** is free too: the pair consistency of the sweep hands a common
  owner of the two picks on the step below, which is the witness.

What is left is three picks or more: pair consistency gives a common owner for each pair, and
nothing forces those witnesses to agree. Measured (`helly dead`, report v132): on Tseitin K4 even
the descent never dead-ends — 140 anchors, 6,718 extensions, 664 full chains, 0 dead ends, with
the whole space of partial chains explored. Transitivity of ownership would close it (`a` owns `b`
and `b` owns `c` giving `a` owns `c` would make *any* parent extend), but that is false: 52,720 of
380,746 ordered triples fail it.
-/

namespace AbsSat.GraphPath.Model.Descent

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview (sharesEveryStep)
open AbsSat.GraphPath.Model.AggFixpoint (AggOk)
open AbsSat.GraphPath.Model.AdjacentOwners (Adj owners_below_iff_parents owners_above_iff_sons)
open AbsSat.GraphPath.Model.NoDeadEnd (SoundFrom upd)

/-- **The extension is a common owner.** A pick on the step below that every pick of the partial
chain owns extends the chain. -/
theorem extend_of_common_owner (g : GPathM) (a : Adj g) (hok : AggOk g)
    {sel : Int → PathNodeId} {lo : Int} (hlo : 0 < lo) (hhi : lo ≤ g.current_step - 1)
    (hs : SoundFrom g sel lo) {c : PathNodeId} {nc : PNodeM} (hc : g.node? c = some nc)
    (hcs : c.id.step = lo - 1)
    (hown : ∀ k, lo ≤ k → k < g.current_step → c ∈ ownersOf g (sel k)) :
    SoundFrom g (upd sel (lo - 1) c) (lo - 1) := by
  have hcsome : (g.node? c).isSome = true := by rw [hc]; rfl
  have hupd_lo : upd sel (lo - 1) c (lo - 1) = c := by
    show (if (lo - 1) = lo - 1 then c else sel (lo - 1)) = c
    rw [if_pos rfl]
  have hupd_hi : ∀ k, lo ≤ k → upd sel (lo - 1) c k = sel k := by
    intro k hk
    show (if k = lo - 1 then c else sel k) = sel k
    rw [if_neg (show ¬(k = lo - 1) from by omega)]
  -- the picks own `c` back, by the symmetry of the tables
  have hback : ∀ k, lo ≤ k → k < g.current_step → sel k ∈ ownersOf g c := by
    intro k hk0 hk1
    obtain ⟨hsome, hstep⟩ := hs.node k hk0 hk1
    obtain ⟨nk, hnk⟩ := Option.isSome_iff_exists.mp hsome
    have hco : c ∈ nk.owners := by
      have := hown k hk0 hk1
      simpa only [ownersOf, hnk] using this
    obtain ⟨hsym, _⟩ := hok (sel k) nk c nc hnk hc (by rw [hstep]; omega) (by rw [hstep]; exact hk1)
      (by rw [hcs]; omega) (by rw [hcs]; omega) hco (a.ctx.nodeval _ nk hnk)
      (a.ctx.nodeval _ nc hc)
    simpa only [ownersOf, hc] using hsym
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- a node at each step
    intro k hk0 hk1
    rcases int_eq_or_ne k (lo - 1) with rfl | hne
    · rw [hupd_lo]; exact ⟨hcsome, hcs⟩
    · rw [hupd_hi k (by omega)]; exact hs.node k (by omega) hk1
  · -- parent link
    intro k hk0 hk1
    rcases int_eq_or_ne k (lo - 1) with rfl | hne
    · rw [hupd_lo, hupd_hi (lo - 1 + 1) (by omega)]
      obtain ⟨hsome, hstep⟩ := hs.node lo (Int.le_refl _) (by omega)
      obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp hsome
      have hlow : c ∈ nl.owners := by
        have := hown lo (Int.le_refl _) (by omega)
        have hsl : sel (lo - 1 + 1) = sel lo := by rw [show lo - 1 + 1 = lo from by omega]
        simpa only [ownersOf, hnl] using this
      have hpar := (owners_below_iff_parents g a (sel lo) nl hnl (by rw [hstep]; omega) c
        (by rw [hcs, hstep])).mp hlow
      rw [show lo - 1 + 1 = lo from by omega, hnl]
      exact hpar
    · rw [hupd_hi k (by omega), hupd_hi (k + 1) (by omega)]
      exact hs.parent_link k (by omega) hk1
  · -- pairwise ownership
    intro i j hi0 hj0 hi1 hj1 hij
    rcases int_eq_or_ne i (lo - 1) with rfl | hni
    · rcases int_eq_or_ne j (lo - 1) with rfl | hnj
      · exact absurd rfl hij
      · rw [hupd_lo, hupd_hi j (by omega)]
        exact List.mem_filter.mpr ⟨hown j (by omega) hj1, beq_iff_eq.mpr hcs⟩
    · rcases int_eq_or_ne j (lo - 1) with rfl | hnj
      · rw [hupd_lo, hupd_hi i (by omega)]
        obtain ⟨_, hstep⟩ := hs.node i (by omega) hi1
        exact List.mem_filter.mpr ⟨hback i (by omega) hi1, beq_iff_eq.mpr hstep⟩
      · rw [hupd_hi i (by omega), hupd_hi j (by omega)]
        exact hs.owned i j (by omega) (by omega) hi1 hj1 hij
  · -- global owner
    intro k hk0 hk1
    rcases int_eq_or_ne k (lo - 1) with rfl | hne
    · rw [hupd_lo]
      obtain ⟨hsome, hstep⟩ := hs.node lo (Int.le_refl _) (by omega)
      obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp hsome
      have hlow : c ∈ nl.owners := by
        have := hown lo (Int.le_refl _) (by omega)
        simpa only [ownersOf, hnl] using this
      exact a.ctx.ownGow (sel lo) nl hnl c hlow (by rw [hcs]; omega) (by rw [hcs]; omega)
    · rw [hupd_hi k (by omega)]; exact hs.gowner k (by omega) hk1
  · -- self ownership
    intro k hk0 hk1
    rcases int_eq_or_ne k (lo - 1) with rfl | hne
    · rw [hupd_lo]
      simpa only [ownersOf, hc] using a.ctx.self c nc hc
    · rw [hupd_hi k (by omega)]; exact hs.self_owned k (by omega) hk1
  · -- son link
    intro k hk0 hk1
    rcases int_eq_or_ne k (lo - 1) with rfl | hne
    · rw [hupd_lo, hupd_hi (lo - 1 + 1) (by omega)]
      obtain ⟨_, hstep⟩ := hs.node lo (Int.le_refl _) (by omega)
      have hsl : sel (lo - 1 + 1) = sel lo := by rw [show lo - 1 + 1 = lo from by omega]
      rw [hsl]
      have hmem : sel lo ∈ nc.owners := by
        have := hback lo (Int.le_refl _) (by omega)
        simpa only [ownersOf, hc] using this
      have := (owners_above_iff_sons g a c nc hc (by rw [hcs]; omega) (sel lo)
        (by rw [hstep, hcs]; omega)).mp hmem
      simpa only [sonsOf, hc] using this
    · rw [hupd_hi k (by omega), hupd_hi (k + 1) (by omega)]
      exact hs.son_link k (by omega) hk1
  · -- root shape
    intro k hk0 hk1
    rcases int_eq_or_ne k (lo - 1) with rfl | hne
    · rw [hupd_lo]
      constructor
      · intro hroot
        have hmem := List.mem_of_find?_eq_some hc
        have hid := node?_id_eq g c nc hc
        by_cases h0 : c.id.step = 0
        · omega
        · exfalso
          have hnr := a.rc.shape.notroot nc hmem (by rw [hid]; omega)
          rw [hid] at hnr
          exact hnr hroot
      · intro hz
        have hmem := List.mem_of_find?_eq_some hc
        have hid := node?_id_eq g c nc hc
        have := a.rc.rootz nc hmem (by rw [hid, hcs]; omega)
        rw [hid] at this
        exact this
    · rw [hupd_hi k (by omega)]; exact hs.root_shape k (by omega) hk1

/-- **The first descent step is free.** Any parent of the anchor extends it. -/
theorem extend_anchor (g : GPathM) (a : Adj g) (hok : AggOk g) (hpos : 1 < g.current_step)
    {q : PathNodeId} (hq : SoundFrom g (fun _ => q) (g.current_step - 1)) :
    ∃ c, SoundFrom g (upd (fun _ => q) (g.current_step - 2) c) (g.current_step - 2) := by
  obtain ⟨hsome, hstep⟩ := hq.node (g.current_step - 1) (Int.le_refl _) (by omega)
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp hsome
  have hroot : nq.id.parent_id.isNone = false := by
    have hid := node?_id_eq g q nq hnq
    have hne : q.parent_id ≠ none := by
      intro hn
      have := (hq.root_shape (g.current_step - 1) (Int.le_refl _) (by omega)).mp hn
      omega
    rw [hid]
    cases hp : q.parent_id with
    | none => exact absurd hp hne
    | some _ => rfl
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _
    (SelfOwn.have_parents_of_isValidNode g nq (a.ctx.nodeval q nq hnq) hroot)
  obtain ⟨mc, hmc, hmcid⟩ := a.rc.shape.pn nq (List.mem_of_find?_eq_some hnq) c hc
  have hcnode : g.node? c = some mc := by rw [← hmcid]; exact node?_of_mem a.rc.nodup mc hmc
  have hcstep : c.id.step = g.current_step - 2 := by
    have hid := node?_id_eq g q nq hnq
    have := a.rc.shape.pbelow nq (List.mem_of_find?_eq_some hnq) c hc
    rw [hid, hstep] at this
    omega
  have hcown : c ∈ nq.owners :=
    (owners_below_iff_parents g a q nq hnq (by rw [hstep]; omega) c
      (by rw [hcstep, hstep]; omega)).mpr hc
  have hcommon : ∀ k, g.current_step - 1 ≤ k → k < g.current_step →
      c ∈ ownersOf g ((fun _ => q) k) := by
    intro k _ _
    simpa only [ownersOf, hnq] using hcown
  have hstep2 : c.id.step = g.current_step - 1 - 1 := by omega
  have hgoal := extend_of_common_owner g a hok (sel := fun _ => q) (lo := g.current_step - 1)
    (by omega) (Int.le_refl _) hq hcnode hstep2 hcommon
  rw [show g.current_step - 1 - 1 = g.current_step - 2 from by omega] at hgoal
  exact ⟨c, hgoal⟩

/-- **The second descent step is free too.** The pair consistency of the sweep hands a common
owner of the two picks on the step below, and that is the witness. -/
theorem extend_pair (g : GPathM) (a : Adj g) (hok : AggOk g) (hpos : 2 < g.current_step)
    {sel : Int → PathNodeId} (hs : SoundFrom g sel (g.current_step - 2)) :
    ∃ c, SoundFrom g (upd sel (g.current_step - 3) c) (g.current_step - 3) := by
  have hlo : (0:Int) < g.current_step - 2 := by omega
  obtain ⟨hxsome, hxstep⟩ := hs.node (g.current_step - 2) (Int.le_refl _) (by omega)
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp hxsome
  obtain ⟨hysome, hystep⟩ := hs.node (g.current_step - 1) (by omega) (by omega)
  obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp hysome
  -- the upper pick is an owner of the lower one
  have hyx : sel (g.current_step - 1) ∈ nx.owners := by
    have h := hs.owned (g.current_step - 1) (g.current_step - 2) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    have h' := (List.mem_filter.mp h).1
    simpa only [ownersOf, hnx] using h'
  -- pair consistency at the step below
  obtain ⟨_, hsh⟩ := hok _ nx _ ny hnx hny (by rw [hxstep]; omega) (by rw [hxstep]; omega)
    (by rw [hystep]; omega) (by rw [hystep]; omega) hyx (a.ctx.nodeval _ nx hnx)
    (a.ctx.nodeval _ ny hny)
  have hall : (intRange 0 (g.current_step - 1)).all
      (fun j => !hasStepEntry ny.owners j || (ownersAt nx.owners j).any
        (fun r => ny.owners.contains r)) = true := by
    simpa only [sharesEveryStep] using hsh
  have hcl := List.all_eq_true.mp hall (g.current_step - 3) (mem_intRange (by omega) (by omega))
  have hent : hasStepEntry ny.owners (g.current_step - 3) = true :=
    LocalContradiction.ownersOk_of_isValidNode g ny (a.ctx.nodeval _ ny hny) _ (by omega) (by omega)
  simp only [hent, Bool.not_true, Bool.false_or] at hcl
  obtain ⟨c, hcx, hcy⟩ := List.any_eq_true.mp hcl
  have hcxo : c ∈ nx.owners := (List.mem_filter.mp hcx).1
  have hcstep : c.id.step = g.current_step - 3 := eq_of_beq (List.mem_filter.mp hcx).2
  have hcyo : c ∈ ny.owners := List.mem_of_elem_eq_true hcy
  -- the witness is a node
  have hcgow : c ∈ g.gowners :=
    a.ctx.ownGow _ nx hnx c hcxo (by rw [hcstep]; omega) (by rw [hcstep]; omega)
  obtain ⟨mc, hmc, hmcid⟩ := a.rc.gn c hcgow
  have hcnode : g.node? c = some mc := by rw [← hmcid]; exact node?_of_mem a.rc.nodup mc hmc
  have hcommon : ∀ k, g.current_step - 2 ≤ k → k < g.current_step → c ∈ ownersOf g (sel k) := by
    intro k hk0 hk1
    rcases int_eq_or_ne k (g.current_step - 2) with rfl | hne
    · simpa only [ownersOf, hnx] using hcxo
    · have hk : k = g.current_step - 1 := by omega
      subst hk
      simpa only [ownersOf, hny] using hcyo
  have hstep3 : c.id.step = g.current_step - 2 - 1 := by omega
  have hgoal := extend_of_common_owner g a hok (lo := g.current_step - 2) hlo (by omega) hs
    hcnode hstep3 hcommon
  rw [show g.current_step - 2 - 1 = g.current_step - 3 from by omega] at hgoal
  exact ⟨c, hgoal⟩


-- ============================================================
-- The one statement left
-- ============================================================

/-- **The single statement the whole verdict rests on.** The picks of a partial chain have an owner
in common on the step below.

The sweep already gives this **pair by pair** (`AggFixpoint.aggOk_reviewAgg`: any two owners share
an entry at every step). What is missing is the step from pairs to the whole set of picks — and the
picks are a *clique* of the pairwise-compatibility relation, with a common neighbour for every pair
on that step. In the language of constraint propagation: the machine maintains 2-consistency and the
descent needs k-consistency, which does not follow for an arbitrary network and follows here only
from the structure the machine keeps (the tables of a node are born from one history, `RunEnv`). -/
def CommonOwner (g : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo : Int), 0 < lo → lo ≤ g.current_step - 1 → SoundFrom g sel lo →
    ∃ c nc, g.node? c = some nc ∧ c.id.step = lo - 1 ∧
      ∀ k, lo ≤ k → k < g.current_step → c ∈ ownersOf g (sel k)

/-- **With one parent per node, the common owner is free.** The pick at `lo` is not a root, so it has
a parent `c`, and `SingleParents` makes it *the* parent. For every pick above, the sweep's pair
consistency hands a common owner on the step below `lo`; an owner exactly one step below a node **is**
a parent of it (`owners_below_iff_parents`), so each of those witnesses is `c` itself. The `k`-fold
intersection the descent asks for is therefore the 2-fold one, read `k` times at the same node.

This is `ParentWitness.par_witness_triple` along the whole partial chain instead of one triple, and it
is where the window pays: by `ParentWitness.parents_differ_below` two parents of a node agree on their
map id (`PMP`) and on their own parent (`GPMP`), so `SingleParent` is the statement that the previous
line holds no two nodes with the same two-step history — one level deeper than what a window of two
could even say. -/
theorem commonOwner_of_singleParents (g : GPathM) (a : Adj g) (hok : AggOk g)
    (hsp : ParentWitness.SingleParents g) : CommonOwner g := by
  intro sel lo hlo0 hlo hs
  obtain ⟨hsome, hstep⟩ := hs.node lo (Int.le_refl _) (by omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = sel lo := node?_id_eq g _ n hn
  -- above step 0 the pick is not a root, so it has a parent
  have hroot : n.id.parent_id.isNone = false := by
    have hne : (sel lo).parent_id ≠ none := by
      intro hnone
      have := (hs.root_shape lo (Int.le_refl _) (by omega)).mp hnone
      omega
    rw [hid]
    cases hp : (sel lo).parent_id with
    | none => exact absurd hp hne
    | some _ => rfl
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _
    (SelfOwn.have_parents_of_isValidNode g n (a.ctx.nodeval _ n hn) hroot)
  obtain ⟨mc, hmc, hmcid⟩ := a.rc.shape.pn n hmem c hc
  have hcnode : g.node? c = some mc := by rw [← hmcid]; exact node?_of_mem a.rc.nodup mc hmc
  have hcstep : c.id.step = lo - 1 := by
    have := a.rc.shape.pbelow n hmem c hc
    rw [hid, hstep] at this
    omega
  have hcown : c ∈ n.owners :=
    (owners_below_iff_parents g a (sel lo) n hn (by rw [hstep]; omega) c
      (by rw [hcstep, hstep])).mpr hc
  refine ⟨c, mc, hcnode, hcstep, fun k hk0 hk1 => ?_⟩
  rcases int_eq_or_ne k lo with rfl | hne
  · simpa only [ownersOf, hn] using hcown
  · -- the pick above owns `sel lo`, so pair consistency shares an owner on the step below
    obtain ⟨hksome, hkstep⟩ := hs.node k hk0 hk1
    obtain ⟨nk, hnk⟩ := Option.isSome_iff_exists.mp hksome
    have hkx : sel k ∈ n.owners := by
      have h := hs.owned k lo hk0 (Int.le_refl _) hk1 (by omega) hne
      have h' := (List.mem_filter.mp h).1
      simpa only [ownersOf, hn] using h'
    obtain ⟨w, hwn, hwk, hws⟩ := ParentWitness.shared_owner a hok hn hnk
      (by rw [hstep]; omega) (by rw [hstep]; omega)
      (by rw [hkstep]; omega) (by rw [hkstep]; exact hk1) hkx (lo - 1) (by omega) (by omega)
    -- and that shared owner is one step below `sel lo`, hence a parent of it, hence `c`
    have hwp : w ∈ n.parents :=
      (owners_below_iff_parents g a (sel lo) n hn (by rw [hstep]; omega) w
        (by rw [hws, hstep])).mp hwn
    have hwc : w = c := hsp n hmem w hwp c hc
    rw [hwc] at hwk
    simpa only [ownersOf, hnk] using hwk

/-- info: 'AbsSat.GraphPath.Model.Descent.commonOwner_of_singleParents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms commonOwner_of_singleParents

/-- **And with it the state has no dead ends**, so the verdict follows
(`NoDeadEndVerdict.sat_of_noDeadEnd`). -/
theorem noDeadEnd_of_commonOwner (g : GPathM) (a : Adj g) (hok : AggOk g)
    (h : CommonOwner g) : NoDeadEnd.NoDeadEnd g := by
  intro sel lo hlo0 hlo hs
  obtain ⟨c, nc, hc, hcs, hown⟩ := h sel lo hlo0 hlo hs
  exact ⟨c, extend_of_common_owner g a hok hlo0 hlo hs hc hcs hown⟩

/-- info: 'AbsSat.GraphPath.Model.Descent.noDeadEnd_of_commonOwner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_of_commonOwner

/-- info: 'AbsSat.GraphPath.Model.Descent.extend_of_common_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms extend_of_common_owner

/-- info: 'AbsSat.GraphPath.Model.Descent.extend_anchor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms extend_anchor

/-- info: 'AbsSat.GraphPath.Model.Descent.extend_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms extend_pair

end AbsSat.GraphPath.Model.Descent
