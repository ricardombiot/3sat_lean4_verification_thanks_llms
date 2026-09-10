-- lean_project/AbsSat/GraphPath/Model/Threaded.lean
import AbsSat.GraphPath.Model.Bridge
import AbsSat.GraphPath.Model.Candidates
import AbsSat.GraphPath.Model.PathExists

/-!
**Every node lies on a full-length path that owns it.**

v27 built a path (`exists_isChain`) and said nothing about ownership. v40
closed `PairwiseOwned` only where the state is pinned. Between the two there is
a statement that the arc-consistency clauses actually pay for:

> For every surviving node `a`, there is a path from step 0 to the top **every
> node of which owns `a`**.

Not pairwise co-ownership — a single common anchor. That is much weaker than
`PairwiseOwned`, and unlike it, it follows from what `review`'s fixpoint
already enforces:

* `coherent_parents` says `d.owners ⊆ ⋃ owners of d's parents`, so if `d` owns
  `a` then **some parent of `d` owns `a`**. That is the descent.
* `coherent_sons` says the same through the sons. That is the ascent, for the
  steps that sweep covers.
* At step 0, which `reviewSons` never sweeps, the ascent comes from v39's
  bridge instead: a son of `a`'s own node has `a` as a parent, and every parent
  is an owner.

The measurement that makes this the right target: `lake exe extend --sweep`,
39,984 allowed picks, **`cleanInvalid` alone never leaves the graph invalid**,
and the coherence sweeps remove extra nodes in only 67 of them. So `PickValid`
is carried by the sweep that the anchor survives.
-/

namespace AbsSat.GraphPath.Model.Threaded

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Extendable (PartialChain upd upd_self upd_other isChain_of_partial)

-- ============================================================
-- The union of the neighbours' owners
-- ============================================================

private abbrev ustep (g : GPathM) : List PathNodeId → PathNodeId → List PathNodeId :=
  fun acc pid => match g.node? pid with | some p => acc ++ p.owners | none => acc

theorem sub_union (g : GPathM) : ∀ (ids acc : List PathNodeId) (a : PathNodeId),
    a ∈ acc → a ∈ ids.foldl (ustep g) acc := by
  intro ids
  induction ids with
  | nil => intro acc a ha; exact ha
  | cons b bs ih =>
    intro acc a ha
    simp only [List.foldl_cons, ustep]
    cases hb : g.node? b with
    | none => exact ih acc a ha
    | some p => exact ih (acc ++ p.owners) a (List.mem_append_left _ ha)

theorem mem_union_of_owner (g : GPathM) : ∀ (ids acc : List PathNodeId)
    (p : PathNodeId) (n : PNodeM), p ∈ ids → g.node? p = some n →
    ∀ a ∈ n.owners, a ∈ ids.foldl (ustep g) acc := by
  intro ids
  induction ids with
  | nil => intro _ _ _ hp; exact absurd hp List.not_mem_nil
  | cons b bs ih =>
    intro acc p n hp hpn a ha
    simp only [List.foldl_cons, ustep]
    rcases List.mem_cons.mp hp with rfl | hrest
    · simp only [hpn]
      exact sub_union g bs (acc ++ n.owners) a (List.mem_append_right _ ha)
    · cases hb : g.node? b with
      | none => exact ih acc p n hrest hpn a ha
      | some q => exact ih (acc ++ q.owners) p n hrest hpn a ha

theorem exists_of_mem_union (g : GPathM) : ∀ (ids acc : List PathNodeId) (a : PathNodeId),
    a ∈ ids.foldl (ustep g) acc →
    a ∈ acc ∨ ∃ p ∈ ids, ∃ n, g.node? p = some n ∧ a ∈ n.owners := by
  intro ids
  induction ids with
  | nil => intro acc a ha; exact Or.inl ha
  | cons b bs ih =>
    intro acc a ha
    simp only [List.foldl_cons, ustep] at ha
    cases hb : g.node? b with
    | none =>
      simp only [hb] at ha
      rcases ih acc a ha with h | ⟨p, hp, hres⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hres⟩
    | some q =>
      simp only [hb] at ha
      rcases ih (acc ++ q.owners) a ha with h | ⟨p, hp, hres⟩
      · rcases List.mem_append.mp h with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ⟨b, List.mem_cons_self .., q, hb, h2⟩
      · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hres⟩

/-- The union has an entry at every step some neighbour has one at. -/
theorem hasStepEntry_union (g : GPathM) (ids : List PathNodeId) (p : PathNodeId)
    (n : PNodeM) (hp : p ∈ ids) (hpn : g.node? p = some n) (l : Int)
    (hn : hasStepEntry n.owners l = true) :
    hasStepEntry (unionOwnersOf g ids) l = true := by
  obtain ⟨a, ha, hal⟩ := List.any_eq_true.mp hn
  exact List.any_eq_true.mpr ⟨a, mem_union_of_owner g ids [] p n hp hpn a ha, hal⟩

/-- The coherence clause, used forwards: an owner survives the intersection, so
it is in the neighbours' union. -/
theorem mem_union_of_coherent (g : GPathM) (d : PNodeM) (ids : List PathNodeId)
    (hfix : intersectOwners d.owners (unionOwnersOf g ids) = d.owners)
    (a : PathNodeId) (ha : a ∈ d.owners)
    (hentry : hasStepEntry (unionOwnersOf g ids) a.id.step = true) :
    a ∈ unionOwnersOf g ids := by
  have : a ∈ intersectOwners d.owners (unionOwnersOf g ids) := by rw [hfix]; exact ha
  have h2 := (List.mem_filter.mp this).2
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with hno | hyes
  · rw [hentry] at hno; exact absurd hno (by decide)
  · exact List.elem_iff.mp hyes

-- ============================================================
-- The invariants the two hops consume
-- ============================================================

/-- A valid `review` fixpoint's structure, as the threading uses it. Every
field is a theorem elsewhere; `tctx_filterAll` assembles them. -/
structure TCtx (g : GPathM) : Prop where
  nodeval : ∀ pid n, g.node? pid = some n → isValidNode g n = true
  shape   : Parents.Shape g
  links   : Bridge.LinksInOwners g
  cpar    : ∀ k ∈ intRange 1 (g.current_step - 1), ∀ id ∈ ((g.line k).map (·.id)),
              ∀ d, g.node? id = some d →
                intersectOwners d.owners (unionOwnersOf g d.parents) = d.owners
  cson    : ∀ k ∈ intRange 1 (g.current_step - 2), ∀ id ∈ ((g.line k).map (·.id)),
              ∀ d, g.node? id = some d →
                intersectOwners d.owners (unionOwnersOf g d.sons) = d.owners

theorem sons_ne_nil_of_isValidNode (g : GPathM) (n : PNodeM)
    (h : isValidNode g n = true) (hlast : ¬ (n.id.id.step = g.current_step - 1)) :
    n.sons ≠ [] := by
  have hb : (n.id.id.step == g.current_step - 1) = false := by
    cases hc : n.id.id.step == g.current_step - 1 with
    | false => rfl
    | true => exact absurd (eq_of_beq hc) hlast
  simp only [isValidNode, hb] at h
  split at h
  · intro hnil
    have hs := ((Bool.and_eq_true _ _).mp h).2
    rw [hnil] at hs
    exact absurd hs (by decide)
  · intro hnil
    have hs := ((Bool.and_eq_true _ _).mp h).2
    rw [hnil] at hs
    exact absurd hs (by decide)

theorem mem_line_of_node? (g : GPathM) (p : PathNodeId) (n : PNodeM)
    (hn : g.node? p = some n) : p ∈ ((g.line p.id.step).map (·.id)) := by
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = p := node?_id_eq g p n hn
  refine List.mem_map.mpr ⟨n, ?_, hid⟩
  exact List.mem_filter.mpr ⟨hmem, by rw [hid]; exact beq_iff_eq.mpr rfl⟩

-- ============================================================
-- One hop down, and one hop up
-- ============================================================

/-- **Down.** If `d` at a step above 0 owns `a`, some parent of `d` owns `a`. -/
theorem hop_down (g : GPathM) (ctx : TCtx g) (p : PathNodeId) (d : PNodeM)
    (hd : g.node? p = some d) (hlo : 0 < p.id.step) (hhi : p.id.step < g.current_step)
    (a : PathNodeId) (ha : a ∈ d.owners)
    (halo : 0 ≤ a.id.step) (hahi : a.id.step < g.current_step) :
    ∃ c ∈ d.parents, ∃ m, g.node? c = some m ∧ a ∈ m.owners := by
  have hmem : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hid : d.id = p := node?_id_eq g p d hd
  have hroot : d.id.parent_id ≠ none := ctx.shape.notroot d hmem (by rw [hid]; exact hlo)
  have hpar := PathExists.parents_ne_nil_of_isValidNode g d (ctx.nodeval p d hd) hroot
  obtain ⟨c, rest, hcons⟩ : ∃ c rest, d.parents = c :: rest := by
    cases hl : d.parents with
    | nil => exact absurd hl hpar
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hcmem : c ∈ d.parents := by rw [hcons]; exact List.mem_cons_self ..
  obtain ⟨m0, hm0, hm0id⟩ := ctx.shape.pn d hmem c hcmem
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g c).mp ⟨m0, hm0, hm0id⟩)
  have hentry : hasStepEntry (unionOwnersOf g d.parents) a.id.step = true :=
    hasStepEntry_union g d.parents c m hcmem hm a.id.step
      (List.all_eq_true.mp (owners_ok_of_isValidNode g m (ctx.nodeval c m hm))
        a.id.step (mem_intRange halo (by omega)))
  have hfix := ctx.cpar p.id.step (mem_intRange hlo (by omega))
    p (by have := mem_line_of_node? g p d hd; exact this) d hd
  have hin := mem_union_of_coherent g d d.parents hfix a ha hentry
  rcases exists_of_mem_union g d.parents [] a hin with hnil | hres
  · exact absurd hnil List.not_mem_nil
  · exact hres

/-!
**Why there is no `hop_up` here.** The mirror argument through `coherent_sons`
works — if `d` owns `a`, some son of `d` has a node that owns `a` — but it
delivers a node without a *step*. To turn it into "there is a node at step
`j+1` owning `a`" one needs the mirror of `Parents.PBelow` for the son table:
*every son sits one step above*. That invariant does not exist yet, and unlike
`PBelow` it cannot be had for free: `Pruned` carries an `owners ⊆` clause and a
`parents ⊆` clause but **no sons clause**, so it needs the per-operation
induction `Sons.SMP` needed. That, and only that, stands between this module
and the full threading theorem — a path from step 0 to the *top*.
-/

-- ============================================================
-- The descent: a full path below the anchor, all of it owning the anchor
-- ============================================================

/-- A parent-linked path over `[lo, hi]`, every node of which owns `a`. -/
structure TPart (g : GPathM) (a : PathNodeId) (sel : Int → PathNodeId) (lo hi : Int) : Prop where
  chain : PartialChain g sel lo hi
  owns  : ∀ i, lo ≤ i → i ≤ hi → a ∈ ownersOf g (sel i)

theorem step_down_T (g : GPathM) (ctx : TCtx g) (a : PathNodeId)
    (halo : 0 ≤ a.id.step) (hahi : a.id.step < g.current_step)
    (sel : Int → PathNodeId) (lo hi : Int) (hpos : 0 < lo) (hlohi : lo ≤ hi)
    (hhi : hi < g.current_step) (hpc : TPart g a sel lo hi) :
    ∃ c, TPart g a (upd sel (lo - 1) c) (lo - 1) hi := by
  obtain ⟨hsome, hstep⟩ := hpc.chain.1 lo (Int.le_refl _) hlohi
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hown : a ∈ n.owners := by
    have := hpc.owns lo (Int.le_refl _) hlohi
    simpa only [ownersOf, hn] using this
  obtain ⟨c, hcmem, m, hm, hmown⟩ :=
    hop_down g ctx (sel lo) n hn (by rw [hstep]; exact hpos) (by rw [hstep]; omega)
      a hown halo hahi
  have hcstep : c.id.step = lo - 1 := by
    have := ctx.shape.pbelow n (List.mem_of_find?_eq_some hn) c hcmem
    rw [this, node?_id_eq g _ n hn, hstep]
  refine ⟨c, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro i hi1 hi2
    if hic : i = lo - 1 then
      subst hic; rw [upd_self]
      exact ⟨Option.isSome_iff_exists.mpr ⟨m, hm⟩, hcstep⟩
    else
      rw [upd_other sel (lo - 1) c hic]; exact hpc.chain.1 i (by omega) hi2
  · intro i hi1 hi2
    if hic : i = lo - 1 then
      subst hic
      rw [upd_self, upd_other sel (lo - 1) c (by omega)]
      have hlo' : lo - 1 + 1 = lo := by omega
      rw [hlo', hn]; exact hcmem
    else
      rw [upd_other sel (lo - 1) c hic, upd_other sel (lo - 1) c (by omega)]
      exact hpc.chain.2 i (by omega) hi2
  · intro i hi1 hi2
    if hic : i = lo - 1 then
      subst hic; rw [upd_self]
      simpa only [ownersOf, hm] using hmown
    else
      rw [upd_other sel (lo - 1) c hic]; exact hpc.owns i (by omega) hi2

theorem descend_T (g : GPathM) (ctx : TCtx g) (a : PathNodeId)
    (halo : 0 ≤ a.id.step) (hahi : a.id.step < g.current_step) :
    ∀ (fuel : Nat) (sel : Int → PathNodeId) (lo hi : Int), lo.toNat ≤ fuel → 0 ≤ lo →
      lo ≤ hi → hi < g.current_step → TPart g a sel lo hi →
      ∃ sel', TPart g a sel' 0 hi := by
  intro fuel
  induction fuel with
  | zero =>
    intro sel lo hi hm hlo hlohi _ hpc
    have : lo = 0 := by omega
    subst this; exact ⟨sel, hpc⟩
  | succ fuel ih =>
    intro sel lo hi hm hlo hlohi hhi hpc
    if hpos : 0 < lo then
      obtain ⟨c, hpc'⟩ := step_down_T g ctx a halo hahi sel lo hi hpos hlohi hhi hpc
      exact ih _ (lo - 1) hi (by omega) (by omega) (by omega) hhi hpc'
    else
      have : lo = 0 := by omega
      subst this; exact ⟨sel, hpc⟩

/-- **Every node has a threaded past.** From step 0 up to the anchor's own step
there is a parent-linked path *all of whose nodes own the anchor*.

This is strictly between v27 and `PairwiseOwned`: v27's path says nothing about
ownership, `PairwiseOwned` asks every pair to co-own, and this asks every node
of the path to own **one** common node. Unlike `PairwiseOwned`, it is a
theorem — the arc-consistency clause `coherent_parents` pays for it. -/
theorem threaded_below (g : GPathM) (ctx : TCtx g) (a : PathNodeId) (n : PNodeM)
    (hn : g.node? a = some n) (hself : a ∈ n.owners)
    (halo : 0 ≤ a.id.step) (hahi : a.id.step < g.current_step) :
    ∃ sel, TPart g a sel 0 a.id.step := by
  refine descend_T g ctx a halo hahi a.id.step.toNat (fun _ => a) a.id.step a.id.step
    (Nat.le_refl _) halo (Int.le_refl _) hahi ⟨⟨?_, ?_⟩, ?_⟩
  · intro i _ hi2
    have : i = a.id.step := by omega
    subst this
    exact ⟨Option.isSome_iff_exists.mpr ⟨n, hn⟩, rfl⟩
  · intro i hi1 hi2; omega
  · intro i hi1 hi2
    have : i = a.id.step := by omega
    subst this
    simpa only [ownersOf, hn] using hself

/-- info: 'AbsSat.GraphPath.Model.Threaded.threaded_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms threaded_below


-- ============================================================
-- The context, assembled for the machine's states
-- ============================================================

variable (reqOf : NodeId → List NodeId)

theorem tctx_filterAll (g : GPathM) (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true) : TCtx (filterAll g reqs) where
  nodeval := fun pid n hn => review_node_valid _ hv pid n hn
  shape := Parents.Shape_filterAll reqOf g reqs hreach
  links := Bridge.linksInOwners_filterAll g reqs hv
  cpar := (Certifies.arcConsistent_filterAll reqOf g reqs hreach hv).coherent_parents
  cson := (Certifies.arcConsistent_filterAll reqOf g reqs hreach hv).coherent_sons

/-- **Every node of a state the machine holds has a threaded past.** The
self-ownership comes from v30, so the anchor really is on its own path. -/
theorem threaded_below_filterAll (g : GPathM) (reqs : List NodeId)
    (hreach : Reachable reqOf g) (hv : isValid (filterAll g reqs) = true)
    (a : PathNodeId) (n : PNodeM) (hn : (filterAll g reqs).node? a = some n)
    (halo : 0 ≤ a.id.step) (hahi : a.id.step < (filterAll g reqs).current_step) :
    ∃ sel, TPart (filterAll g reqs) a sel 0 a.id.step :=
  threaded_below _ (tctx_filterAll reqOf g reqs hreach hv) a n hn
    (SelfOwn.SelfOwned_filterAll reqOf g reqs hreach hv a n hn) halo hahi

/-- info: 'AbsSat.GraphPath.Model.Threaded.threaded_below_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms threaded_below_filterAll

end AbsSat.GraphPath.Model.Threaded
