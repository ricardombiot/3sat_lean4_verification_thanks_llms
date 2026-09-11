-- lean_project/AbsSat/GraphPath/Model/Threaded.lean
import AbsSat.GraphPath.Model.Bridge
import AbsSat.GraphPath.Model.Candidates
import AbsSat.GraphPath.Model.PathExists

/-!
**Every node lies on a full-length path that owns it.**

v27 built a path (`exists_isChain`) and said nothing about ownership. v40
closed `PairwiseOwned` only where the state is pinned. Between the two there is
a statement that the arc-consistency clauses actually pay for:

> For every surviving node `a` above step 0, there is a path from step 0 to the
> top **every node of which owns `a`**.

Not pairwise co-ownership — a single common anchor. That is much weaker than
`PairwiseOwned`, and unlike it, it follows from what `review`'s fixpoint
already enforces:

* `coherent_parents` says `d.owners ⊆ ⋃ owners of d's parents`, so if `d` owns
  `a` then **some parent of `d` owns `a`**. That is the descent, and it is what
  supplies the parent links of the path.
* `coherent_sons` says the same through the sons, and `Sons.SAbove` — every son
  sits one step above — turns that into a climb by step number. Only existence
  is needed here; the links come from the descent afterwards.

So the construction is: climb from `a` to the top, then descend from there.

**What is still out of reach: step 0.** `reviewSons` sweeps steps
`1 .. current_step-2`, so `coherent_sons` is silent at step 0 and the climb
cannot start there — hence the hypothesis `1 ≤ a.id.step` on `threaded`.
Closing it needs either that sweep extended, or the *other* son-table mirror
(every son has the node as one of its parents), which is a different invariant
from `SAbove` and would take the induction `Sons.SMP` took. Measured cost:
`lake exe extend --pickvalid`, **3,090 of 63,314** allowed picks sit at step 0.

The measurement that makes this the right target: `lake exe extend --sweep`,
39,984 allowed picks, **`cleanInvalid` alone never leaves the graph invalid**,
and the coherence sweeps remove extra nodes in only 67 of them. So `PickValid`
is carried by the sweep the anchor survives.
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
  cson    : ∀ k ∈ intRange 0 (g.current_step - 2), ∀ id ∈ ((g.line k).map (·.id)),
              ∀ d, g.node? id = some d →
                intersectOwners d.owners (unionOwnersOf g d.sons) = d.owners
  sabove  : Sons.SAbove g
  sn      : Sons.SN g
  pms     : Sons.PMS g
  ownerNode : ∀ pid n, g.node? pid = some n → ∀ q ∈ n.owners,
                0 ≤ q.id.step → q.id.step < g.current_step → (g.node? q).isSome = true

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

/-- **A node that does not branch hands its parent everything.** `hop_down`
says each owner of `p` is an owner of *some* parent. With exactly one parent
there is nothing to choose, so the whole owner set transfers at once:

    parents p = [c]  ⟹  owners p ⊆ owners c   (in range)

This is the `down` half of `Extendable.GoodParentOnCliques` at every node that
does not branch — which `lake exe extend --randomupdown` puts at 473,730 of
594,332 configurations. What it does **not** settle is the branching case:
sibling parents have different owner sets (4,274 pairs), and every one of those
pairs is *incomparable*, so there is no maximum parent to fall back on. -/
theorem owners_subset_of_unique_parent (g : GPathM) (ctx : TCtx g)
    (p : PathNodeId) (d : PNodeM) (hd : g.node? p = some d)
    (hlo : 0 < p.id.step) (hhi : p.id.step < g.current_step)
    (c : PathNodeId) (hpar : d.parents = [c]) (m : PNodeM) (hm : g.node? c = some m)
    (q : PathNodeId) (hq : q ∈ d.owners)
    (hqlo : 0 ≤ q.id.step) (hqhi : q.id.step < g.current_step) :
    q ∈ m.owners := by
  obtain ⟨c', hc', m', hm', hqm⟩ := hop_down g ctx p d hd hlo hhi q hq hqlo hqhi
  rw [hpar] at hc'
  rcases List.mem_singleton.mp hc' with rfl
  have hmm : m' = m := Option.some.inj (hm'.symm.trans hm)
  rw [← hmm]; exact hqm

/-- info: 'AbsSat.GraphPath.Model.Threaded.owners_subset_of_unique_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms owners_subset_of_unique_parent

/-- **Up.** The mirror of `hop_down` through `coherent_sons`: if `d` owns `a`,
some son of `d` — a node one step above, by `Sons.SAbove` — owns `a` too.

`SAbove` is what v41 said was missing here, and it is now a theorem
(`Sons.SAbove_reachable`). What remains out of reach is only step 0:
`reviewSons` sweeps steps `1 .. current_step-2`, so `coherent_sons` says
nothing at step 0, and the hypothesis `1 ≤ p.id.step` below is not removable
by this argument. -/
theorem hop_up (g : GPathM) (ctx : TCtx g) (p : PathNodeId) (d : PNodeM)
    (hd : g.node? p = some d) (hlo : 0 ≤ p.id.step) (hhi : p.id.step ≤ g.current_step - 2)
    (a : PathNodeId) (ha : a ∈ d.owners)
    (halo : 0 ≤ a.id.step) (hahi : a.id.step < g.current_step) :
    ∃ c ∈ d.sons, ∃ m, g.node? c = some m ∧ a ∈ m.owners ∧ c.id.step = p.id.step + 1 := by
  have hmem : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hid : d.id = p := node?_id_eq g p d hd
  have hson := sons_ne_nil_of_isValidNode g d (ctx.nodeval p d hd) (by rw [hid]; omega)
  obtain ⟨c₀, rest, hcons⟩ : ∃ c rest, d.sons = c :: rest := by
    cases hl : d.sons with
    | nil => exact absurd hl hson
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hc₀mem : c₀ ∈ d.sons := by rw [hcons]; exact List.mem_cons_self ..
  -- a witness son, so the union has an entry at `a`'s step
  have hstep₀ : c₀.id.step = p.id.step + 1 := by
    have := ctx.sabove d hmem c₀ hc₀mem; rw [hid] at this; exact this
  have hc₀own : c₀ ∈ d.owners := (ctx.links p d hd).2 c₀ hc₀mem
  obtain ⟨m₀, hm₀⟩ := Option.isSome_iff_exists.mp
    (ctx.ownerNode p d hd c₀ hc₀own (by rw [hstep₀]; omega) (by rw [hstep₀]; omega))
  have hentry : hasStepEntry (unionOwnersOf g d.sons) a.id.step = true :=
    hasStepEntry_union g d.sons c₀ m₀ hc₀mem hm₀ a.id.step
      (List.all_eq_true.mp (owners_ok_of_isValidNode g m₀ (ctx.nodeval c₀ m₀ hm₀))
        a.id.step (mem_intRange halo (by omega)))
  have hfix := ctx.cson p.id.step (mem_intRange hlo (by omega))
    p (mem_line_of_node? g p d hd) d hd
  have hin := mem_union_of_coherent g d d.sons hfix a ha hentry
  rcases exists_of_mem_union g d.sons [] a hin with hnil | ⟨c, hcmem, m, hm, hmown⟩
  · exact absurd hnil List.not_mem_nil
  · refine ⟨c, hcmem, m, hm, hmown, ?_⟩
    have := ctx.sabove d hmem c hcmem; rw [hid] at this; exact this

/-- **The first hop, from step 0** — the one `coherent_sons` cannot make,
because `reviewSons` never sweeps step 0. `Sons.PMS` makes it instead: a son of
the anchor's own node has the anchor among its **parents**, and v39's bridge
turns a parent into an owner. `Sons.SAbove` supplies the step.

This is what v42 said was missing, and it is why `threaded` below no longer
needs `1 ≤ a.id.step`. -/
theorem hop_up_zero (g : GPathM) (ctx : TCtx g) (a : PathNodeId) (n : PNodeM)
    (hn : g.node? a = some n) (hz : a.id.step = 0) (hpos : 1 < g.current_step) :
    ∃ c m, g.node? c = some m ∧ a ∈ m.owners ∧ c.id.step = 1 := by
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = a := node?_id_eq g a n hn
  have hlast : ¬ (n.id.id.step = g.current_step - 1) := by
    intro hc
    rw [hid] at hc
    omega
  have hson := sons_ne_nil_of_isValidNode g n (ctx.nodeval a n hn) hlast
  obtain ⟨c, rest, hcons⟩ : ∃ c rest, n.sons = c :: rest := by
    cases hl : n.sons with
    | nil => exact absurd hl hson
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hcmem : c ∈ n.sons := by rw [hcons]; exact List.mem_cons_self ..
  obtain ⟨m0, hm0, hm0id⟩ := ctx.sn n hmem c hcmem
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g c).mp ⟨m0, hm0, hm0id⟩)
  have hmmem : m ∈ g.nodes := List.mem_of_find?_eq_some hm
  have hmid : m.id = c := node?_id_eq g c m hm
  have hpar : a ∈ m.parents := by
    have := ctx.pms n hmem c hcmem m hmmem hmid
    rwa [hid] at this
  refine ⟨c, m, hm, (ctx.links c m hm).1 a hpar, ?_⟩
  have hsa := ctx.sabove n hmem c hcmem
  rw [hid] at hsa
  omega

/-- **Climb to the top.** Iterating `hop_up`: from an owner-carrying node above
step 0 there is one at the very top. Only existence is claimed — the *linked*
path is built afterwards, by descending. -/
theorem climb (g : GPathM) (ctx : TCtx g) (a : PathNodeId)
    (halo : 0 ≤ a.id.step) (hahi : a.id.step < g.current_step) :
    ∀ (fuel : Nat) (j : Int), (g.current_step - 1 - j).toNat ≤ fuel → 1 ≤ j →
      j < g.current_step → ∀ p n, g.node? p = some n → p.id.step = j → a ∈ n.owners →
      ∃ p' n', g.node? p' = some n' ∧ p'.id.step = g.current_step - 1 ∧ a ∈ n'.owners := by
  intro fuel
  induction fuel with
  | zero =>
    intro j hf _ hjhi p n hn hps ha
    exact ⟨p, n, hn, by omega, ha⟩
  | succ fuel ih =>
    intro j hf hjlo hjhi p n hn hps ha
    if htop : j = g.current_step - 1 then
      exact ⟨p, n, hn, by omega, ha⟩
    else
      obtain ⟨c, _, m, hm, hmown, hcstep⟩ :=
        hop_up g ctx p n hn (by omega) (by omega) a ha halo hahi
      exact ih (j + 1) (by omega) (by omega) (by omega) c m hm (by omega) hmown

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
      ∃ sel', TPart g a sel' 0 hi ∧ sel' hi = sel hi := by
  intro fuel
  induction fuel with
  | zero =>
    intro sel lo hi hm hlo hlohi _ hpc
    have : lo = 0 := by omega
    subst this; exact ⟨sel, hpc, rfl⟩
  | succ fuel ih =>
    intro sel lo hi hm hlo hlohi hhi hpc
    if hpos : 0 < lo then
      obtain ⟨c, hpc'⟩ := step_down_T g ctx a halo hahi sel lo hi hpos hlohi hhi hpc
      obtain ⟨sel', hT, hEq⟩ :=
        ih _ (lo - 1) hi (by omega) (by omega) (by omega) hhi hpc'
      exact ⟨sel', hT, hEq.trans (upd_other sel (lo - 1) c (by omega))⟩
    else
      have : lo = 0 := by omega
      subst this; exact ⟨sel, hpc, rfl⟩

/-- **Every node has a threaded past.** From step 0 up to the anchor's own step
there is a parent-linked path *all of whose nodes own the anchor*.

This is strictly between v27 and `PairwiseOwned`: v27's path says nothing about
ownership, `PairwiseOwned` asks every pair to co-own, and this asks every node
of the path to own **one** common node. Unlike `PairwiseOwned`, it is a
theorem — the arc-consistency clause `coherent_parents` pays for it. -/
theorem threaded_below (g : GPathM) (ctx : TCtx g) (a : PathNodeId) (n : PNodeM)
    (hn : g.node? a = some n) (hself : a ∈ n.owners)
    (halo : 0 ≤ a.id.step) (hahi : a.id.step < g.current_step) :
    ∃ sel, TPart g a sel 0 a.id.step ∧ sel a.id.step = a := by
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
  sabove := Sons.SAbove_reachable_filterAll reqOf g reqs hreach
  sn := Sons.SN_reachable_filterAll reqOf g reqs hreach
  pms := Sons.PMS_reachable_filterAll reqOf g reqs hreach
  ownerNode := fun pid n hn q hq hlo hhi =>
    Candidates.owner_is_node _ hv
      (GownersNodes.GN_filterAll g reqs (GownersNodes.GN_reachable reqOf g hreach))
      pid n hn q hq hlo hhi

/-- **Every node of a state the machine holds has a threaded past.** The
self-ownership comes from v30, so the anchor really is on its own path. -/
theorem threaded_below_filterAll (g : GPathM) (reqs : List NodeId)
    (hreach : Reachable reqOf g) (hv : isValid (filterAll g reqs) = true)
    (a : PathNodeId) (n : PNodeM) (hn : (filterAll g reqs).node? a = some n)
    (halo : 0 ≤ a.id.step) (hahi : a.id.step < (filterAll g reqs).current_step) :
    ∃ sel, TPart (filterAll g reqs) a sel 0 a.id.step ∧ sel a.id.step = a :=
  threaded_below _ (tctx_filterAll reqOf g reqs hreach hv) a n hn
    (SelfOwn.SelfOwned_filterAll reqOf g reqs hreach hv a n hn) halo hahi

/-- info: 'AbsSat.GraphPath.Model.Threaded.threaded_below_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms threaded_below_filterAll


-- ============================================================
-- The full threading theorem
-- ============================================================

/-- **Every node above step 0 lies on a full path that owns it.** Climb to the
top with `hop_up`, then descend with `hop_down`: the descent is what supplies
the parent links, and both directions preserve the anchor.

This is the statement v41 was one invariant short of. What it is *not* is
`PairwiseOwned`: the path's nodes all own `a`, and say nothing about owning
each other.

The hypothesis `1 ≤ a.id.step` is the one thing left. `reviewSons` sweeps
steps `1 .. current_step-2`, so `coherent_sons` is silent at step 0 and the
climb cannot start there. Closing it needs either that sweep extended, or the
*other* son-table mirror — every son has the node as a parent — which is a
different invariant from `Sons.SAbove` and would take the induction
`Sons.SMP` took. -/
theorem threaded (g : GPathM) (ctx : TCtx g) (a : PathNodeId) (n : PNodeM)
    (hn : g.node? a = some n) (hself : a ∈ n.owners)
    (halo : 0 ≤ a.id.step) (hahi : a.id.step < g.current_step) :
    ∃ sel, IsChain g sel ∧
      ∀ i, 0 ≤ i → i < g.current_step → a ∈ ownersOf g (sel i) := by
  obtain ⟨t, nt, hnt, htstep, htown⟩ :
      ∃ t nt, g.node? t = some nt ∧ t.id.step = g.current_step - 1 ∧ a ∈ nt.owners := by
    if hz : a.id.step = 0 then
      if htp : (0 : Int) = g.current_step - 1 then
        exact ⟨a, n, hn, by rw [hz]; exact htp, hself⟩
      else
        obtain ⟨c, m, hm, hmu, hcs⟩ := hop_up_zero g ctx a n hn hz (by omega)
        exact climb g ctx a halo hahi (g.current_step - 1 - 1).toNat 1
          (Nat.le_refl _) (Int.le_refl _) (by omega) c m hm hcs hmu
    else
      exact climb g ctx a halo hahi (g.current_step - 1 - a.id.step).toNat a.id.step
        (Nat.le_refl _) (by omega) hahi a n hn rfl hself
  have hseed : TPart g a (fun _ => t) (g.current_step - 1) (g.current_step - 1) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi1 hi2
      have : i = g.current_step - 1 := by omega
      subst this
      exact ⟨Option.isSome_iff_exists.mpr ⟨nt, hnt⟩, htstep⟩
    · intro i hi1 hi2; omega
    · intro i hi1 hi2
      have : i = g.current_step - 1 := by omega
      subst this
      simpa only [ownersOf, hnt] using htown
  obtain ⟨sel, hpc, _⟩ :=
    descend_T g ctx a (by omega) hahi (g.current_step - 1).toNat (fun _ => t)
      (g.current_step - 1) (g.current_step - 1) (Nat.le_refl _) (by omega) (Int.le_refl _)
      (by omega) hseed
  exact ⟨sel, isChain_of_partial g sel hpc.chain,
    fun i hi1 hi2 => hpc.owns i hi1 (by omega)⟩

/-- The same on the machine's own states. -/
theorem threaded_filterAll (g : GPathM) (reqs : List NodeId) (hreach : Reachable reqOf g)
    (hv : isValid (filterAll g reqs) = true)
    (a : PathNodeId) (n : PNodeM) (hn : (filterAll g reqs).node? a = some n)
    (halo : 0 ≤ a.id.step) (hahi : a.id.step < (filterAll g reqs).current_step) :
    ∃ sel, IsChain (filterAll g reqs) sel ∧
      ∀ i, 0 ≤ i → i < (filterAll g reqs).current_step →
        a ∈ ownersOf (filterAll g reqs) (sel i) :=
  threaded _ (tctx_filterAll reqOf g reqs hreach hv) a n hn
    (SelfOwn.SelfOwned_filterAll reqOf g reqs hreach hv a n hn) halo hahi

/-- info: 'AbsSat.GraphPath.Model.Threaded.threaded_filterAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms threaded_filterAll


-- ============================================================
-- Where a node's support below it actually lives
-- ============================================================

/-- **Every owner below a node lies on a descent from it.** Given `v` among
`p`'s owners at a lower step, there is a parent-linked chain from step 0 up to
`p`, whose top *is* `p`, all of whose nodes own `v` — and whose node at `v`'s
own step **is `v` itself**, because `OOS` leaves a node no other owner there.

So the support of a node below it is a set of its **ancestors**, reached by
chains that carry the owner all the way. Together with v39's bridge — every
parent is an owner — this sandwiches the owners table:

    parents(p) ⊆ owners(p) at step-1        (the bridge, v39)
    owners(p) at l ⊆ ancestors of p at l    (here)

and v40's refuted transitivity says neither inclusion is an equality: a
grandparent need not be an owner. -/
theorem owner_below_on_descent (g : GPathM) (ctx : TCtx g) (hoos : SelfOwn.OOS g)
    (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n)
    (hplo : 0 ≤ p.id.step) (hphi : p.id.step < g.current_step)
    (v : PathNodeId) (hv : v ∈ n.owners) (hvlo : 0 ≤ v.id.step)
    (hvle : v.id.step ≤ p.id.step) :
    ∃ sel, TPart g v sel 0 p.id.step ∧ sel p.id.step = p ∧ sel v.id.step = v := by
  have hvhi : v.id.step < g.current_step := by omega
  have hseed : TPart g v (fun _ => p) p.id.step p.id.step := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi1 hi2
      have : i = p.id.step := by omega
      subst this
      exact ⟨Option.isSome_iff_exists.mpr ⟨n, hn⟩, rfl⟩
    · intro i hi1 hi2; omega
    · intro i hi1 hi2
      have : i = p.id.step := by omega
      subst this
      simpa only [ownersOf, hn] using hv
  obtain ⟨sel, hT, hEq⟩ :=
    descend_T g ctx v hvlo hvhi p.id.step.toNat (fun _ => p) p.id.step p.id.step
      (Nat.le_refl _) hplo (Int.le_refl _) hphi hseed
  refine ⟨sel, hT, hEq, ?_⟩
  obtain ⟨hs, hstep⟩ := hT.chain.1 v.id.step hvlo hvle
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
  have hown := hT.owns v.id.step hvlo hvle
  simp only [ownersOf, hm] at hown
  have hmid : m.id = sel v.id.step := node?_id_eq g _ m hm
  have hvm : v = m.id := hoos m (List.mem_of_find?_eq_some hm) v hown (by rw [hmid, hstep])
  exact (hvm.trans hmid).symm

/-- info: 'AbsSat.GraphPath.Model.Threaded.owner_below_on_descent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms owner_below_on_descent

end AbsSat.GraphPath.Model.Threaded
