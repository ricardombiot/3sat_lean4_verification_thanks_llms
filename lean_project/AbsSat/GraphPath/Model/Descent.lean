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
open AbsSat.GraphPath.Model.AdjacentOwners (Adj owners_below_iff_parents owners_above_iff_sons
  mem_union_of_coherent)
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

-- ============================================================
-- Where the descent really breaks: the multiplicity of the tables
-- ============================================================

/-- **Un owner de `x` lo posee ya algún padre de `x`** — y esto sale de la *coherencia del punto
fijo* (`cohP`), no de la consistencia de pares. La revisión deja la tabla de un nodo contenida en
la unión de las de sus padres, así que todo lo que `x` posee lo posee alguno de ellos. -/
theorem parent_owns_of_coherent (g : GPathM) (a : Adj g) {x : PathNodeId} {n : PNodeM}
    (hx : g.node? x = some n) (hx1 : 1 ≤ x.id.step) (hxs : x.id.step < g.current_step)
    (v : PathNodeId) (hv : v ∈ n.owners) (hv0 : 0 ≤ v.id.step) (hv1 : v.id.step < g.current_step) :
    ∃ c ∈ n.parents, ∃ m, g.node? c = some m ∧ v ∈ m.owners := by
  have hcoh := a.cohP _ (mem_intRange hx1 (by omega)) x
    (Threaded.mem_line_of_node? g x n hx) n hx
  exact mem_union_of_coherent g n.parents n.owners v hcoh hv
    (ParentWitness.union_entry_below a hx hx1 v.id.step hv0 hv1)

/-- **Y si en ese paso la tabla de `x` tiene un solo owner, lo poseen *todos* sus padres.**

Un padre `c` de `x` tiene a `x` en su propia tabla (`owners_above_iff_sons`), así que la criba del
autor exige que `c` y `x` compartan un owner en cada paso. En el paso `j` ese owner común está en
la tabla de `x`; si ahí no hay más que `v`, es `v`, y entonces `v` está también en la de `c`.

**Esto es donde el descenso se rompe de verdad.** El descenso necesita *un* padre que posea a
todos los picks; lo único que se lo impide es que las tablas tengan **más de un candidato por
paso**. Donde la revisión ha dejado la tabla decidida, no hay nada que elegir.

Ni siquiera hace falta suponer `v ∈ n.owners`: la validez ya pone una entrada en el paso `j`, y
`huniq` la identifica con `v`. -/
theorem parents_own_unique_owner (g : GPathM) (a : Adj g) (hok : AggOk g) (hsmp : Sons.SMP g)
    {x : PathNodeId} {n : PNodeM} (hx : g.node? x = some n)
    (hx1 : 1 ≤ x.id.step) (hxs : x.id.step < g.current_step)
    (j : Int) (hj0 : 0 ≤ j) (hj1 : j < g.current_step)
    (v : PathNodeId) (huniq : ∀ w ∈ n.owners, w.id.step = j → w = v)
    (c : PathNodeId) (hc : c ∈ n.parents) (mc : PNodeM) (hmc : g.node? c = some mc) :
    v ∈ mc.owners := by
  have hid := node?_id_eq g x n hx
  have hcstep : c.id.step = x.id.step - 1 := by
    have := a.rc.shape.pbelow n (List.mem_of_find?_eq_some hx) c hc
    rw [hid] at this; exact this
  -- `x` está en la tabla de su padre: un owner un paso por encima es un hijo
  have hxson : x ∈ mc.sons := by
    have := hsmp n (List.mem_of_find?_eq_some hx) c hc mc (List.mem_of_find?_eq_some hmc)
      (node?_id_eq g c mc hmc)
    rwa [hid] at this
  have hxc : x ∈ mc.owners := (a.links c mc hmc).2 x hxson
  -- la criba da un owner común en el paso `j`, y la unicidad lo identifica con `v`
  obtain ⟨z, hzc, hzx, hzs⟩ := ParentWitness.shared_owner a hok hmc hx
    (by omega) (by omega) (by omega) hxs hxc j hj0 hj1
  rw [← huniq z hzx hzs]
  exact hzc

/-- **Two parents of the same node never own each other.** They sit at the same step, and an owner
at a node's own step *is* that node (`OOS`), so if one owned the other they would be equal.

The consequence is about the filter, not about the parents: `aggPair` only ever tests a pair
`(x, w)` with `w` already in `x`'s table, so **no sweep ever compares two parents of a node**. The
ambiguity the in-degree measures is invisible to both legs of the aggressive review. -/
theorem parents_never_own_each_other (g : GPathM) (a : Adj g) {x : PathNodeId} {n : PNodeM}
    (hx : g.node? x = some n)
    {c c' : PathNodeId} (hc : c ∈ n.parents) (hc' : c' ∈ n.parents) (hne : c ≠ c')
    {mc : PNodeM} (hmc : g.node? c = some mc) : c' ∉ mc.owners := by
  intro hown
  have hmem := List.mem_of_find?_eq_some hx
  have hid := node?_id_eq g x n hx
  have hcs : c.id.step = x.id.step - 1 := by
    have := a.rc.shape.pbelow n hmem c hc; rw [hid] at this; exact this
  have hcs' : c'.id.step = x.id.step - 1 := by
    have := a.rc.shape.pbelow n hmem c' hc'; rw [hid] at this; exact this
  have hmcid := node?_id_eq g c mc hmc
  exact hne (((a.rc.oos mc (List.mem_of_find?_eq_some hmc) c' hown
    (by rw [hmcid]; omega)).trans hmcid).symm)

/-- **What the descent really asks of a node**: among its parents there is one that *every* pick
owning the node owns too.

`SingleParents` supplies it for a trivial reason — there is only one parent to choose. But the
descent never needed uniqueness: it needs the choice to be makeable **once, for all the picks above
at the same time**. That is strictly less, and it is exactly what `CommonOwner` consumes. -/
def ParentMeet (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → 1 ≤ x.id.step → x.id.step < g.current_step →
    ∃ c ∈ n.parents, ∀ y m, g.node? y = some m → x.id.step ≤ y.id.step →
      y.id.step < g.current_step → y ∈ n.owners → c ∈ m.owners

/-! **Measured (probe `row-degree pm`, 2026-09-22): `ParentMeet` is FALSE.** It does hold far more
often than `SingleParents` — 71% to 78% of the nodes with two parents pass it, against 0% for
`ParentMeetAll` — but it fails: 18 nodes of 635, and 4 of 229.

**And every failure is spurious.** Pulling, for each parent, the owner above that does *not* carry
it, the witnesses came out **mutually incompatible in all 22 cases**: neither owns the other, so no
single chain can pick both, and the failure says nothing against `CommonOwner`.

Restricting the quantifier to owners that *can* share a chain is therefore the right statement — and
it is `CommonOwner` itself (`commonOwner_gives_parent`). Between `SingleParents` and the goal there
is no room for a statement of this shape. -/

/-- The same demand with the owners *below* the node included. **Measured (2026-09-22): it fails on
every node with two parents, without exception** — and it must, by `parents_never_own_each_other`:
the other parent is itself an owner of the node, and no parent lives in another parent's table. So
`ParentMeetAll` is `SingleParents` in disguise (`singleParent_of_parentMeetAll`), and the bound
`x.id.step ≤ y.id.step` in `ParentMeet` is not a convenience — it is what keeps the statement from
collapsing. The descent only ever asks about the picks **above** the node anyway. -/
def ParentMeetAll (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → 1 ≤ x.id.step → x.id.step < g.current_step →
    ∃ c ∈ n.parents, ∀ y m, g.node? y = some m → 0 ≤ y.id.step → y.id.step < g.current_step →
      y ∈ n.owners → c ∈ m.owners

/-- **Asking it of the owners below collapses it to `SingleParents`.** If a node had two parents, one
of them differs from the meeting parent `c`; it is an owner of the node and a node itself, so `c`
would have to sit in its table — which `parents_never_own_each_other` forbids. -/
theorem singleParent_of_parentMeetAll (g : GPathM) (a : Adj g) (hpm : ParentMeetAll g)
    {x : PathNodeId} {n : PNodeM} (hx : g.node? x = some n) (hx1 : 1 ≤ x.id.step)
    (hxs : x.id.step < g.current_step) : ∀ c ∈ n.parents, ∀ c' ∈ n.parents, c = c' := by
  have hmem := List.mem_of_find?_eq_some hx
  have hid := node?_id_eq g x n hx
  obtain ⟨cs, hcs, hall⟩ := hpm x n hx hx1 hxs
  have hcss : cs.id.step = x.id.step - 1 := by
    have := a.rc.shape.pbelow n hmem cs hcs; rw [hid] at this; exact this
  have key : ∀ y ∈ n.parents, y = cs := by
    intro y hy
    obtain ⟨my, hmy, hmyid⟩ := a.rc.shape.pn n hmem y hy
    have hynode : g.node? y = some my := by rw [← hmyid]; exact node?_of_mem a.rc.nodup my hmy
    have hys : y.id.step = x.id.step - 1 := by
      have := a.rc.shape.pbelow n hmem y hy; rw [hid] at this; exact this
    have hyo : y ∈ n.owners := (owners_below_iff_parents g a x n hx hx1 y hys).mpr hy
    have hin := hall y my hynode (by omega) (by omega) hyo
    have hmyid2 := node?_id_eq g y my hynode
    exact ((a.rc.oos my (List.mem_of_find?_eq_some hynode) cs hin
      (by rw [hmyid2]; omega)).trans hmyid2).symm
  intro c hc c' hc'
  rw [key c hc, key c' hc']

/-- **And it is enough.** No sweep, no `AggOk`: the meeting parent is handed to every pick above
directly. -/
theorem commonOwner_of_parentMeet (g : GPathM) (a : Adj g) (hpm : ParentMeet g) : CommonOwner g := by
  intro sel lo hlo0 hlo hs
  obtain ⟨hsome, hstep⟩ := hs.node lo (Int.le_refl _) (by omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = sel lo := node?_id_eq g _ n hn
  obtain ⟨c, hc, hcall⟩ := hpm (sel lo) n hn (by rw [hstep]; omega) (by rw [hstep]; omega)
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
  · obtain ⟨hksome, hkstep⟩ := hs.node k hk0 hk1
    obtain ⟨nk, hnk⟩ := Option.isSome_iff_exists.mp hksome
    have hkx : sel k ∈ n.owners := by
      have h := hs.owned k lo hk0 (Int.le_refl _) hk1 (by omega) hne
      have h' := (List.mem_filter.mp h).1
      simpa only [ownersOf, hn] using h'
    simpa only [ownersOf, hnk] using
      hcall (sel k) nk hnk (by rw [hkstep, hstep]; omega) (by rw [hkstep]; exact hk1) hkx

/-- **The node `CommonOwner` hands over is always a parent of the pick it sits under.** An owner one
step below a node is a parent of it, and `CommonOwner`'s witness is owned by `sel lo` itself.

So the clique-restricted `ParentMeet` — quantified only over owners that could be picks of one
chain — *is* `CommonOwner`, and the two ends of the interval are `SingleParents` on one side
(`ParentMeetAll`, `singleParent_of_parentMeetAll`) and the goal on the other. -/
theorem commonOwner_gives_parent (g : GPathM) (a : Adj g) (h : CommonOwner g)
    (sel : Int → PathNodeId) (lo : Int) (hlo0 : 0 < lo) (hlo : lo ≤ g.current_step - 1)
    (hs : SoundFrom g sel lo) :
    ∃ c nc n, g.node? (sel lo) = some n ∧ c ∈ n.parents ∧ g.node? c = some nc ∧
      ∀ k, lo ≤ k → k < g.current_step → c ∈ ownersOf g (sel k) := by
  obtain ⟨c, nc, hcnode, hcstep, hall⟩ := h sel lo hlo0 hlo hs
  obtain ⟨hsome, hstep⟩ := hs.node lo (Int.le_refl _) (by omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hco : c ∈ n.owners := by
    have := hall lo (Int.le_refl _) (by omega)
    simpa only [ownersOf, hn] using this
  exact ⟨c, nc, n, hn, (owners_below_iff_parents g a (sel lo) n hn (by rw [hstep]; omega) c
    (by rw [hcstep, hstep])).mp hco, hcnode, hall⟩

/-- **At most two parents per node.** Any three parents of a node have two equal. Measured: the
in-degree never exceeded 2 on any state of any run of the corpus. -/
def TwoParents (g : GPathM) : Prop :=
  ∀ n ∈ g.nodes, ∀ c ∈ n.parents, ∀ c' ∈ n.parents, ∀ c'' ∈ n.parents,
    c = c' ∨ c = c'' ∨ c' = c''

/-- **The witness hypothesis.** Two owners of a node, both at or above its step, **that own each
other**, share a parent of the node.

This is what the 375 measured failures of `ParentMeet` all had in common: the two witnesses never
owned each other. It is a statement about *one node and two of its owners* — pairwise, where
`CommonOwner` is `k`-wise. -/
def PairMeet (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → 1 ≤ x.id.step → x.id.step < g.current_step →
    ∀ u mu v mv, g.node? u = some mu → g.node? v = some mv →
      x.id.step ≤ u.id.step → u.id.step < g.current_step →
      x.id.step ≤ v.id.step → v.id.step < g.current_step →
      u ∈ n.owners → v ∈ n.owners → v ∈ mu.owners → u ∈ mv.owners →
      ∃ c ∈ n.parents, c ∈ mu.owners ∧ c ∈ mv.owners

/-- **Pairwise is enough when there are only two parents.** The sets `parents(n) ∩ owners(sel k)`
are non-empty (the sweep's pair consistency) and live in a two-element ground set, so `PairMeet`'s
pairwise intersections force a common element — Helly with Helly number two.

Concretely: look for a pick above that does **not** own the first parent. If there is none, that
parent is the common owner. If there is one, the non-emptiness gives it the *other* parent `c₂`, and
for every further pick `PairMeet` hands a parent owned by both, which `TwoParents` identifies with
`c₂`. -/
theorem commonOwner_of_pairMeet (g : GPathM) (a : Adj g) (hok : AggOk g)
    (htp : TwoParents g) (hpm : PairMeet g) : CommonOwner g := by
  intro sel lo hlo0 hlo hs
  obtain ⟨hsome, hstep⟩ := hs.node lo (Int.le_refl _) (by omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = sel lo := node?_id_eq g _ n hn
  have hlo1 : 1 ≤ (sel lo).id.step := by rw [hstep]; omega
  have hlos : (sel lo).id.step < g.current_step := by rw [hstep]; omega
  -- every pick above is a node, and an owner of `n`
  have hnode : ∀ k, lo ≤ k → k < g.current_step →
      ∃ m, g.node? (sel k) = some m ∧ (sel k).id.step = k := by
    intro k hk0 hk1
    obtain ⟨hks, hkst⟩ := hs.node k hk0 hk1
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hks
    exact ⟨m, hm, hkst⟩
  have howned : ∀ k, lo ≤ k → k < g.current_step → sel k ∈ n.owners := by
    intro k hk0 hk1
    rcases int_eq_or_ne k lo with rfl | hne
    · simpa only [ownersOf, hn] using hs.self_owned k hk0 hk1
    · have h := hs.owned k lo hk0 (Int.le_refl _) hk1 (by omega) hne
      simpa only [ownersOf, hn] using (List.mem_filter.mp h).1
  -- and each pick owns at least one parent of `n`
  have hsome_parent : ∀ k, lo ≤ k → k < g.current_step → ∀ m, g.node? (sel k) = some m →
      ∃ c ∈ n.parents, c ∈ m.owners := by
    intro k hk0 hk1 m hm
    obtain ⟨_, hkst⟩ := hs.node k hk0 hk1
    obtain ⟨w, hwn, hwm, hws⟩ := ParentWitness.shared_owner a hok hn hm (by omega) hlos
      (by rw [hkst]; omega) (by rw [hkst]; exact hk1) (howned k hk0 hk1)
      ((sel lo).id.step - 1) (by omega) (by omega)
    exact ⟨w, (owners_below_iff_parents g a (sel lo) n hn hlo1 w hws).mp hwn, hwm⟩
  -- a parent to start from
  have hroot : n.id.parent_id.isNone = false := by
    have hnr := a.rc.shape.notroot n hmem (by rw [hid]; omega)
    cases hp : n.id.parent_id with
    | none => exact absurd hp hnr
    | some _ => rfl
  obtain ⟨c₁, hc₁⟩ := List.exists_mem_of_ne_nil _
    (SelfOwn.have_parents_of_isValidNode g n (a.ctx.nodeval (sel lo) n hn) hroot)
  have hnc : ∀ c, c ∈ n.parents → ∃ nc, g.node? c = some nc ∧ c.id.step = lo - 1 := by
    intro c hc
    obtain ⟨mc, hmc, hmcid⟩ := a.rc.shape.pn n hmem c hc
    refine ⟨mc, by rw [← hmcid]; exact node?_of_mem a.rc.nodup mc hmc, ?_⟩
    have := a.rc.shape.pbelow n hmem c hc
    rw [hid, hstep] at this; omega
  -- is there a pick above that does not own `c₁`?
  cases hf : (intRange lo (g.current_step - 1)).find?
      (fun k => !(ownersOf g (sel k)).contains c₁) with
  | none =>
    obtain ⟨nc, hncd, hncs⟩ := hnc c₁ hc₁
    refine ⟨c₁, nc, hncd, hncs, fun k hk0 hk1 => ?_⟩
    have := List.find?_eq_none.mp hf k (mem_intRange hk0 (by omega))
    simp only [Bool.not_eq_true', Bool.not_eq_false] at this
    exact List.mem_of_elem_eq_true this
  | some aa =>
    have haaR : aa ∈ intRange lo (g.current_step - 1) := List.mem_of_find?_eq_some hf
    have haa0 : lo ≤ aa := mem_intRange_lower haaR
    have haa1 : aa < g.current_step := by have := mem_intRange_upper haaR; omega
    have hbad : c₁ ∉ ownersOf g (sel aa) := by
      have h0 := List.find?_some hf
      simpa using h0
    obtain ⟨ma, hma, _⟩ := hnode aa haa0 haa1
    obtain ⟨c₂, hc₂, hc₂a⟩ := hsome_parent aa haa0 haa1 ma hma
    have hne : c₂ ≠ c₁ := by
      intro h; rw [h] at hc₂a; exact hbad (by simpa only [ownersOf, hma] using hc₂a)
    obtain ⟨nc, hncd, hncs⟩ := hnc c₂ hc₂
    refine ⟨c₂, nc, hncd, hncs, fun k hk0 hk1 => ?_⟩
    obtain ⟨mk, hmk, hkst⟩ := hnode k hk0 hk1
    rcases int_eq_or_ne k aa with rfl | hka
    · simpa only [ownersOf, hma] using hc₂a
    · -- the pair `(sel aa, sel k)` owns each other, so `PairMeet` gives a shared parent
      obtain ⟨_, hast⟩ := hs.node aa haa0 haa1
      have huv : sel k ∈ ma.owners := by
        have h := hs.owned k aa hk0 haa0 hk1 haa1 hka
        simpa only [ownersOf, hma] using (List.mem_filter.mp h).1
      have hvu : sel aa ∈ mk.owners := by
        have h := hs.owned aa k haa0 hk0 haa1 hk1 (fun hc => hka hc.symm)
        simpa only [ownersOf, hmk] using (List.mem_filter.mp h).1
      obtain ⟨c, hc, hca, hck⟩ := hpm (sel lo) n hn hlo1 hlos (sel aa) ma (sel k) mk hma hmk
        (by rw [hast, hstep]; omega) (by rw [hast]; exact haa1)
        (by rw [hkst, hstep]; omega) (by rw [hkst]; exact hk1)
        (howned aa haa0 haa1) (howned k hk0 hk1) huv hvu
      have hcc : c = c₂ := by
        rcases htp n hmem c hc c₁ hc₁ c₂ hc₂ with h | h | h
        · exact absurd (by rw [← h]; simpa only [ownersOf, hma] using hca) hbad
        · exact h
        · exact absurd h.symm hne
      rw [hcc] at hck
      simpa only [ownersOf, hmk] using hck

/-- **One parent per node gives the meeting for free.** The sweep's pair consistency hands, for each
pick above, a common owner one step below the node; an owner exactly one step below **is** a parent
(`owners_below_iff_parents`), and `SingleParent` identifies every one of those witnesses with the
same `c`. -/
theorem parentMeet_of_singleParents (g : GPathM) (a : Adj g) (hok : AggOk g)
    (hsp : ParentWitness.SingleParents g) : ParentMeet g := by
  intro x n hx hx1 hxs
  have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hx
  have hid : n.id = x := node?_id_eq g x n hx
  have hroot : n.id.parent_id.isNone = false := by
    have hnr := a.rc.shape.notroot n hmem (by rw [hid]; omega)
    cases hp : n.id.parent_id with
    | none => exact absurd hp hnr
    | some _ => rfl
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _
    (SelfOwn.have_parents_of_isValidNode g n (a.ctx.nodeval x n hx) hroot)
  refine ⟨c, hc, fun y m hy hyx hys hyn => ?_⟩
  obtain ⟨w, hwn, hwy, hws⟩ := ParentWitness.shared_owner a hok hx hy (by omega) hxs
    (by omega) hys hyn
    (x.id.step - 1) (by omega) (by omega)
  have hwp : w ∈ n.parents :=
    (owners_below_iff_parents g a x n hx hx1 w hws).mp hwn
  rw [← hsp n hmem w hwp c hc]
  exact hwy

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
    (hsp : ParentWitness.SingleParents g) : CommonOwner g :=
  commonOwner_of_parentMeet g a (parentMeet_of_singleParents g a hok hsp)

/-- `SingleParents` is the degenerate case of both new hypotheses. -/
theorem twoParents_of_singleParents (g : GPathM) (hsp : ParentWitness.SingleParents g) :
    TwoParents g := fun n hn c hc c' hc' _ _ => Or.inl (hsp n hn c hc c' hc')

theorem pairMeet_of_singleParents (g : GPathM) (a : Adj g) (hok : AggOk g)
    (hsp : ParentWitness.SingleParents g) : PairMeet g := by
  intro x n hx hx1 hxs u mu v mv hu hv hux hus hvx hvs hun hvn _ _
  obtain ⟨c, hc, hall⟩ := parentMeet_of_singleParents g a hok hsp x n hx hx1 hxs
  exact ⟨c, hc, hall u mu hu hux hus hun, hall v mv hv hvx hvs hvn⟩

/-- info: 'AbsSat.GraphPath.Model.Descent.parent_owns_of_coherent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parent_owns_of_coherent

/-- info: 'AbsSat.GraphPath.Model.Descent.parents_own_unique_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parents_own_unique_owner

/-- info: 'AbsSat.GraphPath.Model.Descent.commonOwner_of_singleParents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms commonOwner_of_singleParents

/-- info: 'AbsSat.GraphPath.Model.Descent.parents_never_own_each_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parents_never_own_each_other

/-- info: 'AbsSat.GraphPath.Model.Descent.commonOwner_of_parentMeet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms commonOwner_of_parentMeet

/-- info: 'AbsSat.GraphPath.Model.Descent.singleParent_of_parentMeetAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms singleParent_of_parentMeetAll

/-- info: 'AbsSat.GraphPath.Model.Descent.commonOwner_gives_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms commonOwner_gives_parent

/-- info: 'AbsSat.GraphPath.Model.Descent.commonOwner_of_pairMeet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms commonOwner_of_pairMeet

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
