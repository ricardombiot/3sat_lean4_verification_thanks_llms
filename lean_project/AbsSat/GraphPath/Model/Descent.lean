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

/-- **Lo que el descenso consume, exactamente: que el padre no haya que elegirlo.**

Para todo nodo `x` y todo owner suyo `v` **a su altura o por encima**, *todos* los padres de `x`
tienen a `v` en su tabla.

Es la forma precisa de la intuición *«al lector siempre le queda un camino de owners por el que
bajar»*. Dice justo lo que hace falta y nada más: si todo padre posee a todo owner de arriba, el
descenso no tiene nada que elegir, y por eso **no acota el in-degree** — ni `SingleParents`, ni
`TwoParents`, ni `PairMeet`, que son todas maneras de acotar cuántos padres hay para no tener que
decidir entre ellos. Aquí sobra decidir.

Y la cota `x.id.step ≤ v.id.step` es la que evita el colapso de §5.16: los padres de `x` viven
**por debajo** de `x`, así que quedan fuera del cuantificador y `parents_never_own_each_other` no
lo convierte en padre único, que es lo que mató a `ParentMeetAll`. -/
def AllParentsOwn (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → 1 ≤ x.id.step → x.id.step < g.current_step →
    ∀ v ∈ n.owners, x.id.step ≤ v.id.step → v.id.step < g.current_step →
      ∀ c ∈ n.parents, ∀ mc, g.node? c = some mc → v ∈ mc.owners

/-- **La tabla decidida por encima.** En todo nodo, y en todo paso a su altura o por encima, la
tabla tiene como mucho una entrada. Es el caso que `parents_own_unique_owner` cubre: donde la
revisión dejó la tabla decidida, no hay nada que elegir. -/
def DecidedAbove (g : GPathM) : Prop :=
  ∀ x n, g.node? x = some n → ∀ w ∈ n.owners, ∀ w' ∈ n.owners,
    x.id.step ≤ w.id.step → w.id.step = w'.id.step → w = w'

/-- **Decidida ⟹ todos los padres poseen.** Es `parents_own_unique_owner` leído con la unicidad
puesta por hipótesis en vez de comprobada paso a paso. -/
theorem allParentsOwn_of_decided (g : GPathM) (a : Adj g) (hok : AggOk g) (hsmp : Sons.SMP g)
    (hdec : DecidedAbove g) : AllParentsOwn g := by
  intro x n hx hx1 hxs v hv hv0 hv1 c hc mc hmc
  exact parents_own_unique_owner g a hok hsmp hx hx1 hxs v.id.step (by omega) hv1 v
    (fun w hw hws => (hdec x n hx v hv w hw hv0 hws.symm).symm) c hc mc hmc

/-- **La intuición, demostrada: si el padre no hay que elegirlo, el descenso baja.**

El padre lo regala la coherencia del punto fijo (`parent_owns_of_coherent`), `AllParentsOwn` pone
cada pick en su tabla, y la simetría de `AggOk` lo devuelve a la tabla del pick, que es la forma en
que `CommonOwner` lo pide. Sale **sin acotar el in-degree**: un nodo puede tener cuatro padres y el
descenso baja igual.

Lo que esto localiza: el obstáculo abierto nunca fue la multiplicidad de los **padres** —contra lo
que suponían `SingleParents`, `TwoParents` y `PairMeet`— sino la de las **tablas**. Un nodo con
cuatro padres no estorba; un owner que solo una rama posee, sí. -/
theorem commonOwner_of_allParentsOwn (g : GPathM) (a : Adj g) (hok : AggOk g)
    (hap : AllParentsOwn g) : CommonOwner g := by
  intro sel lo hlo0 hlo hs
  obtain ⟨hsome, hstep⟩ := hs.node lo (Int.le_refl _) (by omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hid : n.id = sel lo := node?_id_eq g _ n hn
  have hx1 : 1 ≤ (sel lo).id.step := by rw [hstep]; omega
  have hxs : (sel lo).id.step < g.current_step := by rw [hstep]; omega
  have hself : sel lo ∈ n.owners := by
    simpa only [ownersOf, hn] using hs.self_owned lo (Int.le_refl _) (by omega)
  -- un padre cualquiera: la coherencia del punto fijo lo regala
  obtain ⟨c, hc, mc, hcnode, _⟩ :=
    parent_owns_of_coherent g a hn hx1 hxs (sel lo) hself (by rw [hstep]; omega) hxs
  have hcstep : c.id.step = lo - 1 := by
    have := a.rc.shape.pbelow n (List.mem_of_find?_eq_some hn) c hc
    rw [hid, hstep] at this; omega
  refine ⟨c, mc, hcnode, hcstep, fun k hk0 hk1 => ?_⟩
  obtain ⟨hksome, hkstep⟩ := hs.node k hk0 hk1
  obtain ⟨nk, hnk⟩ := Option.isSome_iff_exists.mp hksome
  have hkx : sel k ∈ n.owners := by
    rcases int_eq_or_ne k lo with rfl | hne
    · exact hself
    · have h := hs.owned k lo hk0 (Int.le_refl _) hk1 (by omega) hne
      simpa only [ownersOf, hn] using (List.mem_filter.mp h).1
  -- todo padre posee al pick, en particular el que tenemos
  have hvk : sel k ∈ mc.owners :=
    hap (sel lo) n hn hx1 hxs (sel k) hkx (by rw [hstep, hkstep]; omega)
      (by rw [hkstep]; exact hk1) c hc mc hcnode
  -- y `AggOk` es simétrica: el padre está entonces en la tabla del pick
  have hsymc := (hok c mc (sel k) nk hcnode hnk (by rw [hcstep]; omega) (by rw [hcstep]; omega)
    (by rw [hkstep]; omega) (by rw [hkstep]; exact hk1) hvk
    (a.ctx.nodeval c mc hcnode) (a.ctx.nodeval (sel k) nk hnk)).1
  simpa only [ownersOf, hnk] using hsymc

/-- **El caso decidido, como composición.** -/
theorem commonOwner_of_decided (g : GPathM) (a : Adj g) (hok : AggOk g) (hsmp : Sons.SMP g)
    (hdec : DecidedAbove g) : CommonOwner g :=
  commonOwner_of_allParentsOwn g a hok (allParentsOwn_of_decided g a hok hsmp hdec)

/-- **Y `SingleParents` es el caso degenerado**: con un solo padre, el que la coherencia del punto
fijo devuelve *es* ese padre, así que «todos los padres poseen» es «alguno posee». Queda entonces la
escalera entera, y `AllParentsOwn` es el escalón de abajo:

```
SingleParents  ⟹  AllParentsOwn  ⟸  DecidedAbove
                        ⇓
                   CommonOwner  ⟹  NoDeadEnd  ⟹  el veredicto, y el lector no se atasca
```
-/
theorem allParentsOwn_of_singleParents (g : GPathM) (a : Adj g)
    (hsp : ParentWitness.SingleParents g) : AllParentsOwn g := by
  intro x n hx hx1 hxs v hv hv0 hv1 c hc mc hmc
  obtain ⟨c', hc', mc', hmc', hv'⟩ := parent_owns_of_coherent g a hx hx1 hxs v hv (by omega) hv1
  have : c' = c := hsp n (List.mem_of_find?_eq_some hx) c' hc' c hc
  subst this
  rw [hmc'] at hmc
  cases hmc
  exact hv'

-- ============================================================
-- De dónde puede salir `AllParentsOwn`: las tablas nacen cerradas
-- ============================================================

/-- **La tabla cerrada hacia abajo.** Si la tabla de un nodo contiene a `v`, contiene también a
todo padre de `v`.

Esto no es una conjetura sobre el algoritmo: es su diseño. `rowOwners` define la tabla de un nodo
de fila como la unión de las de sus padres recortada a `gowners`, así que contiene entera la de
**cada** padre (`owners_sub_rowOwners`). Y la tabla de un nodo contiene a sus propios padres
(`owners_below_iff_parents`). Compuesto: cuando `up` crea la fila nueva, la tabla que hereda ya
está cerrada hacia abajo si lo estaban las de sus padres — **nace cerrada**.

Lo único que puede romperla es la revisión, que quita: que la criba borre un padre de la tabla y
deje al hijo dentro. Eso deja la obligación en un enunciado sobre **una pasada de la criba**, que es
lo más local a lo que ha bajado esto. -/
def TableDownClosed (g : GPathM) : Prop :=
  ∀ r nr, g.node? r = some nr → ∀ v ∈ nr.owners, ∀ nv, g.node? v = some nv →
    ∀ c ∈ nv.parents, c ∈ nr.owners

/-- **El motor del diseño, dicho como lema**: la tabla de un nodo de fila contiene entera la de
cada uno de sus padres, recortada a lo que sigue globalmente vivo. Es `rowOwners` leído literal. -/
theorem owners_sub_rowOwners (g : GPathM) (d : NodeId) (pid r : PathNodeId) (nr : PNodeM)
    (hr : r ∈ rowParents g d pid) (hnr : g.node? r = some nr)
    (q : PathNodeId) (hq : q ∈ nr.owners) (hgq : g.gowners.contains q = true) :
    q ∈ rowOwners g d pid := by
  simp only [rowOwners, List.mem_append, List.mem_filter]
  exact Or.inl ⟨mem_unionOwnersOf g _ r nr q hr hnr hq, hgq⟩

/-- **Y la cerradura hacia abajo da la intuición.**

Dos pasos y los dos son simetría de `AggOk`: si `v` está en la tabla de `x`, entonces `x` está en la
de `v`; la tabla de `v` está cerrada hacia abajo, así que contiene a todo padre `c` de `x`; y de
vuelta, `v` está en la tabla de `c`. Que es `AllParentsOwn`.

Nótese el cambio de sitio del cuantificador: `AllParentsOwn` habla de **todos los padres de `x`** —
lo que suena fuerte— y `TableDownClosed` habla de **una tabla y los padres de lo que contiene** —
que es lo que `rowOwners` construye. Son la misma frase vista desde los dos lados de la simetría. -/
theorem allParentsOwn_of_tableDownClosed (g : GPathM) (a : Adj g) (hok : AggOk g)
    (hdc : TableDownClosed g) : AllParentsOwn g := by
  intro x n hx hx1 hxs v hv hv0 hv1 c hc mc hmc
  -- `v` es nodo: es owner de `x` en rango, luego owner global, luego nodo
  have hvg : v ∈ g.gowners := a.ctx.ownGow x n hx v hv (by omega) hv1
  obtain ⟨nv, hnv⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff g v).mp (a.rc.gn v hvg))
  have hcstep : c.id.step = x.id.step - 1 := by
    have := a.rc.shape.pbelow n (List.mem_of_find?_eq_some hx) c hc
    rwa [node?_id_eq g x n hx] at this
  -- simetría: `x` está en la tabla de `v`
  have hxv : x ∈ nv.owners :=
    (hok x n v nv hx hnv (by omega) hxs (by omega) hv1 hv
      (a.ctx.nodeval x n hx) (a.ctx.nodeval v nv hnv)).1
  -- la tabla de `v` está cerrada hacia abajo, luego contiene al padre
  have hcv : c ∈ nv.owners := hdc v nv hnv x hxv n hx c hc
  -- y de vuelta por simetría
  exact (hok v nv c mc hnv hmc (by omega) hv1 (by omega) (by omega) hcv
    (a.ctx.nodeval v nv hnv) (a.ctx.nodeval c mc hmc)).1

/-- **Y `TableDownClosed` colapsa: es `SingleParents`.**

Tómese la tabla de un padre `c` de `x`. Contiene a `x` —`owners_below_iff_parents` más la simetría
de `AggOk`—, así que la cerradura le mete dentro **todos** los padres de `x`. Y
`parents_never_own_each_other` dice que ningún padre de `x` vive en la tabla de otro. Luego no hay
más que uno.

**Cuarta vez que este repo tropieza con el mismo colapso**, y siempre por lo mismo: una hipótesis
que cuantifica sobre los owners de un nodo **sin excluir a sus padres** obliga a padre único. La
cota `x.id.step ≤ v.id.step` de `AllParentsOwn` es exactamente lo que la salva — `TableDownClosed`
no la tiene, y por eso cae donde `AllParentsOwn` sigue en pie.

Consecuencia práctica: `allParentsOwn_of_tableDownClosed` es cierto pero **no es una reducción** —
su hipótesis ya da `SingleParents`, que por `allParentsOwn_of_singleParents` da la conclusión sola.
La vía «las tablas nacen cerradas hacia abajo» queda cerrada, y la razón es que `rowOwners` cierra
la tabla hacia abajo **por rama**, no en total: un nodo viejo entra en la fila nueva por *una* de
sus ramas y no tiene por qué llevarse las otras. -/
theorem singleParent_of_tableDownClosed (g : GPathM) (a : Adj g) (hok : AggOk g)
    (hdc : TableDownClosed g) {x : PathNodeId} {n : PNodeM} (hx : g.node? x = some n)
    (hx1 : 1 ≤ x.id.step) (hxs : x.id.step < g.current_step) :
    ∀ c ∈ n.parents, ∀ c' ∈ n.parents, c = c' := by
  intro c hc c' hc'
  obtain ⟨mc, hmc, hmcid⟩ := a.rc.shape.pn n (List.mem_of_find?_eq_some hx) c hc
  have hcnode : g.node? c = some mc := by rw [← hmcid]; exact node?_of_mem a.rc.nodup mc hmc
  have hcs : c.id.step = x.id.step - 1 := by
    have := a.rc.shape.pbelow n (List.mem_of_find?_eq_some hx) c hc
    rwa [node?_id_eq g x n hx] at this
  have hcs' : c'.id.step = x.id.step - 1 := by
    have := a.rc.shape.pbelow n (List.mem_of_find?_eq_some hx) c' hc'
    rwa [node?_id_eq g x n hx] at this
  have hco : c ∈ n.owners := (owners_below_iff_parents g a x n hx hx1 c hcs).mpr hc
  -- simetría: `x` está en la tabla de `c`
  have hxc : x ∈ mc.owners :=
    (hok x n c mc hx hcnode (by omega) hxs (by omega) (by omega) hco
      (a.ctx.nodeval x n hx) (a.ctx.nodeval c mc hcnode)).1
  -- la cerradura mete al otro padre en la tabla de `c`, y un owner al paso propio ES el nodo
  have hin : c' ∈ mc.owners := hdc c mc hcnode x hxc n hx c' hc'
  have hmcid2 := node?_id_eq g c mc hcnode
  exact ((a.rc.oos mc (List.mem_of_find?_eq_some hcnode) c' hin
    (by rw [hmcid2]; omega)).trans hmcid2).symm

/-- **Lo que sí sobrevive del diseño, y es lo que ya estaba**: la versión *existencial*. Si la tabla
de un nodo contiene a `v`, contiene a **algún** padre de `v`. `rowOwners` la conserva por rama, y es
literalmente `parent_owns_of_coherent` leído con la simetría de `AggOk`.

Se deja escrita para que no se vuelva a intentar la universal: el salto de «algún padre» a «todos
los padres» es el hueco entero, y no lo regala el `up`. -/
theorem tableDownBranch (g : GPathM) (a : Adj g) (hok : AggOk g)
    (r : PathNodeId) (nr : PNodeM) (hr : g.node? r = some nr)
    (v : PathNodeId) (hv : v ∈ nr.owners) (nv : PNodeM) (hnv : g.node? v = some nv)
    (hv1 : 1 ≤ v.id.step) (hvs : v.id.step < g.current_step)
    (hr0 : 0 ≤ r.id.step) (hrs : r.id.step < g.current_step) :
    ∃ c ∈ nv.parents, c ∈ nr.owners := by
  -- `r` está en la tabla de `v` por simetría
  have hrv : r ∈ nv.owners :=
    (hok r nr v nv hr hnv hr0 hrs (by omega) hvs hv
      (a.ctx.nodeval r nr hr) (a.ctx.nodeval v nv hnv)).1
  -- y la coherencia del punto fijo da un padre de `v` que también lo posee
  obtain ⟨c, hc, mc, hmc, hrc⟩ :=
    parent_owns_of_coherent g a hnv hv1 hvs r hrv hr0 hrs
  have hcs : c.id.step = v.id.step - 1 := by
    have := a.rc.shape.pbelow nv (List.mem_of_find?_eq_some hnv) c hc
    rwa [node?_id_eq g v nv hnv] at this
  exact ⟨c, hc, (hok c mc r nr hmc hr (by omega) (by omega) hr0 hrs hrc
    (a.ctx.nodeval c mc hmc) (a.ctx.nodeval r nr hr)).1⟩

/-- **La primera pata de `aggPair` no dispara nunca sobre owners simétricos.**

`aggPair` borra `w` de la tabla de `x` cuando `w` está en ella y `x` **no** está en la de `w`. Con
`OwnSymmetric` eso es imposible, así que de las dos patas de la criba agresiva solo queda viva la
segunda —*no comparten owner en algún paso*— y toda conservación por la revisión se reduce a ella.

Es el recorte que deja el ataque a `aggPair` con la mitad de casos. -/
theorem aggPair_sym_second_leg (g : GPathM) (hsym : Threaded.OwnSymmetric g) (x w : PathNodeId)
    (nx nw : PNodeM) (hx : g.node? x = some nx) (hw : g.node? w = some nw) :
    nx.owners.contains w = true → nw.owners.contains x = true := fun h1 =>
  List.elem_eq_true_of_mem (hsym x nx w nw hx hw (List.mem_of_elem_eq_true h1))

/-- **`up` conserva la intuición: la fila nueva se hereda uniformemente.**

Si un nodo viejo `x` gana el nodo de fila `pid` como owner, **todo padre `c` de `x` lo gana
también**. La razón es literalmente `rowOwners`: `x` entra en la tabla de `pid` porque algún padre
`q` de `pid` —un nodo de la última fila— tiene a `x` en su tabla; `AllParentsOwn` en el estado de
antes pone ahí también a `c`; y `owners_sub_rowOwners` se lleva la tabla de `q` entera a `pid`.

**Y esta es exactamente la diferencia con `TableDownClosed`**, que el `up` no conserva: la herencia
de `rowOwners` es uniforme **hacia arriba** —todo lo que un padre de la fila posee pasa a la fila—
y solo por rama **hacia abajo**. `AllParentsOwn` habla de arriba (`x.id.step ≤ v.id.step`), así que
cae del lado bueno del diseño; `TableDownClosed` hablaba de abajo y caía del malo.

Queda por tanto localizado dónde puede romperse la intuición: **no en el `up`**. Solo en `doJoin`
—que funde dos procedencias bajo la misma clave y une las listas de padres— y en la revisión. -/
theorem gained_of_parent (g : GPathM) (d : NodeId) (hsym : Threaded.OwnSymmetric g)
    (hap : AllParentsOwn g) {x c : PathNodeId} {n mc : PNodeM}
    (hx : g.node? x = some n) (hmc : g.node? c = some mc) (hc : c ∈ n.parents)
    (hx1 : 1 ≤ x.id.step) (hxs : x.id.step < g.current_step)
    (hcg : g.gowners.contains c = true)
    (hrow : ∀ q ∈ newParents g, q.id.step = g.current_step - 1)
    {pid : PathNodeId} (hne : x ≠ pid) (hpid : x ∈ rowOwners g d pid) :
    c ∈ rowOwners g d pid := by
  -- `x` no es el nodo nuevo, así que está en la unión de las tablas de los padres de la fila
  have hin : x ∈ (unionOwnersOf g (rowParents g d pid)).filter (fun q => g.gowners.contains q) := by
    simp only [rowOwners, List.mem_append, List.mem_singleton] at hpid
    rcases hpid with h | h
    · exact h
    · exact absurd h hne
  obtain ⟨hu, _⟩ := List.mem_filter.mp hin
  obtain ⟨q, hq, mq, hmq, hxq⟩ := exists_owner_of_mem_unionOwnersOf g _ x hu
  have hqs : q.id.step = g.current_step - 1 := by
    have : q ∈ newParents g := by
      simp only [rowParents, List.mem_filter] at hq; exact hq.1
    exact hrow q this
  -- simetría: `q` está en la tabla de `x`
  have hqn : q ∈ n.owners := hsym q mq x n hmq hx hxq
  -- la intuición en el estado de antes: el padre `c` posee a `q`
  have hqc : q ∈ mc.owners := hap x n hx hx1 hxs q hqn (by omega) (by omega) c hc mc hmc
  -- y de vuelta: `c` está en la tabla de `q`, que `rowOwners` se lleva entera
  exact owners_sub_rowOwners g d pid q mq hq hmq c (hsym c mc q mq hmc hmq hqc) hcg

/-- **Tres pines consecutivos determinan el nodo entero, no solo su nodo de mapa.**

Un pin fija el **id de mapa** de un paso (`ReaderComplete.pin_id`), no el `PathNodeId`: varios nodos
del mismo paso pueden compartir id de mapa y diferir en su historia. Pero con la ventana de tres eso
se arregla solo en cuanto están pinchados los **tres** pasos de la ventana: `PMP` lee el segundo
componente del padre y `GPMP` el tercero del abuelo, y los dos están pinchados también. El
`PathNodeId` queda escrito.

**Por qué importa**: es el único mecanismo de la máquina que convierte *«mismo id de mapa»* en
*«mismo nodo»*, y «mismo nodo» es justo lo que `parents_own_unique_owner` pide para que el descenso
no tenga que elegir padre. O sea: **por debajo de una zona pinchada de tres pasos, el descenso es
gratis**, sin `SingleParents`, sin `PairMeet` y sin `AllParentsOwn`.

Y de ahí sale la sugerencia sobre el algoritmo: el lector pincha hoy el **primer** paso con elección
(`ReaderExec.firstChoice`). Si pinchara el **último** —de arriba abajo— iría dejando detrás
precisamente esa zona de tres pasos determinada, que es donde el descenso no pide nada. El coste es
cero: el mismo número de pines, la misma cota `measure`, y el veredicto no depende del orden
(`readerVerdictW_sound` no lo lee). -/
theorem pid_of_three_pins (g : GPathM)
    (hpmp : ParentId.PMP g) (hgpmp : ParentId.GPMP g)
    {r0 r1 r2 : NodeId}
    (hq0 : ∀ q ∈ g.gowners, q.id.step = r0.step → q.id = r0)
    (hq1 : ∀ q ∈ g.gowners, q.id.step = r1.step → q.id = r1)
    (hq2 : ∀ q ∈ g.gowners, q.id.step = r2.step → q.id = r2)
    {w : PathNodeId} {nw : PNodeM} (hw : g.node? w = some nw) (hwg : w ∈ g.gowners)
    (hws : w.id.step = r0.step)
    {p : PathNodeId} (hp : p ∈ nw.parents) {np : PNodeM} (hnp : g.node? p = some np)
    (hpg : p ∈ g.gowners) (hps : p.id.step = r1.step)
    {p' : PathNodeId} (hp' : p' ∈ np.parents) (hp'g : p' ∈ g.gowners)
    (hp's : p'.id.step = r2.step) :
    w = { id := r0, parent_id := some r1, gparent_id := some r2 } := by
  have hwid : nw.id = w := node?_id_eq g w nw hw
  have hnpid : np.id = p := node?_id_eq g p np hnp
  have h0 : w.id = r0 := hq0 w hwg hws
  -- el segundo componente: `PMP` lo lee del padre, que el pin de abajo fija
  have h1 : w.parent_id = some r1 := by
    have h := hpmp nw (List.mem_of_find?_eq_some hw) p hp
    rw [hwid] at h
    rw [← h, hq1 p hpg hps]
  -- el tercero: `GPMP` lo lee del abuelo, que el pin de más abajo fija
  have h2 : w.gparent_id = some r2 := by
    have hg := hgpmp.1 nw (List.mem_of_find?_eq_some hw) p hp
    have hpp := hpmp np (List.mem_of_find?_eq_some hnp) p' hp'
    rw [hnpid] at hpp
    rw [hwid] at hg
    rw [hg, ← hpp, hq2 p' hp'g hp's]
  obtain ⟨i, pi, gi⟩ := w
  simp only at h0 h1 h2
  rw [h0, h1, h2]

/-- Un nodo por encima del paso 0 tiene padre: `notroot` dice que su id declara uno, y
`isValidNode` obliga a que la lista no esté vacía. Descarga la única condición de forma que las
dos lemas de la zona pinchada piden. -/
theorem parents_exists (g : GPathM) (a : Adj g) :
    ∀ y ny, g.node? y = some ny → 1 ≤ y.id.step → ∃ c, c ∈ ny.parents := by
  intro y ny hy hy1
  have hmem := List.mem_of_find?_eq_some hy
  have hroot : ny.id.parent_id ≠ none :=
    a.rc.shape.notroot ny hmem (by rw [node?_id_eq g y ny hy]; omega)
  have hne := PathExists.parents_ne_nil_of_isValidNode g ny (a.ctx.nodeval y ny hy) hroot
  cases hc : ny.parents with
  | nil => exact absurd hc hne
  | cons c cs => exact ⟨c, List.mem_cons_self⟩

/-- **La zona pinchada.** De `j` para arriba, los owners globales de cada paso comparten id de mapa.
Es exactamente lo que un pin deja detrás (`ReaderComplete.pin_id`), acumulado sobre varios pasos. -/
def MapPinnedFrom (g : GPathM) (j : Int) : Prop :=
  ∀ k, j ≤ k → k < g.current_step → ∃ r : NodeId, r.step = k ∧
    ∀ q ∈ g.gowners, q.id.step = k → q.id = r

/-- **Un owner dos pasos por encima llega por un hijo.** `cohS` deja la tabla de un nodo contenida
en la unión de las de sus hijos, así que lo que un nodo posee dos pasos arriba lo posee ya alguno de
sus hijos — y por `owners_above_iff_sons` ese owner es a su vez hijo suyo. Es el escalón que le
permite a la ventana llevar un pin **dos** niveles más abajo, no solo uno. -/
theorem owner_two_above_via_son (g : GPathM) (a : Adj g) {x : PathNodeId} {n : PNodeM}
    (hx : g.node? x = some n) (hx0 : 0 ≤ x.id.step) (hxl : x.id.step + 2 < g.current_step)
    (w : PathNodeId) (hw : w ∈ n.owners) (hws : w.id.step = x.id.step + 2) :
    ∃ s ∈ n.sons, ∃ ms, g.node? s = some ms ∧ w ∈ ms.owners ∧ s.id.step = x.id.step + 1 := by
  have hmem := List.mem_of_find?_eq_some hx
  have hid := node?_id_eq g x n hx
  -- todo hijo está un paso por encima
  have sonStep : ∀ c ∈ n.sons, ∀ m, g.node? c = some m → c.id.step = x.id.step + 1 := by
    intro c hc m hm
    have hxp : n.id ∈ m.parents := a.pms n hmem c hc m (List.mem_of_find?_eq_some hm)
      (node?_id_eq g c m hm)
    have := a.rc.shape.pbelow m (List.mem_of_find?_eq_some hm) n.id hxp
    rw [hid, node?_id_eq g c m hm] at this
    omega
  -- hay al menos un hijo, y su tabla tiene entrada en el paso de `w`
  have hnl : (n.id.id.step == g.current_step - 1) = false := by
    rw [hid]; exact beq_false_of_ne (by omega)
  obtain ⟨s0, hs0⟩ := List.exists_mem_of_ne_nil _
    (SelfOwn.have_sons_of_isValidNode g n (a.ctx.nodeval x n hx) hnl)
  obtain ⟨m0, hm0, hm0id⟩ := a.sn n hmem s0 hs0
  have hs0node : g.node? s0 = some m0 := by rw [← hm0id]; exact node?_of_mem a.rc.nodup m0 hm0
  have hent : hasStepEntry (unionOwnersOf g n.sons) w.id.step = true := by
    have hall := owners_ok_of_isValidNode g m0 (a.ctx.nodeval s0 m0 hs0node)
    have := List.all_eq_true.mp hall w.id.step (mem_intRange (by omega) (by omega))
    simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at this ⊢
    obtain ⟨z, hz, hzs⟩ := this
    exact ⟨z, mem_unionOwnersOf g n.sons s0 m0 z hs0 hs0node hz, hzs⟩
  have hcoh := a.cohS _ (mem_intRange hx0 (by omega)) x (Threaded.mem_line_of_node? g x n hx) n hx
  obtain ⟨s, hs, ms, hms, hwms⟩ := mem_union_of_coherent g n.sons n.owners w hcoh hw hent
  exact ⟨s, hs, ms, hms, hwms, sonStep s hs ms hms⟩

/-- Un padre del nodo, con su nodo, su paso y su condición de owner global. La cadena de hechos de
forma que los dos casos altos necesitan, empaquetada una vez. -/
theorem parent_facts (g : GPathM) (a : Adj g)
    (hpar : ∀ y ny, g.node? y = some ny → 1 ≤ y.id.step → ∃ c, c ∈ ny.parents)
    {y : PathNodeId} {ny : PNodeM} (hy : g.node? y = some ny) (hy1 : 1 ≤ y.id.step)
    (hys : y.id.step < g.current_step) :
    ∃ p mp, g.node? p = some mp ∧ p ∈ ny.parents ∧ p.id.step = y.id.step - 1 ∧
      p ∈ g.gowners := by
  obtain ⟨p, hp⟩ := hpar y ny hy hy1
  have hmem := List.mem_of_find?_eq_some hy
  obtain ⟨mp, hmp, hmpid⟩ := a.rc.shape.pn ny hmem p hp
  have hpnode : g.node? p = some mp := by rw [← hmpid]; exact node?_of_mem a.rc.nodup mp hmp
  have hps : p.id.step = y.id.step - 1 := by
    have := a.rc.shape.pbelow ny hmem p hp
    rwa [node?_id_eq g y ny hy] at this
  exact ⟨p, mp, hpnode, hp, hps,
    a.ctx.ownGow y ny hy p ((a.links y ny hy).1 p hp) (by omega) (by omega)⟩

/-- **Dentro de la zona pinchada, la tabla de todo nodo está decidida.**

Tres casos, y los tres son el diseño:

* al **paso propio**, `OOS`: un owner a la altura del nodo *es* el nodo;
* **un paso arriba**, los owners son los hijos (`owners_above_iff_sons`), y un hijo lleva en su
  identificador el id de mapa de su padre (`PMP`) y el del abuelo (`GPMP`) — que son el nodo mismo y
  su padre. Con el id de mapa del paso ya pinchado, los tres componentes están escritos;
* **dos o más arriba**, `pid_of_three_pins`: los tres pasos de la ventana caen dentro de la zona.

O sea: **por dentro de una zona pinchada de tres pasos el descenso no elige.** Por
`parents_own_unique_owner`, todo padre del pick de abajo es un owner común de todos los picks, así
que la cadena baja un paso por debajo de la zona **sin hipótesis ninguna** — ni `SingleParents`, ni
`PairMeet`, ni `AllParentsOwn`. -/
theorem decided_in_pinned_zone (g : GPathM) (a : Adj g)
    (hpmp : ParentId.PMP g) (hgpmp : ParentId.GPMP g)
    (hpar : ∀ y ny, g.node? y = some ny → 1 ≤ y.id.step → ∃ c, c ∈ ny.parents)
    {j : Int} (hpin : MapPinnedFrom g j)
    {x : PathNodeId} {n : PNodeM} (hx : g.node? x = some n) (hxj : j - 1 ≤ x.id.step)
    {w w' : PathNodeId} (hw : w ∈ n.owners) (hw' : w' ∈ n.owners)
    (hge : x.id.step ≤ w.id.step) (heq : w.id.step = w'.id.step) : w = w' := by
  have hmem := List.mem_of_find?_eq_some hx
  have hid : n.id = x := node?_id_eq g x n hx
  have hx0 : 0 ≤ x.id.step := by
    have := a.rc.snn n hmem; rwa [hid] at this
  have hws : w.id.step < g.current_step := by
    have := a.rc.ownb n hmem w hw; exact this
  have hw's : w'.id.step < g.current_step := by
    have := a.rc.ownb n hmem w' hw'; exact this
  -- el nodo del owner, y que es owner global
  have hnode : ∀ u, u ∈ n.owners → 0 ≤ u.id.step → u.id.step < g.current_step →
      ∃ mu, g.node? u = some mu ∧ u ∈ g.gowners := by
    intro u hu hu0 hus
    have hug : u ∈ g.gowners := a.ctx.ownGow x n hx u hu hu0 hus
    obtain ⟨mu, hmu⟩ := Option.isSome_iff_exists.mp
      ((GownersNodes.hasNode_iff g u).mp (a.rc.gn u hug))
    exact ⟨mu, hmu, hug⟩
  rcases int_eq_or_ne w.id.step x.id.step with hcase | hne1
  · -- (1) al paso propio: `OOS`
    have e1 : w = n.id := a.rc.oos n hmem w hw (by rw [hid]; exact hcase)
    have e2 : w' = n.id := a.rc.oos n hmem w' hw' (by rw [hid, ← heq]; exact hcase)
    rw [e1, e2]
  rcases int_eq_or_ne w.id.step (x.id.step + 1) with hcase | hne2
  · -- (2) un paso arriba: los owners son hijos, y el hijo lleva escritos padre y abuelo
    obtain ⟨r, hrs, hr⟩ := hpin w.id.step (by omega) hws
    have hxl : x.id.step ≤ g.current_step - 2 := by omega
    have son : ∀ u, u ∈ n.owners → u.id.step = x.id.step + 1 →
        ∀ mu, g.node? u = some mu → u ∈ g.gowners → u = ⟨r, some x.id, x.parent_id⟩ := by
      intro u hu hus mu hmu hug
      have hson : u ∈ n.sons := (owners_above_iff_sons g a x n hx hxl u (by rw [hus])).mp hu
      have hxpar : x ∈ mu.parents := by
        have := a.pms n hmem u hson mu (List.mem_of_find?_eq_some hmu) (node?_id_eq g u mu hmu)
        rwa [hid] at this
      have h1 : u.id = r := hr u hug (by rw [hus, ← hcase])
      have h2 : u.parent_id = some x.id := by
        have := hpmp mu (List.mem_of_find?_eq_some hmu) x hxpar
        rw [node?_id_eq g u mu hmu] at this; rw [← this]
      have h3 : u.gparent_id = x.parent_id := by
        have := hgpmp.1 mu (List.mem_of_find?_eq_some hmu) x hxpar
        rwa [node?_id_eq g u mu hmu] at this
      obtain ⟨i, pi, gi⟩ := u
      simp only at h1 h2 h3
      rw [h1, h2, h3]
    obtain ⟨mw, hmw, hwg⟩ := hnode w hw (by omega) hws
    obtain ⟨mw', hmw', hw'g⟩ := hnode w' hw' (by omega) hw's
    rw [son w hw hcase mw hmw hwg, son w' hw' (by rw [← heq]; exact hcase) mw' hmw' hw'g]
  · -- (3) dos o más arriba
    have hgt : x.id.step + 2 ≤ w.id.step := by omega
    by_cases hdeep : j ≤ w.id.step - 2
    case neg =>
      -- `x` está justo debajo de la zona y `w` dos pasos arriba: la ventana lo lleva por el hijo
      obtain ⟨r0, hr0s, hr0⟩ := hpin w.id.step (by omega) hws
      obtain ⟨r1, hr1s, hr1⟩ := hpin (x.id.step + 1) (by omega) (by omega)
      have det : ∀ u, u ∈ n.owners → u.id.step = w.id.step →
          ∀ mu, g.node? u = some mu → u = ⟨r0, some r1, some x.id⟩ := by
        intro u hu hus mu hmu
        obtain ⟨sn, hsn, ms, hms, hums, hss⟩ :=
          owner_two_above_via_son g a hx (by omega) (by omega) u hu (by omega)
        have husons : u ∈ ms.sons :=
          (owners_above_iff_sons g a sn ms hms (by omega) u (by omega)).mp hums
        have hsu : sn ∈ mu.parents := by
          have := a.pms ms (List.mem_of_find?_eq_some hms) u husons mu
            (List.mem_of_find?_eq_some hmu) (node?_id_eq g u mu hmu)
          rwa [node?_id_eq g sn ms hms] at this
        have hxs : x ∈ ms.parents := by
          have := a.pms n hmem sn hsn ms (List.mem_of_find?_eq_some hms)
            (node?_id_eq g sn ms hms)
          rwa [hid] at this
        have hsg : sn ∈ g.gowners :=
          a.ctx.ownGow x n hx sn ((a.links x n hx).2 sn hsn) (by omega) (by omega)
        have hug : u ∈ g.gowners := a.ctx.ownGow x n hx u hu (by omega) (by omega)
        have h1 : u.id = r0 := hr0 u hug (by rw [hus, ← hr0s])
        have h2 : u.parent_id = some sn.id := by
          have := hpmp mu (List.mem_of_find?_eq_some hmu) sn hsu
          rw [node?_id_eq g u mu hmu] at this; rw [← this]
        have h3 : u.gparent_id = sn.parent_id := by
          have := hgpmp.1 mu (List.mem_of_find?_eq_some hmu) sn hsu
          rwa [node?_id_eq g u mu hmu] at this
        have h4 : sn.parent_id = some x.id := by
          have := hpmp ms (List.mem_of_find?_eq_some hms) x hxs
          rw [node?_id_eq g sn ms hms] at this; rw [← this]
        have h5 : sn.id = r1 := hr1 sn hsg (by rw [hss])
        obtain ⟨i, pi, gi⟩ := u
        simp only at h1 h2 h3
        rw [h1, h2, h3, h4, h5]
      obtain ⟨mw, hmw, _⟩ := hnode w hw (by omega) hws
      obtain ⟨mw', hmw', _⟩ := hnode w' hw' (by omega) hw's
      rw [det w hw rfl mw hmw, det w' hw' heq.symm mw' hmw']
    case pos =>
    obtain ⟨r0, hr0s, hr0⟩ := hpin w.id.step (by omega) hws
    obtain ⟨r1, hr1s, hr1⟩ := hpin (w.id.step - 1) (by omega) (by omega)
    obtain ⟨r2, hr2s, hr2⟩ := hpin (w.id.step - 2) (by omega) (by omega)
    have det : ∀ u, u ∈ n.owners → u.id.step = w.id.step →
        ∀ mu, g.node? u = some mu → u = ⟨r0, some r1, some r2⟩ := by
      intro u hu hus mu hmu
      obtain ⟨mu', hmu', hug⟩ := hnode u hu (by omega) (by rw [hus]; exact hws)
      rw [hmu'] at hmu; cases hmu
      obtain ⟨p, mp, hpnode, hp, hps, hpg⟩ :=
        parent_facts g a hpar hmu' (by omega) (by rw [hus]; exact hws)
      obtain ⟨p', mp', hp'node, hp', hp's, hp'g⟩ :=
        parent_facts g a hpar hpnode (by omega) (by omega)
      have hr0' : ∀ q ∈ g.gowners, q.id.step = r0.step → q.id = r0 := by rw [hr0s]; exact hr0
      have hr1' : ∀ q ∈ g.gowners, q.id.step = r1.step → q.id = r1 := by rw [hr1s]; exact hr1
      have hr2' : ∀ q ∈ g.gowners, q.id.step = r2.step → q.id = r2 := by rw [hr2s]; exact hr2
      exact pid_of_three_pins g hpmp hgpmp hr0' hr1' hr2' hmu' hug (by rw [hus, ← hr0s])
        hp hpnode hpg (by rw [hps, hus, hr1s]) hp' hp'g (by rw [hp's, hps, hus, hr2s]; omega)
    obtain ⟨mw, hmw, _⟩ := hnode w hw (by omega) hws
    obtain ⟨mw', hmw', _⟩ := hnode w' hw' (by omega) hw's
    rw [det w hw rfl mw hmw, det w' hw' heq.symm mw' hmw']

/-- **El descenso baja gratis por debajo de una zona pinchada.**

Si los pasos de `j` para arriba tienen su id de mapa fijado, toda cadena parcial sana cuyo pick más
bajo esté en la zona se extiende un paso **sin hipótesis ninguna**: `decided_in_pinned_zone` deja la
tabla del pick de abajo decidida en todos los pasos de los picks, `parents_own_unique_owner` hace
entonces que **todo** padre sirva, y `parent_owns_of_coherent` regala uno.

Es la conclusión de `CommonOwner` en ese `lo`, sin `SingleParents`, sin `TwoParents`, sin `PairMeet`
y sin `AllParentsOwn`. La hipótesis que la sustituye no es sobre las tablas: es sobre **lo que el
lector ya ha pinchado**. -/
theorem extend_below_pinned (g : GPathM) (a : Adj g) (hok : AggOk g) (hsmp : Sons.SMP g)
    (hpmp : ParentId.PMP g) (hgpmp : ParentId.GPMP g)
    (hpar : ∀ y ny, g.node? y = some ny → 1 ≤ y.id.step → ∃ c, c ∈ ny.parents)
    {j : Int} (hpin : MapPinnedFrom g j)
    (sel : Int → PathNodeId) (lo : Int) (hlo0 : 0 < lo) (hlo : lo ≤ g.current_step - 1)
    (hjlo : j - 1 ≤ lo) (hs : SoundFrom g sel lo) :
    ∃ c nc, g.node? c = some nc ∧ c.id.step = lo - 1 ∧
      ∀ k, lo ≤ k → k < g.current_step → c ∈ ownersOf g (sel k) := by
  obtain ⟨hsome, hstep⟩ := hs.node lo (Int.le_refl _) (by omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hid : n.id = sel lo := node?_id_eq g _ n hn
  have hx1 : 1 ≤ (sel lo).id.step := by rw [hstep]; omega
  have hxs : (sel lo).id.step < g.current_step := by rw [hstep]; omega
  have hself : sel lo ∈ n.owners := by
    simpa only [ownersOf, hn] using hs.self_owned lo (Int.le_refl _) (by omega)
  obtain ⟨c, hc, mc, hcnode, _⟩ :=
    parent_owns_of_coherent g a hn hx1 hxs (sel lo) hself (by rw [hstep]; omega) hxs
  have hcstep : c.id.step = lo - 1 := by
    have := a.rc.shape.pbelow n (List.mem_of_find?_eq_some hn) c hc
    rw [hid, hstep] at this; omega
  refine ⟨c, mc, hcnode, hcstep, fun k hk0 hk1 => ?_⟩
  obtain ⟨hksome, hkstep⟩ := hs.node k hk0 hk1
  obtain ⟨nk, hnk⟩ := Option.isSome_iff_exists.mp hksome
  have hkx : sel k ∈ n.owners := by
    rcases int_eq_or_ne k lo with rfl | hne
    · exact hself
    · have h := hs.owned k lo hk0 (Int.le_refl _) hk1 (by omega) hne
      simpa only [ownersOf, hn] using (List.mem_filter.mp h).1
  -- la zona pinchada decide la tabla: el pick ES la entrada de su paso
  have huniq : ∀ w ∈ n.owners, w.id.step = k → w = sel k := by
    intro w hw hws
    exact decided_in_pinned_zone g a hpmp hgpmp hpar hpin hn (by rw [hstep]; omega)
      hw hkx (by rw [hstep, hws]; omega) (by rw [hws, hkstep])
  have hvk : sel k ∈ mc.owners :=
    parents_own_unique_owner g a hok hsmp hn hx1 hxs k (by omega) hk1 (sel k) huniq c hc mc hcnode
  have hsymc := (hok c mc (sel k) nk hcnode hnk (by rw [hcstep]; omega) (by rw [hcstep]; omega)
    (by rw [hkstep]; omega) (by rw [hkstep]; exact hk1) hvk
    (a.ctx.nodeval c mc hcnode) (a.ctx.nodeval (sel k) nk hnk)).1
  simpa only [ownersOf, hnk] using hsymc

/-- **Y con toda la corrida pinchada, es `CommonOwner` entero**, o sea el veredicto y que el lector
no se atasca (`NoDeadEndVerdict.sat_of_commonOwner`, `ReaderDescent.pinExtends_of_commonOwner`).

`MapPinnedFrom g 1` dice que todo paso de 1 para arriba tiene su id de mapa fijado — el paso 0 no
hace falta, porque el descenso nunca pide extender por debajo de él. -/
theorem commonOwner_of_mapPinned (g : GPathM) (a : Adj g) (hok : AggOk g) (hsmp : Sons.SMP g)
    (hpin : MapPinnedFrom g 1) : CommonOwner g := fun sel lo hlo0 hlo hs =>
  extend_below_pinned g a hok hsmp a.rc.pmp a.rc.gpmp (parents_exists g a) hpin sel lo hlo0 hlo
    (by omega) hs

-- ============================================================
-- El argumento del lector, formalizado hasta donde llega
-- ============================================================

/-- **Todo candidato del lector es compatible con algo en cada paso, en los dos sentidos.**

Es el argumento de que el lector no puede bloquearse, escrito: el nodo `q` que va a pinchar es
válido, así que `isValidNode` le da una entrada en **cada** paso; esa entrada es owner global luego
es nodo; y la simetría de `AggOk` la devuelve, así que `q` está también en su tabla.

O sea: **el pin nunca se queda sin candidato en ningún paso.** Lo que el lector sabe de antemano
cuando elige `q` es exactamente esto, y es cierto.

Lo que *no* da, y es el único hueco: que los `z_j` de distintos pasos sean compatibles **entre
sí**. `AggOk` compara un nodo con cada uno de sus owners, nunca dos owners entre ellos
(`aggPair` solo dispara sobre pares ya enlazados), así que de aquí sale 2-consistencia con `q` y no
la cadena. Medido: 52.720 de 380.746 tríos ordenados incumplen la transitividad de la posesión.

Desde `ReaderBT.readerVerdictBT_iff` eso ya **no afecta a la corrección** de la máquina: el
retroceso lo cubre. Afecta solo a cuántas veces puede retroceder, que medido es cero. -/
theorem pin_compatible_at_every_step (g : GPathM) (a : Adj g) (hok : AggOk g)
    {q : PathNodeId} {nq : PNodeM} (hq : g.node? q = some nq)
    (hq0 : 0 ≤ q.id.step) (hqs : q.id.step < g.current_step)
    (j : Int) (hj0 : 0 ≤ j) (hj1 : j < g.current_step) :
    ∃ z nz, g.node? z = some nz ∧ z.id.step = j ∧ z ∈ nq.owners ∧ q ∈ nz.owners := by
  -- `isValidNode` le da a `q` una entrada en el paso `j`
  have hent : hasStepEntry nq.owners j = true :=
    List.all_eq_true.mp (owners_ok_of_isValidNode g nq (a.ctx.nodeval q nq hq)) j
      (mem_intRange hj0 (by omega))
  simp only [hasStepEntry, List.any_eq_true, beq_iff_eq] at hent
  obtain ⟨z, hz, hzs⟩ := hent
  -- esa entrada es owner global, luego nodo
  have hzg : z ∈ g.gowners := a.ctx.ownGow q nq hq z hz (by rw [hzs]; exact hj0) (by rw [hzs]; exact hj1)
  obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff g z).mp (a.rc.gn z hzg))
  -- y `AggOk` la devuelve: `q` está también en su tabla
  exact ⟨z, nz, hnz, hzs, hz,
    (hok q nq z nz hq hnz hq0 hqs (by rw [hzs]; exact hj0) (by rw [hzs]; exact hj1) hz
      (a.ctx.nodeval q nq hq) (a.ctx.nodeval z nz hnz)).1⟩

/-- **Y lo que falta, dicho como definición para que se vea que es una sola frase.**

`pin_compatible_at_every_step` da los `z_j`. `CompatChain` pide que se puedan elegir compatibles
entre sí. Con ella, `q` está en una cadena y el lector no retrocede nunca. Es la misma frase que
`NoDeadEnd`, `Inhabited` y `ValidHasChain`, vista desde el candidato del lector. -/
def CompatChain (g : GPathM) : Prop :=
  ∀ q nq, g.node? q = some nq → 0 ≤ q.id.step → q.id.step < g.current_step →
    ∃ sel : Int → PathNodeId, ChainSound g sel ∧ sel q.id.step = q

/-- **La criba ya está en su techo: consistencia de caminos completa.**

Para todo nodo `x`, todo owner suyo `w` y **todo** paso `j`, hay un testigo `z` en el paso `j`
compatible con los dos **en los dos sentidos**: `z` está en las tablas de `x` y de `w`, y `x` y `w`
están en la de `z`.

Eso es 3-consistencia (path consistency) con testigo simétrico, y es **lo máximo que unas tablas
por pares pueden sostener**. Por eso no hay tercera pata que añadir a `aggPair`: las dos que tiene
—asimetría y no compartir paso— ya saturan lo que la información por pares permite podar.

La consecuencia, junto con `pin_compatible_at_every_step`: lo que le falta al lector para no
retroceder nunca no es más criba. Cualquier poda que mire solo pares ya está hecha; la que faltaría
tendría que mirar **tríos**, que es la escalera que no termina (una tabla por tríos da
4-consistencia, y hace falta `n`-consistencia sobre un grafo de restricciones completo). -/
theorem path_consistent_witness (g : GPathM) (a : Adj g) (hok : AggOk g)
    {x w : PathNodeId} {nx nw : PNodeM} (hx : g.node? x = some nx) (hw : g.node? w = some nw)
    (hx0 : 0 ≤ x.id.step) (hxs : x.id.step < g.current_step)
    (hw0 : 0 ≤ w.id.step) (hws : w.id.step < g.current_step) (hwx : w ∈ nx.owners)
    (j : Int) (hj0 : 0 ≤ j) (hjs : j < g.current_step) :
    ∃ z nz, g.node? z = some nz ∧ z.id.step = j ∧
      z ∈ nx.owners ∧ x ∈ nz.owners ∧ z ∈ nw.owners ∧ w ∈ nz.owners := by
  obtain ⟨z, hzx, hzw, hzs⟩ :=
    ParentWitness.shared_owner a hok hx hw hx0 hxs hw0 hws hwx j hj0 hjs
  have hzg : z ∈ g.gowners := a.ctx.ownGow x nx hx z hzx (by rw [hzs]; exact hj0)
    (by rw [hzs]; exact hjs)
  obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff g z).mp (a.rc.gn z hzg))
  exact ⟨z, nz, hnz, hzs, hzx,
    (hok x nx z nz hx hnz hx0 hxs (by rw [hzs]; exact hj0) (by rw [hzs]; exact hjs) hzx
      (a.ctx.nodeval x nx hx) (a.ctx.nodeval z nz hnz)).1,
    hzw,
    (hok w nw z nz hw hnz hw0 hws (by rw [hzs]; exact hj0) (by rw [hzs]; exact hjs) hzw
      (a.ctx.nodeval w nw hw) (a.ctx.nodeval z nz hnz)).1⟩

/-- **Y la tercera pata que faltaría no es sana.**

La tentación, leyendo `pin_compatible_at_every_step`, es hacer que la criba compare **dos owners del
mismo nodo** entre sí y borre el nodo cuando son incompatibles. No vale, y la razón es la de siempre
en este repo: *la tabla de un nodo es la unión de sus ramas.* Si `x` está en una cadena real por
`u`, su tabla lleva además owners de otras cadenas reales, que no tienen por qué ser compatibles con
`u`. Borrar `x` por eso tira un nodo bueno.

El criterio de sanidad está escrito en el repo como `ConservationFilter.PrunesF` /
`ChainSound_reviewAgg`: solo se puede quitar lo que **ninguna** cadena sana usa. Y una cadena sana a
través de `x` usa **uno** de los dos owners incompatibles, no los dos — así que su incompatibilidad
no autoriza a quitar nada.

Lo que sí autorizaría es una tabla por **pares de owners**, o sea por tríos de nodos: eso es
4-consistencia, cuesta ×N por nivel y la escalera reproduce la obligación un piso más arriba. -/
def TripleWitness (g : GPathM) : Prop :=
  ∀ x nx u nu v nv, g.node? x = some nx → g.node? u = some nu → g.node? v = some nv →
    u ∈ nx.owners → v ∈ nx.owners → v ∈ nu.owners →
    ∀ j, 0 ≤ j → j < g.current_step →
      ∃ z, z ∈ nx.owners ∧ z ∈ nu.owners ∧ z ∈ nv.owners ∧ z.id.step = j

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

/-- info: 'AbsSat.GraphPath.Model.Descent.decided_in_pinned_zone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decided_in_pinned_zone

/-- info: 'AbsSat.GraphPath.Model.Descent.extend_below_pinned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms extend_below_pinned

/-- info: 'AbsSat.GraphPath.Model.Descent.commonOwner_of_mapPinned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms commonOwner_of_mapPinned

/-- info: 'AbsSat.GraphPath.Model.Descent.path_consistent_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms path_consistent_witness

/-- info: 'AbsSat.GraphPath.Model.Descent.pin_compatible_at_every_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pin_compatible_at_every_step

/-- info: 'AbsSat.GraphPath.Model.Descent.pid_of_three_pins' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pid_of_three_pins

/-- info: 'AbsSat.GraphPath.Model.Descent.gained_of_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gained_of_parent

/-- info: 'AbsSat.GraphPath.Model.Descent.singleParent_of_tableDownClosed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms singleParent_of_tableDownClosed

/-- info: 'AbsSat.GraphPath.Model.Descent.tableDownBranch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tableDownBranch

/-- info: 'AbsSat.GraphPath.Model.Descent.aggPair_sym_second_leg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms aggPair_sym_second_leg

/-- info: 'AbsSat.GraphPath.Model.Descent.allParentsOwn_of_tableDownClosed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms allParentsOwn_of_tableDownClosed

/-- info: 'AbsSat.GraphPath.Model.Descent.owners_sub_rowOwners' depends on axioms: [propext] -/
#guard_msgs in
#print axioms owners_sub_rowOwners

/-- info: 'AbsSat.GraphPath.Model.Descent.commonOwner_of_allParentsOwn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms commonOwner_of_allParentsOwn

/-- info: 'AbsSat.GraphPath.Model.Descent.allParentsOwn_of_singleParents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms allParentsOwn_of_singleParents

/-- info: 'AbsSat.GraphPath.Model.Descent.commonOwner_of_decided' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms commonOwner_of_decided

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
