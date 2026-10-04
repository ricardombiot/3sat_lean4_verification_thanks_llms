-- lean_project/AbsSat/GraphPath/Model/Greedy.lean
import AbsSat.GraphPath.Model.WeakPairs
import AbsSat.GraphPath.Model.LinkedChain

/-!
# The greedy construction of a path through an entry

The pair level (`PairPinExact`) asks, for each entry `(x, q)` of a pinned, reviewed state, for a whole
path through `x` and `q`. Splicing two known paths does not give it (probe `splice`, v144: many splices
fail). This module builds the path **from the tables of the reviewed state itself**, greedily: start with
`{x, q}` and fill the remaining steps in a fixed order, each time with a node that owns, and is owned by,
every node already chosen.

* **`Clique`** — nodes of `R`, one per step, each owning every other.
* **`NeverStuck R T order`** — filling the steps of `order` from `T`, *every* choice so far leaves a
  next choice (the construction never gets stuck, whatever it picks); **`Completes`** — some sequence
  of choices fills them all. `completes_of_neverStuck`.
* **`chain_of_clique`** — a clique covering every step **is** a sound chain: pairwise ownership gives
  the owner tables, the review's link rule (`Sup.link`) gives the parent links, `SMP` the son links.
* **`tablesSound_of_greedy`** — if from every entry the greedy construction never gets stuck, the tables
  are exact; **`pinExact_of_greedy`** — the same for a pinned reviewed state: the pair level reduces to
  the greedy construction not getting stuck.

Nothing here uses the exactness of the state before the pin: the whole content of the pair level is
moved into one combinatorial statement about the reviewed tables.
-/

namespace AbsSat.GraphPath.Model.Greedy

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.AnchoredSurvive (Sup SMP_filterAllAgg)
open AbsSat.GraphPath.Model.AggFixpoint (AggOk aggOk_reviewAgg)
open AbsSat.GraphPath.Model.Exactness (TablesSound Realizes)
open AbsSat.GraphPath.Model.SupportSplit (rel_self mem_of_hasNode')
open AbsSat.GraphPath.Model.LinkedChain (sup_self)

-- ============================================================
-- Cliques and the greedy construction
-- ============================================================

/-- Nodes of `R`, at most one per step, each owning every other (and itself). -/
structure Clique (R : GPathM) (T : List PathNodeId) : Prop where
  rel : ∀ a ∈ T, ∀ b ∈ T, Rel R a b
  step : ∀ a ∈ T, ∀ b ∈ T, a.id.step = b.id.step → a = b

/-- Some sequence of choices fills every step of `order`. -/
def Completes (R : GPathM) : List PathNodeId → List Int → Prop
  | _, [] => True
  | T, l :: rest => ∃ y : PathNodeId, y.id.step = l ∧ Clique R (y :: T) ∧ Completes R (y :: T) rest

/-- **The greedy construction never gets stuck**: at each step of `order` there is a choice, and every
choice leaves the rest fillable in the same sense. -/
def NeverStuck (R : GPathM) : List PathNodeId → List Int → Prop
  | _, [] => True
  | T, l :: rest => (∃ y : PathNodeId, y.id.step = l ∧ Clique R (y :: T)) ∧
      ∀ y : PathNodeId, y.id.step = l → Clique R (y :: T) → NeverStuck R (y :: T) rest

theorem completes_of_neverStuck (R : GPathM) : ∀ (order : List Int) (T : List PathNodeId),
    NeverStuck R T order → Completes R T order
  | [], _, _ => trivial
  | _ :: rest, _, ⟨⟨y, hy, hc⟩, h⟩ => ⟨y, hy, hc, completes_of_neverStuck R rest _ (h y hy hc)⟩

/-- A completed construction is a clique covering the start and every step of the order. -/
theorem clique_of_completes (R : GPathM) : ∀ (order : List Int) (T : List PathNodeId),
    Clique R T → Completes R T order →
      ∃ T', Clique R T' ∧ (∀ p ∈ T, p ∈ T') ∧ ∀ l ∈ order, ∃ p ∈ T', p.id.step = l
  | [], T, hc, _ => ⟨T, hc, fun _ h => h, fun _ h => absurd h List.not_mem_nil⟩
  | l :: rest, T, _, ⟨y, hy, hc', hrest⟩ => by
    obtain ⟨T', hcT, hsub, hcov⟩ := clique_of_completes R rest (y :: T) hc' hrest
    refine ⟨T', hcT, fun p hp => hsub p (List.mem_cons_of_mem _ hp), fun l' hl' => ?_⟩
    rcases List.mem_cons.mp hl' with rfl | hl''
    · exact ⟨y, hsub y List.mem_cons_self, hy⟩
    · exact hcov l' hl''

-- ============================================================
-- A covering clique is a sound chain
-- ============================================================

/-- **A clique covering every step is a sound chain** through all of its nodes. -/
theorem chain_of_clique (R : GPathM) (ad : AdjacentOwners.Adj R) (hok : AggOk R) (hsmp : Sons.SMP R)
    (hpos : 0 < R.current_step) (T : List PathNodeId) (x0 : PathNodeId) (hc : Clique R T)
    (hcov : ∀ k, 0 ≤ k → k < R.current_step → ∃ p ∈ T, p.id.step = k) :
    ∃ sel, ChainSound R sel ∧ ∀ p ∈ T, sel p.id.step = p := by
  have sup := sup_self R ad hok hsmp
  let sel : Int → PathNodeId := fun k => (T.find? (fun p => p.id.step == k)).getD x0
  have pick : ∀ k, (∃ p ∈ T, p.id.step = k) → sel k ∈ T ∧ (sel k).id.step = k := by
    intro k ⟨p, hp, hps⟩
    cases hf : T.find? (fun p => p.id.step == k) with
    | none =>
      have := List.find?_eq_none.mp hf p hp
      rw [hps] at this
      exact absurd ((beq_iff_eq.mpr rfl : (k == k) = true)) this
    | some p' =>
      have he : sel k = p' := by show (T.find? (fun p => p.id.step == k)).getD x0 = p'; rw [hf]; rfl
      rw [he]
      have hb := List.find?_some hf
      exact ⟨List.mem_of_find?_eq_some hf, eq_of_beq hb⟩
  have hselT : ∀ p ∈ T, sel p.id.step = p := by
    intro p hp
    obtain ⟨h1, h2⟩ := pick p.id.step ⟨p, hp, rfl⟩
    exact hc.step _ h1 p hp h2
  have inR : ∀ k, 0 ≤ k → k < R.current_step → sel k ∈ T ∧ (sel k).id.step = k :=
    fun k h0 h1 => pick k (hcov k h0 h1)
  have rel : ∀ i j, 0 ≤ i → i < R.current_step → 0 ≤ j → j < R.current_step → Rel R (sel i) (sel j) :=
    fun i j hi0 hi1 hj0 hj1 => hc.rel _ (inR i hi0 hi1).1 _ (inR j hj0 hj1).1
  have hchain : IsChain R sel := by
    refine ⟨fun k h0 h1 => ?_, fun k h0 h1 => ?_⟩
    · obtain ⟨m, hm, _⟩ := rel k k h0 h1 h0 h1
      exact ⟨by rw [hm]; rfl, (inR k h0 h1).2⟩
    · obtain ⟨d, hd, _⟩ := rel (k + 1) k (by omega) h1 h0 (by omega)
      have hl := sup.link (sel (k + 1)) (sel k) d (rel (k + 1) k (by omega) h1 h0 (by omega))
        (rel k (k + 1) h0 (by omega) (by omega) h1)
        (by rw [(inR k h0 (by omega)).2, (inR (k + 1) (by omega) h1).2]) hd
      rw [hd]
      exact hl
  refine ⟨sel, ⟨⟨hchain, fun i j hi hj hi1 hj1 _ => ?_, fun k h0 h1 => ?_⟩, fun k h0 h1 => ?_,
    Sons.son_link_of_SMP R hsmp sel hchain, Sons.root_shape_of R ad.rc.rootz ad.rc.shape.notroot sel hchain hpos⟩,
    hselT⟩
  · obtain ⟨m, hm, hin, _⟩ := rel j i hj hj1 hi hi1
    unfold ownersOf
    rw [hm]
    refine List.mem_filter.mpr ⟨hin, ?_⟩
    rw [(inR i hi hi1).2]
    exact (beq_iff_eq.mpr rfl : (i == i) = true)
  · obtain ⟨_, _, _, hmk⟩ := rel k k h0 h1 h0 h1
    exact sup.gow _ hmk
  · obtain ⟨m, hm, hin, _⟩ := rel k k h0 h1 h0 h1
    unfold ownersOf
    rw [hm]
    exact hin

-- ============================================================
-- Exactness from the greedy construction
-- ============================================================

/-- **Exactness from the greedy construction.** If, from every entry `(x, q)`, filling the other steps
greedily never gets stuck, every entry lies on a sound chain. -/
theorem tablesSound_of_greedy (R : GPathM) (ad : AdjacentOwners.Adj R) (hok : AggOk R) (hsmp : Sons.SMP R)
    (ord : PathNodeId → PathNodeId → List Int)
    (hord : ∀ x q k, 0 ≤ k → k < R.current_step → k ≠ x.id.step → k ≠ q.id.step → k ∈ ord x q)
    (hg : ∀ x q, Rel R x q → NeverStuck R [x, q] (ord x q)) : TablesSound R := by
  intro x n hx hx0 hx1 q hq0 hq1 hqn
  have sup := sup_self R ad hok hsmp
  have hmx : Mem R x := ⟨n, hx⟩
  have hmq : Mem R q := mem_of_hasNode' R ad (ad.ctx.gn q (ad.ctx.ownGow x n hx q hqn hq0 hq1))
  have hxq : Rel R x q := ⟨n, hx, hqn, hmq⟩
  have hqx : Rel R q x := sup.sym x q hxq
  have hstep : q.id.step = x.id.step → q = x := by
    intro hs
    have hxid := node?_id_eq R x n hx
    have := ad.rc.oos n (List.mem_of_find?_eq_some hx) q hqn (by rw [hxid]; exact hs)
    rw [this, hxid]
  have hc : Clique R [x, q] := by
    refine ⟨fun a ha b hb => ?_, fun a ha b hb hab => ?_⟩
    · rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
      · exact rel_self R ad hmx
      · rw [List.mem_singleton.mp hb']; exact hxq
      · rw [List.mem_singleton.mp ha']; exact hqx
      · rw [List.mem_singleton.mp ha', List.mem_singleton.mp hb']; exact rel_self R ad hmq
    · rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · rw [List.mem_singleton.mp hb'] at hab ⊢; exact (hstep hab.symm).symm
      · rw [List.mem_singleton.mp ha'] at hab ⊢; exact hstep hab
      · rw [List.mem_singleton.mp ha', List.mem_singleton.mp hb']
  obtain ⟨T', hcT, hsub, hcov⟩ := clique_of_completes R _ _ hc
    (completes_of_neverStuck R _ _ (hg x q hxq))
  have hcov' : ∀ k, 0 ≤ k → k < R.current_step → ∃ p ∈ T', p.id.step = k := by
    intro k h0 h1
    by_cases hkx : k = x.id.step
    · exact ⟨x, hsub x List.mem_cons_self, hkx.symm⟩
    · by_cases hkq : k = q.id.step
      · exact ⟨q, hsub q (List.mem_cons_of_mem _ List.mem_cons_self), hkq.symm⟩
      · exact hcov k (hord x q k h0 h1 hkx hkq)
  obtain ⟨sel, hsc, hsel⟩ := chain_of_clique R ad hok hsmp (by omega) T' x hcT hcov'
  exact ⟨sel, hsc, hsel x (hsub x List.mem_cons_self),
    hsel q (hsub q (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- **The pair level from the greedy construction.** On a readable state, if after a pin and the review
the greedy construction never gets stuck from any entry, the pinned state is exact. -/
theorem pinExact_of_greedy (g : GPathM) (hR : ReadableAgg g) (hsmp : Sons.SMP g) (hpms : Sons.PMS g)
    (hsn : Sons.SN g) (r : NodeId) (hvr : isValid (filterAllAgg g [r]) = true)
    (ord : PathNodeId → PathNodeId → List Int)
    (hord : ∀ x q k, 0 ≤ k → k < (filterAllAgg g [r]).current_step → k ≠ x.id.step → k ≠ q.id.step →
      k ∈ ord x q)
    (hg : ∀ x q, Rel (filterAllAgg g [r]) x q → NeverStuck (filterAllAgg g [r]) [x, q] (ord x q)) :
    TablesSound (filterAllAgg g [r]) := by
  have hc := RCtx_of_readableAgg g hR
  have ad := AdjacentOwners.adj_of_readable _ (ReadableAgg_filterAllAgg g hR [r]) hvr
    (AggInvariants.PMS_filterAllAgg g [r] hpms) (AggInvariants.SN_filterAllAgg g [r] hsn)
  exact tablesSound_of_greedy _ ad (aggOk_reviewAgg _ hvr) (SMP_filterAllAgg g hsmp hc.shape.notroot [r])
    ord hord hg

/-- info: 'AbsSat.GraphPath.Model.Greedy.tablesSound_of_greedy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tablesSound_of_greedy

/-- info: 'AbsSat.GraphPath.Model.Greedy.pinExact_of_greedy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pinExact_of_greedy

end AbsSat.GraphPath.Model.Greedy
