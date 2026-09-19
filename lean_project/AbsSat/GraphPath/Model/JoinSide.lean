-- lean_project/AbsSat/GraphPath/Model/JoinSide.lean
import AbsSat.GraphPath.Model.TripleA

/-!
# The review over a join: which side carries an entry

The distributivity of the review over the driver's joins reduces (v140) to splitting the reviewed
join's tables into two supports, one inside each side; the candidate split anchors every entry at a
common owner on the **top** step (`SupportSplit.PartSplit`), and it passes every condition at the
driver's joins (probe `split`). This module proves the part of it that is structural:

* **`entry_side`** (no hypothesis) — an entry of a state below a join that names a node **absent from
  one side** comes from the other side's tables: the join unions the owner lists, and a side's owners
  are that side's nodes.
* **`part_of_anchor`** — so, where the top step separates the sides (the driver's joins: the two sides'
  top nodes carry different parents), an entry of the reviewed join with a top anchor on side `a` is in
  `a`'s part as soon as **the entry itself** is in `a`'s tables; the anchor entries come for free.
* **`SideCover`**, **`cover_of_sideCover`** — the covering half of the split reduces to one statement:
  every entry has a top anchor on a side whose tables carry it.
-/

namespace AbsSat.GraphPath.Model.JoinSide

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.SupportSplit (RelIn TopIn Part Separates)

/-- **An entry naming a node absent from `b` comes from `a`'s tables.** -/
theorem entry_side (a b R : GPathM) (hpr : Pruned (join a b) R) (hnd : NodupIds (join a b))
    (hownB : ∀ n ∈ b.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode b q)
    (x z : PathNodeId) (m : PNodeM) (hx : R.node? x = some m) (hz : z ∈ m.owners)
    (hzb : ¬ GownersNodes.HasNode b z) : ∃ ma, a.node? x = some ma ∧ z ∈ ma.owners := by
  obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived m (List.mem_of_find?_eq_some hx)
  have hxid := node?_id_eq R x m hx
  have hjn : (join a b).node? x = some n := by rw [← hxid, hid]; exact node?_of_mem hnd n hn
  rcases join_owners_source a b x n hjn z (hown z hz) with ⟨ma, hma, hza⟩ | ⟨mb, hmb, hzb'⟩
  · exact ⟨ma, hma, hza⟩
  · exact absurd (hownB mb (List.mem_of_find?_eq_some hmb) z hzb') hzb

theorem not_hasNode_of_not_mem {b : GPathM} {z : PathNodeId} (hnd : NodupIds b) (h : ¬ Mem b z) :
    ¬ GownersNodes.HasNode b z := by
  rintro ⟨n, hn, hid⟩
  exact h ⟨n, by rw [← hid]; exact node?_of_mem hnd n hn⟩

/-- **The anchor entries come for free.** Where the top step separates the sides, an entry of the
reviewed join with a top anchor on side `a`, carried by `a`'s tables, is in `a`'s part. -/
theorem part_of_anchor (a b : GPathM) (hnd : NodupIds (join a b)) (hndB : NodupIds b)
    (hownB : ∀ n ∈ b.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode b q)
    (hsep : Separates (reviewAgg (join a b)) a b ((reviewAgg (join a b)).current_step - 1))
    (x v z : PathNodeId) (hxv : Rel (reviewAgg (join a b)) x v) (hxvA : Rel a x v)
    (hza : Mem a z) (hzs : z.id.step = (reviewAgg (join a b)).current_step - 1)
    (hxz : Rel (reviewAgg (join a b)) x z) (hvz : Rel (reviewAgg (join a b)) v z) :
    Part (reviewAgg (join a b)) a x v := by
  have hpr := pruned_reviewAgg (join a b)
  have hxz' := hxz
  obtain ⟨_, _, _, hzR⟩ := hxz'
  have hzb : ¬ GownersNodes.HasNode b z :=
    not_hasNode_of_not_mem hndB (fun hb => hsep.2.2 z hzR hzs hza hb)
  have side : ∀ y, Rel (reviewAgg (join a b)) y z → Rel a y z := by
    intro y ⟨my, hmy, hzy, _⟩
    obtain ⟨ma, hma, hzma⟩ := entry_side a b _ hpr hnd hownB y z my hmy hzy hzb
    exact ⟨ma, hma, hzma, hza⟩
  exact ⟨⟨hxv, hxvA⟩, z, ⟨hzR, hza, hzs⟩, ⟨hxz, side x hxz⟩, ⟨hvz, side v hvz⟩⟩

/-- **The covering half, reduced**: every entry of the reviewed join has a top anchor on a side whose
tables carry the entry. -/
def SideCover (a b : GPathM) : Prop :=
  ∀ x v, Rel (reviewAgg (join a b)) x v → ∃ z, z.id.step = (reviewAgg (join a b)).current_step - 1 ∧
    Rel (reviewAgg (join a b)) x z ∧ Rel (reviewAgg (join a b)) v z ∧
    ((Mem a z ∧ Rel a x v) ∨ (Mem b z ∧ Rel b x v))

/-- **The covering half of the split from `SideCover`.** -/
theorem cover_of_sideCover (a b : GPathM) (hnd : NodupIds (join a b)) (hndA : NodupIds a)
    (hndB : NodupIds b)
    (hownA : ∀ n ∈ a.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode a q)
    (hownB : ∀ n ∈ b.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode b q)
    (hsep : Separates (reviewAgg (join a b)) a b ((reviewAgg (join a b)).current_step - 1))
    (h : SideCover a b) :
    ∀ x v, Rel (reviewAgg (join a b)) x v →
      Part (reviewAgg (join a b)) a x v ∨ Part (reviewAgg (join a b)) b x v := by
  have hpr := pruned_reviewAgg (join a b)
  -- the other side: an entry naming a top node of `b` comes from `b`'s tables
  have hSwap : ∀ y z, Rel (reviewAgg (join a b)) y z → Mem b z →
      z.id.step = (reviewAgg (join a b)).current_step - 1 → Rel b y z := by
    intro y z ⟨my, hmy, hzy, hzR⟩ hzb hzs
    obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived my (List.mem_of_find?_eq_some hmy)
    have hyid := node?_id_eq _ y my hmy
    have hjn : (join a b).node? y = some n := by rw [← hyid, hid]; exact node?_of_mem hnd n hn
    rcases join_owners_source a b y n hjn z (hown z hzy) with ⟨ma, hma, hza⟩ | ⟨mb, hmb, hzb'⟩
    · have hza' := hownA ma (List.mem_of_find?_eq_some hma) z hza
      obtain ⟨na, hna, hnaid⟩ := hza'
      exact absurd (hsep.2.2 z hzR hzs ⟨na, by rw [← hnaid]; exact node?_of_mem hndA na hna⟩ hzb) id
    · exact ⟨mb, hmb, hzb', hzb⟩
  intro x v hxv
  obtain ⟨z, hzs, hxz, hvz, hside⟩ := h x v hxv
  rcases hside with ⟨hza, hxvA⟩ | ⟨hzb, hxvB⟩
  · exact Or.inl (part_of_anchor a b hnd hndB hownB hsep x v z hxv hxvA hza hzs hxz hvz)
  · have hxz' := hxz
    obtain ⟨_, _, _, hzR⟩ := hxz'
    exact Or.inr ⟨⟨hxv, hxvB⟩, z, ⟨hzR, hzb, hzs⟩, ⟨hxz, hSwap x z hxz hzb hzs⟩, ⟨hvz, hSwap v z hvz hzb hzs⟩⟩

-- ============================================================
-- Where `SideCover` has content
-- ============================================================

/-- The mirror of `entry_side`: an entry naming a node absent from `a` comes from `b`'s tables. -/
theorem entry_side_right (a b R : GPathM) (hpr : Pruned (join a b) R) (hnd : NodupIds (join a b))
    (hownA : ∀ n ∈ a.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode a q)
    (x z : PathNodeId) (m : PNodeM) (hx : R.node? x = some m) (hz : z ∈ m.owners)
    (hza : ¬ GownersNodes.HasNode a z) : ∃ mb, b.node? x = some mb ∧ z ∈ mb.owners := by
  obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived m (List.mem_of_find?_eq_some hx)
  have hxid := node?_id_eq R x m hx
  have hjn : (join a b).node? x = some n := by rw [← hxid, hid]; exact node?_of_mem hnd n hn
  rcases join_owners_source a b x n hjn z (hown z hz) with ⟨ma, hma, hza'⟩ | ⟨mb, hmb, hzb⟩
  · exact absurd (hownA ma (List.mem_of_find?_eq_some hma) z hza') hza
  · exact ⟨mb, hmb, hzb⟩

theorem mem_of_hasNode {g : GPathM} (hnd : NodupIds g) {z : PathNodeId} (h : GownersNodes.HasNode g z) :
    Mem g z := by
  obtain ⟨n, hn, hid⟩ := h
  exact ⟨n, by rw [← hid]; exact node?_of_mem hnd n hn⟩

/-- An entry of a state below a join comes from one side's tables. -/
theorem rel_side (a b R : GPathM) (hpr : Pruned (join a b) R) (hnd : NodupIds (join a b))
    (hndA : NodupIds a) (hndB : NodupIds b)
    (hownA : ∀ n ∈ a.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode a q)
    (hownB : ∀ n ∈ b.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode b q)
    {x v : PathNodeId} (h : Rel R x v) : Rel a x v ∨ Rel b x v := by
  obtain ⟨m, hm, hv, _⟩ := h
  obtain ⟨n, hn, hid, hown, _⟩ := hpr.nodes_derived m (List.mem_of_find?_eq_some hm)
  have hxid := node?_id_eq R x m hm
  have hjn : (join a b).node? x = some n := by rw [← hxid, hid]; exact node?_of_mem hnd n hn
  rcases join_owners_source a b x n hjn v (hown v hv) with ⟨ma, hma, hva⟩ | ⟨mb, hmb, hvb⟩
  · exact Or.inl ⟨ma, hma, hva, mem_of_hasNode hndA (hownA ma (List.mem_of_find?_eq_some hma) v hva)⟩
  · exact Or.inr ⟨mb, hmb, hvb, mem_of_hasNode hndB (hownB mb (List.mem_of_find?_eq_some hmb) v hvb)⟩

/-- A node of a state below a join is a node of one side. -/
theorem mem_side (a b R : GPathM) (hpr : Pruned (join a b) R) (hnd : NodupIds (join a b))
    {z : PathNodeId} (h : Mem R z) : Mem a z ∨ Mem b z := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨n, hn, hid, _, _⟩ := hpr.nodes_derived m (List.mem_of_find?_eq_some hm)
  have hzid := node?_id_eq R z m hm
  have hjn : (join a b).node? z = some n := by rw [← hzid, hid]; exact node?_of_mem hnd n hn
  rcases join_node?_source a b z n hjn with h1 | h2
  · obtain ⟨ma, hma⟩ := Option.isSome_iff_exists.mp h1; exact Or.inl ⟨ma, hma⟩
  · obtain ⟨mb, hmb⟩ := Option.isSome_iff_exists.mp h2; exact Or.inr ⟨mb, hmb⟩

/-- **Where `SideCover` has content**: entries carried by the tables of one side whose two nodes are
nodes of **both** sides. Everywhere else a top anchor is on the carrying side by structure. -/
def SharedCover (a b : GPathM) : Prop :=
  ∀ x v, Rel (reviewAgg (join a b)) x v → Mem a x → Mem b x → Mem a v → Mem b v →
    ∃ z, z.id.step = (reviewAgg (join a b)).current_step - 1 ∧
      Rel (reviewAgg (join a b)) x z ∧ Rel (reviewAgg (join a b)) v z ∧
      ((Mem a z ∧ Rel a x v) ∨ (Mem b z ∧ Rel b x v))

/-- **`SideCover` from its shared case.** Given the reviewed join's common top owner for every entry
(its own coverage rule), an entry not in the shared case has an anchor on the side carrying it. -/
theorem sideCover_of_shared (a b : GPathM) (hnd : NodupIds (join a b)) (hndA : NodupIds a)
    (hndB : NodupIds b)
    (hownA : ∀ n ∈ a.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode a q)
    (hownB : ∀ n ∈ b.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode b q)
    (hsep : Separates (reviewAgg (join a b)) a b ((reviewAgg (join a b)).current_step - 1))
    (hagg : ∀ x v, Rel (reviewAgg (join a b)) x v → ∃ z,
      z.id.step = (reviewAgg (join a b)).current_step - 1 ∧
        Rel (reviewAgg (join a b)) x z ∧ Rel (reviewAgg (join a b)) v z)
    (hS : SharedCover a b) : SideCover a b := by
  have hpr := pruned_reviewAgg (join a b)
  intro x v hxv
  obtain ⟨z, hzs, hxz, hvz⟩ := hagg x v hxv
  have hxz' := hxz
  obtain ⟨_, _, _, hzR⟩ := hxz'
  have fromA : Mem a z → ∀ y, Rel (reviewAgg (join a b)) y z → Mem a y := by
    intro hza y ⟨my, hmy, hzy, _⟩
    obtain ⟨ma, hma, _⟩ := entry_side a b _ hpr hnd hownB y z my hmy hzy
      (not_hasNode_of_not_mem hndB (fun hb => hsep.2.2 z hzR hzs hza hb))
    exact ⟨ma, hma⟩
  have fromB : Mem b z → ∀ y, Rel (reviewAgg (join a b)) y z → Mem b y := by
    intro hzb y ⟨my, hmy, hzy, _⟩
    obtain ⟨mb, hmb, _⟩ := entry_side_right a b _ hpr hnd hownA y z my hmy hzy
      (not_hasNode_of_not_mem hndA (fun ha => hsep.2.2 z hzR hzs ha hzb))
    exact ⟨mb, hmb⟩
  have relMem : ∀ {g : GPathM} {p q : PathNodeId}, Rel g p q → Mem g p ∧ Mem g q := by
    intro g p q ⟨m, hm, _, hq⟩; exact ⟨⟨m, hm⟩, hq⟩
  rcases mem_side a b _ hpr hnd hzR with hza | hzb
  · rcases rel_side a b _ hpr hnd hndA hndB hownA hownB hxv with hA | hB
    · exact ⟨z, hzs, hxz, hvz, Or.inl ⟨hza, hA⟩⟩
    · exact hS x v hxv (fromA hza x hxz) (relMem hB).1 (fromA hza v hvz) (relMem hB).2
  · rcases rel_side a b _ hpr hnd hndA hndB hownA hownB hxv with hA | hB
    · exact hS x v hxv (relMem hA).1 (fromB hzb x hxz) (relMem hA).2 (fromB hzb v hvz)
    · exact ⟨z, hzs, hxz, hvz, Or.inr ⟨hzb, hB⟩⟩

/-- info: 'AbsSat.GraphPath.Model.JoinSide.sideCover_of_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sideCover_of_shared

-- ============================================================
-- `SideCover` from exact sides
-- ============================================================

/-- Two nodes of a sound chain are an entry of the state. -/
theorem rel_of_chain (g : GPathM) (sel : Int → PathNodeId) (h : ChainSound g sel) (i j : Int)
    (hi0 : 0 ≤ i) (hi1 : i < g.current_step) (hj0 : 0 ≤ j) (hj1 : j < g.current_step) :
    Rel g (sel j) (sel i) := by
  obtain ⟨hsj, _⟩ := h.chain.1.1 j hj0 hj1
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsj
  obtain ⟨hsi, hsti⟩ := h.chain.1.1 i hi0 hi1
  obtain ⟨mi, hmi⟩ := Option.isSome_iff_exists.mp hsi
  have hown : sel i ∈ m.owners := by
    by_cases hij : i = j
    · have := h.self_owned j hj0 hj1
      unfold ownersOf at this
      rw [hm] at this
      rw [hij]; exact this
    · have := h.chain.2.1 i j hi0 hj0 hi1 hj1 hij
      unfold ownersOf at this
      rw [hm] at this
      exact (List.mem_filter.mp this).1
  exact ⟨m, hm, hown, mi, hmi⟩

/-- **`SideCover` from exact sides.** If both sides' tables are exact, an entry of the reviewed join
carried by a side lies on a path of that side; the path survives the join and the review, and its top
node is an anchor on that side. -/
theorem sideCover_of_sound (a b : GPathM) (hok : okJoin a b = true) (hnd : NodupIds (join a b))
    (hndA : NodupIds a) (hndB : NodupIds b)
    (hownA : ∀ n ∈ a.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode a q)
    (hownB : ∀ n ∈ b.nodes, ∀ q ∈ n.owners, GownersNodes.HasNode b q)
    (hbA : ∀ p, Mem a p → 0 ≤ p.id.step ∧ p.id.step < a.current_step)
    (hbB : ∀ p, Mem b p → 0 ≤ p.id.step ∧ p.id.step < b.current_step)
    (hta : Exactness.TablesSound a) (htb : Exactness.TablesSound b) : SideCover a b := by
  have hpr := pruned_reviewAgg (join a b)
  have gA := grown_join_left a b
  have gB := grown_join_right a b hok
  have hcsA : (reviewAgg (join a b)).current_step = a.current_step := hpr.step_eq.trans gA.step_eq.symm
  have hcsB : (reviewAgg (join a b)).current_step = b.current_step := hpr.step_eq.trans gB.step_eq
  have lift : ∀ (g : GPathM), Grown g (join a b) → (reviewAgg (join a b)).current_step = g.current_step →
      (∀ p, Mem g p → 0 ≤ p.id.step ∧ p.id.step < g.current_step) → Exactness.TablesSound g →
      ∀ x v, Rel g x v → ∃ z, z.id.step = (reviewAgg (join a b)).current_step - 1 ∧
        Rel (reviewAgg (join a b)) x z ∧ Rel (reviewAgg (join a b)) v z ∧ Mem g z := by
    intro g hg hcs hb ht x v ⟨m, hm, hv, hmv⟩
    obtain ⟨hx0, hx1⟩ := hb x ⟨m, hm⟩
    obtain ⟨hv0, hv1⟩ := hb v hmv
    obtain ⟨sel, hsc, hsx, hsv⟩ := ht x m hm hx0 hx1 v hv0 hv1 hv
    have hscR := ChainSound_reviewAgg _ sel (ChainSound_of_grown hg sel hsc)
    have htop0 : 0 ≤ g.current_step - 1 := by omega
    refine ⟨sel (g.current_step - 1), ?_, ?_, ?_, ?_⟩
    · rw [hcs]; exact (hsc.chain.1.1 _ htop0 (by omega)).2
    · have := rel_of_chain _ sel hscR (g.current_step - 1) x.id.step (by omega) (by rw [hcs]; omega)
        hx0 (by rw [hcs]; exact hx1)
      rw [hsx] at this; exact this
    · have := rel_of_chain _ sel hscR (g.current_step - 1) v.id.step (by omega) (by rw [hcs]; omega)
        hv0 (by rw [hcs]; exact hv1)
      rw [hsv] at this; exact this
    · obtain ⟨hs, _⟩ := hsc.chain.1.1 _ htop0 (by omega)
      obtain ⟨mz, hmz⟩ := Option.isSome_iff_exists.mp hs
      exact ⟨mz, hmz⟩
  intro x v hxv
  rcases rel_side a b _ hpr hnd hndA hndB hownA hownB hxv with hA | hB
  · obtain ⟨z, hzs, hxz, hvz, hza⟩ := lift a gA hcsA hbA hta x v hA
    exact ⟨z, hzs, hxz, hvz, Or.inl ⟨hza, hA⟩⟩
  · obtain ⟨z, hzs, hxz, hvz, hzb⟩ := lift b gB hcsB hbB htb x v hB
    exact ⟨z, hzs, hxz, hvz, Or.inr ⟨hzb, hB⟩⟩

/-- info: 'AbsSat.GraphPath.Model.JoinSide.sideCover_of_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sideCover_of_sound

/-- info: 'AbsSat.GraphPath.Model.JoinSide.cover_of_sideCover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cover_of_sideCover

end AbsSat.GraphPath.Model.JoinSide
