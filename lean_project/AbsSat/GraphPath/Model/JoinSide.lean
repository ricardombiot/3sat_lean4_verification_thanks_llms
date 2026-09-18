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

/-- info: 'AbsSat.GraphPath.Model.JoinSide.cover_of_sideCover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cover_of_sideCover

end AbsSat.GraphPath.Model.JoinSide
