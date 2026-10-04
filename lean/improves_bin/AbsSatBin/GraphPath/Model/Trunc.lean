-- lean/improves_bin/AbsSatBin/GraphPath/Model/Trunc.lean
import AbsSatBin.GraphPath.Model.KernelUp

/-!
# Cutting the top row off a kernel

`trunc g` drops the top row of `g`: its nodes, their ids from every table and son list, and the global owners of
that step. **`kernel_trunc`**: the truncation of a kernel (whose links go one step up or down) is a kernel — every
condition of the kernel below the top only mentions steps below the top, except a node's support by its sons at the
step just under the top, which the truncation no longer asks for.

Used for the prohibited window (`LineUnion`): the piece with a skipped window, without its top row, sits below its
source pinned at the requirements and at `L1 = 1`.
-/

namespace AbsSatBin.GraphPath.Model.Trunc

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel

/-- A node with the ids of step `t` dropped from its owners and sons. -/
def cutTop (t : Int) (n : PNodeM) : PNodeM :=
  { n with owners := n.owners.filter (fun q => q.id.step != t), sons := n.sons.filter (fun q => q.id.step != t) }

/-- `g` without its top row. -/
def trunc (g : GPathM) : GPathM :=
  { g with
    nodes := (g.nodes.filter (fun n => n.id.id.step != g.current_step - 1)).map (cutTop (g.current_step - 1)),
    gowners := g.gowners.filter (fun q => q.id.step != g.current_step - 1),
    current_step := g.current_step - 1 }

theorem mem_cutTop_owners (t : Int) (n : PNodeM) (q : PathNodeId) :
    q ∈ (cutTop t n).owners ↔ q ∈ n.owners ∧ q.id.step ≠ t := by
  simp [cutTop]

theorem mem_cutTop_sons (t : Int) (n : PNodeM) (q : PathNodeId) :
    q ∈ (cutTop t n).sons ↔ q ∈ n.sons ∧ q.id.step ≠ t := by
  simp [cutTop]

theorem find_filter (t : Int) (p : PathNodeId) :
    ∀ l : List PNodeM, (l.filter (fun n => n.id.id.step != t)).find? (fun n => n.id == p) =
      if p.id.step = t then none else l.find? (fun n => n.id == p) := by
  intro l
  induction l with
  | nil => split <;> rfl
  | cons a as ih =>
    rw [List.filter_cons, List.find?_cons]
    by_cases ha : a.id.id.step = t
    · have : (a.id.id.step != t) = false := by simp [ha]
      rw [this, if_neg (by simp), ih]
      by_cases hp : p.id.step = t
      · rw [if_pos hp, if_pos hp]
      · rw [if_neg hp, if_neg hp]
        cases hb : a.id == p with
        | false => rfl
        | true => exact absurd (by rw [← eq_of_beq hb]; exact ha) hp
    · have : (a.id.id.step != t) = true := by simp [ha]
      rw [this, if_pos rfl, List.find?_cons, ih]
      cases hb : a.id == p with
      | false => rfl
      | true =>
        have hp : ¬ p.id.step = t := by rw [← eq_of_beq hb]; exact ha
        simp only [if_neg hp]

theorem trunc_node? (g : GPathM) (p : PathNodeId) :
    (trunc g).node? p =
      if p.id.step = g.current_step - 1 then none else (g.node? p).map (cutTop (g.current_step - 1)) := by
  have hf : (fun x : PNodeM => (cutTop (g.current_step - 1) x).id == p) = (fun x : PNodeM => x.id == p) := rfl
  simp only [node?, trunc, List.find?_map, Function.comp_def, hf]
  rw [find_filter]
  split <;> rfl

theorem trunc_node?_some (g : GPathM) (p : PathNodeId) (n' : PNodeM) (h : (trunc g).node? p = some n') :
    ∃ n, g.node? p = some n ∧ p.id.step ≠ g.current_step - 1 ∧ n' = cutTop (g.current_step - 1) n := by
  rw [trunc_node?] at h
  split at h
  · cases h
  · next hp =>
    cases e : g.node? p with
    | none => rw [e] at h; cases h
    | some n => rw [e] at h; exact ⟨n, rfl, hp, (Option.some.inj h).symm⟩

theorem trunc_node?_of (g : GPathM) (p : PathNodeId) (n : PNodeM) (h : g.node? p = some n)
    (hp : p.id.step ≠ g.current_step - 1) : (trunc g).node? p = some (cutTop (g.current_step - 1) n) := by
  rw [trunc_node?, if_neg hp, h]; rfl

/-- **The truncation of a kernel is a kernel.** -/
theorem kernel_trunc {g : GPathM} (hk : Kernel g) (hpb : Parents.PBelow g) (hsa : Sons.SAbove g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) : Kernel (trunc g) := by
  have hcs : (trunc g).current_step = g.current_step - 1 := rfl
  have hstep : ∀ p n, g.node? p = some n → p.id.step < g.current_step := by
    intro p n h; have := hbelow n (List.mem_of_find?_eq_some h); rwa [node?_id_eq g p n h] at this
  have hgow : ∀ q, q ∈ (trunc g).gowners ↔ q ∈ g.gowners ∧ q.id.step ≠ g.current_step - 1 := by
    intro q; simp [trunc]
  have up : ∀ p n, g.node? p = some n → p.id.step ≠ g.current_step - 1 → ∀ q ∈ n.owners,
      q.id.step ≠ g.current_step - 1 → q ∈ (cutTop (g.current_step - 1) n).owners :=
    fun _ _ _ _ q hq hqs => (mem_cutTop_owners _ _ q).mpr ⟨hq, hqs⟩
  refine
    { gow := ?_, gn := ?_, own := ?_, valid := ?_, sym := ?_, linkP := ?_, linkS := ?_, pair := ?_,
      nbrP := ?_, nbrS := ?_ }
  -- gow
  · intro p n' hn'
    obtain ⟨n, hn, hp, rfl⟩ := trunc_node?_some g p n' hn'
    exact (hgow p).mpr ⟨hk.gow p n hn, hp⟩
  -- gn
  · intro q hq
    obtain ⟨hq, hqs⟩ := (hgow q).mp hq
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hk.gn q hq)
    rw [trunc_node?_of g q n hn hqs]; rfl
  -- own
  · intro p n' hn' v hv
    obtain ⟨n, hn, _, rfl⟩ := trunc_node?_some g p n' hn'
    obtain ⟨hv, hvs⟩ := (mem_cutTop_owners _ _ v).mp hv
    exact (hgow v).mpr ⟨hk.own p n hn v hv, hvs⟩
  -- valid
  · intro p n' hn'
    obtain ⟨n, hn, hp, rfl⟩ := trunc_node?_some g p n' hn'
    have hps := hstep p n hn
    have hid := node?_id_eq g p n hn
    obtain ⟨hall, h2, h3⟩ := (isValidNode_iff g n).mp (hk.valid p n hn)
    refine (isValidNode_iff _ _).mpr ⟨List.all_eq_true.mpr (fun k hkr => ?_), h2, ?_⟩
    · have h0 := mem_intRange_lower hkr
      have h1 := mem_intRange_upper hkr
      rw [hcs] at h1
      obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall k (mem_intRange_zero k _ h0 (by omega)))
      exact List.any_eq_true.mpr ⟨q, up p n hn hp q hq (by rw [eq_of_beq hqs]; omega), hqs⟩
    · by_cases htop : p.id.step = g.current_step - 1 - 1
      · left; show ((cutTop _ n).id.id.step == (trunc g).current_step - 1) = true
        rw [hcs]; exact beq_iff_eq.mpr (by show n.id.id.step = _; rw [hid]; exact htop)
      · right
        rcases h3 with h | h
        · exact absurd (by rw [← hid]; exact eq_of_beq h) hp
        · obtain ⟨sn, hsn⟩ := List.exists_mem_of_ne_nil _ h
          have := hsa n (List.mem_of_find?_eq_some hn) sn hsn
          rw [hid] at this
          exact List.ne_nil_of_mem ((mem_cutTop_sons _ _ sn).mpr ⟨hsn, by omega⟩)
  -- sym
  · intro p n' q m' hn' hm' hq
    obtain ⟨n, hn, hp, rfl⟩ := trunc_node?_some g p n' hn'
    obtain ⟨m, hm, hqs, rfl⟩ := trunc_node?_some g q m' hm'
    exact up q m hm hqs p (hk.sym p n q m hn hm ((mem_cutTop_owners _ _ q).mp hq).1) hp
  -- linkP
  · intro p n' hn' c hc
    obtain ⟨n, hn, hp, rfl⟩ := trunc_node?_some g p n' hn'
    have hc' : c ∈ n.parents := hc
    obtain ⟨hco, nc, hnc, hpo⟩ := hk.linkP p n hn c hc'
    have hcs' := hpb n (List.mem_of_find?_eq_some hn) c hc'
    rw [node?_id_eq g p n hn] at hcs'
    have hps := hstep p n hn
    have hcn : c.id.step ≠ g.current_step - 1 := by omega
    exact ⟨up p n hn hp c hco hcn, _, trunc_node?_of g c nc hnc hcn, up c nc hnc hcn p hpo hp⟩
  -- linkS
  · intro p n' hn' c hc
    obtain ⟨n, hn, hp, rfl⟩ := trunc_node?_some g p n' hn'
    obtain ⟨hc', hcn⟩ := (mem_cutTop_sons _ _ c).mp hc
    obtain ⟨hco, nc, hnc, hpo⟩ := hk.linkS p n hn c hc'
    exact ⟨up p n hn hp c hco hcn, _, trunc_node?_of g c nc hnc hcn, up c nc hnc hcn p hpo hp⟩
  -- pair
  · intro p n' w nw' hn' hnw' hw k h0 h1
    obtain ⟨n, hn, hp, rfl⟩ := trunc_node?_some g p n' hn'
    obtain ⟨nw, hnw, hws, rfl⟩ := trunc_node?_some g w nw' hnw'
    rw [hcs] at h1
    obtain ⟨r, hr1, hr2, hrs⟩ := hk.pair p n w nw hn hnw ((mem_cutTop_owners _ _ w).mp hw).1 k h0 (by omega)
    exact ⟨r, up p n hn hp r hr1 (by omega), up w nw hnw hws r hr2 (by omega), hrs⟩
  -- nbrP
  · intro p n' hn' h1 v hv
    obtain ⟨n, hn, hp, rfl⟩ := trunc_node?_some g p n' hn'
    obtain ⟨hv, hvs⟩ := (mem_cutTop_owners _ _ v).mp hv
    obtain ⟨c, hc, nc, hnc, hvc⟩ := hk.nbrP p n hn h1 v hv
    have hcs' := hpb n (List.mem_of_find?_eq_some hn) c hc
    rw [node?_id_eq g p n hn] at hcs'
    have hps := hstep p n hn
    have hcn : c.id.step ≠ g.current_step - 1 := by omega
    exact ⟨c, hc, _, trunc_node?_of g c nc hnc hcn, up c nc hnc hcn v hvc hvs⟩
  -- nbrS
  · intro p n' hn' h2 v hv
    obtain ⟨n, hn, hp, rfl⟩ := trunc_node?_some g p n' hn'
    obtain ⟨hv, hvs⟩ := (mem_cutTop_owners _ _ v).mp hv
    rw [hcs] at h2
    obtain ⟨c, hc, nc, hnc, hvc⟩ := hk.nbrS p n hn (by omega) v hv
    have hcs' := hsa n (List.mem_of_find?_eq_some hn) c hc
    rw [node?_id_eq g p n hn] at hcs'
    have hcn : c.id.step ≠ g.current_step - 1 := by omega
    exact ⟨c, (mem_cutTop_sons _ _ c).mpr ⟨hc, hcn⟩, _, trunc_node?_of g c nc hnc hcn, up c nc hnc hcn v hvc hvs⟩

/-- info: 'AbsSatBin.GraphPath.Model.Trunc.kernel_trunc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kernel_trunc

end AbsSatBin.GraphPath.Model.Trunc
