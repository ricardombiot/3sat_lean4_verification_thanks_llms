-- lean/improves_bingo/AbsSatBingo/Model/UnionEquiv.lean
import AbsSatBingo.Model.SideLinks

/-!
# `KernelUnion` ⇔ `SplitAt` ∧ `SidePinned`

El recíproco de `kernelUnion_of_split`: con los lados exactos (`KernelExact`) y la separación por el origen,
`KernelUnion` da `SplitAt` (por `kernel_split` en el lado y la monotonía: toda estructura cerrada de un lado lo es de
la unión) y `SidePinned` (fijada en un origen de `e`, el núcleo de `g` está vacío). Así que `SplitAt` no es más débil
que `KernelUnion` una vez se tiene `SidePinned`: es donde vive la mezcla de los dos lados.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- El documento de la unión de un nodo de `e` tiene al menos sus enlaces. -/
theorem node?_join_left_sup {e g : GPathB} {x : PathNodeId} {n : PNodeB} (h : e.node? x = some n) :
    ∃ n', (join e g).node? x = some n' ∧ (∀ p ∈ n.parents, p ∈ n'.parents) ∧ (∀ s ∈ n.sons, s ∈ n'.sons) := by
  rw [node?_join, h]
  simp only [Option.map_some, Option.some_or]
  refine ⟨_, rfl, ?_, ?_⟩
  · intro p hp; split
    · exact mem_merge_parents_left hp
    · exact hp
  · intro s hs; split
    · exact mem_merge_sons_left hs
    · exact hs

/-- El documento de la unión de un nodo de `g` tiene al menos sus enlaces. -/
theorem node?_join_right_sup {e g : GPathB} {x : PathNodeId} {m : PNodeB} (h : g.node? x = some m) :
    ∃ n', (join e g).node? x = some n' ∧ (∀ p ∈ m.parents, p ∈ n'.parents) ∧ (∀ s ∈ m.sons, s ∈ n'.sons) := by
  rw [node?_join]
  cases hn : e.node? x with
  | some n =>
    have hnid := node?_id hn
    simp only [Option.map_some, Option.some_or]
    rw [hnid, h]
    exact ⟨_, rfl, fun p hp => mem_merge_parents hp, fun s hs => mem_merge_sons hs⟩
  | none =>
    simp only [Option.map_none, Option.none_or]
    rw [find?_filter_of]
    · exact ⟨m, h, fun _ hp => hp, fun _ hs => hs⟩
    · intro a _ ha
      have : a.id = x := by simpa using ha
      rw [this, hn]; rfl

/-- **Una estructura cerrada de un lado lo es de la unión** (a izquierda). -/
theorem secStruct_join_left {e g : GPathB} {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    (hst : SecStruct e V R) : SecStruct (join e g) V R := by
  have hn : ∀ {x n'}, V x → (join e g).node? x = some n' → ∃ n, e.node? x = some n ∧
      (∀ p ∈ n.parents, p ∈ n'.parents) ∧ (∀ s ∈ n.sons, s ∈ n'.sons) := by
    intro x n' hx h
    obtain ⟨n, hn, _⟩ := hst.node hx
    obtain ⟨n'', h'', hp, hs⟩ := node?_join_left_sup (g := g) hn
    rw [h] at h''; cases h''
    exact ⟨n, hn, hp, hs⟩
  refine ⟨fun hy => (alive_join e g _).mpr (Or.inl (hst.alive hy)), hst.refl, hst.symm, hst.dom,
    fun h => adj_join_left (hst.adj h), fun h l h0 h1 => hst.pair h l h0 h1, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn', hpar, hson⟩ := hst.node hy
    obtain ⟨n', h', hp, hs⟩ := node?_join_left_sup (g := g) hn'
    refine ⟨n', h', fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨p, hp', hyp⟩ := hpar hk; exact ⟨p, hp p hp', hyp⟩
    · obtain ⟨s, hs', hys⟩ := hson hk; exact ⟨s, hs s hs', hys⟩
  · intro x w n' hxw hne h' h1
    obtain ⟨n, hn', hp, _⟩ := hn (hst.dom hxw).1 h'
    obtain ⟨p, hp', hxp, hpw⟩ := hst.par hxw hne hn' h1
    exact ⟨p, hp p hp', hxp, hpw⟩
  · intro x w n' hxw hne h' h1
    obtain ⟨n, hn', _, hs⟩ := hn (hst.dom hxw).1 h'
    obtain ⟨s, hs', hxs, hsw⟩ := hst.son hxw hne hn' h1
    exact ⟨s, hs s hs', hxs, hsw⟩

/-- **Y a derecha** (con el mismo paso). -/
theorem secStruct_join_right {e g : GPathB} (hcs : e.current_step = g.current_step) {V : PathNodeId → Prop}
    {R : PathNodeId → PathNodeId → Prop} (hst : SecStruct g V R) : SecStruct (join e g) V R := by
  have hstep : (join e g).current_step = g.current_step := hcs
  have hn : ∀ {x n'}, V x → (join e g).node? x = some n' → ∃ m, g.node? x = some m ∧
      (∀ p ∈ m.parents, p ∈ n'.parents) ∧ (∀ s ∈ m.sons, s ∈ n'.sons) := by
    intro x n' hx h
    obtain ⟨m, hm, _⟩ := hst.node hx
    obtain ⟨n'', h'', hp, hs⟩ := node?_join_right_sup (e := e) hm
    rw [h] at h''; cases h''
    exact ⟨m, hm, hp, hs⟩
  refine ⟨fun hy => (alive_join e g _).mpr (Or.inr (hst.alive hy)), hst.refl, hst.symm, hst.dom,
    fun h => adj_join_right (hst.adj h), fun h l h0 h1 => hst.pair h l h0 (hstep ▸ h1), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨m, hm, hpar, hson⟩ := hst.node hy
    obtain ⟨n', h', hp, hs⟩ := node?_join_right_sup (e := e) hm
    refine ⟨n', h', fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨p, hp', hyp⟩ := hpar hk; exact ⟨p, hp p hp', hyp⟩
    · obtain ⟨s, hs', hys⟩ := hson (hstep ▸ hk); exact ⟨s, hs s hs', hys⟩
  · intro x w n' hxw hne h' h1
    obtain ⟨m, hm, hp, _⟩ := hn (hst.dom hxw).1 h'
    obtain ⟨p, hp', hxp, hpw⟩ := hst.par hxw hne hm h1
    exact ⟨p, hp p hp', hxp, hpw⟩
  · intro x w n' hxw hne h' h1
    obtain ⟨m, hm, _, hs⟩ := hn (hst.dom hxw).1 h'
    obtain ⟨s, hs', hxs, hsw⟩ := hst.son hxw hne hm (hstep ▸ h1)
    exact ⟨s, hs s hs', hxs, hsw⟩

theorem kernel_join_left {e g : GPathB} {P : List NodeId} {y w : PathNodeId} (h : Kernel e P y w) :
    Kernel (join e g) P y w := by
  obtain ⟨V, R, hst, ha, hr⟩ := h
  exact ⟨V, R, secStruct_join_left hst, ha, hr⟩

theorem kernel_join_right {e g : GPathB} (hcs : e.current_step = g.current_step) {P : List NodeId}
    {y w : PathNodeId} (h : Kernel g P y w) : Kernel (join e g) P y w := by
  obtain ⟨V, R, hst, ha, hr⟩ := h
  exact ⟨V, R, secStruct_join_right hcs hst, ha, hr⟩

/-- Fijado en un nodo del mapa sin vivos en `g`, el núcleo de `g` está vacío. -/
theorem kernel_empty_of_off {g : GPathB} {b : NodeId} (hoff : OffSide g b) (hb0 : 0 ≤ b.step)
    (hbc : b.step < g.current_step) {P : List NodeId} {y w : PathNodeId} (h : Kernel g (P ++ [b]) y w) : False := by
  obtain ⟨V, R, hst, ha, hr⟩ := h
  have hy := (hst.dom hr).1
  obtain ⟨r, hrs, hyr, _⟩ := hst.pair (hst.refl hy) b.step hb0 hbc
  have hrb : r.id = b := ha b (List.mem_append_right _ (List.mem_singleton_self b)) (hst.dom hyr).2 hrs
  exact hoff r (hst.alive (hst.dom hyr).2) hrb

/-- **`KernelUnion` da `SplitAt`** con los lados exactos. -/
theorem splitAt_of_kernelUnion {e g : GPathB} {k : Int} (hk0 : 0 ≤ k) (hkc : k < e.current_step)
    (hcs : e.current_step = g.current_step) (hke : KernelExact e) (hkg : KernelExact g) (hu : KernelUnion e g) :
    SplitAt (join e g) k := by
  intro P y w h
  rcases hu P y w h with h | h
  · obtain ⟨b, hb, h'⟩ := kernel_split hke h hk0 hkc
    exact ⟨b, hb, kernel_join_left h'⟩
  · obtain ⟨b, hb, h'⟩ := kernel_split hkg h hk0 (hcs ▸ hkc)
    exact ⟨b, hb, kernel_join_right hcs h'⟩

/-- **`KernelUnion` da `SidePinned`** con la separación. -/
theorem sidePinned_of_kernelUnion {e g : GPathB} {k : Int} (hk0 : 0 ≤ k) (hkc : k < e.current_step)
    (hcs : e.current_step = g.current_step) (hsep : SepAt e g k) (hu : KernelUnion e g) :
    SidePinned (join e g) e g k := by
  intro b hb
  rcases hsep b hb with hoff | hoff
  · refine Or.inl (fun P y w h => ?_)
    rcases hu _ y w h with h | h
    · exact h
    · exact (kernel_empty_of_off hoff (hb ▸ hk0) (hcs ▸ hb ▸ hkc) h).elim
  · refine Or.inr (fun P y w h => ?_)
    rcases hu _ y w h with h | h
    · exact (kernel_empty_of_off hoff (hb ▸ hk0) (hb ▸ hkc) h).elim
    · exact h

/-- **`KernelUnion` ⇔ `SplitAt` ∧ `SidePinned`** en el paso de origen, con los lados exactos y la separación. -/
theorem kernelUnion_iff_split {e g : GPathB} {k : Int} (hk0 : 0 ≤ k) (hkc : k < e.current_step)
    (hcs : e.current_step = g.current_step) (hke : KernelExact e) (hkg : KernelExact g) (hsep : SepAt e g k) :
    KernelUnion e g ↔ SplitAt (join e g) k ∧ SidePinned (join e g) e g k :=
  ⟨fun hu => ⟨splitAt_of_kernelUnion hk0 hkc hcs hke hkg hu, sidePinned_of_kernelUnion hk0 hkc hcs hsep hu⟩,
   fun ⟨hs, hp⟩ => kernelUnion_of_split hs hp⟩

end GPathB

end AbsSatBingo.Model
