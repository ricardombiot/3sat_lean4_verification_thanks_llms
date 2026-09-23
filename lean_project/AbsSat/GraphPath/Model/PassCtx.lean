-- lean_project/AbsSat/GraphPath/Model/PassCtx.lean
import AbsSat.GraphPath.Model.TopGoodLadder

/-!
# Lo que las pasadas de padres e hijos conservan, nodo a nodo

Las pruebas nodo a nodo de `SegReview` piden condiciones sobre el estado intermedio. Medido
(`row-degree passhyp`, semilla 1, antes de cada nodo de las dos pasadas): padres vivos, hijos vivos
y autoposesión nunca fallan. Aquí se demuestra que `reviewNode` las conserva.

La clave es una sola observación: `reviewNode x` solo puede eliminar el nodo `x`, y cuando lo hace lo
desenlaza de todos (`removeNode` filtra `x` de todas las listas de padres e hijos).
-/

namespace AbsSat.GraphPath.Model.PassCtx

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.NodeIds (Ids ids_updateAt ids_unlinkIncompatible)

/-- **Padres vivos**: los padres de un nodo son nodos. -/
def PLive (g : GPathM) : Prop :=
  ∀ y ny, g.node? y = some ny → ∀ p ∈ ny.parents, (g.node? p).isSome

theorem mem_ids_of_node (g : GPathM) (y : PathNodeId) (h : (g.node? y).isSome) : y ∈ Ids g := by
  obtain ⟨n, hn, hid⟩ := (GownersNodes.hasNode_iff g y).mpr h
  exact List.mem_map.mpr ⟨n, hn, hid⟩

theorem node_of_mem_ids (g : GPathM) (y : PathNodeId) (h : y ∈ Ids g) : (g.node? y).isSome := by
  obtain ⟨n, hn, hid⟩ := List.mem_map.mp h
  exact (GownersNodes.hasNode_iff g y).mp ⟨n, hn, hid⟩

theorem mem_ids_removeNode (g : GPathM) (x y : PathNodeId) (h : y ∈ Ids g) (hne : y ≠ x) :
    y ∈ Ids (removeNode g x) := by
  obtain ⟨n, hn, hid⟩ := List.mem_map.mp h
  refine List.mem_map.mpr ⟨unlink x n, ?_, hid⟩
  rw [removeNode_nodes]
  refine List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨hn, ?_⟩, rfl⟩
  rw [hid]; exact bne_iff_ne.mpr hne

/-- En un estado del que se ha eliminado `x`, nadie tiene a `x` por padre. -/
theorem not_parent_removeNode (g : GPathM) (x : PathNodeId) (n : PNodeM)
    (hn : n ∈ (removeNode g x).nodes) : x ∉ n.parents := by
  rw [removeNode_nodes] at hn
  obtain ⟨n0, _, rfl⟩ := List.mem_map.mp hn
  intro h
  have := (List.mem_filter.mp h).2
  simp at this

/-- **`reviewNode x` solo puede eliminar `x`.** -/
theorem survives_reviewNode (g : GPathM) (nb : PNodeM → List PathNodeId) (x y : PathNodeId)
    (hy : (g.node? y).isSome) (hne : y ≠ x) : ((reviewNode g nb x).node? y).isSome := by
  apply node_of_mem_ids
  have hy' := mem_ids_of_node g y hy
  unfold reviewNode
  cases hn : g.node? x with
  | none => exact hy'
  | some d =>
    simp only
    have hup : Ids (updateAt g x
        (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) }))
        = Ids g := ids_updateAt g x _ (fun _ => rfl)
    have hunl := ids_unlinkIncompatible
      (updateAt g x
        (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x
    split
    · split
      · rw [hunl, hup]; exact hy'
      · exact mem_ids_removeNode _ x y (by rw [hunl, hup]; exact hy') hne
    · exact mem_ids_removeNode g x y hy' hne

/-- **Si `reviewNode x` elimina `x`, nadie lo tiene por padre** (con padres vivos antes). -/
theorem not_parent_of_removed (g : GPathM) (hnd : NodupIds g) (hpl : PLive g)
    (nb : PNodeM → List PathNodeId) (x : PathNodeId)
    (hgone : ((reviewNode g nb x).node? x).isSome = false) :
    ∀ n ∈ (reviewNode g nb x).nodes, x ∉ n.parents := by
  cases hn : g.node? x with
  | none =>
    have hR : reviewNode g nb x = g := by unfold reviewNode; rw [hn]
    rw [hR]
    intro n hnm hx
    have hnode : g.node? n.id = some n := node?_of_mem hnd n hnm
    have := hpl n.id n hnode x hx
    rw [hn] at this
    exact Bool.false_ne_true this
  | some d =>
    have hxin : x ∈ Ids g := mem_ids_of_node g x (by rw [hn]; rfl)
    unfold reviewNode at hgone ⊢
    simp only [hn] at hgone ⊢
    split
    · split
      · rename_i hv1 hv2
        exfalso
        rw [if_pos hv1, if_pos hv2] at hgone
        have hup : Ids (updateAt g x
            (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) }))
            = Ids g := ids_updateAt g x _ (fun _ => rfl)
        have hunl := ids_unlinkIncompatible
          (updateAt g x
            (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x
        have := node_of_mem_ids _ x (by rw [hunl, hup]; exact hxin)
        rw [this] at hgone
        exact Bool.noConfusion hgone
      · exact fun n hn' => not_parent_removeNode _ x n hn'
    · exact fun n hn' => not_parent_removeNode g x n hn'

/-- **`reviewNode` conserva los padres vivos.** -/
theorem pLive_reviewNode (g : GPathM) (hnd : NodupIds g) (hpl : PLive g)
    (nb : PNodeM → List PathNodeId) (x : PathNodeId) : PLive (reviewNode g nb x) := by
  have hpr := pruned_reviewNode nb x g
  intro y ny hy p hp
  obtain ⟨n0, hn0, hid0, _, hpar0⟩ := hpr.nodes_derived ny (List.mem_of_find?_eq_some hy)
  have hyid : ny.id = y := node?_id_eq _ y ny hy
  have hn0g : g.node? y = some n0 := by rw [← hyid, hid0]; exact node?_of_mem hnd n0 hn0
  have hpg := hpl y n0 hn0g p (hpar0 p hp)
  cases hx : ((reviewNode g nb x).node? x).isSome with
  | true =>
    if hpx : p = x then rw [hpx]; exact hx
    else exact survives_reviewNode g nb x p hpg hpx
  | false =>
    have hnot := not_parent_of_removed g hnd hpl nb x hx ny (List.mem_of_find?_eq_some hy)
    have hpx : p ≠ x := fun h => hnot (h ▸ hp)
    exact survives_reviewNode g nb x p hpg hpx

/-- info: 'AbsSat.GraphPath.Model.PassCtx.pLive_reviewNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pLive_reviewNode

-- ============================================================
-- La autoposesión
-- ============================================================

/-- **Cada nodo vivo se posee a sí mismo.** -/
def SelfL (g : GPathM) : Prop := ∀ y ny, g.node? y = some ny → y ∈ ny.owners

/-- Si `reviewNode x` deja vivo a `x`, su nueva tabla tiene entrada en cada paso. -/
theorem owners_ok_of_kept (g : GPathM) (nb : PNodeM → List PathNodeId) (x : PathNodeId)
    (d : PNodeM) (hd : g.node? x = some d) (nx : PNodeM)
    (hx : (reviewNode g nb x).node? x = some nx) :
    (intRange 0 (g.current_step - 1)).all
      (fun k => hasStepEntry (intersectOwners d.owners (unionOwnersOf g (nb d))) k) = true := by
  unfold reviewNode at hx
  rw [hd] at hx
  simp only at hx
  split at hx
  · split at hx
    · rename_i _ hv2
      have hok := owners_ok_of_isValidNode _ _ hv2
      have hcs : (unlinkIncompatible (updateAt g x
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x).current_step
          = g.current_step := PinAliveChain.current_step_unlinkIncompatible _ x
      rw [hcs] at hok
      exact hok
    · exact absurd rfl (SegReview.removeNode_ne _ x x nx hx)
  · exact absurd rfl (SegReview.removeNode_ne _ x x nx hx)

/-- **`reviewNode` conserva la autoposesión**: los demás nodos no cambian de tabla, y `x`, si
sobrevive, es válido, así que tiene entrada en su propio paso, que solo puede ser él mismo. -/
theorem selfL_reviewNode (g : GPathM) (hnd : NodupIds g) (hoos : SelfOwn.OOS g)
    (hsnn : SelfOwn.SNN g) (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hself : SelfL g) (nb : PNodeM → List PathNodeId) (x : PathNodeId) :
    SelfL (reviewNode g nb x) := by
  intro y ny hy
  obtain ⟨n, hn, hne, heq⟩ := SegReview.reviewNode_owners g hnd nb x y ny hy
  if hyx : y = x then
    subst hyx
    rw [heq rfl]
    have hmem : n ∈ g.nodes := List.mem_of_find?_eq_some hn
    have hid : n.id = y := node?_id_eq g y n hn
    have hok := owners_ok_of_kept g nb y n hn ny hy
    have hent := List.all_eq_true.mp hok y.id.step
      (mem_intRange (by rw [← hid]; exact hsnn n hmem) (by have := hbelow n hmem; rw [hid] at this; omega))
    obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp hent
    have hqn : q ∈ n.owners := (List.mem_filter.mp hq).1
    have hqeq : q = n.id := hoos n hmem q hqn (by rw [eq_of_beq hqs, hid])
    rw [hid] at hqeq
    rw [← hqeq]; exact hq
  else
    rw [hne hyx]; exact hself y n hn

/-- info: 'AbsSat.GraphPath.Model.PassCtx.selfL_reviewNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms selfL_reviewNode

end AbsSat.GraphPath.Model.PassCtx
