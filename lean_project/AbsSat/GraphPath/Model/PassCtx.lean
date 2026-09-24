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
open AbsSat.GraphPath.Model.Extendable (upd upd_self upd_other)

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
    have hup : Ids (mirrorDrop (updateAt g x
        (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x (cutRemoved d (unionOwnersOf g (nb d))))
        = Ids g := by rw [NodeIds.ids_mirrorDrop]; exact ids_updateAt g x _ (fun _ => rfl)
    have hunl := ids_unlinkIncompatible
      (mirrorDrop (updateAt g x
        (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x (cutRemoved d (unionOwnersOf g (nb d)))) x
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
        have hup : Ids (mirrorDrop (updateAt g x
            (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x (cutRemoved d (unionOwnersOf g (nb d))))
            = Ids g := by rw [NodeIds.ids_mirrorDrop]; exact ids_updateAt g x _ (fun _ => rfl)
        have hunl := ids_unlinkIncompatible
          (mirrorDrop (updateAt g x
            (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x (cutRemoved d (unionOwnersOf g (nb d)))) x
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
-- Hijos vivos: el espejo
-- ============================================================

/-- **Hijos vivos**: los hijos de un nodo son nodos. -/
def SLive (g : GPathM) : Prop :=
  ∀ y ny, g.node? y = some ny → ∀ q ∈ ny.sons, (g.node? q).isSome

theorem not_son_removeNode (g : GPathM) (x : PathNodeId) (n : PNodeM)
    (hn : n ∈ (removeNode g x).nodes) : x ∉ n.sons := by
  rw [removeNode_nodes] at hn
  obtain ⟨n0, _, rfl⟩ := List.mem_map.mp hn
  intro h
  have := (List.mem_filter.mp h).2
  simp at this

theorem not_son_of_removed (g : GPathM) (hnd : NodupIds g) (hsl : SLive g)
    (nb : PNodeM → List PathNodeId) (x : PathNodeId)
    (hgone : ((reviewNode g nb x).node? x).isSome = false) :
    ∀ n ∈ (reviewNode g nb x).nodes, x ∉ n.sons := by
  cases hn : g.node? x with
  | none =>
    have hR : reviewNode g nb x = g := by unfold reviewNode; rw [hn]
    rw [hR]
    intro n hnm hx
    have hnode : g.node? n.id = some n := node?_of_mem hnd n hnm
    have := hsl n.id n hnode x hx
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
        have hup : Ids (mirrorDrop (updateAt g x
            (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x (cutRemoved d (unionOwnersOf g (nb d))))
            = Ids g := by rw [NodeIds.ids_mirrorDrop]; exact ids_updateAt g x _ (fun _ => rfl)
        have hunl := ids_unlinkIncompatible
          (mirrorDrop (updateAt g x
            (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x (cutRemoved d (unionOwnersOf g (nb d)))) x
        have := node_of_mem_ids _ x (by rw [hunl, hup]; exact hxin)
        rw [this] at hgone
        exact Bool.noConfusion hgone
      · exact fun n hn' => not_son_removeNode _ x n hn'
    · exact fun n hn' => not_son_removeNode g x n hn'

/-- `reviewNode` solo quita hijos. -/
theorem sonsSub_reviewNode (g : GPathM) (nb : PNodeM → List PathNodeId) (id : PathNodeId) :
    Sons.SonsSub g (reviewNode g nb id) := by
  simp only [reviewNode]
  split
  · exact Sons.SonsSub_refl g
  · next d _ =>
    split
    · have h₁ : Sons.SonsSub g (updateAt g id
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) :=
        Sons.SonsSub_updateAt g id _ (fun _ => rfl) (fun _ _ hs => hs)
      have h₂ := Sons.SonsSub_trans (Sons.SonsSub_trans h₁ (Sons.SonsSub_mirrorDrop _ id
        (cutRemoved d (unionOwnersOf g (nb d))))) (Sons.SonsSub_unlinkIncompatible _ id)
      split
      · exact h₂
      · exact Sons.SonsSub_trans h₂ (Sons.SonsSub_removeNode _ id)
    · exact Sons.SonsSub_removeNode g id

/-- **`reviewNode` conserva los hijos vivos.** -/
theorem sLive_reviewNode (g : GPathM) (hnd : NodupIds g) (hsl : SLive g)
    (nb : PNodeM → List PathNodeId) (x : PathNodeId) : SLive (reviewNode g nb x) := by
  have hsub := NodeIds.ids_reviewNode g nb x
  intro y ny hy q hq
  -- el nodo de antes: sus hijos contienen a los de ahora
  have hmem : ny ∈ (reviewNode g nb x).nodes := List.mem_of_find?_eq_some hy
  have hsons : ∃ n0, g.node? y = some n0 ∧ q ∈ n0.sons := by
    obtain ⟨n0, hn0, hid0, hs0⟩ := sonsSub_reviewNode g nb x ny hmem
    have hyid : ny.id = y := node?_id_eq _ y ny hy
    exact ⟨n0, by rw [← hyid, hid0]; exact node?_of_mem hnd n0 hn0, hs0 q hq⟩
  obtain ⟨n0, hn0, hq0⟩ := hsons
  have hqg := hsl y n0 hn0 q hq0
  cases hx : ((reviewNode g nb x).node? x).isSome with
  | true =>
    if hqx : q = x then rw [hqx]; exact hx
    else exact survives_reviewNode g nb x q hqg hqx
  | false =>
    have hnot := not_son_of_removed g hnd hsl nb x hx ny hmem
    exact survives_reviewNode g nb x q hqg (fun h => hnot (h ▸ hq))

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
      have hcs : (unlinkIncompatible (mirrorDrop (updateAt g x
          (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x (cutRemoved d (unionOwnersOf g (nb d)))) x).current_step
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
    exact (hne hyx).2.1 y (hself y n hn) hyx

/-- info: 'AbsSat.GraphPath.Model.PassCtx.selfL_reviewNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms selfL_reviewNode

-- ============================================================
-- La versión viva, y que la pasada de padres no elimina a nadie
-- ============================================================

/-- **`SegGood` con entrada común viva.** Medido en los estados intermedios de las pasadas de padres
e hijos (`passhyp`, semilla 1): 0 casos con solo entradas muertas en 227 millones. -/
def SegGoodL (g : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi ≤ g.current_step - 1 →
    Extendable.PartialChain g sel lo hi →
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners) →
    ∀ i, 0 ≤ i → i ≤ g.current_step - 1 → (i < lo ∨ hi < i) → ∃ r, r.id.step = i ∧
      (g.node? r).isSome ∧
      ∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r ∈ nj.owners

/-- **Un paso por debajo, los owners vivos son padres.** -/
def I1L (g : GPathM) : Prop :=
  ∀ y ny, g.node? y = some ny → ∀ w ∈ ny.owners, (g.node? w).isSome →
    w.id.step + 1 = y.id.step → w ∈ ny.parents

/-- **Un paso por encima, los owners vivos son hijos.** -/
def I1sL (g : GPathM) : Prop :=
  ∀ y ny, g.node? y = some ny → ∀ w ∈ ny.owners, (g.node? w).isSome →
    w.id.step = y.id.step + 1 → w ∈ ny.sons

/-- **La validez, desde sus piezas.** -/
theorem isValidNode_of (h : GPathM) (n : PNodeM)
    (hok : ∀ k, 0 ≤ k → k ≤ h.current_step - 1 → ∃ q ∈ n.owners, q.id.step = k)
    (hroot : n.id.parent_id.isNone = false) (hpar : n.parents ≠ [])
    (hsons : n.id.id.step ≠ h.current_step - 1 → n.sons ≠ []) : isValidNode h n = true := by
  have hok' : (intRange 0 (h.current_step - 1)).all (fun k => hasStepEntry n.owners k) = true := by
    refine List.all_eq_true.mpr (fun k hk => ?_)
    obtain ⟨q, hq, hqs⟩ := hok k (mem_intRange_lower hk) (mem_intRange_upper hk)
    exact List.any_eq_true.mpr ⟨q, hq, beq_iff_eq.mpr hqs⟩
  have hp : (!n.parents.isEmpty) = true := by
    cases hq : n.parents with
    | nil => exact absurd hq hpar
    | cons _ _ => rfl
  unfold isValidNode
  dsimp only
  rw [hroot, if_neg Bool.false_ne_true, hok', hp]
  cases hl : (n.id.id.step == h.current_step - 1) with
  | true => rfl
  | false =>
    have hne : n.id.id.step ≠ h.current_step - 1 := fun e => by
      rw [beq_iff_eq.mpr e] at hl; exact Bool.noConfusion hl
    have hs : (!n.sons.isEmpty) = true := by
      cases hq : n.sons with
      | nil => exact absurd hq (hsons hne)
      | cons _ _ => rfl
    rw [hs]; rfl

/-- El tramo de un solo nodo. -/
theorem seg_single (g : GPathM) (x : PathNodeId) (d : PNodeM) (hd : g.node? x = some d) :
    TopGoodUp.Seg g (fun _ => x) x.id.step x.id.step :=
  ⟨⟨fun i hi1 hi2 => by
      have : i = x.id.step := by omega
      subst this; exact ⟨by rw [hd]; rfl, rfl⟩,
    fun i hi1 hi2 => by omega⟩,
   fun i j hi1 hj1 hi2 hj2 hij => absurd (by omega) hij⟩

/-- **La pasada de padres no elimina el nodo que procesa.** Un padre vivo `u` de `x` en su tabla
(`SegGoodL` en `[x]`) alarga el tramo a `[u, x]` (`LocSym`); sus entradas comunes están en la tabla
de `u`, así que sobreviven al corte con la unión de los padres: `x` conserva una entrada en cada
paso, al padre `u` y un hijo, y sigue siendo válido. -/
theorem kept_reviewNode_parents (g : GPathM) (hsgl : SegGoodL g) (hI1 : I1L g) (hI1s : I1sL g)
    (hself : SelfL g) (hlsym : SegReview.LocSym g) (hnr : Parents.NotRoot g)
    (x : PathNodeId) (d : PNodeM) (hd : g.node? x = some d)
    (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1) :
    ((reviewNode g (·.parents) x).node? x).isSome := by
  have hdid : d.id = x := node?_id_eq g x d hd
  have hdm : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hs1 := seg_single g x d hd
  -- un padre vivo `u` en la tabla de `x`
  obtain ⟨u, hus, hul, hu⟩ := hsgl (fun _ => x) x.id.step x.id.step (by omega) (Int.le_refl _) hxc
    hs1.1 hs1.2 (x.id.step - 1) (by omega) (by omega) (Or.inl (by omega))
  have hud : u ∈ d.owners := hu x.id.step (Int.le_refl _) (Int.le_refl _) d hd
  have hup : u ∈ d.parents := hI1 x d hd u hud hul (by omega)
  obtain ⟨nu, hnu⟩ := Option.isSome_iff_exists.mp hul
  have hxu : x ∈ nu.owners := hlsym (fun _ => x) x.id.step x.id.step (Int.le_refl _) hs1 u nu hnu
    hus hu x.id.step (Int.le_refl _) (Int.le_refl _)
  -- el tramo `[u, x]`
  have hs2 := SegReview.seg_extend g (fun _ => x) x.id.step x.id.step (Int.le_refl _) hs1 u nu hnu
    hus (fun nl hnl => by rw [← Option.some.inj (hd.symm.trans hnl)]; exact hup) hu
    (fun _ _ _ => hxu)
  have hsel_u : upd (fun _ => x) (x.id.step - 1) u (x.id.step - 1) = u := upd_self _ _ _
  have hsel_x : upd (fun _ => x) (x.id.step - 1) u x.id.step = x :=
    upd_other _ _ _ (by omega)
  -- una entrada común viva de `[u, x]` en cada paso de fuera: en las dos tablas
  have common : ∀ k, 0 ≤ k → k ≤ g.current_step - 1 → k ≠ x.id.step - 1 → k ≠ x.id.step →
      ∃ r, r.id.step = k ∧ (g.node? r).isSome ∧ r ∈ nu.owners ∧ r ∈ d.owners := by
    intro k hk0 hk1 hkne hkne'
    obtain ⟨r, hrs, hrl, hr⟩ := hsgl _ (x.id.step - 1) x.id.step (by omega) (by omega) hxc
      hs2.1 hs2.2 k hk0 hk1 (by omega)
    refine ⟨r, hrs, hrl, ?_, ?_⟩
    · exact hr (x.id.step - 1) (Int.le_refl _) (by omega) nu (by rw [hsel_u]; exact hnu)
    · exact hr x.id.step (by omega) (Int.le_refl _) d (by rw [hsel_x]; exact hd)
  let T' := intersectOwners d.owners (unionOwnersOf g d.parents)
  have inT' : ∀ r, r ∈ d.owners → r ∈ nu.owners → r ∈ T' :=
    fun r hr hrn => SegReview.mem_intersect_of_parent g d r hr u hup nu hnu hrn
  have hT'sub : ∀ r, r ∈ T' → r ∈ d.owners := fun r hr => (List.mem_filter.mp hr).1
  have hokT : ∀ k, 0 ≤ k → k ≤ g.current_step - 1 → ∃ q ∈ T', q.id.step = k := by
    intro k hk0 hk1
    rcases int_eq_or_ne k x.id.step with he | he
    · exact ⟨x, inT' x (hself x d hd) hxu, he.symm⟩
    · rcases int_eq_or_ne k (x.id.step - 1) with he' | he'
      · exact ⟨u, inT' u hud (hself u nu hnu), by rw [hus, he']⟩
      · obtain ⟨r, hrs, _, hrn, hrd⟩ := common k hk0 hk1 he' he
        exact ⟨r, inT' r hrd hrn, hrs⟩
  -- un hijo que queda
  have hson : x.id.step ≠ g.current_step - 1 → ∃ s ∈ d.sons, s ∈ T' := by
    intro hlast
    obtain ⟨r, hrs, hrl, hrn, hrd⟩ := common (x.id.step + 1) (by omega) (by omega) (by omega)
      (by omega)
    exact ⟨r, hI1s x d hd r hrd hrl hrs, inT' r hrd hrn⟩
  have hroot : d.id.parent_id.isNone = false := by
    cases hp : d.id.parent_id with
    | none => exact absurd hp (hnr d hdm (by rw [hdid]; omega))
    | some _ => rfl
  -- `x` es válido antes
  have hvd : isValidNode g d = true := by
    refine isValidNode_of g d (fun k hk0 hk1 => ?_) hroot (List.ne_nil_of_mem hup)
      (fun hl => ?_)
    · obtain ⟨q, hq, hqs⟩ := hokT k hk0 hk1
      exact ⟨q, hT'sub q hq, hqs⟩
    · obtain ⟨s, hs, _⟩ := hson (by rw [← hdid]; exact hl)
      exact List.ne_nil_of_mem hs
  -- y sigue siéndolo tras el corte
  have hcs : (unlinkIncompatible (mirrorDrop (updateAt g x
      (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g d.parents) })) x (cutRemoved d (unionOwnersOf g d.parents))) x
      ).current_step = g.current_step := PinAliveChain.current_step_unlinkIncompatible _ x
  have hvd' : isValidNode (unlinkIncompatible (mirrorDrop (updateAt g x
      (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g d.parents) })) x (cutRemoved d (unionOwnersOf g d.parents))) x)
      (relink T' d) = true := by
    refine isValidNode_of _ _ (fun k hk0 hk1 => ?_) hroot ?_ (fun hl => ?_)
    · rw [hcs] at hk1; exact hokT k hk0 hk1
    · exact List.ne_nil_of_mem
        (List.mem_filter.mpr ⟨hup, List.elem_iff.mpr (inT' u hud (hself u nu hnu))⟩)
    · rw [hcs] at hl
      obtain ⟨s, hs, hsT⟩ := hson (by rw [← hdid]; exact hl)
      exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hs, List.elem_iff.mpr hsT⟩)
  have hxin : x ∈ Ids g := mem_ids_of_node g x (by rw [hd]; rfl)
  unfold reviewNode
  rw [hd]
  simp only [hvd, ↓reduceIte]
  rw [if_pos hvd']
  apply node_of_mem_ids
  rw [ids_unlinkIncompatible, NodeIds.ids_mirrorDrop,
    ids_updateAt g x (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g d.parents) })
      (fun _ => rfl)]
  exact hxin

/-- info: 'AbsSat.GraphPath.Model.PassCtx.kept_reviewNode_parents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kept_reviewNode_parents



/-- **Tras `reviewNode x` de la pasada de padres, lo vivo sigue vivo.** -/
theorem live_reviewNode_parents (g : GPathM) (hsgl : SegGoodL g) (hI1 : I1L g) (hI1s : I1sL g)
    (hself : SelfL g) (hlsym : SegReview.LocSym g) (hnr : Parents.NotRoot g)
    (x : PathNodeId) (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1)
    (r : PathNodeId) (hr : (g.node? r).isSome) :
    ((reviewNode g (·.parents) x).node? r).isSome := by
  if hrx : r = x then
    subst hrx
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hr
    exact kept_reviewNode_parents g hsgl hI1 hI1s hself hlsym hnr r d hd hx1 hxc
  else
    exact survives_reviewNode g (·.parents) x r hr hrx

/-- Bajar un paso, con las hipótesis vivas: la entrada común viva de debajo es padre (`I1L`), y la
simetría local mete al tramo en su tabla. -/
theorem seg_down_L (g : GPathM) (hseg : SegGoodL g) (hI1 : I1L g) (hplive : PLive g)
    (hlsym : SegReview.LocSym g) (sel : Int → PathNodeId) (lo hi : Int) (hpos : 0 < lo)
    (hlohi : lo ≤ hi) (hhi : hi ≤ g.current_step - 1) (hs : TopGoodUp.Seg g sel lo hi) :
    ∃ r, TopGoodUp.Seg g (upd sel (lo - 1) r) (lo - 1) hi := by
  obtain ⟨r0, hr0s, hr0l, hr0all⟩ := hseg sel lo hi (by omega) hlohi hhi hs.1 hs.2 (lo - 1)
    (by omega) (by omega) (Or.inl (by omega))
  obtain ⟨hls, hlstep⟩ := hs.1.1 lo (Int.le_refl _) hlohi
  obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp hls
  have hr0p : r0 ∈ nl.parents :=
    hI1 _ nl hnl r0 (hr0all lo (Int.le_refl _) hlohi nl hnl) hr0l (by rw [hr0s, hlstep]; omega)
  obtain ⟨nr0, hnr0⟩ := Option.isSome_iff_exists.mp (hplive _ nl hnl r0 hr0p)
  exact ⟨r0, SegReview.seg_extend g sel lo hi hlohi hs r0 nr0 hnr0 hr0s
    (fun nl' hnl' => by rw [← Option.some.inj (hnl.symm.trans hnl')]; exact hr0p) hr0all
    (hlsym sel lo hi hlohi hs r0 nr0 hnr0 hr0s hr0all)⟩

/-- Subir un paso, con las hipótesis vivas. -/
theorem seg_up_L (g : GPathM) (hseg : SegGoodL g) (hI1 : I1L g) (hI1s : I1sL g) (hslive : SLive g)
    (hlsymU : SegReview.LocSymUp g) (sel : Int → PathNodeId) (lo hi : Int) (hlo : 0 ≤ lo)
    (hlohi : lo ≤ hi) (hhi : hi < g.current_step - 1) (hs : TopGoodUp.Seg g sel lo hi) :
    ∃ r, TopGoodUp.Seg g (upd sel (hi + 1) r) lo (hi + 1) := by
  obtain ⟨r0, hr0s, hr0l, hr0all⟩ := hseg sel lo hi hlo hlohi (by omega) hs.1 hs.2 (hi + 1)
    (by omega) (by omega) (Or.inr (by omega))
  obtain ⟨hhs, hhstep⟩ := hs.1.1 hi hlohi (Int.le_refl _)
  obtain ⟨nh, hnh⟩ := Option.isSome_iff_exists.mp hhs
  have hr0son : r0 ∈ nh.sons :=
    hI1s _ nh hnh r0 (hr0all hi hlohi (Int.le_refl _) nh hnh) hr0l (by rw [hr0s, hhstep])
  obtain ⟨nr0, hnr0⟩ := Option.isSome_iff_exists.mp (hslive _ nh hnh r0 hr0son)
  have hback := hlsymU sel lo hi hlohi hs r0 nr0 hnr0 hr0s hr0all
  have hpar : sel hi ∈ nr0.parents :=
    hI1 _ nr0 hnr0 _ (hback hi hlohi (Int.le_refl _)) hhs (by rw [hhstep, hr0s])
  exact ⟨r0, SegReview.seg_extend_up g sel lo hi hlohi hs r0 nr0 hnr0 hr0s hpar hr0all hback⟩

/-- **Todo tramo se extiende a una cadena completa**, con las hipótesis vivas (`SegReview.seg_full`). -/
theorem seg_full_L (g : GPathM) (hseg : SegGoodL g) (hI1 : I1L g) (hI1s : I1sL g)
    (hplive : PLive g) (hslive : SLive g) (hlsym : SegReview.LocSym g)
    (hlsymU : SegReview.LocSymUp g) (sel : Int → PathNodeId) (lo hi : Int) (hlo : 0 ≤ lo)
    (hlohi : lo ≤ hi) (hhi : hi ≤ g.current_step - 1) (hs : TopGoodUp.Seg g sel lo hi) :
    ∃ sel', TopGoodUp.Seg g sel' 0 (g.current_step - 1) ∧ ∀ j, lo ≤ j → j ≤ hi → sel' j = sel j := by
  have down : ∀ (fuel : Nat) (s : Int → PathNodeId) (l : Int), l.toNat ≤ fuel → 0 ≤ l → l ≤ lo →
      TopGoodUp.Seg g s l hi → (∀ j, lo ≤ j → j ≤ hi → s j = sel j) →
      ∃ s', TopGoodUp.Seg g s' 0 hi ∧ ∀ j, lo ≤ j → j ≤ hi → s' j = sel j := by
    intro fuel
    induction fuel with
    | zero =>
      intro s l hm hl0 hll hs' hagree
      have : l = 0 := by omega
      subst this; exact ⟨s, hs', hagree⟩
    | succ fuel ih =>
      intro s l hm hl0 hll hs' hagree
      if hpos : 0 < l then
        obtain ⟨r, hr⟩ := seg_down_L g hseg hI1 hplive hlsym s l hi hpos (by omega) hhi hs'
        exact ih _ (l - 1) (by omega) (by omega) (by omega) hr
          (fun j hj1 hj2 => by rw [upd_other s (l - 1) r (by omega)]; exact hagree j hj1 hj2)
      else
        have : l = 0 := by omega
        subst this; exact ⟨s, hs', hagree⟩
  obtain ⟨s1, hs1, hag1⟩ := down lo.toNat sel lo (Nat.le_refl _) hlo (Int.le_refl _) hs
    (fun _ _ _ => rfl)
  have up : ∀ (fuel : Nat) (s : Int → PathNodeId) (h : Int),
      (g.current_step - 1 - h).toNat ≤ fuel → hi ≤ h → h ≤ g.current_step - 1 →
      TopGoodUp.Seg g s 0 h → (∀ j, lo ≤ j → j ≤ hi → s j = sel j) →
      ∃ s', TopGoodUp.Seg g s' 0 (g.current_step - 1) ∧ ∀ j, lo ≤ j → j ≤ hi → s' j = sel j := by
    intro fuel
    induction fuel with
    | zero =>
      intro s h hm hh1 hh2 hs' hagree
      have : h = g.current_step - 1 := by omega
      subst this; exact ⟨s, hs', hagree⟩
    | succ fuel ih =>
      intro s h hm hh1 hh2 hs' hagree
      if hlt : h < g.current_step - 1 then
        obtain ⟨r, hr⟩ := seg_up_L g hseg hI1 hI1s hslive hlsymU s 0 h (Int.le_refl _) (by omega) hlt hs'
        exact ih _ (h + 1) (by omega) (by omega) (by omega) hr
          (fun j hj1 hj2 => by rw [upd_other s (h + 1) r (by omega)]; exact hagree j hj1 hj2)
      else
        have : h = g.current_step - 1 := by omega
        subst this; exact ⟨s, hs', hagree⟩
  exact up (g.current_step - 1 - hi).toNat s1 hi (Nat.le_refl _) (Int.le_refl _) hhi hs1 hag1

/-- **`reviewNode x`, con los padres como vecinos, conserva `SegGoodL`** (review simétrico). El
argumento de `SegReview.segGood_reviewNode_parents` con las hipótesis vivas: el tramo se extiende a
una cadena completa `Q` (`seg_full_L`), y `Q i` es la entrada común de después —en la tabla de `x`
porque la tiene el padre de `x` en `Q`; en las demás porque el espejo solo podría quitarla si fuera
`x`, y entonces el padre de `x` en `Q` tiene al miembro—; y sigue viva porque `x` no se elimina. -/
theorem segGoodL_reviewNode_parents (g : GPathM) (hnd : NodupIds g) (hI1 : I1L g) (hI1s : I1sL g)
    (hplive : PLive g) (hslive : SLive g) (hself : SelfL g) (hlsym : SegReview.LocSym g)
    (hlsymU : SegReview.LocSymUp g) (hnr : Parents.NotRoot g)
    (hseg : SegGoodL g) (x : PathNodeId) (hx1 : 1 ≤ x.id.step)
    (hxc : x.id.step ≤ g.current_step - 1) :
    SegGoodL (reviewNode g (·.parents) x) := by
  have hpr := pruned_reviewNode (·.parents) x g
  have live := live_reviewNode_parents g hseg hI1 hI1s hself hlsym hnr x hx1 hxc
  have lift : ∀ y n', (reviewNode g (·.parents) x).node? y = some n' →
      ∃ n, g.node? y = some n ∧ (∀ q ∈ n'.owners, q ∈ n.owners) ∧ (∀ p ∈ n'.parents, p ∈ n.parents) := by
    intro y n' h
    obtain ⟨n0, hn0, hid0, hown0, hpar0⟩ := hpr.nodes_derived n' (List.mem_of_find?_eq_some h)
    have hy : n'.id = y := node?_id_eq _ y n' h
    exact ⟨n0, by rw [← hy, hid0]; exact node?_of_mem hnd n0 hn0, hown0, hpar0⟩
  intro sel lo hi hlo0 hlohi hhi hch' hpw' i hi0 hic hout
  rw [hpr.step_eq] at hhi hic
  have hsG : TopGoodUp.Seg g sel lo hi := by
    refine ⟨⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_⟩, fun a b ha1 hb1 ha2 hb2 hab nb hnb => ?_⟩
    · obtain ⟨hs, hjs⟩ := hch'.1 j hj1 hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _⟩ := lift _ m hm
      exact ⟨by rw [hn]; rfl, hjs⟩
    · obtain ⟨hs, _⟩ := hch'.1 (j + 1) (by omega) hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _, hpar⟩ := lift _ m hm
      have hl := hch'.2 j hj1 hj2
      rw [hm] at hl
      rw [hn]
      simp only [Option.map_some, Option.getD_some] at hl ⊢
      exact hpar _ hl
    · obtain ⟨hs, _⟩ := hch'.1 b hb1 hb2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, hown, _⟩ := lift _ m hm
      rw [← Option.some.inj (hn.symm.trans hnb)]
      exact hown _ (hpw' a b ha1 hb1 ha2 hb2 hab m hm)
  obtain ⟨Q, hQ, hQag⟩ := seg_full_L g hseg hI1 hI1s hplive hslive hlsym hlsymU sel lo hi hlo0 hlohi
    hhi hsG
  have hQnode : ∀ k, 0 ≤ k → k ≤ g.current_step - 1 → ∃ nk, g.node? (Q k) = some nk :=
    fun k hk0 hk1 => Option.isSome_iff_exists.mp (hQ.1.1 k hk0 hk1).1
  have hQown : ∀ a b, 0 ≤ a → 0 ≤ b → a ≤ g.current_step - 1 → b ≤ g.current_step - 1 →
      ∀ nb, g.node? (Q b) = some nb → Q a ∈ nb.owners := by
    intro a b ha hb ha' hb' nb hnb
    rcases int_eq_or_ne a b with hab | hab
    · subst hab; exact hself _ nb hnb
    · exact hQ.2 a b ha hb ha' hb' hab nb hnb
  have hQpar : ∀ k, 1 ≤ k → k ≤ g.current_step - 1 → ∀ nk, g.node? (Q k) = some nk →
      Q (k - 1) ∈ nk.parents := by
    intro k hk1 hk2 nk hnk
    have hl := hQ.1.2 (k - 1) (by omega) (by omega)
    rw [show k - 1 + 1 = k by omega, hnk] at hl
    simpa using hl
  refine ⟨Q i, (hQ.1.1 i hi0 hic).2, live (Q i) (hQ.1.1 i hi0 hic).1, fun j hj1 hj2 nj' hnj' => ?_⟩
  obtain ⟨n, hn, hne, heq⟩ := SegReview.reviewNode_owners g hnd (·.parents) x (sel j) nj' hnj'
  have hQj : Q j = sel j := hQag j hj1 hj2
  have hjs : (sel j).id.step = j := (hsG.1.1 j hj1 hj2).2
  have hnQ : g.node? (Q j) = some n := by rw [hQj]; exact hn
  have hci : Q i ∈ n.owners := hQown i j hi0 (by omega) hic (by omega) n hnQ
  if hjx : sel j = x then
    rw [heq hjx]
    have hj1' : 1 ≤ j := by rw [← hjs, hjx]; exact hx1
    obtain ⟨np, hnp⟩ := hQnode (j - 1) (by omega) (by omega)
    exact SegReview.mem_intersect_of_parent g n (Q i) hci (Q (j - 1)) (hQpar j hj1' (by omega) n hnQ)
      np hnp (hQown i (j - 1) hi0 (by omega) hic (by omega) np hnp)
  else
    obtain ⟨_, hkeep, hmk⟩ := hne hjx
    if hcx : Q i = x then
      rw [hmk (fun dx hdx hin => ?_)]
      · exact hci
      · have hdx' : g.node? (Q i) = some dx := by rw [hcx]; exact hdx
        have hi1 : 1 ≤ i := by rw [← (hQ.1.1 i hi0 hic).2, hcx]; exact hx1
        obtain ⟨np, hnp⟩ := hQnode (i - 1) (by omega) (by omega)
        exact SegReview.mem_intersect_of_parent g dx (sel j) hin (Q (i - 1)) (hQpar i hi1 hic dx hdx')
          np hnp (by rw [← hQj]; exact hQown j (i - 1) (by omega) (by omega) (by omega) (by omega) np hnp)
    else
      exact hkeep _ hci hcx

/-- info: 'AbsSat.GraphPath.Model.PassCtx.segGoodL_reviewNode_parents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segGoodL_reviewNode_parents

-- ============================================================
-- La forma de `reviewNode` cuando `x` sobrevive, y la conservación de `I1L`
-- ============================================================

theorem beq_false_of_ne' (a b : PathNodeId) (h : a ≠ b) : (a == b) = false := by
  cases hb : (a == b) with
  | false => rfl
  | true => exact absurd (eq_of_beq hb) h

theorem removed_none (h : GPathM) (x : PathNodeId) : ((removeNode h x).node? x).isSome = false := by
  cases hh : (removeNode h x).node? x with
  | none => rfl
  | some n => exact absurd rfl (SegReview.removeNode_ne _ x x n hh)

/-- **Si `x` sobrevive, `reviewNode x` es cortar su tabla, el espejo y desenlazar.** -/
theorem kept_form (g : GPathM) (nb : PNodeM → List PathNodeId) (x : PathNodeId) (d : PNodeM)
    (hd : g.node? x = some d) (hk : ((reviewNode g nb x).node? x).isSome = true) :
    reviewNode g nb x = unlinkIncompatible (mirrorDrop (updateAt g x
      (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x
      (cutRemoved d (unionOwnersOf g (nb d)))) x := by
  unfold reviewNode at hk ⊢
  rw [hd] at hk ⊢
  dsimp only at hk ⊢
  split
  · rename_i hv1
    rw [if_pos hv1] at hk
    split
    · rfl
    · rename_i hv2
      rw [if_neg hv2, removed_none] at hk
      exact Bool.noConfusion hk
  · rename_i hv1
    rw [if_neg hv1, removed_none] at hk
    exact Bool.noConfusion hk

/-- **El nodo `y` tras `reviewNode x`, si `x` sobrevive**: el de antes —con el espejo, si es otro—,
desenlazado contra la nueva tabla de `x`. -/
theorem node_after (g : GPathM) (nb : PNodeM → List PathNodeId) (x : PathNodeId) (d : PNodeM)
    (hd : g.node? x = some d) (hk : ((reviewNode g nb x).node? x).isSome = true)
    (y : PathNodeId) (n : PNodeM) (hn : g.node? y = some n) :
    (reviewNode g nb x).node? y =
      some (unlinkMap { d with owners := intersectOwners d.owners (unionOwnersOf g (nb d)) } x
        (if y = x then { d with owners := intersectOwners d.owners (unionOwnersOf g (nb d)) }
          else mirrorMap x (cutRemoved d (unionOwnersOf g (nb d))) n)) := by
  rw [kept_form g nb x d hd hk]
  have hux : (updateAt g x
      (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })).node? x
      = some { d with owners := intersectOwners d.owners (unionOwnersOf g (nb d)) } := by
    rw [updateAt_node? g x (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) }) (fun _ => rfl) x d hd,
      show (d.id == x) = true from beq_iff_eq.mpr (node?_id_eq g x d hd)]
  have hmx : (mirrorDrop (updateAt g x
      (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) x
      (cutRemoved d (unionOwnersOf g (nb d)))).node? x
      = some { d with owners := intersectOwners d.owners (unionOwnersOf g (nb d)) } := by
    rw [mirrorDrop_node? _ x _ x _ hux,
      SegReview.mirrorMap_self_cut_eq x d (unionOwnersOf g (nb d)) (node?_id_eq g x d hd)]
  if hyx : y = x then
    subst hyx
    rw [if_pos rfl]
    exact unlinkIncompatible_node? _ y _ hmx y _ hmx
  else
    rw [if_neg hyx]
    have huy : (updateAt g x
        (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })).node? y
        = some n := by
      rw [updateAt_node? g x (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) }) (fun _ => rfl) y n hn,
        beq_false_of_ne' n.id x (by rw [node?_id_eq g y n hn]; exact hyx)]
    exact unlinkIncompatible_node? _ x _ hmx y _ (mirrorDrop_node? _ x _ y n huy)

/-- **La pasada de padres conserva `I1L`.** El único caso con contenido: un hijo vivo `y` que tiene a
`x` en su tabla. `LocSym` en `[y]` pone a `y` en la tabla de `x`, y en `[x, y]` en la de un padre
de `x`; así que `y` queda en la nueva tabla de `x` y el desenlace no lo toca. -/
theorem i1L_reviewNode_parents (g : GPathM) (hnd : NodupIds g) (hsgl : SegGoodL g) (hI1 : I1L g)
    (hI1s : I1sL g) (hself : SelfL g) (hlsym : SegReview.LocSym g) (hnr : Parents.NotRoot g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (x : PathNodeId) (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1) :
    I1L (reviewNode g (·.parents) x) := by
  have hsub := NodeIds.ids_reviewNode g (·.parents) x
  have liveG : ∀ w, ((reviewNode g (·.parents) x).node? w).isSome → (g.node? w).isSome :=
    fun w h => node_of_mem_ids g w (hsub.subset (mem_ids_of_node _ w h))
  intro y ny hy w hw hwl hws
  cases hd : g.node? x with
  | none =>
    have hR : reviewNode g (·.parents) x = g := by unfold reviewNode; rw [hd]
    rw [hR] at hy hwl
    exact hI1 y ny hy w hw hwl hws
  | some d =>
    have hk := kept_reviewNode_parents g hsgl hI1 hI1s hself hlsym hnr x d hd hx1 hxc
    obtain ⟨n, hn, _, _⟩ := SegReview.reviewNode_owners g hnd (·.parents) x y ny hy
    have hform := node_after g (·.parents) x d hd hk y n hn
    rw [hy] at hform
    have hny := Option.some.inj hform
    have hwlg := liveG w hwl
    if hyx : y = x then
      subst hyx
      rw [if_pos rfl, PinAliveChain.unlinkMap_self
        { d with owners := intersectOwners d.owners (unionOwnersOf g d.parents) } y
        (node?_id_eq g y d hd)] at hny
      rw [hny] at hw ⊢
      have hwd : w ∈ d.owners := (List.mem_filter.mp hw).1
      have hwp := hI1 y d hd w hwd hwlg hws
      exact List.mem_filter.mpr ⟨hwp, List.elem_iff.mpr hw⟩
    else
      rw [if_neg hyx] at hny
      have hnid : n.id = y := node?_id_eq g y n hn
      have hwn : w ∈ n.owners := by
        rw [hny, PinAliveChain.owners_unlinkMap] at hw; exact mirrorMap_owners_sub _ _ n w hw
      have hwp := hI1 y n hn w hwn hwlg hws
      if hwx : w = x then
        subst hwx
        -- `y` queda en la nueva tabla de `w` (= `x`)
        have hnm : n ∈ g.nodes := List.mem_of_find?_eq_some hn
        have hyc : y.id.step ≤ g.current_step - 1 := by have := hbelow n hnm; rw [hnid] at this; omega
        have hsy := seg_single g y n hn
        have hyd : y ∈ d.owners := hlsym (fun _ => y) y.id.step y.id.step (Int.le_refl _) hsy w d hd
          (by omega) (fun _ _ _ nj hnj => by rw [← Option.some.inj (hn.symm.trans hnj)]; exact hwn)
          y.id.step (Int.le_refl _) (Int.le_refl _)
        have hs2 := SegReview.seg_extend g (fun _ => y) y.id.step y.id.step (Int.le_refl _) hsy w d hd
          (by omega) (fun nl hnl => by rw [← Option.some.inj (hn.symm.trans hnl)]; exact hwp)
          (fun _ _ _ nj hnj => by rw [← Option.some.inj (hn.symm.trans hnj)]; exact hwn)
          (fun _ _ _ => hyd)
        have hsel_w : upd (fun _ => y) (y.id.step - 1) w (y.id.step - 1) = w := upd_self _ _ _
        have hsel_y : upd (fun _ => y) (y.id.step - 1) w y.id.step = y := upd_other _ _ _ (by omega)
        obtain ⟨u, hus, hul, hu⟩ := hsgl _ (y.id.step - 1) y.id.step (by omega) (by omega) hyc
          hs2.1 hs2.2 (y.id.step - 2) (by omega) (by omega) (Or.inl (by omega))
        have hud : u ∈ d.owners := hu (y.id.step - 1) (Int.le_refl _) (by omega) d (by rw [hsel_w]; exact hd)
        have hup : u ∈ d.parents := hI1 w d hd u hud hul (by omega)
        obtain ⟨nu, hnu⟩ := Option.isSome_iff_exists.mp hul
        have hyu : y ∈ nu.owners := by
          have := hlsym _ (y.id.step - 1) y.id.step (by omega) hs2 u nu hnu (by omega) hu y.id.step
            (by omega) (Int.le_refl _)
          rw [hsel_y] at this; exact this
        have hyT : y ∈ intersectOwners d.owners (unionOwnersOf g d.parents) :=
          SegReview.mem_intersect_of_parent g d y hyd u hup nu hnu hyu
        rw [PinAliveChain.unlinkMap_keeps _ _ _ (by rw [mirrorMap_id, hnid]; exact hyx)
          (by rw [mirrorMap_id, hnid]; exact List.elem_iff.mpr hyT)] at hny
        rw [hny, mirrorMap_parents]; exact hwp
      else
        rw [hny]
        exact PinAliveChain.parents_unlinkMap_keeps _ x _ (by rw [mirrorMap_id, hnid]; exact hyx) w
          (by rw [mirrorMap_parents]; exact hwp) hwx

/-- info: 'AbsSat.GraphPath.Model.PassCtx.i1L_reviewNode_parents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms i1L_reviewNode_parents

/-- **La pasada de padres conserva `I1sL`.** El caso con contenido: `x` hijo de un nodo vivo `y` que
lo tiene en su tabla. `LocSymUp` en `[y]` pone a `y` en la tabla de `x`; `y` es padre de `x`
(`I1L`) y se posee, así que queda en el corte y el desenlace no lo toca. -/
theorem i1sL_reviewNode_parents (g : GPathM) (hnd : NodupIds g) (hsgl : SegGoodL g) (hI1 : I1L g)
    (hI1s : I1sL g) (hself : SelfL g) (hlsym : SegReview.LocSym g) (hlsymU : SegReview.LocSymUp g)
    (hnr : Parents.NotRoot g) (x : PathNodeId) (hx1 : 1 ≤ x.id.step)
    (hxc : x.id.step ≤ g.current_step - 1) :
    I1sL (reviewNode g (·.parents) x) := by
  have hsub := NodeIds.ids_reviewNode g (·.parents) x
  have liveG : ∀ w, ((reviewNode g (·.parents) x).node? w).isSome → (g.node? w).isSome :=
    fun w h => node_of_mem_ids g w (hsub.subset (mem_ids_of_node _ w h))
  intro y ny hy w hw hwl hws
  cases hd : g.node? x with
  | none =>
    have hR : reviewNode g (·.parents) x = g := by unfold reviewNode; rw [hd]
    rw [hR] at hy hwl
    exact hI1s y ny hy w hw hwl hws
  | some d =>
    have hk := kept_reviewNode_parents g hsgl hI1 hI1s hself hlsym hnr x d hd hx1 hxc
    obtain ⟨n, hn, _, _⟩ := SegReview.reviewNode_owners g hnd (·.parents) x y ny hy
    have hform := node_after g (·.parents) x d hd hk y n hn
    rw [hy] at hform
    have hny := Option.some.inj hform
    have hwlg := liveG w hwl
    if hyx : y = x then
      subst hyx
      rw [if_pos rfl, PinAliveChain.unlinkMap_self
        { d with owners := intersectOwners d.owners (unionOwnersOf g d.parents) } y
        (node?_id_eq g y d hd)] at hny
      rw [hny] at hw ⊢
      have hwd : w ∈ d.owners := (List.mem_filter.mp hw).1
      have hws' := hI1s y d hd w hwd hwlg hws
      exact List.mem_filter.mpr ⟨hws', List.elem_iff.mpr hw⟩
    else
      rw [if_neg hyx] at hny
      have hnid : n.id = y := node?_id_eq g y n hn
      have hwn : w ∈ n.owners := by
        rw [hny, PinAliveChain.owners_unlinkMap] at hw; exact mirrorMap_owners_sub _ _ n w hw
      have hws' := hI1s y n hn w hwn hwlg hws
      if hwx : w = x then
        subst hwx
        have hsy := seg_single g y n hn
        have hyd : y ∈ d.owners := hlsymU (fun _ => y) y.id.step y.id.step (Int.le_refl _) hsy w d hd
          (by omega) (fun _ _ _ nj hnj => by rw [← Option.some.inj (hn.symm.trans hnj)]; exact hwn)
          y.id.step (Int.le_refl _) (Int.le_refl _)
        have hyl : (g.node? y).isSome := by rw [hn]; rfl
        have hyp : y ∈ d.parents := hI1 w d hd y hyd hyl (by omega)
        have hyT : y ∈ intersectOwners d.owners (unionOwnersOf g d.parents) :=
          SegReview.mem_intersect_of_parent g d y hyd y hyp n hn (hself y n hn)
        rw [PinAliveChain.unlinkMap_keeps _ _ _ (by rw [mirrorMap_id, hnid]; exact hyx)
          (by rw [mirrorMap_id, hnid]; exact List.elem_iff.mpr hyT)] at hny
        rw [hny, mirrorMap_sons]; exact hws'
      else
        rw [hny]
        exact PinAliveChain.sons_unlinkMap_keeps _ x _ (by rw [mirrorMap_id, hnid]; exact hyx) w
          (by rw [mirrorMap_sons]; exact hws') hwx

/-- info: 'AbsSat.GraphPath.Model.PassCtx.i1sL_reviewNode_parents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms i1sL_reviewNode_parents

-- ============================================================
-- La pasada de padres entera
-- ============================================================

/-- **Lo que un estado de la pasada de padres lleva.** -/
structure PState (g : GPathM) : Prop where
  nd : NodupIds g
  sgl : SegGoodL g
  i1 : I1L g
  i1s : I1sL g
  plive : PLive g
  slive : SLive g
  self : SelfL g
  lsym : SegReview.LocSym g
  lsymU : SegReview.LocSymUp g
  nr : Parents.NotRoot g
  below : ∀ n ∈ g.nodes, n.id.id.step < g.current_step
  oos : SelfOwn.OOS g
  snn : SelfOwn.SNN g
  rootz : Sons.RootAtZero g

/-- **La simetría local se conserva nodo a nodo en la pasada de padres.** La única hipótesis de la
pasada; medida (`row-degree localsym`, semilla 1): 0 casos entre nodos vivos. -/
def LocSymStable : Prop :=
  ∀ g x, PState g → 1 ≤ x.id.step → x.id.step ≤ g.current_step - 1 →
    SegReview.LocSym (reviewNode g (·.parents) x) ∧ SegReview.LocSymUp (reviewNode g (·.parents) x)

theorem pstate_reviewNode (hLS : LocSymStable) (g : GPathM) (h : PState g) (x : PathNodeId)
    (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1) :
    PState (reviewNode g (·.parents) x) := by
  have hpr := pruned_reviewNode (·.parents) x g
  obtain ⟨hl, hlu⟩ := hLS g x h hx1 hxc
  exact
    { nd := List.Nodup.sublist (NodeIds.ids_reviewNode g (·.parents) x) h.nd
      sgl := segGoodL_reviewNode_parents g h.nd h.i1 h.i1s h.plive h.slive h.self h.lsym h.lsymU h.nr
        h.sgl x hx1 hxc
      i1 := i1L_reviewNode_parents g h.nd h.sgl h.i1 h.i1s h.self h.lsym h.nr h.below x hx1 hxc
      i1s := i1sL_reviewNode_parents g h.nd h.sgl h.i1 h.i1s h.self h.lsym h.lsymU h.nr x hx1 hxc
      plive := pLive_reviewNode g h.nd h.plive _ x
      slive := sLive_reviewNode g h.nd h.slive _ x
      self := selfL_reviewNode g h.nd h.oos h.snn h.below h.self _ x
      lsym := hl
      lsymU := hlu
      nr := Parents.NotRoot_of_pruned hpr h.nr
      below := Certifies.nodes_below_of_pruned hpr h.below
      oos := SelfOwn.OOS_of_pruned hpr h.oos
      snn := SelfOwn.SNN_of_pruned hpr h.snn
      rootz := Sons.RootAtZero_of_pruned hpr h.rootz }

theorem pstate_foldl (hLS : LocSymStable) (k : Int) (hk1 : 1 ≤ k) :
    ∀ (L : List PathNodeId) (g : GPathM), PState g → k ≤ g.current_step - 1 →
      (∀ id ∈ L, id.id.step = k) →
      PState (L.foldl (fun g id => reviewNode g (·.parents) id) g) := by
  intro L
  induction L with
  | nil => intro g h _ _; exact h
  | cons x xs ih =>
    intro g h hkc hL
    have hxs := hL x List.mem_cons_self
    have hstep := (pruned_reviewNode (·.parents) x g).step_eq
    exact ih _ (pstate_reviewNode hLS g h x (by omega) (by omega)) (by rw [hstep]; exact hkc)
      (fun id hid => hL id (List.mem_cons_of_mem _ hid))

theorem pstate_reviewLine (hLS : LocSymStable) (k : Int) (hk1 : 1 ≤ k) (g : GPathM)
    (h : PState g) (hkc : k ≤ g.current_step - 1) : PState (reviewLine g (·.parents) k) := by
  refine pstate_foldl hLS k hk1 _ g h hkc (fun id hid => ?_)
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hid
  exact eq_of_beq (List.mem_filter.mp hn).2

theorem pstate_reviewSteps (hLS : LocSymStable) (c : Int) :
    ∀ (ks : List Int) (g : GPathM), PState g → g.current_step - 1 = c →
      (∀ k ∈ ks, 1 ≤ k ∧ k ≤ c) → PState (reviewSteps g (·.parents) ks) := by
  intro ks
  induction ks with
  | nil => intro g h _ _; exact h
  | cons k ks ih =>
    intro g h hc hks
    unfold reviewSteps
    split
    · have hk := hks k List.mem_cons_self
      have hstep := (pruned_reviewLine (·.parents) k g).step_eq
      exact ih _ (pstate_reviewLine hLS k hk.1 g h (by omega)) (by rw [hstep]; exact hc)
        (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
    · exact h

/-- **La pasada de padres entera conserva `PState`, y con él `SegGoodL`.** Única hipótesis:
`LocSymStable`. -/
theorem pstate_reviewParents (hLS : LocSymStable) (g : GPathM) (h : PState g) :
    PState (reviewParents g) :=
  pstate_reviewSteps hLS (g.current_step - 1) _ g h rfl
    (fun _ hk => ⟨mem_intRange_lower hk, mem_intRange_upper hk⟩)

/-- info: 'AbsSat.GraphPath.Model.PassCtx.pstate_reviewParents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pstate_reviewParents

end AbsSat.GraphPath.Model.PassCtx
