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
  have hcs : (unlinkIncompatible (updateAt g x
      (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g d.parents) })) x
      ).current_step = g.current_step := PinAliveChain.current_step_unlinkIncompatible _ x
  have hvd' : isValidNode (unlinkIncompatible (updateAt g x
      (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g d.parents) })) x)
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
  rw [ids_unlinkIncompatible,
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

/-- **`reviewNode x`, con los padres como vecinos, conserva `SegGoodL`.** La prueba del v179
(`SegReview.segGood_reviewNode_parents`) con las hipótesis en su versión viva, que son las que la
máquina cumple (`passhyp`): la entrada común que alarga el tramo es viva, así que es padre, y lo vivo
sigue vivo porque `x` no se elimina. -/
theorem segGoodL_reviewNode_parents (g : GPathM) (hnd : NodupIds g) (hI1 : I1L g) (hI1s : I1sL g)
    (hplive : PLive g) (hself : SelfL g) (hlsym : SegReview.LocSym g) (hnr : Parents.NotRoot g)
    (hseg : SegGoodL g) (x : PathNodeId) (hx1 : 1 ≤ x.id.step)
    (hxc : x.id.step ≤ g.current_step - 1) :
    SegGoodL (reviewNode g (·.parents) x) := by
  have hpr := pruned_reviewNode (·.parents) x g
  have live := live_reviewNode_parents g hseg hI1 hI1s hself hlsym hnr x hx1 hxc
  have lift : ∀ y n', (reviewNode g (·.parents) x).node? y = some n' →
      ∃ n, g.node? y = some n ∧ (∀ q ∈ n'.owners, q ∈ n.owners) ∧
        (∀ p ∈ n'.parents, p ∈ n.parents) ∧ (y ≠ x → n'.owners = n.owners) ∧
        (y = x → n'.owners = intersectOwners n.owners (unionOwnersOf g n.parents)) := by
    intro y n' h
    obtain ⟨n, hn, hne, heq⟩ := SegReview.reviewNode_owners g hnd (·.parents) x y n' h
    obtain ⟨n0, hn0, hid0, hown0, hpar0⟩ := hpr.nodes_derived n' (List.mem_of_find?_eq_some h)
    have hy : n'.id = y := node?_id_eq _ y n' h
    have hn0' : g.node? y = some n0 := by rw [← hy, hid0]; exact node?_of_mem hnd n0 hn0
    rw [hn] at hn0'; cases hn0'
    exact ⟨n, hn, hown0, hpar0, hne, heq⟩
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
      obtain ⟨n, hn, _, hpar, _⟩ := lift _ m hm
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
  have keep : ∀ r, (∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r ∈ nj.owners) →
      (∀ j, lo ≤ j → j ≤ hi → sel j = x → ∀ nj, g.node? (sel j) = some nj →
        ∃ p ∈ nj.parents, ∃ np, g.node? p = some np ∧ r ∈ np.owners) →
      ∀ j, lo ≤ j → j ≤ hi → ∀ nj', (reviewNode g (·.parents) x).node? (sel j) = some nj' →
        r ∈ nj'.owners := by
    intro r hr hx j hj1 hj2 nj' hnj'
    obtain ⟨n, hn, _, _, hne, heq⟩ := lift _ nj' hnj'
    if hjx : sel j = x then
      rw [heq hjx]
      obtain ⟨p, hp, np, hnp, hrp⟩ := hx j hj1 hj2 hjx n hn
      exact SegReview.mem_intersect_of_parent g n r (hr j hj1 hj2 n hn) p hp np hnp hrp
    else
      rw [hne hjx]; exact hr j hj1 hj2 n hn
  obtain ⟨hlsome, hls⟩ := hsG.1.1 lo (Int.le_refl _) hlohi
  obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp hlsome
  if hlx : sel lo = x then
    have hlo1 : 1 ≤ lo := by rw [← hls, hlx]; exact hx1
    obtain ⟨r0, hr0s, hr0l, hr0all⟩ := hseg sel lo hi hlo0 hlohi hhi hsG.1 hsG.2 (lo - 1) (by omega)
      (by omega) (Or.inl (by omega))
    have hr0p : r0 ∈ nl.parents :=
      hI1 _ nl hnl r0 (hr0all lo (Int.le_refl _) hlohi nl hnl) hr0l (by rw [hr0s, hls]; omega)
    obtain ⟨nr0, hnr0⟩ := Option.isSome_iff_exists.mp (hplive _ nl hnl r0 hr0p)
    have hback := hlsym sel lo hi hlohi hsG r0 nr0 hnr0 hr0s hr0all
    have hs' := SegReview.seg_extend g sel lo hi hlohi hsG r0 nr0 hnr0 hr0s
      (fun nl' hnl' => by rw [← Option.some.inj (hnl.symm.trans hnl')]; exact hr0p) hr0all hback
    have hxonly : ∀ j, lo ≤ j → j ≤ hi → sel j = x → j = lo := by
      intro j hj1 hj2 hjx
      have := (hsG.1.1 j hj1 hj2).2
      rw [hjx, ← hlx, hls] at this; omega
    rcases int_eq_or_ne i (lo - 1) with hie | hie
    · refine ⟨r0, by omega, live r0 hr0l, keep r0 hr0all (fun j hj1 hj2 hjx nj hnj => ?_)⟩
      rw [hxonly j hj1 hj2 hjx] at hnj
      rw [← Option.some.inj (hnl.symm.trans hnj)]
      exact ⟨r0, hr0p, nr0, hnr0, hself _ nr0 hnr0⟩
    · obtain ⟨r, hrs, hrl, hrall⟩ := hseg _ (lo - 1) hi (by omega) (by omega) hhi hs'.1 hs'.2 i hi0
        hic (by omega)
      have hr : ∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r ∈ nj.owners := by
        intro j hj1 hj2 nj hnj
        have := hrall j (by omega) hj2 nj
        rw [upd_other sel (lo - 1) r0 (by omega)] at this
        exact this hnj
      refine ⟨r, hrs, live r hrl, keep r hr (fun j hj1 hj2 hjx nj hnj => ?_)⟩
      rw [hxonly j hj1 hj2 hjx] at hnj
      rw [← Option.some.inj (hnl.symm.trans hnj)]
      have hrr0 := hrall (lo - 1) (Int.le_refl _) (by omega) nr0
      rw [upd_self] at hrr0
      exact ⟨r0, hr0p, nr0, hnr0, hrr0 hnr0⟩
  else
    obtain ⟨r, hrs, hrl, hrall⟩ := hseg sel lo hi hlo0 hlohi hhi hsG.1 hsG.2 i hi0 hic hout
    refine ⟨r, hrs, live r hrl, keep r hrall (fun j hj1 hj2 hjx nj hnj => ?_)⟩
    have hjlo : j ≠ lo := fun h => hlx (by rw [← h]; exact hjx)
    obtain ⟨hps, _⟩ := hsG.1.1 (j - 1) (by omega) (by omega)
    obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp hps
    have hl := hsG.1.2 (j - 1) (by omega) (by omega)
    rw [show j - 1 + 1 = j by omega, hnj] at hl
    simp only [Option.map_some, Option.getD_some] at hl
    exact ⟨sel (j - 1), hl, np, hnp, hrall (j - 1) (by omega) (by omega) np hnp⟩

/-- info: 'AbsSat.GraphPath.Model.PassCtx.segGoodL_reviewNode_parents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segGoodL_reviewNode_parents

end AbsSat.GraphPath.Model.PassCtx
