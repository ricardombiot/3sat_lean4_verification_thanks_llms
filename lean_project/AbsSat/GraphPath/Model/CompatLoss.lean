-- lean_project/AbsSat/GraphPath/Model/CompatLoss.lean
import AbsSat.GraphPath.Model.PassPlain
import AbsSat.GraphPath.Model.Threaded

/-!
# Una entrada solo sale de una tabla si pierde un nodo común (S1′)

Postulado del autor (2026-09-23), medido con `row-degree roundseg` (semilla 1: 375 de 375): en una
vuelta del review, una entrada común `r` de un tramo que sigue viva solo deja de estar en la tabla de
un nodo `x` del tramo si `r` y `x` dejan de compartir un nodo en algún otro paso.

Aquí, el mecanismo local, en las dos pasadas:

* **padres** (`sep_of_drop_parents`): el corte de `x` con la unión de las tablas de sus padres quita
  `r` solo si ningún padre tiene a `r`. Si la nueva tabla de `x` y la de `r` compartieran un nodo `q`
  en el paso de debajo de `x`, `q` sería padre de `x` (`I1`), `r` estaría en la tabla de `q`
  (simetría) y el corte habría conservado a `r`. Luego, al salir, `r` y `x` **no comparten nada en el
  paso `x − 1`**;
* **hijos** (`sep_of_drop_sons`): lo mismo en el paso `x + 1`;
* y esa separación **dura el resto de la vuelta** (`Sep.of_pruned`): las tablas solo encogen.

El paso de «ningún nodo que `x` conserva en el paso de sus padres tiene a `r`» (`lost_parents_nosym`,
sin hipótesis de simetría) a «`x` y `r` no comparten nada ahí» (`lost_parents`) usa la simetría de la
propiedad entre nodos (`Threaded.OwnSymmetric`) en el estado de antes del corte. Está demostrada al
final de la review agresiva (`ownSymmetric_of_aggOk`), **no** en los estados intermedios de las
pasadas, donde un corte anterior puede haberla roto: es la hipótesis abierta de este módulo.
-/

namespace AbsSat.GraphPath.Model.CompatLoss

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.PassPlain (OwnLive I1 I1s)

/-- **`x` y `r` no comparten ningún nodo en el paso `k`.** -/
def Sep (g : GPathM) (x r : PathNodeId) (k : Int) : Prop :=
  ∀ nx nr, g.node? x = some nx → g.node? r = some nr →
    ∀ q ∈ nx.owners, q.id.step = k → q ∉ nr.owners

/-- **La separación dura**: tras cualquier estrechamiento las tablas solo han encogido. -/
theorem Sep.of_pruned {g g' : GPathM} (hpr : Pruned g g') (hnd : NodupIds g) {x r : PathNodeId}
    {k : Int} (h : Sep g x r k) : Sep g' x r k := by
  intro nx' nr' hx' hr' q hq hqk hqr
  obtain ⟨nx, hnx, hidx, hownx, _⟩ := hpr.nodes_derived nx' (List.mem_of_find?_eq_some hx')
  obtain ⟨nr, hnr, hidr, hownr, _⟩ := hpr.nodes_derived nr' (List.mem_of_find?_eq_some hr')
  have hgx : g.node? x = some nx := by
    rw [← node?_id_eq _ x nx' hx', hidx]; exact node?_of_mem hnd nx hnx
  have hgr : g.node? r = some nr := by
    rw [← node?_id_eq _ r nr' hr', hidr]; exact node?_of_mem hnd nr hnr
  exact h nx nr hgx hgr q (hownx q hq) hqk (hownr q hqr)

-- ============================================================
-- El corte de la pasada de padres
-- ============================================================

/-- **Sin simetría: si el corte con los padres quita `r`, ningún nodo que `x` conserva en el paso de
sus padres tiene a `r` en su tabla.** Es el hecho local tal cual; con simetría entre nodos se convierte
en `lost_parents`. -/
theorem lost_parents_nosym (g : GPathM) (hI1 : I1 g)
    (x : PathNodeId) (d : PNodeM) (hd : g.node? x = some d)
    (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1)
    (r : PathNodeId) (hr : r ∈ d.owners)
    (hdrop : r ∉ intersectOwners d.owners (unionOwnersOf g d.parents)) :
    ∀ q ∈ intersectOwners d.owners (unionOwnersOf g d.parents), q.id.step = x.id.step - 1 →
      ∀ nq, g.node? q = some nq → r ∉ nq.owners := by
  intro q hq hqs nq hnq hrq
  have hqd : q ∈ d.owners := (List.mem_filter.mp hq).1
  have hqpar : q ∈ d.parents := hI1 x d hd q hqd (by omega) (by omega) (by omega)
  exact hdrop (mem_intersectOwners_of_mem_union d.owners g d.parents r hr
    (mem_unionOwnersOf g d.parents q nq r hqpar hnq hrq))

/-- The sons mirror of `lost_parents_nosym`. -/
theorem lost_sons_nosym (g : GPathM) (hI1s : I1s g)
    (x : PathNodeId) (d : PNodeM) (hd : g.node? x = some d)
    (hx0 : 0 ≤ x.id.step) (hxl : x.id.step ≤ g.current_step - 2)
    (r : PathNodeId) (hr : r ∈ d.owners)
    (hdrop : r ∉ intersectOwners d.owners (unionOwnersOf g d.sons)) :
    ∀ q ∈ intersectOwners d.owners (unionOwnersOf g d.sons), q.id.step = x.id.step + 1 →
      ∀ nq, g.node? q = some nq → r ∉ nq.owners := by
  intro q hq hqs nq hnq hrq
  have hqd : q ∈ d.owners := (List.mem_filter.mp hq).1
  have hqson : q ∈ d.sons := hI1s x d hd q hqd (by omega) (by omega) hqs
  exact hdrop (mem_intersectOwners_of_mem_union d.owners g d.sons r hr
    (mem_unionOwnersOf g d.sons q nq r hqson hnq hrq))

/-- **Si el corte con los padres quita `r`, la tabla cortada no comparte nada con la de `r` en el paso
de los padres.** -/
theorem lost_parents (g : GPathM) (hsym : Threaded.OwnSymmetric g) (hI1 : I1 g) (hol : OwnLive g)
    (x : PathNodeId) (d : PNodeM) (hd : g.node? x = some d)
    (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1)
    (r : PathNodeId) (nr : PNodeM) (hnr : g.node? r = some nr) (hr : r ∈ d.owners)
    (hdrop : r ∉ intersectOwners d.owners (unionOwnersOf g d.parents)) :
    ∀ q ∈ intersectOwners d.owners (unionOwnersOf g d.parents), q.id.step = x.id.step - 1 →
      q ∉ nr.owners := by
  intro q hq hqs hqr
  have hqd : q ∈ d.owners := (List.mem_filter.mp hq).1
  have hqpar : q ∈ d.parents := hI1 x d hd q hqd (by omega) (by omega) (by omega)
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (hol x d hd q hqd (by omega) (by omega))
  have hrq : r ∈ nq.owners := hsym r nr q nq hnr hnq hqr
  exact hdrop (mem_intersectOwners_of_mem_union d.owners g d.parents r hr
    (mem_unionOwnersOf g d.parents q nq r hqpar hnq hrq))

/-- **El corte con los hijos**: lo mismo en el paso de los hijos. -/
theorem lost_sons (g : GPathM) (hsym : Threaded.OwnSymmetric g) (hI1s : I1s g) (hol : OwnLive g)
    (x : PathNodeId) (d : PNodeM) (hd : g.node? x = some d)
    (hx0 : 0 ≤ x.id.step) (hxl : x.id.step ≤ g.current_step - 2)
    (r : PathNodeId) (nr : PNodeM) (hnr : g.node? r = some nr) (hr : r ∈ d.owners)
    (hdrop : r ∉ intersectOwners d.owners (unionOwnersOf g d.sons)) :
    ∀ q ∈ intersectOwners d.owners (unionOwnersOf g d.sons), q.id.step = x.id.step + 1 →
      q ∉ nr.owners := by
  intro q hq hqs hqr
  have hqd : q ∈ d.owners := (List.mem_filter.mp hq).1
  have hqson : q ∈ d.sons := hI1s x d hd q hqd (by omega) (by omega) hqs
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (hol x d hd q hqd (by omega) (by omega))
  have hrq : r ∈ nq.owners := hsym r nr q nq hnr hnq hqr
  exact hdrop (mem_intersectOwners_of_mem_union d.owners g d.sons r hr
    (mem_unionOwnersOf g d.sons q nq r hqson hnq hrq))

-- ============================================================
-- En el estado: tras `reviewNode x`, `x` y `r` quedan separados
-- ============================================================

/-- The owners of `r` after `reviewNode x` (x kept) are inside its owners before. -/
theorem owners_after_sub (g : GPathM) (hnd : NodupIds g) (nb : PNodeM → List PathNodeId)
    (x r : PathNodeId) (nr : PNodeM) (hnr : g.node? r = some nr) (nr' : PNodeM)
    (hnr' : (reviewNode g nb x).node? r = some nr') : ∀ q ∈ nr'.owners, q ∈ nr.owners := by
  have hpr := pruned_reviewNode nb x g
  obtain ⟨n0, hn0, hid, hown, _⟩ := hpr.nodes_derived nr' (List.mem_of_find?_eq_some hnr')
  have hg : g.node? r = some n0 := by
    rw [← node?_id_eq _ r nr' hnr', hid]; exact node?_of_mem hnd n0 hn0
  rw [hnr] at hg
  cases hg
  exact hown

/-- The owners of `x` after `reviewNode x` (x kept) are its cut table. -/
theorem owners_self_after (g : GPathM) (nb : PNodeM → List PathNodeId) (x : PathNodeId)
    (d : PNodeM) (hd : g.node? x = some d) (hk : ((reviewNode g nb x).node? x).isSome = true)
    (nx' : PNodeM) (hnx' : (reviewNode g nb x).node? x = some nx') :
    nx'.owners = intersectOwners d.owners (unionOwnersOf g (nb d)) := by
  rw [PassCtx.node_after g nb x d hd hk x d hd, if_pos rfl] at hnx'
  cases hnx'
  rw [unlinkMap_owners]

/-- **Pasada de padres**: si `reviewNode x` conserva `x` pero quita `r` de su tabla, al salir `x` y
`r` no comparten nada en el paso `x − 1`. -/
theorem sep_of_drop_parents (g : GPathM) (hnd : NodupIds g) (hsym : Threaded.OwnSymmetric g)
    (hI1 : I1 g) (hol : OwnLive g) (x : PathNodeId) (d : PNodeM) (hd : g.node? x = some d)
    (hx1 : 1 ≤ x.id.step) (hxc : x.id.step ≤ g.current_step - 1)
    (hk : ((reviewNode g (·.parents) x).node? x).isSome = true)
    (r : PathNodeId) (nr : PNodeM) (hnr : g.node? r = some nr) (hr : r ∈ d.owners)
    (hdrop : r ∉ intersectOwners d.owners (unionOwnersOf g d.parents)) :
    Sep (reviewNode g (·.parents) x) x r (x.id.step - 1) := by
  intro nx' nr' hx' hr' q hq hqk hqr
  rw [owners_self_after g (·.parents) x d hd hk nx' hx'] at hq
  exact lost_parents g hsym hI1 hol x d hd hx1 hxc r nr hnr hr hdrop q hq hqk
    (owners_after_sub g hnd _ x r nr hnr nr' hr' q hqr)

/-- **Pasada de hijos**: lo mismo en el paso `x + 1`. -/
theorem sep_of_drop_sons (g : GPathM) (hnd : NodupIds g) (hsym : Threaded.OwnSymmetric g)
    (hI1s : I1s g) (hol : OwnLive g) (x : PathNodeId) (d : PNodeM) (hd : g.node? x = some d)
    (hx0 : 0 ≤ x.id.step) (hxl : x.id.step ≤ g.current_step - 2)
    (hk : ((reviewNode g (·.sons) x).node? x).isSome = true)
    (r : PathNodeId) (nr : PNodeM) (hnr : g.node? r = some nr) (hr : r ∈ d.owners)
    (hdrop : r ∉ intersectOwners d.owners (unionOwnersOf g d.sons)) :
    Sep (reviewNode g (·.sons) x) x r (x.id.step + 1) := by
  intro nx' nr' hx' hr' q hq hqk hqr
  rw [owners_self_after g (·.sons) x d hd hk nx' hx'] at hq
  exact lost_sons g hsym hI1s hol x d hd hx0 hxl r nr hnr hr hdrop q hq hqk
    (owners_after_sub g hnd _ x r nr hnr nr' hr' q hqr)

-- ============================================================
-- `reviewNode x` solo toca la tabla de `x`
-- ============================================================

/-- **Solo cambia la tabla del nodo que se procesa**: tras `reviewNode x`, cualquier otro nodo que
siga vivo tiene la misma tabla (el desenlace solo toca padres e hijos). Así, dentro de una pasada, una
tabla solo pierde entradas en el `reviewNode` de su propio nodo, que es donde valen
`lost_parents_nosym` y `lost_sons_nosym`. -/
theorem owners_other_reviewNode (g : GPathM) (nb : PNodeM → List PathNodeId) (x y : PathNodeId)
    (hne : y ≠ x) (ny : PNodeM) (hny : g.node? y = some ny) (ny' : PNodeM)
    (hny' : (reviewNode g nb x).node? y = some ny') : ny'.owners = ny.owners := by
  have hid : ny.id = y := node?_id_eq g y ny hny
  have hbeq : (ny.id == x) = false := PassCtx.beq_false_of_ne' ny.id x (by rw [hid]; exact hne)
  unfold reviewNode at hny'
  cases hd : g.node? x with
  | none => rw [hd] at hny'; rw [hny] at hny'; cases hny'; rfl
  | some d =>
    rw [hd] at hny'
    have hdid : d.id = x := node?_id_eq g x d hd
    let f := fun n : PNodeM => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) }
    have h1y : (updateAt g x f).node? y = some ny := by
      rw [updateAt_node? g x f (fun _ => rfl) y ny hny, hbeq]
    have h1x : (updateAt g x f).node? x = some (f d) := by
      rw [updateAt_node? g x f (fun _ => rfl) x d hd, show (d.id == x) = true from beq_iff_eq.mpr hdid]
    have h2y : (unlinkIncompatible (updateAt g x f) x).node? y = some (unlinkMap (f d) x ny) :=
      unlinkIncompatible_node? _ x (f d) h1x y ny h1y
    dsimp only at hny'
    split at hny'
    · split at hny'
      · rw [h2y] at hny'; cases hny'; exact unlinkMap_owners _ _ _
      · rw [removeNode_node? _ x y _ h2y hne] at hny'; cases hny'
        exact unlinkMap_owners _ _ _
    · rw [removeNode_node? g x y ny hny hne] at hny'; cases hny'; rfl

/-- info: 'AbsSat.GraphPath.Model.CompatLoss.owners_other_reviewNode' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms owners_other_reviewNode

/-- info: 'AbsSat.GraphPath.Model.CompatLoss.sep_of_drop_parents' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms sep_of_drop_parents

/-- info: 'AbsSat.GraphPath.Model.CompatLoss.sep_of_drop_sons' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms sep_of_drop_sons

/-- info: 'AbsSat.GraphPath.Model.CompatLoss.Sep.of_pruned' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Sep.of_pruned

/-- info: 'AbsSat.GraphPath.Model.CompatLoss.lost_parents_nosym' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms lost_parents_nosym

end AbsSat.GraphPath.Model.CompatLoss
