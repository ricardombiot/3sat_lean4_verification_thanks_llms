-- lean_project/AbsSat/GraphPath/Model/AncestorOwned.lean
import AbsSat.GraphPath.Model.SupportedRun
import AbsSat.GraphPath.Model.DescentUp

/-!
# Un nodo posee a todos sus ancestros

El autor lo dice del diseño: *«cuando se construye un nuevo nodo se le da la compatibilidad con
todos sus ancestros, siendo sus owners la unión de los de sus padres»*. Este módulo escribe esa
frase y la usa.

* **`Anc g y a`** — `a` es `y` o un ancestro suyo, por padres iterados.
* **`AncOwned g`** — la tabla de todo nodo contiene a todos sus ancestros.

Y de ahí sale el residuo que quedaba de la ruta B de un tirón:

* **`pairwiseOwned_of_ancOwned`** — una cadena enlazada es un camino de ancestros, así que sus
  nodos se poseen entre sí: hacia abajo por `AncOwned`, hacia arriba por la simetría de owners.
* **`chainPairwise_of_ancOwned`**, **`supportedS_of_ancOwned`** — con eso, `SupportedS`, y por
  tanto que el lector sin retroceso no se atasca.

Lo que hace distinto a `AncOwned` de las cinco hipótesis que esta sesión vio caerse (`ParentMeet`,
`PairMeet`, `DecidedAbove`, `TableDownClosed`, `AllParentsOwn`) es la forma del enunciado: habla de
**dos** nodos y la relación padre-hijo entre ellos, no de tríos. Es del lado de la frontera donde
viven `SupportedG` y `TablesSound`, las dos que se miden al 100%.

Y el nacimiento está demostrado:

* **`ancOwned_addNode`** — **`up` la conserva**, y la prueba es literalmente `rowOwners`: la fila
  nueva hereda entera la tabla de cada padre (`owners_sub_rowOwners`), y la tabla de cada padre ya
  contenía a sus ancestros. El recorte a `gowners` no estorba porque un owner de un nodo vivo en
  rango es owner global (`ownGow`).

Nótese la diferencia con `TableDownClosed`, que colapsaba a `SingleParents`: aquella cuantificaba
sobre *los padres de lo que una tabla contiene*, sin cota de paso, y se llevaba por delante a los
hermanos. `AncOwned` recorre solo hacia abajo desde el propio nodo, que es la dirección en la que
`rowOwners` hereda de verdad.

Lo que queda por ver es qué le hace la revisión — y ahí, a diferencia de las hipótesis caídas, hay
una razón de diseño para que no la rompa: la criba borra `w` de la tabla de `x` cuando no comparten
owner en algún paso, y un ancestro comparte con su descendiente toda la cadena que los une.
-/

namespace AbsSat.GraphPath.Model.AncestorOwned

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Descent (SupportedS)

-- ============================================================
-- La relación y el invariante
-- ============================================================

/-- **`a` es `y` o un ancestro suyo**: se llega de `y` a `a` bajando por padres. -/
inductive Anc (g : GPathM) : PathNodeId → PathNodeId → Prop
  | refl (y : PathNodeId) : Anc g y y
  | step {y c a : PathNodeId} {n : PNodeM} :
      g.node? y = some n → c ∈ n.parents → Anc g c a → Anc g y a

/-- **La tabla de todo nodo contiene a todos sus ancestros.** La frase del autor sobre el diseño,
escrita como invariante de estado. -/
def AncOwned (g : GPathM) : Prop :=
  ∀ y n, g.node? y = some n → ∀ a, Anc g y a → a ∈ n.owners

/-- Un ancestro está en un paso menor o igual: cada salto baja uno. -/
theorem anc_step_le (g : GPathM) (hshape : Parents.Shape g) {y a : PathNodeId}
    (h : Anc g y a) : a.id.step ≤ y.id.step := by
  induction h with
  | refl z => exact Int.le_refl _
  | @step z c b n hz hc _ ih =>
      have hid : n.id = z := node?_id_eq g z n hz
      have hp := hshape.pbelow n (List.mem_of_find?_eq_some hz) c hc
      rw [hid] at hp
      omega

/-- Y sigue siendo un nodo: los padres de un nodo son nodos. -/
theorem anc_isSome (g : GPathM) (hshape : Parents.Shape g) (hnd : NodupIds g)
    {y a : PathNodeId} (h : Anc g y a) :
    (g.node? y).isSome = true → (g.node? a).isSome = true := by
  induction h with
  | refl _ => exact id
  | @step z c b n hz hc _ ih =>
      intro _
      obtain ⟨mc, hmc, hmcid⟩ := hshape.pn n (List.mem_of_find?_eq_some hz) c hc
      refine ih ?_
      rw [← hmcid, node?_of_mem hnd mc hmc]
      rfl

-- ============================================================
-- El residuo de la ruta B, cerrado
-- ============================================================

/-- **Una cadena enlazada sube por ancestros**, por inducción sobre la distancia. -/
theorem anc_of_chain_add (g : GPathM) (sel : Int → PathNodeId) (hchain : IsChain g sel)
    (i : Int) (hi : 0 ≤ i) :
    ∀ dist : Nat, i + (dist : Int) < g.current_step → Anc g (sel (i + (dist : Int))) (sel i) := by
  intro dist
  induction dist with
  | zero => intro _; simpa using Anc.refl (g := g) (sel i)
  | succ m ih =>
      intro hlt
      have hcast : i + ((m + 1 : Nat) : Int) = (i + (m : Int)) + 1 := by push_cast; omega
      rw [hcast] at hlt ⊢
      have hm0 : (0 : Int) ≤ (m : Int) := Int.natCast_nonneg m
      have hlink := hchain.2 (i + (m : Int)) (by omega) hlt
      obtain ⟨hs, _⟩ := hchain.1 ((i + (m : Int)) + 1) (by omega) hlt
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
      rw [hn] at hlink
      simp only [Option.map_some, Option.getD_some] at hlink
      exact Anc.step hn hlink (ih (by omega))

theorem anc_of_chain_le (g : GPathM) (sel : Int → PathNodeId) (hchain : IsChain g sel)
    {i j : Int} (hi : 0 ≤ i) (hij : i ≤ j) (hj : j < g.current_step) :
    Anc g (sel j) (sel i) := by
  obtain ⟨dist, hdist⟩ : ∃ dist : Nat, j = i + (dist : Int) := ⟨(j - i).toNat, by omega⟩
  subst hdist
  exact anc_of_chain_add g sel hchain i hi dist hj

/-- **Y entonces los nodos de una cadena enlazada se poseen entre sí.**

Es el residuo entero de la ruta B (`SupportedRun.ChainPairwise`), y se parte en dos mitades que no
piden nada más: hacia abajo lo da `AncOwned` —el de arriba es descendiente del de abajo—, y hacia
arriba lo devuelve la simetría de owners. -/
theorem pairwiseOwned_of_ancOwned (g : GPathM) (hsym : Threaded.OwnSymmetric g)
    (hao : AncOwned g) (sel : Int → PathNodeId) (hchain : IsChain g sel) :
    PairwiseOwned g sel := by
  intro i j hi hj hi1 hj1 hne
  obtain ⟨hsi, hstepi⟩ := hchain.1 i hi hi1
  obtain ⟨hsj, _⟩ := hchain.1 j hj hj1
  obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp hsi
  obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp hsj
  simp only [ownersAt, ownersOf, hnj, List.mem_filter, beq_iff_eq]
  refine ⟨?_, hstepi⟩
  have hlt : i < j ∨ j < i := by omega
  rcases hlt with h | h
  · exact hao (sel j) nj hnj (sel i) (anc_of_chain_le g sel hchain hi (by omega) hj1)
  · exact hsym (sel i) ni (sel j) nj hni hnj
      (hao (sel i) ni hni (sel j) (anc_of_chain_le g sel hchain hj (by omega) hi1))

/-- El residuo de la ruta B, en los términos en que estaba escrito. -/
theorem chainPairwise_of_ancOwned (g : GPathM) (hsym : Threaded.OwnSymmetric g)
    (hao : AncOwned g) : SupportedRun.ChainPairwise g :=
  fun _ _ _ sel hchain _ => pairwiseOwned_of_ancOwned g hsym hao sel hchain

/-- **Y con eso `SupportedS`**: todo nodo del estado está en una cadena sana, que es lo que hace
que el lector sin retroceso nunca se quede sin continuación. -/
theorem supportedS_of_ancOwned (g : GPathM) (a : AdjacentOwners.Adj g) (hsmp : Sons.SMP g)
    (ctx : Threaded.TCtx g) (hsym : Threaded.OwnSymmetric g) (hpos : 0 < g.current_step)
    (hao : AncOwned g) : SupportedS g :=
  SupportedRun.supportedS_of_chainPairwise g a hsmp ctx hsym hpos
    (chainPairwise_of_ancOwned g hsym hao)

-- ============================================================
-- El nacimiento: `up` la conserva
-- ============================================================

/-- Por debajo del paso nuevo, un ancestro del estado extendido lo es del estado. -/
theorem anc_of_addNode_below (g : GPathM) (d : NodeId) (title : String)
    (hd : d.step = g.current_step) (hshape : Parents.Shape g)
    {y a : PathNodeId} (h : Anc (addNode g d title) y a) :
    y.id.step < g.current_step → Anc g y a := by
  induction h with
  | refl z => intro _; exact Anc.refl (g := g) z
  | @step z c b n hz hc _ ih =>
      intro hzs
      obtain ⟨m, hm, hEq⟩ := addNode_node?_below g d title hd z n hz hzs
      have hcm : c ∈ m.parents := by rw [hEq, upMap_parents] at hc; exact hc
      have hp := hshape.pbelow m (List.mem_of_find?_eq_some hm) c hcm
      rw [node?_id_eq g z m hm] at hp
      exact Anc.step hm hcm (ih (by omega))

/-- **`up` conserva la frase del autor, y la prueba es `rowOwners` leída literal.**

El nodo de fila nace con la unión de las tablas de sus padres recortada a `gowners`
(`owners_sub_rowOwners`). Cada padre ya contenía a sus propios ancestros por hipótesis, y esos
ancestros siguen vivos globalmente porque son owners de un nodo válido dentro del rango
(`ownGow`). Así que la fila nueva nace poseyendo a **todos** sus ancestros, que es exactamente lo
que el autor describe. Los nodos viejos no cambian de padres y solo ganan owners del paso nuevo,
así que conservan la suya sin tocar. -/
theorem ancOwned_addNode (g : GPathM) (d : NodeId) (title : String)
    (hnd : NodupIds g) (hshape : Parents.Shape g) (hsnn : SelfOwn.SNN g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step)
    (hgow : ∀ pid n, g.node? pid = some n → ∀ q ∈ n.owners,
      0 ≤ q.id.step → q.id.step < g.current_step → q ∈ g.gowners)
    (hd : d.step = g.current_step) (hpos : 0 < g.current_step)
    (hao : AncOwned g) : AncOwned (addNode g d title) := by
  intro y n hy b hb
  rcases DescentUp.node_addNode_cases g d title hnd hy with ⟨hrow, hn⟩ | ⟨m, hm, hn⟩
  · -- nodo de la fila nueva
    subst hn
    cases hb with
    | refl _ => rw [rowNode_owners]; exact self_mem_rowOwners g d y
    | @step _ c _ n' hz hc hanc =>
        -- `n'` es el mismo nodo, así que `c` es un padre de fila
        have hn' : n' = rowNode g d title y := by
          rw [hy] at hz; exact (Option.some.inj hz).symm
        have hcrow : c ∈ rowParents g d y := by rw [hn', rowNode_parents] at hc; exact hc
        obtain ⟨hcs, hcstep⟩ := rowParent_node g d hpos hcrow
        obtain ⟨mc, hmc⟩ := Option.isSome_iff_exists.mp hcs
        -- el ancestro lo es ya del estado de antes
        have hancg : Anc g c b :=
          anc_of_addNode_below g d title hd hshape hanc (by omega)
        have hbmc : b ∈ mc.owners := hao c mc hmc b hancg
        -- y sigue vivo globalmente: es owner de un nodo válido dentro del rango
        have hble : b.id.step ≤ c.id.step := anc_step_le g hshape hancg
        have hbnode := anc_isSome g hshape hnd hancg (by rw [hmc]; rfl)
        obtain ⟨mb, hmb⟩ := Option.isSome_iff_exists.mp hbnode
        have hb0 : 0 ≤ b.id.step := by
          have := hsnn mb (List.mem_of_find?_eq_some hmb)
          rwa [node?_id_eq g b mb hmb] at this
        have hbg : g.gowners.contains b = true :=
          List.elem_eq_true_of_mem (hgow c mc hmc b hbmc hb0 (by omega))
        rw [rowNode_owners]
        exact Descent.owners_sub_rowOwners g d y c mc hcrow hmc b hbmc hbg
  · -- nodo viejo: ni cambia de padres ni pierde owners
    subst hn
    have hys : y.id.step < g.current_step := by
      have := hbelow m (List.mem_of_find?_eq_some hm)
      rwa [node?_id_eq g y m hm] at this
    rw [upMap_owners]
    exact List.mem_append_left _
      (hao y m hm b (anc_of_addNode_below g d title hd hshape hb hys))

/-- info: 'AbsSat.GraphPath.Model.AncestorOwned.pairwiseOwned_of_ancOwned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairwiseOwned_of_ancOwned

/-- info: 'AbsSat.GraphPath.Model.AncestorOwned.supportedS_of_ancOwned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms supportedS_of_ancOwned

/-- info: 'AbsSat.GraphPath.Model.AncestorOwned.ancOwned_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ancOwned_addNode

end AbsSat.GraphPath.Model.AncestorOwned
