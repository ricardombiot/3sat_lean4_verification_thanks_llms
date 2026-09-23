-- lean_project/AbsSat/GraphPath/Model/TopGoodUp.lean
import AbsSat.GraphPath.Model.OwnerChainedBuild
import AbsSat.GraphPath.Model.L6Up
import AbsSat.GraphPath.Model.BranchRun

/-!
# «Toda cadena desde la cima es buena», y el `up` lo conserva

`OwnerChainedBuild.AnyOptionStep` pide que la tabla colectiva de lo elegido **desde la cima** no se
quede vacía en ningún paso de abajo. Las sondas lo dicen así (`row-degree chainshare`): una cadena
enlazada por padres, poseída por pares y con un anfitrión `a` tiene entrada común por debajo **si
arranca en la cima** —0 fallos en 133.623— y no en general.

Este módulo escribe esa propiedad (`TopGood`) y demuestra la mitad del `up`: **el `up` la conserva**,
sin hipótesis sobre el review. La razón es la construcción de la fila (`rowOwners`): la tabla de un
nodo nuevo es la unión de las de sus padres recortada a la tabla global, así que lo que la cadena
tenía en común lo tiene también el hijo de su cima. Medido en `row-degree upextend`: 628.961 de
628.961 cadenas prolongadas, por **cualquier** hijo.

Lo que queda para la inducción es la otra mitad: que el filtro y el review, que solo quitan, dejen
buena toda cadena desde la cima que sobrevive.
-/

namespace AbsSat.GraphPath.Model.TopGoodUp

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM

/-- **Toda cadena desde la cima, con un anfitrión, es buena.** Una cadena parcial de `lo` a la cima,
enlazada por padres, poseída por pares y poseída mutuamente con `a`, tiene en cada paso de abajo
una entrada común a la tabla de `a` y a las de toda la cadena. -/
def TopGood (g : GPathM) : Prop :=
  ∀ a na, g.node? a = some na → ∀ (sel : Int → PathNodeId) (lo : Int), 0 ≤ lo →
    lo ≤ g.current_step - 1 →
    Extendable.PartialChain g sel lo (g.current_step - 1) →
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ g.current_step - 1 → j ≤ g.current_step - 1 → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners) →
    (∀ j, lo ≤ j → j ≤ g.current_step - 1 →
      sel j ∈ na.owners ∧ ∀ nj, g.node? (sel j) = some nj → a ∈ nj.owners) →
    ∀ i, 0 ≤ i → i < lo → ∃ r, r.id.step = i ∧ r ∈ na.owners ∧
      ∀ j, lo ≤ j → j ≤ g.current_step - 1 → ∀ nj, g.node? (sel j) = some nj → r ∈ nj.owners

-- ============================================================
-- Las tablas tras el `up`
-- ============================================================

/-- Un nodo antiguo, por debajo de la fila nueva, tiene la misma tabla. -/
theorem old_mem (P : GPathM) (d : NodeId) (hd : d.step = P.current_step) (n : PNodeM)
    (q : PathNodeId) (hq : q.id.step < P.current_step) :
    q ∈ (upMap P d n).owners ↔ q ∈ n.owners := by
  rw [upMap_owners, List.mem_append]
  refine ⟨fun h => h.resolve_right (fun hg => ?_), Or.inl⟩
  have := mapId_of_mem_newRowIds P d q (gainedOwners_subset P d n q hg)
  rw [this, hd] at hq
  omega

/-- Un nodo de la fila, por debajo de su paso: lo que hereda de sus padres, recortado a la tabla
global. -/
theorem row_mem_below (P : GPathM) (d : NodeId) (hd : d.step = P.current_step) (w : PathNodeId)
    (hw : w ∈ newRowIds P d) (q : PathNodeId) (hq : q.id.step < P.current_step) :
    q ∈ rowOwners P d w ↔ q ∈ unionOwnersOf P (rowParents P d w) ∧ q ∈ P.gowners := by
  rw [mem_rowOwners_iff]
  refine ⟨fun h => h.resolve_right (fun he => ?_), Or.inl⟩
  have := mapId_of_mem_newRowIds P d w hw
  rw [he, this, hd] at hq
  omega

/-- En su propio paso, un nodo de la fila solo se posee a sí mismo. -/
theorem row_mem_top (P : GPathM) (d : NodeId)
    (hgs : ∀ q ∈ P.gowners, q.id.step < P.current_step) (w q : PathNodeId)
    (hq : q ∈ rowOwners P d w) (hqs : q.id.step = P.current_step) : q = w := by
  rcases (mem_rowOwners_iff P d w q).mp hq with ⟨_, hg⟩ | he
  · have := hgs q hg; omega
  · exact he

/-- Lo que tiene un padre, y está en la tabla global, lo tiene el hijo de la fila. -/
theorem row_of_parent (P : GPathM) (d : NodeId) (w p : PathNodeId) (hp : p ∈ rowParents P d w)
    (np : PNodeM) (hnp : P.node? p = some np) (q : PathNodeId) (hq : q ∈ np.owners)
    (hg : q ∈ P.gowners) : q ∈ rowOwners P d w :=
  (mem_rowOwners_iff P d w q).mpr (Or.inl ⟨mem_unionOwnersOf P _ p np q hp hnp hq, hg⟩)

/-- Un nodo del estado nuevo es antiguo (por debajo) o de la fila. -/
theorem lookup (P : GPathM) (d : NodeId) (t : String) (hd : d.step = P.current_step)
    (hbelow : ∀ n ∈ P.nodes, n.id.id.step < P.current_step)
    (x : PathNodeId) (m : PNodeM) (hx : (addNode P d t).node? x = some m) :
    (x.id.step < P.current_step ∧ ∃ n, P.node? x = some n ∧ m = upMap P d n) ∨
      (x.id.step = P.current_step ∧ x ∈ newRowIds P d ∧ m = rowNode P d t x) := by
  rcases BranchRun.mem_addNode ⟨m, hx⟩ with hrow | ⟨n, hn⟩
  · right
    have hs : x.id.step = P.current_step := by rw [mapId_of_mem_newRowIds P d x hrow, hd]
    refine ⟨hs, hrow, ?_⟩
    rw [addNode_node?_new P d t hd hbelow x hrow] at hx
    exact (Option.some.inj hx).symm
  · left
    have hs : x.id.step < P.current_step := by
      have := hbelow n (List.mem_of_find?_eq_some hn)
      rwa [node?_id_eq P x n hn] at this
    refine ⟨hs, n, hn, ?_⟩
    rw [addNode_node?_old P d t x n hn] at hx
    exact (Option.some.inj hx).symm

/-- Un padre de la fila es un nodo del último paso. -/
theorem rowParent_node (P : GPathM) (hpos : 0 < P.current_step) (d : NodeId) (w p : PathNodeId)
    (hp : p ∈ rowParents P d w) :
    (∃ np, P.node? p = some np) ∧ p.id.step = P.current_step - 1 := by
  have hnp := rowParents_subset P d w p hp
  refine ⟨?_, step_of_mem_newParents P hpos p hnp⟩
  unfold newParents at hnp
  rw [if_pos hpos] at hnp
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hnp
  exact Option.isSome_iff_exists.mp (node?_isSome_of_mem P n (List.mem_filter.mp hn).1)

/-- Todo nodo de la fila tiene algún padre. -/
theorem row_has_parent (P : GPathM) (hpos : 0 < P.current_step) (d : NodeId) (w : PathNodeId)
    (hw : w ∈ newRowIds P d) : ∃ p, p ∈ rowParents P d w := by
  obtain ⟨q, hq, rfl⟩ := exists_shift_of_mem_newRowIds P d w hpos hw
  exact ⟨q, mem_rowParents_of_mem_newParents P d q hq⟩

-- ============================================================
-- La mitad del `up`
-- ============================================================

/-- **El `up` conserva «toda cadena desde la cima es buena».**

Una cadena del estado nuevo desde su cima termina en un nodo `v` de la fila. Por debajo de `v` es una
cadena del estado de antes, y desde su cima; la entrada común que allí tiene está en la tabla del
padre de `v` y en la tabla global, así que `rowOwners` la pone en la de `v`. Si el anfitrión es de la
fila, es el propio `v`, y hace de anfitrión su padre en la cadena. Y si la cadena es solo `v`, basta
un padre de `v`: la cadena de un solo nodo desde la cima del estado de antes. -/
theorem topGood_addNode (P : GPathM) (d : NodeId) (t : String) (hd : d.step = P.current_step)
    (hpos : 0 < P.current_step)
    (hbelow : ∀ n ∈ P.nodes, n.id.id.step < P.current_step)
    (hgs : ∀ q ∈ P.gowners, q.id.step < P.current_step)
    (hgow : ∀ pid n, P.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < P.current_step → q ∈ P.gowners)
    (hself : ∀ pid n, P.node? pid = some n → pid ∈ n.owners)
    (hsym : Threaded.OwnSymmetric P) (hg : TopGood P) :
    TopGood (addNode P d t) := by
  intro a na hna sel lo hlo0 hlo1 hch hpw hhost i hi0 hilo
  have hcsU : (addNode P d t).current_step - 1 = P.current_step := by rw [addNode_current]; omega
  rw [hcsU] at hlo1 hch hpw hhost ⊢
  -- la cima de la cadena es un nodo de la fila
  obtain ⟨hvsome, hvs⟩ := hch.1 P.current_step hlo1 (Int.le_refl _)
  obtain ⟨mv, hmv⟩ := Option.isSome_iff_exists.mp hvsome
  obtain ⟨hvrow, hmveq⟩ : sel P.current_step ∈ newRowIds P d ∧
      mv = rowNode P d t (sel P.current_step) := by
    rcases lookup P d t hd hbelow _ mv hmv with ⟨hlt, _⟩ | ⟨_, hr, he⟩
    · omega
    · exact ⟨hr, he⟩
  subst hmveq
  -- lo que tiene un padre de la cima y está en la tabla global, lo tiene la cima
  have toTop : ∀ p ∈ rowParents P d (sel P.current_step), ∀ np, P.node? p = some np →
      ∀ r ∈ np.owners, 0 ≤ r.id.step → r.id.step < P.current_step →
      r ∈ (rowNode P d t (sel P.current_step)).owners := fun p hp np hnp r hr h0 h1 =>
    row_of_parent P d _ p hp np hnp r hr (hgow p np hnp r hr h0 h1)
  -- los nodos antiguos de la cadena
  have oldAt : ∀ j, lo ≤ j → j ≤ P.current_step - 1 →
      ∃ nj, P.node? (sel j) = some nj ∧ (addNode P d t).node? (sel j) = some (upMap P d nj) := by
    intro j hj1 hj2
    obtain ⟨hs, hjs⟩ := hch.1 j hj1 (by omega)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    rcases lookup P d t hd hbelow _ m hm with ⟨_, n, hn, rfl⟩ | ⟨hst, _⟩
    · exact ⟨n, hn, hm⟩
    · omega
  rcases (show lo < P.current_step ∨ lo = P.current_step by omega) with hlt | heq
  · ------------------------------------------------------------ la cadena baja de la fila
    obtain ⟨np, hnp, hnpU⟩ := oldAt (P.current_step - 1) (by omega) (Int.le_refl _)
    have hpv : sel (P.current_step - 1) ∈ rowParents P d (sel P.current_step) := by
      have hl := hch.2 (P.current_step - 1) (by omega) (by omega)
      rw [show P.current_step - 1 + 1 = P.current_step by omega, hmv] at hl
      simpa [rowNode_parents] using hl
    -- la cadena de antes
    have hchP : Extendable.PartialChain P sel lo (P.current_step - 1) := by
      refine ⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_⟩
      · obtain ⟨nj, hnj, _⟩ := oldAt j hj1 hj2
        exact ⟨by rw [hnj]; rfl, (hch.1 j hj1 (by omega)).2⟩
      · obtain ⟨nj, hnj, hnjU⟩ := oldAt (j + 1) (by omega) hj2
        have hl := hch.2 j hj1 (by omega)
        rw [hnjU] at hl
        rw [hnj]
        simpa [upMap_parents] using hl
    have stepOf : ∀ j, lo ≤ j → j ≤ P.current_step → (sel j).id.step = j :=
      fun j hj1 hj2 => (hch.1 j hj1 hj2).2
    have hpwP : ∀ i j, lo ≤ i → lo ≤ j → i ≤ P.current_step - 1 → j ≤ P.current_step - 1 →
        i ≠ j → ∀ nj, P.node? (sel j) = some nj → sel i ∈ nj.owners := by
      intro i' j hi1 hj1 hi2 hj2 hij nj hnj
      have h := hpw i' j hi1 hj1 (by omega) (by omega) hij (upMap P d nj)
        (by rw [addNode_node?_old P d t _ nj hnj])
      exact (old_mem P d hd nj _ (by rw [stepOf i' hi1 (by omega)]; omega)).mp h
    -- la entrada común, sobre un anfitrión del estado de antes
    have finish : ∀ (h : PathNodeId) (nh : PNodeM), P.node? h = some nh →
        (∀ j, lo ≤ j → j ≤ P.current_step - 1 →
          sel j ∈ nh.owners ∧ ∀ nj, P.node? (sel j) = some nj → h ∈ nj.owners) →
        ∃ r, r.id.step = i ∧ r ∈ nh.owners ∧ ∀ j, lo ≤ j → j ≤ P.current_step →
          ∀ nj, (addNode P d t).node? (sel j) = some nj → r ∈ nj.owners := by
      intro h nh hnh hhostP
      obtain ⟨r, hrs, hrh, hrall⟩ := hg h nh hnh sel lo hlo0 (by omega) hchP hpwP hhostP i hi0 hilo
      refine ⟨r, hrs, hrh, fun j hj1 hj2 nj hnj => ?_⟩
      rcases (show j ≤ P.current_step - 1 ∨ j = P.current_step by omega) with hjl | hje
      · obtain ⟨nj0, hnj0, hnjU⟩ := oldAt j hj1 hjl
        rw [hnjU] at hnj; cases hnj
        exact (old_mem P d hd nj0 r (by omega)).mpr (hrall j hj1 hjl nj0 hnj0)
      · subst hje
        rw [hmv] at hnj; cases hnj
        exact toTop _ hpv np hnp r (hrall _ (by omega) (Int.le_refl _) np hnp) (by omega) (by omega)
    rcases lookup P d t hd hbelow a na hna with ⟨has, n_a, hna0, rfl⟩ | ⟨has, harow, rfl⟩
    · -- anfitrión antiguo
      obtain ⟨r, hrs, hra, hrall⟩ := finish a n_a hna0 (fun j hj1 hj2 => by
        obtain ⟨hin, hback⟩ := hhost j hj1 (by omega)
        refine ⟨(old_mem P d hd n_a _ (by rw [stepOf j hj1 (by omega)]; omega)).mp hin,
          fun nj hnj => ?_⟩
        exact (old_mem P d hd nj a has).mp (hback _ (by rw [addNode_node?_old P d t _ nj hnj])))
      exact ⟨r, hrs, (old_mem P d hd n_a r (by omega)).mpr hra, hrall⟩
    · -- anfitrión de la fila: es la cima, y hace de anfitrión su padre en la cadena
      have hva : sel P.current_step = a := by
        have := (hhost P.current_step (by omega) (Int.le_refl _)).1
        exact row_mem_top P d hgs a _ this (stepOf _ (by omega) (Int.le_refl _))
      obtain ⟨r, hrs, hrp, hrall⟩ := finish _ np hnp (fun j hj1 hj2 => by
        rcases int_eq_or_ne j (P.current_step - 1) with he | he
        · subst he
          exact ⟨hself _ np hnp, fun nj hnj => by
            rw [← Option.some.inj (hnp.symm.trans hnj)]; exact hself _ np hnp⟩
        · exact ⟨hpwP j _ hj1 (by omega) hj2 (Int.le_refl _) he np hnp,
            fun nj hnj => hpwP _ j (by omega) hj1 (Int.le_refl _) hj2 (fun h => he h.symm) nj hnj⟩)
      refine ⟨r, hrs, ?_, hrall⟩
      rw [← hva]
      exact toTop _ hpv np hnp r hrp (by omega) (by omega)
  · ------------------------------------------------------------ la cadena es solo la cima
    rw [heq] at hilo hhost ⊢
    have hconc : ∀ r, r ∈ (rowNode P d t (sel P.current_step)).owners →
        ∀ j, P.current_step ≤ j → j ≤ P.current_step → ∀ nj, (addNode P d t).node? (sel j) = some nj → r ∈ nj.owners := by
      intro r hr j hj1 hj2 nj hnj
      have : j = P.current_step := by omega
      rw [this, hmv] at hnj; cases hnj; exact hr
    -- un padre `p` de la cima y una entrada en su tabla, en la del anfitrión y en la global
    have viaParent : ∀ p ∈ rowParents P d (sel P.current_step), ∀ (h : PathNodeId) (nh : PNodeM),
        P.node? h = some nh → p ∈ nh.owners → (∀ np, P.node? p = some np → h ∈ np.owners) →
        ∃ r, r.id.step = i ∧ r ∈ nh.owners ∧ r ∈ (rowNode P d t (sel P.current_step)).owners := by
      intro p hp h nh hnh hpn hhp
      obtain ⟨⟨np, hnp⟩, hps⟩ := rowParent_node P hpos d _ p hp
      rcases (show i = P.current_step - 1 ∨ i < P.current_step - 1 by omega) with hie | hil
      · exact ⟨p, by omega, hpn, toTop p hp np hnp p (hself p np hnp) (by omega) (by omega)⟩
      · have hchp : Extendable.PartialChain P (fun _ => p) (P.current_step - 1)
            (P.current_step - 1) :=
          ⟨fun j hj1 hj2 => ⟨by rw [hnp]; rfl, by rw [hps]; omega⟩, fun j hj1 hj2 => by omega⟩
        obtain ⟨r, hrs, hrh, hrall⟩ := hg h nh hnh (fun _ => p) (P.current_step - 1) (by omega)
          (Int.le_refl _) hchp (fun _ _ h1 h2 h3 h4 hne => absurd (by omega) hne)
          (fun _ _ _ => ⟨hpn, fun np' hnp' => hhp np' hnp'⟩) i hi0 (by omega)
        exact ⟨r, hrs, hrh, toTop p hp np hnp r
          (hrall _ (Int.le_refl _) (Int.le_refl _) np hnp) (by omega) (by omega)⟩
    rcases lookup P d t hd hbelow a na hna with ⟨has, n_a, hna0, rfl⟩ | ⟨has, harow, rfl⟩
    · -- anfitrión antiguo: está en la tabla de algún padre de la cima
      have hain := (hhost P.current_step (Int.le_refl _) (Int.le_refl _)).2 _ hmv
      rw [rowNode_owners, row_mem_below P d hd _ hvrow a has] at hain
      obtain ⟨p, hp, np, hnp, hanp⟩ := FabricAdd.exists_owner_of_mem_unionOwnersOf P _ a hain.1
      obtain ⟨r, hrs, hra, hrv⟩ := viaParent p hp a n_a hna0 (hsym p np a n_a hnp hna0 hanp)
        (fun np' hnp' => by rw [← Option.some.inj (hnp.symm.trans hnp')]; exact hanp)
      exact ⟨r, hrs, (old_mem P d hd n_a r (by omega)).mpr hra, hconc r hrv⟩
    · -- anfitrión de la fila: es la cima; cualquier padre sirve
      have hva : sel P.current_step = a := by
        have := (hhost P.current_step (Int.le_refl _) (Int.le_refl _)).1
        exact row_mem_top P d hgs a _ this hvs
      obtain ⟨p, hp⟩ := row_has_parent P hpos d _ hvrow
      obtain ⟨⟨np, hnp⟩, _⟩ := rowParent_node P hpos d _ p hp
      obtain ⟨r, hrs, _, hrv⟩ := viaParent p hp p np hnp (hself p np hnp)
        (fun np' hnp' => by rw [← Option.some.inj (hnp.symm.trans hnp')]; exact hself p np hnp)
      refine ⟨r, hrs, ?_, hconc r hrv⟩
      rw [← hva]; exact hrv

/-- info: 'AbsSat.GraphPath.Model.TopGoodUp.topGood_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topGood_addNode

-- ============================================================
-- Y `TopGood` es la frase del lector
-- ============================================================

open AbsSat.GraphPath.Model.OwnerChainedBuild in
/-- **`TopGood` da `AnyOptionStep`.** Añadir cualquier opción `u` a lo elegido da otra cadena desde
la cima (`opart_extend`), con el mismo anfitrión; `TopGood` le da entrada común en cada paso de
abajo, y eso es lo que la frase del lector pide. -/
theorem anyOptionStep_of_topGood (g : GPathM) (ctx : Threaded.TCtx g)
    (adj : AdjacentOwners.Adj g) (hsym : Threaded.OwnSymmetric g) (hg : TopGood g) :
    AnyOptionStep g := by
  intro a na hna sel lo hpos hhi hp u hus hun huown i hi0 hi1
  have hop := opart_extend g ctx adj hsym a na hna sel lo hpos hhi hp.op u hun hus
    (fun j hj1 hj2 nj hnj => huown j (by omega) hj2 nj hnj)
  obtain ⟨r, hrs, hra, hrall⟩ := hg a na hna (Extendable.upd sel (lo - 1) u) (lo - 1) (by omega)
    (by omega) hop.chain
    (fun i' j hi1 hj1 hi2 hj2 hij nj hnj => by
      have := hop.owned i' j hi1 hj1 hi2 hj2 hij
      simp only [ownersAt, List.mem_filter, ownersOf, hnj] at this
      exact this.1)
    (fun j hj1 hj2 => ⟨hop.inTable j hj1 hj2, fun nj hnj =>
      hsym a na _ nj hna hnj (hop.inTable j hj1 hj2)⟩)
    i hi0 hi1
  refine ⟨r, hrs, hra, fun j hj1 hj2 nj hnj => ?_, fun nu hnu => ?_⟩
  · have := hrall j (by omega) (by omega) nj
    rw [Extendable.upd_other sel (lo - 1) u (by omega)] at this
    exact this hnj
  · have := hrall (lo - 1) (Int.le_refl _) (by omega) nu
    rw [Extendable.upd_self] at this
    exact this hnu

/-- info: 'AbsSat.GraphPath.Model.TopGoodUp.anyOptionStep_of_topGood' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms anyOptionStep_of_topGood

-- ============================================================
-- El `doJoin`: cada cadena es de un lado
-- ============================================================

/-- **Lo que `TopGood` pide de una cadena**, empaquetado: el anfitrión es un nodo, la cadena arranca
en la cima, está enlazada por padres, poseída por pares y poseída mutuamente con el anfitrión. -/
def ChainFrom (g : GPathM) (a : PathNodeId) (sel : Int → PathNodeId) (lo : Int) : Prop :=
  ∃ na, g.node? a = some na ∧ 0 ≤ lo ∧ lo ≤ g.current_step - 1 ∧
    Extendable.PartialChain g sel lo (g.current_step - 1) ∧
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ g.current_step - 1 → j ≤ g.current_step - 1 → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners) ∧
    (∀ j, lo ≤ j → j ≤ g.current_step - 1 →
      sel j ∈ na.owners ∧ ∀ nj, g.node? (sel j) = some nj → a ∈ nj.owners)

/-- **La hipótesis: la unión no mezcla.** Toda cadena desde la cima del estado unido es cadena, con
sus propias tablas y padres, de uno de los dos lados.

Medido (`row-degree joinmix`), en cada `doJoin` real de la línea: `dos_de_tres.cnf` 744 + 387 de
1.131; aleatorias semilla 1, 312.559 + 147.964 de 460.523 en 711 uniones. **Ninguna mezclada.** -/
def NoMix (J A B : GPathM) : Prop :=
  ∀ a sel lo, ChainFrom J a sel lo → ChainFrom A a sel lo ∨ ChainFrom B a sel lo

/-- **Lo bueno de un lado lo es en un estado que lo contiene.** Si `g` crece a `J` (`Grown`: las
tablas solo ganan), la entrada común que `TopGood g` da para una cadena de `g` sigue siendo común en
`J`. -/
theorem common_of_grown {g J : GPathM} (hgr : Grown g J) (hg : TopGood g)
    (a : PathNodeId) (sel : Int → PathNodeId) (lo : Int) (hc : ChainFrom g a sel lo)
    (na : PNodeM) (hna : J.node? a = some na) (i : Int) (hi0 : 0 ≤ i) (hi1 : i < lo) :
    ∃ r, r.id.step = i ∧ r ∈ na.owners ∧
      ∀ j, lo ≤ j → j ≤ J.current_step - 1 → ∀ nj, J.node? (sel j) = some nj → r ∈ nj.owners := by
  obtain ⟨ga, hga, hlo0, hlo1, hch, hpw, hhost⟩ := hc
  obtain ⟨r, hrs, hra, hrall⟩ := hg a ga hga sel lo hlo0 hlo1 hch hpw hhost i hi0 hi1
  obtain ⟨na', hna', hown, _, _⟩ := hgr.node?_grown a ga hga
  rw [hna] at hna'; cases hna'
  refine ⟨r, hrs, hown r hra, fun j hj1 hj2 nj hnj => ?_⟩
  rw [hgr.step_eq] at hj2
  obtain ⟨hs, _⟩ := hch.1 j hj1 hj2
  obtain ⟨gj, hgj⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨nj', hnj', hownj, _, _⟩ := hgr.node?_grown _ gj hgj
  rw [hnj] at hnj'; cases hnj'
  exact hownj r (hrall j hj1 hj2 gj hgj)

/-- **Dos lados buenos que no se mezclan dan un estado bueno.** -/
theorem topGood_of_sides {J A B : GPathM} (hA : Grown A J) (hB : Grown B J)
    (tA : TopGood A) (tB : TopGood B) (hmix : NoMix J A B) : TopGood J := by
  intro a na hna sel lo hlo0 hlo1 hch hpw hhost i hi0 hi1
  rcases hmix a sel lo ⟨na, hna, hlo0, hlo1, hch, hpw, hhost⟩ with hc | hc
  · exact common_of_grown hA tA a sel lo hc na hna i hi0 hi1
  · exact common_of_grown hB tB a sel lo hc na hna i hi0 hi1

/-- **El `doJoin` conserva `TopGood`**, con la unión sin mezcla como única hipótesis. Si los dos
lados no casan, `doJoin` devuelve el de la izquierda tal cual. -/
theorem topGood_doJoin (A B : GPathM) (tA : TopGood A) (tB : TopGood B)
    (hmix : okJoin A B = true → NoMix (join A B) A B) : TopGood (doJoin A B) := by
  unfold doJoin
  split
  · next hok =>
    exact topGood_of_sides (grown_join_left A B) (grown_join_right A B hok) tA tB (hmix hok)
  · exact tA

/-- info: 'AbsSat.GraphPath.Model.TopGoodUp.common_of_grown' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms common_of_grown

/-- info: 'AbsSat.GraphPath.Model.TopGoodUp.topGood_of_sides' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topGood_of_sides

/-- info: 'AbsSat.GraphPath.Model.TopGoodUp.topGood_doJoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topGood_doJoin

-- ============================================================
-- SIN anfitrión
-- ============================================================

/-! El anfitrión es lo que rompía los estados intermedios: con él, `cleanInvalid` nodo a nodo deja
134 de 519 estados sin entrada común en `dos_de_tres.cnf`; sin él, **ninguno**, y ninguno en las
demás pasadas (`row-degree nohostnodes`). En los estados de la máquina y del lector tampoco falla
(`row-degree nohostops`: semilla 1, 0 de 194.166 cadenas). Y la escalera no lo necesita:
`ownerChained_of_tableHasOwnedChain` no usa que la cadena esté en la tabla de `a`. -/

/-- **Toda cadena desde la cima es buena**, sin anfitrión: enlazada por padres y poseída por pares,
tiene en cada paso de abajo una entrada común a las tablas de todos sus miembros. -/
def TopGoodNH (g : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo : Int), 0 ≤ lo → lo ≤ g.current_step - 1 →
    Extendable.PartialChain g sel lo (g.current_step - 1) →
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ g.current_step - 1 → j ≤ g.current_step - 1 → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners) →
    ∀ i, 0 ≤ i → i < lo → ∃ r, r.id.step = i ∧
      ∀ j, lo ≤ j → j ≤ g.current_step - 1 → ∀ nj, g.node? (sel j) = some nj → r ∈ nj.owners

/-- **El `up` conserva `TopGoodNH`**, con menos hipótesis que con anfitrión: ni simetría ni la
forma de la tabla global. Por debajo de la cima nueva la cadena es del estado de antes; su entrada
común está en la tabla del padre de la cima, y `rowOwners` la hereda. Si la cadena es solo la cima,
basta un padre suyo. -/
theorem topGoodNH_addNode (P : GPathM) (d : NodeId) (t : String) (hd : d.step = P.current_step)
    (hpos : 0 < P.current_step)
    (hbelow : ∀ n ∈ P.nodes, n.id.id.step < P.current_step)
    (hgow : ∀ pid n, P.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < P.current_step → q ∈ P.gowners)
    (hself : ∀ pid n, P.node? pid = some n → pid ∈ n.owners) (hg : TopGoodNH P) :
    TopGoodNH (addNode P d t) := by
  intro sel lo hlo0 hlo1 hch hpw i hi0 hilo
  have hcsU : (addNode P d t).current_step - 1 = P.current_step := by rw [addNode_current]; omega
  rw [hcsU] at hlo1 hch hpw ⊢
  obtain ⟨hvsome, hvs⟩ := hch.1 P.current_step hlo1 (Int.le_refl _)
  obtain ⟨mv, hmv⟩ := Option.isSome_iff_exists.mp hvsome
  obtain ⟨hvrow, hmveq⟩ : sel P.current_step ∈ newRowIds P d ∧
      mv = rowNode P d t (sel P.current_step) := by
    rcases lookup P d t hd hbelow _ mv hmv with ⟨hlt, _⟩ | ⟨_, hr, he⟩
    · omega
    · exact ⟨hr, he⟩
  subst hmveq
  have toTop : ∀ p ∈ rowParents P d (sel P.current_step), ∀ np, P.node? p = some np →
      ∀ r ∈ np.owners, 0 ≤ r.id.step → r.id.step < P.current_step →
      r ∈ (rowNode P d t (sel P.current_step)).owners := fun p hp np hnp r hr h0 h1 =>
    row_of_parent P d _ p hp np hnp r hr (hgow p np hnp r hr h0 h1)
  have oldAt : ∀ j, lo ≤ j → j ≤ P.current_step - 1 →
      ∃ nj, P.node? (sel j) = some nj ∧ (addNode P d t).node? (sel j) = some (upMap P d nj) := by
    intro j hj1 hj2
    obtain ⟨hs, hjs⟩ := hch.1 j hj1 (by omega)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    rcases lookup P d t hd hbelow _ m hm with ⟨_, n, hn, rfl⟩ | ⟨hst, _⟩
    · exact ⟨n, hn, hm⟩
    · omega
  rcases (show lo < P.current_step ∨ lo = P.current_step by omega) with hlt | heq
  · obtain ⟨np, hnp, _⟩ := oldAt (P.current_step - 1) (by omega) (Int.le_refl _)
    have hpv : sel (P.current_step - 1) ∈ rowParents P d (sel P.current_step) := by
      have hl := hch.2 (P.current_step - 1) (by omega) (by omega)
      rw [show P.current_step - 1 + 1 = P.current_step by omega, hmv] at hl
      simpa [rowNode_parents] using hl
    have hchP : Extendable.PartialChain P sel lo (P.current_step - 1) := by
      refine ⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_⟩
      · obtain ⟨nj, hnj, _⟩ := oldAt j hj1 hj2
        exact ⟨by rw [hnj]; rfl, (hch.1 j hj1 (by omega)).2⟩
      · obtain ⟨nj, hnj, hnjU⟩ := oldAt (j + 1) (by omega) hj2
        have hl := hch.2 j hj1 (by omega)
        rw [hnjU] at hl
        rw [hnj]
        simpa [upMap_parents] using hl
    have hpwP : ∀ i j, lo ≤ i → lo ≤ j → i ≤ P.current_step - 1 → j ≤ P.current_step - 1 →
        i ≠ j → ∀ nj, P.node? (sel j) = some nj → sel i ∈ nj.owners := by
      intro i' j hi1 hj1 hi2 hj2 hij nj hnj
      have h := hpw i' j hi1 hj1 (by omega) (by omega) hij (upMap P d nj)
        (by rw [addNode_node?_old P d t _ nj hnj])
      exact (old_mem P d hd nj _ (by rw [(hch.1 i' hi1 (by omega)).2]; omega)).mp h
    obtain ⟨r, hrs, hrall⟩ := hg sel lo hlo0 (by omega) hchP hpwP i hi0 hilo
    refine ⟨r, hrs, fun j hj1 hj2 nj hnj => ?_⟩
    rcases (show j ≤ P.current_step - 1 ∨ j = P.current_step by omega) with hjl | hje
    · obtain ⟨nj0, hnj0, hnjU⟩ := oldAt j hj1 hjl
      rw [hnjU] at hnj; cases hnj
      exact (old_mem P d hd nj0 r (by omega)).mpr (hrall j hj1 hjl nj0 hnj0)
    · subst hje
      rw [hmv] at hnj; cases hnj
      exact toTop _ hpv np hnp r (hrall _ (by omega) (Int.le_refl _) np hnp) (by omega) (by omega)
  · rw [heq] at hilo ⊢
    obtain ⟨p, hp⟩ := row_has_parent P hpos d _ hvrow
    obtain ⟨⟨np, hnp⟩, hps⟩ := rowParent_node P hpos d _ p hp
    have hconc : ∀ r, r ∈ (rowNode P d t (sel P.current_step)).owners →
        ∀ j, P.current_step ≤ j → j ≤ P.current_step → ∀ nj,
          (addNode P d t).node? (sel j) = some nj → r ∈ nj.owners := by
      intro r hr j hj1 hj2 nj hnj
      have : j = P.current_step := by omega
      rw [this, hmv] at hnj; cases hnj; exact hr
    rcases (show i = P.current_step - 1 ∨ i < P.current_step - 1 by omega) with hie | hil
    · exact ⟨p, by omega, hconc p (toTop p hp np hnp p (hself p np hnp) (by omega) (by omega))⟩
    · have hchp : Extendable.PartialChain P (fun _ => p) (P.current_step - 1)
          (P.current_step - 1) :=
        ⟨fun j hj1 hj2 => ⟨by rw [hnp]; rfl, by rw [hps]; omega⟩, fun j hj1 hj2 => by omega⟩
      obtain ⟨r, hrs, hrall⟩ := hg (fun _ => p) (P.current_step - 1) (by omega) (Int.le_refl _)
        hchp (fun _ _ h1 h2 h3 h4 hne => absurd (by omega) hne) i hi0 (by omega)
      exact ⟨r, hrs, hconc r (toTop p hp np hnp r
        (hrall _ (Int.le_refl _) (Int.le_refl _) np hnp) (by omega) (by omega))⟩

/-- La cadena sin anfitrión, empaquetada. -/
def ChainFromNH (g : GPathM) (sel : Int → PathNodeId) (lo : Int) : Prop :=
  0 ≤ lo ∧ lo ≤ g.current_step - 1 ∧ Extendable.PartialChain g sel lo (g.current_step - 1) ∧
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ g.current_step - 1 → j ≤ g.current_step - 1 → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners)

/-- **La unión no mezcla**, sin anfitrión. -/
def NoMixNH (J A B : GPathM) : Prop :=
  ∀ sel lo, ChainFromNH J sel lo → ChainFromNH A sel lo ∨ ChainFromNH B sel lo

theorem commonNH_of_grown {g J : GPathM} (hgr : Grown g J) (hg : TopGoodNH g)
    (sel : Int → PathNodeId) (lo : Int) (hc : ChainFromNH g sel lo) (i : Int) (hi0 : 0 ≤ i)
    (hi1 : i < lo) :
    ∃ r, r.id.step = i ∧
      ∀ j, lo ≤ j → j ≤ J.current_step - 1 → ∀ nj, J.node? (sel j) = some nj → r ∈ nj.owners := by
  obtain ⟨hlo0, hlo1, hch, hpw⟩ := hc
  obtain ⟨r, hrs, hrall⟩ := hg sel lo hlo0 hlo1 hch hpw i hi0 hi1
  refine ⟨r, hrs, fun j hj1 hj2 nj hnj => ?_⟩
  rw [hgr.step_eq] at hj2
  obtain ⟨hs, _⟩ := hch.1 j hj1 hj2
  obtain ⟨gj, hgj⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨nj', hnj', hownj, _, _⟩ := hgr.node?_grown _ gj hgj
  rw [hnj] at hnj'; cases hnj'
  exact hownj r (hrall j hj1 hj2 gj hgj)

/-- **El `doJoin` conserva `TopGoodNH`** si la unión no mezcla. -/
theorem topGoodNH_doJoin (A B : GPathM) (tA : TopGoodNH A) (tB : TopGoodNH B)
    (hmix : okJoin A B = true → NoMixNH (join A B) A B) : TopGoodNH (doJoin A B) := by
  unfold doJoin
  split
  · next hok =>
    intro sel lo hlo0 hlo1 hch hpw i hi0 hi1
    rcases hmix hok sel lo ⟨hlo0, hlo1, hch, hpw⟩ with hc | hc
    · exact commonNH_of_grown (grown_join_left A B) tA sel lo hc i hi0 hi1
    · exact commonNH_of_grown (grown_join_right A B hok) tB sel lo hc i hi0 hi1
  · exact tA

/-- info: 'AbsSat.GraphPath.Model.TopGoodUp.topGoodNH_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topGoodNH_addNode

/-- info: 'AbsSat.GraphPath.Model.TopGoodUp.topGoodNH_doJoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms topGoodNH_doJoin

-- ============================================================
-- `SegGood`: tramos cualesquiera, en los dos sentidos
-- ============================================================

/-! Para que la cadena pase por un nodo dado `a` hay que construirla **desde `a`**: bajando hasta el
paso 0 y subiendo hasta la cima. Eso pide que los tramos que no arrancan en la cima también sean
buenos, por debajo y por encima. Medido sin anfitrión (`row-degree segments`, `segops`): 0 fallos en
todas las clases de estado de la máquina y del lector. Como las otras dos versiones, solo falla en
estados intermedios de `cleanInvalid` (nodo a nodo), y ahí los tramos rotos mueren antes de acabar
la pasada (`row-degree cleandiag`). -/

/-- **Todo tramo es bueno**: un tramo enlazado por padres y poseído por pares tiene, en cada paso
fuera de él —por debajo y por encima—, una entrada común a las tablas de todos sus miembros. -/
def SegGood (g : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi ≤ g.current_step - 1 →
    Extendable.PartialChain g sel lo hi →
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners) →
    ∀ i, 0 ≤ i → i ≤ g.current_step - 1 → (i < lo ∨ hi < i) → ∃ r, r.id.step = i ∧
      ∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → r ∈ nj.owners

/-- Un nodo antiguo gana como owner al hijo de fila de un nodo del último paso cuya tabla lo
contiene. -/
theorem gained_of_parent (P : GPathM) (d : NodeId) (hpos : 0 < P.current_step)
    (p : PathNodeId) (np : PNodeM) (hnp : P.node? p = some np)
    (hps : p.id.step = P.current_step - 1)
    (x : PathNodeId) (nx : PNodeM) (hxp : x ∈ np.owners) (hxg : x ∈ P.gowners)
    (hnx : nx.id = x) :
    shiftPid p d ∈ (upMap P d nx).owners := by
  have hpn : p ∈ newParents P := by
    unfold newParents; rw [if_pos hpos]
    exact mem_line_of_node? P p np hnp _ hps
  have hv := mem_newRowIds_of_mem_newParents P d p hpos hpn
  have hrow : x ∈ rowOwners P d (shiftPid p d) :=
    row_of_parent P d _ p (mem_rowParents_of_mem_newParents P d p hpn) np hnp x hxp hxg
  rw [upMap_owners]
  refine List.mem_append_right _ (List.mem_filter.mpr ⟨hv, ?_⟩)
  rw [hnx]; exact List.elem_iff.mpr hrow

/-- **El `up` conserva `SegGood`.**

* Un tramo que termina en la fila nueva es como en `topGoodNH_addNode`: por debajo es un tramo de
  antes, y la cima hereda su entrada común por su padre.
* Un tramo antiguo es tramo de antes, con las mismas tablas por debajo de la fila; lo único nuevo es
  el paso de la fila, y ahí sirve el hijo de fila de un nodo `p` del último paso cuya tabla contiene
  al tramo: el propio extremo alto si el tramo llega a la cima antigua, o, si no, la entrada común
  que `SegGood` da por encima, vuelta del revés por la simetría. -/
theorem segGood_addNode (P : GPathM) (d : NodeId) (t : String) (hd : d.step = P.current_step)
    (hpos : 0 < P.current_step)
    (hbelow : ∀ n ∈ P.nodes, n.id.id.step < P.current_step)
    (hgow : ∀ pid n, P.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < P.current_step → q ∈ P.gowners)
    (hself : ∀ pid n, P.node? pid = some n → pid ∈ n.owners)
    (hnode : ∀ pid n, P.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < P.current_step → (P.node? q).isSome)
    (hsym : Threaded.OwnSymmetric P) (hg : SegGood P) :
    SegGood (addNode P d t) := by
  intro sel lo hi hlo0 hlohi hhi hch hpw i hi0 hic hout
  have hcsU : (addNode P d t).current_step - 1 = P.current_step := by rw [addNode_current]; omega
  rw [hcsU] at hhi hic
  -- los nodos antiguos del tramo
  have oldAt : ∀ j, lo ≤ j → j ≤ hi → j ≤ P.current_step - 1 →
      ∃ nj, P.node? (sel j) = some nj ∧ (addNode P d t).node? (sel j) = some (upMap P d nj) := by
    intro j hj1 hj2 hj3
    obtain ⟨hs, hjs⟩ := hch.1 j hj1 hj2
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    rcases lookup P d t hd hbelow _ m hm with ⟨_, n, hn, rfl⟩ | ⟨hst, _⟩
    · exact ⟨n, hn, hm⟩
    · omega
  -- el tramo antiguo, restringido hasta `top'`
  have restrict : ∀ top', lo ≤ top' → top' ≤ hi → top' ≤ P.current_step - 1 →
      Extendable.PartialChain P sel lo top' ∧
      ∀ i j, lo ≤ i → lo ≤ j → i ≤ top' → j ≤ top' → i ≠ j →
        ∀ nj, P.node? (sel j) = some nj → sel i ∈ nj.owners := by
    intro top' h1 h2 h3
    refine ⟨⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_⟩, fun i' j hi1 hj1 hi2 hj2 hij nj hnj => ?_⟩
    · obtain ⟨nj, hnj, _⟩ := oldAt j hj1 (by omega) (by omega)
      exact ⟨by rw [hnj]; rfl, (hch.1 j hj1 (by omega)).2⟩
    · obtain ⟨nj, hnj, hnjU⟩ := oldAt (j + 1) (by omega) (by omega) (by omega)
      have hl := hch.2 j hj1 (by omega)
      rw [hnjU] at hl
      rw [hnj]
      simpa [upMap_parents] using hl
    · have h := hpw i' j hi1 hj1 (by omega) (by omega) hij (upMap P d nj)
        (by rw [addNode_node?_old P d t _ nj hnj])
      exact (old_mem P d hd nj _ (by rw [(hch.1 i' hi1 (by omega)).2]; omega)).mp h
  rcases (show hi < P.current_step ∨ hi = P.current_step by omega) with hhl | hhe
  · ---------------------------------------------------------------- tramo antiguo
    obtain ⟨hchP, hpwP⟩ := restrict hi (by omega) (Int.le_refl _) (by omega)
    rcases (show i < P.current_step ∨ i = P.current_step by omega) with hil | hie
    · obtain ⟨r, hrs, hrall⟩ := hg sel lo hi hlo0 hlohi (by omega) hchP hpwP i hi0 (by omega) hout
      refine ⟨r, hrs, fun j hj1 hj2 nj hnj => ?_⟩
      obtain ⟨nj0, hnj0, hnjU⟩ := oldAt j hj1 hj2 (by omega)
      rw [hnjU] at hnj; cases hnj
      exact (old_mem P d hd nj0 r (by omega)).mpr (hrall j hj1 hj2 nj0 hnj0)
    · -- el paso de la fila: un `p` del último paso cuya tabla contiene al tramo
      obtain ⟨p, np, hnp, hps, hin⟩ : ∃ p np, P.node? p = some np ∧
          p.id.step = P.current_step - 1 ∧
          ∀ j, lo ≤ j → j ≤ hi → sel j ∈ np.owners := by
        rcases (show hi = P.current_step - 1 ∨ hi < P.current_step - 1 by omega) with he | hlt
        · obtain ⟨np, hnp, _⟩ := oldAt hi (by omega) (Int.le_refl _) (by omega)
          refine ⟨sel hi, np, hnp, by rw [(hch.1 hi (by omega) (Int.le_refl _)).2, he], ?_⟩
          intro j hj1 hj2
          rcases int_eq_or_ne j hi with hje | hjne
          · rw [hje]; exact hself _ np hnp
          · exact hpwP j hi hj1 (by omega) hj2 (Int.le_refl _) hjne np hnp
        · obtain ⟨r, hrs, hrall⟩ := hg sel lo hi hlo0 hlohi (by omega) hchP hpwP
            (P.current_step - 1) (by omega) (Int.le_refl _) (Or.inr hlt)
          obtain ⟨nl, hnl, _⟩ := oldAt lo (Int.le_refl _) hlohi (by omega)
          obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp
            (hnode _ nl hnl r (hrall lo (Int.le_refl _) hlohi nl hnl) (by omega) (by omega))
          refine ⟨r, nr, hnr, hrs, fun j hj1 hj2 => ?_⟩
          obtain ⟨nj, hnj, _⟩ := oldAt j hj1 hj2 (by omega)
          exact hsym _ nj r nr hnj hnr (hrall j hj1 hj2 nj hnj)
      refine ⟨shiftPid p d, by rw [hie]; show d.step = _; exact hd, fun j hj1 hj2 nj hnj => ?_⟩
      obtain ⟨nj0, hnj0, hnjU⟩ := oldAt j hj1 hj2 (by omega)
      rw [hnjU] at hnj; cases hnj
      have hjs := (hch.1 j hj1 hj2).2
      exact gained_of_parent P d hpos p np hnp hps _ nj0 (hin j hj1 hj2)
        (hgow p np hnp _ (hin j hj1 hj2) (by omega) (by omega)) (node?_id_eq P _ nj0 hnj0)
  · ---------------------------------------------------------------- tramo que acaba en la fila
    subst hhe
    have hil : i < lo := by omega
    obtain ⟨hvsome, _⟩ := hch.1 P.current_step hlohi (Int.le_refl _)
    obtain ⟨mv, hmv⟩ := Option.isSome_iff_exists.mp hvsome
    obtain ⟨hvrow, hmveq⟩ : sel P.current_step ∈ newRowIds P d ∧
        mv = rowNode P d t (sel P.current_step) := by
      rcases lookup P d t hd hbelow _ mv hmv with ⟨hlt, _⟩ | ⟨_, hr, he⟩
      · have := (hch.1 P.current_step hlohi (Int.le_refl _)).2; omega
      · exact ⟨hr, he⟩
    subst hmveq
    have toTop : ∀ p ∈ rowParents P d (sel P.current_step), ∀ np, P.node? p = some np →
        ∀ r ∈ np.owners, 0 ≤ r.id.step → r.id.step < P.current_step →
        r ∈ (rowNode P d t (sel P.current_step)).owners := fun p hp np hnp r hr h0 h1 =>
      row_of_parent P d _ p hp np hnp r hr (hgow p np hnp r hr h0 h1)
    rcases (show lo < P.current_step ∨ lo = P.current_step by omega) with hlt | heq
    · obtain ⟨np, hnp, _⟩ := oldAt (P.current_step - 1) (by omega) (by omega) (Int.le_refl _)
      have hpv : sel (P.current_step - 1) ∈ rowParents P d (sel P.current_step) := by
        have hl := hch.2 (P.current_step - 1) (by omega) (by omega)
        rw [show P.current_step - 1 + 1 = P.current_step by omega, hmv] at hl
        simpa [rowNode_parents] using hl
      obtain ⟨hchP, hpwP⟩ := restrict (P.current_step - 1) (by omega) (by omega) (Int.le_refl _)
      obtain ⟨r, hrs, hrall⟩ := hg sel lo (P.current_step - 1) hlo0 (by omega) (Int.le_refl _)
        hchP hpwP i hi0 (by omega) (Or.inl hil)
      refine ⟨r, hrs, fun j hj1 hj2 nj hnj => ?_⟩
      rcases (show j ≤ P.current_step - 1 ∨ j = P.current_step by omega) with hjl | hje
      · obtain ⟨nj0, hnj0, hnjU⟩ := oldAt j hj1 hj2 hjl
        rw [hnjU] at hnj; cases hnj
        exact (old_mem P d hd nj0 r (by omega)).mpr (hrall j hj1 hjl nj0 hnj0)
      · subst hje
        rw [hmv] at hnj; cases hnj
        exact toTop _ hpv np hnp r (hrall _ (by omega) (Int.le_refl _) np hnp) (by omega)
          (by omega)
    · subst heq
      obtain ⟨p, hp⟩ := row_has_parent P hpos d _ hvrow
      obtain ⟨⟨np, hnp⟩, hps⟩ := rowParent_node P hpos d _ p hp
      have hconc : ∀ r, r ∈ (rowNode P d t (sel P.current_step)).owners →
          ∀ j, P.current_step ≤ j → j ≤ P.current_step → ∀ nj,
            (addNode P d t).node? (sel j) = some nj → r ∈ nj.owners := by
        intro r hr j hj1 hj2 nj hnj
        have : j = P.current_step := by omega
        rw [this, hmv] at hnj; cases hnj; exact hr
      rcases (show i = P.current_step - 1 ∨ i < P.current_step - 1 by omega) with hie | hil'
      · exact ⟨p, by omega, hconc p (toTop p hp np hnp p (hself p np hnp) (by omega) (by omega))⟩
      · have hchp : Extendable.PartialChain P (fun _ => p) (P.current_step - 1)
            (P.current_step - 1) :=
          ⟨fun j hj1 hj2 => ⟨by rw [hnp]; rfl, by rw [hps]; omega⟩, fun j hj1 hj2 => by omega⟩
        obtain ⟨r, hrs, hrall⟩ := hg (fun _ => p) (P.current_step - 1) (P.current_step - 1)
          (by omega) (Int.le_refl _) (Int.le_refl _) hchp
          (fun _ _ h1 h2 h3 h4 hne => absurd (by omega) hne) i hi0 (by omega) (Or.inl hil')
        exact ⟨r, hrs, hconc r (toTop p hp np hnp r
          (hrall _ (Int.le_refl _) (Int.le_refl _) np hnp) (by omega) (by omega))⟩

/-- info: 'AbsSat.GraphPath.Model.TopGoodUp.segGood_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segGood_addNode

/-- Un tramo, empaquetado. -/
def SegFrom (g : GPathM) (sel : Int → PathNodeId) (lo hi : Int) : Prop :=
  0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ g.current_step - 1 ∧ Extendable.PartialChain g sel lo hi ∧
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners)

/-- **La unión no mezcla tramos**: todo tramo del estado unido es tramo de uno de los lados. -/
def NoMixSeg (J A B : GPathM) : Prop :=
  ∀ sel lo hi, SegFrom J sel lo hi → SegFrom A sel lo hi ∨ SegFrom B sel lo hi

theorem segCommon_of_grown {g J : GPathM} (hgr : Grown g J) (hg : SegGood g)
    (sel : Int → PathNodeId) (lo hi : Int) (hc : SegFrom g sel lo hi) (i : Int) (hi0 : 0 ≤ i)
    (hic : i ≤ J.current_step - 1) (hout : i < lo ∨ hi < i) :
    ∃ r, r.id.step = i ∧
      ∀ j, lo ≤ j → j ≤ hi → ∀ nj, J.node? (sel j) = some nj → r ∈ nj.owners := by
  obtain ⟨hlo0, hlohi, hhi, hch, hpw⟩ := hc
  rw [hgr.step_eq] at hic
  obtain ⟨r, hrs, hrall⟩ := hg sel lo hi hlo0 hlohi hhi hch hpw i hi0 hic hout
  refine ⟨r, hrs, fun j hj1 hj2 nj hnj => ?_⟩
  obtain ⟨hs, _⟩ := hch.1 j hj1 hj2
  obtain ⟨gj, hgj⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨nj', hnj', hownj, _, _⟩ := hgr.node?_grown _ gj hgj
  rw [hnj] at hnj'; cases hnj'
  exact hownj r (hrall j hj1 hj2 gj hgj)

/-- **El `doJoin` conserva `SegGood`** si la unión no mezcla tramos. -/
theorem segGood_doJoin (A B : GPathM) (tA : SegGood A) (tB : SegGood B)
    (hmix : okJoin A B = true → NoMixSeg (join A B) A B) : SegGood (doJoin A B) := by
  unfold doJoin
  split
  · next hok =>
    intro sel lo hi hlo0 hlohi hhi hch hpw i hi0 hic hout
    rcases hmix hok sel lo hi ⟨hlo0, hlohi, hhi, hch, hpw⟩ with hc | hc
    · exact segCommon_of_grown (grown_join_left A B) tA sel lo hi hc i hi0 hic hout
    · exact segCommon_of_grown (grown_join_right A B hok) tB sel lo hi hc i hi0 hic hout
  · exact tA

/-- info: 'AbsSat.GraphPath.Model.TopGoodUp.segGood_doJoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segGood_doJoin

-- ============================================================
-- El descenso DESDE `a`: bajando y subiendo
-- ============================================================

open AbsSat.GraphPath.Model.Extendable (upd upd_self upd_other isChain_of_partial)

/-- **Un tramo**: enlazado por padres de `lo` a `hi` y poseído por pares. -/
def Seg (g : GPathM) (sel : Int → PathNodeId) (lo hi : Int) : Prop :=
  Extendable.PartialChain g sel lo hi ∧
    ∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, g.node? (sel j) = some nj → sel i ∈ nj.owners

/-- **Bajar un paso.** La entrada común que `SegGood` da en `lo - 1` está en la tabla de `sel lo`,
así que es su padre; y la simetría mete al tramo en su tabla. -/
theorem seg_down (g : GPathM) (adj : AdjacentOwners.Adj g) (hsym : Threaded.OwnSymmetric g)
    (hnode : ∀ pid n, g.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < g.current_step → (g.node? q).isSome)
    (hseg : SegGood g) (sel : Int → PathNodeId) (lo hi : Int) (hpos : 0 < lo) (hlohi : lo ≤ hi)
    (hhi : hi ≤ g.current_step - 1) (hs : Seg g sel lo hi) :
    ∃ r, Seg g (upd sel (lo - 1) r) (lo - 1) hi := by
  obtain ⟨hch, hpw⟩ := hs
  obtain ⟨r, hrs, hrall⟩ := hseg sel lo hi (by omega) hlohi hhi hch hpw (lo - 1) (by omega)
    (by omega) (Or.inl (by omega))
  obtain ⟨hlsome, hls⟩ := hch.1 lo (Int.le_refl _) hlohi
  obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp hlsome
  have hrl := hrall lo (Int.le_refl _) hlohi nl hnl
  obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp (hnode _ nl hnl r hrl (by omega) (by omega))
  refine ⟨r, ⟨fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_⟩, fun i j hi1 hj1 hi2 hj2 hij nj hnj => ?_⟩
  · rcases int_eq_or_ne i (lo - 1) with he | he
    · subst he; rw [upd_self]; exact ⟨by rw [hnr]; rfl, hrs⟩
    · rw [upd_other sel (lo - 1) r he]; exact hch.1 i (by omega) hi2
  · rcases int_eq_or_ne i (lo - 1) with he | he
    · subst he
      rw [upd_self, upd_other sel (lo - 1) r (by omega), show lo - 1 + 1 = lo from by omega, hnl]
      simp only [Option.map_some, Option.getD_some]
      exact (AdjacentOwners.owners_below_iff_parents g adj (sel lo) nl hnl (by omega) r
        (by rw [hrs, hls])).mp hrl
    · rw [upd_other sel (lo - 1) r he, upd_other sel (lo - 1) r (by omega)]
      exact hch.2 i (by omega) hi2
  · rcases int_eq_or_ne i (lo - 1) with hei | hei
    · subst hei
      rw [upd_self]
      rw [upd_other sel (lo - 1) r (fun h => hij h.symm)] at hnj
      exact hrall j (by omega) hj2 nj hnj
    · rw [upd_other sel (lo - 1) r hei]
      rcases int_eq_or_ne j (lo - 1) with hej | hej
      · subst hej
        rw [upd_self] at hnj
        obtain ⟨hsi, _⟩ := hch.1 i (by omega) hi2
        obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp hsi
        exact hsym _ ni r nj hni hnj (hrall i (by omega) hi2 ni hni)
      · rw [upd_other sel (lo - 1) r hej] at hnj
        exact hpw i j (by omega) (by omega) hi2 hj2 hij nj hnj

/-- **Subir un paso.** La entrada común de `hi + 1` tiene, por simetría, a `sel hi` en su tabla, y
en el paso de justo abajo eso es ser su padre. -/
theorem seg_up (g : GPathM) (adj : AdjacentOwners.Adj g) (hsym : Threaded.OwnSymmetric g)
    (hnode : ∀ pid n, g.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < g.current_step → (g.node? q).isSome)
    (hseg : SegGood g) (sel : Int → PathNodeId) (lo hi : Int) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (hhi : hi < g.current_step - 1) (hs : Seg g sel lo hi) :
    ∃ r, Seg g (upd sel (hi + 1) r) lo (hi + 1) := by
  obtain ⟨hch, hpw⟩ := hs
  obtain ⟨r, hrs, hrall⟩ := hseg sel lo hi hlo hlohi (by omega) hch hpw (hi + 1) (by omega)
    (by omega) (Or.inr (by omega))
  obtain ⟨hhsome, hhs⟩ := hch.1 hi hlohi (Int.le_refl _)
  obtain ⟨nh, hnh⟩ := Option.isSome_iff_exists.mp hhsome
  have hrh := hrall hi hlohi (Int.le_refl _) nh hnh
  obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp (hnode _ nh hnh r hrh (by omega) (by omega))
  refine ⟨r, ⟨fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_⟩, fun i j hi1 hj1 hi2 hj2 hij nj hnj => ?_⟩
  · rcases int_eq_or_ne i (hi + 1) with he | he
    · subst he; rw [upd_self]; exact ⟨by rw [hnr]; rfl, hrs⟩
    · rw [upd_other sel (hi + 1) r he]; exact hch.1 i hi1 (by omega)
  · rcases int_eq_or_ne i hi with he | he
    · subst he
      rw [upd_self, upd_other sel (i + 1) r (by omega), hnr]
      simp only [Option.map_some, Option.getD_some]
      exact (AdjacentOwners.owners_below_iff_parents g adj r nr hnr (by omega) (sel i)
        (by rw [hrs, hhs]; omega)).mp (hsym _ nh r nr hnh hnr hrh)
    · rw [upd_other sel (hi + 1) r (by omega), upd_other sel (hi + 1) r (by omega)]
      exact hch.2 i hi1 (by omega)
  · rcases int_eq_or_ne i (hi + 1) with hei | hei
    · subst hei
      rw [upd_self]
      rw [upd_other sel (hi + 1) r (fun h => hij h.symm)] at hnj
      exact hrall j hj1 (by omega) nj hnj
    · rw [upd_other sel (hi + 1) r hei]
      rcases int_eq_or_ne j (hi + 1) with hej | hej
      · subst hej
        rw [upd_self] at hnj
        obtain ⟨hsi, _⟩ := hch.1 i hi1 (by omega)
        obtain ⟨ni, hni⟩ := Option.isSome_iff_exists.mp hsi
        exact hsym _ ni r nj hni hnj (hrall i hi1 (by omega) ni hni)
      · rw [upd_other sel (hi + 1) r hej] at hnj
        exact hpw i j hi1 hj1 (by omega) (by omega) hij nj hnj

/-- **Bajar hasta el paso 0**, conservando lo que ya se había elegido en el paso `s`. -/
theorem seg_down_all (g : GPathM) (adj : AdjacentOwners.Adj g) (hsym : Threaded.OwnSymmetric g)
    (hnode : ∀ pid n, g.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < g.current_step → (g.node? q).isSome)
    (hseg : SegGood g) (s : Int) (x : PathNodeId) :
    ∀ (fuel : Nat) (sel : Int → PathNodeId) (lo hi : Int), lo.toNat ≤ fuel → 0 ≤ lo →
      lo ≤ s → s ≤ hi → hi ≤ g.current_step - 1 → Seg g sel lo hi → sel s = x →
      ∃ sel', Seg g sel' 0 hi ∧ sel' s = x := by
  intro fuel
  induction fuel with
  | zero =>
    intro sel lo hi hm hlo hls hsh hhi hs hx
    have : lo = 0 := by omega
    subst this; exact ⟨sel, hs, hx⟩
  | succ fuel ih =>
    intro sel lo hi hm hlo hls hsh hhi hs hx
    if hpos : 0 < lo then
      obtain ⟨r, hs'⟩ := seg_down g adj hsym hnode hseg sel lo hi hpos (by omega) hhi hs
      exact ih _ (lo - 1) hi (by omega) (by omega) (by omega) hsh hhi hs'
        (by rw [upd_other sel (lo - 1) r (by omega)]; exact hx)
    else
      have : lo = 0 := by omega
      subst this; exact ⟨sel, hs, hx⟩

/-- **Subir hasta la cima**, conservando lo elegido en el paso `s`. -/
theorem seg_up_all (g : GPathM) (adj : AdjacentOwners.Adj g) (hsym : Threaded.OwnSymmetric g)
    (hnode : ∀ pid n, g.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < g.current_step → (g.node? q).isSome)
    (hseg : SegGood g) (s : Int) (x : PathNodeId) :
    ∀ (fuel : Nat) (sel : Int → PathNodeId) (hi : Int),
      (g.current_step - 1 - hi).toNat ≤ fuel → 0 ≤ s → s ≤ hi → hi ≤ g.current_step - 1 →
      Seg g sel 0 hi → sel s = x →
      ∃ sel', Seg g sel' 0 (g.current_step - 1) ∧ sel' s = x := by
  intro fuel
  induction fuel with
  | zero =>
    intro sel hi hm hs0 hsh hhi hs hx
    have : hi = g.current_step - 1 := by omega
    subst this; exact ⟨sel, hs, hx⟩
  | succ fuel ih =>
    intro sel hi hm hs0 hsh hhi hs hx
    if hlt : hi < g.current_step - 1 then
      obtain ⟨r, hs'⟩ := seg_up g adj hsym hnode hseg sel 0 hi (Int.le_refl _) (by omega) hlt hs
      exact ih _ (hi + 1) (by omega) hs0 (by omega) (by omega) hs'
        (by rw [upd_other sel (hi + 1) r (by omega)]; exact hx)
    else
      have : hi = g.current_step - 1 := by omega
      subst this; exact ⟨sel, hs, hx⟩

/-- **Por todo nodo pasa una cadena completa poseída por pares.** Se parte del tramo `[a]`, se baja
hasta el paso 0 y se sube hasta la cima: en cada paso, cualquier entrada común sirve. -/
theorem chain_through_of_segGood (g : GPathM) (adj : AdjacentOwners.Adj g)
    (hsym : Threaded.OwnSymmetric g)
    (hnode : ∀ pid n, g.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < g.current_step → (g.node? q).isSome)
    (hseg : SegGood g) (a : PathNodeId) (na : PNodeM) (hna : g.node? a = some na)
    (ha0 : 0 ≤ a.id.step) (ha1 : a.id.step < g.current_step) :
    ∃ sel, IsChain g sel ∧ PairwiseOwned g sel ∧ sel a.id.step = a := by
  have hseed : Seg g (fun _ => a) a.id.step a.id.step :=
    ⟨⟨fun i hi1 hi2 => by
        have : i = a.id.step := by omega
        subst this; exact ⟨by rw [hna]; rfl, rfl⟩,
      fun i hi1 hi2 => by omega⟩,
     fun i j hi1 hj1 hi2 hj2 hij => absurd (by omega) hij⟩
  obtain ⟨s1, hs1, hx1⟩ := seg_down_all g adj hsym hnode hseg a.id.step a a.id.step.toNat
    (fun _ => a) a.id.step a.id.step (Nat.le_refl _) ha0 (Int.le_refl _) (Int.le_refl _)
    (by omega) hseed rfl
  obtain ⟨s2, hs2, hx2⟩ := seg_up_all g adj hsym hnode hseg a.id.step a
    (g.current_step - 1 - a.id.step).toNat s1 a.id.step (Nat.le_refl _) ha0 (Int.le_refl _)
    (by omega) hs1 hx1
  refine ⟨s2, isChain_of_partial g s2 hs2.1, fun i j hi0 hj0 hi1 hj1 hij => ?_, hx2⟩
  obtain ⟨hsj, _⟩ := hs2.1.1 j hj0 (by omega)
  obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp hsj
  obtain ⟨_, hstep⟩ := hs2.1.1 i hi0 (by omega)
  refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hstep⟩
  simp only [ownersOf, hnj]
  exact hs2.2 i j hi0 hj0 (by omega) (by omega) hij nj hnj

/-- **Y la escalera, desde `SegGood`.**

    SegGood  →  por todo nodo pasa una cadena  →  OwnerChained  →  PinAlive  →  el veredicto -/
theorem ownerChained_of_segGood (g : GPathM) (adj : AdjacentOwners.Adj g) (hsmp : Sons.SMP g)
    (hpos : 0 < g.current_step) (hgn : GownersNodes.GN g) (hsym : Threaded.OwnSymmetric g)
    (hnode : ∀ pid n, g.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < g.current_step → (g.node? q).isSome)
    (hseg : SegGood g) : ReaderChain.OwnerChained g := by
  intro q hq h0 h1
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g q).mp (hgn q hq))
  obtain ⟨sel, hchain, howned, hsq⟩ := chain_through_of_segGood g adj hsym hnode hseg q n hn h0 h1
  exact ⟨sel, SupportedRun.chainSound_of_chain g adj hsmp hpos sel hchain howned, by rw [hsq]⟩

/-- info: 'AbsSat.GraphPath.Model.TopGoodUp.chain_through_of_segGood' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_through_of_segGood

/-- info: 'AbsSat.GraphPath.Model.TopGoodUp.ownerChained_of_segGood' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownerChained_of_segGood

end AbsSat.GraphPath.Model.TopGoodUp
