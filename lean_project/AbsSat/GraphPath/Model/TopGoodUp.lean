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

end AbsSat.GraphPath.Model.TopGoodUp
