-- lean_project/AbsSat/GraphPath/Model/FullExt.lean
import AbsSat.GraphPath.Model.SegReview

/-!
# `FullExtG`: todo tramo se extiende a una cadena completa, dentro de la tabla global

El invariante único. Un tramo —enlazado por padres, poseído por pares— cuyos miembros están en la
tabla global se extiende a una cadena completa, del paso 0 a la cima, formada solo por nodos de la
tabla global y sin cambiar sus miembros.

* **Da la escalera sin nada más**: el tramo `[q]` de una entrada global se extiende a una cadena por
  `q` (`ownerChained_of_fullExtG`). Ni simetría, ni descenso paso a paso.
* **El `up` lo conserva sin simetría** (`fullExtG_addNode`): a la cadena completa del estado de antes
  se le añade el hijo de fila de su último nodo, que hereda su tabla y al que todos ganan como owner.

Medido (`row-degree fullext`, `cleanobl`, `filterkill`): se cumple en todas las clases de estado, y
tras un filtro **el review mata exactamente los tramos que no se extienden dentro de la global y
conserva todos los que sí** (`dos_de_tres.cnf`: 1.904 + 1.896, sin excepción).
-/

namespace AbsSat.GraphPath.Model.FullExt

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.TopGoodUp
open AbsSat.GraphPath.Model.SegReview
open AbsSat.GraphPath.Model.Extendable (upd upd_self upd_other isChain_of_partial)

/-- **Todo tramo dentro de la tabla global se extiende a una cadena completa dentro de ella.** -/
def FullExtG (g : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi ≤ g.current_step - 1 →
    Seg g sel lo hi → (∀ j, lo ≤ j → j ≤ hi → sel j ∈ g.gowners) →
    ∃ sel', Seg g sel' 0 (g.current_step - 1) ∧
      (∀ j, 0 ≤ j → j ≤ g.current_step - 1 → sel' j ∈ g.gowners) ∧
      ∀ j, lo ≤ j → j ≤ hi → sel' j = sel j

-- ============================================================
-- La escalera
-- ============================================================

/-- **Por toda entrada global pasa una cadena completa poseída por pares**, y con ella
`OwnerChained`. -/
theorem ownerChained_of_fullExtG (g : GPathM) (adj : AdjacentOwners.Adj g) (hsmp : Sons.SMP g)
    (hpos : 0 < g.current_step) (hgn : GownersNodes.GN g) (h : FullExtG g) :
    ReaderChain.OwnerChained g := by
  intro q hq h0 h1
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g q).mp (hgn q hq))
  have hseg : Seg g (fun _ => q) q.id.step q.id.step :=
    ⟨⟨fun i hi1 hi2 => by
        have : i = q.id.step := by omega
        subst this; exact ⟨by rw [hn]; rfl, rfl⟩,
      fun i hi1 hi2 => by omega⟩,
     fun i j hi1 hj1 hi2 hj2 hij => absurd (by omega) hij⟩
  obtain ⟨s, hs, _, hag⟩ := h (fun _ => q) q.id.step q.id.step h0 (Int.le_refl _) (by omega) hseg
    (fun _ _ _ => hq)
  have hchain := isChain_of_partial g s hs.1
  have howned : PairwiseOwned g s := by
    intro i j hi0 hj0 hi1 hj1 hij
    obtain ⟨hsj, _⟩ := hs.1.1 j hj0 (by omega)
    obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp hsj
    obtain ⟨_, hstep⟩ := hs.1.1 i hi0 (by omega)
    refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hstep⟩
    simp only [ownersOf, hnj]
    exact hs.2 i j hi0 hj0 (by omega) (by omega) hij nj hnj
  exact ⟨s, SupportedRun.chainSound_of_chain g adj hsmp hpos s hchain howned,
    by rw [hag q.id.step (Int.le_refl _) (Int.le_refl _)]⟩

-- ============================================================
-- El `up`
-- ============================================================

/-- Un nodo antiguo gana como owner a un nodo de fila cuya tabla lo contiene. -/
theorem gained_of_row (P : GPathM) (d : NodeId) (v : PathNodeId) (hv : v ∈ newRowIds P d)
    (x : PathNodeId) (nx : PNodeM) (hnx : nx.id = x) (hx : x ∈ rowOwners P d v) :
    v ∈ (upMap P d nx).owners := by
  rw [upMap_owners]
  refine List.mem_append_right _ (List.mem_filter.mpr ⟨hv, ?_⟩)
  rw [hnx]; exact List.elem_iff.mpr hx

/-- **Añadir el hijo de fila a una cadena completa dentro de la global**: sigue siendo cadena
completa, dentro de la global, en el estado nuevo. -/
theorem append_row (P : GPathM) (d : NodeId) (t : String) (hd : d.step = P.current_step)
    (hbelow : ∀ n ∈ P.nodes, n.id.id.step < P.current_step)
    (hself : ∀ pid n, P.node? pid = some n → pid ∈ n.owners)
    (s : Int → PathNodeId) (hs : Seg P s 0 (P.current_step - 1))
    (hsg : ∀ j, 0 ≤ j → j ≤ P.current_step - 1 → s j ∈ P.gowners)
    (v : PathNodeId) (hv : v ∈ newRowIds P d)
    (hpv : s (P.current_step - 1) ∈ rowParents P d v) (hpos : 0 < P.current_step) :
    Seg (addNode P d t) (upd s P.current_step v) 0 P.current_step ∧
      ∀ j, 0 ≤ j → j ≤ P.current_step → upd s P.current_step v j ∈ (addNode P d t).gowners := by
  have hvnode := addNode_node?_new P d t hd hbelow v hv
  have hvs : v.id.step = P.current_step := by rw [mapId_of_mem_newRowIds P d v hv, hd]
  have nodeAt : ∀ j, 0 ≤ j → j ≤ P.current_step - 1 → ∃ nj, P.node? (s j) = some nj :=
    fun j h0 h1 => Option.isSome_iff_exists.mp (hs.1.1 j h0 h1).1
  -- lo que está en la tabla del último nodo y en la global, lo tiene `v`
  obtain ⟨np, hnp⟩ := nodeAt (P.current_step - 1) (by omega) (Int.le_refl _)
  have inV : ∀ i, 0 ≤ i → i ≤ P.current_step - 1 → s i ∈ rowOwners P d v := by
    intro i hi0 hi1
    have hin : s i ∈ np.owners := by
      rcases int_eq_or_ne i (P.current_step - 1) with he | he
      · subst he; exact hself _ np hnp
      · exact hs.2 i _ hi0 (by omega) hi1 (Int.le_refl _) he np hnp
    exact row_of_parent P d v _ hpv np hnp _ hin (hsg i hi0 hi1)
  refine ⟨⟨⟨fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_⟩, fun i j hi1 hj1 hi2 hj2 hij nj hnj => ?_⟩,
    fun j hj0 hj1 => ?_⟩
  · rcases int_eq_or_ne i P.current_step with he | he
    · subst he; rw [upd_self, hvnode]; exact ⟨rfl, hvs⟩
    · rw [upd_other s _ v he]
      obtain ⟨ni, hni⟩ := nodeAt i hi1 (by omega)
      rw [addNode_node?_old P d t _ ni hni]
      exact ⟨rfl, (hs.1.1 i hi1 (by omega)).2⟩
  · rcases int_eq_or_ne i (P.current_step - 1) with he | he
    · subst he
      rw [show P.current_step - 1 + 1 = P.current_step by omega, upd_self, hvnode,
        upd_other s _ v (show P.current_step - 1 ≠ P.current_step by omega)]
      simpa [rowNode_parents] using hpv
    · rw [upd_other s _ v (by omega), upd_other s _ v (by omega)]
      obtain ⟨ni1, hni1⟩ := nodeAt (i + 1) (by omega) (by omega)
      rw [addNode_node?_old P d t _ ni1 hni1]
      have hl := hs.1.2 i hi1 (by omega)
      rw [hni1] at hl
      simpa [upMap_parents] using hl
  · rcases int_eq_or_ne j P.current_step with hje | hje
    · subst hje
      rw [upd_self, hvnode] at hnj; cases hnj
      rw [upd_other s _ v (by omega)]
      exact inV i hi1 (by omega)
    · rw [upd_other s _ v hje] at hnj
      obtain ⟨nj0, hnj0⟩ := nodeAt j hj1 (by omega)
      rw [addNode_node?_old P d t _ nj0 hnj0] at hnj; cases hnj
      rcases int_eq_or_ne i P.current_step with hie | hie
      · subst hie
        rw [upd_self]
        exact gained_of_row P d v hv _ nj0 (node?_id_eq P _ nj0 hnj0) (inV j hj1 (by omega))
      · rw [upd_other s _ v hie]
        exact (old_mem P d hd nj0 _ (by rw [(hs.1.1 i hi1 (by omega)).2]; omega)).mpr
          (hs.2 i j hi1 hj1 (by omega) (by omega) hij nj0 hnj0)
  · rw [addNode_gowners]
    rcases int_eq_or_ne j P.current_step with he | he
    · subst he; rw [upd_self]; exact List.mem_append_right _ hv
    · rw [upd_other s _ v he]; exact List.mem_append_left _ (hsg j hj0 (by omega))

/-- info: 'AbsSat.GraphPath.Model.FullExt.ownerChained_of_fullExtG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownerChained_of_fullExtG

/-- info: 'AbsSat.GraphPath.Model.FullExt.append_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms append_row

/-- **El `up` conserva `FullExtG`, sin simetría.** Un tramo antiguo se extiende en el estado de antes
y se le añade el hijo de fila de su último nodo; uno que acaba en la fila se extiende por su parte
antigua —o por un padre de la cima, si es solo la cima— y se le añade la cima. -/
theorem fullExtG_addNode (P : GPathM) (d : NodeId) (t : String) (hd : d.step = P.current_step)
    (hpos : 0 < P.current_step)
    (hbelow : ∀ n ∈ P.nodes, n.id.id.step < P.current_step)
    (hgow : ∀ pid n, P.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < P.current_step → q ∈ P.gowners)
    (hself : ∀ pid n, P.node? pid = some n → pid ∈ n.owners) (h : FullExtG P) :
    FullExtG (addNode P d t) := by
  intro sel lo hi hlo0 hlohi hhi hs hsg
  have hcsU : (addNode P d t).current_step - 1 = P.current_step := by rw [addNode_current]; omega
  rw [hcsU] at hhi ⊢
  have oldAt : ∀ j, lo ≤ j → j ≤ hi → j ≤ P.current_step - 1 →
      ∃ nj, P.node? (sel j) = some nj ∧ (addNode P d t).node? (sel j) = some (upMap P d nj) := by
    intro j hj1 hj2 hj3
    obtain ⟨hsm, hjs⟩ := hs.1.1 j hj1 hj2
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsm
    rcases lookup P d t hd hbelow _ m hm with ⟨_, n, hn, rfl⟩ | ⟨hst, _⟩
    · exact ⟨n, hn, hm⟩
    · omega
  -- la parte antigua del tramo es tramo del estado de antes, dentro de su global
  have restrict : ∀ top', lo ≤ top' → top' ≤ hi → top' ≤ P.current_step - 1 →
      Seg P sel lo top' ∧ ∀ j, lo ≤ j → j ≤ top' → sel j ∈ P.gowners := by
    intro top' h1 h2 h3
    refine ⟨⟨⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_⟩, fun i' j hi1 hj1 hi2 hj2 hij nj hnj => ?_⟩,
      fun j hj1 hj2 => ?_⟩
    · obtain ⟨nj, hnj, _⟩ := oldAt j hj1 (by omega) (by omega)
      exact ⟨by rw [hnj]; rfl, (hs.1.1 j hj1 (by omega)).2⟩
    · obtain ⟨nj, hnj, hnjU⟩ := oldAt (j + 1) (by omega) (by omega) (by omega)
      have hl := hs.1.2 j hj1 (by omega)
      rw [hnjU] at hl
      rw [hnj]
      simpa [upMap_parents] using hl
    · have hh := hs.2 i' j hi1 hj1 (by omega) (by omega) hij (upMap P d nj)
        (by rw [addNode_node?_old P d t _ nj hnj])
      exact (old_mem P d hd nj _ (by rw [(hs.1.1 i' hi1 (by omega)).2]; omega)).mp hh
    · have hm := hsg j hj1 (by omega)
      rw [addNode_gowners] at hm
      rcases List.mem_append.mp hm with hl | hr
      · exact hl
      · have := mapId_of_mem_newRowIds P d _ hr
        have hjs := (hs.1.1 j hj1 (by omega)).2
        rw [this, hd] at hjs; omega
  -- un nodo del último paso es padre de su hijo de fila
  have rowOf : ∀ p np, P.node? p = some np → p.id.step = P.current_step - 1 →
      shiftPid p d ∈ newRowIds P d ∧ p ∈ rowParents P d (shiftPid p d) := by
    intro p np hnp hps
    have hpn : p ∈ newParents P := by
      unfold newParents; rw [if_pos hpos]; exact mem_line_of_node? P p np hnp _ hps
    exact ⟨mem_newRowIds_of_mem_newParents P d p hpos hpn, mem_rowParents_of_mem_newParents P d p hpn⟩
  rcases (show hi < P.current_step ∨ hi = P.current_step by omega) with hhl | hhe
  · -- tramo antiguo
    obtain ⟨hsP, hgP⟩ := restrict hi (by omega) (Int.le_refl _) (by omega)
    obtain ⟨s, hsF, hsFg, hag⟩ := h sel lo hi hlo0 hlohi (by omega) hsP hgP
    obtain ⟨hpsome, hps⟩ := hsF.1.1 (P.current_step - 1) (by omega) (Int.le_refl _)
    obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp hpsome
    obtain ⟨hv, hpv⟩ := rowOf _ np hnp hps
    obtain ⟨hsU, hgU⟩ := append_row P d t hd hbelow hself s hsF hsFg _ hv hpv hpos
    exact ⟨_, hsU, hgU, fun j hj1 hj2 => by
      rw [upd_other s _ _ (by omega)]; exact hag j hj1 hj2⟩
  · -- tramo que acaba en la fila
    subst hhe
    obtain ⟨hvsome, hvs⟩ := hs.1.1 P.current_step hlohi (Int.le_refl _)
    obtain ⟨mv, hmv⟩ := Option.isSome_iff_exists.mp hvsome
    obtain ⟨hvrow, hmveq⟩ : sel P.current_step ∈ newRowIds P d ∧
        mv = rowNode P d t (sel P.current_step) := by
      rcases lookup P d t hd hbelow _ mv hmv with ⟨hlt, _⟩ | ⟨_, hr, he⟩
      · omega
      · exact ⟨hr, he⟩
    subst hmveq
    rcases (show lo < P.current_step ∨ lo = P.current_step by omega) with hlt | heq
    · obtain ⟨hsP, hgP⟩ := restrict (P.current_step - 1) (by omega) (by omega) (Int.le_refl _)
      obtain ⟨s, hsF, hsFg, hag⟩ := h sel lo (P.current_step - 1) hlo0 (by omega)
        (Int.le_refl _) hsP hgP
      have hpv : s (P.current_step - 1) ∈ rowParents P d (sel P.current_step) := by
        rw [hag _ (by omega) (Int.le_refl _)]
        have hl := hs.1.2 (P.current_step - 1) (by omega) (by omega)
        rw [show P.current_step - 1 + 1 = P.current_step by omega, hmv] at hl
        simpa [rowNode_parents] using hl
      obtain ⟨hsU, hgU⟩ := append_row P d t hd hbelow hself s hsF hsFg _ hvrow hpv hpos
      refine ⟨_, hsU, hgU, fun j hj1 hj2 => ?_⟩
      rcases int_eq_or_ne j P.current_step with he | he
      · subst he; rw [upd_self]
      · rw [upd_other s _ _ he]; exact hag j hj1 (by omega)
    · subst heq
      obtain ⟨p, hp⟩ := row_has_parent P hpos d _ hvrow
      obtain ⟨⟨np, hnp⟩, hps⟩ := TopGoodUp.rowParent_node P hpos d _ p hp
      have hpg : p ∈ P.gowners :=
        hgow p np hnp p (hself p np hnp) (by omega) (by omega)
      have hsp : Seg P (fun _ => p) (P.current_step - 1) (P.current_step - 1) :=
        ⟨⟨fun j hj1 hj2 => ⟨by rw [hnp]; rfl, by rw [hps]; omega⟩, fun j hj1 hj2 => by omega⟩,
         fun i' j hi1 hj1 hi2 hj2 hij => absurd (by omega) hij⟩
      obtain ⟨s, hsF, hsFg, hag⟩ := h (fun _ => p) (P.current_step - 1) (P.current_step - 1)
        (by omega) (Int.le_refl _) (Int.le_refl _) hsp (fun _ _ _ => hpg)
      have hpv : s (P.current_step - 1) ∈ rowParents P d (sel P.current_step) := by
        rw [hag _ (Int.le_refl _) (Int.le_refl _)]; exact hp
      obtain ⟨hsU, hgU⟩ := append_row P d t hd hbelow hself s hsF hsFg _ hvrow hpv hpos
      refine ⟨_, hsU, hgU, fun j hj1 hj2 => ?_⟩
      have : j = P.current_step := by omega
      subst this; rw [upd_self]

/-- info: 'AbsSat.GraphPath.Model.FullExt.fullExtG_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullExtG_addNode

end AbsSat.GraphPath.Model.FullExt
