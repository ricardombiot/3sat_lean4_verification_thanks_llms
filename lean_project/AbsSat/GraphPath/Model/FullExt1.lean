-- lean_project/AbsSat/GraphPath/Model/FullExt1.lean
import AbsSat.GraphPath.Model.FullExt

/-!
# `FullExt1`: cada entrada de la tabla global está en una cadena completa dentro de ella

`FullExtG` pedía de más: exige que **todo** tramo se extienda, y la unión crea tramos que mezclan los
dos lados y no se extienden (`row-degree joinext`, semilla 1: 3 de 710 uniones con lados limpios,
36 tramos, y sobreviven al review; `fullext`: 12 tramos en un estado del lector). La escalera solo
usa el tramo `[q]` de una entrada, y para eso basta:

    FullExt1 g  :=  toda entrada global q está en una cadena completa dentro de la global

Medido (`row-degree ext1`, semilla 1): **0 fallos** tras cada unión (24.411 entradas), en la línea
(29.987), tras su review y en el lector (3.297).

Y con un solo nodo la unión deja de ser un problema: la cadena de un lado es cadena de la unión,
porque la unión solo añade (`fullExt1_join`, sin `NoMix`).
-/

namespace AbsSat.GraphPath.Model.FullExt1

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.TopGoodUp
open AbsSat.GraphPath.Model.FullExt
open AbsSat.GraphPath.Model.Extendable (upd upd_self upd_other isChain_of_partial)

/-- **Cada entrada de la tabla global está en una cadena completa dentro de ella.** -/
def FullExt1 (g : GPathM) : Prop :=
  ∀ q ∈ g.gowners, 0 ≤ q.id.step → q.id.step < g.current_step →
    ∃ s, FullChainG g s ∧ s q.id.step = q

/-- `FullExtG` da `FullExt1`: es su tramo de un nodo. -/
theorem fullExt1_of_fullExtG (g : GPathM) (hgn : GownersNodes.GN g) (h : FullExtG g) :
    FullExt1 g := by
  intro q hq h0 h1
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((GownersNodes.hasNode_iff g q).mp (hgn q hq))
  have hseg : Seg g (fun _ => q) q.id.step q.id.step :=
    ⟨⟨fun i hi1 hi2 => by
        have : i = q.id.step := by omega
        subst this; exact ⟨by rw [hn]; rfl, rfl⟩,
      fun i hi1 hi2 => by omega⟩,
     fun i j hi1 hj1 hi2 hj2 hij => absurd (by omega) hij⟩
  obtain ⟨s, hs, hsg, hag⟩ := h (fun _ => q) q.id.step q.id.step h0 (Int.le_refl _) (by omega) hseg
    (fun _ _ _ => hq)
  exact ⟨s, ⟨hs, hsg⟩, hag q.id.step (Int.le_refl _) (Int.le_refl _)⟩

/-- **La escalera**: por toda entrada global pasa una cadena `ChainSound`. -/
theorem ownerChained_of_fullExt1 (g : GPathM) (adj : AdjacentOwners.Adj g) (hsmp : Sons.SMP g)
    (hpos : 0 < g.current_step) (h : FullExt1 g) : ReaderChain.OwnerChained g := by
  intro q hq h0 h1
  obtain ⟨s, ⟨hs, _⟩, hsq⟩ := h q hq h0 h1
  have hchain := isChain_of_partial g s hs.1
  have howned : PairwiseOwned g s := by
    intro i j hi0 hj0 hi1 hj1 hij
    obtain ⟨hsj, _⟩ := hs.1.1 j hj0 (by omega)
    obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp hsj
    obtain ⟨_, hstep⟩ := hs.1.1 i hi0 (by omega)
    refine List.mem_filter.mpr ⟨?_, beq_iff_eq.mpr hstep⟩
    simp only [ownersOf, hnj]
    exact hs.2 i j hi0 hj0 (by omega) (by omega) hij nj hnj
  exact ⟨s, SupportedRun.chainSound_of_chain g adj hsmp hpos s hchain howned, by rw [hsq]⟩

/-- info: 'AbsSat.GraphPath.Model.FullExt1.ownerChained_of_fullExt1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ownerChained_of_fullExt1

-- ============================================================
-- El `up`
-- ============================================================

/-- **El `up` conserva `FullExt1`.** Una entrada antigua: su cadena, más el hijo de fila de la cima.
Una entrada de la fila: la cadena de uno de sus padres, más ella. -/
theorem fullExt1_addNode (P : GPathM) (d : NodeId) (t : String) (hd : d.step = P.current_step)
    (hpos : 0 < P.current_step)
    (hbelow : ∀ n ∈ P.nodes, n.id.id.step < P.current_step) (hgn : GownersNodes.GN P)
    (hgow : ∀ pid n, P.node? pid = some n → ∀ q ∈ n.owners, 0 ≤ q.id.step →
      q.id.step < P.current_step → q ∈ P.gowners)
    (hself : ∀ pid n, P.node? pid = some n → pid ∈ n.owners) (h : FullExt1 P) :
    FullExt1 (addNode P d t) := by
  have rowOf : ∀ p np, P.node? p = some np → p.id.step = P.current_step - 1 →
      shiftPid p d ∈ newRowIds P d ∧ p ∈ rowParents P d (shiftPid p d) := by
    intro p np hnp hps
    have hpn : p ∈ newParents P := by
      unfold newParents; rw [if_pos hpos]; exact mem_line_of_node? P p np hnp _ hps
    exact ⟨mem_newRowIds_of_mem_newParents P d p hpos hpn, mem_rowParents_of_mem_newParents P d p hpn⟩
  have hc : (addNode P d t).current_step - 1 = P.current_step := by rw [addNode_current]; omega
  have grow : ∀ s, FullChainG P s → ∀ v, v ∈ newRowIds P d →
      s (P.current_step - 1) ∈ rowParents P d v →
      FullChainG (addNode P d t) (upd s P.current_step v) := by
    intro s hs v hv hpv
    obtain ⟨hsU, hgU⟩ := append_row P d t hd hbelow hself s hs.1 hs.2 v hv hpv hpos
    exact ⟨by rw [hc]; exact hsU, fun j h0 h1 => hgU j h0 (by rw [hc] at h1; exact h1)⟩
  intro q hq h0 _
  rw [addNode_gowners] at hq
  rcases List.mem_append.mp hq with hqo | hqn
  · obtain ⟨m, hmm, hmid⟩ := hgn q hqo
    have hqs : q.id.step < P.current_step := by rw [← hmid]; exact hbelow m hmm
    obtain ⟨s, hs, hsq⟩ := h q hqo h0 hqs
    obtain ⟨hpsome, hps⟩ := hs.1.1.1 (P.current_step - 1) (by omega) (Int.le_refl _)
    obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp hpsome
    obtain ⟨hv, hpv⟩ := rowOf _ np hnp hps
    exact ⟨_, grow s hs _ hv hpv, by rw [upd_other s _ _ (by omega)]; exact hsq⟩
  · obtain ⟨p, hp⟩ := row_has_parent P hpos d q hqn
    obtain ⟨⟨np, hnp⟩, hps⟩ := TopGoodUp.rowParent_node P hpos d q p hp
    have hpg : p ∈ P.gowners := hgow p np hnp p (hself p np hnp) (by omega) (by omega)
    obtain ⟨s, hs, hsp⟩ := h p hpg (by omega) (by omega)
    have htop : s (P.current_step - 1) = p := by rw [← hps]; exact hsp
    have hqs : q.id.step = P.current_step := by rw [mapId_of_mem_newRowIds P d q hqn, hd]
    exact ⟨_, grow s hs q hqn (by rw [htop]; exact hp), by rw [hqs, upd_self]⟩

/-- info: 'AbsSat.GraphPath.Model.FullExt1.fullExt1_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullExt1_addNode

-- ============================================================
-- La unión
-- ============================================================

/-- **Una cadena completa sigue siéndolo en un estado que solo crece.** -/
theorem fullChain_of_grown {g g' : GPathM} (hg : Grown g g') (s : Int → PathNodeId)
    (h : FullChainG g s) : FullChainG g' s := by
  obtain ⟨⟨⟨hn, hl⟩, ho⟩, hgw⟩ := h
  have hc : g'.current_step = g.current_step := hg.step_eq
  refine ⟨⟨⟨fun i h0 h1 => ?_, fun i h0 h1 => ?_⟩, fun i j hi0 hj0 hi1 hj1 hij nj hnj => ?_⟩,
    fun j h0 h1 => ?_⟩
  · obtain ⟨hs, hst⟩ := hn i h0 (by rw [hc] at h1; exact h1)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨m', hm', _⟩ := hg.node?_grown _ m hm
    exact ⟨by rw [hm']; rfl, hst⟩
  · have hli := hl i h0 (by rw [hc] at h1; exact h1)
    obtain ⟨hs1, _⟩ := hn (i + 1) (by omega) (by rw [hc] at h1; exact h1)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs1
    obtain ⟨m', hm', _, hp, _⟩ := hg.node?_grown _ m hm
    rw [hm] at hli
    rw [hm']
    simp only [Option.map_some, Option.getD_some] at hli ⊢
    exact hp _ hli
  · obtain ⟨hsj, _⟩ := hn j hj0 (by rw [hc] at hj1; exact hj1)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsj
    obtain ⟨m', hm', ho', _⟩ := hg.node?_grown _ m hm
    rw [hm'] at hnj
    cases hnj
    exact ho' _ (ho i j hi0 hj0 (by rw [hc] at hi1; exact hi1) (by rw [hc] at hj1; exact hj1) hij
      m hm)
  · exact hg.gowners_grown _ (hgw j h0 (by rw [hc] at h1; exact h1))

/-- **La unión conserva `FullExt1`, sin `NoMix`**: la entrada viene de un lado, y la cadena de ese
lado es cadena de la unión. -/
theorem fullExt1_join (g₁ g₂ : GPathM) (hok : okJoin g₁ g₂ = true) (h₁ : FullExt1 g₁)
    (h₂ : FullExt1 g₂) : FullExt1 (join g₁ g₂) := by
  have G₁ := grown_join_left g₁ g₂
  have G₂ := grown_join_right g₁ g₂ hok
  intro q hq h0 h1
  have hj : (join g₁ g₂).gowners =
      g₁.gowners ++ g₂.gowners.filter (fun q => !g₁.gowners.contains q) := rfl
  rw [hj] at hq
  rcases List.mem_append.mp hq with hq1 | hq2
  · obtain ⟨s, hs, hsq⟩ := h₁ q hq1 h0 (by rw [← G₁.step_eq]; exact h1)
    exact ⟨s, fullChain_of_grown G₁ s hs, hsq⟩
  · obtain ⟨s, hs, hsq⟩ := h₂ q (List.mem_filter.mp hq2).1 h0 (by rw [← G₂.step_eq]; exact h1)
    exact ⟨s, fullChain_of_grown G₂ s hs, hsq⟩

/-- info: 'AbsSat.GraphPath.Model.FullExt1.fullExt1_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullExt1_join

-- ============================================================
-- El review
-- ============================================================

/-- **La completitud del review, entrada a entrada**: lo que el review deja en la tabla global ya
estaba en una cadena que sobrevive (`ChainSound`). -/
def ReviewComplete1 (g : GPathM) : Prop :=
  ∀ q ∈ (AggressiveReview.reviewAgg g).gowners, 0 ≤ q.id.step → q.id.step < g.current_step →
    ∃ s, ChainSound g s ∧ s q.id.step = q

theorem fullExt1_reviewAgg (g : GPathM) (h : ReviewComplete1 g) :
    FullExt1 (AggressiveReview.reviewAgg g) := by
  intro q hq h0 h1
  have hpr := AggressiveReview.pruned_reviewAgg g
  obtain ⟨s, hs, hsq⟩ := h q hq h0 (by rw [← hpr.step_eq]; exact h1)
  exact ⟨s, fullChain_of_chainSound _ s (AggressiveReview.ChainSound_reviewAgg g s hs), hsq⟩

/-- info: 'AbsSat.GraphPath.Model.FullExt1.fullExt1_reviewAgg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullExt1_reviewAgg

end AbsSat.GraphPath.Model.FullExt1
