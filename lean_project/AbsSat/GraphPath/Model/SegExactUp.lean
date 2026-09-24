-- lean_project/AbsSat/GraphPath/Model/SegExactUp.lean
import AbsSat.GraphPath.Model.SegExact

/-!
# El `up` conserva que todo tramo esté en una cadena completa

La versión por tramos de `FullExt1.fullExt1_addNode`. Un tramo del estado nuevo:

* **solo con nodos antiguos**: en el estado de antes ya era tramo (sus enlaces no cambian y las
  tablas solo ganan ids de la fila nueva, que no son del tramo), así que está en una cadena completa;
  esa cadena crece con el hijo de fila de su cima (`append_row`);
* **acabado en un nodo `v` de la fila nueva**: el resto del tramo es antiguo y su cima es un padre de
  `v` (los padres de un nodo de fila son exactamente sus `rowParents`). Su cadena de antes, más `v`,
  es la cadena completa. Si el tramo es solo `v`, sirve la cadena de uno de sus padres.

Así que **el `up` no crea tramos sin cadena**: la compatibilidad colectiva que la fila nueva hereda es
la de las cadenas que ya había. La parte de UP que queda abierta es el **filtro del envío** (los
requisitos de la cláusula), que es de la misma forma que el pin del lector.
-/

namespace AbsSat.GraphPath.Model.SegExactUp

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.TopGoodUp
open AbsSat.GraphPath.Model.FullExt
open AbsSat.GraphPath.Model.Extendable (upd upd_self upd_other)
open AbsSat.GraphPath.Model.SegExact (SegExact)

/-- An old node's gained owners are row ids, all at the new step. -/
theorem gained_step (P : GPathM) (d : NodeId) (hd : d.step = P.current_step) (n : PNodeM)
    (q : PathNodeId) (hq : q ∈ gainedOwners P d n) : q.id.step = P.current_step := by
  have hq' : q ∈ newRowIds P d := (List.mem_filter.mp hq).1
  rw [mapId_of_mem_newRowIds P d q hq', hd]

/-- Below the new step, an old node's table in the new state is its table before. -/
theorem old_owner (P : GPathM) (d : NodeId) (hd : d.step = P.current_step) (n : PNodeM)
    (q : PathNodeId) (hq : q ∈ (upMap P d n).owners) (hqs : q.id.step < P.current_step) :
    q ∈ n.owners := by
  rw [upMap_owners] at hq
  rcases List.mem_append.mp hq with h | h
  · exact h
  · have := gained_step P d hd n q h; omega

/-- **A segment of the new state below the new step was a segment before.** -/
theorem seg_old (P : GPathM) (d : NodeId) (t : String) (hd : d.step = P.current_step)
    (sel : Int → PathNodeId) (lo hi : Int) (hhi : hi ≤ P.current_step - 1)
    (hpc : Extendable.PartialChain (addNode P d t) sel lo hi)
    (hpo : ∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, (addNode P d t).node? (sel j) = some nj → sel i ∈ nj.owners) :
    Extendable.PartialChain P sel lo hi ∧
    (∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, P.node? (sel j) = some nj → sel i ∈ nj.owners) := by
  have below : ∀ i, lo ≤ i → i ≤ hi → ∃ n, P.node? (sel i) = some n ∧
      (addNode P d t).node? (sel i) = some (upMap P d n) := by
    intro i hlo hhi'
    obtain ⟨hs, hst⟩ := hpc.1 i hlo hhi'
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨n, hn, rfl⟩ := addNode_node?_below P d t hd (sel i) n' hn' (by omega)
    exact ⟨n, hn, hn'⟩
  refine ⟨⟨fun i hlo hhi' => ?_, fun i hlo hhi' => ?_⟩, fun i j hi hj hi' hj' hne nj hnj => ?_⟩
  · obtain ⟨n, hn, _⟩ := below i hlo hhi'
    exact ⟨by rw [hn]; rfl, (hpc.1 i hlo hhi').2⟩
  · have hl := hpc.2 i hlo hhi'
    obtain ⟨n, hn, hn'⟩ := below (i + 1) (by omega) hhi'
    rw [hn'] at hl
    rw [hn]
    simpa [upMap_parents] using hl
  · obtain ⟨n, hn, hn'⟩ := below j hj hj'
    rw [hnj] at hn
    cases hn
    have hs := (hpc.1 i hi hi').2
    exact old_owner P d hd nj (sel i) (hpo i j hi hj hi' hj' hne _ hn') (by omega)

/-- A node of the new state at the new step is a row node, with the row parents. -/
theorem row_node (P : GPathM) (d : NodeId) (t : String)
    (hbelow : ∀ n ∈ P.nodes, n.id.id.step < P.current_step)
    (v : PathNodeId) (n' : PNodeM) (hn' : (addNode P d t).node? v = some n')
    (hvs : v.id.step = P.current_step) :
    v ∈ newRowIds P d ∧ n'.parents = rowParents P d v := by
  have hmem : n' ∈ (addNode P d t).nodes := List.mem_of_find?_eq_some hn'
  have hid : n'.id = v := node?_id_eq _ v n' hn'
  rw [addNode_nodes] at hmem
  rcases List.mem_append.mp hmem with hl | hr
  · obtain ⟨n, hn, hEq⟩ := List.mem_map.mp hl
    have h1 := hbelow n hn
    rw [← upMap_id P d n, hEq, hid] at h1
    omega
  · obtain ⟨pid, hpid, hEq⟩ := List.mem_map.mp hr
    have hpv : pid = v := by rw [← hid, ← hEq]; rfl
    subst hpv
    refine ⟨hpid, ?_⟩
    rw [← hEq]; rfl

/-- **El `up` conserva `SegExact`.** -/
theorem segExact_addNode (P : GPathM) (d : NodeId) (t : String) (hd : d.step = P.current_step)
    (hpos : 0 < P.current_step)
    (hbelow : ∀ n ∈ P.nodes, n.id.id.step < P.current_step)
    (hself : ∀ pid n, P.node? pid = some n → pid ∈ n.owners) (h : SegExact P) :
    SegExact (addNode P d t) := by
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
  intro sel lo hi hlo hlh hhi hpc hpo
  rw [hc] at hhi
  rcases Int.lt_or_eq_of_le hhi with hlt | heq
  · -- only old nodes
    obtain ⟨hpc0, hpo0⟩ := seg_old P d t hd sel lo hi (by omega) hpc hpo
    obtain ⟨s, hs, hsel⟩ := h sel lo hi hlo hlh (by omega) hpc0 hpo0
    obtain ⟨hpsome, hps⟩ := hs.1.1.1 (P.current_step - 1) (by omega) (Int.le_refl _)
    obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp hpsome
    obtain ⟨hv, hpv⟩ := rowOf _ np hnp hps
    refine ⟨_, grow s hs _ hv hpv, fun j hj0 hj1 => ?_⟩
    rw [upd_other s _ _ (by omega)]
    exact hsel j hj0 hj1
  · -- the top is a row node `v`
    subst heq
    obtain ⟨hvs, hvst⟩ := hpc.1 P.current_step hlh (Int.le_refl _)
    obtain ⟨nv, hnv⟩ := Option.isSome_iff_exists.mp hvs
    obtain ⟨hvrow, hvpar⟩ := row_node P d t hbelow _ nv hnv hvst
    rcases Int.lt_or_eq_of_le hlh with hlt | hleq
    · -- the rest of the segment is old, and its top is a parent of `v`
      have hpc' : Extendable.PartialChain (addNode P d t) sel lo (P.current_step - 1) :=
        ⟨fun i h0 h1 => hpc.1 i h0 (by omega), fun i h0 h1 => hpc.2 i h0 (by omega)⟩
      obtain ⟨hpc0, hpo0⟩ := seg_old P d t hd sel lo (P.current_step - 1) (Int.le_refl _) hpc'
        (fun i j hi hj hi' hj' hne nj hnj => hpo i j hi hj (by omega) (by omega) hne nj hnj)
      obtain ⟨s, hs, hsel⟩ := h sel lo (P.current_step - 1) hlo (by omega) (Int.le_refl _) hpc0 hpo0
      have hlink := hpc.2 (P.current_step - 1) (by omega) (by omega)
      rw [show P.current_step - 1 + 1 = P.current_step by omega, hnv] at hlink
      simp only [Option.map_some, Option.getD_some, hvpar] at hlink
      have htop : s (P.current_step - 1) = sel (P.current_step - 1) :=
        hsel _ (by omega) (Int.le_refl _)
      refine ⟨_, grow s hs _ hvrow (by rw [htop]; exact hlink), fun j hj0 hj1 => ?_⟩
      rcases Int.lt_or_eq_of_le hj1 with hjl | hje
      · rw [upd_other s _ _ (by omega)]; exact hsel j hj0 (by omega)
      · subst hje; rw [upd_self]
    · -- the segment is only `v`: the chain of one of its parents
      subst hleq
      obtain ⟨p, hp⟩ := row_has_parent P hpos d _ hvrow
      obtain ⟨⟨np, hnp⟩, hps⟩ := TopGoodUp.rowParent_node P hpos d _ p hp
      have hseg : Extendable.PartialChain P (fun _ => p) p.id.step p.id.step :=
        ⟨fun i hi1 hi2 => by
            have : i = p.id.step := by omega
            subst this; exact ⟨by rw [hnp]; rfl, rfl⟩,
          fun i hi1 hi2 => by omega⟩
      obtain ⟨s, hs, hsel⟩ := h (fun _ => p) p.id.step p.id.step (by omega) (Int.le_refl _)
        (by omega) hseg (fun i j hi hj hi' hj' hne => absurd (by omega) hne)
      have htop : s (P.current_step - 1) = p := by
        rw [← hps]; exact hsel _ (Int.le_refl _) (Int.le_refl _)
      refine ⟨_, grow s hs _ hvrow (by rw [htop]; exact hp), fun j hj0 hj1 => ?_⟩
      have : j = P.current_step := by omega
      subst this; rw [upd_self]

/-- info: 'AbsSat.GraphPath.Model.SegExactUp.segExact_addNode' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms segExact_addNode

-- ============================================================
-- La unión
-- ============================================================

/-- **La unión no mezcla tramos**: todo tramo del estado unido es tramo, con sus propias tablas y
padres, de uno de los dos lados. Versión por tramos de `TopGoodUp.NoMix`. **Medido falso** en general
(`segmix`, semilla 1: 24 tramos mezclados); la hipótesis buena es `MixDies`, tras el review. -/
def SegNoMix (J A B : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), Seg J sel lo hi → Seg A sel lo hi ∨ Seg B sel lo hi

/-- **La unión conserva `SegExact`, si no mezcla tramos**: el tramo es de un lado, y la cadena de ese
lado sigue siendo completa en la unión (las tablas y la global solo crecen). -/
theorem segExact_doJoin (A B : GPathM) (hA : SegExact A) (hB : SegExact B)
    (hmix : okJoin A B = true → SegNoMix (join A B) A B) : SegExact (doJoin A B) := by
  unfold doJoin
  split
  · next hok =>
    have G₁ := grown_join_left A B
    have G₂ := grown_join_right A B hok
    intro sel lo hi hlo hlh hhi hpc hpo
    rcases hmix hok sel lo hi ⟨hpc, hpo⟩ with hs | hs
    · obtain ⟨s, hfs, hsel⟩ := hA sel lo hi hlo hlh (by rw [← G₁.step_eq]; exact hhi) hs.1 hs.2
      exact ⟨s, FullExt1.fullChain_of_grown G₁ s hfs, hsel⟩
    · obtain ⟨s, hfs, hsel⟩ := hB sel lo hi hlo hlh (by rw [← G₂.step_eq]; exact hhi) hs.1 hs.2
      exact ⟨s, FullExt1.fullChain_of_grown G₂ s hfs, hsel⟩
  · exact hA

/-- info: 'AbsSat.GraphPath.Model.SegExactUp.segExact_doJoin' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms segExact_doJoin

/-- **Los tramos mezclados no sobreviven al review de la unión**: todo tramo del revisado de la unión
es tramo de uno de los dos lados. `SegNoMix` (sin review) es **falso** en general — medido
(`row-degree segmix`, semilla 1, fórmula 6): 24 tramos mezclados de 142.778, ninguno en una cadena
completa —, pero el review que sigue los elimina (`segexact`: 0 fallos en los envíos y el lector). -/
def MixDies (A B : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), Seg (AggressiveReview.reviewAgg (join A B)) sel lo hi →
    Seg A sel lo hi ∨ Seg B sel lo hi

/-- **La unión revisada conserva `SegExact`**, si los tramos mezclados no sobreviven a su review: el
tramo es de un lado, su cadena crece a la unión, es sana allí y sobrevive al review. -/
theorem segExact_reviewAgg_join (A B : GPathM) (hok : okJoin A B = true)
    (hA : SegExact A) (hB : SegExact B)
    (hself : ∀ pid n, (join A B).node? pid = some n → pid ∈ n.owners)
    (hsmp : Sons.SMP (join A B)) (hroot : Sons.RootAtZero (join A B))
    (hnr : Parents.NotRoot (join A B)) (hpos : 0 < (join A B).current_step)
    (hdie : MixDies A B) : SegExact (AggressiveReview.reviewAgg (join A B)) := by
  have G₁ := grown_join_left A B
  have G₂ := grown_join_right A B hok
  have hpr := AggressiveReview.pruned_reviewAgg (join A B)
  have survive : ∀ s, FullChainG (join A B) s →
      FullChainG (AggressiveReview.reviewAgg (join A B)) s := fun s hs =>
    fullChain_of_chainSound _ s (AggressiveReview.ChainSound_reviewAgg _ s
      (chainSound_of_fullChain _ hself hsmp hroot hnr hpos s hs))
  intro sel lo hi hlo hlh hhi hpc hpo
  have hhiJ : hi ≤ (join A B).current_step - 1 := by rw [← hpr.step_eq]; exact hhi
  rcases hdie sel lo hi ⟨hpc, hpo⟩ with hs | hs
  · obtain ⟨s, hfs, hsel⟩ := hA sel lo hi hlo hlh (by rw [← G₁.step_eq]; exact hhiJ) hs.1 hs.2
    exact ⟨s, survive s (FullExt1.fullChain_of_grown G₁ s hfs), hsel⟩
  · obtain ⟨s, hfs, hsel⟩ := hB sel lo hi hlo hlh (by rw [← G₂.step_eq]; exact hhiJ) hs.1 hs.2
    exact ⟨s, survive s (FullExt1.fullChain_of_grown G₂ s hfs), hsel⟩

/-- info: 'AbsSat.GraphPath.Model.SegExactUp.segExact_reviewAgg_join' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms segExact_reviewAgg_join

end AbsSat.GraphPath.Model.SegExactUp
