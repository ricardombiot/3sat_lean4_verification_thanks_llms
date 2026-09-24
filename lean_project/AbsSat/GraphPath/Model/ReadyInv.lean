-- lean_project/AbsSat/GraphPath/Model/ReadyInv.lean
import AbsSat.GraphPath.Model.SymInvariant

/-!
# Dos de las tres condiciones de `Ready`, demostradas (review simétrico)

`PinDoomed.Ready` pide, al empezar una vuelta que progresa: todo nodo válido, todo nodo en la global y
todo enlace dentro de la tabla. Las dos últimas son invariantes de la vuelta anterior:

* **todo nodo en la global** (`Ownership.NodesAreGowners`): tras una limpieza válida, cada nodo vivo
  está en su propio corte (`SymInvariant.self_in_cut`), luego en la global; las pasadas solo quitan de
  la global el nodo que eliminan;
* **todo enlace dentro de la tabla** (`Bridge.LinksInOwners`): el corte final de la limpieza solo
  guarda los enlaces que los dos extremos admiten; en una pasada, el desenlace quita justo los enlaces
  con los nodos que salen de la tabla del procesado, y el espejo solo le quita el procesado a esos
  mismos nodos.
-/

namespace AbsSat.GraphPath.Model.ReadyInv

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.SymInvariant
open AbsSat.GraphPath.Model.Ownership (NodesAreGowners)
open AbsSat.GraphPath.Model.Bridge (LinksInOwners)

-- ============================================================
-- Todo nodo en la global
-- ============================================================

theorem nodesGow_of_same {g g' : GPathM} (hpr : Pruned g g') (hg : g'.gowners = g.gowners)
    (h : NodesAreGowners g) : NodesAreGowners g' := by
  intro n' hn'
  obtain ⟨n, hn, hid, _, _⟩ := hpr.nodes_derived n' hn'
  rw [hid, hg]; exact h n hn

theorem nodesGow_removeNode (g : GPathM) (id : PathNodeId) (h : NodesAreGowners g) :
    NodesAreGowners (removeNode g id) := by
  intro n' hn'
  rw [removeNode_nodes] at hn'
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hn'
  have hf := List.mem_filter.mp hn
  rw [removeNode_gowners]
  exact List.mem_filter.mpr ⟨h n hf.1, hf.2⟩

theorem nodesGow_reviewNode (g : GPathM) (nb : PNodeM → List PathNodeId) (x : PathNodeId)
    (h : NodesAreGowners g) : NodesAreGowners (reviewNode g nb x) := by
  unfold reviewNode
  cases hd : g.node? x with
  | none => exact h
  | some d =>
    simp only
    have h1 : NodesAreGowners (updateAt g x
        (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g (nb d)) })) :=
      nodesGow_of_same (pruned_updateAt g x _ (fun _ => rfl)
        (fun _ _ hq => (List.mem_filter.mp hq).1) (fun _ _ hp => hp)) rfl h
    have h2 := nodesGow_of_same (pruned_mirrorDrop _ x (cutRemoved d (unionOwnersOf g (nb d)))) rfl h1
    have h3 := nodesGow_of_same (pruned_unlinkIncompatible _ x) (unlinkIncompatible_gowners _ x) h2
    split
    · split
      · exact h3
      · exact nodesGow_removeNode _ x h3
    · exact nodesGow_removeNode g x h

theorem nodesGow_foldl (nb : PNodeM → List PathNodeId) :
    ∀ (L : List PathNodeId) (g : GPathM), NodesAreGowners g →
      NodesAreGowners (L.foldl (fun g id => reviewNode g nb id) g) := by
  intro L
  induction L with
  | nil => intro g h; exact h
  | cons x xs ih => intro g h; exact ih _ (nodesGow_reviewNode g nb x h)

theorem nodesGow_reviewSteps (nb : PNodeM → List PathNodeId) :
    ∀ (ks : List Int) (g : GPathM), NodesAreGowners g → NodesAreGowners (reviewSteps g nb ks) := by
  intro ks
  induction ks with
  | nil => intro g h; exact h
  | cons k ks ih =>
    intro g h
    unfold reviewSteps
    split
    · exact ih _ (nodesGow_foldl nb _ g h)
    · exact h

/-- **Tras una limpieza válida, todo nodo está en la global.** -/
theorem nodesGow_cleanInvalid₂ (g : GPathM) (hnd : NodupIds g) (hsh : ShapeOk g)
    (hv : isValid (cleanInvalid₂ g) = true) : NodesAreGowners (cleanInvalid₂ g) := by
  let g0 := purgeFuel (g.nodes.length + 1) g
  have hst := CleanTwoPhase.stable_purgeFuel _ g hnd (Nat.lt_succ_self _) hv
  have hsh0 := hsh.of_pruned (pruned_purgeFuel (g.nodes.length + 1) g)
  have hnd0 : NodupIds g0 :=
    List.Sublist.nodup (CleanTwoPhase.keeps_purgeFuel _ g).2.2.2 hnd
  have hv0 : isValid g0 = true := hv
  intro n' hn'
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hn'
  show n.id ∈ g0.gowners
  have hin := self_in_cut g0 hsh0 hst n.id n (node?_of_mem hnd0 n hn)
  have hse : hasStepEntry g0.gowners n.id.id.step = true :=
    hasStepEntry_of_isValid _ hv0 _ (hsh0.snn n hn) (hsh0.below n hn)
  rw [hse] at hin
  simp only [Bool.not_true, Bool.false_or] at hin
  exact List.contains_iff_mem.mp hin

/-- **`cleanPair` termina en una limpieza de un estado con ids sin repetir y forma buena.** -/
theorem cleanPair_eq_clean_ok (g : GPathM) (hnd : NodupIds g) (hsh : ShapeOk g) :
    ∃ h, cleanPair g = cleanInvalid₂ h ∧ NodupIds h ∧ ShapeOk h :=
  cleanPair_inv (fun x => ∃ h, x = cleanInvalid₂ h ∧ NodupIds h ∧ ShapeOk h) g ⟨g, rfl, hnd, hsh⟩
    (fun x _ ⟨h, hx, hndh, hshh⟩ =>
      have hndx : NodupIds x := hx ▸ CleanTwoPhase.nodupIds_cleanInvalid₂ h hndh
      have hshx : ShapeOk x := hx ▸ hshh.of_pruned (pruned_cleanInvalid₂ h)
      ⟨pairSweep x, rfl, SymInvariant.nodupIds_pairSweep x hndx, hshx.of_pruned (pruned_pairSweep x)⟩)

/-- **Tras una limpieza con parejas válida, todo nodo está en la global.** -/
theorem nodesGow_cleanPair (g : GPathM) (hnd : NodupIds g) (hsh : ShapeOk g)
    (hv : isValid (cleanPair g) = true) : NodesAreGowners (cleanPair g) := by
  obtain ⟨h, he, hndh, hshh⟩ := cleanPair_eq_clean_ok g hnd hsh
  rw [he] at hv ⊢
  exact nodesGow_cleanInvalid₂ h hndh hshh hv

/-- **Tras una vuelta con limpieza válida, todo nodo está en la global.** -/
theorem nodesGow_reviewPass (g : GPathM) (hnd : NodupIds g) (hsh : ShapeOk g)
    (hv : isValid (cleanPair g) = true) : NodesAreGowners (reviewPass g) :=
  nodesGow_reviewSteps _ _ _ (nodesGow_reviewSteps _ _ _ (nodesGow_cleanPair g hnd hsh hv))

/-- info: 'AbsSat.GraphPath.Model.ReadyInv.nodesGow_reviewPass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nodesGow_reviewPass

-- ============================================================
-- Todo enlace dentro de la tabla
-- ============================================================

theorem links_removeNode (g : GPathM) (id : PathNodeId) (hnd : NodupIds g) (h : LinksInOwners g) :
    LinksInOwners (removeNode g id) := by
  intro pid d' hd'
  have hm := List.mem_of_find?_eq_some hd'
  rw [removeNode_nodes] at hm
  obtain ⟨n0, hn0, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hp, hs⟩ := h n0.id n0 (node?_of_mem hnd n0 (List.mem_filter.mp hn0).1)
  exact ⟨fun p hpm => hp p (List.mem_filter.mp hpm).1, fun q hqm => hs q (List.mem_filter.mp hqm).1⟩

/-- **El corte final de la limpieza solo guarda enlaces que el nodo admite.** -/
theorem links_cutAll (g : GPathM) : LinksInOwners (cutAll g) := by
  intro pid d' hd'
  rw [node?_cutAll] at hd'
  cases hn : g.node? pid with
  | none => rw [hn] at hd'; exact absurd hd' (by simp)
  | some n =>
    rw [hn] at hd'
    obtain rfl := (Option.some.inj hd').symm
    have hnid : g.node? n.id = some n := by rw [node?_id_eq g pid n hn]; exact hn
    have adm : ∀ x, admits g.gowners g n.id x = true → x ∈ cutOwners g.gowners n := by
      intro x hx
      unfold admits at hx
      rw [hnid] at hx
      exact List.contains_iff_mem.mp hx
    refine ⟨fun p hp => ?_, fun q hq => ?_⟩
    · have := (List.mem_filter.mp hp).2
      exact adm p (Bool.and_eq_true _ _ |>.mp this).1
    · have := (List.mem_filter.mp hq).2
      exact adm q (Bool.and_eq_true _ _ |>.mp this).1

theorem links_cleanInvalid₂ (g : GPathM) : LinksInOwners (cleanInvalid₂ g) := links_cutAll _

/-- **Un paso de una pasada conserva los enlaces dentro de la tabla.** El procesado filtra sus
enlaces contra su tabla cortada; un nodo que sigue en ella no pierde nada; uno que sale pierde a la vez
el enlace (desenlace) y la entrada (espejo). -/
theorem links_reviewNode (g : GPathM) (hnd : NodupIds g) (h : LinksInOwners g)
    (nb : PNodeM → List PathNodeId) (x : PathNodeId) : LinksInOwners (reviewNode g nb x) := by
  unfold reviewNode
  cases hd : g.node? x with
  | none => exact h
  | some d =>
    simp only
    let B := unionOwnersOf g (nb d)
    let G1 := updateAt g x (fun n => { n with owners := intersectOwners n.owners B })
    let G2 := mirrorDrop G1 x (cutRemoved d B)
    let c : PNodeM := { d with owners := intersectOwners d.owners B }
    have hdid : d.id = x := node?_id_eq g x d hd
    have hc1 : G1.node? x = some c := by
      show (updateAt g x (fun n => { n with owners := intersectOwners n.owners B })).node? x = _
      rw [updateAt_node? g x (fun n => { n with owners := intersectOwners n.owners B }) (fun _ => rfl) x d hd,
        show (d.id == x) = true from beq_iff_eq.mpr hdid]
    have hc : G2.node? x = some c := by
      show (mirrorDrop G1 x (cutRemoved d B)).node? x = _
      rw [mirrorDrop_node? _ x _ x _ hc1, SegReview.mirrorMap_self_cut_eq x d B hdid]
    have hnd1 : NodupIds G1 := PinAliveChain.NodupIds_updateAt g x _ (fun _ => rfl) hnd
    have hnd2 : NodupIds G2 := SegReview.NodupIds_mirrorDrop _ x _ hnd1
    have hG3 : LinksInOwners (unlinkIncompatible G2 x) := by
      intro y n' hn'
      cases hm : G2.node? y with
      | none =>
        exfalso
        have hmem := List.mem_of_find?_eq_some hn'
        have hshape : (unlinkIncompatible G2 x).nodes = G2.nodes.map (unlinkMap c x) := by
          simp only [GPathM.unlinkIncompatible, hc]
        rw [hshape] at hmem
        obtain ⟨m0, hm0, heq⟩ := List.mem_map.mp hmem
        have hid : m0.id = y := by rw [← node?_id_eq _ y n' hn', ← heq, unlinkMap_id]
        have := node?_isSome_of_mem G2 m0 hm0
        rw [hid, hm] at this
        exact Bool.noConfusion this
      | some m =>
        rw [unlinkIncompatible_node? G2 x c hc y m hm] at hn'
        obtain rfl := (Option.some.inj hn')
        have hmid : m.id = y := node?_id_eq _ y m hm
        -- `m` comes from `g`
        obtain ⟨m1, hm1, hmeq⟩ := mirrorDrop_node?_inv G1 x _ y m hm
        obtain ⟨m0, hm0, hm1eq⟩ := Reader.updateAt_node?_inv g x
          (fun n => { n with owners := intersectOwners n.owners B }) (fun _ => rfl) y m1 hm1
        have hm0id : m0.id = y := node?_id_eq g y m0 hm0
        obtain ⟨hp0, hs0⟩ := h y m0 hm0
        unfold GPathM.unlinkMap
        split
        · next hb =>
          -- `y` is `x`: `m` is the cut node, its links filtered by its own table
          have hyx : y = x := by rw [← hmid]; exact eq_of_beq hb
          have hmc : m = c := by rw [hyx] at hm; exact Option.some.inj (hm.symm.trans hc)
          refine ⟨fun p hp => ?_, fun q hq => ?_⟩
          · have := (List.mem_filter.mp hp).2
            rw [hmc]; exact List.contains_iff_mem.mp this
          · have := (List.mem_filter.mp hq).2
            rw [hmc]; exact List.contains_iff_mem.mp this
        · next hb =>
          have hyx : y ≠ x := fun he => hb (by rw [hmid, he]; exact beq_self_eq_true x)
          have hb0 : (m0.id == x) = false := by rw [hm0id]; exact beq_false_of_ne hyx
          rw [hm1eq, hb0] at hmeq
          -- `m = mirrorMap x rem m0`
          split
          · next hin =>
            -- `y` stays in the cut: the mirror does not touch it
            have hnot : (cutRemoved d B).contains m0.id = false := by
              rw [hm0id]
              refine not_mem_cutRemoved d B y (fun _ => ?_)
              have : y ∈ c.owners := by rw [← hmid]; exact List.contains_iff_mem.mp hin
              exact this
            rw [hmeq, mirrorMap_of_not _ _ m0 hnot]
            exact ⟨hp0, hs0⟩
          · -- `y` leaves the cut: link and entry `x` both go
            refine ⟨fun p hp => ?_, fun q hq => ?_⟩
            · obtain ⟨hpm, hpx⟩ := List.mem_filter.mp hp
              rw [hmeq, mirrorMap_parents] at hpm
              show p ∈ m.owners
              rw [hmeq]
              exact mirrorMap_owners_keep _ _ m0 p (hp0 p hpm) (bne_iff_ne.mp hpx)
            · obtain ⟨hqm, hqx⟩ := List.mem_filter.mp hq
              rw [hmeq, mirrorMap_sons] at hqm
              show q ∈ m.owners
              rw [hmeq]
              exact mirrorMap_owners_keep _ _ m0 q (hs0 q hqm) (bne_iff_ne.mp hqx)
    have hnd3 : NodupIds (unlinkIncompatible G2 x) := PinAliveChain.NodupIds_unlinkIncompatible _ x hnd2
    split
    · split
      · exact hG3
      · exact links_removeNode _ x hnd3 hG3
    · exact links_removeNode g x hnd h

theorem links_foldl (nb : PNodeM → List PathNodeId) :
    ∀ (L : List PathNodeId) (g : GPathM), NodupIds g → LinksInOwners g →
      LinksInOwners (L.foldl (fun g id => reviewNode g nb id) g) := by
  intro L
  induction L with
  | nil => intro g _ h; exact h
  | cons x xs ih =>
    intro g hnd h
    exact ih _ (List.Nodup.sublist (NodeIds.ids_reviewNode g nb x) hnd) (links_reviewNode g hnd h nb x)

theorem links_reviewSteps (nb : PNodeM → List PathNodeId) :
    ∀ (ks : List Int) (g : GPathM), NodupIds g → LinksInOwners g →
      LinksInOwners (reviewSteps g nb ks) := by
  intro ks
  induction ks with
  | nil => intro g _ h; exact h
  | cons k ks ih =>
    intro g hnd h
    unfold reviewSteps
    split
    · exact ih _ (List.Nodup.sublist (NodeIds.ids_reviewLine g nb k) hnd) (links_foldl nb _ g hnd h)
    · exact h

/-- **Tras una vuelta, todo enlace está dentro de la tabla.** -/
theorem links_cleanPair (g : GPathM) : LinksInOwners (cleanPair g) := by
  obtain ⟨h, he, _⟩ := cleanPair_eq_clean g
  rw [he]; exact links_cleanInvalid₂ h

theorem links_reviewPass (g : GPathM) (hnd : NodupIds g) : LinksInOwners (reviewPass g) := by
  have h0 : NodupIds (cleanPair g) := List.Nodup.sublist (NodeIds.ids_cleanPair g) hnd
  have h1 : NodupIds (reviewParents (cleanPair g)) :=
    List.Nodup.sublist (NodeIds.ids_reviewSteps _ (·.parents) _) h0
  exact links_reviewSteps _ _ _ h1 (links_reviewSteps _ _ _ h0 (links_cleanPair g))

/-- info: 'AbsSat.GraphPath.Model.ReadyInv.links_reviewPass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms links_reviewPass

end AbsSat.GraphPath.Model.ReadyInv
