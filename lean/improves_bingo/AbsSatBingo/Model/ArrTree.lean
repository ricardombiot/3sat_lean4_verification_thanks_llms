-- lean/improves_bingo/AbsSatBingo/Model/ArrTree.lean
import AbsSatBingo.Model.CliqueSplit

/-!
# `CliqueSplit` para árboles de llegadas

`cliqueSplit` (`CliqueSplit.lean`) vale para la unión de dos llegadas concretas de la línea. Para usarlo dentro de la
inducción de la línea (`JoinProv`) se generaliza a **árboles de llegadas**: una llegada `arr φ kv d` de un remitente
`kv` de la línea `steps φ n (init φ)`, o el `doJoin` de dos árboles. Cada entrada de la línea siguiente es un árbol,
y serlo se conserva al insertar sin ninguna contabilidad de remitentes.

* **`tree_facts`**: un árbol está bien (`StateOk`), tiene la estructura de la máquina (`Struct`), sigue el mapa
  (`MapLinks`) y su cima es de `d` (`TopDocsId`).
* **`tree_carried`**: una selección válida hasta `d` cuyo nodo del paso del remitente está vivo en el árbol es una
  camarilla del árbol: ese nodo es de la clave de una hoja, la completitud la lleva en el remitente y la llegada
  también (`carried_arrival`).
* **`cliqueSplitTree`**: en el `doJoin` de dos árboles, toda camarilla es camarilla de uno de los dos.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace CliqueSplit

open GPathB Driver Machine

variable {φ : Cnf}

/-- **Árbol de llegadas** a `d` desde la línea `steps φ n (init φ)`. -/
inductive ArrTree (φ : Cnf) (n : Nat) (d : NodeId) : GPathB → Prop
  | leaf (kv : NodeId × GPathB) (hkv : kv ∈ steps φ n (init φ)) (hd : d ∈ sonsOfMap φ kv.1)
      (hv : (arr φ kv d).isValid = true) : ArrTree φ n d (arr φ kv d)
  | node {t₁ t₂ : GPathB} : ArrTree φ n d t₁ → ArrTree φ n d t₂ → ArrTree φ n d (doJoin t₁ t₂)

/-- La cima de una llegada es de su destino. -/
theorem topDocsId_arr (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {d : NodeId} (hv : (arr φ kv d).isValid = true) : TopDocsId (arr φ kv d) d := by
  obtain ⟨hl, _, _, _, _⟩ := line_facts hbd n
  have hb := below_of_shrinks (shrinks_filterAll kv.2 (reqOf φ d)) (hl kv hkv).below
  show TopDocsId (kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)) d
  unfold upFiltering up
  rw [if_pos (valid_filter_of_arr hv)]
  exact topDocsId_of_shrinks (shrinks_review _) (topDocsId_addNode hb)

/-- **Los hechos de un árbol.** -/
theorem tree_facts (hbd : Bounded φ) {n : Nat} {d : NodeId} {t : GPathB} (h : ArrTree φ n d t) :
    StateOk ((n : Int) + 1 + 1) d t ∧ Struct.Struct φ t ∧ MapLinks φ t ∧ TopDocsId t d := by
  obtain ⟨hl, hent, _, hls, hml⟩ := line_facts hbd n
  induction h with
  | leaf kv hkv hd hv =>
    have ho := hl kv hkv
    exact ⟨stateOk_upFiltering ho hd hv, Struct.struct_upFiltering hbd ho (hls kv hkv).1 (hls kv hkv).2 hd,
      mapLinks_upFiltering (by omega) ho (hml kv hkv) (hent kv hkv).2 hd, topDocsId_arr hbd hkv hv⟩
  | node _ _ ih₁ ih₂ =>
    obtain ⟨o₁, s₁, m₁, t₁⟩ := ih₁
    obtain ⟨o₂, s₂, m₂, t₂⟩ := ih₂
    refine ⟨stateOk_doJoin o₁ o₂, ?_⟩
    unfold doJoin
    split
    · exact ⟨Struct.struct_join s₁ s₂, mapLinks_join m₁ m₂, topDocsId_join t₁ t₂ (o₁.step.trans o₂.step.symm)⟩
    · exact ⟨s₁, m₁, t₁⟩

/-- **Una selección válida hasta `d` con su nodo del remitente vivo en el árbol es camarilla del árbol.** -/
theorem tree_carried (hbd : Bounded φ) {n : Nat} {d : NodeId} {t : GPathB} (h : ArrTree φ n d t)
    {S : Int → PathNodeId} (hv : ValidSel φ ((n : Int) + 1) S) (hd : (S ((n : Int) + 1)).id = d)
    (hSn : S n ∈ t.alive) : Carried t S := by
  obtain ⟨hl, hent, hnd, _, _⟩ := line_facts hbd n
  induction h with
  | leaf kv hkv hdk hvk =>
    have ho := hl kv hkv
    have hon := originIn_upFiltering (φ := φ) ho (hent kv hkv).2 hdk
    have hns : (S n).id.step = (n : Int) + 1 - 1 := by rw [hv.step n (by omega) (by omega)]; omega
    have hid : (S n).id = kv.1 := hon _ hSn hns
    obtain ⟨_, g0, hf, hc0⟩ := steps_has_sel n (hv.mono (by omega))
    have hmem := List.mem_of_find?_eq_some hf
    have hkv' : ((S n).id, g0) = kv := eq_of_nodup_keys hnd hmem hkv hid
    have hc : Carried kv.2 S := by rw [← hkv']; exact hc0
    have hok : StateOk ((n : Int) + 1) (S n).id kv.2 := by rw [hid]; exact ho
    have := carried_arrival (by omega) hv hok hc
    rw [hd] at this
    exact this
  | node h₁ h₂ ih₁ ih₂ =>
    unfold doJoin at hSn ⊢
    split
    · rename_i hok
      rw [if_pos hok] at hSn
      rcases (alive_join _ _ _).mp hSn with ha | ha
      · exact carried_join_left (ih₁ ha)
      · have hok' := hok
        unfold okJoin at hok'
        simp only [Bool.and_eq_true, beq_iff_eq] at hok'
        exact carried_join_right hok'.1.1.1 (ih₂ ha)
    · rename_i hok
      rw [if_neg hok] at hSn
      exact ih₁ hSn

/-- **`CliqueSplit` para árboles**: en el `doJoin` de dos árboles a `d`, toda camarilla es de uno de los dos. -/
theorem cliqueSplitTree (hbd : Bounded φ) {n : Nat} {d : NodeId} {e g : GPathB} (he : ArrTree φ n d e)
    (hg : ArrTree φ n d g) {S : Int → PathNodeId} (hS : Carried (doJoin e g) S) : Carried e S ∨ Carried g S := by
  by_cases hok : okJoin e g = true
  · have hj : doJoin e g = join e g := by unfold doJoin; rw [if_pos hok]
    rw [hj] at hS
    obtain ⟨o₁, s₁, m₁, t₁⟩ := tree_facts hbd he
    obtain ⟨o₂, s₂, m₂, t₂⟩ := tree_facts hbd hg
    have hcs : (join e g).current_step = (n : Int) + 1 + 1 := o₁.step
    have hv := validSel_of_carried hbd (Struct.struct_join s₁ s₂) (mapLinks_join m₁ m₂) hS (by omega)
    rw [hcs, show (n : Int) + 1 + 1 - 1 = (n : Int) + 1 by omega] at hv
    have htd : TopDocsId (join e g) d := topDocsId_join t₁ t₂ (o₁.step.trans o₂.step.symm)
    have htopd : (S ((n : Int) + 1)).id = d := by
      obtain ⟨m, hm, _, _⟩ := hS.node ((n : Int) + 1) (by omega) (by rw [hcs]; omega)
      have := htd m (node?_mem hm) (by rw [node?_id hm, hv.step _ (by omega) (Int.le_refl _), hcs]; omega)
      rw [node?_id hm] at this; exact this
    have hSn : S n ∈ (join e g).alive := hS.alive n (by omega) (by rw [hcs]; omega)
    rcases (alive_join _ _ _).mp hSn with ha | ha
    · exact Or.inl (tree_carried hbd he hv htopd ha)
    · exact Or.inr (tree_carried hbd hg hv htopd ha)
  · have hj : doJoin e g = e := by unfold doJoin; rw [if_neg hok]
    rw [hj] at hS
    exact Or.inl hS

end CliqueSplit

end AbsSatBingo.Model
