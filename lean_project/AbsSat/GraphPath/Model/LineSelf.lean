-- lean_project/AbsSat/GraphPath/Model/LineSelf.lean
import AbsSat.GraphPath.Model.ReaderLadder

/-!
# La autoposesión de la línea final

Todo nodo de un estado de la línea final se posee a sí mismo. Es un invariante de la construcción:

* la semilla nace con `owners = [id]`;
* el `up` añade la fila con `rowOwners = … ++ [pid]` y a los nodos viejos solo les **añade**
  owners (`upOwners`);
* la unión conserva los owners del primer lado (`mergeNode`) y copia los nodos del segundo;
* y el estado sobre el que se hace el `up` es un review válido, donde la autoposesión ya estaba
  demostrada (`ReaderLadder.selfOwned_of_readable`).

Con ella, la hipótesis de la construcción de `ReaderLadder.readerVerdictW_iff_of_machine` se queda
en `FullExtG` de la línea final, sin nada más.
-/

namespace AbsSat.GraphPath.Model.LineSelf

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun

variable (φ : Cnf)

/-- **Cada nodo se posee a sí mismo**, dicho sobre la lista de nodos (sin `node?`). -/
def SelfMem (g : GPathM) : Prop := ∀ n ∈ g.nodes, n.id ∈ n.owners

theorem selfOwned_of_selfMem (g : GPathM) (h : SelfMem g) : Ownership.SelfOwned g := by
  intro pid n hn
  rw [← node?_id_eq g pid n hn]
  exact h n (List.mem_of_find?_eq_some hn)

theorem selfMem_of_selfOwned (g : GPathM) (hnd : NodupIds g) (h : Ownership.SelfOwned g) :
    SelfMem g :=
  fun n hn => h n.id n (node?_of_mem hnd n hn)

/-- El `up` solo añade owners a los viejos, y la fila nueva se posee por construcción. -/
theorem selfMem_addNode (F : GPathM) (d : NodeId) (title : String) (h : SelfMem F) :
    SelfMem (addNode F d title) := by
  intro n hn
  rcases ParentOwners.mem_addNode_nodes hn with ⟨m, hm, rfl⟩ | ⟨pid, _, rfl⟩
  · rw [upMap_id, upMap_owners]
    exact List.mem_append_left _ (h m hm)
  · rw [rowNode_id, rowNode_owners]
    simp only [rowOwners]
    exact List.mem_append_right _ (List.mem_singleton_self _)

/-- La unión conserva los owners del primer lado y copia los nodos del segundo. -/
theorem selfMem_join (g₁ g₂ : GPathM) (h₁ : SelfMem g₁) (h₂ : SelfMem g₂) :
    SelfMem (join g₁ g₂) := by
  intro n hn
  have hj : (join g₁ g₂).nodes =
      g₁.nodes.map (fun n => match g₂.node? n.id with | some m => mergeNode n m | none => n) ++
        g₂.nodes.filter (fun m => (g₁.node? m.id).isNone) := rfl
  rw [hj] at hn
  rcases List.mem_append.mp hn with hl | hr
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
    cases hm : g₂.node? a.id with
    | none => simp only; exact h₁ a ha
    | some m =>
      simp only [mergeNode]
      exact List.mem_append_left _ (h₁ a ha)
  · exact h₂ n (List.mem_filter.mp hr).1

theorem selfMem_initSeed (d : NodeId) : SelfMem (GPathM.initSeed d "") := by
  intro n hn
  rw [initSeed_nodes] at hn
  rw [List.mem_singleton.mp hn]
  exact List.mem_singleton_self _

/-- **Un estado enviado se posee a sí mismo**: el `up` se hace sobre un review válido. -/
theorem selfMem_sent (kv : NodeId × GPathM) (hm : MInv φ kv.2) (d : NodeId)
    (hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true) :
    SelfMem (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") := by
  let F := filterAllAgg (filterWeakAll kv.2 (weakReqOfCnf φ d)) (reqOfCnf φ d)
  have hRF : ReadableAgg F :=
    ⟨filterWeakAll kv.2 (weakReqOfCnf φ d), reqOfCnf φ d,
      RCtx_of_keeps (keeps_filterWeakAll _ _) hm.rctx, rfl⟩
  cases hvF : isValid F with
  | false =>
    exfalso
    have he : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" = F := by
      simp only [upFilteringWeak, GPathM.up, F] at hvF ⊢
      rw [if_neg (by rw [hvF]; exact Bool.false_ne_true)]
    rw [he, hvF] at hval
    exact Bool.false_ne_true hval
  | true =>
    have heq : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" = addNode F d "" := by
      simp only [upFilteringWeak, GPathM.up, F] at hvF ⊢
      rw [if_pos hvF]
    rw [heq]
    exact selfMem_addNode F d "" (selfMem_of_selfOwned F (RCtx_of_readableAgg F hRF).nodup
      (ReaderLadder.selfOwned_of_readable F hRF hvF))

theorem selfMem_insertPure (line : PureLine) (key : NodeId) (g : GPathM)
    (hl : ∀ kv ∈ line, SelfMem kv.2) (hg : SelfMem g) :
    ∀ kv ∈ insertPure line key g, SelfMem kv.2 := by
  intro kv hkv
  unfold insertPure at hkv
  cases hf : line.find? (fun x => x.1 == key) with
  | none =>
    simp only [hf] at hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton.mp h]; exact hg
  | some e =>
    simp only [hf] at hkv
    obtain ⟨x, hx, hEq⟩ := List.mem_map.mp hkv
    cases hb : x.1 == key with
    | true =>
      have hx2 : kv = (key, doJoin e.2 g) := by rw [← hEq]; simp only [hb]; rfl
      rw [hx2]
      show SelfMem (doJoin e.2 g)
      unfold doJoin
      split
      · exact selfMem_join _ _ (hl e (List.mem_of_find?_eq_some hf)) hg
      · exact hl e (List.mem_of_find?_eq_some hf)
    | false =>
      have hx2 : kv = x := by rw [← hEq]; simp only [hb]; rfl
      rw [hx2]; exact hl x hx

theorem selfMem_sendToW (kv : NodeId × GPathM) (hm : MInv φ kv.2) (next : PureLine)
    (hn : ∀ x ∈ next, SelfMem x.2) (d : NodeId) : ∀ x ∈ sendToW φ kv.2 next d, SelfMem x.2 := by
  simp only [sendToW]
  split
  · next hval => exact selfMem_insertPure next d _ hn (selfMem_sent φ kv hm d hval)
  · exact hn

/-- **Una línea nueva sale solo de envíos**, así que basta `MInv` de la anterior. -/
theorem selfMem_pureAdvanceW (line : PureLine) (hm : ∀ kv ∈ line, MInv φ kv.2) :
    ∀ kv ∈ pureAdvanceW φ line, SelfMem kv.2 := by
  simp only [pureAdvanceW]
  have hsend : ∀ kv : NodeId × GPathM, MInv φ kv.2 → ∀ acc : PureLine,
      (∀ x ∈ acc, SelfMem x.2) → ∀ x ∈ sendAllW φ kv acc, SelfMem x.2 := by
    intro kv hmk acc hacc
    simp only [sendAllW]
    have main : ∀ (l : List NodeId) (acc : PureLine), (∀ x ∈ acc, SelfMem x.2) →
        ∀ x ∈ l.foldl (sendToW φ kv.2) acc, SelfMem x.2 := by
      intro l
      induction l with
      | nil => intro acc h; exact h
      | cons y ys ih =>
        intro acc h
        simp only [List.foldl_cons]
        exact ih _ (selfMem_sendToW φ kv hmk acc h y)
    exact main _ acc hacc
  have main : ∀ (l : PureLine), (∀ kv ∈ l, MInv φ kv.2) → ∀ acc : PureLine,
      (∀ x ∈ acc, SelfMem x.2) →
        ∀ x ∈ l.foldl (fun next kv => sendAllW φ kv next) acc, SelfMem x.2 := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons y ys ih =>
      intro hy acc h
      simp only [List.foldl_cons]
      exact ih (fun kv hkv => hy kv (List.mem_cons_of_mem _ hkv)) _
        (hsend y (hy y List.mem_cons_self) acc h)
  exact main line hm [] (fun x hx => absurd hx List.not_mem_nil)

theorem selfMem_init : ∀ kv ∈ pureInit φ, SelfMem kv.2 := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId) (acc : PureLine), (∀ x ∈ acc, SelfMem x.2) →
      ∀ x ∈ l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc,
        SelfMem x.2 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons y ys ih =>
      intro acc h
      simp only [List.foldl_cons]
      exact ih _ (selfMem_insertPure acc y _ h (selfMem_initSeed y))
  exact main _ [] (fun x hx => absurd hx List.not_mem_nil)

theorem selfMem_steps (hwf : WF φ) :
    ∀ (n : Nat) (k : Int) (line : PureLine), LineInv φ k line →
      (∀ kv ∈ line, SelfMem kv.2) → ∀ kv ∈ pureStepsW φ n line, SelfMem kv.2 := by
  intro n
  induction n with
  | zero => intro _ _ _ hs; exact hs
  | succ m ih =>
    intro k line hl _
    exact ih (k + 1) _ (LineInv_pureAdvanceW φ hwf k line hl) (selfMem_pureAdvanceW φ line hl.2)

/-- **Todo estado de la línea final se posee a sí mismo.** -/
theorem pureRunW_selfOwned (hwf : WF φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) :
    Ownership.SelfOwned kv.2 :=
  selfOwned_of_selfMem _ (selfMem_steps φ hwf _ 0 (pureInit φ) (LineInv_init φ hwf)
    (selfMem_init φ) kv hkv)

/-- info: 'AbsSat.GraphPath.Model.LineSelf.pureRunW_selfOwned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pureRunW_selfOwned

-- ============================================================
-- La escalera, con la construcción reducida a FullExtG
-- ============================================================

/-- **Lo que la construcción debe dar**, ya sin la autoposesión. -/
def LineFullExtG : Prop :=
  ∀ ψ : Cnf, WF ψ → ∀ kv ∈ pureRunW ψ, FullExt.FullExtG kv.2

theorem lineFullExt_of_lineFullExtG (h : LineFullExtG) : ReaderLadder.LineFullExt :=
  fun ψ hwf kv hkv => ⟨h ψ hwf kv hkv, pureRunW_selfOwned ψ hwf kv hkv⟩

/-- **El lector sin retroceso decide 3-SAT** con dos hipótesis: la línea final cumple `FullExtG`, y
el review tras un pin es completo. -/
theorem readerVerdictW_iff_of_lineFullExtG (hL : LineFullExtG) (hP : ReaderLadder.PinComplete)
    (hwf : WF φ) : ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  ReaderLadder.readerVerdictW_iff_of_machine (lineFullExt_of_lineFullExtG hL) hP φ hwf

/-- info: 'AbsSat.GraphPath.Model.LineSelf.readerVerdictW_iff_of_lineFullExtG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_lineFullExtG

end AbsSat.GraphPath.Model.LineSelf
