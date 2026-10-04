-- lean_project/AbsSat/GraphPath/Model/LineExt.lean
import AbsSat.GraphPath.Model.LineSelf

/-!
# `FullExtG` a lo largo de la línea

La inducción de la construcción, con la misma forma que `ReaderAggRun.LineInv`:

* la **semilla** cumple `FullExtG` (un solo paso: el tramo ya es la cadena);
* el **envío** es `up (reviewAgg (duros (débil g)))`: el review lo lleva la completitud tras los dos
  filtros (`SendComplete`) y el `up` lo lleva `FullExt.fullExtG_addNode`, sin hipótesis;
* la **unión** es la otra hipótesis con nombre (`JoinFullExt`), la del `NoMix`.

Con ellas, la construcción da `LineSelf.LineFullExtG`.
-/

namespace AbsSat.GraphPath.Model.LineExt

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF Fsac prunes_Fsac StateOkF_sent
  stateOkF_initSeed okJoin_of_stateOkF)
open AbsSat.GraphPath.Model.FullExt (FullExtG fullExtG_addNode)
open AbsSat.GraphPath.Model.ReaderLadder (ReviewCompleteCS fullExtG_reviewAgg_cs
  nodupIds_foldl_filterRequire)

variable (φ : Cnf)

/-- **La unión conserva `FullExtG`.** Abierta: es el `NoMix` (una cadena de la unión no mezcla los
dos lados). -/
def JoinFullExt : Prop :=
  ∀ g₁ g₂ : GPathM, okJoin g₁ g₂ = true → MInv φ g₁ → MInv φ g₂ →
    FullExtG g₁ → FullExtG g₂ → FullExtG (join g₁ g₂)

/-- **El review tras los filtros de un envío es completo**, si el estado que envía cumple
`FullExtG`. Abierta en el filtro débil; sin él la da el argumento de la cima
(`ReaderLadder.reviewCompleteCS_of_hardReqs`). -/
def SendComplete : Prop :=
  ∀ (k : Int) (kv : NodeId × GPathM), StateOkF φ k kv → MInv φ kv.2 → FullExtG kv.2 →
    ∀ d ∈ mapSons φ kv.1.step kv.1.index,
      isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true →
      ReviewCompleteCS ((reqOfCnf φ d).foldl filterRequire (filterWeakAll kv.2 (weakReqOfCnf φ d)))

/-- **La semilla**: un solo paso, y el tramo ya es la cadena. -/
theorem fullExtG_initSeed (d : NodeId) : FullExtG (GPathM.initSeed d "") := by
  intro sel lo hi hlo0 hlohi hhi hs hsg
  have hc : (GPathM.initSeed d "").current_step - 1 = 0 := by rw [initSeed_current]; rfl
  rw [hc] at hhi ⊢
  have hlo : lo = 0 := by omega
  have hhi' : hi = 0 := by omega
  subst hlo
  subst hhi'
  exact ⟨sel, hs, hsg, fun _ _ _ => rfl⟩

/-- **El envío**: el review por la completitud, el `up` sin hipótesis. -/
theorem fullExtG_sent (hS : SendComplete φ) (k : Int) (hk0 : 0 ≤ k) (kv : NodeId × GPathM)
    (hkv : StateOkF φ k kv) (hm : MInv φ kv.2) (hF : FullExtG kv.2) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hval : isValid (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") = true) :
    FullExtG (upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "") := by
  have hsok := StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv hkv d hd hval
  have hdstep : d.step = k + 1 := mapNodes_step φ (k + 1) d hsok.onMap
  let W := filterWeakAll kv.2 (weakReqOfCnf φ d)
  let F := filterAllAgg W (reqOfCnf φ d)
  have hk : Keeps kv.2 F := Keeps.trans (keeps_filterWeakAll _ _) (keeps_filterAllAgg _ _)
  have hcW := RCtx_of_keeps (keeps_filterWeakAll kv.2 (weakReqOfCnf φ d)) hm.rctx
  have hRF : ReadableAgg F := ⟨W, reqOfCnf φ d, hcW, rfl⟩
  have rcF := RCtx_of_readableAgg F hRF
  have hvF : isValid F = true := by
    cases h : isValid F with
    | true => rfl
    | false =>
      exfalso
      have he : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" = F := by
        simp only [upFilteringWeak, GPathM.up, F, W] at h ⊢
        rw [if_neg (by rw [h]; exact Bool.false_ne_true)]
      rw [he, h] at hval
      exact Bool.false_ne_true hval
  have heq : upFilteringWeak kv.2 (weakReqOfCnf φ d) (reqOfCnf φ d) d "" = addNode F d "" := by
    simp only [upFilteringWeak, GPathM.up, F, W] at hvF ⊢
    rw [if_pos hvF]
  rw [heq]
  have hFF : FullExtG F :=
    fullExtG_reviewAgg_cs _ (nodupIds_foldl_filterRequire _ W hcW.nodup)
      (hS k kv hkv hm hF d hd hval)
  have ctxF := Reader.Ctx_of_readable F (readable_of_readableAgg F hRF) hvF
  have hstepF : F.current_step = k + 1 := by rw [hk.1.step_eq, hkv.step]
  exact fullExtG_addNode F d "" (by rw [hstepF, hdstep]) (by rw [hstepF]; omega) rcF.below
    ctxF.ownGow ctxF.self hFF

/-- La línea con `FullExtG` en cada estado. -/
def LineExtInv (k : Int) (line : PureLine) : Prop :=
  LineInv φ k line ∧ ∀ kv ∈ line, FullExtG kv.2

theorem lineExtInv_insertPure (hJ : JoinFullExt φ) (k : Int) (line : PureLine) (key : NodeId)
    (g : GPathM) (hl : LineExtInv φ k line) (hg : StateOkF φ k (key, g)) (hm : MInv φ g)
    (hgF : FullExtG g) : LineExtInv φ k (insertPure line key g) := by
  refine ⟨LineInv_insertPure φ k line key g hl.1 hg hm, ?_⟩
  intro kv hkv
  unfold insertPure at hkv
  cases hf : line.find? (fun x => x.1 == key) with
  | none =>
    simp only [hf] at hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl.2 kv h
    · rw [List.mem_singleton.mp h]; exact hgF
  | some e =>
    simp only [hf] at hkv
    obtain ⟨x, hx, hEq⟩ := List.mem_map.mp hkv
    cases hb : x.1 == key with
    | true =>
      have hx2 : kv = (key, doJoin e.2 g) := by rw [← hEq]; simp only [hb]; rfl
      rw [hx2]
      have hekey : e.1 = key :=
        eq_of_beq (List.find?_some (p := fun x : NodeId × GPathM => x.1 == key) hf)
      have hemem : e ∈ line := List.mem_of_find?_eq_some hf
      have hesok : StateOkF φ k (key, e.2) := by
        have h := hl.1.1.2 e hemem
        rwa [← hekey]
      have hok := okJoin_of_stateOkF φ k key e.2 g hesok hg
      show FullExtG (doJoin e.2 g)
      simp only [doJoin, hok, if_pos]
      exact hJ e.2 g hok (hl.1.2 e hemem) hm (hl.2 e hemem) hgF
    | false =>
      have hx2 : kv = x := by rw [← hEq]; simp only [hb]; rfl
      rw [hx2]
      exact hl.2 x hx

theorem lineExtInv_sendToW (hwf : WF φ) (hJ : JoinFullExt φ) (hS : SendComplete φ) (k : Int)
    (hk0 : 0 ≤ k) (kv : NodeId × GPathM) (hkv : StateOkF φ k kv) (hm : MInv φ kv.2)
    (hF : FullExtG kv.2) (d : NodeId) (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (next : PureLine) (hn : LineExtInv φ (k + 1) next) :
    LineExtInv φ (k + 1) (sendToW φ kv.2 next d) := by
  simp only [sendToW]
  split
  · next hval =>
    exact lineExtInv_insertPure φ hJ (k + 1) next d _ hn
      (StateOkF_sent φ (Fsac φ 0) reviewAgg (prunes_Fsac φ 0) k kv hkv d hd hval)
      (MInv_sent φ hwf k kv hkv hm d hd hval) (fullExtG_sent φ hS k hk0 kv hkv hm hF d hd hval)
  · exact hn

theorem lineExtInv_pureAdvanceW (hwf : WF φ) (hJ : JoinFullExt φ) (hS : SendComplete φ)
    (k : Int) (hk0 : 0 ≤ k) (line : PureLine) (hl : LineExtInv φ k line) :
    LineExtInv φ (k + 1) (pureAdvanceW φ line) := by
  simp only [pureAdvanceW]
  have hsend : ∀ kv, StateOkF φ k kv → MInv φ kv.2 → FullExtG kv.2 → ∀ acc,
      LineExtInv φ (k + 1) acc → LineExtInv φ (k + 1) (sendAllW φ kv acc) := by
    intro kv hkv hm hF acc hacc
    simp only [sendAllW]
    have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapSons φ kv.1.step kv.1.index) →
        ∀ acc, LineExtInv φ (k + 1) acc →
          LineExtInv φ (k + 1) (l.foldl (sendToW φ kv.2) acc) := by
      intro l
      induction l with
      | nil => intro _ acc h; exact h
      | cons x xs ih =>
        intro hx acc h
        simp only [List.foldl_cons]
        exact ih (fun d hd => hx d (List.mem_cons_of_mem _ hd)) _
          (lineExtInv_sendToW φ hwf hJ hS k hk0 kv hkv hm hF x (hx x List.mem_cons_self) acc h)
    exact main _ (fun _ hd => hd) acc hacc
  have main : ∀ (l : PureLine), (∀ kv ∈ l, StateOkF φ k kv ∧ MInv φ kv.2 ∧ FullExtG kv.2) →
      ∀ acc, LineExtInv φ (k + 1) acc →
        LineExtInv φ (k + 1) (l.foldl (fun next kv => sendAllW φ kv next) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      have hx0 := hx x List.mem_cons_self
      exact ih (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) _
        (hsend x hx0.1 hx0.2.1 hx0.2.2 acc h)
  exact main line (fun kv hkv => ⟨hl.1.1.2 kv hkv, hl.1.2 kv hkv, hl.2 kv hkv⟩) []
    ⟨⟨⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem lineExtInv_init (hwf : WF φ) (hJ : JoinFullExt φ) : LineExtInv φ 0 (pureInit φ) := by
  simp only [pureInit]
  have main : ∀ (l : List NodeId), (∀ d ∈ l, d ∈ mapNodes φ 0) →
      ∀ acc, LineExtInv φ 0 acc →
        LineExtInv φ 0 (l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x xs ih =>
      intro hx acc h
      simp only [List.foldl_cons]
      have hx0 := hx x List.mem_cons_self
      exact ih (fun d hdm => hx d (List.mem_cons_of_mem _ hdm)) _
        (lineExtInv_insertPure φ hJ 0 acc x _ h (stateOkF_initSeed φ x hx0)
          (MInv_initSeed φ hwf x hx0) (fullExtG_initSeed x))
  exact main _ (fun _ hdm => hdm) []
    ⟨⟨⟨by simp, by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩,
      by intro kv hkv; exact absurd hkv List.not_mem_nil⟩

theorem lineExtInv_steps (hwf : WF φ) (hJ : JoinFullExt φ) (hS : SendComplete φ) :
    ∀ (n : Nat) (k : Int) (line : PureLine), 0 ≤ k → LineExtInv φ k line →
      ∀ kv ∈ pureStepsW φ n line, FullExtG kv.2 := by
  intro n
  induction n with
  | zero => intro _ _ _ hl; exact hl.2
  | succ m ih =>
    intro k line hk0 hl
    exact ih (k + 1) _ (by omega) (lineExtInv_pureAdvanceW φ hwf hJ hS k hk0 line hl)

/-- **La construcción da `FullExtG` en la línea final**, con la unión y el envío como hipótesis. -/
theorem lineFullExtG_of (hJ : ∀ ψ : Cnf, WF ψ → JoinFullExt ψ)
    (hS : ∀ ψ : Cnf, WF ψ → SendComplete ψ) : LineSelf.LineFullExtG :=
  fun ψ hwf kv hkv =>
    lineExtInv_steps ψ hwf (hJ ψ hwf) (hS ψ hwf) _ 0 (pureInit ψ) (Int.le_refl 0)
      (lineExtInv_init ψ hwf (hJ ψ hwf)) kv hkv

/-- **El lector sin retroceso decide 3-SAT** con tres hipótesis, cada una de una operación: la unión
(`JoinFullExt`), el review tras los filtros de un envío (`SendComplete`) y el review tras un pin del
lector (`ReaderLadder.PinComplete`). -/
theorem readerVerdictW_iff_of_ops (hJ : ∀ ψ : Cnf, WF ψ → JoinFullExt ψ)
    (hS : ∀ ψ : Cnf, WF ψ → SendComplete ψ) (hP : ReaderLadder.PinComplete) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ :=
  LineSelf.readerVerdictW_iff_of_lineFullExtG φ (lineFullExtG_of hJ hS) hP hwf

/-- info: 'AbsSat.GraphPath.Model.LineExt.readerVerdictW_iff_of_ops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_ops

end AbsSat.GraphPath.Model.LineExt
