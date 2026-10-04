-- lean/improves_bingo/AbsSatBingo/Model/JoinStar.lean
import AbsSatBingo.Model.RowAgree

/-!
# El paso de la unión como única hipótesis (JoinStarCore)

**`TopStarR`**: una cima del núcleo fijado en `Q` está en una estructura cerrada que concuerda con `Q` y en la que la
cima está relacionada con todos sus nodos (el núcleo de su estrella, con enlaces: lo que mide `probe_starcore.jl`,
donde el núcleo por parejas conserva todas las aristas `t–y` y cumple los enlaces). A diferencia de «el núcleo por
parejas máximo cumple los enlaces» (`StarCoreH`), es monótona por coberturas.

Por estado, `TopStarR` sale de `TopExact` (`topStarR_of_topExact`: la camarilla de la cima), y `TopExact` lo conservan
el pin (`topExact_filterAll`, por `kernel_pin_list_iff`), el review (un pin vacío), el UP (`topExact_addNode`) y el caso
base, sin hipótesis: **`topExact_arrival`**. El único contenido es la unión: **`JoinStarCore`**, `TopStarR` en cada
llegada (los lados) ⇒ `TopStarR` en la unión de la línea siguiente (fijada en cualquier `Q`; el núcleo de la familia
no cambia con el review).

**`readerVerdict_iff_of_joinStarCore`**: el veredicto del lector es la satisfacibilidad bajo `JoinStarCore`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Driver Machine

/-- **`TopStarR`**: la cima está en una estructura cerrada que concuerda con `Q` y la relaciona con todos sus nodos. -/
def TopStarR (F : GPathB → Prop) (c : Int) : Prop :=
  ∀ (Q : List NodeId) (t : PathNodeId), t.id.step = c - 1 → FamKernel F c Q t t →
    ∃ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), FamStruct F c V R ∧ (∀ b ∈ Q, SecAgrees V b) ∧
      V t ∧ ∀ y, V y → R t y

theorem topStarF_of_topStarR {F : GPathB → Prop} {c : Int} (h : TopStarR F c) : TopStarF F c := by
  intro Q t hts hk
  obtain ⟨V, R, hst, ha, hvt, hr⟩ := h Q t hts hk
  exact ⟨V, R, hst, ha, hvt, fun y hy => hst.adj (hr y hy)⟩

/-- **Por estado, `TopStarR` sale de `TopExact`**: la camarilla de la cima la relaciona con todos sus nodos. -/
theorem topStarR_of_topExact {g : GPathB} (hk : TopExact g) : TopStarR (· = g) g.current_step := by
  intro Q t hts hker
  obtain ⟨S, hc, ha, ht⟩ := hk Q t hts (kernel_of_famKernel hker)
  exact ⟨_, _, famStruct_of_secStruct (F := (· = g)) rfl (secStruct_of_carried hc), fun r hr => secAgrees_of_agrees hc (ha r hr),
    ht, fun y hy => ⟨ht, hy⟩⟩

/-- **Una llegada conserva `TopExact`** sin hipótesis: pin (`rq d`), fila nueva y review (un pin vacío). -/
theorem topExact_arrival {rq : NodeId → List NodeId} {title : String} {forb : PathNodeId → Bool} {T : Int}
    (hT : 1 ≤ T) {kv : NodeId × GPathB} (hok : SenderOk T kv) {d : NodeId} (hd : d.step = T) :
    TopExact (arrival rq title forb kv d) := by
  let f := kv.2.filterAll (rq d)
  have hfs : f.current_step = T := (shrinks_filterAll _ _).1.step.trans hok.step
  have hb : Below f := below_of_shrinks (shrinks_filterAll _ _) hok.below
  have hdo : AliveDocs f := aliveDocs_filterAll hok.docs _
  have htf : TopExact f := topExact_filterAll hok.top hok.docs hok.nd _
  have hta : TopExact (f.addNode d title forb) :=
    topExact_addNode htf hdo hb (revPrims_filterAll revPrims_linksStep _ _ hok.links) (by omega) (by omega)
  have hnd : NodupIds (f.addNode d title forb) :=
    nodupIds_addNode (revPrims_filterAll revPrims_nodupIds _ _ hok.nd) hb (by omega)
  show TopExact (f.addNode d title forb).review
  rw [FinalTop.review_eq_filterAll]
  exact topExact_filterAll hta (aliveDocs_addNode hdo) hnd []

/-- **`JoinStarCore`, la única hipótesis**: en cada paso, si cada llegada (cada lado) cumple `TopStarR`, la unión de la
línea siguiente la cumple, fijada en cualquier `Q`. -/
def JoinStarCore (φ : Cnf) : Prop :=
  ∀ n : Nat,
    (∀ a, Arrivals (reqOf φ) "" (isProhibited φ) (· ∈ steps φ n (init φ)) (SonT φ ((n : Int) + 1)) a →
      TopStarR (· = a) ((n : Int) + 2)) →
    TopStarR (famOf (· ∈ steps φ (n + 1) (init φ))) ((n : Int) + 2)

/-- **El paso**: con el invariante de una línea, `JoinStarCore` da `PinFreeF` en la siguiente. -/
theorem pinFree_next {φ : Cnf} (hbd : Bounded φ) (H : JoinStarCore φ) (n : Nat)
    (hinv : LineInv ((n : Int) + 1) (steps φ n (init φ))) :
    PinFreeF (reqOf φ) (· ∈ steps φ (n + 1) (init φ)) ((n : Int) + 2) := by
  obtain ⟨hl, hent, _, _⟩ := hinv
  have hsnd : ∀ kv, kv ∈ steps φ n (init φ) → SenderOk ((n : Int) + 1) kv := by
    intro kv hkv
    obtain ⟨⟨hbk, htid⟩, htop⟩ := hent kv hkv
    exact ⟨(hl kv hkv).docs, hbk.1, (hl kv hkv).below, hbk.2.2.1, htop, (hl kv hkv).step, htid⟩
  have harr : ∀ a, Arrivals (reqOf φ) "" (isProhibited φ) (· ∈ steps φ n (init φ)) (SonT φ ((n : Int) + 1)) a →
      TopStarR (· = a) ((n : Int) + 2) := by
    rintro a ⟨kv, d, hkv, ⟨hd, hk⟩, _, rfl⟩
    have hds : d.step = (n : Int) + 1 := by rw [sonsOfMap_step φ kv.1 d hd, hk]; omega
    have hte := topExact_arrival (rq := reqOf φ) (title := "") (forb := isProhibited φ) (by omega) (hsnd kv hkv) hds
    have hcs : (arrival (reqOf φ) "" (isProhibited φ) kv d).current_step = (n : Int) + 2 := by
      unfold arrival
      rw [(shrinks_review _).1.step]
      show (kv.2.filterAll (reqOf φ d)).current_step + 1 = _
      rw [(shrinks_filterAll _ _).1.step, (hl kv hkv).step]; omega
    rw [← hcs]; exact topStarR_of_topExact hte
  obtain ⟨hl', he'⟩ := lineOk_entOk_steps φ (n + 1)
  have hr : ∀ kv ∈ steps φ (n + 1) (init φ), RowAgree (reqOf φ) kv := by
    rw [steps_succ]; exact advance_rowAgree hbd hl
  have hc : ((n + 1 : Nat) : Int) + 1 = (n : Int) + 2 := by push_cast; omega
  rw [hc] at hl'
  exact pinFreeF_of_topStarF (topStarF_of_topStarR (H n harr)) (rowOwn_line hl' he' hr)

theorem lineInv_steps_join {φ : Cnf} (hbd : Bounded φ) (H : JoinStarCore φ) :
    ∀ n : Nat, LineInv ((n : Int) + 1) (steps φ n (init φ)) := by
  intro n
  induction n with
  | zero => exact lineInv_init φ
  | succ n ih =>
    have hpf := pinFree_next hbd H n ih
    rw [steps_succ] at hpf ⊢
    have := lineInv_advance (φ := φ) (by omega) ih (by rw [show (n : Int) + 1 + 1 = (n : Int) + 2 by omega]; exact hpf)
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

theorem hypsPin_of_joinStarCore {φ : Cnf} (hbd : Bounded φ) (H : JoinStarCore φ) : HypsPin φ :=
  fun n => pinFree_next hbd H n (lineInv_steps_join hbd H n)

/-- **El veredicto del lector es la satisfacibilidad bajo `JoinStarCore` como única hipótesis.** -/
theorem readerVerdict_iff_of_joinStarCore {φ : Cnf} (hbd : Bounded φ) (H : JoinStarCore φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_pinFree hbd (hypsPin_of_joinStarCore hbd H)

end GPathB

end AbsSatBingo.Model
