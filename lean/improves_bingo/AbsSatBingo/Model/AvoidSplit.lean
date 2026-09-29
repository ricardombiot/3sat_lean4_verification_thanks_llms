-- lean/improves_bingo/AbsSatBingo/Model/AvoidSplit.lean
import AbsSatBingo.Model.SepLine

/-!
# `AvoidSat` como reparto de dos pins en un solo estado

Con una ventana saltada, la llegada a `d` (el `L3` de una cláusula, índice 0) no puede alargar las camarillas cuya
cima (en `L2`) es `(L2, 0)` con padre `(L1, 0)`: su hijo sería la ventana prohibida `(0, 0, 0)`. `AvoidSat` pide una
camarilla con cima buena. Como el estado `f` cumple `SecExact`, basta un pin que **fuerce** la cima buena:

* fijar `(L2, 1)`: la cima de la camarilla es `(L2, 1)`;
* fijar `(L1, 1)`: el padre de la cima es `(L1, 1)` (los enlaces son compatibles, `LinksInv`).

> **`AvoidSplit f d`**: una estructura cerrada no vacía de `f` que concuerda con `P` y tiene las cimas buenas deja
> alguna al fijar además `(L2, 1)` o `(L1, 1)`.

**`avoidSat_of_split`**: `SecExact f` + `AvoidSplit f d` ⟹ `AvoidSat f d`. Así las tres hipótesis que quedan son
repartos de existencia entre dos pins: `SplitSat2` (los dos colores del remitente, en la unión), `AvoidSplit` (los dos
índices 1 de la ventana, en un estado) y `SideSat`. Veredicto: **`readerVerdict_iff_of_splits`**.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (shiftPid)

namespace GPathB

/-- **El reparto de la ventana**: fijar `(L2, 1)` o `(L1, 1)` deja una estructura. `L2` es el paso de la cima. -/
def AvoidSplit (φ : Cnf) (f : GPathB) (d : NodeId) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct f V R → (∀ b ∈ P, SecAgrees V b) → GoodTops f d (isProhibited φ) V → (∃ y, V y) →
    (∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct f W R' ∧
        (∀ c ∈ P ++ [⟨f.current_step - 1, 1⟩], SecAgrees W c) ∧ ∃ y, W y) ∨
    (∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct f W R' ∧
        (∀ c ∈ P ++ [⟨f.current_step - 2, 1⟩], SecAgrees W c) ∧ ∃ y, W y)

/-- Con una ventana saltada, el paso de la llegada es un `L3`: hay al menos dos pasos debajo. -/
theorem two_le_of_skips {φ : Cnf} {f : GPathB} {d : NodeId} (hsk : f.skipsWindow d (isProhibited φ) = true) :
    2 ≤ d.step := by
  unfold skipsWindow at hsk
  obtain ⟨pid, hmem, hf⟩ := List.any_eq_true.mp hsk
  have hid := Machine.mapId_of_mem_shiftRowIds hmem
  have hl3 : isL3 φ pid.id.step = true := by
    simp only [isProhibited, Bool.and_eq_true] at hf; exact hf.1.1.1
  simp only [isL3, midFusion, Bool.and_eq_true, decide_eq_true_eq] at hl3
  rw [hid] at hl3
  have h1 := of_decide_eq_true hl3.1.1
  omega

/-- **`SecExact` + el reparto de la ventana ⟹ `AvoidSat`.** -/
theorem avoidSat_of_split {φ : Cnf} {f : GPathB} {d : NodeId} (hse : SecExact f) (hli : LinksInv f)
    (hcs : 2 ≤ f.current_step) (hsp : AvoidSplit φ f d) : AvoidSat f d (isProhibited φ) := by
  intro P V R hst ha hgood hne
  rcases hsp P V R hst ha hgood hne with ⟨W, R', h1, h2, h3⟩ | ⟨W, R', h1, h2, h3⟩
  · -- la cima es (L2, 1)
    obtain ⟨S, hS, hag⟩ := hse _ W R' h1 h2 h3
    have htop : (S (f.current_step - 1)).id = ⟨f.current_step - 1, 1⟩ :=
      hag _ (List.mem_append_right _ (List.mem_singleton_self _)) (by show (0 : Int) ≤ f.current_step - 1; omega)
        (by show f.current_step - 1 < f.current_step; omega)
    refine ⟨S, hS, fun r hr => hag r (List.mem_append_left _ hr), ?_⟩
    simp [isProhibited, shiftPid, htop]
  · -- el padre de la cima es (L1, 1)
    obtain ⟨S, hS, hag⟩ := hse _ W R' h1 h2 h3
    have hpar : (S (f.current_step - 2)).id = ⟨f.current_step - 2, 1⟩ :=
      hag _ (List.mem_append_right _ (List.mem_singleton_self _)) (by show (0 : Int) ≤ f.current_step - 2; omega)
        (by show f.current_step - 2 < f.current_step; omega)
    obtain ⟨n, hn, hp, _⟩ := hS.node (f.current_step - 1) (by omega) (by omega)
    have hpm : S (f.current_step - 1 - 1) ∈ n.parents := hp (by omega)
    have hcomp := (hli.2.2 n (node?_mem hn)).1 _ hpm
    rw [node?_id hn, show f.current_step - 1 - 1 = f.current_step - 2 by omega] at hcomp
    have htp : (S (f.current_step - 1)).parent_id = some ⟨f.current_step - 2, 1⟩ := by
      rw [hcomp.1, hpar]
    refine ⟨S, hS, fun r hr => hag r (List.mem_append_left _ hr), ?_⟩
    simp [isProhibited, shiftPid, htp]

end GPathB

namespace SecLine

open GPathB Driver Machine Final

/-- **Las hipótesis como repartos**: `SplitSat2` en los joins, `SideSat` en los joins separados, `AvoidSplit` en las
ventanas saltadas. -/
structure HypsSplits (φ : Cnf) : Prop where
  split : ∀ T key e g a s, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → Key (T - 2) a →
            Key (T - 2) s → a ≠ s → OriginIn e (T - 2) (· = a) → OriginIn g (T - 2) (· = s) →
            SplitSat2 (join e g) a s
  side  : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → SepAt e g (T - 2) →
            SideSat (join e g) e g (T - 2)
  avoid : ∀ T key g d, StateOk T key g → SInv g → 1 ≤ T → d ∈ sonsOfMap φ key →
            (g.filterAll (reqOf φ d)).isValid = true →
            (g.filterAll (reqOf φ d)).skipsWindow d (isProhibited φ) = true →
            AvoidSplit φ (g.filterAll (reqOf φ d)) d

theorem hypsTwo_of_splits {φ : Cnf} (H : HypsSplits φ) : HypsTwo φ := by
  refine ⟨H.split, H.side, fun T key g d hg hk hT hd hv hsk => ?_⟩
  have hs := shrinks_filterAll g (reqOf φ d)
  have hstep : (g.filterAll (reqOf φ d)).current_step = T := hs.1.step.trans hg.step
  have hdstep : d.step = T := by rw [sonsOfMap_step φ key d hd, hg.key]; omega
  have h2 := two_le_of_skips hsk
  exact avoidSat_of_split (secExact_filterAll hk.1 hg.docs hk.2.1 _)
    (revPrims_filterAll revPrims_linksInv _ _ hk.2.2.2.2.2.2) (by omega) (H.avoid T key g d hg hk hT hd hv hsk)

/-- **El veredicto del lector es la satisfacibilidad bajo los tres repartos.** -/
theorem readerVerdict_iff_of_splits {φ : Cnf} (hbd : Bounded φ) (H : HypsSplits φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_two hbd (hypsTwo_of_splits H)

end SecLine

end AbsSatBingo.Model
