-- lean/improves_bingo/AbsSatBingo/Model/ChainLine.lean
import AbsSatBingo.Model.ChainSide
import AbsSatBingo.Model.LineCtxL
import AbsSatBingo.Model.SpineVerdict

/-!
# `ChainInv` en toda la línea, sin B1

**`chainInv_run`**: todas las entradas finales de la máquina cumplen `ChainInv`, bajo
* **`SibStarInv`** en las entradas de la línea (StarInv solo para estructuras cuyas cimas son hermanos), y
* **`ArrHole`** + **`AbsHole`** (para `StarOneSide` en los joins).

El UP es `chainInv_up_sib`; el join, `chainInv_join_oneSide` (sin `StarJoinDown`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace SecLine

open GPathB Driver Machine CliqueSplit

variable {φ : Cnf}

/-- Las posesiones de un árbol de llegadas están entre vivos, y sus enlaces bien. -/
theorem tree_links (hbd : Bounded φ) {n : Nat} {d : NodeId} {e : GPathB} (h : ArrTree φ n d e) :
    LinksInv e ∧ EdgesAlive e := by
  obtain ⟨hl, hent, _, _, _⟩ := line_facts hbd n
  induction h with
  | leaf kv hkv hd hv =>
    have ho := hl kv hkv
    have hs := shrinks_filterAll kv.2 (reqOf φ d)
    have hcf : (kv.2.filterAll (reqOf φ d)).current_step = (n : Int) + 1 := hs.1.step.trans ho.step
    have hds : d.step = (kv.2.filterAll (reqOf φ d)).current_step := by
      rw [hcf, sonsOfMap_step φ kv.1 d hd, ho.key]; omega
    have hli := revPrims_filterAll revPrims_linksInv _ (reqOf φ d) (line_linksInv hbd n kv hkv)
    have hz := revPrims_filterAll revPrims_aboveZero _ (reqOf φ d) (hent kv hkv).1.2.2.2
    refine ⟨?_, edgesAlive_arr hbd hkv hv⟩
    rw [arr_eq hv]; show LinksInv (GPathB.filterAll _ [])
    exact revPrims_filterAll revPrims_linksInv _ _ (linksInv_addNode hli (below_of_shrinks hs ho.below) hz hds)
  | node _ _ ih₁ ih₂ =>
    unfold doJoin
    split
    · exact ⟨linksInv_join ih₁.1 ih₂.1 ih₁.2 ih₂.2, edgesAlive_join ih₁.2 ih₂.2⟩
    · exact ih₁

/-- **La hipótesis de hermanos**, en todas las entradas de la línea. -/
def HypSib (φ : Cnf) : Prop := ∀ n, ∀ kv ∈ steps φ n (init φ), SibStarInv kv.2

/-- **El UP conserva `ChainInv`**, con `SibStarInv` del remitente. -/
theorem upProvL_chain (hbd : Bounded φ) (HS : HypSib φ) : UpProvL φ ChainInv := by
  intro n kv d hkv hok hC hd hv
  obtain ⟨_, hent, _, _, _⟩ := line_facts hbd n
  have hs := shrinks_filterAll kv.2 (reqOf φ d)
  have hcf : (kv.2.filterAll (reqOf φ d)).current_step = (n : Int) + 1 := hs.1.step.trans hok.step
  have hds : d.step = (kv.2.filterAll (reqOf φ d)).current_step := by
    rw [hcf, sonsOfMap_step φ kv.1 d hd, hok.key]; omega
  have hbk := (hent kv hkv).1
  have hvf := valid_filter_of_arr (φ := φ) (kv := kv) (d := d) hv
  have h := chainInv_up_sib (title := "") (forb := isProhibited φ) hC (HS n kv hkv) hbk.1 hok.docs hvf
    (aliveDocs_filterAll hok.docs _) (below_of_shrinks hs hok.below)
    (revPrims_filterAll revPrims_linksStep _ _ hbk.2.2.1) (revPrims_filterAll revPrims_edgesAlive _ _ hbk.2.1)
    (revPrims_filterAll revPrims_nodupIds _ _ hbk.1)
    (revPrims_filterAll revPrims_topsApart _ _ (line_topsApart hbd n kv hkv)) hds (by omega)
  have heq := arr_eq (φ := φ) (kv := kv) (d := d) hv
  show ChainInv (arr φ kv d)
  rw [heq]; exact h

/-- **El join conserva `ChainInv`** con los huecos. -/
theorem joinProvT_chain (hbd : Bounded φ) (HR : ArrHole φ) (HA : AbsHole φ) {U : Int} (hU : 2 ≤ U) :
    JoinProvT φ ChainInv U := by
  intro key s e g A he hg hke hkg hoe _ hsA hAk hsk n hUn hIl htree kv hkv hks hkd hga
  have hn : U - 2 = (n : Int) := by omega
  rw [hn] at hoe hAk hsk
  unfold doJoin
  split
  · rename_i hok
    obtain ⟨kv₀, hkv₀, hd₀, hv₀, hk₀, hal₀, hadj₀⟩ := tree_single hbd htree hoe hsA hAk hsk
    have hne : kv₀.1 ≠ kv.1 := by rw [hk₀, hks]; exact other_ne hsk
    have hvg : (arr φ kv key).isValid = true := by rw [← hga]; exact hg.valid
    have hp₁ : SenderPair φ n kv₀ kv key := ⟨hkv₀, hkv, hne, hd₀, hkd, hv₀, hvg⟩
    have hp₂ : SenderPair φ n kv kv₀ key := ⟨hkv, hkv₀, hne.symm, hkd, hd₀, hvg, hv₀⟩
    have hcs : e.current_step = g.current_step := he.step.trans hg.step.symm
    have hje : (join e g).current_step = U := he.step
    have hcsX : (arr φ kv₀ key).current_step = U := by
      rw [(stateOk_upFiltering ((line_facts hbd n).1 kv₀ hkv₀) hd₀ hv₀).step]; omega
    have hcsG : (arr φ kv key).current_step = U := by rw [← hga]; exact hg.step
    have hjx : ∀ a b, (join e g).Adj a b ↔ (join (arr φ kv₀ key) (arr φ kv key)).Adj a b := by
      intro a b; rw [adj_join_iff, adj_join_iff, hadj₀, hga]
    have hjy : ∀ a b, (join e g).Adj a b ↔ (join (arr φ kv key) (arr φ kv₀ key)).Adj a b := by
      intro a b; rw [adj_join_iff, adj_join_iff, hadj₀, hga, or_comm]
    have hE : StarOneSideAt (join e g) e :=
      starOneSideAt_congr (by rw [hje]; exact hcsX.symm) hjx hal₀ hadj₀ (oneSide_holes hbd HR HA hp₁)
    have hG : StarOneSideAt (join e g) g :=
      starOneSideAt_congr (by rw [hje]; exact hcsG.symm) hjy (fun _ => by rw [hga]) (fun _ _ => by rw [hga])
        (oneSide_holes hbd HR HA hp₂)
    have hle := (tree_links hbd htree).1
    have hee := (tree_links hbd htree).2
    have hlg : LinksInv g := by rw [hga]; exact (tree_links hbd (ArrTree.leaf kv hkv hkd hvg)).1
    have heg : EdgesAlive g := by rw [hga]; exact edgesAlive_arr hbd hkv hvg
    have hDe : ∀ t, t ∈ e.alive → t.id.step = e.current_step - 1 → t ∉ g.alive := by
      intro t ht hts htg
      rw [hga] at htg
      exact d2_of_pair hbd hp₁ t ((hal₀ t).mp ht) (by rw [hcsX, ← he.step]; exact hts) htg
    have hDg : ∀ t, t ∈ g.alive → t.id.step = e.current_step - 1 → t ∉ e.alive := by
      intro t htg hts hte
      rw [hga] at htg
      exact d2_of_pair hbd hp₂ t htg (by rw [hcsG, ← he.step]; exact hts) ((hal₀ t).mp hte)
    exact chainInv_join_oneSide hcs (by rw [he.step]; omega) hle hlg hee heg hke hkg hE hG hDe hDg
  · exact hke

/-- **`ChainInv` en todas las entradas finales**, bajo `SibStarInv` + `ArrHole` + `AbsHole`. -/
theorem chainInv_run (hbd : Bounded φ) (HS : HypSib φ) (HR : ArrHole φ) (HA : AbsHole φ) :
    ∀ kv ∈ run φ, ChainInv kv.2 :=
  fun kv hkv => (run_provL hbd (upProvL_chain hbd HS) (fun _ hU => joinProvT_chain hbd HR HA hU)
    chainInv_initSeed kv hkv).2

end SecLine

end AbsSatBingo.Model
