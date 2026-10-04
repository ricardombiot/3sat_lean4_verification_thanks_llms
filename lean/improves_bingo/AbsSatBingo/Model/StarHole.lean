-- lean/improves_bingo/AbsSatBingo/Model/StarHole.lean
import AbsSatBingo.Model.ConeHole

/-!
# StarOneSide desde el hueco de la llegada de los padres

En el join `u` de las llegadas de `kvA` y `kvB` (nivel `n = m + 1`), los padres de una cima `t` de la llegada de
`kvA` son cimas de **una sola** llegada `Y` dentro de `kvA` (comparten remitente `E`, del nivel `m`). La estrella de
`t` en la unión cabe en los vivos de `Y`, y las aristas de la unión entre viejos bajan al nivel `m`. Así que basta un
hueco de `Y` con las aristas del nivel `m`:

* si `E` tenía la pareja, `Y` la quitó: **`ArrHole`**;
* si no (pareja **ausente** en `E`, en la otra entrada del nivel `n` y no en `kvA`): **`AbsHole`**. Medido
  (`probe_arrhole.jl`, sonda rápida, 6 instancias): 3 908/3 908.

**`readerVerdict_iff_of_holes`**: el veredicto del lector bajo B1 + `ArrHole` + `AbsHole`. Sin `CrossAt` ni el cono.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace SecLine

open GPathB Driver Machine CliqueSplit

variable {φ : Cnf}

/-- **AbsHole**: una llegada `Y` (remitente `E` del nivel `m`, destino `D`) que conserva a `y` y `w`, cuando `E` no
tiene la pareja, la entrada de `D` del nivel `m + 1` tampoco y otra entrada de ese nivel sí, deja un hueco con las
aristas de todo el nivel `m`. -/
def AbsHole (φ : Cnf) : Prop :=
  ∀ (m : Nat) (E A B : NodeId × GPathB) (y w : PathNodeId), E ∈ steps φ m (init φ) →
    A.1 ∈ sonsOfMap φ E.1 → (arr φ E A.1).isValid = true → y ∈ (arr φ E A.1).alive → w ∈ (arr φ E A.1).alive →
    ¬ E.2.Adj y w → A ∈ steps φ (m + 1) (init φ) → ¬ A.2.Adj y w → B ∈ steps φ (m + 1) (init φ) → B.1 ≠ A.1 →
    B.2.Adj y w →
    ∃ l : Int, 0 ≤ l ∧ l ≤ m ∧ ∀ r, r ∈ (arr φ E A.1).alive → r.id.step = l → ¬ (EdgeL φ m y r ∧ EdgeL φ m w r)

/-- La línea inicial tiene una sola entrada. -/
theorem senderPair_pos {n : Nat} {kvA kvB : NodeId × GPathB} {d : NodeId} (hp : SenderPair φ n kvA kvB d) :
    0 < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    obtain ⟨hA, hB, hne, _⟩ := hp
    have hA' : kvA ∈ init φ := by simpa [steps] using hA
    have hB' : kvB ∈ init φ := by simpa [steps] using hB
    rw [init_eq, List.mem_singleton] at hA' hB'
    exact absurd (by rw [hA', hB']) hne
  · exact h

/-- **El caso ausente de StarOneSide, desde el hueco de la llegada de los padres.** -/
theorem absent_of_holes (hbd : Bounded φ) (HR : ArrHole φ) (HA : AbsHole φ) {n : Nat}
    {kvA kvB : NodeId × GPathB} {d : NodeId} (hp : SenderPair φ n kvA kvB d)
    {t y w : PathNodeId} (htL : t ∈ (arr φ kvA d).alive) (hts : t.id.step = (n : Int) + 1)
    (hty : (join (arr φ kvA d) (arr φ kvB d)).Adj t y) (htw : (join (arr φ kvA d) (arr φ kvB d)).Adj t w)
    (hg : (arr φ kvB d).Adj y w) (habs : ¬ kvA.2.Adj y w) :
    ∃ l, 0 ≤ l ∧ l < (join (arr φ kvA d) (arr φ kvB d)).current_step ∧
      ∀ r, r.id.step = l → (join (arr φ kvA d) (arr φ kvB d)).Adj t r →
        ¬ ((join (arr φ kvA d) (arr φ kvB d)).Adj y r ∧ (join (arr φ kvA d) (arr φ kvB d)).Adj w r) := by
  have hn := senderPair_pos hp
  have hD2 := d2_of_pair hbd hp
  obtain ⟨hA, hB, hne, hdA, hdB, hvA, hvB⟩ := hp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hoA := (line_facts hbd (m + 1)).1 kvA hA
  have hokA := stateOk_upFiltering hoA hdA hvA
  have hcsX : (arr φ kvA d).current_step = ((m + 1 : Nat) : Int) + 1 + 1 := hokA.step
  have hcsu : (join (arr φ kvA d) (arr φ kvB d)).current_step = ((m + 1 : Nat) : Int) + 1 + 1 := hcsX
  have heaX := edgesAlive_arr hbd hA hvA
  have heaG := edgesAlive_arr hbd hB hvB
  have htg := hD2 t htL (by rw [hcsX]; omega)
  have hu : ∀ {a b}, (join (arr φ kvA d) (arr φ kvB d)).Adj a b → (arr φ kvA d).Adj a b ∨ (arr φ kvB d).Adj a b :=
    fun h => adj_join_iff.mp h
  have hte : ∀ {r}, (join (arr φ kvA d) (arr φ kvB d)).Adj t r → (arr φ kvA d).Adj t r := by
    intro r h
    rcases hu h with h | h
    · exact h
    · exact absurd (heaG t r h).1 htg
  have hold : ∀ {r}, (join (arr φ kvA d) (arr φ kvB d)).Adj t r → r ≠ t → r.id.step ≤ ((m + 1 : Nat) : Int) := by
    intro r h hrt
    have hx := hte h
    have hb := alive_below hokA.docs hokA.below (heaX t r hx).2
    rw [hcsX] at hb
    by_cases hr : r.id.step = ((m + 1 : Nat) : Int) + 1
    · exact absurd (arr_topsApart hbd hA hvA t r (by rw [hcsX]; omega) (by rw [hcsX]; omega) hx).symm hrt
    · omega
  have hyt : y ≠ t := fun h => by subst h; exact htg (heaG _ _ hg).1
  have hwt : w ≠ t := fun h => by subst h; exact htg (heaG _ _ hg).2
  have hyo := hold hty hyt
  have hwo := hold htw hwt
  -- los padres de t viven en una llegada Y de un remitente E del nivel m
  have htree := steps_tree m kvA hA
  have hparent : ∀ {r}, (join (arr φ kvA d) (arr φ kvB d)).Adj t r → r.id.step ≤ ((m + 1 : Nat) : Int) →
      ∃ E ∈ steps φ m (init φ), kvA.1 ∈ sonsOfMap φ E.1 ∧ (arr φ E kvA.1).isValid = true ∧
        t.gparent_id = some E.1 ∧ r ∈ (arr φ E kvA.1).alive ∧ ∃ q, q ∈ (arr φ E kvA.1).alive ∧
          q.id.step = ((m : Nat) : Int) + 1 ∧ kvA.2.Adj r q ∧ (arr φ E kvA.1).Adj r q := by
    intro r h hrs
    obtain ⟨q, h1, h2, hqs, hqa, hrq⟩ := parent_of_arr_adj hbd hA hdA hvA (by rw [hts]) hrs (hte h)
    obtain ⟨E, hE, hdE, hvE, hY⟩ := tree_adj htree hrq
    have hqs' : q.id.step = ((m : Nat) : Int) + 1 := by rw [hqs]; push_cast; rfl
    have hqY := (edgesAlive_arr hbd hE hvE r q hY).2
    have hqp := arr_top_parent hbd hE hdE hvE hqY hqs'
    exact ⟨E, hE, hdE, hvE, by rw [h2, hqp], (edgesAlive_arr hbd hE hvE r q hY).1, q, hqY, hqs', hrq, hY⟩
  obtain ⟨E, hE, hdE, hvE, hgp, hyY, q, hqY, hqs, hyq, _⟩ := hparent hty hyo
  have hsame : ∀ {E' : NodeId × GPathB}, E' ∈ steps φ m (init φ) → t.gparent_id = some E'.1 → E' = E := by
    intro E' hE' h
    rw [hgp] at h
    exact entry_unique hbd hE' hE (Option.some.inj h).symm
  have hwY : w ∈ (arr φ E kvA.1).alive := by
    obtain ⟨E', hE', _, _, hgp', hwY', _⟩ := hparent htw hwo
    have := hsame hE' hgp'
    subst this; exact hwY'
  -- y y w son viejos para el nivel m: una cima de kvA no vive en la llegada de kvB
  have hlow : ∀ {z}, z ∈ (arr φ kvB d).alive → z.id.step ≤ ((m + 1 : Nat) : Int) → z ∈ kvA.2.alive →
      z.id.step ≤ (m : Int) := by
    intro z hzg hzs hzA
    by_cases hz : z.id.step = ((m + 1 : Nat) : Int)
    · exfalso
      have hoB := (line_facts hbd (m + 1)).1 kvB hB
      have hsB := shrinks_filterAll kvB.2 (reqOf φ d)
      have hcf : (kvB.2.filterAll (reqOf φ d)).current_step = ((m + 1 : Nat) : Int) + 1 := hsB.1.step.trans hoB.step
      have hds : d.step = (kvB.2.filterAll (reqOf φ d)).current_step := by
        rw [hcf, sonsOfMap_step φ kvB.1 d hdB, hoB.key]; omega
      rw [arr_eq hvB] at hzg
      have ha := (shrinks_review _).1.alive z hzg
      rcases alive_addNode_cases (title := "") (aliveDocs_filterAll hoB.docs _) (below_of_shrinks hsB hoB.below)
          hds ha with ⟨h1, _⟩ | ⟨_, h1⟩
      · have hzB := hsB.1.alive z h1
        exact hne ((top_id hbd hA hzA hz).symm.trans (top_id hbd hB hzB hz))
      · omega
    · push_cast at hz ⊢; omega
  have hyA := (line_edgesAlive hbd hA y q hyq).1
  have hwA : w ∈ kvA.2.alive := by
    obtain ⟨_, _, _, _, _, _, q', _, _, hwq', _⟩ := hparent htw hwo
    exact (line_edgesAlive hbd hA w q' hwq').1
  have hym := hlow (heaG y w hg).1 hyo hyA
  have hwm := hlow (heaG y w hg).2 hwo hwA
  -- el hueco de Y
  have hBedge : kvB.2.Adj y w := old_of_arr_adj hbd hB hdB hvB (by push_cast; omega) (by push_cast; omega) hg
  obtain ⟨l, h0, h1, hl⟩ : ∃ l : Int, 0 ≤ l ∧ l ≤ m ∧
      ∀ r, r ∈ (arr φ E kvA.1).alive → r.id.step = l → ¬ (EdgeL φ m y r ∧ EdgeL φ m w r) := by
    by_cases hEyw : E.2.Adj y w
    · have hnY : ¬ (arr φ E kvA.1).Adj y w := fun h =>
        habs (tree_incl hbd htree hE (line_edgesAlive hbd hA y q hyq).2
          (by rw [hqs]) (by rw [arr_top_parent hbd hE hdE hvE hqY (by rw [hqs])]) y w h)
      exact HR m E kvA.1 y w hE hdE hvE hyY hwY hEyw hnY
    · exact HA m E kvA kvB y w hE hdE hvE hyY hwY hEyw hA habs hB (Ne.symm hne) hBedge
  refine ⟨l, h0, by rw [hcsu]; push_cast; omega, fun r hrl hrt ⟨hyr, hwr⟩ => ?_⟩
  have hrt' : r ≠ t := fun h => by subst h; push_cast at hts; omega
  have hro := hold hrt hrt'
  obtain ⟨E', hE', _, _, hgp', hrY, _⟩ := hparent hrt hro
  have := hsame hE' hgp'
  subst this
  have hrm : r.id.step ≤ (m : Int) := by omega
  have hdown : ∀ {a : PathNodeId}, a.id.step ≤ (m : Int) → (join (arr φ kvA d) (arr φ kvB d)).Adj a r →
      EdgeL φ m a r := by
    intro a ha h
    have h' : EdgeL φ (m + 1) a r := by
      rcases hu h with h | h
      · exact ⟨kvA, hA, old_of_arr_adj hbd hA hdA hvA (by push_cast; omega) (by push_cast; omega) h⟩
      · exact ⟨kvB, hB, old_of_arr_adj hbd hB hdB hvB (by push_cast; omega) (by push_cast; omega) h⟩
    exact edge_down hbd ha hrm h'
  exact hl r hrY hrl ⟨hdown hym hyr, hdown hwm hwr⟩

/-- **StarOneSide en el lado de `kvA` bajo `ArrHole` y `AbsHole`.** -/
theorem oneSide_holes (hbd : Bounded φ) (HR : ArrHole φ) (HA : AbsHole φ) {n : Nat}
    {kvA kvB : NodeId × GPathB} {d : NodeId} (hp : SenderPair φ n kvA kvB d) :
    StarOneSideAt (join (arr φ kvA d) (arr φ kvB d)) (arr φ kvA d) := by
  have heaE := edgesAlive_arr hbd hp.1 hp.2.2.2.2.2.1
  have heaG := edgesAlive_arr hbd hp.2.1 hp.2.2.2.2.2.2
  have hGap : GapDead kvA.2 (arr φ kvA d) (arr φ kvB d) (join (arr φ kvA d) (arr φ kvB d)) :=
    gapDead_of_arrivalGap adj_join_cases rfl heaE heaG (d2_of_pair hbd hp) (arrivalGap_of_arrHole hbd HR hp)
  have hcsX := (stateOk_upFiltering ((line_facts hbd n).1 kvA hp.1) hp.2.2.2.1 hp.2.2.2.2.2.1).step
  intro t htL hts y w hty htw hyw hne
  have hg : (arr φ kvB d).Adj y w := by
    rcases adj_join_iff.mp hyw with h | h
    · exact absurd h hne
    · exact h
  by_cases hAyw : kvA.2.Adj y w
  · obtain ⟨l, h0, h1, hl⟩ := hGap t htL hts y w hty htw hg hne hAyw
    have htg := d2_of_pair hbd hp t htL (by rw [hts]; rfl)
    refine ⟨l, h0, h1, fun r hrl hrt hyr => hl r ?_ hrl hyr⟩
    rcases adj_join_iff.mp hrt with h | h
    · exact (heaE t r h).2
    · exact absurd (heaG t r h).1 htg
  · have hts' : t.id.step = (n : Int) + 1 := by
      have : (join (arr φ kvA d) (arr φ kvB d)).current_step = (arr φ kvA d).current_step := rfl
      rw [hts, this, hcsX]; omega
    exact absent_of_holes hbd HR HA hp htL hts' hty htw hg hAyw

/-- **Las hipótesis**: B1 en los joins y los dos huecos de una llegada. -/
structure HypsHoles (φ : Cnf) : Prop where
  b1 : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvC e → SInvC g → okJoin e g = true →
    StarNodes (join e g)
  rem : ArrHole φ
  abs : AbsHole φ

/-- **El veredicto del lector bajo B1, `ArrHole` y `AbsHole`**: sin `CrossAt`, sin cono, sin `ConeGap`. -/
theorem readerVerdict_iff_of_holes (hbd : Bounded φ) (H : HypsHoles φ) : readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_one hbd H.b1 (fun _ _ _ _ hp _ _ => oneSide_holes hbd H.rem H.abs hp)

end SecLine

end AbsSatBingo.Model
