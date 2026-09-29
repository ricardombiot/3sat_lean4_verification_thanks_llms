-- lean/improves_bingo/AbsSatBingo/Model/PinSide.lean
import AbsSatBingo.Model.StarHole

/-!
# Fijar la historia de la cima: el join de un solo lado

En el join `u` de las llegadas `X` (de `kvA`) y `G` (de `kvB`) al destino `d`, del nivel `n = m + 1`, una estructura
cerrada de `u` **fijada** en el paso `n` en la clave `kvA.1` (el color de los padres de la cima) y en el paso `m` en la
clave `E.1` de una entrada `E` del nivel `m` (el color del abuelo) **usa solo aristas de `X`** (`pinOneSide2`):

* todos sus nodos poseen una cima de `kvA` del paso `n`, que no vive en `G`, así que están vivos en `X`;
* esas cimas poseen un nodo del paso `m` de color `E.1`, que es su padre (TopsApart del remitente), así que son cimas de
  la llegada `Y` de `E` a `kvA.1`, y los nodos viejos de la estructura están vivos en `Y`;
* una pareja de `G` que no es de `X`: si `kvA` la tenía, `X` la quitó (**`ArrHole`** en `X`); si no, **`ArrHole`** o
  **`AbsHole`** en `Y`. El hueco contradice los testigos de la estructura.

Medido (`probe_pinstar.jl`, 6 instancias): fijar así cualquier estructura cerrada de la unión conserva la estrella de
la cima y sus aristas (**`PinKeeps2`**, 2 527 / 0) y deja una estructura de un solo lado (2 527 / 0).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace SecLine

open GPathB Driver Machine CliqueSplit

variable {φ : Cnf}

/-- Un vivo de una llegada en el paso de su remitente es una cima del remitente. -/
theorem arr_old_top (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {d : NodeId} (hd : d ∈ sonsOfMap φ kv.1) (hv : (arr φ kv d).isValid = true) {z : PathNodeId}
    (hz : z ∈ (arr φ kv d).alive) (hzs : z.id.step = (n : Int)) : z ∈ kv.2.alive ∧ z.id = kv.1 := by
  have ho := (line_facts hbd n).1 kv hkv
  have hs := shrinks_filterAll kv.2 (reqOf φ d)
  have hcf : (kv.2.filterAll (reqOf φ d)).current_step = (n : Int) + 1 := hs.1.step.trans ho.step
  have hds : d.step = (kv.2.filterAll (reqOf φ d)).current_step := by
    rw [hcf, sonsOfMap_step φ kv.1 d hd, ho.key]; omega
  rw [arr_eq hv] at hz
  have ha := (shrinks_review _).1.alive z hz
  rcases alive_addNode_cases (title := "") (aliveDocs_filterAll ho.docs _) (below_of_shrinks hs ho.below)
      hds ha with ⟨h1, _⟩ | ⟨_, h1⟩
  · have hzk := hs.1.alive z h1
    exact ⟨hzk, top_id hbd hkv hzk hzs⟩
  · omega

/-- **Fijada la historia de la cima, la estructura es de un solo lado.** -/
theorem pinOneSide2 (hbd : Bounded φ) (HR : ArrHole φ) (HA : AbsHole φ) {m : Nat}
    {kvA kvB : NodeId × GPathB} {d : NodeId} (hp : SenderPair φ (m + 1) kvA kvB d)
    {E : NodeId × GPathB} (hE : E ∈ steps φ m (init φ))
    {u : GPathB} (hu : ∀ {a b}, u.Adj a b → (arr φ kvA d).Adj a b ∨ (arr φ kvB d).Adj a b)
    (hcsu : u.current_step = ((m + 1 : Nat) : Int) + 1 + 1)
    {W : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop} (hst : SecStruct u W R)
    (hpA : SecAgrees W kvA.1) (hpE : SecAgrees W E.1) :
    ∀ {y w}, R y w → (arr φ kvA d).Adj y w := by
  have hD2 := d2_of_pair hbd hp
  obtain ⟨hA, hB, hne, hdA, hdB, hvA, hvB⟩ := hp
  have hoA := (line_facts hbd (m + 1)).1 kvA hA
  have hoE := (line_facts hbd m).1 E hE
  have heaX := edgesAlive_arr hbd hA hvA
  have heaG := edgesAlive_arr hbd hB hvB
  have hkA : kvA.1.step = ((m + 1 : Nat) : Int) := by rw [hoA.key]; omega
  have hkE : E.1.step = (m : Int) := by rw [hoE.key]; omega
  -- un nodo del paso n de la estructura es de kvA y no vive en G
  have hnotG : ∀ {q}, W q → q.id.step = ((m + 1 : Nat) : Int) → q ∉ (arr φ kvB d).alive := by
    intro q hq hqs hqg
    have h1 := (arr_old_top hbd hB hdB hvB hqg hqs).2
    have h2 := hpA hq (by rw [hqs, hkA])
    exact hne (h2.symm.trans h1)
  have hadjX : ∀ {y q}, W q → q.id.step = ((m + 1 : Nat) : Int) → u.Adj y q → (arr φ kvA d).Adj y q := by
    intro y q hq hqs h
    rcases hu h with h | h
    · exact h
    · exact absurd (heaG y q h).2 (hnotG hq hqs)
  -- todo nodo de la estructura posee un nodo del paso n
  have hsn : ∀ {y}, W y → ∃ q, W q ∧ q.id.step = ((m + 1 : Nat) : Int) ∧ R y q := by
    intro y hy
    obtain ⟨q, hqV, hqs, hyq⟩ := GPathB.exists_at hst hy ((m + 1 : Nat) : Int) (by omega) (by rw [hcsu]; omega)
    exact ⟨q, hqV, hqs, hyq⟩
  have hinX : ∀ {y}, W y → y ∈ (arr φ kvA d).alive := by
    intro y hy
    obtain ⟨q, hq, hqs, hyq⟩ := hsn hy
    exact (heaX y q (hadjX hq hqs (hst.adj hyq))).1
  -- las cimas del paso n de la estructura son de la llegada Y de E a kvA.1
  have htree := steps_tree m kvA hA
  have hcsA : (arr φ kvA d).current_step = ((m + 1 : Nat) : Int) + 1 + 1 :=
    (stateOk_upFiltering hoA hdA hvA).step
  have hold : ∀ {a}, a ∈ (arr φ kvA d).alive → a.id.step ≤ ((m + 1 : Nat) : Int) + 1 := by
    intro a ha
    have hok := stateOk_upFiltering hoA hdA hvA
    have := alive_below hok.docs hok.below ha
    rw [hok.step] at this; omega
  have hY : ∀ {q}, W q → q.id.step = ((m + 1 : Nat) : Int) →
      kvA.1 ∈ sonsOfMap φ E.1 ∧ (arr φ E kvA.1).isValid = true ∧ q ∈ (arr φ E kvA.1).alive ∧
        q.parent_id = some E.1 ∧ q ∈ kvA.2.alive := by
    intro q hq hqs
    obtain ⟨q', hq'V, hq's, hqq'⟩ := GPathB.exists_at hst hq (m : Int) (by omega) (by rw [hcsu]; omega)
    have hX : (arr φ kvA d).Adj q q' := by
      have := hadjX hq hqs ((adj_symm _ _ _).mp (hst.adj hqq'))
      exact (adj_symm _ _ _).mp this
    have hkq : kvA.2.Adj q q' := old_of_arr_adj hbd hA hdA hvA (by omega) (by omega) hX
    obtain ⟨S, hS, hdS, hvS, hYS⟩ := tree_adj htree hkq
    have hqs' : q.id.step = (m : Int) + 1 := by rw [hqs]; push_cast; rfl
    have hqY := (edgesAlive_arr hbd hS hvS q q' hYS).1
    obtain ⟨p, hp1, _, hps, hpa, hq'p⟩ := parent_of_arr_adj hbd hS hdS hvS hqs' (by omega) hYS
    have hq'S := (line_edgesAlive hbd hS q' p hq'p).1
    have heq : q' = p := tops_eq hbd hS (by omega) hps hq'p
    subst heq
    have hid : q'.id = E.1 := hpE hq'V (by rw [hq's, hkE])
    have hqp : q.parent_id = some E.1 := by rw [hp1, hid]
    have hSE : S = E := by
      have := arr_top_parent hbd hS hdS hvS hqY hqs'
      rw [hqp] at this
      exact entry_unique hbd hS hE (Option.some.inj this).symm
    subst hSE
    exact ⟨hdS, hvS, hqY, hqp, (line_edgesAlive hbd hA q q' hkq).1⟩
  -- los nodos viejos de la estructura viven en Y
  have hinY : ∀ {y}, W y → y.id.step ≤ ((m + 1 : Nat) : Int) → y ∈ (arr φ E kvA.1).alive := by
    intro y hy hys
    obtain ⟨q, hq, hqs, hyq⟩ := hsn hy
    obtain ⟨hdE, hvE, hqY, hqp, _⟩ := hY hq hqs
    have hX := hadjX hq hqs (hst.adj hyq)
    have hk : kvA.2.Adj y q := old_of_arr_adj hbd hA hdA hvA hys (by omega) hX
    obtain ⟨S, hS, hdS, hvS, hYS⟩ := tree_adj htree hk
    have hqs' : q.id.step = (m : Int) + 1 := by rw [hqs]; push_cast; rfl
    have hqa := (edgesAlive_arr hbd hS hvS y q hYS).2
    have := arr_top_parent hbd hS hdS hvS hqa hqs'
    rw [hqp] at this
    have hSE := entry_unique hbd hS hE (Option.some.inj this).symm
    subst hSE
    exact (edgesAlive_arr hbd hS hvS y q hYS).1
  -- la afirmación
  intro y w hyw
  have hyX := hinX (hst.dom hyw).1
  rcases hu (hst.adj hyw) with h | hg
  · exact h
  refine Classical.byContradiction fun hnX => ?_
  -- y y w no son cimas de X ni nodos del paso n
  have hlow : ∀ {a}, W a → a ∈ (arr φ kvB d).alive → a.id.step ≤ (m : Int) := by
    intro a ha hag
    have hax := hinX ha
    have := hold hax
    by_cases h1 : a.id.step = ((m + 1 : Nat) : Int) + 1
    · exact absurd hag (hD2 a hax (by rw [hcsA, h1]; omega))
    by_cases h2 : a.id.step = ((m + 1 : Nat) : Int)
    · exact absurd hag (hnotG ha h2)
    push_cast at this h1 h2 ⊢; omega
  have hym := hlow (hst.dom hyw).1 (heaG y w hg).1
  have hwm := hlow (hst.dom hyw).2 (heaG y w hg).2
  have hwX := hinX (hst.dom hyw).2
  -- los testigos de la estructura en un paso l ≤ m + 1
  have hwit : ∀ l : Int, 0 ≤ l → l ≤ ((m + 1 : Nat) : Int) → ∃ r, r.id.step = l ∧ W r ∧ R y r ∧ R w r := by
    intro l h0 h1
    obtain ⟨r, hrl, hyr, hwr⟩ := hst.pair hyw l h0 (by rw [hcsu]; omega)
    exact ⟨r, hrl, (hst.dom hyr).2, hyr, hwr⟩
  have hedge : ∀ {a r}, a.id.step ≤ ((m + 1 : Nat) : Int) → r.id.step ≤ ((m + 1 : Nat) : Int) → u.Adj a r →
      EdgeL φ (m + 1) a r := by
    intro a r ha hr h
    rcases hu h with h | h
    · exact ⟨kvA, hA, old_of_arr_adj hbd hA hdA hvA ha hr h⟩
    · exact ⟨kvB, hB, old_of_arr_adj hbd hB hdB hvB ha hr h⟩
  by_cases hAyw : kvA.2.Adj y w
  · -- X la quitó
    obtain ⟨l, h0, h1, hl⟩ := HR (m + 1) kvA d y w hA hdA hvA hyX hwX hAyw hnX
    obtain ⟨r, hrl, hrW, hyr, hwr⟩ := hwit l h0 h1
    exact hl r (hinX hrW) hrl ⟨hedge (by omega) (by omega) (hst.adj hyr), hedge (by omega) (by omega) (hst.adj hwr)⟩
  · -- ausente en kvA: el hueco de Y
    obtain ⟨q, hq, hqs, hyq⟩ := hsn (hst.dom hyw).1
    obtain ⟨hdE, hvE, hqY, hqp, hqA⟩ := hY hq hqs
    have hyY := hinY (hst.dom hyw).1 (by omega)
    have hwY := hinY (hst.dom hyw).2 (by omega)
    have hBedge : kvB.2.Adj y w := old_of_arr_adj hbd hB hdB hvB (by omega) (by omega) hg
    obtain ⟨l, h0, h1, hl⟩ : ∃ l : Int, 0 ≤ l ∧ l ≤ m ∧
        ∀ r, r ∈ (arr φ E kvA.1).alive → r.id.step = l → ¬ (EdgeL φ m y r ∧ EdgeL φ m w r) := by
      by_cases hEyw : E.2.Adj y w
      · have hnY : ¬ (arr φ E kvA.1).Adj y w := fun h =>
          hAyw (tree_incl hbd htree hE hqA (by rw [hqs]; push_cast; rfl) hqp y w h)
        exact HR m E kvA.1 y w hE hdE hvE hyY hwY hEyw hnY
      · exact HA m E kvA kvB y w hE hdE hvE hyY hwY hEyw hA hAyw hB (Ne.symm hne) hBedge
    obtain ⟨r, hrl, hrW, hyr, hwr⟩ := hwit l h0 (by push_cast; omega)
    have hrm : r.id.step ≤ (m : Int) := by omega
    exact hl r (hinY hrW (by omega)) hrl
      ⟨edge_down hbd hym hrm (hedge (by omega) (by omega) (hst.adj hyr)),
       edge_down hbd hwm hrm (hedge (by omega) (by omega) (hst.adj hwr))⟩

end SecLine

end AbsSatBingo.Model
