-- lean/improves_bingo/AbsSatBingo/Model/CliqueSplit.lean
import AbsSatBingo.Model.NodeIn

/-!
# `CliqueSplit`: toda camarilla de la unión de dos llegadas es camarilla de un lado

El primer hecho demostrado **sobre el join** que no es una hipótesis. El argumento es semántico, con las piezas de la
máquina:

1. **Selecciones válidas** (`ValidSel`): lo que la máquina comprueba en un camino hasta el paso `t` — ids encadenados
   por ventanas, hijos del mapa, requisitos cumplidos y ninguna ventana prohibida.
2. **Completitud para toda selección válida** (`steps_has_sel`): la línea del paso `t` tiene, en la clave de `S t`,
   un estado que lleva `S`. Es `steps_inv` (que va de una asignación que satisface `φ`) para cualquier selección
   válida; y la llegada de un remitente que la lleva también la lleva (`carried_arrival`).
3. **Una camarilla de un estado de la máquina es una selección válida** (`validSel_of_carried`), con `Struct` y un
   invariante nuevo, **`MapLinks`**: los enlaces padre → hijo siguen el mapa.

**`cliqueSplit`**: en la unión de las llegadas de dos remitentes distintos a un mismo destino, una camarilla pasa por
uno de los dos remitentes; la llegada de ese remitente la lleva (completitud), así que es camarilla de ese lado.
Medido antes (`probe_cliquesplit.jl`): 33 445 camarillas de 2 688 uniones, 0 fallos.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace CliqueSplit

open GPathB Driver Machine

variable {φ : Cnf}

/-- La raíz. -/
def root : PathNodeId := { id := ⟨0, 0⟩, parent_id := none, gparent_id := none }

/-- **Una selección válida hasta el paso `t`.** -/
structure ValidSel (φ : Cnf) (t : Int) (S : Int → PathNodeId) : Prop where
  step  : ∀ j, 0 ≤ j → j ≤ t → (S j).id.step = j
  root  : S 0 = root
  shift : ∀ j, 1 ≤ j → j ≤ t → shiftPid (S (j - 1)) (S j).id = S j
  son   : ∀ j, 1 ≤ j → j ≤ t → (S j).id ∈ sonsOfMap φ (S (j - 1)).id
  req   : ∀ j, 1 ≤ j → j ≤ t → ∀ r ∈ reqOf φ (S j).id, 0 ≤ r.step → r.step < j → (S r.step).id = r
  forb  : ∀ j, 1 ≤ j → j ≤ t → isProhibited φ (S j) = false

theorem ValidSel.mono {t t' : Int} {S : Int → PathNodeId} (h : ValidSel φ t S) (ht : t' ≤ t) : ValidSel φ t' S :=
  ⟨fun j h0 h1 => h.step j h0 (by omega), h.root, fun j h0 h1 => h.shift j h0 (by omega),
   fun j h0 h1 => h.son j h0 (by omega), fun j h0 h1 => h.req j h0 (by omega), fun j h0 h1 => h.forb j h0 (by omega)⟩

-- ============================================================
-- La llegada lleva la selección
-- ============================================================

/-- **La llegada de un remitente que lleva una selección válida también la lleva.** -/
theorem carried_arrival {t : Int} (ht0 : 0 ≤ t) {S : Int → PathNodeId} (hv : ValidSel φ (t + 1) S) {g0 : GPathB}
    (hok : StateOk (t + 1) (S t).id g0) (hc : Carried g0 S) :
    Carried (g0.upFiltering (reqOf φ (S (t + 1)).id) (S (t + 1)).id "" (isProhibited φ)) S := by
  let d := (S (t + 1)).id
  let g1 := g0.filterAll (reqOf φ d)
  have hs1 := shrinks_filterAll g0 (reqOf φ d)
  have hstep1 : g1.current_step = t + 1 := (step_of_shrinks hs1).trans hok.step
  have hc1 : Carried g1 S := by
    refine carried_filterAll hc _ ?_
    intro r hr h0 h1
    exact hv.req (t + 1) (by omega) (Int.le_refl _) r hr h0 (by rw [hok.step] at h1; exact h1)
  have hnp : S t ∈ g1.newParents := by
    obtain ⟨n, hn, _, _⟩ := hc1.node t ht0 (by omega)
    have hid := node?_id hn
    unfold newParents
    rw [if_pos (by omega)]
    refine List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨node?_mem hn, ?_⟩, hid⟩
    rw [hid, hstep1]; simp [hv.step t ht0 (by omega)]
  have hshift : shiftPid (S t) d = S (t + 1) := by
    have := hv.shift (t + 1) (by omega) (Int.le_refl _)
    simpa using this
  show Carried (g1.up d "" (isProhibited φ)) S
  apply carried_up hc1
  · rw [hstep1]
    refine List.mem_filter.mpr ⟨?_, by simp [hv.forb (t + 1) (by omega) (Int.le_refl _)]⟩
    unfold shiftRowIds
    rw [if_pos (by omega)]
    exact (mem_dedupPids _ _).mpr (List.mem_map.mpr ⟨S t, hnp, hshift⟩)
  · intro _
    rw [hstep1, show t + 1 - 1 = t by omega]
    exact List.mem_filter.mpr ⟨hnp, by simp [hshift]⟩
  · rw [hstep1]; exact hv.step (t + 1) (by omega) (Int.le_refl _)
  · rw [hstep1]; exact fun n hn => hstep1 ▸ below_of_shrinks hs1 hok.below n hn
  · rw [hv.root]; rfl

-- ============================================================
-- Completitud por la línea
-- ============================================================

/-- **El paso**: una selección válida sigue llevada en la línea siguiente. -/
theorem advance_has_sel (t : Int) (ht0 : 0 ≤ t) {S : Int → PathNodeId} (hv : ValidSel φ (t + 1) S) (line : Line)
    (hl : LineOk (t + 1) line) (hh : Has S (S t).id line) : Has S (S (t + 1)).id (advance φ line) := by
  obtain ⟨g0, hf, hc⟩ := hh
  have hmem := List.mem_of_find?_eq_some hf
  have hok : StateOk (t + 1) (S t).id g0 := hl _ hmem
  let d := (S (t + 1)).id
  have hd : d ∈ sonsOfMap φ (S t).id := by
    have := hv.son (t + 1) (by omega) (Int.le_refl _)
    simpa using this
  have hc2 := carried_arrival ht0 hv hok hc
  have hvalid : (g0.upFiltering (reqOf φ d) d "" (isProhibited φ)).isValid = true := isValid_of_carried hc2
  have hok2 : StateOk (t + 1 + 1) d (g0.upFiltering (reqOf φ d) d "" (isProhibited φ)) :=
    stateOk_upFiltering hok hd hvalid
  unfold advance
  refine foldl_establish _ (fun next => Has S d next) (LineOk (t + 1 + 1)) line
    (fun _ kv hkv hx => lineOk_sendAll (hl kv hkv) hx)
    (fun _ kv _ _ hx => by
      unfold sendAll
      exact foldl_pres _ (fun next => Has S d next) _ (fun y d' _ hy => has_sendTo hy) _ hx)
    ((S t).id, g0) ?_ hmem [] (fun _ h => absurd h List.not_mem_nil)
  intro x hx
  unfold sendAll
  refine foldl_establish _ (fun next => Has S d next) (LineOk (t + 1 + 1)) _
    (fun y d' hd' hy => lineOk_sendTo hok d' hd' hy)
    (fun y d' _ _ hy => has_sendTo hy) d ?_ hd x hx
  intro y hy
  unfold sendTo
  dsimp only
  rw [if_pos hvalid]
  exact has_insert_self hy hok2 hc2

/-- La línea inicial lleva toda selección válida (su raíz). -/
theorem init_has_sel {S : Int → PathNodeId} (hv : ValidSel φ 0 S) : Has S (S 0).id (init φ) := by
  obtain ⟨_, hh⟩ := init_inv φ (fun _ => false)
  obtain ⟨g, hf, hc⟩ := hh
  refine ⟨g, ?_, carried_congr hc ?_⟩
  · rw [hv.root]; rw [sel_zero] at hf; exact hf
  · intro k h0 h1
    have hs : g.current_step = 1 := by
      have hl := (init_inv φ (fun _ => false)).1
      exact (hl _ (List.mem_of_find?_eq_some hf)).step
    have hk : k = 0 := by omega
    subst hk
    rw [hv.root]
    simp [pidOfAssign, root, selOfAssign]

/-- **Completitud**: la línea del paso `t` lleva toda selección válida hasta `t`, en la clave de `S t`. -/
theorem steps_has_sel :
    ∀ (n : Nat) {S : Int → PathNodeId}, ValidSel φ n S →
      LineOk ((n : Int) + 1) (steps φ n (init φ)) ∧ Has S (S n).id (steps φ n (init φ)) := by
  intro n
  induction n with
  | zero =>
    intro S hv
    exact ⟨by simpa [steps] using (init_inv φ (fun _ => false)).1, by simpa [steps] using init_has_sel (by simpa using hv)⟩
  | succ n ih =>
    intro S hv
    obtain ⟨hl, hh⟩ := ih (hv.mono (by push_cast; omega))
    rw [steps_succ]
    have hv' : ValidSel φ ((n : Int) + 1) S := by simpa using hv
    refine ⟨?_, ?_⟩
    · rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
      exact lineOk_advance hl
    · rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 by push_cast; rfl]
      exact advance_has_sel n (by omega) hv' _ hl hh

-- ============================================================
-- MapLinks: los enlaces siguen el mapa, y el paso 0 es la raíz
-- ============================================================

/-- **Los enlaces padre → hijo siguen el mapa, y todo documento del paso 0 es la raíz.** -/
def MapLinks (φ : Cnf) (g : GPathB) : Prop :=
  (∀ n ∈ g.nodes, ∀ p ∈ n.parents, n.id.id ∈ sonsOfMap φ p.id) ∧ (∀ n ∈ g.nodes, n.id.id.step = 0 → n.id = root)

theorem mapLinks_of_sub {h g : GPathB} (hs : Sub h g) (hg : MapLinks φ g) : MapLinks φ h := by
  refine ⟨fun n hn p hp => ?_, fun n hn h0 => ?_⟩
  · obtain ⟨m, hm, hid, hpar, _⟩ := hs.nodes n hn
    rw [← hid]; exact hg.1 m hm p (hpar p hp)
  · obtain ⟨m, hm, hid, _, _⟩ := hs.nodes n hn
    rw [← hid] at h0 ⊢; exact hg.2 m hm h0

theorem mapLinks_addNode {g : GPathB} {key d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (hg : MapLinks φ g) (htop : TopDocsId g key) (hd : d ∈ sonsOfMap φ key) (hpos : 0 < g.current_step) :
    MapLinks φ (g.addNode d title forb) := by
  refine ⟨fun n hn p hp => ?_, fun n hn h0 => ?_⟩
  · rcases List.mem_append.mp hn with h | h
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
      exact hg.1 m hm p hp
    · obtain ⟨pid, hpid, rfl⟩ := List.mem_map.mp h
      have hpid' : pid.id = d := Machine.mapId_of_mem_shiftRowIds (List.mem_filter.mp hpid).1
      obtain ⟨m, hm, hmid, hms⟩ := step_of_newParents (rowParents_sub hp)
      have hpk : p.id = key := by rw [← hmid]; exact htop m hm (by rw [hmid]; exact hms)
      show pid.id ∈ sonsOfMap φ p.id
      rw [hpid', hpk]; exact hd
  · rcases List.mem_append.mp hn with h | h
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
      exact hg.2 m hm h0
    · obtain ⟨pid, hpid, rfl⟩ := List.mem_map.mp h
      have hpid' : pid.id = d := Machine.mapId_of_mem_shiftRowIds (List.mem_filter.mp hpid).1
      have hds : d.step = key.step + 1 := sonsOfMap_step φ key d hd
      obtain ⟨q, hq⟩ : ∃ q, q ∈ g.newParents := by
        obtain ⟨q, hq, _⟩ := List.mem_filter.mp hpid |>.1 |> fun h => (by
          unfold shiftRowIds at h
          rw [if_pos hpos, mem_dedupPids] at h
          obtain ⟨q, hq, _⟩ := List.mem_map.mp h
          exact ⟨q, hq, trivial⟩ : ∃ q, q ∈ g.newParents ∧ True)
        exact ⟨q, hq⟩
      obtain ⟨m, hm, hmid, hms⟩ := step_of_newParents hq
      have hkey := htop m hm (by rw [hmid]; exact hms)
      have : pid.id.step = 0 := h0
      rw [hpid', hds, ← hkey, hmid, hms] at this
      omega

theorem mapLinks_join {e g : GPathB} (he : MapLinks φ e) (hg : MapLinks φ g) : MapLinks φ (join e g) := by
  refine ⟨fun n hn p hp => ?_, fun n hn h0 => ?_⟩
  · rcases mem_join_nodes hn with ⟨m, hm, _, hnm⟩ | ⟨m, hm, m', hm', hnm⟩ | ⟨hn', _⟩
    · subst hnm; exact he.1 _ hm p hp
    · subst hnm
      rcases merge_parents_cases hp with h | h
      · exact he.1 _ hm p h
      · have hid : m'.id = m.id := node?_id hm'
        have := hg.1 m' (node?_mem hm') p h
        rw [hid] at this; exact this
    · exact hg.1 n hn' p hp
  · rcases mem_join_nodes hn with ⟨m, hm, _, hnm⟩ | ⟨m, hm, m', hm', hnm⟩ | ⟨hn', _⟩
    · subst hnm; exact he.2 _ hm h0
    · subst hnm; exact he.2 m hm h0
    · exact hg.2 n hn' h0

theorem mapLinks_doJoin {e g : GPathB} (he : MapLinks φ e) (hg : MapLinks φ g) : MapLinks φ (doJoin e g) := by
  unfold doJoin; split
  · exact mapLinks_join he hg
  · exact he

theorem mapLinks_upFiltering {T : Int} (hT : 1 ≤ T) {key d : NodeId} {g : GPathB} (hok : StateOk T key g)
    (hg : MapLinks φ g) (htop : TopDocsId g key) (hd : d ∈ sonsOfMap φ key) :
    MapLinks φ (g.upFiltering (reqOf φ d) d "" (isProhibited φ)) := by
  have hs := shrinks_filterAll g (reqOf φ d)
  have hf := mapLinks_of_sub hs.1 hg
  have htf : TopDocsId (g.filterAll (reqOf φ d)) key := topDocsId_of_shrinks hs htop
  have hstep : (g.filterAll (reqOf φ d)).current_step = T := hs.1.step.trans hok.step
  unfold upFiltering up
  split
  · exact mapLinks_of_sub (shrinks_review _).1 (mapLinks_addNode hf htf hd (by omega))
  · exact hf

theorem mapLinks_initSeed : MapLinks φ (initSeed (⟨0, 0⟩ : NodeId) "") := by
  have hup : initSeed (⟨0, 0⟩ : NodeId) "" = (GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)).review := by
    unfold initSeed up
    rw [if_pos (show GPathB.empty.isValid = true by rfl)]
  rw [hup]
  refine mapLinks_of_sub (shrinks_review _).1 ⟨fun n hn p hp => ?_, fun n hn _ => ?_⟩
  · have hnodes : (GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)).nodes = [GPathB.empty.rowNode ⟨0, 0⟩ "" root] := rfl
    rw [hnodes, List.mem_singleton] at hn
    subst hn
    exact absurd hp (by show p ∉ ([] : List PathNodeId); exact List.not_mem_nil)
  · have hnodes : (GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)).nodes = [GPathB.empty.rowNode ⟨0, 0⟩ "" root] := rfl
    rw [hnodes, List.mem_singleton] at hn
    subst hn
    rfl

theorem mapLinks_insert {line : Line} {key : NodeId} {g : GPathB} (hl : ∀ kv ∈ line, MapLinks φ kv.2)
    (hg : MapLinks φ g) : ∀ kv ∈ Driver.insert line key g, MapLinks φ kv.2 := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have he := hl _ (List.mem_of_find?_eq_some hfind)
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact mapLinks_doJoin he hg
    · exact hl kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton] at h; subst h; exact hg

theorem mapLinks_advance {T : Int} (hT : 1 ≤ T) {line : Line} (hl : LineOk T line) (hent : ∀ kv ∈ line, EntOk kv)
    (hml : ∀ kv ∈ line, MapLinks φ kv.2) : ∀ kv ∈ advance φ line, MapLinks φ kv.2 := by
  unfold advance
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, MapLinks φ kv.2) _ (fun next kv hkv hn => ?_) _
    (fun _ h => absurd h List.not_mem_nil)
  unfold sendAll
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, MapLinks φ kv.2) _ (fun y d hd hy => ?_) _ hn
  unfold sendTo
  dsimp only
  split
  · exact mapLinks_insert hy (mapLinks_upFiltering hT (hl kv hkv) (hml kv hkv) (hent kv hkv).2 hd)
  · exact hy

-- ============================================================
-- Los hechos de las líneas de la máquina
-- ============================================================

/-- Las líneas de la máquina: bien formadas, contabilidad, claves únicas, estructura y `MapLinks`. -/
theorem line_facts (hbd : Bounded φ) : ∀ n : Nat,
    LineOk ((n : Int) + 1) (steps φ n (init φ)) ∧ (∀ kv ∈ steps φ n (init φ), EntOk kv) ∧
    ((steps φ n (init φ)).map (·.1)).Nodup ∧ Struct.LineStruct φ (steps φ n (init φ)) ∧
    (∀ kv ∈ steps φ n (init φ), MapLinks φ kv.2) := by
  intro n
  induction n with
  | zero =>
    obtain ⟨hl, hent, hnd, _⟩ := GPathB.lineInv_init φ
    refine ⟨by simpa [steps] using hl, fun kv hkv => (hent kv (by simpa [steps] using hkv)).1,
      by simpa [steps] using hnd, by simpa [steps] using Struct.lineStruct_init hbd, ?_⟩
    intro kv hkv
    have hkv' : kv ∈ init φ := by simpa [steps] using hkv
    rw [init_eq, List.mem_singleton] at hkv'
    subst hkv'
    exact mapLinks_initSeed
  | succ n ih =>
    obtain ⟨hl, he, hnd, hs, hml⟩ := ih
    rw [steps_succ]
    refine ⟨?_, advance_entOk (by omega) hl he, advance_nodup φ _, Struct.lineStruct_advance hbd hl hs,
      mapLinks_advance (by omega) hl he hml⟩
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact lineOk_advance hl

-- ============================================================
-- Una camarilla es una selección válida
-- ============================================================

theorem mapNodes_zero : mapNodes φ 0 = [⟨0, 0⟩] := by
  unfold mapNodes
  have := stepCount_pos φ
  simp only [show ¬ (0 : Int) < 0 by omega, if_false, show ¬ stepCount φ ≤ 0 by omega, if_true]

/-- **Una camarilla de un estado con la estructura de la máquina y `MapLinks` es una selección válida.** -/
theorem validSel_of_carried (hbd : Bounded φ) {g : GPathB} {S : Int → PathNodeId} (hs : Struct.Struct φ g)
    (hml : MapLinks φ g) (hc : Carried g S) (hpos : 0 < g.current_step) : ValidSel φ (g.current_step - 1) S := by
  refine ⟨fun j h0 h1 => hc.step j h0 (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n, hn, _, _⟩ := hc.node 0 (Int.le_refl 0) hpos
    rw [← node?_id hn]
    exact hml.2 n (node?_mem hn) (by rw [node?_id hn]; exact hc.step 0 (Int.le_refl 0) hpos)
  · intro j h0 h1
    obtain ⟨n, hn, hp, _⟩ := hc.node j (by omega) (by omega)
    have hpm : S (j - 1) ∈ n.parents := hp (by omega)
    have h1' := hs.pmp n (node?_mem hn) _ hpm
    have h2' := hs.gpmp n (node?_mem hn) _ hpm
    rw [node?_id hn] at h1' h2'
    have hS : S j = ⟨(S j).id, (S j).parent_id, (S j).gparent_id⟩ := rfl
    rw [hS]; unfold shiftPid
    rw [← h1', h2']
  · intro j h0 h1
    obtain ⟨n, hn, hp, _⟩ := hc.node j (by omega) (by omega)
    have := hml.1 n (node?_mem hn) _ (hp (by omega))
    rw [node?_id hn] at this; exact this
  · intro j h0 h1 r hr hr0 hr1
    exact Decode.reqSat_of_carried hbd hs hc j (by omega) (by omega) r hr hr0 (by omega)
  · intro j h0 h1
    obtain ⟨n, hn, _, _⟩ := hc.node j (by omega) (by omega)
    have := hs.noforb n (node?_mem hn)
    rw [node?_id hn] at this; exact this

-- ============================================================
-- CliqueSplit
-- ============================================================

/-- La llegada de `kv` a `d`. -/
abbrev arr (φ : Cnf) (kv : NodeId × GPathB) (d : NodeId) : GPathB := kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)

theorem valid_filter_of_arr {kv : NodeId × GPathB} {d : NodeId} (hv : (arr φ kv d).isValid = true) :
    (kv.2.filterAll (reqOf φ d)).isValid = true := by
  cases h : (kv.2.filterAll (reqOf φ d)).isValid
  · have : arr φ kv d = kv.2.filterAll (reqOf φ d) := by
      show kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ) = _
      unfold upFiltering up
      rw [if_neg (by rw [h]; simp)]
    rw [this, h] at hv
    exact absurd hv (by simp)
  · rfl

/-- **`CliqueSplit`**: en la unión de las llegadas de dos remitentes distintos de una línea de la máquina a un mismo
destino, toda camarilla es camarilla de una de las dos llegadas. -/
theorem cliqueSplit (hbd : Bounded φ) (n : Nat) {kv₁ kv₂ : NodeId × GPathB}
    (h₁ : kv₁ ∈ steps φ n (init φ)) (h₂ : kv₂ ∈ steps φ n (init φ)) {d : NodeId}
    (hd₁ : d ∈ sonsOfMap φ kv₁.1) (hd₂ : d ∈ sonsOfMap φ kv₂.1) {S : Int → PathNodeId}
    (hS : Carried (doJoin (arr φ kv₁ d) (arr φ kv₂ d)) S) :
    Carried (arr φ kv₁ d) S ∨ Carried (arr φ kv₂ d) S := by
  obtain ⟨hl, hent, hnd, hls, hml⟩ := line_facts hbd n
  by_cases hok : okJoin (arr φ kv₁ d) (arr φ kv₂ d) = true
  · have hj : doJoin (arr φ kv₁ d) (arr φ kv₂ d) = join (arr φ kv₁ d) (arr φ kv₂ d) := by
      unfold doJoin; rw [if_pos hok]
    rw [hj] at hS
    have hok' := hok
    unfold okJoin at hok'
    simp only [Bool.and_eq_true, beq_iff_eq] at hok'
    have hv₁ : (arr φ kv₁ d).isValid = true := hok'.1.2
    have hv₂ : (arr φ kv₂ d).isValid = true := hok'.2
    have ho₁ := hl kv₁ h₁
    have ho₂ := hl kv₂ h₂
    have hso₁ := stateOk_upFiltering ho₁ hd₁ hv₁
    have hso₂ := stateOk_upFiltering ho₂ hd₂ hv₂
    -- la unión: estructura y enlaces del mapa
    have hst : Struct.Struct φ (join (arr φ kv₁ d) (arr φ kv₂ d)) :=
      Struct.struct_join (Struct.struct_upFiltering hbd ho₁ (hls kv₁ h₁).1 (hls kv₁ h₁).2 hd₁)
        (Struct.struct_upFiltering hbd ho₂ (hls kv₂ h₂).1 (hls kv₂ h₂).2 hd₂)
    have hmu : MapLinks φ (join (arr φ kv₁ d) (arr φ kv₂ d)) :=
      mapLinks_join (mapLinks_upFiltering (by omega) ho₁ (hml kv₁ h₁) (hent kv₁ h₁).2 hd₁)
        (mapLinks_upFiltering (by omega) ho₂ (hml kv₂ h₂) (hent kv₂ h₂).2 hd₂)
    have hcs : (join (arr φ kv₁ d) (arr φ kv₂ d)).current_step = (n : Int) + 1 + 1 := hso₁.step
    have hv := validSel_of_carried hbd hst hmu hS (by omega)
    rw [hcs, show (n : Int) + 1 + 1 - 1 = (n : Int) + 1 by omega] at hv
    -- la cima de la camarilla es de d
    have htopd : (S ((n : Int) + 1)).id = d := by
      have htd : TopDocsId (join (arr φ kv₁ d) (arr φ kv₂ d)) d := by
        have hb₁ := below_of_shrinks (shrinks_filterAll kv₁.2 (reqOf φ d)) ho₁.below
        have hb₂ := below_of_shrinks (shrinks_filterAll kv₂.2 (reqOf φ d)) ho₂.below
        have ht₁ : TopDocsId (arr φ kv₁ d) d := by
          show TopDocsId (kv₁.2.upFiltering (reqOf φ d) d "" (isProhibited φ)) d
          unfold upFiltering up
          rw [if_pos (valid_filter_of_arr hv₁)]
          exact topDocsId_of_shrinks (shrinks_review _) (topDocsId_addNode hb₁)
        have ht₂ : TopDocsId (arr φ kv₂ d) d := by
          show TopDocsId (kv₂.2.upFiltering (reqOf φ d) d "" (isProhibited φ)) d
          unfold upFiltering up
          rw [if_pos (valid_filter_of_arr hv₂)]
          exact topDocsId_of_shrinks (shrinks_review _) (topDocsId_addNode hb₂)
        exact topDocsId_join ht₁ ht₂ (hso₁.step.trans hso₂.step.symm)
      obtain ⟨m, hm, _, _⟩ := hS.node ((n : Int) + 1) (by omega) (by rw [hcs]; omega)
      have := htd m (node?_mem hm) (by rw [node?_id hm, hv.step _ (by omega) (Int.le_refl _), hcs]; omega)
      rw [node?_id hm] at this; exact this
    -- el remitente de la camarilla es uno de los dos
    have hSn : S n ∈ (join (arr φ kv₁ d) (arr φ kv₂ d)).alive := hS.alive n (by omega) (by rw [hcs]; omega)
    have hon₁ := originIn_upFiltering (φ := φ) ho₁ (hent kv₁ h₁).2 hd₁
    have hon₂ := originIn_upFiltering (φ := φ) ho₂ (hent kv₂ h₂).2 hd₂
    have hns : (S n).id.step = (n : Int) + 1 - 1 := by rw [hv.step n (by omega) (by omega)]; omega
    -- la completitud y la llegada
    obtain ⟨_, g0, hf, hc0⟩ := steps_has_sel n (hv.mono (by omega))
    have hmem := List.mem_of_find?_eq_some hf
    have hdS : (S ((n : Int) + 1)).id ∈ sonsOfMap φ (S n).id := by
      have := hv.son ((n : Int) + 1) (by omega) (Int.le_refl _)
      simpa using this
    have hsd : S ((n : Int) + 1) = S ((n : Int) + 1) := rfl
    rcases (alive_join _ _ _).mp hSn with ha | ha
    · have hid : (S n).id = kv₁.1 := hon₁ _ ha hns
      have hkv : ((S n).id, g0) = kv₁ := eq_of_nodup_keys hnd hmem h₁ hid
      have hc1 : Carried kv₁.2 S := by rw [← hkv]; exact hc0
      have hok1 : StateOk ((n : Int) + 1) (S n).id kv₁.2 := by rw [hid]; exact ho₁
      have := carried_arrival (by omega) hv hok1 hc1
      rw [htopd] at this
      exact Or.inl this
    · have hid : (S n).id = kv₂.1 := hon₂ _ ha hns
      have hkv : ((S n).id, g0) = kv₂ := eq_of_nodup_keys hnd hmem h₂ hid
      have hc2 : Carried kv₂.2 S := by rw [← hkv]; exact hc0
      have hok2 : StateOk ((n : Int) + 1) (S n).id kv₂.2 := by rw [hid]; exact ho₂
      have := carried_arrival (by omega) hv hok2 hc2
      rw [htopd] at this
      exact Or.inr this
  · have hj : doJoin (arr φ kv₁ d) (arr φ kv₂ d) = arr φ kv₁ d := by unfold doJoin; rw [if_neg hok]
    rw [hj] at hS
    exact Or.inl hS

end CliqueSplit

end AbsSatBingo.Model
