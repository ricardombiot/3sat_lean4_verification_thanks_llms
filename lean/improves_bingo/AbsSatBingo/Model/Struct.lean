-- lean/improves_bingo/AbsSatBingo/Model/Struct.lean
import AbsSatBingo.Model.Machine

/-!
# Invariantes estructurales (fase L7, parte 1)

Lo que la decodificación de una camarilla necesita de un estado, y que la máquina y el lector conservan:

* `PMP` / `GPMP` — el id de un nodo declara a su padre y a su abuelo: todo padre `p` de `n` tiene
  `p.id = n.id.parent_id`, y `n.id.gparent_id = p.parent_id` (como `ParentId` de `improves_bin`);
* `NoForb` — ningún nodo es una ventana prohibida;
* `OnMap` — todo nodo está sobre un nodo del mapa de su paso;
* `ReqEdges` — **los requisitos, como invariante de aristas**: si `x` posee a otro `w` que está en el paso de un
  requisito `r` de `x`, entonces `w` está en `r`. Es la forma en grafo del filtro por requisitos: la arista
  nace después del filtro (`create_from_parents!` solo enlaza con vivos filtrados), y el review solo borra.

Todo lo que solo borra los conserva (`struct_of_sub`); el UP (`struct_addNode`) y el join (`struct_join`) también.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace Struct

open GPathB Driver Machine

variable (φ : Cnf)

structure Struct (g : GPathB) : Prop where
  pmp    : ∀ n ∈ g.nodes, ∀ p ∈ n.parents, some p.id = n.id.parent_id
  gpmp   : ∀ n ∈ g.nodes, ∀ p ∈ n.parents, n.id.gparent_id = p.parent_id
  noforb : ∀ n ∈ g.nodes, isProhibited φ n.id = false
  onmap  : ∀ n ∈ g.nodes, n.id.id ∈ mapNodes φ n.id.id.step
  req    : ∀ x w, g.Adj x w → x ≠ w → ∀ r ∈ reqOf φ x.id, w.id.step = r.step → w.id = r

variable {φ}

/-- **Todo lo que solo borra conserva la estructura.** -/
theorem struct_of_sub {h g : GPathB} (hs : Sub h g) (hg : Struct φ g) : Struct φ h := by
  refine ⟨?_, ?_, ?_, ?_, fun x w hx hne r hr hw => hg.req x w (hs.adj x w hx) hne r hr hw⟩
  · intro n hn p hp
    obtain ⟨m, hm, hid, hpar, _⟩ := hs.nodes n hn
    rw [← hid]; exact hg.pmp m hm p (hpar p hp)
  · intro n hn p hp
    obtain ⟨m, hm, hid, hpar, _⟩ := hs.nodes n hn
    rw [← hid]; exact hg.gpmp m hm p (hpar p hp)
  · intro n hn
    obtain ⟨m, hm, hid, _, _⟩ := hs.nodes n hn
    rw [← hid]; exact hg.noforb m hm
  · intro n hn
    obtain ⟨m, hm, hid, _, _⟩ := hs.nodes n hn
    rw [← hid]; exact hg.onmap m hm

-- ============================================================
-- El filtro por requisitos deja solo el nodo requerido en su paso
-- ============================================================

theorem review_of_invalid {g : GPathB} (h : g.isValid = false) : g.review = g := by
  unfold review
  simp only [reviewFuel, h, Bool.false_and, Bool.false_eq_true, if_false]

/-- Tras `filterAll g [r]` válido, todo vivo del paso de `r` está en `r`. -/
theorem filtered_filterAll {g : GPathB} (hdocs : AliveDocs g) (reqs : List NodeId) (hlen : reqs.length ≤ 1)
    (hv : (g.filterAll reqs).isValid = true) :
    ∀ q ∈ (g.filterAll reqs).alive, ∀ r ∈ reqs, q.id.step = r.step → q.id = r := by
  intro q hq r hr hqs
  match reqs, hlen, hr with
  | [], _, hr => exact absurd hr List.not_mem_nil
  | _ :: _ :: _, hlen, _ => simp at hlen
  | [r'], _, hr =>
    rw [List.mem_singleton] at hr
    subst hr
    have hsub := (shrinks_review (g.filterRequire r)).1
    have hq' := hsub.alive q hq
    unfold filterRequire at hq'
    by_cases hgv : g.isValid = true
    · rw [if_pos hgv] at hq'
      dsimp only at hq'
      have hq2 : q ∈ ((((g.line r.step).map (·.id)).filter (fun q => q.id != r)).foldl killVertex g).alive := hq'
      rw [alive_foldl_killVertex] at hq2
      obtain ⟨hqg, hnot⟩ := List.mem_filter.mp hq2
      by_cases hne : q.id = r
      · exact hne
      · exfalso
        obtain ⟨n, hn, hnid⟩ := hdocs q hqg
        have hin : q ∈ ((g.line r.step).map (·.id)).filter (fun q => q.id != r) :=
          List.mem_filter.mpr ⟨List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨hn, by rw [hnid, hqs]; simp⟩, hnid⟩,
            bne_iff_ne.mpr hne⟩
        have hc : (((g.line r.step).map (·.id)).filter (fun q => q.id != r)).contains q = true :=
          List.contains_iff_mem.mpr hin
        rw [hc] at hnot
        exact Bool.noConfusion hnot
    · exfalso
      have hgv' : g.isValid = false := by simpa using hgv
      unfold filterAll at hv
      simp only [List.foldl_cons, List.foldl_nil] at hv
      unfold filterRequire at hv
      rw [if_neg hgv, review_of_invalid hgv'] at hv
      rw [hgv'] at hv
      exact Bool.noConfusion hv

-- ============================================================
-- El UP y el join
-- ============================================================

theorem alive_step_lt {g : GPathB} (hdocs : AliveDocs g) (hb : Below g) :
    ∀ q ∈ g.alive, q.id.step < g.current_step := by
  intro q hq
  obtain ⟨n, hn, rfl⟩ := hdocs q hq
  exact hb n hn

theorem struct_addNode (hbd : Bounded φ) {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (hg : Struct φ g) (hd : d ∈ mapNodes φ d.step) (hdstep : d.step = g.current_step)
    (hnf : ∀ pid ∈ g.newRowIds d forb, isProhibited φ pid = false)
    (hfilt : ∀ q ∈ g.alive, ∀ r ∈ reqOf φ d, q.id.step = r.step → q.id = r)
    (hlt : ∀ q ∈ g.alive, q.id.step < g.current_step) :
    Struct φ (g.addNode d title forb) := by
  have hnodes : ∀ n ∈ (g.addNode d title forb).nodes,
      (∃ m ∈ g.nodes, n.id = m.id ∧ n.parents = m.parents) ∨
      (∃ pid ∈ g.newRowIds d forb, n = g.rowNode d title pid) := by
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      exact Or.inl ⟨m, hm, rfl, rfl⟩
    · obtain ⟨pid, hpid, rfl⟩ := List.mem_map.mp hn
      exact Or.inr ⟨pid, hpid, rfl⟩
  have hrow : ∀ pid, ∀ p ∈ g.rowParents d pid, shiftPid p d = pid := by
    intro pid p hp
    simpa using (List.mem_filter.mp hp).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn p hp
    rcases hnodes n hn with ⟨m, hm, hid, hpar⟩ | ⟨pid, _, rfl⟩
    · rw [hid]; rw [hpar] at hp; exact hg.pmp m hm p hp
    · rw [← hrow pid p hp]; rfl
  · intro n hn p hp
    rcases hnodes n hn with ⟨m, hm, hid, hpar⟩ | ⟨pid, _, rfl⟩
    · rw [hid]; rw [hpar] at hp; exact hg.gpmp m hm p hp
    · show pid.gparent_id = _
      rw [← hrow pid p hp]; rfl
  · intro n hn
    rcases hnodes n hn with ⟨m, hm, hid, _⟩ | ⟨pid, hpid, rfl⟩
    · rw [hid]; exact hg.noforb m hm
    · exact hnf pid hpid
  · intro n hn
    rcases hnodes n hn with ⟨m, hm, hid, _⟩ | ⟨pid, hpid, rfl⟩
    · rw [hid]; exact hg.onmap m hm
    · show pid.id ∈ mapNodes φ pid.id.step
      rw [mapId_of_mem_shiftRowIds (List.mem_filter.mp hpid).1]; exact hd
  · intro x w hx hne r hr hw
    rw [adj_iff] at hx
    rcases hx with ⟨hxw, _⟩ | ⟨e, he, hj⟩
    · exact absurd hxw hne
    · rcases List.mem_append.mp he with he | he
      · exact hg.req x w (by rw [adj_iff]; exact Or.inr ⟨e, he, hj⟩) hne r hr hw
      · obtain ⟨pid, hpid, he'⟩ := List.mem_flatMap.mp he
        obtain ⟨w', hw', rfl⟩ := List.mem_map.mp he'
        have hpidd : pid.id = d := mapId_of_mem_shiftRowIds (List.mem_filter.mp hpid).1
        have hw'a := (List.mem_filter.mp hw').1
        rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- x es el nodo nuevo: sus requisitos son los del filtro
          simp only at h1 h2
          subst h1; subst h2
          rw [hpidd] at hr
          exact hfilt w' hw'a r hr hw
        · -- x es viejo: sus requisitos están por debajo de él, y el nuevo está en el paso nuevo
          simp only at h1 h2
          subst h1; subst h2
          have hback := reqOf_backward φ hbd _ r hr
          have hxlt := hlt _ hw'a
          rw [hpidd, hdstep] at hw
          omega

theorem struct_join {g₁ g₂ : GPathB} (h₁ : Struct φ g₁) (h₂ : Struct φ g₂) : Struct φ (join g₁ g₂) := by
  have hnodes : ∀ n ∈ (join g₁ g₂).nodes,
      (∃ m ∈ g₁.nodes, n.id = m.id ∧ ∀ p ∈ n.parents, p ∈ m.parents ∨
        ∃ m' ∈ g₂.nodes, m'.id = m.id ∧ p ∈ m'.parents) ∨ n ∈ g₂.nodes := by
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      refine Or.inl ⟨m, hm, by split <;> rfl, ?_⟩
      intro p hp
      split at hp
      · rename_i m' hm'
        rcases List.mem_append.mp hp with hp | hp
        · exact Or.inl hp
        · exact Or.inr ⟨m', node?_mem hm', node?_id hm', (List.mem_filter.mp hp).1⟩
      · exact Or.inl hp
    · exact Or.inr (List.mem_filter.mp hn).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn p hp
    rcases hnodes n hn with ⟨m, hm, hid, hpar⟩ | hn2
    · rw [hid]
      rcases hpar p hp with hp | ⟨m', hm', hid', hp'⟩
      · exact h₁.pmp m hm p hp
      · rw [← hid']; exact h₂.pmp m' hm' p hp'
    · exact h₂.pmp n hn2 p hp
  · intro n hn p hp
    rcases hnodes n hn with ⟨m, hm, hid, hpar⟩ | hn2
    · rw [hid]
      rcases hpar p hp with hp | ⟨m', hm', hid', hp'⟩
      · exact h₁.gpmp m hm p hp
      · rw [← hid']; exact h₂.gpmp m' hm' p hp'
    · exact h₂.gpmp n hn2 p hp
  · intro n hn
    rcases hnodes n hn with ⟨m, hm, hid, _⟩ | hn2
    · rw [hid]; exact h₁.noforb m hm
    · exact h₂.noforb n hn2
  · intro n hn
    rcases hnodes n hn with ⟨m, hm, hid, _⟩ | hn2
    · rw [hid]; exact h₁.onmap m hm
    · exact h₂.onmap n hn2
  · intro x w hx hne r hr hw
    rw [adj_iff] at hx
    rcases hx with ⟨hxw, _⟩ | ⟨e, he, hj⟩
    · exact absurd hxw hne
    · rcases List.mem_append.mp he with he | he
      · exact h₁.req x w (by rw [adj_iff]; exact Or.inr ⟨e, he, hj⟩) hne r hr hw
      · exact h₂.req x w (by rw [adj_iff]; exact Or.inr ⟨e, (List.mem_filter.mp he).1, hj⟩) hne r hr hw

theorem struct_doJoin {g₁ g₂ : GPathB} (h₁ : Struct φ g₁) (h₂ : Struct φ g₂) : Struct φ (doJoin g₁ g₂) := by
  unfold doJoin; split
  · exact struct_join h₁ h₂
  · exact h₁

-- ============================================================
-- La máquina
-- ============================================================

/-- Todo estado de la línea tiene la estructura, y su clave está en el mapa. -/
def LineStruct (φ : Cnf) (line : Line) : Prop :=
  ∀ kv ∈ line, Struct φ kv.2 ∧ kv.1 ∈ mapNodes φ kv.1.step

theorem struct_upFiltering (hbd : Bounded φ) {T : Int} {key d : NodeId} {g : GPathB} (hok : StateOk T key g)
    (hg : Struct φ g) (hkey : key ∈ mapNodes φ key.step) (hd : d ∈ sonsOfMap φ key) :
    Struct φ (g.upFiltering (reqOf φ d) d "" (isProhibited φ)) := by
  have hs := shrinks_filterAll g (reqOf φ d)
  have hg1 : Struct φ (g.filterAll (reqOf φ d)) := struct_of_sub hs.1 hg
  have hdocs1 := aliveDocs_filterAll hok.docs (reqOf φ d)
  have hb1 := below_of_shrinks hs hok.below
  have hdmap : d ∈ mapNodes φ d.step := by
    have := sonsOfMap_subset φ key hkey d hd
    rwa [sonsOfMap_step φ key d hd]
  have hdstep : d.step = (g.filterAll (reqOf φ d)).current_step := by
    rw [sonsOfMap_step φ key d hd, hok.key, step_of_shrinks hs, hok.step]; omega
  unfold upFiltering up
  split
  · rename_i hv1
    refine struct_of_sub (shrinks_review _).1 (struct_addNode hbd hg1 hdmap hdstep ?_ ?_
      (alive_step_lt hdocs1 hb1))
    · intro pid hpid
      simpa using (List.mem_filter.mp hpid).2
    · exact filtered_filterAll hok.docs _ (reqOf_length_le_one φ d) hv1
  · exact hg1

theorem lineStruct_insert {line : Line} {key : NodeId} {g : GPathB} (hl : LineStruct φ line)
    (hg : Struct φ g) (hkey : key ∈ mapNodes φ key.step) : LineStruct φ (Driver.insert line key g) := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have hkey' : key' = key := by simpa using List.find?_some hfind
    subst hkey'
    have he := (hl _ (List.mem_of_find?_eq_some hfind)).1
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact ⟨struct_doJoin he hg, hkey⟩
    · exact hl kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton] at h; subst h; exact ⟨hg, hkey⟩

theorem lineStruct_advance (hbd : Bounded φ) {T : Int} {line : Line} (hl : LineOk T line)
    (hs : LineStruct φ line) : LineStruct φ (advance φ line) := by
  unfold advance
  refine foldl_pres _ (LineStruct φ) _ (fun next kv hkv hn => ?_) _ (fun _ h => absurd h List.not_mem_nil)
  unfold sendAll
  refine foldl_pres _ (LineStruct φ) _ (fun y d hd hy => ?_) _ hn
  unfold sendTo
  dsimp only
  split
  · have hdmap : d ∈ mapNodes φ d.step := by
      have := sonsOfMap_subset φ kv.1 (hs kv hkv).2 d hd
      rwa [sonsOfMap_step φ kv.1 d hd]
    exact lineStruct_insert hy (struct_upFiltering hbd (hl kv hkv) (hs kv hkv).1 (hs kv hkv).2 hd) hdmap
  · exact hy

theorem isL3_zero : isL3 φ 0 = false := by
  unfold isL3 midFusion
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  left; left; omega

theorem lineStruct_init (hbd : Bounded φ) : LineStruct φ (init φ) := by
  rw [init_eq]
  intro kv hkv
  rw [List.mem_singleton] at hkv
  subst hkv
  have hmap : (⟨0, 0⟩ : NodeId) ∈ mapNodes φ 0 := by
    unfold mapNodes
    have := stepCount_pos φ
    simp [show ¬ stepCount φ ≤ 0 by omega]
  refine ⟨?_, hmap⟩
  unfold initSeed up
  rw [if_pos (show GPathB.empty.isValid = true by rfl)]
  show Struct φ (GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)).review
  refine struct_of_sub (shrinks_review _).1
    (struct_addNode (g := GPathB.empty) (title := "") (forb := fun _ => false) hbd ?_ hmap rfl ?_ ?_ ?_)
  · exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
      fun x w hx hne => by
        rw [adj_iff] at hx
        rcases hx with ⟨h, _⟩ | ⟨e, he, _⟩
        · exact absurd h hne
        · exact absurd he List.not_mem_nil⟩
  · intro pid hpid
    have hpid' := (List.mem_filter.mp hpid).1
    unfold shiftRowIds at hpid'
    rw [if_neg (by show ¬ (0 : Int) < 0; omega)] at hpid'
    rw [List.mem_singleton] at hpid'
    subst hpid'
    unfold isProhibited
    rw [show ({ id := ⟨0, 0⟩, parent_id := none, gparent_id := none } : PathNodeId).id.step = 0 from rfl,
      isL3_zero]
    rfl
  · intro q hq; exact absurd hq List.not_mem_nil
  · intro q hq; exact absurd hq List.not_mem_nil

theorem lineStruct_steps (hbd : Bounded φ) :
    ∀ (n : Nat) (T : Int) (line : Line), LineOk T line → LineStruct φ line → LineStruct φ (steps φ n line) := by
  intro n
  induction n with
  | zero => intro _ _ _ hs; exact hs
  | succ n ih =>
    intro T line hl hs
    exact ih (T + 1) _ (lineOk_advance hl) (lineStruct_advance hbd hl hs)

/-- **Todo estado de la línea final tiene la estructura.** -/
theorem struct_run (hbd : Bounded φ) : ∀ kv ∈ run φ, Struct φ kv.2 := by
  intro kv hkv
  have hl := (init_inv φ (fun _ => false)).1
  exact (lineStruct_steps hbd _ 1 (init φ) hl (lineStruct_init hbd) kv hkv).1

-- ============================================================
-- El lector
-- ============================================================

/-- Todo estado que visita el lector está por debajo del de partida. -/
theorem shrinks_visited {g₀ h : GPathB} (hv : Visited g₀ h) : Shrinks h g₀ := by
  induction hv with
  | start => exact (shrinks_review _).trans (shrinks_dirty g₀ true)
  | pin q _ ih => exact (shrinks_filterAll _ [q.id]).trans ih

theorem struct_visited {g₀ h : GPathB} (hv : Visited g₀ h) (hg : Struct φ g₀) : Struct φ h :=
  struct_of_sub (shrinks_visited hv).1 hg

end Struct

end AbsSatBingo.Model
