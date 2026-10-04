-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnLine.lean
import AbsSatBingo.Model.ForbidOnMachine
import AbsSatBingo.Model.LineInduction
import AbsSatBingo.Model.Struct
import AbsSatBingo.Model.LiveExt
import AbsSatBingo.Model.Decode

/-!
# Los invariantes de forma de la línea `:on` (`docs/plans/lean_forbid_on.md`, F3)

Las operaciones `:on` son, sobre el grafo, las de `:off` más cortes de aristas (primitivas de `RevPrims`) y
cambios de tríos (que ningún invariante de forma mira). Así los invariantes de forma de la línea `:off` (`BK`,
`LinksInv`, `Struct`) valen también en la línea `:on`, con las mismas piezas de `addNode` y `join`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

-- ============================================================
-- El review `:on` borra
-- ============================================================

theorem shrinks_setT (g : GPathB) (T : List (PathNodeId × PathNodeId × PathNodeId)) : Shrinks (g.setT T) g :=
  ⟨⟨rfl, rfl, fun _ h => h, fun _ _ h => h, fun n hn => ⟨n, hn, rfl, fun _ h => h, fun _ h => h⟩⟩, Nat.le_refl _⟩

theorem shrinks_forbidRound (g : GPathB) : Shrinks g.forbidRound.1 g := by
  simp only [forbidRound]
  obtain ⟨T', hT⟩ := addTrios_eq g (Idx.of g) (g.newTrios (Idx.of g))
  rw [hT]
  split
  · exact shrinks_setT g T'
  · refine (shrinks_clean _).trans ((shrinks_dirty _ true).trans ?_)
    exact (shrinks_foldl (fun (h : GPathB) (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2)
      (fun g e => shrinks_removeEdge g e.1 e.2) _ _).trans (shrinks_setT g T')

theorem shrinks_forbidFuel : ∀ (n : Nat) (g : GPathB), Shrinks (forbidFuel n g) g := by
  intro n
  induction n with
  | zero => intro g; exact Shrinks.refl g
  | succ n ih =>
    intro g
    unfold forbidFuel
    split
    · simp only
      split
      · exact (ih _).trans (shrinks_forbidRound g)
      · exact shrinks_forbidRound g
    · exact Shrinks.refl g

theorem shrinks_reviewPassOn (g : GPathB) : Shrinks g.reviewPassOn g :=
  (shrinks_pruneLinks _).trans ((shrinks_reviewSons _).trans ((shrinks_reviewParents _).trans
    ((shrinks_pruneLinks _).trans ((shrinks_forbidFuel _ _).trans (shrinks_cleanPair g)))))

theorem shrinks_reviewOn (g : GPathB) : Shrinks g.reviewOn g :=
  reviewFuelOn_pres (fun x => Shrinks x g)
    (fun x hx => (shrinks_reviewPassOn _).trans ((shrinks_dirty x false).trans hx))
    (fun x hx => (shrinks_finalPass x).trans hx) _ g (Shrinks.refl g)

theorem shrinks_filterAllOn (g : GPathB) (reqs : List NodeId) : Shrinks (g.filterAllOn reqs) g :=
  (shrinks_reviewOn _).trans (shrinks_foldl filterRequire shrinks_filterRequire reqs g)

theorem reviewOn_invalid {g : GPathB} (hv : g.isValid = false) : g.reviewOn = g := by
  unfold reviewOn
  cases h : g.measure + 1 with
  | zero => omega
  | succ n => rw [reviewFuelOn.eq_2, if_neg (by simp [hv])]

/-- **El filtro `:on` fija el paso de su requisito** (con a lo sumo un requisito). -/
theorem filtered_filterAllOn {g : GPathB} (hdocs : AliveDocs g) (reqs : List NodeId) (hlen : reqs.length ≤ 1)
    (hv : (g.filterAllOn reqs).isValid = true) :
    ∀ q ∈ (g.filterAllOn reqs).alive, ∀ r ∈ reqs, q.id.step = r.step → q.id = r := by
  intro q hq r hr hqs
  match reqs, hlen, hr with
  | [], _, hr => exact absurd hr List.not_mem_nil
  | _ :: _ :: _, hlen, _ => simp at hlen
  | [r'], _, hr =>
    rw [List.mem_singleton] at hr
    subst hr
    have hsub := (shrinks_reviewOn (g.filterRequire r)).1
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
      unfold filterAllOn at hv
      have hfr : [r].foldl filterRequire g = g := by
        simp only [List.foldl_cons, List.foldl_nil]
        unfold filterRequire; rw [if_neg hgv]
      rw [hfr, reviewOn_invalid hgv'] at hv
      rw [hgv'] at hv; cases hv

end GPathB

namespace MachineOn

open GPathB Driver Machine Struct

variable {φ : Cnf}

/-- **La forma de una entrada**: contabilidad, enlaces, estructura, y su clave en el mapa. -/
def ShapeOn (φ : Cnf) (key : NodeId) (g : GPathB) : Prop :=
  BK g ∧ LinksInv g ∧ Struct φ g ∧ key ∈ mapNodes φ key.step

def LineShape (φ : Cnf) (line : Line) : Prop := ∀ kv ∈ line, ShapeOn φ kv.1 kv.2

theorem mapNodes_nonneg (φ : Cnf) (d : NodeId) (h : d ∈ mapNodes φ d.step) : 0 ≤ d.step := by
  by_cases hn : d.step < 0
  · unfold mapNodes at h
    rw [if_pos hn] at h
    exact absurd h List.not_mem_nil
  · omega

theorem struct_setT {g : GPathB} (h : Struct φ g) (T : List (PathNodeId × PathNodeId × PathNodeId)) :
    Struct φ (g.setT T) := ⟨h.pmp, h.gpmp, h.noforb, h.onmap, h.req⟩

theorem bk_reviewOn {g : GPathB} (h : BK g) : BK g.reviewOn :=
  ⟨revPrims_reviewOn revPrims_nodupIds trioBlind_nodupIds _ h.1,
   revPrims_reviewOn revPrims_edgesAlive trioBlind_edgesAlive _ h.2.1,
   revPrims_reviewOn revPrims_linksStep trioBlind_linksStep _ h.2.2.1,
   revPrims_reviewOn revPrims_aboveZero trioBlind_aboveZero _ h.2.2.2⟩

theorem bk_filterAllOn {g : GPathB} (h : BK g) (reqs : List NodeId) : BK (g.filterAllOn reqs) :=
  ⟨revPrims_filterAllOn revPrims_nodupIds trioBlind_nodupIds _ _ h.1,
   revPrims_filterAllOn revPrims_edgesAlive trioBlind_edgesAlive _ _ h.2.1,
   revPrims_filterAllOn revPrims_linksStep trioBlind_linksStep _ _ h.2.2.1,
   revPrims_filterAllOn revPrims_aboveZero trioBlind_aboveZero _ _ h.2.2.2⟩

/-- **El UP `:on` desde un estado válido** conserva la forma. -/
theorem shape_upOn (hbd : Bounded φ) {g : GPathB} {d : NodeId} (hv : g.isValid = true) (hbk : BK g)
    (hli : LinksInv g) (hst : Struct φ g) (hb : Machine.Below g) (hdocs : AliveDocs g)
    (hdmap : d ∈ mapNodes φ d.step) (hds : d.step = g.current_step) (hd0 : 0 ≤ d.step)
    (hnf : ∀ pid ∈ g.newRowIds d (isProhibited φ), isProhibited φ pid = false)
    (hfilt : ∀ q ∈ g.alive, ∀ r ∈ reqOf φ d, q.id.step = r.step → q.id = r) :
    ShapeOn φ d (g.upOn d "" (isProhibited φ)) := by
  obtain ⟨T', hT⟩ := upOn_eq (d := d) (title := "") (forb := isProhibited φ) hv
  rw [hT]
  let a := g.addNode d "" (isProhibited φ)
  have hbka : BK a := ⟨nodupIds_addNode hbk.1 hb hds, edgesAlive_addNode hbk.2.1, linksStep_addNode hbk.2.2.1 hds,
    aboveZero_addNode hbk.2.2.2 hd0⟩
  have hlia : LinksInv a := linksInv_addNode hli hb hbk.2.2.2 hds
  have hsta : Struct φ a := struct_addNode hbd hst hdmap hds hnf hfilt (alive_step_lt hdocs hb)
  exact ⟨bk_reviewOn (g := a.setT T') hbka,
    revPrims_reviewOn revPrims_linksInv trioBlind_linksInv _ (show LinksInv (a.setT T') from hlia),
    struct_of_sub (shrinks_reviewOn _).1 (struct_setT hsta T'), hdmap⟩

theorem shape_upFilteringOn (hbd : Bounded φ) {T : Int} {key d : NodeId} {g : GPathB} (hok : StateOk T key g)
    (hg : ShapeOn φ key g) (hd : d ∈ sonsOfMap φ key)
    (hv : (g.upFilteringOn (reqOf φ d) d "" (isProhibited φ)).isValid = true) :
    ShapeOn φ d (g.upFilteringOn (reqOf φ d) d "" (isProhibited φ)) := by
  let g1 := g.filterAllOn (reqOf φ d)
  have hs1 := shrinks_filterAllOn g (reqOf φ d)
  have hv1 : g1.isValid = true := by
    by_cases hn : g1.isValid = true
    · exact hn
    · unfold upFilteringOn upOn at hv
      rw [if_neg hn] at hv
      exact absurd hv hn
  have hdmap : d ∈ mapNodes φ d.step := by
    have := sonsOfMap_subset φ key hg.2.2.2 d hd
    rwa [sonsOfMap_step φ key d hd]
  have hdstep : d.step = g1.current_step := by
    rw [sonsOfMap_step φ key d hd, hok.key, step_filterAllOn, hok.step]; omega
  have hb1 : Machine.Below g1 := below_filterAllOn hok.below _
  have hdocs1 : AliveDocs g1 := docs_filterAllOn hok.docs _
  exact shape_upOn hbd hv1 (bk_filterAllOn hg.1 _) (revPrims_filterAllOn revPrims_linksInv trioBlind_linksInv _ _ hg.2.1)
    (struct_of_sub hs1.1 hg.2.2.1) hb1 hdocs1 hdmap hdstep (mapNodes_nonneg φ d hdmap)
    (fun pid hpid => by simpa using (List.mem_filter.mp hpid).2)
    (filtered_filterAllOn hok.docs _ (reqOf_length_le_one φ d) hv1)

theorem shape_doJoinOn {key : NodeId} {e g : GPathB} (he : ShapeOn φ key e) (hg : ShapeOn φ key g) :
    ShapeOn φ key (doJoinOn e g) := by
  unfold doJoinOn
  split
  · obtain ⟨T', hT⟩ := joinOn_eq e g
    rw [hT]
    exact ⟨⟨nodupIds_join he.1.1 hg.1.1, edgesAlive_join he.1.2.1 hg.1.2.1, linksStep_join he.1.2.2.1 hg.1.2.2.1,
      aboveZero_join he.1.2.2.2 hg.1.2.2.2⟩, linksInv_join he.2.1 hg.2.1 he.1.2.1 hg.1.2.1,
      struct_setT (struct_join he.2.2.1 hg.2.2.1) T', he.2.2.2⟩
  · exact he

theorem lineShape_insertM {line : Line} {key : NodeId} {g : GPathB} (hl : LineShape φ line)
    (hg : ShapeOn φ key g) : LineShape φ (insertM .on line key g) := by
  unfold insertM
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    subst hkey
    have he := hl _ (List.mem_of_find?_eq_some hfind)
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact shape_doJoinOn he hg
    · exact hl kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton] at h; subst h; exact hg

theorem lineShape_advance (hbd : Bounded φ) {T : Int} {line : Line} (hl : LineOn T line) (hs : LineShape φ line) :
    LineShape φ (advanceM .on φ line) := by
  unfold advanceM
  refine foldl_pres _ (LineShape φ) _ (fun next kv hkv hn => ?_) _ (fun _ h => absurd h List.not_mem_nil)
  unfold sendAllM
  refine foldl_pres _ (LineShape φ) _ (fun y d hd hy => ?_) _ hn
  unfold sendToM
  dsimp only
  split
  · rename_i hv
    exact lineShape_insertM hy (shape_upFilteringOn hbd (hl kv hkv).1 (hs kv hkv) hd hv)
  · exact hy

theorem empty_shape0 : BK GPathB.empty ∧ LinksInv GPathB.empty ∧ Struct φ GPathB.empty := by
  have hadj : ∀ x w, ¬ GPathB.empty.Adj x w := by
    intro x w h; unfold Adj adjb isAlive hasEdge at h; simp [GPathB.empty] at h
  refine ⟨⟨?_, fun y w h => absurd h (hadj y w), fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩, ⟨fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩,
    ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
      fun x w hx _ => absurd hx (hadj x w)⟩⟩
  unfold NodupIds; simp [GPathB.empty]

theorem lineShape_init (hbd : Bounded φ) : LineShape φ (initM .on φ) := by
  rw [initM_eq]
  intro kv hkv
  rw [List.mem_singleton] at hkv
  subst hkv
  have hmap : (⟨0, 0⟩ : NodeId) ∈ mapNodes φ 0 := by
    unfold mapNodes
    have := stepCount_pos φ
    simp [show ¬ stepCount φ ≤ 0 by omega]
  obtain ⟨hbk, hli, hst⟩ := (empty_shape0 (φ := φ))
  show ShapeOn φ ⟨0, 0⟩ (GPathB.empty.upOn ⟨0, 0⟩ "" (fun _ => false))
  obtain ⟨T', hT⟩ := upOn_eq (g := GPathB.empty) (d := ⟨0, 0⟩) (title := "") (forb := fun _ => false) rfl
  rw [hT]
  let a := GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)
  have hb0 : Machine.Below GPathB.empty := fun _ h => absurd h List.not_mem_nil
  have hbka : BK a := ⟨nodupIds_addNode hbk.1 hb0 rfl, edgesAlive_addNode hbk.2.1, linksStep_addNode hbk.2.2.1 rfl,
    aboveZero_addNode hbk.2.2.2 (by show (0 : Int) ≤ 0; omega)⟩
  have hlia : LinksInv a := linksInv_addNode hli hb0 hbk.2.2.2 rfl
  have hsta : Struct φ a := by
    refine struct_addNode (g := GPathB.empty) (title := "") (forb := fun _ => false) hbd hst hmap rfl ?_ ?_ ?_
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
  exact ⟨bk_reviewOn (g := a.setT T') hbka,
    revPrims_reviewOn revPrims_linksInv trioBlind_linksInv _ (show LinksInv (a.setT T') from hlia),
    struct_of_sub (shrinks_reviewOn _).1 (struct_setT hsta T'), hmap⟩

/-- **La forma en toda la línea `:on`.** -/
theorem lineOnShape_steps (hbd : Bounded φ) :
    ∀ (n : Nat) (T : Int) (line : Line), LineOn T line → LineShape φ line →
      LineOn (T + n) (stepsM .on φ n line) ∧ LineShape φ (stepsM .on φ n line) := by
  intro n
  induction n with
  | zero => intro T line hl hs; simp only [stepsM]; exact ⟨by simpa using hl, hs⟩
  | succ n ih =>
    intro T line hl hs
    simp only [stepsM]
    have := ih (T + 1) _ (lineOn_advance hl) (lineShape_advance hbd hl hs)
    rw [show T + 1 + (n : Int) = T + ((n + 1 : Nat) : Int) by push_cast; omega] at this
    exact this

theorem lineOn_run_shape (hbd : Bounded φ) :
    LineOn (stepCount φ) (runM .on φ) ∧ LineShape φ (runM .on φ) := by
  have hpos := stepCount_pos φ
  have h := lineOnShape_steps hbd (stepCount φ - 1).toNat 1 (initM .on φ) (initOn_inv φ (fun _ => false)).1
    (lineShape_init hbd)
  rw [show (1 : Int) + ((stepCount φ - 1).toNat : Int) = stepCount φ by rw [Int.toNat_of_nonneg (by omega)]; omega] at h
  exact h

-- ============================================================
-- El veredicto de la espina con la regla activa
-- ============================================================

/-- El estado final revisado con la regla (Julia `reviewAll` con `FORBID = :on`). -/
def reviewAllOn (g : GPathB) : GPathB := GPathB.reviewOn { g with dirty := true }

/-- **La espina con tríos, con la regla activa**: dice SAT si algún estado final de la máquina `:on`, revisado con la
regla, es válido. -/
def SpineVerdictOn (φ : Cnf) : Prop := ∃ kv ∈ runM .on φ, (reviewAllOn kv.2).isValid = true

/-- **La espina `:on` decide la satisfacibilidad** si los estados finales revisados cumplen `LiveExt` con **sus
propios tríos** (`TF`): toda cadena viva, que no pasa por ningún trío guardado, se alarga. Sin familias fantasma. -/
theorem spineVerdictOn_iff_of_liveExt (hbd : Bounded φ)
    (H : ∀ kv ∈ runM .on φ, (reviewAllOn kv.2).isValid = true →
      LiveExt (reviewAllOn kv.2) (TF (reviewAllOn kv.2))) :
    SpineVerdictOn φ ↔ Satisfiable φ := by
  constructor
  · rintro ⟨kv, hkv, hval⟩
    obtain ⟨hlo, hls⟩ := lineOn_run_shape hbd
    have hent := hlo kv hkv
    have hsh := hls kv hkv
    let g0 : GPathB := { kv.2 with dirty := true }
    have hsc : 2 ≤ stepCount φ := by unfold stepCount; omega
    have hcs0 : g0.current_step = stepCount φ := hent.1.step
    have hcl := closedState_reviewOn (g := g0) rfl hval hent.1.docs hsh.1.1 hent.1.below hsh.1.2.2.2 (by omega)
    have hdocs : AliveDocs (reviewAllOn kv.2) := aliveDocs_reviewOn hent.1.docs
    have hb : Machine.Below (reviewAllOn kv.2) := revPrims_reviewOn revPrims_below trioBlind_below _ hent.1.below
    have hz : AboveZero (reviewAllOn kv.2) := revPrims_reviewOn revPrims_aboveZero trioBlind_aboveZero _ hsh.1.2.2.2
    have hlst : LinksStep (reviewAllOn kv.2) := revPrims_reviewOn revPrims_linksStep trioBlind_linksStep _ hsh.1.2.2.1
    have hli : LinksInv (reviewAllOn kv.2) := revPrims_reviewOn revPrims_linksInv trioBlind_linksInv _ hsh.2.1
    have hcs : (reviewAllOn kv.2).current_step = stepCount φ := (step_reviewOn g0).trans hcs0
    have hcs1 : 1 ≤ g0.reviewOn.current_step := by have := (step_reviewOn g0).trans hcs0; omega
    obtain ⟨S, hc⟩ := noZombie_of_liveExt hcl hdocs hb hz hlst hli hcs1 (H kv hkv hval) hval
    have hstr : Struct φ (reviewAllOn kv.2) :=
      struct_of_sub (shrinks_reviewOn g0).1 ⟨hsh.2.2.1.pmp, hsh.2.2.1.gpmp, hsh.2.2.1.noforb, hsh.2.2.1.onmap,
        hsh.2.2.1.req⟩
    exact ⟨Decode.decode S, Decode.sat_of_carried hbd hstr hc hcs⟩
  · rintro ⟨a, ha⟩
    obtain ⟨g, hf, hct, _⟩ := run_carriesOn hbd a ha
    refine ⟨_, List.mem_of_find?_eq_some hf, ?_⟩
    exact isValid_of_carried (ct_reviewOn (ct_dirty hct true)).1

end MachineOn

end AbsSatBingo.Model
