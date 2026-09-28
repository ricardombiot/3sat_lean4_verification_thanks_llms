-- lean/improves_bingo/AbsSatBingo/Model/ReaderTop.lean
import AbsSatBingo.Model.ReaderFinal
import AbsSatBingo.Model.TopExact

/-!
# El veredicto del lector con `TopExact`: una sola hipótesis, `TopUnion`

La misma cadena que `ReaderFinal.lean`, con `TopExact` (la exactitud solo para las cimas) en lugar de `KernelExact`:
el UP la conserva sin `AvoidExact` (`topExact_addNode`), así que la hipótesis `skip` desaparece, y el join pide solo
**`TopUnion`**: una cima del núcleo de la unión fijada está en el núcleo de algún lado (por nodo, no por pareja).
**`readerVerdict_iff_of_topUnion`**.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace FinalTop

open GPathB Driver Machine

/-- El invariante de un estado de la línea (además de `StateOk`), con `TopExact` en vez de `KernelExact`. -/
def KInv (g : GPathB) : Prop :=
  TopExact g ∧ NodupIds g ∧ EdgesAlive g ∧ LinksStep g ∧ AboveZero g ∧ TopNoSons g ∧ LinksInv g

/-- **La única hipótesis**: en cada join de la máquina, una cima del núcleo de la unión fijada está en el núcleo de
algún lado (`TopUnion`). `skip` ya no hace falta: el UP conserva `TopExact` con o sin ventana saltada. -/
structure Hyps (φ : Cnf) : Prop where
  union  : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → KInv e → KInv g → TopUnion e g

theorem review_eq_filterAll (g : GPathB) : g.review = g.filterAll [] := rfl

-- ============================================================
-- Un envío
-- ============================================================

theorem kInv_filterAll {g : GPathB} (hk : KInv g) (hd : AliveDocs g) (reqs : List NodeId) :
    KInv (g.filterAll reqs) :=
  ⟨topExact_filterAll hk.1 hd hk.2.1 reqs, revPrims_filterAll revPrims_nodupIds _ _ hk.2.1,
   revPrims_filterAll revPrims_edgesAlive _ _ hk.2.2.1, revPrims_filterAll revPrims_linksStep _ _ hk.2.2.2.1,
   revPrims_filterAll revPrims_aboveZero _ _ hk.2.2.2.2.1, revPrims_filterAll revPrims_topNoSons _ _ hk.2.2.2.2.2.1,
   revPrims_filterAll revPrims_linksInv _ _ hk.2.2.2.2.2.2⟩

theorem kInv_upFiltering {φ : Cnf} {T : Int} {key d : NodeId} {g : GPathB} (hg : StateOk T key g)
    (hk : KInv g) (hT : 1 ≤ T) (hd : d ∈ sonsOfMap φ key)
    (hv : (g.upFiltering (reqOf φ d) d "" (isProhibited φ)).isValid = true) :
    KInv (g.upFiltering (reqOf φ d) d "" (isProhibited φ)) := by
  have hs := shrinks_filterAll g (reqOf φ d)
  have hstep : (g.filterAll (reqOf φ d)).current_step = T := (step_of_shrinks hs).trans hg.step
  have hdstep : d.step = (g.filterAll (reqOf φ d)).current_step := by
    rw [hstep, sonsOfMap_step φ key d hd, hg.key]; omega
  have hf := kInv_filterAll hk hg.docs (reqOf φ d)
  have hfd : AliveDocs (g.filterAll (reqOf φ d)) := aliveDocs_filterAll hg.docs _
  have hfb : Below (g.filterAll (reqOf φ d)) := below_of_shrinks hs hg.below
  unfold upFiltering up at hv ⊢
  split
  · rename_i hvf
    let f := g.filterAll (reqOf φ d)
    let a := f.addNode d "" (isProhibited φ)
    have hfpos : 0 < f.current_step := by show 0 < (g.filterAll (reqOf φ d)).current_step; omega
    have hka : TopExact a := topExact_addNode hf.1 hfd hfb hf.2.2.2.1 hfpos hdstep
    have hnd : NodupIds a := nodupIds_addNode hf.2.1 hfb hdstep
    have hda : AliveDocs a := aliveDocs_addNode hfd
    rw [review_eq_filterAll]
    exact ⟨topExact_filterAll hka hda hnd [], revPrims_filterAll revPrims_nodupIds _ _ hnd,
      revPrims_filterAll revPrims_edgesAlive _ _ (edgesAlive_addNode hf.2.2.1),
      revPrims_filterAll revPrims_linksStep _ _ (linksStep_addNode hf.2.2.2.1 hdstep),
      revPrims_filterAll revPrims_aboveZero _ _ (aboveZero_addNode hf.2.2.2.2.1 (by omega)),
      revPrims_filterAll revPrims_topNoSons _ _ (topNoSons_addNode hfb),
      revPrims_filterAll revPrims_linksInv _ _ (linksInv_addNode hf.2.2.2.2.2.2 hfb hf.2.2.2.2.1 hdstep)⟩
  · rename_i hvf
    rw [if_neg hvf] at hv
    exact absurd hv hvf

-- ============================================================
-- La línea
-- ============================================================

def LineK (line : Line) : Prop := ∀ kv ∈ line, KInv kv.2

theorem kInv_doJoin {φ : Cnf} (H : Hyps φ) {T : Int} (hT : 2 ≤ T) {key : NodeId} {e g : GPathB} (he : StateOk T key e)
    (hg : StateOk T key g) (hke : KInv e) (hkg : KInv g) : KInv (doJoin e g) := by
  refine ⟨topExact_doJoin hke.1 hkg.1 (H.union T key e g hT he hg hke hkg), nodupIds_doJoin hke.2.1 hkg.2.1,
    edgesAlive_doJoin hke.2.2.1 hkg.2.2.1, ?_, ?_, ?_, ?_⟩
  · unfold doJoin; split
    · exact linksStep_join hke.2.2.2.1 hkg.2.2.2.1
    · exact hke.2.2.2.1
  · unfold doJoin; split
    · exact aboveZero_join hke.2.2.2.2.1 hkg.2.2.2.2.1
    · exact hke.2.2.2.2.1
  · unfold doJoin; split
    · rename_i hok
      unfold okJoin at hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      exact topNoSons_join hke.2.2.2.2.2.1 hkg.2.2.2.2.2.1 hok.1.1.1
    · exact hke.2.2.2.2.2.1
  · unfold doJoin; split
    · exact linksInv_join hke.2.2.2.2.2.2 hkg.2.2.2.2.2.2 hke.2.2.1 hkg.2.2.1
    · exact hke.2.2.2.2.2.2

theorem lineK_insert {φ : Cnf} (H : Hyps φ) {T : Int} (hT : 2 ≤ T) {line : Line} {key : NodeId} {g : GPathB}
    (hl : LineOk T line) (hlk : LineK line) (hg : StateOk T key g) (hk : KInv g) :
    LineK (Driver.insert line key g) := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    subst hkey
    have hmem := List.mem_of_find?_eq_some hfind
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact kInv_doJoin H hT (hl _ hmem) hg (hlk _ hmem) hk
    · exact hlk kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hlk kv h
    · rw [List.mem_singleton] at h; subst h; exact hk

theorem lineK_advance {φ : Cnf} (H : Hyps φ) {T : Int} (hT : 1 ≤ T) {line : Line} (hl : LineOk T line)
    (hlk : LineK line) : LineK (advance φ line) := by
  have key : ∀ (l : Line), (∀ kv ∈ l, kv ∈ line) → ∀ next, LineOk (T + 1) next → LineK next →
      LineOk (T + 1) (l.foldl (fun next kv => sendAll φ kv next) next) ∧
        LineK (l.foldl (fun next kv => sendAll φ kv next) next) := by
    intro l
    induction l with
    | nil => intro _ next h1 h2; exact ⟨h1, h2⟩
    | cons kv rest ih =>
      intro hsub next h1 h2
      have hkv := hsub kv (List.mem_cons_self ..)
      -- los envíos de kv
      have hsend : ∀ (ds : List NodeId), (∀ d ∈ ds, d ∈ sonsOfMap φ kv.1) → ∀ nx, LineOk (T + 1) nx →
          LineK nx → LineOk (T + 1) (ds.foldl (sendTo φ kv.2) nx) ∧ LineK (ds.foldl (sendTo φ kv.2) nx) := by
        intro ds
        induction ds with
        | nil => intro _ nx a b; exact ⟨a, b⟩
        | cons d ds ihd =>
          intro hds nx a b
          have hd := hds d (List.mem_cons_self ..)
          simp only [List.foldl_cons]
          apply ihd (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd'))
          · exact lineOk_sendTo (hl kv hkv) d hd a
          · unfold sendTo
            dsimp only
            split
            · rename_i hv
              exact lineK_insert H (by omega) a b (stateOk_upFiltering (hl kv hkv) hd hv)
                (kInv_upFiltering (hl kv hkv) (hlk kv hkv) hT hd hv)
            · exact b
      simp only [List.foldl_cons]
      obtain ⟨a, b⟩ := hsend _ (fun _ h => h) next h1 h2
      exact ih (fun kv' h => hsub kv' (List.mem_cons_of_mem _ h)) _ a b
  exact (key line (fun _ h => h) [] (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil)).2

-- ============================================================
-- La semilla
-- ============================================================

theorem kInv_initSeed : KInv (initSeed (⟨0, 0⟩ : NodeId) "") := by
  let d : NodeId := ⟨0, 0⟩
  let root : PathNodeId := { id := d, parent_id := none, gparent_id := none }
  let a := GPathB.empty.addNode d "" (fun _ => false)
  have hal : a.alive = [root] := rfl
  have hed : a.edges = [] := rfl
  have hnodes : a.nodes = [GPathB.empty.rowNode d "" root] := rfl
  have hadj : ∀ y w, a.Adj y w → y = root ∧ w = root := by
    intro y w h
    rw [adj_iff, hal, hed] at h
    rcases h with ⟨rfl, hy⟩ | ⟨e, he, _⟩
    · rw [List.mem_singleton] at hy; exact ⟨hy, hy⟩
    · cases he
  let S : Int → PathNodeId := fun _ => root
  have hc : Carried a S := by
    apply carried_addNode (carried_empty S)
    · show root ∈ (GPathB.empty.shiftRowIds d).filter _
      refine List.mem_filter.mpr ⟨?_, rfl⟩
      unfold shiftRowIds
      rw [if_neg (show ¬ (0 : Int) < GPathB.empty.current_step by show ¬ (0 : Int) < 0; omega)]
      exact List.mem_singleton_self _
    · intro h; exact absurd h (by show ¬ (0 : Int) < 0; omega)
    · rfl
    · intro n hn; exact absurd hn List.not_mem_nil
    · rfl
  have hka' : KernelExact a := by
    intro P y w ⟨V, R, hst, ha, hr⟩
    obtain ⟨rfl, rfl⟩ := hadj y w (hst.adj hr)
    refine ⟨S, hc, ?_, ⟨0, Int.le_refl 0, by decide, rfl⟩, ⟨0, Int.le_refl 0, by decide, rfl⟩⟩
    intro r hr' h0 h1
    have h1' : r.step < 1 := h1
    have hr0 : r.step = 0 := by omega
    exact ha r hr' (hst.dom hr).1 (by rw [hr0])
  have hnd : NodupIds a := by
    unfold NodupIds; rw [hnodes]; exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  have hda : AliveDocs a := aliveDocs_addNode (fun q hq => absurd hq List.not_mem_nil)
  have hea : EdgesAlive a := by
    intro y w h
    obtain ⟨rfl, rfl⟩ := hadj y w h
    rw [hal]; exact ⟨List.mem_singleton_self _, List.mem_singleton_self _⟩
  have hls : LinksStep a := by
    intro n hn
    rw [hnodes, List.mem_singleton] at hn
    subst hn
    have hp0 : (GPathB.empty.rowNode d "" root).parents = [] := rfl
    have hs0 : (GPathB.empty.rowNode d "" root).sons = [] := rfl
    refine ⟨fun p hp => ?_, fun s hs => ?_⟩
    · rw [hp0] at hp; cases hp
    · rw [hs0] at hs; cases hs
  have hup : initSeed d "" = a.filterAll [] := by
    unfold initSeed up
    rw [if_pos (show GPathB.empty.isValid = true by rfl)]
    rfl
  have hz : AboveZero a := by
    intro n hn
    rw [hnodes, List.mem_singleton] at hn
    subst hn
    show 0 ≤ d.step
    decide
  have ht : TopNoSons a := by
    intro n hn _
    rw [hnodes, List.mem_singleton] at hn
    subst hn
    rfl
  have hli : LinksInv a := by
    refine ⟨hda, ?_, ?_⟩
    · intro n hn p _ ha
      rw [hnodes, List.mem_singleton] at hn
      subst hn
      obtain ⟨_, rfl⟩ := hadj _ _ ha
      refine ⟨fun hc => ?_, fun hc => ?_⟩ <;> (have := hc.2.2; exact absurd this (by show ¬ (0 : Int) + 1 = 0; omega))
    · intro n hn
      rw [hnodes, List.mem_singleton] at hn
      subst hn
      have hp0 : (GPathB.empty.rowNode d "" root).parents = [] := rfl
      have hs0 : (GPathB.empty.rowNode d "" root).sons = [] := rfl
      refine ⟨fun p hp => ?_, fun s hs => ?_⟩
      · rw [hp0] at hp; cases hp
      · rw [hs0] at hs; cases hs
  rw [hup]
  have hka : TopExact a := topExact_of_kernelExact hka'
  exact ⟨topExact_filterAll hka hda hnd [], revPrims_filterAll revPrims_nodupIds _ _ hnd,
    revPrims_filterAll revPrims_edgesAlive _ _ hea, revPrims_filterAll revPrims_linksStep _ _ hls,
    revPrims_filterAll revPrims_aboveZero _ _ hz, revPrims_filterAll revPrims_topNoSons _ _ ht,
    revPrims_filterAll revPrims_linksInv _ _ hli⟩

-- ============================================================
-- La máquina entera
-- ============================================================

theorem stepsK {φ : Cnf} (H : Hyps φ) :
    ∀ (n : Nat) (t : Int) (line : Line), 0 ≤ t → LineOk (t + 1) line → LineK line →
      LineOk (t + n + 1) (steps φ n line) ∧ LineK (steps φ n line) := by
  intro n
  induction n with
  | zero =>
    intro t line _ hl hk
    simp only [steps]
    rw [show t + ((0 : Nat) : Int) = t by omega]
    exact ⟨hl, hk⟩
  | succ n ih =>
    intro t line h0 hl hk
    simp only [steps]
    have h1 := lineOk_advance (φ := φ) hl
    have h2 := lineK_advance H (by omega) hl hk
    have := ih (t + 1) (advance φ line) (by omega) h1 h2
    rw [show t + 1 + (n : Int) = t + ((n + 1 : Nat) : Int) by push_cast; omega] at this
    exact this

/-- **Todo estado de la línea final cumple el invariante.** -/
theorem run_kInv {φ : Cnf} (H : Hyps φ) : ∀ kv ∈ run φ, StateOk (stepCount φ) kv.1 kv.2 ∧ KInv kv.2 := by
  have hpos := stepCount_pos φ
  have hl0 := (init_inv φ (fun _ => false)).1
  have hk0 : LineK (init φ) := by
    rw [init_eq]
    intro kv hkv
    rw [List.mem_singleton] at hkv; subst hkv
    exact kInv_initSeed
  have hn : (0 : Int) + ((stepCount φ - 1).toNat : Int) = stepCount φ - 1 := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  obtain ⟨hl, hk⟩ := stepsK H (stepCount φ - 1).toNat 0 (init φ) (Int.le_refl 0) (by simpa using hl0) hk0
  rw [hn, show stepCount φ - 1 + 1 = stepCount φ by omega] at hl
  intro kv hkv
  exact ⟨hl kv hkv, hk kv hkv⟩

-- ============================================================
-- El lector
-- ============================================================

/-- El invariante de un estado del lector. -/
def VInv (h : GPathB) : Prop := TopExact h ∧ NodupIds h ∧ EdgesAlive h ∧ AliveDocs h

theorem vInv_filterAll {h : GPathB} (hv : VInv h) (reqs : List NodeId) : VInv (h.filterAll reqs) :=
  ⟨topExact_filterAll hv.1 hv.2.2.2 hv.2.1 reqs, revPrims_filterAll revPrims_nodupIds _ _ hv.2.1,
   revPrims_filterAll revPrims_edgesAlive _ _ hv.2.2.1, aliveDocs_filterAll hv.2.2.2 reqs⟩

theorem vInv_visited {g₀ : GPathB} (hk : KInv g₀) (hd : AliveDocs g₀) : ∀ h, Visited g₀ h → VInv h := by
  intro h hvis
  induction hvis with
  | start =>
    show VInv (review { g₀ with dirty := true })
    rw [review_eq_filterAll]
    exact vInv_filterAll (h := { g₀ with dirty := true }) ⟨topExact_dirty hk.1 true, hk.2.1, hk.2.2.1, hd⟩ []
  | pin q _ ih => exact vInv_filterAll ih [q.id]

/-- **El veredicto del lector es la satisfacibilidad bajo `TopUnion` sola.** -/
theorem readerVerdict_iff_of_topUnion {φ : Cnf} (hbd : Bounded φ) (H : Hyps φ) :
    readerVerdict φ = true ↔ Satisfiable φ := by
  apply Decode.readerVerdict_iff_of_noZombie hbd
  intro kv hkv h hvis
  obtain ⟨hok, hk⟩ := run_kInv H kv hkv
  have hv := vInv_visited hk hok.docs h hvis
  have hcs : 2 ≤ kv.2.current_step := by rw [hok.step]; unfold stepCount; omega
  have hc := Final.cInv_visited hok.docs hk.2.1 hok.below hk.2.2.2.2.1 hcs h hvis
  exact fun hval => noZombie_of_topExact hv.1 (hc.2.2.2.2.2 hval) (by have := hc.2.2.2.2.1; omega) hval

end FinalTop

end AbsSatBingo.Model
