-- lean/improves_bingo/AbsSatBingo/Model/ReaderFinal.lean
import AbsSatBingo.Model.ClosedReview

/-!
# El veredicto del lector bajo tres hipótesis con nombre

La cadena entera: `KernelExact` («el núcleo de cualquier pin está hecho de camarillas») es un invariante de la
máquina y del lector, y en los estados del lector, con el cierre del review, da `EdgeClique`, `NoZombie` y el
veredicto (`readerVerdict_iff_of_noZombie`).

**`readerVerdict_iff_of_hyps`**: el veredicto del lector es la satisfacibilidad bajo `Hyps φ`. (La antigua
hipótesis `closed`, que los estados del lector estén cerrados por las reglas, es ya el teorema `closedState_review`,
con la comprobación final del review; aquí, `cInv_visited`.)
* `union` — en cada join de la máquina, el núcleo de la unión es la unión de los núcleos (`KernelUnion`; medido:
  `probe_kernelunion.jl`);
* `skip` — el UP con una ventana saltada conserva `KernelExact` en su fila (medido: `probe_kernelexact_up.jl`,
  `probe_edgeclique.jl` punto U).

Las hipótesis `union` y `skip` se piden sobre los estados con el invariante de línea (una sobreaproximación de los
alcanzables).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace Final

open GPathB Driver Machine

/-- El invariante de un estado de la línea (además de `StateOk`). -/
def KInv (g : GPathB) : Prop := KernelExact g ∧ NodupIds g ∧ EdgesAlive g ∧ LinksStep g ∧ AboveZero g

/-- **Las dos hipótesis** (la tercera, `closed`, es ya el teorema `closedState_review`). -/
structure Hyps (φ : Cnf) : Prop where
  union  : ∀ T key e g, StateOk T key e → StateOk T key g → KInv e → KInv g → KernelUnion e g
  skip   : ∀ T key g d, StateOk T key g → KInv g → 1 ≤ T → d ∈ sonsOfMap φ key →
             (g.filterAll (reqOf φ d)).isValid = true →
             (g.filterAll (reqOf φ d)).skipsWindow d (isProhibited φ) = true →
             KernelExact ((g.filterAll (reqOf φ d)).addNode d "" (isProhibited φ))

theorem review_eq_filterAll (g : GPathB) : g.review = g.filterAll [] := rfl

-- ============================================================
-- Un envío
-- ============================================================

theorem kInv_filterAll {g : GPathB} (hk : KInv g) (hd : AliveDocs g) (reqs : List NodeId) :
    KInv (g.filterAll reqs) :=
  ⟨kernelExact_filterAll hk.1 hd hk.2.1 reqs, revPrims_filterAll revPrims_nodupIds _ _ hk.2.1,
   revPrims_filterAll revPrims_edgesAlive _ _ hk.2.2.1, revPrims_filterAll revPrims_linksStep _ _ hk.2.2.2.1,
   revPrims_filterAll revPrims_aboveZero _ _ hk.2.2.2.2⟩

theorem kInv_upFiltering {φ : Cnf} (H : Hyps φ) {T : Int} {key d : NodeId} {g : GPathB} (hg : StateOk T key g)
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
    have hka : KernelExact a := by
      cases hsk : f.skipsWindow d (isProhibited φ)
      · exact kernelExact_addNode hf.1 hfd hfb hf.2.2.2.1 hf.2.2.1
          (by show 0 < (g.filterAll (reqOf φ d)).current_step; omega) hsk hdstep
      · exact H.skip T key g d hg hk hT hd hvf hsk
    have hnd : NodupIds a := nodupIds_addNode hf.2.1 hfb hdstep
    have hda : AliveDocs a := aliveDocs_addNode hfd
    rw [review_eq_filterAll]
    exact ⟨kernelExact_filterAll hka hda hnd [], revPrims_filterAll revPrims_nodupIds _ _ hnd,
      revPrims_filterAll revPrims_edgesAlive _ _ (edgesAlive_addNode hf.2.2.1),
      revPrims_filterAll revPrims_linksStep _ _ (linksStep_addNode hf.2.2.2.1 hdstep),
      revPrims_filterAll revPrims_aboveZero _ _ (aboveZero_addNode hf.2.2.2.2 (by omega))⟩
  · rename_i hvf
    rw [if_neg hvf] at hv
    exact absurd hv hvf

-- ============================================================
-- La línea
-- ============================================================

def LineK (line : Line) : Prop := ∀ kv ∈ line, KInv kv.2

theorem kInv_doJoin {φ : Cnf} (H : Hyps φ) {T : Int} {key : NodeId} {e g : GPathB} (he : StateOk T key e)
    (hg : StateOk T key g) (hke : KInv e) (hkg : KInv g) : KInv (doJoin e g) := by
  refine ⟨kernelExact_doJoin hke.1 hkg.1 (H.union T key e g he hg hke hkg), nodupIds_doJoin hke.2.1 hkg.2.1,
    edgesAlive_doJoin hke.2.2.1 hkg.2.2.1, ?_, ?_⟩
  · unfold doJoin; split
    · exact linksStep_join hke.2.2.2.1 hkg.2.2.2.1
    · exact hke.2.2.2.1
  · unfold doJoin; split
    · exact aboveZero_join hke.2.2.2.2 hkg.2.2.2.2
    · exact hke.2.2.2.2

theorem lineK_insert {φ : Cnf} (H : Hyps φ) {T : Int} {line : Line} {key : NodeId} {g : GPathB}
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
    · exact kInv_doJoin H (hl _ hmem) hg (hlk _ hmem) hk
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
              exact lineK_insert H a b (stateOk_upFiltering (hl kv hkv) hd hv)
                (kInv_upFiltering H (hl kv hkv) (hlk kv hkv) hT hd hv)
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
  have hka : KernelExact a := by
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
  rw [hup]
  exact ⟨kernelExact_filterAll hka hda hnd [], revPrims_filterAll revPrims_nodupIds _ _ hnd,
    revPrims_filterAll revPrims_edgesAlive _ _ hea, revPrims_filterAll revPrims_linksStep _ _ hls,
    revPrims_filterAll revPrims_aboveZero _ _ hz⟩

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

/-- Cambiar `dirty` no cambia `KernelExact`. -/
theorem kernelExact_dirty {g : GPathB} (hk : KernelExact g) (b : Bool) : KernelExact { g with dirty := b } := by
  intro P y w ⟨V, R, hst, ha, hr⟩
  have hst' : SecStruct g V R := ⟨hst.alive, hst.refl, hst.symm, hst.dom, hst.adj, hst.pair, hst.node, hst.par, hst.son⟩
  obtain ⟨S, hc, hag, hy, hw⟩ := hk P y w ⟨V, R, hst', ha, hr⟩
  exact ⟨S, carried_dirty hc b, hag, hy, hw⟩

/-- El invariante de un estado del lector. -/
def VInv (h : GPathB) : Prop := KernelExact h ∧ NodupIds h ∧ EdgesAlive h ∧ AliveDocs h

theorem vInv_filterAll {h : GPathB} (hv : VInv h) (reqs : List NodeId) : VInv (h.filterAll reqs) :=
  ⟨kernelExact_filterAll hv.1 hv.2.2.2 hv.2.1 reqs, revPrims_filterAll revPrims_nodupIds _ _ hv.2.1,
   revPrims_filterAll revPrims_edgesAlive _ _ hv.2.2.1, aliveDocs_filterAll hv.2.2.2 reqs⟩

theorem vInv_visited {g₀ : GPathB} (hk : KInv g₀) (hd : AliveDocs g₀) : ∀ h, Visited g₀ h → VInv h := by
  intro h hvis
  induction hvis with
  | start =>
    show VInv (review { g₀ with dirty := true })
    rw [review_eq_filterAll]
    exact vInv_filterAll (h := { g₀ with dirty := true }) ⟨kernelExact_dirty hk.1 true, hk.2.1, hk.2.2.1, hd⟩ []
  | pin q _ ih => exact vInv_filterAll ih [q.id]

-- ============================================================
-- Los estados del lector están cerrados (antes la hipótesis `closed`)
-- ============================================================

theorem closedState_congr {h h' : GPathB} (ha : h'.alive = h.alive) (he : h'.edges = h.edges)
    (hn : h'.nodes = h.nodes) (hs : h'.current_step = h.current_step) (hc : ClosedState h) : ClosedState h' := by
  obtain ⟨n₁, a₁, e₁, c₁, m₁, d₁⟩ := h
  obtain ⟨n₂, a₂, e₂, c₂, m₂, d₂⟩ := h'
  simp only at ha he hn hs
  subst ha he hn hs
  exact ⟨hc.alive, hc.refl, hc.symm, hc.dom, hc.adj, hc.pair, hc.node, hc.par, hc.son⟩

/-- Un requisito que no mata a nadie deja el grafo y los documentos. -/
theorem filterRequire_clean_full {h : GPathB} {r : NodeId} (hd : (h.filterRequire r).dirty = false) :
    (h.filterRequire r).alive = h.alive ∧ (h.filterRequire r).edges = h.edges ∧
      (h.filterRequire r).nodes = h.nodes ∧ (h.filterRequire r).current_step = h.current_step := by
  unfold filterRequire at hd ⊢
  by_cases hv : h.isValid = true
  · rw [if_pos hv] at hd ⊢
    dsimp only at hd ⊢
    generalize (List.filter (fun q => q.id != r) (List.map (fun x => x.id) (h.line r.step))) = victims at hd ⊢
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hd
    rw [hd.2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [if_neg hv]; exact ⟨rfl, rfl, rfl, rfl⟩

/-- El invariante de cierre de un estado del lector. -/
def CInv (h : GPathB) : Prop :=
  AliveDocs h ∧ NodupIds h ∧ Below h ∧ AboveZero h ∧ 2 ≤ h.current_step ∧ (h.isValid = true → ClosedState h)

theorem revPrims_filterRequire {P : GPathB → Prop} (hp : RevPrims P) (g : GPathB) (r : NodeId) (hg : P g) :
    P (g.filterRequire r) := by
  unfold filterRequire
  split
  · exact hp.dirty _ _ (inv_foldl P killVertex _ (fun g'' q _ hc' => hp.kill _ _ hc') g hg)
  · exact hg

theorem cInv_visited {g₀ : GPathB} (had : AliveDocs g₀) (hnd : NodupIds g₀) (hb : Below g₀) (hz : AboveZero g₀)
    (hcs : 2 ≤ g₀.current_step) : ∀ h, Visited g₀ h → CInv h := by
  intro h hvis
  induction hvis with
  | start =>
    let g₁ : GPathB := { g₀ with dirty := true }
    have had₁ : AliveDocs g₁ := aliveDocs_dirty had true
    have hnd₁ : NodupIds g₁ := revPrims_nodupIds.dirty _ _ hnd
    have hb₁ : Below g₁ := revPrims_below.dirty _ _ hb
    have hz₁ : AboveZero g₁ := revPrims_aboveZero.dirty _ _ hz
    have hcs₁ : g₁.review.current_step = g₀.current_step := (shrinks_review g₁).1.step
    show CInv g₁.review
    exact ⟨aliveDocs_review had₁, revPrims_review revPrims_nodupIds _ hnd₁, revPrims_review revPrims_below _ hb₁,
      revPrims_review revPrims_aboveZero _ hz₁, by omega,
      fun hv => closedState_review rfl hv had₁ hnd₁ hb₁ hz₁ hcs⟩
  | @pin h q _ ih =>
    obtain ⟨had', hnd', hb', hz', hcs', hcl'⟩ := ih
    have hstep : (h.filterAll [q.id]).current_step = h.current_step := (shrinks_filterAll h [q.id]).1.step
    refine ⟨aliveDocs_filterAll had' _, revPrims_filterAll revPrims_nodupIds _ _ hnd',
      revPrims_filterAll revPrims_below _ _ hb', revPrims_filterAll revPrims_aboveZero _ _ hz', by omega, ?_⟩
    intro hv
    have hfa : h.filterAll [q.id] = (h.filterRequire q.id).review := rfl
    rw [hfa] at hv ⊢
    cases hdr : (h.filterRequire q.id).dirty
    · -- el requisito no mató a nadie: el review no corre y el estado es el anterior
      obtain ⟨ha, he, hn, hs⟩ := filterRequire_clean_full hdr
      have hr : (h.filterRequire q.id).review = h.filterRequire q.id := reviewFuel_of_clean hdr _
      rw [hr] at hv ⊢
      have hvh : h.isValid = true := by
        unfold isValid at hv ⊢; rw [ha, hs] at hv; exact hv
      exact closedState_congr ha he hn hs (hcl' hvh)
    · have hsf : (h.filterRequire q.id).current_step = h.current_step := (shrinks_filterRequire h q.id).1.step
      exact closedState_review hdr hv (aliveDocs_filterRequire had' _)
        (revPrims_filterRequire revPrims_nodupIds _ _ hnd') (revPrims_filterRequire revPrims_below _ _ hb')
        (revPrims_filterRequire revPrims_aboveZero _ _ hz') (by omega)

/-- **El veredicto del lector es la satisfacibilidad**, bajo las dos hipótesis con nombre (`union`, `skip`). -/
theorem readerVerdict_iff_of_hyps {φ : Cnf} (hbd : Bounded φ) (H : Hyps φ) :
    readerVerdict φ = true ↔ Satisfiable φ := by
  apply Decode.readerVerdict_iff_of_noZombie hbd
  intro kv hkv h hvis
  obtain ⟨hok, hk⟩ := run_kInv H kv hkv
  have hv := vInv_visited hk hok.docs h hvis
  have hcs : 2 ≤ kv.2.current_step := by rw [hok.step]; unfold stepCount; omega
  have hc := cInv_visited hok.docs hk.2.1 hok.below hk.2.2.2.2 hcs h hvis
  intro hval
  exact noZombie_of_edgeClique (edgeClique_of_kernelExact hv.1 (hc.2.2.2.2.2 hval) hv.2.2.1) hval

end Final

end AbsSatBingo.Model
