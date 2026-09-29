-- lean/improves_bingo/AbsSatBingo/Model/SecExactLine.lean
import AbsSatBingo.Model.SeqUp
import AbsSatBingo.Model.ReaderFinal

/-!
# La máquina entera bajo la versión de existencia de la exactitud (`SecExact`)

`SeqExact.lean` dejó el lector en `SeqExact` (pins válidos ⟹ camarilla que concuerda) sobre los arranques. Para
llevarlo por la máquina sin `ClosedState` en cada estado intermedio, se formula sobre estructuras cerradas, como
`KernelExact`, pero **solo pidiendo existencia**:

> **`SecExact g`**: toda estructura cerrada **no vacía** de `g` que concuerda con `P` tiene **una** camarilla de `g`
> que concuerda con `P`.

`KernelExact` pide una camarilla **por cada pareja** de la estructura; `SecExact` una sola
(`secExact_of_kernelExact`).

Operación por operación (sin hipótesis salvo la contabilidad de siempre):
* el filtro y el review (`secExact_filterAll`); el cambio de `dirty` (`secExact_dirty`);
* la fila nueva (`secExact_addNode`), bajo **`AvoidSat`** (existencia de una camarilla con cima de hijo permitido);
  sin ventana saltada `AvoidSat` sale de `SecExact` (`avoidSat_of_noSkip`);
* el join (`secExact_doJoin`), bajo **`SecSplit`**: una estructura cerrada no vacía de la unión que concuerda con `P`
  da una en algún lado.

La línea (`run_sInv`) y el lector (`readerVerdict_iff_of_secSplit`): **el veredicto del lector es la
satisfacibilidad bajo `SecSplit` en los joins y `AvoidSat` en las ventanas saltadas**. Son las versiones de existencia
de `union` y `skip` (`Final.Hyps`): estado a estado, `KernelUnion ⟹ SecSplit` (`secSplit_of_kernelUnion`) y
`AvoidExact ⟹ AvoidSat` (`avoidSat_of_avoidExact`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid)

namespace GPathB

open Machine (Below)

/-- **La exactitud en su versión de existencia**: toda estructura cerrada no vacía que concuerda con `P` tiene una
camarilla que concuerda con `P`. -/
def SecExact (g : GPathB) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct g V R → (∀ b ∈ P, SecAgrees V b) → (∃ y, V y) →
    ∃ S, Carried g S ∧ ∀ r ∈ P, Agrees g.current_step S r

theorem secExact_of_kernelExact {g : GPathB} (hk : KernelExact g) : SecExact g := by
  intro P V R hst ha ⟨y, hy⟩
  obtain ⟨S, hS, hag, _, _⟩ := hk P y y ⟨V, R, hst, ha, hst.refl hy⟩
  exact ⟨S, hS, hag⟩

theorem secExact_dirty {g : GPathB} (hse : SecExact g) (b : Bool) : SecExact { g with dirty := b } := by
  intro P V R hst ha hne
  obtain ⟨S, hS, hag⟩ := hse P V R ⟨hst.alive, hst.refl, hst.symm, hst.dom, hst.adj, hst.pair, hst.node, hst.par,
    hst.son⟩ ha hne
  exact ⟨S, carried_dirty hS b, hag⟩

-- ============================================================
-- El filtro y el review
-- ============================================================

/-- **El filtro (y el review, `Q = []`) conserva `SecExact`.** -/
theorem secExact_filterAll {x : GPathB} (hse : SecExact x) (hd : AliveDocs x) (hnd : NodupIds x) (Q : List NodeId) :
    SecExact (x.filterAll Q) := by
  intro P V R hst ha ⟨y, hy⟩
  have hsub := (shrinks_filterAll x Q).1
  have hv := isValid_of_sec hst hy
  obtain ⟨S, hS, hag⟩ := hse (Q ++ P) V R (secStruct_of_sub hsub hnd hst) (by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact fun hq hqs => pinned_filterAll_list hd Q hv b hb _ (hst.alive hq) hqs
    · exact ha b hb) ⟨y, hy⟩
  refine ⟨S, carried_filterAll hS Q (fun r hr => hag r (List.mem_append_left _ hr)), ?_⟩
  rw [hsub.step]
  exact fun r hr => hag r (List.mem_append_right _ hr)

-- ============================================================
-- La fila nueva
-- ============================================================

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **Existencia de una camarilla con cima de hijo permitido** (la versión de existencia de `AvoidExact`). -/
def AvoidSat (g : GPathB) (d : NodeId) (forb : PathNodeId → Bool) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct g V R → (∀ b ∈ P, SecAgrees V b) → GoodTops g d forb V → (∃ y, V y) →
    ∃ S, Carried g S ∧ (∀ r ∈ P, Agrees g.current_step S r) ∧ forb (shiftPid (S (g.current_step - 1)) d) = false

theorem avoidSat_of_avoidExact (hav : AvoidExact g d forb) : AvoidSat g d forb := by
  intro P V R hst ha hgood ⟨y, hy⟩
  obtain ⟨S, hS, hag, _, _, hf⟩ := hav P y y V R hst ha hgood (hst.refl hy)
  exact ⟨S, hS, hag, hf⟩

/-- **Sin ventana saltada, `AvoidSat` sale de `SecExact`.** -/
theorem avoidSat_of_noSkip (hse : SecExact g) (hpos : 0 < g.current_step) (hskip : g.skipsWindow d forb = false) :
    AvoidSat g d forb := by
  intro P V R hst ha _ hne
  obtain ⟨S, hS, hag⟩ := hse P V R hst ha hne
  refine ⟨S, hS, hag, ?_⟩
  have hmem : shiftPid (S (g.current_step - 1)) d ∈ g.shiftRowIds d := by
    unfold shiftRowIds
    rw [if_pos hpos, AbsSatBin.GraphPath.Model.GPathM.mem_dedupPids]
    exact List.mem_map.mpr ⟨_, top_newParents hS hpos, rfl⟩
  unfold skipsWindow at hskip
  exact List.any_eq_false.mp hskip _ hmem |> fun h => by simpa using h

/-- **La fila nueva conserva `SecExact`** bajo `AvoidSat`. -/
theorem secExact_addNode (hav : AvoidSat g d forb) (hdocs : AliveDocs g) (hb : Below g) (hls : LinksStep g)
    (htop0 : TopNoSons g) (hpos : 0 < g.current_step) (hd : d.step = g.current_step) :
    SecExact (g.addNode d title forb) := by
  intro P V R hst ha ⟨y, hy⟩
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  have hdown := secStruct_addNode_down (title := title) (forb := forb) hdocs hb hls hd hst
  -- un nodo de V en el paso 0 (viejo) y otro en el paso nuevo (de la fila)
  obtain ⟨q0, hq0s, hyq0, _⟩ := hst.pair (hst.refl hy) 0 (Int.le_refl 0) (by rw [hcs]; omega)
  have hq0V := (hst.dom hyq0).2
  obtain ⟨qt, hqts, hyqt, _⟩ := hst.pair (hst.refl hy) g.current_step (by omega) (by rw [hcs]; omega)
  have hqtV := (hst.dom hyqt).2
  have hP : ∀ r ∈ P, r.step = g.current_step → r = d := by
    intro r hr hrs
    have hqd : qt.id = d := by
      rcases alive_addNode_cases (title := title) hdocs hb hd (hst.alive hqtV) with ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · exact Machine.mapId_of_mem_shiftRowIds (List.mem_filter.mp h).1
    rw [← hqd]
    exact (ha r hr hqtV (by rw [hqts, hrs])).symm
  -- las cimas viejas de V tienen hijo permitido (su hijo en V es de la fila)
  have hgood : GoodTops g d forb (fun q => V q ∧ q.id.step < g.current_step) := by
    rintro q ⟨hq, _⟩ hqs
    obtain ⟨m, hm, _, hson⟩ := hst.node hq
    obtain ⟨s, hs, _⟩ := hson (by rw [hcs]; omega)
    rw [node?_addNode_old (title := title) hd (by omega)] at hm
    cases hn : g.node? q with
    | none => rw [hn] at hm; cases hm
    | some n =>
      rw [hn] at hm; cases hm
      have hnid := node?_id hn
      have hsons : n.sons = [] := htop0 n (node?_mem hn) (by rw [hnid]; omega)
      simp only [withGained, hsons, List.nil_append] at hs
      have ⟨hs1, hs2⟩ := List.mem_filter.mp hs
      have hqp := List.contains_iff_mem.mp hs2
      rw [hnid] at hqp
      have hsh : shiftPid q d = s := by simpa using (List.mem_filter.mp hqp).2
      rw [hsh]
      simpa using (List.mem_filter.mp hs1).2
  obtain ⟨S, hc, hag, hf⟩ := hav P _ _ hdown (fun r hr' _ hq hqs => ha r hr' hq.1 hqs) hgood
    ⟨q0, hq0V, by omega⟩
  obtain ⟨hn, hp⟩ := son_in_row_of (d := d) (forb := forb) hpos (top_newParents hc hpos) hf
  obtain ⟨hc', hag', _, _⟩ := extend_through (title := title) hc hpos hb hd hag hP hn hp
  exact ⟨_, hc', hag'⟩

-- ============================================================
-- El join
-- ============================================================

/-- **`SecSplit`**: una estructura cerrada no vacía de la unión que concuerda con `P` da una en algún lado. -/
def SecSplit (e g : GPathB) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct (doJoin e g) V R → (∀ b ∈ P, SecAgrees V b) → (∃ y, V y) →
    (∃ (V' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
        SecStruct e V' R' ∧ (∀ b ∈ P, SecAgrees V' b) ∧ ∃ y, V' y) ∨
    (∃ (V' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
        SecStruct g V' R' ∧ (∀ b ∈ P, SecAgrees V' b) ∧ ∃ y, V' y)

/-- **El join conserva `SecExact` bajo `SecSplit`.** -/
theorem secExact_doJoin {e g : GPathB} (he : SecExact e) (hg : SecExact g) (hsp : SecSplit e g) :
    SecExact (doJoin e g) := by
  by_cases hok : okJoin e g = true
  · intro P V R hst ha hne
    rw [step_doJoin]
    rcases hsp P V R hst ha hne with ⟨V', R', h1, h2, h3⟩ | ⟨V', R', h1, h2, h3⟩
    · obtain ⟨S, hS, hag⟩ := he P V' R' h1 h2 h3
      exact ⟨S, carried_doJoin_left hS, hag⟩
    · obtain ⟨S, hS, hag⟩ := hg P V' R' h1 h2 h3
      rw [step_eq_of_okJoin hok]
      exact ⟨S, carried_doJoin_right hok hS, hag⟩
  · have : doJoin e g = e := by unfold doJoin; rw [if_neg hok]
    rw [this]
    exact he

end GPathB

-- ============================================================
-- La línea
-- ============================================================

namespace SecLine

open GPathB Driver Machine Final

/-- El invariante de un estado de la línea: `SecExact` y la contabilidad de `KInv`. -/
def SInv (g : GPathB) : Prop :=
  SecExact g ∧ NodupIds g ∧ EdgesAlive g ∧ LinksStep g ∧ AboveZero g ∧ TopNoSons g ∧ LinksInv g

/-- `AvoidSat` en las ventanas saltadas. -/
def SkipHyp (φ : Cnf) : Prop :=
  ∀ T key g d, StateOk T key g → SInv g → 1 ≤ T → d ∈ sonsOfMap φ key →
    (g.filterAll (reqOf φ d)).isValid = true →
    (g.filterAll (reqOf φ d)).skipsWindow d (isProhibited φ) = true →
    AvoidSat (g.filterAll (reqOf φ d)) d (isProhibited φ)

/-- **Las dos hipótesis de existencia**: `SecSplit` en los joins y `AvoidSat` en las ventanas saltadas. -/
structure HypsSec (φ : Cnf) : Prop where
  split : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → SecSplit e g
  skip  : SkipHyp φ

theorem sInv_filterAll {g : GPathB} (hk : SInv g) (hd : AliveDocs g) (reqs : List NodeId) :
    SInv (g.filterAll reqs) :=
  ⟨secExact_filterAll hk.1 hd hk.2.1 reqs, revPrims_filterAll revPrims_nodupIds _ _ hk.2.1,
   revPrims_filterAll revPrims_edgesAlive _ _ hk.2.2.1, revPrims_filterAll revPrims_linksStep _ _ hk.2.2.2.1,
   revPrims_filterAll revPrims_aboveZero _ _ hk.2.2.2.2.1, revPrims_filterAll revPrims_topNoSons _ _ hk.2.2.2.2.2.1,
   revPrims_filterAll revPrims_linksInv _ _ hk.2.2.2.2.2.2⟩

theorem sInv_upFiltering {φ : Cnf} (Hs : SkipHyp φ) {T : Int} {key d : NodeId} {g : GPathB} (hg : StateOk T key g)
    (hk : SInv g) (hT : 1 ≤ T) (hd : d ∈ sonsOfMap φ key)
    (hv : (g.upFiltering (reqOf φ d) d "" (isProhibited φ)).isValid = true) :
    SInv (g.upFiltering (reqOf φ d) d "" (isProhibited φ)) := by
  have hs := shrinks_filterAll g (reqOf φ d)
  have hstep : (g.filterAll (reqOf φ d)).current_step = T := (step_of_shrinks hs).trans hg.step
  have hdstep : d.step = (g.filterAll (reqOf φ d)).current_step := by
    rw [hstep, sonsOfMap_step φ key d hd, hg.key]; omega
  have hf := sInv_filterAll hk hg.docs (reqOf φ d)
  have hfd : AliveDocs (g.filterAll (reqOf φ d)) := aliveDocs_filterAll hg.docs _
  have hfb : Below (g.filterAll (reqOf φ d)) := below_of_shrinks hs hg.below
  unfold upFiltering up at hv ⊢
  split
  · rename_i hvf
    let f := g.filterAll (reqOf φ d)
    let a := f.addNode d "" (isProhibited φ)
    have hfpos : 0 < f.current_step := by show 0 < (g.filterAll (reqOf φ d)).current_step; omega
    have hav : AvoidSat f d (isProhibited φ) := by
      cases hsk : f.skipsWindow d (isProhibited φ)
      · exact avoidSat_of_noSkip hf.1 hfpos hsk
      · exact Hs T key g d hg hk hT hd hvf hsk
    have hka : SecExact a :=
      secExact_addNode hav hfd hfb hf.2.2.2.1 hf.2.2.2.2.2.1 hfpos hdstep
    have hnd : NodupIds a := nodupIds_addNode hf.2.1 hfb hdstep
    have hda : AliveDocs a := aliveDocs_addNode hfd
    rw [review_eq_filterAll]
    exact ⟨secExact_filterAll hka hda hnd [], revPrims_filterAll revPrims_nodupIds _ _ hnd,
      revPrims_filterAll revPrims_edgesAlive _ _ (edgesAlive_addNode hf.2.2.1),
      revPrims_filterAll revPrims_linksStep _ _ (linksStep_addNode hf.2.2.2.1 hdstep),
      revPrims_filterAll revPrims_aboveZero _ _ (aboveZero_addNode hf.2.2.2.2.1 (by omega)),
      revPrims_filterAll revPrims_topNoSons _ _ (topNoSons_addNode hfb),
      revPrims_filterAll revPrims_linksInv _ _ (linksInv_addNode hf.2.2.2.2.2.2 hfb hf.2.2.2.2.1 hdstep)⟩
  · rename_i hvf
    rw [if_neg hvf] at hv
    exact absurd hv hvf

def LineS (line : Line) : Prop := ∀ kv ∈ line, SInv kv.2

theorem sInv_doJoin_of {e g : GPathB} (hsp : SecSplit e g) (hke : SInv e) (hkg : SInv g) : SInv (doJoin e g) := by
  refine ⟨secExact_doJoin hke.1 hkg.1 hsp, nodupIds_doJoin hke.2.1 hkg.2.1,
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

theorem sInv_doJoin {φ : Cnf} (H : HypsSec φ) {T : Int} (hT : 2 ≤ T) {key : NodeId} {e g : GPathB}
    (he : StateOk T key e) (hg : StateOk T key g) (hke : SInv e) (hkg : SInv g) : SInv (doJoin e g) :=
  sInv_doJoin_of (H.split T key e g hT he hg hke hkg) hke hkg

theorem lineS_insert {φ : Cnf} (H : HypsSec φ) {T : Int} (hT : 2 ≤ T) {line : Line} {key : NodeId} {g : GPathB}
    (hl : LineOk T line) (hlk : LineS line) (hg : StateOk T key g) (hk : SInv g) :
    LineS (Driver.insert line key g) := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    subst hkey
    have hmem := List.mem_of_find?_eq_some hfind
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact sInv_doJoin H hT (hl _ hmem) hg (hlk _ hmem) hk
    · exact hlk kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hlk kv h
    · rw [List.mem_singleton] at h; subst h; exact hk

theorem lineS_advance {φ : Cnf} (H : HypsSec φ) {T : Int} (hT : 1 ≤ T) {line : Line} (hl : LineOk T line)
    (hlk : LineS line) : LineS (advance φ line) := by
  have key : ∀ (l : Line), (∀ kv ∈ l, kv ∈ line) → ∀ next, LineOk (T + 1) next → LineS next →
      LineOk (T + 1) (l.foldl (fun next kv => sendAll φ kv next) next) ∧
        LineS (l.foldl (fun next kv => sendAll φ kv next) next) := by
    intro l
    induction l with
    | nil => intro _ next h1 h2; exact ⟨h1, h2⟩
    | cons kv rest ih =>
      intro hsub next h1 h2
      have hkv := hsub kv (List.mem_cons_self ..)
      have hsend : ∀ (ds : List NodeId), (∀ d ∈ ds, d ∈ sonsOfMap φ kv.1) → ∀ nx, LineOk (T + 1) nx →
          LineS nx → LineOk (T + 1) (ds.foldl (sendTo φ kv.2) nx) ∧ LineS (ds.foldl (sendTo φ kv.2) nx) := by
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
              exact lineS_insert H (by omega) a b (stateOk_upFiltering (hl kv hkv) hd hv)
                (sInv_upFiltering H.skip (hl kv hkv) (hlk kv hkv) hT hd hv)
            · exact b
      simp only [List.foldl_cons]
      obtain ⟨a, b⟩ := hsend _ (fun _ h => h) next h1 h2
      exact ih (fun kv' h => hsub kv' (List.mem_cons_of_mem _ h)) _ a b
  exact (key line (fun _ h => h) [] (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil)).2

theorem sInv_initSeed : SInv (initSeed (⟨0, 0⟩ : NodeId) "") :=
  let h := kInv_initSeed
  ⟨secExact_of_kernelExact h.1, h.2⟩

theorem stepsS {φ : Cnf} (H : HypsSec φ) :
    ∀ (n : Nat) (t : Int) (line : Line), 0 ≤ t → LineOk (t + 1) line → LineS line →
      LineOk (t + n + 1) (steps φ n line) ∧ LineS (steps φ n line) := by
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
    have h2 := lineS_advance H (by omega) hl hk
    have := ih (t + 1) (advance φ line) (by omega) h1 h2
    rw [show t + 1 + (n : Int) = t + ((n + 1 : Nat) : Int) by push_cast; omega] at this
    exact this

/-- **Todo estado de la línea final cumple `SInv`.** -/
theorem run_sInv {φ : Cnf} (H : HypsSec φ) : ∀ kv ∈ run φ, StateOk (stepCount φ) kv.1 kv.2 ∧ SInv kv.2 := by
  have hpos := stepCount_pos φ
  have hl0 := (init_inv φ (fun _ => false)).1
  have hk0 : LineS (init φ) := by
    rw [init_eq]
    intro kv hkv
    rw [List.mem_singleton] at hkv; subst hkv
    exact sInv_initSeed
  have hn : (0 : Int) + ((stepCount φ - 1).toNat : Int) = stepCount φ - 1 := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  obtain ⟨hl, hk⟩ := stepsS H (stepCount φ - 1).toNat 0 (init φ) (Int.le_refl 0) (by simpa using hl0) hk0
  rw [hn, show stepCount φ - 1 + 1 = stepCount φ by omega] at hl
  intro kv hkv
  exact ⟨hl kv hkv, hk kv hkv⟩

-- ============================================================
-- El lector
-- ============================================================

/-- **El veredicto del lector es la satisfacibilidad si todo estado de la línea final cumple `SInv`.** -/
theorem readerVerdict_iff_of_final {φ : Cnf} (hbd : Bounded φ)
    (hfin : ∀ kv ∈ run φ, StateOk (stepCount φ) kv.1 kv.2 ∧ SInv kv.2) :
    readerVerdict φ = true ↔ Satisfiable φ := by
  apply Decode.readerVerdict_iff_of_noZombie hbd
  intro kv hkv h hvis hval
  obtain ⟨hok, hk⟩ := hfin kv hkv
  have hcs : 2 ≤ kv.2.current_step := by rw [hok.step]; unfold stepCount; omega
  have hcl := (cInv_visited hok.docs hk.2.1 hok.below hk.2.2.2.2.1 hcs h hvis).2.2.2.2.2 hval
  obtain ⟨P, rfl⟩ := visited_pinSeq hvis
  have hd0 : AliveDocs { kv.2 with dirty := true } := aliveDocs_dirty hok.docs true
  have hnd0 : NodupIds { kv.2 with dirty := true } := revPrims_nodupIds.dirty _ _ hk.2.1
  have hse1 : SecExact (reviewAll kv.2) := by
    show SecExact (review { kv.2 with dirty := true })
    rw [review_eq_filterAll]
    exact secExact_filterAll (secExact_dirty hk.1 true) hd0 hnd0 []
  have hd1 : AliveDocs (reviewAll kv.2) := aliveDocs_review hd0
  have hnd1 : NodupIds (reviewAll kv.2) := revPrims_review revPrims_nodupIds _ hnd0
  obtain ⟨hst, ha⟩ := sec_of_pinSeq (Sub.refl _) hnd1 hd1 hval hcl
  have hcs1 : 0 < (pinSeq (reviewAll kv.2) P).current_step := by
    rw [step_pinSeq, show (reviewAll kv.2).current_step = kv.2.current_step from (shrinks_review _).1.step]
    omega
  obtain ⟨y, hy, _⟩ := alive_zero_of_valid hval hcs1
  obtain ⟨S, hS, hag⟩ := hse1 P _ _ hst ha ⟨y, hy⟩
  exact ⟨S, carried_pinSeq P _ hS hag⟩

/-- **El veredicto del lector es la satisfacibilidad bajo `SecSplit` y `AvoidSat`.** -/
theorem readerVerdict_iff_of_secSplit {φ : Cnf} (hbd : Bounded φ) (H : HypsSec φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (run_sInv H)

/-- **`KernelUnion` ⟹ `SecSplit`**: la versión de existencia es más débil. -/
theorem secSplit_of_kernelUnion {e g : GPathB} (hu : KernelUnion e g) : SecSplit e g := by
  intro P V R hst ha ⟨y, hy⟩
  by_cases hok : okJoin e g = true
  · have hj : doJoin e g = join e g := by unfold doJoin; rw [if_pos hok]
    rw [hj] at hst
    rcases hu P y y ⟨V, R, hst, ha, hst.refl hy⟩ with ⟨V', R', h1, h2, h3⟩ | ⟨V', R', h1, h2, h3⟩
    · exact Or.inl ⟨V', R', h1, h2, y, (h1.dom h3).1⟩
    · exact Or.inr ⟨V', R', h1, h2, y, (h1.dom h3).1⟩
  · have hj : doJoin e g = e := by unfold doJoin; rw [if_neg hok]
    rw [hj] at hst
    exact Or.inl ⟨V, R, hst, ha, y, hy⟩

end SecLine

end AbsSatBingo.Model
