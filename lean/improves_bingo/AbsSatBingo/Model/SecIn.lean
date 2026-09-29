-- lean/improves_bingo/AbsSatBingo/Model/SecIn.lean
import AbsSatBingo.Model.AvoidSplit

/-!
# `SecIn`: la camarilla dentro de la estructura, y el veredicto con una sola hipótesis

`SecExact` pide, para cada estructura cerrada no vacía, **una** camarilla que concuerde; `SecIn` la pide **dentro** de
la estructura:

> **`SecIn g`**: toda estructura cerrada no vacía `V` de `g` que concuerda con `P` contiene una camarilla que
> concuerda con `P` (todos sus nodos están en `V`).

Medido en Julia (`probe_secin.jl`, 42 instancias, 4 UNSAT): estructuras cerradas al azar tras el UP (22 417) y en las
uniones (10 518): siempre contienen una camarilla; y la de la unión contiene una de un lado (10 518): 0 fallos.

Lo que compra:
* **la fila nueva ya no necesita `AvoidSat`** (`secIn_addNode`): la camarilla está dentro de `V`, su cima está en
  `V`, y su hijo en `V` también (la regla de enlaces de `V`), así que la ventana está permitida;
* el filtro, el review y el cambio de `dirty` la conservan (`secIn_filterAll`, `secIn_dirty`);
* el join la conserva bajo **`SecSplitIn`** (`secIn_doJoin`): una estructura cerrada no vacía de la unión contiene una
  de un lado;
* la semilla la cumple (`secIn_initSeed`).

Resultado: **`readerVerdict_iff_of_secIn`**, el veredicto del lector bajo `SecSplitIn` en los joins **como única
hipótesis** (con la separación y los colores ya demostrados a mano).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid)

namespace GPathB

open Machine (Below)

/-- **La camarilla dentro de la estructura.** -/
def SecIn (g : GPathB) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct g V R → (∀ b ∈ P, SecAgrees V b) → (∃ y, V y) →
    ∃ S, Carried g S ∧ (∀ r ∈ P, Agrees g.current_step S r) ∧
      ∀ k, 0 ≤ k → k < g.current_step → V (S k)

theorem secExact_of_secIn {g : GPathB} (h : SecIn g) : SecExact g := by
  intro P V R hst ha hne
  obtain ⟨S, hS, hag, _⟩ := h P V R hst ha hne
  exact ⟨S, hS, hag⟩

theorem secIn_dirty {g : GPathB} (hse : SecIn g) (b : Bool) : SecIn { g with dirty := b } := by
  intro P V R hst ha hne
  obtain ⟨S, hS, hag, hin⟩ := hse P V R ⟨hst.alive, hst.refl, hst.symm, hst.dom, hst.adj, hst.pair, hst.node,
    hst.par, hst.son⟩ ha hne
  exact ⟨S, carried_dirty hS b, hag, hin⟩

/-- **El filtro (y el review) conserva `SecIn`.** -/
theorem secIn_filterAll {x : GPathB} (hse : SecIn x) (hd : AliveDocs x) (hnd : NodupIds x) (Q : List NodeId) :
    SecIn (x.filterAll Q) := by
  intro P V R hst ha ⟨y, hy⟩
  have hsub := (shrinks_filterAll x Q).1
  have hv := isValid_of_sec hst hy
  obtain ⟨S, hS, hag, hin⟩ := hse (Q ++ P) V R (secStruct_of_sub hsub hnd hst) (by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact fun hq hqs => pinned_filterAll_list hd Q hv b hb _ (hst.alive hq) hqs
    · exact ha b hb) ⟨y, hy⟩
  refine ⟨S, carried_filterAll hS Q (fun r hr => hag r (List.mem_append_left _ hr)), ?_, ?_⟩
  · rw [hsub.step]
    exact fun r hr => hag r (List.mem_append_right _ hr)
  · intro k h0 h1
    exact hin k h0 (by rw [← hsub.step]; exact h1)

-- ============================================================
-- La fila nueva, sin AvoidSat
-- ============================================================

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **La fila nueva conserva `SecIn`**, con o sin ventana saltada. -/
theorem secIn_addNode (hse : SecIn g) (hdocs : AliveDocs g) (hb : Below g) (hls : LinksStep g)
    (htop0 : TopNoSons g) (hpos : 0 < g.current_step) (hd : d.step = g.current_step) :
    SecIn (g.addNode d title forb) := by
  intro P V R hst ha ⟨y, hy⟩
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  have hdown := secStruct_addNode_down (title := title) (forb := forb) hdocs hb hls hd hst
  -- un nodo viejo de V (paso 0) y otro de la fila (el paso nuevo)
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
  -- la camarilla dentro de la parte vieja de V
  obtain ⟨S, hc, hag, hin⟩ := hse P _ _ hdown (fun r hr' _ hq hqs => ha r hr' hq.1 hqs) ⟨q0, hq0V, by omega⟩
  -- su cima está en V; su hijo en V es el de la fila, y su ventana está permitida
  have htV : V (S (g.current_step - 1)) := (hin _ (by omega) (by omega)).1
  have hts : (S (g.current_step - 1)).id.step = g.current_step - 1 := hc.step _ (by omega) (by omega)
  obtain ⟨m, hm, _, hson⟩ := hst.node htV
  obtain ⟨s, hs, hRs⟩ := hson (by rw [hcs, hts]; omega)
  rw [node?_addNode_old (title := title) hd (by rw [hts]; omega)] at hm
  have hsV : V s := (hst.dom hRs).2
  have key : shiftPid (S (g.current_step - 1)) d = s ∧ forb (shiftPid (S (g.current_step - 1)) d) = false := by
    cases hn : g.node? (S (g.current_step - 1)) with
    | none => rw [hn] at hm; cases hm
    | some n =>
      rw [hn] at hm; cases hm
      have hnid := node?_id hn
      have hsons : n.sons = [] := htop0 n (node?_mem hn) (by rw [hnid, hts]; omega)
      simp only [withGained, hsons, List.nil_append] at hs
      have ⟨hs1, hs2⟩ := List.mem_filter.mp hs
      have hqp := List.contains_iff_mem.mp hs2
      rw [hnid] at hqp
      have hsh : shiftPid (S (g.current_step - 1)) d = s := by simpa using (List.mem_filter.mp hqp).2
      refine ⟨hsh, ?_⟩
      rw [hsh]
      simpa using (List.mem_filter.mp hs1).2
  obtain ⟨hn, hp⟩ := son_in_row_of (d := d) (forb := forb) hpos (top_newParents hc hpos) key.2
  obtain ⟨hc', hag', _, _⟩ := extend_through (title := title) hc hpos hb hd hag hP hn hp
  refine ⟨_, hc', hag', fun k h0 h1 => ?_⟩
  rw [hcs] at h1
  unfold extSel
  split
  · rw [key.1]; exact hsV
  · exact (hin k h0 (by omega)).1

-- ============================================================
-- El join
-- ============================================================

/-- **`SecSplitIn`**: una estructura cerrada no vacía de la unión que concuerda con `P` contiene una estructura
cerrada no vacía de un lado que concuerda con `P`. -/
def SecSplitIn (e g : GPathB) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct (doJoin e g) V R → (∀ b ∈ P, SecAgrees V b) → (∃ y, V y) →
    (∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
        SecStruct e W R' ∧ (∀ b ∈ P, SecAgrees W b) ∧ (∃ y, W y) ∧ ∀ y, W y → V y) ∨
    (∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
        SecStruct g W R' ∧ (∀ b ∈ P, SecAgrees W b) ∧ (∃ y, W y) ∧ ∀ y, W y → V y)

theorem secSplit_of_in {e g : GPathB} (h : SecSplitIn e g) : SecSplit e g := by
  intro P V R hst ha hne
  rcases h P V R hst ha hne with ⟨W, R', h1, h2, h3, _⟩ | ⟨W, R', h1, h2, h3, _⟩
  · exact Or.inl ⟨W, R', h1, h2, h3⟩
  · exact Or.inr ⟨W, R', h1, h2, h3⟩

/-- **El join conserva `SecIn` bajo `SecSplitIn`.** -/
theorem secIn_doJoin {e g : GPathB} (he : SecIn e) (hg : SecIn g) (hsp : SecSplitIn e g) :
    SecIn (doJoin e g) := by
  by_cases hok : okJoin e g = true
  · intro P V R hst ha hne
    rw [step_doJoin]
    rcases hsp P V R hst ha hne with ⟨W, R', h1, h2, h3, h4⟩ | ⟨W, R', h1, h2, h3, h4⟩
    · obtain ⟨S, hS, hag, hin⟩ := he P W R' h1 h2 h3
      exact ⟨S, carried_doJoin_left hS, hag, fun k h0 h1' => h4 _ (hin k h0 h1')⟩
    · obtain ⟨S, hS, hag, hin⟩ := hg P W R' h1 h2 h3
      rw [step_eq_of_okJoin hok]
      exact ⟨S, carried_doJoin_right hok hS, hag, fun k h0 h1' => h4 _ (hin k h0 h1')⟩
  · have : doJoin e g = e := by unfold doJoin; rw [if_neg hok]
    rw [this]
    exact he

-- ============================================================
-- La semilla
-- ============================================================

theorem secIn_initSeed : SecIn (initSeed (⟨0, 0⟩ : NodeId) "") := by
  let d : NodeId := ⟨0, 0⟩
  let root : PathNodeId := { id := d, parent_id := none, gparent_id := none }
  let a := GPathB.empty.addNode d "" (fun _ => false)
  have hal : a.alive = [root] := rfl
  have hnodes : a.nodes = [GPathB.empty.rowNode d "" root] := rfl
  let S : Int → PathNodeId := fun _ => root
  have hc : Carried a S := by
    apply carried_addNode (Machine.carried_empty S)
    · show root ∈ (GPathB.empty.shiftRowIds d).filter _
      refine List.mem_filter.mpr ⟨?_, rfl⟩
      unfold shiftRowIds
      rw [if_neg (show ¬ (0 : Int) < GPathB.empty.current_step by show ¬ (0 : Int) < 0; omega)]
      exact List.mem_singleton_self _
    · intro h; exact absurd h (by show ¬ (0 : Int) < 0; omega)
    · rfl
    · intro n hn; exact absurd hn List.not_mem_nil
    · rfl
  have hsa : SecIn a := by
    intro P V R hst ha ⟨y, hy⟩
    have hyr : y = root := by
      have := hst.alive hy
      rw [hal, List.mem_singleton] at this
      exact this
    subst hyr
    refine ⟨S, hc, ?_, fun _ _ _ => hy⟩
    intro r hr' h0 h1
    have h1' : r.step < 1 := h1
    have hr0 : r.step = 0 := by omega
    exact ha r hr' hy (by rw [hr0])
  have hnd : NodupIds a := by
    unfold NodupIds; rw [hnodes]; exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  have hda : AliveDocs a := Machine.aliveDocs_addNode (fun q hq => absurd hq List.not_mem_nil)
  have hup : initSeed d "" = a.filterAll [] := by
    unfold initSeed up
    rw [if_pos (show GPathB.empty.isValid = true by rfl)]
    rfl
  rw [hup]
  exact secIn_filterAll hsa hda hnd []

end GPathB

-- ============================================================
-- La línea y el veredicto
-- ============================================================

namespace SecLine

open GPathB Driver Machine Final

/-- El invariante: `SecIn` y `SInv`. -/
def SInvIn (g : GPathB) : Prop := SecIn g ∧ SInv g

/-- **La única hipótesis**: `SecSplitIn` en cada join de la línea, con lo demostrado a mano (un color por lado,
distintos, separados). -/
structure HypsIn (φ : Cnf) : Prop where
  split : ∀ T key e g a s, 2 ≤ T → StateOk T key e → StateOk T key g → SInvIn e → SInvIn g → Key (T - 2) a →
            Key (T - 2) s → a ≠ s → OriginIn e (T - 2) (· = a) → OriginIn g (T - 2) (· = s) →
            SecSplitIn e g

/-- **La llegada conserva `SInvIn` sin hipótesis**: `AvoidSat` sale de `SecIn` del estado filtrado. -/
theorem upProv_in (φ : Cnf) : UpProv φ SInvIn := by
  intro T key g d hg hk hT hd hv
  have hs := shrinks_filterAll g (reqOf φ d)
  have hstep : (g.filterAll (reqOf φ d)).current_step = T := (step_of_shrinks hs).trans hg.step
  have hdstep : d.step = (g.filterAll (reqOf φ d)).current_step := by
    rw [hstep, sonsOfMap_step φ key d hd, hg.key]; omega
  have hf := sInv_filterAll hk.2 hg.docs (reqOf φ d)
  have hfin : SecIn (g.filterAll (reqOf φ d)) := secIn_filterAll hk.1 hg.docs hk.2.2.1 _
  have hfd : AliveDocs (g.filterAll (reqOf φ d)) := aliveDocs_filterAll hg.docs _
  have hfb : Below (g.filterAll (reqOf φ d)) := below_of_shrinks hs hg.below
  -- AvoidSat del estado filtrado, por SecIn: la camarilla está dentro de V, con cima buena
  have havf : (g.filterAll (reqOf φ d)).isValid = true →
      (g.filterAll (reqOf φ d)).skipsWindow d (isProhibited φ) = true →
      AvoidSat (g.filterAll (reqOf φ d)) d (isProhibited φ) := by
    intro _ _ P V R hst ha hgood hne
    obtain ⟨S, hS, hag, hin⟩ := hfin P V R hst ha hne
    refine ⟨S, hS, hag, hgood _ (hin _ (by omega) (by omega)) (hS.step _ (by omega) (by omega))⟩
  refine ⟨?_, sInv_upFiltering_of hg hk.2 hT hd havf hv⟩
  unfold upFiltering up at hv ⊢
  split
  · rename_i hvf
    let f := g.filterAll (reqOf φ d)
    have hfpos : 0 < f.current_step := by show 0 < (g.filterAll (reqOf φ d)).current_step; omega
    have hka : SecIn (f.addNode d "" (isProhibited φ)) :=
      secIn_addNode hfin hfd hfb hf.2.2.2.1 hf.2.2.2.2.2.1 hfpos hdstep
    have hnd : NodupIds (f.addNode d "" (isProhibited φ)) := nodupIds_addNode hf.2.1 hfb hdstep
    have hda : AliveDocs (f.addNode d "" (isProhibited φ)) := aliveDocs_addNode hfd
    rw [review_eq_filterAll]
    exact secIn_filterAll hka hda hnd []
  · rename_i hvf
    rw [if_neg hvf] at hv
    exact absurd hv hvf

/-- En cada join, con un color por lado, `SecSplitIn` da `SInvIn` de la unión. -/
theorem joinProv_in {φ : Cnf} (H : HypsIn φ) {U : Int} (hU : 2 ≤ U) : JoinProv SInvIn U := by
  intro key s e g A he hg hke hkg hoe hog hsA hAk hsk
  have hne : ∀ c, A c → c ≠ s := fun c hc h => hsA (h ▸ hc)
  have hoe' : OriginIn e (U - 2) (· = other s) :=
    originIn_mono hoe (fun c hc => eq_other (hAk c hc) hsk (hne c hc))
  have hos : other s ≠ s := by
    intro h
    have := congrArg NodeId.index h
    simp only [other] at this
    rcases hsk.2 with h' | h' <;> omega
  have hok : Key (U - 2) (other s) := by
    refine ⟨hsk.1, ?_⟩
    simp only [other]
    rcases hsk.2 with h' | h' <;> omega
  have hsp := H.split U key e g (other s) s hU he hg hke hkg hok hsk hos hoe' hog
  exact ⟨secIn_doJoin hke.1 hkg.1 hsp, sInv_doJoin_of (secSplit_of_in hsp) hke.2 hkg.2⟩

theorem sInvIn_initSeed : SInvIn (initSeed (⟨0, 0⟩ : NodeId) "") := ⟨secIn_initSeed, sInv_initSeed⟩

/-- **El veredicto del lector es la satisfacibilidad bajo `SecSplitIn` en los joins, como única hipótesis.** -/
theorem readerVerdict_iff_of_secIn {φ : Cnf} (hbd : Bounded φ) (H : HypsIn φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (fun kv hkv =>
    let h := run_prov (upProv_in φ) (fun _ hU => joinProv_in H hU) sInvIn_initSeed kv hkv
    ⟨h.1, h.2.2⟩)

end SecLine

end AbsSatBingo.Model
