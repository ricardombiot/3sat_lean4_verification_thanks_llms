-- lean/improves_bingo/AbsSatBingo/Model/NodeIn.lean
import AbsSatBingo.Model.SecSplitInParts

/-!
# `NodeIn`: todo nodo de una estructura cerrada está en una camarilla dentro de ella

> **`NodeIn g`**: para toda estructura cerrada `V` de `g` que concuerda con `P` y todo `x ∈ V`, hay una camarilla que
> concuerda con `P`, **pasa por `x`** y tiene todos sus nodos en `V`.

Medido (`probe_secin.jl`, 26 instancias): 113 569 nodos de estructuras cerradas al azar, tras el UP y en las uniones,
0 fallos. Es más fuerte que `SecIn` (`secIn_of_nodeIn`) y más natural: dice «nada de lo que una estructura cerrada
contiene está fuera de sus soluciones».

Operación por operación:
* el filtro, el review, `dirty` y la semilla: sin hipótesis;
* **la fila nueva, sin hipótesis** (`nodeIn_addNode`): para un nodo viejo, su camarilla dentro de `V` se alarga con el
  hijo de su cima, que está en `V`; para un nodo nuevo, la camarilla de su padre (en `V`) se alarga con él;
* el join, bajo **`NodeSplitIn`** (`nodeIn_doJoin`): todo nodo de una estructura cerrada de la unión está en una
  estructura cerrada de un lado dentro de ella.

Veredicto: **`readerVerdict_iff_of_nodeIn`**. Y el ataque al join, nodo a nodo (`nodeSplitIn_of_colour`): basta que
cada nodo `x` de `V` sobreviva, dentro de `V`, a fijar el color de algún lado (**`NodeColour`**), más `SideEdgesAt`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid)

namespace GPathB

open Machine (Below)

/-- **Todo nodo de una estructura cerrada está en una camarilla dentro de ella.** -/
def NodeIn (g : GPathB) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct g V R → (∀ b ∈ P, SecAgrees V b) → ∀ x, V x →
    ∃ S, Carried g S ∧ (∀ r ∈ P, Agrees g.current_step S r) ∧
      (∀ k, 0 ≤ k → k < g.current_step → V (S k)) ∧ OnS g.current_step S x

theorem secIn_of_nodeIn {g : GPathB} (h : NodeIn g) : SecIn g := by
  intro P V R hst ha ⟨x, hx⟩
  obtain ⟨S, hS, hag, hin, _⟩ := h P V R hst ha x hx
  exact ⟨S, hS, hag, hin⟩

theorem nodeIn_dirty {g : GPathB} (hse : NodeIn g) (b : Bool) : NodeIn { g with dirty := b } := by
  intro P V R hst ha x hx
  obtain ⟨S, hS, hag, hin, hon⟩ := hse P V R ⟨hst.alive, hst.refl, hst.symm, hst.dom, hst.adj, hst.pair,
    hst.node, hst.par, hst.son⟩ ha x hx
  exact ⟨S, carried_dirty hS b, hag, hin, hon⟩

/-- **El filtro (y el review) conserva `NodeIn`.** -/
theorem nodeIn_filterAll {x0 : GPathB} (hse : NodeIn x0) (hd : AliveDocs x0) (hnd : NodupIds x0) (Q : List NodeId) :
    NodeIn (x0.filterAll Q) := by
  intro P V R hst ha x hx
  have hsub := (shrinks_filterAll x0 Q).1
  have hv := isValid_of_sec hst hx
  obtain ⟨S, hS, hag, hin, hon⟩ := hse (Q ++ P) V R (secStruct_of_sub hsub hnd hst) (by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact fun hq hqs => pinned_filterAll_list hd Q hv b hb _ (hst.alive hq) hqs
    · exact ha b hb) x hx
  refine ⟨S, carried_filterAll hS Q (fun r hr => hag r (List.mem_append_left _ hr)), ?_, ?_, ?_⟩
  · rw [hsub.step]
    exact fun r hr => hag r (List.mem_append_right _ hr)
  · intro k h0 h1
    exact hin k h0 (by rw [← hsub.step]; exact h1)
  · obtain ⟨k, h0, h1, hk⟩ := hon
    exact ⟨k, h0, by rw [hsub.step]; exact h1, hk⟩

-- ============================================================
-- La fila nueva, sin hipótesis
-- ============================================================

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **La fila nueva conserva `NodeIn`**, con o sin ventana saltada. -/
theorem nodeIn_addNode (hse : NodeIn g) (hdocs : AliveDocs g) (hb : Below g) (hls : LinksStep g)
    (htop0 : TopNoSons g) (hpos : 0 < g.current_step) (hd : d.step = g.current_step) :
    NodeIn (g.addNode d title forb) := by
  intro P V R hst ha x hx
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  have hdown := secStruct_addNode_down (title := title) (forb := forb) hdocs hb hls hd hst
  have hadown : ∀ r ∈ P, SecAgrees (fun q => V q ∧ q.id.step < g.current_step) r :=
    fun r hr' _ hq hqs => ha r hr' hq.1 hqs
  -- lo que P fija en el paso nuevo es d
  obtain ⟨qt, hqts, hxqt, _⟩ := hst.pair (hst.refl hx) g.current_step (by omega) (by rw [hcs]; omega)
  have hqtV := (hst.dom hxqt).2
  have hP : ∀ r ∈ P, r.step = g.current_step → r = d := by
    intro r hr hrs
    have hqd : qt.id = d := by
      rcases alive_addNode_cases (title := title) hdocs hb hd (hst.alive hqtV) with ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · exact Machine.mapId_of_mem_shiftRowIds (List.mem_filter.mp h).1
    rw [← hqd]
    exact (ha r hr hqtV (by rw [hqts, hrs])).symm
  rcases alive_addNode_cases (title := title) hdocs hb hd (hst.alive hx) with ⟨_, hxs⟩ | ⟨hxn, hxs⟩
  · -- x viejo: su camarilla dentro de la parte vieja de V, alargada con el hijo de su cima (en V)
    obtain ⟨S, hc, hag, hin, hon⟩ := hse P _ _ hdown hadown x ⟨hx, hxs⟩
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
    obtain ⟨hc', hag', hkeep, _⟩ := extend_through (title := title) hc hpos hb hd hag hP hn hp
    refine ⟨_, hc', hag', fun k h0 h1 => ?_, hkeep x hon⟩
    rw [hcs] at h1
    unfold extSel
    split
    · rw [key.1]; exact hsV
    · exact (hin k h0 (by omega)).1
  · -- x nuevo: la camarilla de su padre (en V), alargada con x
    have hm := node?_addNode_new (title := title) hb hd hxn
    obtain ⟨m, hm', hpar, _⟩ := hst.node hx
    rw [hm] at hm'
    cases hm'
    obtain ⟨q, _, hq⟩ := parent_of_row hpos hxn
    have hroot : x.parent_id.isNone = false := by rw [hq]; rfl
    obtain ⟨p, hp, hxp⟩ := hpar hroot
    have hpV := (hst.dom hxp).2
    obtain ⟨_, _, _, hps⟩ := step_of_newParents (rowParents_sub hp)
    obtain ⟨S, hc, hag, hin, hon⟩ := hse P _ _ hdown hadown p ⟨hpV, by omega⟩
    have htop' := top_of_onS hc hon hps
    obtain ⟨hc', hag', _, hx'⟩ := extend_through (title := title) hc hpos hb hd hag hP hxn
      (by rw [htop']; exact hp)
    refine ⟨_, hc', hag', fun k h0 h1 => ?_, hx'⟩
    rw [hcs] at h1
    unfold extSel
    split
    · exact hx
    · exact (hin k h0 (by omega)).1

-- ============================================================
-- El join y la semilla
-- ============================================================

/-- **`NodeSplitIn`**: todo nodo de una estructura cerrada de la unión está en una estructura cerrada de un lado,
dentro de ella, que concuerda con `P`. -/
def NodeSplitIn (e g : GPathB) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct (doJoin e g) V R → (∀ b ∈ P, SecAgrees V b) → ∀ x, V x →
    (∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
        SecStruct e W R' ∧ (∀ b ∈ P, SecAgrees W b) ∧ W x ∧ ∀ y, W y → V y) ∨
    (∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
        SecStruct g W R' ∧ (∀ b ∈ P, SecAgrees W b) ∧ W x ∧ ∀ y, W y → V y)

theorem secSplitIn_of_node {e g : GPathB} (h : NodeSplitIn e g) : SecSplitIn e g := by
  intro P V R hst ha ⟨x, hx⟩
  rcases h P V R hst ha x hx with ⟨W, R', h1, h2, h3, h4⟩ | ⟨W, R', h1, h2, h3, h4⟩
  · exact Or.inl ⟨W, R', h1, h2, ⟨x, h3⟩, h4⟩
  · exact Or.inr ⟨W, R', h1, h2, ⟨x, h3⟩, h4⟩

/-- **El join conserva `NodeIn` bajo `NodeSplitIn`.** -/
theorem nodeIn_doJoin {e g : GPathB} (he : NodeIn e) (hg : NodeIn g) (hsp : NodeSplitIn e g) :
    NodeIn (doJoin e g) := by
  by_cases hok : okJoin e g = true
  · intro P V R hst ha x hx
    rw [step_doJoin]
    rcases hsp P V R hst ha x hx with ⟨W, R', h1, h2, h3, h4⟩ | ⟨W, R', h1, h2, h3, h4⟩
    · obtain ⟨S, hS, hag, hin, hon⟩ := he P W R' h1 h2 x h3
      exact ⟨S, carried_doJoin_left hS, hag, fun k h0 h1' => h4 _ (hin k h0 h1'), hon⟩
    · obtain ⟨S, hS, hag, hin, hon⟩ := hg P W R' h1 h2 x h3
      rw [step_eq_of_okJoin hok]
      exact ⟨S, carried_doJoin_right hok hS, hag, fun k h0 h1' => h4 _ (hin k h0 h1'), hon⟩
  · have : doJoin e g = e := by unfold doJoin; rw [if_neg hok]
    rw [this]
    exact he

theorem nodeIn_initSeed : NodeIn (initSeed (⟨0, 0⟩ : NodeId) "") := by
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
  have hsa : NodeIn a := by
    intro P V R hst ha y hy
    have hyr : y = root := by
      have := hst.alive hy
      rw [hal, List.mem_singleton] at this
      exact this
    subst hyr
    refine ⟨S, hc, ?_, fun _ _ _ => hy, ⟨0, Int.le_refl 0, by decide, rfl⟩⟩
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
  exact nodeIn_filterAll hsa hda hnd []

-- ============================================================
-- El ataque al join, nodo a nodo
-- ============================================================

/-- **`NodeColour`**: todo nodo `x` de una estructura cerrada `V` de la unión sobrevive, dentro de `V`, a fijar algún
color del paso `k`. -/
def NodeColour (u : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct u V R → (∀ b ∈ P, SecAgrees V b) → ∀ x, V x →
    ∃ c : NodeId, c.step = k ∧ ∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
      SecStruct u W R' ∧ (∀ b ∈ P ++ [c], SecAgrees W b) ∧ W x ∧ ∀ y, W y → V y

/-- **`NodeColour` + `SideEdgesAt` (con los colores de los lados) ⟹ `NodeSplitIn`.** El color que sobrevive es el
de un lado (el testigo del paso `k` de `x` en `W` tiene ese color y está vivo en la unión), y fijada la unión en ese
color, las parejas son del lado. -/
theorem nodeSplitIn_of_colour {e g : GPathB} {k : Int} {a s : NodeId} (hk0 : 0 ≤ k) (hkc : k < e.current_step)
    (hcs : e.current_step = g.current_step) (hle : LinksInv e) (hlg : LinksInv g) (hee : EdgesAlive e)
    (heg : EdgesAlive g) (ha : a.step = k) (hs : s.step = k) (hoa : OffSide g a) (hos : OffSide e s)
    (ho : OriginIn (join e g) k (fun c => c = a ∨ c = s))
    (hnc : NodeColour (join e g) k) (hse : SideEdgesAt e g k) : NodeSplitIn e g := by
  intro P V R hst hag x hx
  by_cases hok : okJoin e g = true
  · have hj : doJoin e g = join e g := by unfold doJoin; rw [if_pos hok]
    rw [hj] at hst
    obtain ⟨c, hck, W, R', h1, h2, h3, h4⟩ := hnc P V R hst hag x hx
    have hWc : SecAgrees W c := h2 c (List.mem_append_right _ (List.mem_singleton_self c))
    have h2' : ∀ b ∈ P, SecAgrees W b := fun b hb => h2 b (List.mem_append_left _ hb)
    -- el color c es el de un lado: el testigo de x en el paso k lo tiene
    obtain ⟨r, hrs, hxr, _⟩ := h1.pair (h1.refl h3) k hk0 (by show k < e.current_step; exact hkc)
    have hrc : r.id = c := hWc (h1.dom hxr).2 (by rw [hrs, hck])
    rcases ho r (h1.alive (h1.dom hxr).2) hrs with hra | hrs'
    · have hca : c = a := hrc.symm.trans hra
      subst hca
      have hadj : ∀ {y w}, R' y w → e.Adj y w := fun hr => ((hse c ha).1 hoa) W R' h1 hWc hr
      have hal : ∀ {y}, W y → y ∈ e.alive := fun hy => (hee _ _ (hadj (h1.refl hy))).1
      exact Or.inl ⟨W, R', secStruct_of_sideEdges (isUnion_join_left hle hlg hee heg) h1 hal hadj hle, h2', h3, h4⟩
    · have hcs' : c = s := hrc.symm.trans hrs'
      subst hcs'
      have hadj : ∀ {y w}, R' y w → g.Adj y w := fun hr => ((hse c hs).2 hos) W R' h1 hWc hr
      have hal : ∀ {y}, W y → y ∈ g.alive := fun hy => (heg _ _ (hadj (h1.refl hy))).1
      exact Or.inr ⟨W, R', secStruct_of_sideEdges (isUnion_join_right hcs hle hlg hee heg) h1 hal hadj hlg,
        h2', h3, h4⟩
  · have hj : doJoin e g = e := by unfold doJoin; rw [if_neg hok]
    rw [hj] at hst
    exact Or.inl ⟨V, R, hst, hag, hx, fun _ h => h⟩

end GPathB

-- ============================================================
-- La línea y el veredicto
-- ============================================================

namespace SecLine

open GPathB Driver Machine Final

def SInvN (g : GPathB) : Prop := NodeIn g ∧ SInv g

/-- **Una sola hipótesis, nodo a nodo**: `NodeSplitIn` en cada join de la línea. -/
structure HypsNode (φ : Cnf) : Prop where
  split : ∀ T key e g a s, 2 ≤ T → StateOk T key e → StateOk T key g → SInvN e → SInvN g → Key (T - 2) a →
            Key (T - 2) s → a ≠ s → OriginIn e (T - 2) (· = a) → OriginIn g (T - 2) (· = s) →
            NodeSplitIn e g

theorem upProv_node (φ : Cnf) : UpProv φ SInvN := by
  intro T key g d hg hk hT hd hv
  have hs := shrinks_filterAll g (reqOf φ d)
  have hstep : (g.filterAll (reqOf φ d)).current_step = T := (step_of_shrinks hs).trans hg.step
  have hdstep : d.step = (g.filterAll (reqOf φ d)).current_step := by
    rw [hstep, sonsOfMap_step φ key d hd, hg.key]; omega
  have hf := sInv_filterAll hk.2 hg.docs (reqOf φ d)
  have hfin : NodeIn (g.filterAll (reqOf φ d)) := nodeIn_filterAll hk.1 hg.docs hk.2.2.1 _
  have hfd : AliveDocs (g.filterAll (reqOf φ d)) := aliveDocs_filterAll hg.docs _
  have hfb : Below (g.filterAll (reqOf φ d)) := below_of_shrinks hs hg.below
  have havf : (g.filterAll (reqOf φ d)).isValid = true →
      (g.filterAll (reqOf φ d)).skipsWindow d (isProhibited φ) = true →
      AvoidSat (g.filterAll (reqOf φ d)) d (isProhibited φ) := by
    intro _ _ P V R hst ha hgood hne
    obtain ⟨S, hS, hag, hin⟩ := secIn_of_nodeIn hfin P V R hst ha hne
    exact ⟨S, hS, hag, hgood _ (hin _ (by omega) (by omega)) (hS.step _ (by omega) (by omega))⟩
  refine ⟨?_, sInv_upFiltering_of hg hk.2 hT hd havf hv⟩
  unfold upFiltering up at hv ⊢
  split
  · rename_i hvf
    let f := g.filterAll (reqOf φ d)
    have hfpos : 0 < f.current_step := by show 0 < (g.filterAll (reqOf φ d)).current_step; omega
    have hka : NodeIn (f.addNode d "" (isProhibited φ)) :=
      nodeIn_addNode hfin hfd hfb hf.2.2.2.1 hf.2.2.2.2.2.1 hfpos hdstep
    have hnd : NodupIds (f.addNode d "" (isProhibited φ)) := nodupIds_addNode hf.2.1 hfb hdstep
    have hda : AliveDocs (f.addNode d "" (isProhibited φ)) := aliveDocs_addNode hfd
    rw [review_eq_filterAll]
    exact nodeIn_filterAll hka hda hnd []
  · rename_i hvf
    rw [if_neg hvf] at hv
    exact absurd hv hvf

theorem joinProv_node {φ : Cnf} (H : HypsNode φ) {U : Int} (hU : 2 ≤ U) : JoinProv SInvN U := by
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
  exact ⟨nodeIn_doJoin hke.1 hkg.1 hsp, sInv_doJoin_of (secSplit_of_in (secSplitIn_of_node hsp)) hke.2 hkg.2⟩

theorem sInvN_initSeed : SInvN (initSeed (⟨0, 0⟩ : NodeId) "") := ⟨nodeIn_initSeed, sInv_initSeed⟩

/-- **El veredicto del lector es la satisfacibilidad bajo `NodeSplitIn` en los joins.** -/
theorem readerVerdict_iff_of_nodeIn {φ : Cnf} (hbd : Bounded φ) (H : HypsNode φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (fun kv hkv =>
    let h := run_prov (upProv_node φ) (fun _ hU => joinProv_node H hU) sInvN_initSeed kv hkv
    ⟨h.1, h.2.2⟩)

/-- **Nodo a nodo**: `NodeColour` y `SideEdgesAt` en cada join. -/
structure HypsNodeColour (φ : Cnf) : Prop where
  colour : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvN e → SInvN g →
             NodeColour (join e g) (T - 2)
  side   : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvN e → SInvN g →
             SideEdgesAt e g (T - 2)

theorem hypsNode_of_colour {φ : Cnf} (H : HypsNodeColour φ) : HypsNode φ := by
  refine ⟨fun T key e g a s hT he hg hke hkg hka hks hne hoe hog => ?_⟩
  have hoa : OffSide g a := fun q hq hqa => hne (hqa ▸ (hog q hq (by rw [hqa]; exact hka.1)))
  have hos : OffSide e s := fun q hq hqs => hne ((hoe q hq (by rw [hqs]; exact hks.1)).symm.trans hqs)
  have ho : OriginIn (join e g) (T - 2) (fun c => c = a ∨ c = s) := by
    intro q hq hk
    rcases (alive_join e g q).mp hq with h | h
    · exact Or.inl (hoe q h hk)
    · exact Or.inr (hog q h hk)
  exact nodeSplitIn_of_colour (by omega) (by rw [he.step]; omega) (he.step.trans hg.step.symm)
    hke.2.2.2.2.2.2.2 hkg.2.2.2.2.2.2.2 hke.2.2.2.1 hkg.2.2.2.1 hka.1 hks.1 hoa hos ho
    (H.colour T key e g hT he hg hke hkg) (H.side T key e g hT he hg hke hkg)

/-- **El veredicto del lector bajo `NodeColour` y `SideEdgesAt`.** -/
theorem readerVerdict_iff_of_nodeColour {φ : Cnf} (hbd : Bounded φ) (H : HypsNodeColour φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_nodeIn hbd (hypsNode_of_colour H)

end SecLine

end AbsSatBingo.Model
