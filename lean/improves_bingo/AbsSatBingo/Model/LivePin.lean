-- lean/improves_bingo/AbsSatBingo/Model/LivePin.lean
import AbsSatBingo.Model.LiveCommute

/-!
# `PinStable` con revisión forzada: el UP sin hipótesis de cierre

`liveExt_arrival_pinned` (`LiveCommute`) pedía que los dos estados de la conmutación fueran cerrados. Aquí los pins
se hacen con **revisión forzada** (`pinF`: fijar y revisar siempre, como el arranque del lector `reviewAll`), y el
cierre sale de `closedState_review`. Los invariantes de contabilidad van juntos en `SInvB` y pasan por todas las
operaciones.

* **`pinF g R`**: `review { R.foldl filterRequire g with dirty := true }`; `pinF g [] = reviewAll g`.
* **`PinStableF g`**: tras cualquier `pinF`, `LiveExt` para alguna relación de tríos.
* **`pinStableF_arrival`**: si el remitente es `PinStableF`, la llegada `up (filterAll g reqs) d` lo es, sin
  restricción sobre los pins (los de la cima o fijan `d`, que no cambia nada, o dejan el estado inválido).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Machine (Below mapId_of_mem_shiftRowIds)

/-- **Fijar y revisar siempre.** -/
def pinF (g : GPathB) (R : List NodeId) : GPathB := review { R.foldl filterRequire g with dirty := true }

-- ============================================================
-- Los invariantes de contabilidad
-- ============================================================

/-- Los invariantes de contabilidad de un estado de la línea. -/
structure SInvB (g : GPathB) : Prop where
  links : LinksInv g
  nodup : NodupIds g
  below : Below g
  zero  : AboveZero g
  lstep : LinksStep g
  edges : EdgesAlive g
  root  : RootNone g

theorem rootNone_of_sub {h g : GPathB} (hs : Sub h g) (hr : RootNone g) : RootNone h :=
  fun x hx hx0 => hr x (hs.alive x hx) hx0

theorem SInvB.docs {g : GPathB} (h : SInvB g) : AliveDocs g := h.links.1

theorem sInvB_prims {g h : GPathB} (hg : SInvB g) (hs : Sub h g)
    (hP : ∀ {P : GPathB → Prop}, RevPrims P → P g → P h) : SInvB h :=
  ⟨hP revPrims_linksInv hg.links, hP revPrims_nodupIds hg.nodup, hP revPrims_below hg.below,
   hP revPrims_aboveZero hg.zero, hP revPrims_linksStep hg.lstep, hP revPrims_edgesAlive hg.edges,
   rootNone_of_sub hs hg.root⟩

theorem sInvB_review {g : GPathB} (hg : SInvB g) : SInvB g.review :=
  sInvB_prims hg (shrinks_review g).1 (fun hp h => revPrims_review hp g h)

theorem sInvB_dirty {g : GPathB} (hg : SInvB g) (b : Bool) : SInvB { g with dirty := b } :=
  sInvB_prims hg (shrinks_dirty g b).1 (fun hp h => hp.dirty g b h)

theorem sInvB_foldl {g : GPathB} (hg : SInvB g) (R : List NodeId) : SInvB (R.foldl filterRequire g) :=
  sInvB_prims hg (shrinks_foldl _ shrinks_filterRequire R g).1
    (fun hp h => inv_foldl _ filterRequire R (fun g' r _ hc => Final.revPrims_filterRequire hp g' r hc) g h)

theorem sInvB_pinF {g : GPathB} (hg : SInvB g) (R : List NodeId) : SInvB (pinF g R) :=
  sInvB_review (sInvB_dirty (sInvB_foldl hg R) true)

theorem sInvB_filterAll {g : GPathB} (hg : SInvB g) (R : List NodeId) : SInvB (g.filterAll R) :=
  sInvB_review (sInvB_foldl hg R)

theorem sub_pinF (g : GPathB) (R : List NodeId) : Sub (pinF g R) g :=
  (shrinks_review _).1.trans ((shrinks_dirty _ true).1.trans (shrinks_foldl _ shrinks_filterRequire R g).1)

theorem step_pinF (g : GPathB) (R : List NodeId) : (pinF g R).current_step = g.current_step := (sub_pinF g R).step

variable {d : NodeId} {title : String} {forb : PathNodeId → Bool}

theorem sInvB_addNode {g : GPathB} (hg : SInvB g) (hd : d.step = g.current_step) (hd0 : 0 ≤ d.step) :
    SInvB (g.addNode d title forb) :=
  ⟨linksInv_addNode hg.links hg.below hg.zero hd, nodupIds_addNode hg.nodup hg.below hd,
   Machine.below_addNode hg.below hd, aboveZero_addNode hg.zero hd0, linksStep_addNode hg.lstep hd,
   edgesAlive_addNode hg.edges, rootNone_addNode hg.root hd⟩

-- ============================================================
-- Los pins forzados: fijan, conservan estructuras y cierran
-- ============================================================

/-- Tras los filtros (válidos), en el paso de cada requisito solo quedan vivos de él. -/
theorem pinned_foldl {b : NodeId} : ∀ (l : List NodeId) (g : GPathB), AliveDocs g →
    (l.foldl filterRequire g).isValid = true →
    ∀ q ∈ (l.foldl filterRequire g).alive, (b ∈ l → q.id.step = b.step → q.id = b) := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ hb; cases hb
  | cons r rs ih =>
    intro g' hd' hvl q hq hb hqs
    simp only [List.foldl_cons] at hq hvl
    rcases List.mem_cons.mp hb with heq | hb'
    · subst heq
      have hsub' := (shrinks_foldl filterRequire shrinks_filterRequire rs (g'.filterRequire b)).1
      have hv1 : (g'.filterRequire b).isValid = true := isValid_of_sub hsub' hvl
      have hv0 : g'.isValid = true := isValid_of_sub (shrinks_filterRequire g' b).1 hv1
      exact pinned_filterRequire hd' hv0 b q (hsub'.alive q hq) hqs
    · exact ih _ (aliveDocs_filterRequire hd' r) hvl q hq hb' hqs

theorem pinned_pinF {g : GPathB} (hd : AliveDocs g) {R : List NodeId} (hv : (pinF g R).isValid = true) :
    ∀ b ∈ R, ∀ q ∈ (pinF g R).alive, q.id.step = b.step → q.id = b := by
  have hs1 : Sub (pinF g R) (R.foldl filterRequire g) := (shrinks_review _).1.trans (shrinks_dirty _ true).1
  have hv1 : (R.foldl filterRequire g).isValid = true := isValid_of_sub hs1 hv
  intro b hb q hq hqs
  exact pinned_foldl R g hd hv1 q (hs1.alive q hq) hb hqs

variable {V : PathNodeId → Prop} {Rl : PathNodeId → PathNodeId → Prop}

theorem secStruct_dirty {g : GPathB} (h : SecStruct g V Rl) (b : Bool) : SecStruct { g with dirty := b } V Rl :=
  ⟨h.alive, h.refl, h.symm, h.dom, h.adj, h.pair, h.node, h.par, h.son⟩

theorem secStruct_pinF {g : GPathB} (h : SecStruct g V Rl) (R : List NodeId) (ha : ∀ b ∈ R, SecAgrees V b) :
    SecStruct (pinF g R) V Rl := by
  unfold pinF
  apply secStruct_review
  exact secStruct_dirty (inv_foldl (fun g' => SecStruct g' V Rl) filterRequire R
    (fun g' b hb hc => sec_filterRequire hc (ha b hb)) g h) true

theorem closedState_pinF {g : GPathB} (hg : SInvB g) {R : List NodeId} (hv : (pinF g R).isValid = true)
    (hcs : 2 ≤ g.current_step) : ClosedState (pinF g R) := by
  have hf := sInvB_dirty (sInvB_foldl hg R) true
  exact closedState_review rfl hv hf.docs hf.nodup hf.below hf.zero
    (by rw [(shrinks_foldl _ shrinks_filterRequire R g).1.step]; exact hcs)

-- ============================================================
-- PinStableF y el UP
-- ============================================================

/-- **`PinStableF g`**: tras cualquier pin forzado válido, `LiveExt` para alguna relación de tríos sin degenerar y
por debajo del paso. -/
def PinStableF (g : GPathB) : Prop :=
  ∀ R : List NodeId, (pinF g R).isValid = true →
    ∃ F, LiveExt (pinF g R) F ∧ FBelow F (pinF g R).current_step ∧ NoDeg F

theorem exists_alive_at {g : GPathB} (hv : g.isValid = true) {k : Int} (h0 : 0 ≤ k) (h1 : k < g.current_step) :
    ∃ q ∈ g.alive, q.id.step = k := by
  unfold isValid at hv
  have := List.all_eq_true.mp hv k (mem_intRange h0 (by omega))
  obtain ⟨q, hq, hqk⟩ := List.any_eq_true.mp this
  exact ⟨q, hq, by simpa using hqk⟩

theorem valid_of_up {Z : GPathB} (hv : (Z.up d title forb).isValid = true) : Z.isValid = true := by
  unfold up at hv
  split at hv
  · assumption
  · exact hv

theorem liveExt_dirty {g : GPathB} {F : Trios} (hli : LinksInv g) (hext : LiveExt g F) (b : Bool) :
    LiveExt { g with dirty := b } F :=
  liveExt_congr (A := { g with dirty := b }) (B := g) rfl (fun _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    (revPrims_linksInv.dirty g b hli) hli hext

/-- **La llegada fijada es el UP del remitente con el filtro ampliado** (en vivos y aristas), sin hipótesis de
cierre: la pieza de `pinStableF_arrival`, aparte. -/
theorem arrival_pin_commute {g : GPathB} {reqs R : List NodeId} (hg : SInvB g)
    (hpos : 0 < g.current_step) (hd : d.step = g.current_step)
    (hvA : (pinF ((g.filterAll reqs).up d title forb) R).isValid = true) :
    (pinF g (reqs ++ R)).isValid = true ∧
    (∀ q, q ∈ (pinF ((g.filterAll reqs).up d title forb) R).alive ↔
      q ∈ (({ (pinF g (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review.alive) ∧
    (∀ y w, y ∈ (pinF ((g.filterAll reqs).up d title forb) R).alive →
      w ∈ (pinF ((g.filterAll reqs).up d title forb) R).alive →
      ((pinF ((g.filterAll reqs).up d title forb) R).Adj y w ↔
        (({ (pinF g (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review.Adj y w)) := by
  -- los estados
  have hcsY : (g.filterAll reqs).current_step = g.current_step := (shrinks_filterAll g reqs).1.step
  have hvA0 : ((g.filterAll reqs).up d title forb).isValid = true := isValid_of_sub (sub_pinF _ R) hvA
  have hvY : (g.filterAll reqs).isValid = true := valid_of_up hvA0
  have hdY : d.step = (g.filterAll reqs).current_step := by rw [hcsY]; exact hd
  have hiY := sInvB_filterAll hg reqs
  have hiYa : SInvB ((g.filterAll reqs).addNode d title forb) := sInvB_addNode hiY hdY (by omega)
  have hA0eq : (g.filterAll reqs).up d title forb = ((g.filterAll reqs).addNode d title forb).review := by
    unfold up; rw [if_pos hvY]
  have hiA0 : SInvB ((g.filterAll reqs).up d title forb) := by rw [hA0eq]; exact sInvB_review hiYa
  have hcsA0 : ((g.filterAll reqs).up d title forb).current_step = g.current_step + 1 := by
    rw [step_up hvY, hcsY]
  have hsubA : Sub (pinF ((g.filterAll reqs).up d title forb) R) ((g.filterAll reqs).addNode d title forb) :=
    (sub_pinF _ R).trans (sub_up_addNode hvY)
  have hcA := closedState_pinF hiA0 hvA (by rw [hcsA0]; omega)
  -- A' → X: bajar y filtrar
  have hU1 := secStruct_of_sub hsubA hiYa.nodup hcA
  have hdown1 := secStruct_addNode_down hiY.docs hiY.below hiY.lstep hdY hU1
  have hg1 := secStruct_of_sub (shrinks_filterAll g reqs).1 hg.nodup hdown1
  have hX1 := secStruct_pinF hg1 (reqs ++ R) (fun b hb q ⟨hq, hqs⟩ hqb => by
    rcases List.mem_append.mp hb with hb | hb
    · rcases alive_addNode_cases hiY.docs hiY.below hdY (hsubA.alive q hq) with ⟨hqY, _⟩ | ⟨_, h⟩
      · exact pinned_filterAll_list hg.docs reqs hvY b hb q hqY hqb
      · omega
    · exact pinned_pinF hiA0.docs hvA b hb q hq hqb)
  -- X es válido: la parte vieja de A' no es vacía
  obtain ⟨q0, hq0, hq0s⟩ := exists_alive_at hvA (k := 0) (by omega) (by rw [step_pinF, hcsA0]; omega)
  have hvX : (pinF g (reqs ++ R)).isValid = true :=
    isValid_of_sec hX1 (y := q0) ⟨hq0, by rw [hq0s, hcsY]; exact hpos⟩
  have hcsX : (pinF g (reqs ++ R)).current_step = g.current_step := step_pinF g _
  have hdX : d.step = (pinF g (reqs ++ R)).current_step := by rw [hcsX]; exact hd
  have hiX := sInvB_pinF hg (reqs ++ R)
  have hiXa : SInvB ((pinF g (reqs ++ R)).addNode d title forb) := sInvB_addNode hiX hdX (by omega)
  have hiXd := sInvB_dirty hiXa true
  have hiB := sInvB_review hiXd
  -- A' → B: subir por la fila sobre X
  have hlift1 := secStruct_addNode_lift (X := pinF g (reqs ++ R)) (Y := g.filterAll reqs) (title := title)
    (forb := forb) (by rw [hcsX, hcsY]) (by rw [hcsY]; exact hpos) hdX hdY hiX.docs hiX.below hiX.links
    hiY.docs hiY.below hiY.edges hiY.lstep hiY.links.2.2 hU1 hX1
  have hB1 := secStruct_review (secStruct_dirty hlift1 true)
  have hvB : ((({ (pinF g (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review).isValid = true :=
    isValid_of_sec hB1 (y := q0) (hcA.alive hq0)
  have hcB := closedState_review rfl hvB hiXd.docs hiXd.nodup hiXd.below hiXd.zero
    (by show 2 ≤ (pinF g (reqs ++ R)).current_step + 1; rw [hcsX]; omega)
  -- B → A': bajar a X, al remitente, filtrar por reqs y subir por la fila sobre Y
  have hsubB : Sub (({ (pinF g (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review
      ((pinF g (reqs ++ R)).addNode d title forb) := (shrinks_review _).1.trans (shrinks_dirty _ true).1
  have hU2 := secStruct_of_sub hsubB hiXa.nodup hcB
  have hdown2 := secStruct_addNode_down hiX.docs hiX.below hiX.lstep hdX hU2
  have hg2 := secStruct_of_sub (sub_pinF g _) hg.nodup hdown2
  have hY2 := secStruct_filterAll_list hg2 reqs (fun b hb q ⟨hq, hqs⟩ hqb => by
    rcases alive_addNode_cases hiX.docs hiX.below hdX (hsubB.alive q hq) with ⟨hqX, _⟩ | ⟨_, h⟩
    · exact pinned_pinF hg.docs hvX b (List.mem_append_left _ hb) q hqX hqb
    · omega)
  have hlift2 := secStruct_addNode_lift (X := g.filterAll reqs) (Y := pinF g (reqs ++ R)) (title := title)
    (forb := forb) (by rw [hcsX, hcsY]) (by rw [hcsX]; exact hpos) hdY hdX hiY.docs hiY.below hiY.links
    hiX.docs hiX.below hiX.edges hiX.lstep hiX.links.2.2 hU2 hY2
  have hA02 := secStruct_review hlift2
  rw [← hA0eq] at hA02
  have hA2 := secStruct_pinF hA02 R (fun b hb q hq hqb => by
    rcases alive_addNode_cases hiX.docs hiX.below hdX (hsubB.alive q hq) with ⟨hqX, _⟩ | ⟨hqn, hqT⟩
    · exact pinned_pinF hg.docs hvX b (List.mem_append_right _ hb) q hqX hqb
    · -- en la cima: el pin tiene que ser `d`, o A' no tendría vivos en la cima
      obtain ⟨q1, hq1, hq1s⟩ := exists_alive_at hvA (k := g.current_step)
        (by omega) (by rw [step_pinF, hcsA0]; omega)
      have hb1 := pinned_pinF hiA0.docs hvA b hb q1 hq1 (by rw [hq1s, ← hqb, hqT, hcsX])
      rcases alive_addNode_cases hiY.docs hiY.below hdY (hsubA.alive q1 hq1) with ⟨_, h⟩ | ⟨hq1n, _⟩
      · rw [hcsY] at h; omega
      · rw [newRow_id hqn, ← hb1, newRow_id hq1n])
  -- mismos vivos y aristas
  have halive : ∀ q, q ∈ (pinF ((g.filterAll reqs).up d title forb) R).alive ↔
      q ∈ (({ (pinF g (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review.alive :=
    fun q => ⟨fun h => hB1.alive h, fun h => hA2.alive h⟩
  have hadj : ∀ y w, y ∈ (pinF ((g.filterAll reqs).up d title forb) R).alive →
      w ∈ (pinF ((g.filterAll reqs).up d title forb) R).alive →
      ((pinF ((g.filterAll reqs).up d title forb) R).Adj y w ↔
        (({ (pinF g (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review.Adj y w) :=
    fun y w hy hw => ⟨fun h => hB1.adj ⟨hy, hw, h⟩, fun h => hA2.adj ⟨hB1.alive hy, hB1.alive hw, h⟩⟩
  exact ⟨hvX, halive, hadj⟩

/-- **El UP conserva `PinStableF`**, sin hipótesis de cierre ni de pins: de los invariantes de contabilidad del
remitente y de `PinStableF`. Para un pin `R` de la llegada `A₀ = up (filterAll g reqs) d`:
`A' = pinF A₀ R` y `B = review {addNode (pinF g (reqs ++ R)) d, dirty}` tienen las mismas estructuras cerradas
(se bajan al remitente y se suben por la otra fila), los dos son cerrados (revisión forzada), luego los mismos vivos y
aristas; `B` cumple `LiveExt` por `PinStableF g` y la fila nueva con su revisión. -/
theorem pinStableF_arrival {g : GPathB} {reqs : List NodeId} (hg : SInvB g) (hps : PinStableF g)
    (hpos : 0 < g.current_step) (hd : d.step = g.current_step) :
    PinStableF ((g.filterAll reqs).up d title forb) := by
  intro R hvA
  -- los estados
  have hcsY : (g.filterAll reqs).current_step = g.current_step := (shrinks_filterAll g reqs).1.step
  have hvA0 : ((g.filterAll reqs).up d title forb).isValid = true := isValid_of_sub (sub_pinF _ R) hvA
  have hvY : (g.filterAll reqs).isValid = true := valid_of_up hvA0
  have hdY : d.step = (g.filterAll reqs).current_step := by rw [hcsY]; exact hd
  have hiY := sInvB_filterAll hg reqs
  have hiYa : SInvB ((g.filterAll reqs).addNode d title forb) := sInvB_addNode hiY hdY (by omega)
  have hA0eq : (g.filterAll reqs).up d title forb = ((g.filterAll reqs).addNode d title forb).review := by
    unfold up; rw [if_pos hvY]
  have hiA0 : SInvB ((g.filterAll reqs).up d title forb) := by rw [hA0eq]; exact sInvB_review hiYa
  have hcsA0 : ((g.filterAll reqs).up d title forb).current_step = g.current_step + 1 := by
    rw [step_up hvY, hcsY]
  have hsubA : Sub (pinF ((g.filterAll reqs).up d title forb) R) ((g.filterAll reqs).addNode d title forb) :=
    (sub_pinF _ R).trans (sub_up_addNode hvY)
  have hcA := closedState_pinF hiA0 hvA (by rw [hcsA0]; omega)
  -- A' → X: bajar y filtrar
  have hU1 := secStruct_of_sub hsubA hiYa.nodup hcA
  have hdown1 := secStruct_addNode_down hiY.docs hiY.below hiY.lstep hdY hU1
  have hg1 := secStruct_of_sub (shrinks_filterAll g reqs).1 hg.nodup hdown1
  have hX1 := secStruct_pinF hg1 (reqs ++ R) (fun b hb q ⟨hq, hqs⟩ hqb => by
    rcases List.mem_append.mp hb with hb | hb
    · rcases alive_addNode_cases hiY.docs hiY.below hdY (hsubA.alive q hq) with ⟨hqY, _⟩ | ⟨_, h⟩
      · exact pinned_filterAll_list hg.docs reqs hvY b hb q hqY hqb
      · omega
    · exact pinned_pinF hiA0.docs hvA b hb q hq hqb)
  -- X es válido: la parte vieja de A' no es vacía
  obtain ⟨q0, hq0, hq0s⟩ := exists_alive_at hvA (k := 0) (by omega) (by rw [step_pinF, hcsA0]; omega)
  have hvX : (pinF g (reqs ++ R)).isValid = true :=
    isValid_of_sec hX1 (y := q0) ⟨hq0, by rw [hq0s, hcsY]; exact hpos⟩
  have hcsX : (pinF g (reqs ++ R)).current_step = g.current_step := step_pinF g _
  have hdX : d.step = (pinF g (reqs ++ R)).current_step := by rw [hcsX]; exact hd
  have hiX := sInvB_pinF hg (reqs ++ R)
  have hiXa : SInvB ((pinF g (reqs ++ R)).addNode d title forb) := sInvB_addNode hiX hdX (by omega)
  have hiXd := sInvB_dirty hiXa true
  have hiB := sInvB_review hiXd
  -- A' → B: subir por la fila sobre X
  have hlift1 := secStruct_addNode_lift (X := pinF g (reqs ++ R)) (Y := g.filterAll reqs) (title := title)
    (forb := forb) (by rw [hcsX, hcsY]) (by rw [hcsY]; exact hpos) hdX hdY hiX.docs hiX.below hiX.links
    hiY.docs hiY.below hiY.edges hiY.lstep hiY.links.2.2 hU1 hX1
  have hB1 := secStruct_review (secStruct_dirty hlift1 true)
  have hvB : ((({ (pinF g (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review).isValid = true :=
    isValid_of_sec hB1 (y := q0) (hcA.alive hq0)
  have hcB := closedState_review rfl hvB hiXd.docs hiXd.nodup hiXd.below hiXd.zero
    (by show 2 ≤ (pinF g (reqs ++ R)).current_step + 1; rw [hcsX]; omega)
  -- B → A': bajar a X, al remitente, filtrar por reqs y subir por la fila sobre Y
  have hsubB : Sub (({ (pinF g (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review
      ((pinF g (reqs ++ R)).addNode d title forb) := (shrinks_review _).1.trans (shrinks_dirty _ true).1
  have hU2 := secStruct_of_sub hsubB hiXa.nodup hcB
  have hdown2 := secStruct_addNode_down hiX.docs hiX.below hiX.lstep hdX hU2
  have hg2 := secStruct_of_sub (sub_pinF g _) hg.nodup hdown2
  have hY2 := secStruct_filterAll_list hg2 reqs (fun b hb q ⟨hq, hqs⟩ hqb => by
    rcases alive_addNode_cases hiX.docs hiX.below hdX (hsubB.alive q hq) with ⟨hqX, _⟩ | ⟨_, h⟩
    · exact pinned_pinF hg.docs hvX b (List.mem_append_left _ hb) q hqX hqb
    · omega)
  have hlift2 := secStruct_addNode_lift (X := g.filterAll reqs) (Y := pinF g (reqs ++ R)) (title := title)
    (forb := forb) (by rw [hcsX, hcsY]) (by rw [hcsX]; exact hpos) hdY hdX hiY.docs hiY.below hiY.links
    hiX.docs hiX.below hiX.edges hiX.lstep hiX.links.2.2 hU2 hY2
  have hA02 := secStruct_review hlift2
  rw [← hA0eq] at hA02
  have hA2 := secStruct_pinF hA02 R (fun b hb q hq hqb => by
    rcases alive_addNode_cases hiX.docs hiX.below hdX (hsubB.alive q hq) with ⟨hqX, _⟩ | ⟨hqn, hqT⟩
    · exact pinned_pinF hg.docs hvX b (List.mem_append_right _ hb) q hqX hqb
    · -- en la cima: el pin tiene que ser `d`, o A' no tendría vivos en la cima
      obtain ⟨q1, hq1, hq1s⟩ := exists_alive_at hvA (k := g.current_step)
        (by omega) (by rw [step_pinF, hcsA0]; omega)
      have hb1 := pinned_pinF hiA0.docs hvA b hb q1 hq1 (by rw [hq1s, ← hqb, hqT, hcsX])
      rcases alive_addNode_cases hiY.docs hiY.below hdY (hsubA.alive q1 hq1) with ⟨_, h⟩ | ⟨hq1n, _⟩
      · rw [hcsY] at h; omega
      · rw [newRow_id hqn, ← hb1, newRow_id hq1n])
  -- mismos vivos y aristas
  have halive : ∀ q, q ∈ (pinF ((g.filterAll reqs).up d title forb) R).alive ↔
      q ∈ (({ (pinF g (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review.alive :=
    fun q => ⟨fun h => hB1.alive h, fun h => hA2.alive h⟩
  have hadj : ∀ y w, y ∈ (pinF ((g.filterAll reqs).up d title forb) R).alive →
      w ∈ (pinF ((g.filterAll reqs).up d title forb) R).alive →
      ((pinF ((g.filterAll reqs).up d title forb) R).Adj y w ↔
        (({ (pinF g (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review.Adj y w) :=
    fun y w hy hw => ⟨fun h => hB1.adj ⟨hy, hw, h⟩, fun h => hA2.adj ⟨hB1.alive hy, hB1.alive hw, h⟩⟩
  -- LiveExt en B
  obtain ⟨F, hext, hFB, hnF⟩ := hps (reqs ++ R) hvX
  have hda : DocsAlive (pinF g (reqs ++ R)) := docsAlive_review hvX (Or.inr rfl)
  have hextA := liveExt_addNode (title := title) (forb := forb) hext hiX.docs hiX.below hda hdX hFB hnF
  have hextB := liveExt_review (liveExt_dirty hiXa.links hextA true) hiXd.docs hiXd.links hiXd.root hiXd.nodup
    (noDeg_upF hnF)
  refine ⟨upF (pinF g (reqs ++ R)) F d, liveExt_congr ?_ halive hadj (sInvB_pinF hiA0 R).links hiB.links hextB,
    ?_, noDeg_upF hnF⟩
  · rw [step_pinF, hcsA0]
    show g.current_step + 1 = ((({ (pinF g (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review).current_step
    rw [(shrinks_review _).1.step]
    show g.current_step + 1 = (pinF g (reqs ++ R)).current_step + 1
    rw [hcsX]
  · have := fBelow_upF (d := d) hFB
    rw [step_pinF, hcsA0]; rw [hcsX] at this; exact this

end GPathB

end AbsSatBingo.Model
