-- lean/improves_bingo/AbsSatBingo/Model/SecStruct.lean
import AbsSatBingo.Model.Keeps
import AbsSatBingo.Model.SecPair

/-!
# `SecStruct`: una estructura cerrada por las reglas sobrevive al review

La generalización de `Carried` (una camarilla, un nodo por paso) a una **sección**: un conjunto de nodos `V` y una
relación `R` entre ellos. `SecStruct g V R` pide los cierres que el review necesita para no tocarla:

* **parejas**: cada pareja de `R` tiene, en cada paso, una entrada común relacionada con las dos (así la regla de
  parejas no la corta, y los nodos de `V` tienen vecino en cada paso);
* **enlaces**: cada nodo de `V` que no es raíz tiene un padre enlazado relacionado con él, y cada uno que no es cima
  un hijo (así la purga no lo elimina y los enlaces no caducan);
* **apoyo**: para cada pareja `(x, w)` de `R` con `x ≠ w`, algún padre de `x` relacionado con `x` lo está con `w`
  (si `x` está en un paso `≥ 1`), y lo mismo con los hijos (si `x` no está en la cima). Así las pasadas de padres e
  hijos no la cortan.

**`secStruct_review`**: el review conserva `SecStruct`. **`secStruct_filterAll`**: también el filtro por un nodo del
mapa con el que `V` concuerda en su paso. Con eso, **`secInPin_of_secStructAt`**: si toda sección de `b` se extiende
a una `SecStruct` que concuerda con `b` (`SecStructAt`), vale `SecInPin` (la mitad difícil de `PinEqSec`).

Medido en Julia (`julia/improves_bingo/test_3sat/probe_secinpin.jl`): las secciones de los estados del lector tienen
los cierres de enlaces y de apoyo con 0 fallos. Queda abierto `SecStructAt` en los estados del lector.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

variable {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- **Una estructura cerrada por las reglas del review.** -/
structure SecStruct (g : GPathB) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop) : Prop where
  alive : ∀ {y}, V y → y ∈ g.alive
  refl  : ∀ {y}, V y → R y y
  symm  : ∀ {y w}, R y w → R w y
  dom   : ∀ {y w}, R y w → V y ∧ V w
  adj   : ∀ {y w}, R y w → g.Adj y w
  pair  : ∀ {y w}, R y w → ∀ l, 0 ≤ l → l < g.current_step → ∃ r, r.id.step = l ∧ R y r ∧ R w r
  node  : ∀ {y}, V y → ∃ n, g.node? y = some n ∧
            (y.parent_id.isNone = false → ∃ p ∈ n.parents, R y p) ∧
            (y.id.step ≠ g.current_step - 1 → ∃ s ∈ n.sons, R y s)
  par   : ∀ {x w n}, R x w → x ≠ w → g.node? x = some n → 1 ≤ x.id.step → ∃ p ∈ n.parents, R x p ∧ R p w
  son   : ∀ {x w n}, R x w → x ≠ w → g.node? x = some n → x.id.step + 1 < g.current_step →
            ∃ s ∈ n.sons, R x s ∧ R s w

-- ============================================================
-- Los nodos de la estructura son válidos
-- ============================================================

theorem ownersOk_of_sec {g : GPathB} (h : SecStruct g V R) {y : PathNodeId} (hy : V y) : g.ownersOk y = true := by
  unfold ownersOk isAlive
  rw [Bool.and_eq_true]
  refine ⟨List.contains_iff_mem.mpr (h.alive hy), ?_⟩
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨h0, h1⟩ := intRange_bounds hl
  obtain ⟨r, hrl, hyr, _⟩ := h.pair (h.refl hy) l h0 (by omega)
  unfold hasNeighborAt
  exact List.any_eq_true.mpr ⟨r, h.alive (h.dom hyr).2, by
    rw [Bool.and_eq_true]; exact ⟨by simp [hrl], h.adj hyr⟩⟩

theorem isValidNode_of_sec {g : GPathB} (h : SecStruct g V R) {y : PathNodeId} (hy : V y) {n : PNodeB}
    (hn : g.node? y = some n) : g.isValidNode n = true := by
  have hid := node?_id hn
  obtain ⟨n', hn', hpar, hson⟩ := h.node hy
  rw [hn] at hn'
  cases hn'
  have hok : g.ownersOk n.id = true := by rw [hid]; exact ownersOk_of_sec h hy
  have hp : n.id.parent_id.isNone = false → n.parents.isEmpty = false := fun hr => by
    obtain ⟨p, hp, _⟩ := hpar (by rw [← hid]; exact hr)
    cases hps : n.parents with
    | nil => rw [hps] at hp; cases hp
    | cons _ _ => rfl
  have hs : n.id.id.step ≠ g.current_step - 1 → n.sons.isEmpty = false := fun hl => by
    obtain ⟨s, hs, _⟩ := hson (by rw [← hid]; exact hl)
    cases hss : n.sons with
    | nil => rw [hss] at hs; cases hs
    | cons _ _ => rfl
  unfold isValidNode
  simp only
  by_cases hroot : n.id.parent_id.isNone = true
  · rw [if_pos hroot]
    by_cases hlast : (n.id.id.step == g.current_step - 1) = true
    · rw [if_pos hlast]; exact hok
    · rw [if_neg hlast]
      have : n.id.id.step ≠ g.current_step - 1 := by simpa using hlast
      simp [hok, hs this]
  · rw [if_neg hroot]
    have hr : n.id.parent_id.isNone = false := Bool.eq_false_iff.mpr hroot
    by_cases hlast : (n.id.id.step == g.current_step - 1) = true
    · rw [if_pos hlast]; simp [hok, hp hr]
    · rw [if_neg hlast]
      have : n.id.id.step ≠ g.current_step - 1 := by simpa using hlast
      simp [hok, hp hr, hs this]

theorem not_V_of_invalid {g : GPathB} (h : SecStruct g V R) {id : PathNodeId} {n : PNodeB}
    (hn : g.node? id = some n) (hv : g.isValidNode n = false) : ¬ V id := by
  intro hid
  rw [isValidNode_of_sec h hid hn] at hv
  exact Bool.noConfusion hv

/-- Dos nodos relacionados cumplen la regla de parejas. -/
theorem pairOk_of_sec {g : GPathB} (h : SecStruct g V R) {x w : PathNodeId} (hr : R x w) : g.pairOk x w = true := by
  unfold pairOk
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨h0, h1⟩ := intRange_bounds hl
  obtain ⟨r, hrl, hxr, hwr⟩ := h.pair hr l h0 (by omega)
  unfold commonAt
  refine List.any_eq_true.mpr ⟨r, h.alive (h.dom hxr).2, ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨⟨by simp [hrl], h.adj hxr⟩, h.adj hwr⟩

-- ============================================================
-- Las primitivas
-- ============================================================

theorem sec_dirty {g : GPathB} (h : SecStruct g V R) (b : Bool) : SecStruct { g with dirty := b } V R :=
  ⟨h.alive, h.refl, h.symm, h.dom, h.adj, h.pair, h.node, h.par, h.son⟩

theorem sec_killVertex {g : GPathB} (h : SecStruct g V R) {id : PathNodeId} (hid : ¬ V id) :
    SecStruct (g.killVertex id) V R := by
  have hne : ∀ {y}, V y → y ≠ id := fun hy he => hid (he ▸ hy)
  exact ⟨fun hy => List.mem_filter.mpr ⟨h.alive hy, bne_iff_ne.mpr (hne hy)⟩, h.refl, h.symm, h.dom,
    fun hr => adj_killVertex_of (h.adj hr) (hne (h.dom hr).1) (hne (h.dom hr).2), h.pair, h.node, h.par, h.son⟩

theorem sec_removeNode {g : GPathB} (h : SecStruct g V R) {id : PathNodeId} (hid : ¬ V id) :
    SecStruct (g.removeNode id) V R := by
  have hk := sec_killVertex h hid
  have hne : ∀ {y}, V y → y ≠ id := fun hy he => hid (he ▸ hy)
  have hnode : ∀ {x m}, V x → (g.removeNode id).node? x = some m → ∃ n, g.node? x = some n ∧ m = unlinkAll id n := by
    intro x m hx hm
    rw [node?_removeNode (hne hx)] at hm
    cases hg : g.node? x with
    | none => rw [hg] at hm; cases hm
    | some n => rw [hg] at hm; cases hm; exact ⟨n, rfl, rfl⟩
  have hkeep : ∀ {p : PathNodeId} {l : List PathNodeId}, p ∈ l → V p → p ∈ l.filter (· != id) :=
    fun hp hv => List.mem_filter.mpr ⟨hp, bne_iff_ne.mpr (hne hv)⟩
  refine ⟨hk.alive, h.refl, h.symm, h.dom, hk.adj, h.pair, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn, hp, hs⟩ := h.node hy
    refine ⟨unlinkAll id n, by rw [node?_removeNode (hne hy), hn]; rfl, ?_, ?_⟩
    · intro hr
      obtain ⟨p, hpm, hyp⟩ := hp hr
      exact ⟨p, hkeep hpm (h.dom hyp).2, hyp⟩
    · intro hl
      obtain ⟨s, hsm, hys⟩ := hs hl
      exact ⟨s, hkeep hsm (h.dom hys).2, hys⟩
  · intro x w m hr hxw hm hx1
    obtain ⟨n, hn, rfl⟩ := hnode (h.dom hr).1 hm
    obtain ⟨p, hpm, hxp, hpw⟩ := h.par hr hxw hn hx1
    exact ⟨p, hkeep hpm (h.dom hxp).2, hxp, hpw⟩
  · intro x w m hr hxw hm hx1
    obtain ⟨n, hn, rfl⟩ := hnode (h.dom hr).1 hm
    obtain ⟨s, hsm, hxs, hsw⟩ := h.son hr hxw hn hx1
    exact ⟨s, hkeep hsm (h.dom hxs).2, hxs, hsw⟩

theorem sec_removeEdge {g : GPathB} (h : SecStruct g V R) {x w : PathNodeId} (hxw : ¬ R x w) :
    SecStruct (g.removeEdge x w) V R := by
  refine ⟨h.alive, h.refl, h.symm, h.dom, ?_, h.pair, h.node, h.par, h.son⟩
  intro a b hr
  apply adj_removeEdge_of (h.adj hr)
  · rintro ⟨rfl, rfl⟩; exact hxw hr
  · rintro ⟨rfl, rfl⟩; exact hxw (h.symm hr)

/-- Un `foldl` de pasos que conservan un invariante lo conserva. -/
theorem inv_foldl {α : Type} (P : GPathB → Prop) (f : GPathB → α → GPathB) (l : List α)
    (hf : ∀ g a, a ∈ l → P g → P (f g a)) : ∀ g, P g → P (l.foldl f g) := by
  induction l with
  | nil => intro g h; exact h
  | cons a as ih =>
    intro g h
    exact ih (fun g' a' ha' => hf g' a' (List.mem_cons_of_mem _ ha')) _ (hf g a (List.mem_cons_self ..) h)

-- ============================================================
-- Filtro, purga, parejas, enlaces
-- ============================================================

/-- `V` concuerda con el requisito `req`: en su paso, sus nodos son de `req`. -/
def SecAgrees (V : PathNodeId → Prop) (req : NodeId) : Prop := ∀ {y}, V y → y.id.step = req.step → y.id = req

theorem sec_filterRequire {g : GPathB} (h : SecStruct g V R) {req : NodeId} (ha : SecAgrees V req) :
    SecStruct (g.filterRequire req) V R := by
  unfold filterRequire
  split
  · apply sec_dirty
    refine inv_foldl (fun g' => SecStruct g' V R) killVertex _ ?_ g h
    intro g' q hq hc
    refine sec_killVertex hc ?_
    intro hvq
    obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
    obtain ⟨n, hn, hnid⟩ := List.mem_map.mp hq1
    have hstep := (List.mem_filter.mp hn).2
    rw [hnid] at hstep
    have := ha hvq (by simpa using hstep)
    simp [this] at hq2
  · exact h

theorem sec_purgeStep {g : GPathB} (h : SecStruct g V R) (id : PathNodeId) : SecStruct (g.purgeStep id) V R := by
  unfold purgeStep
  split
  · exact h
  · rename_i n hn
    split
    · exact h
    · rename_i hv
      exact sec_dirty (sec_removeNode h (not_V_of_invalid h hn (by simpa using hv))) _

theorem sec_purgeRound {g : GPathB} (h : SecStruct g V R) : SecStruct g.purgeRound V R :=
  inv_foldl (fun g' => SecStruct g' V R) purgeStep _ (fun _ a _ hc => sec_purgeStep hc a) g h

theorem sec_purgeFuel : ∀ (n : Nat) (g : GPathB), SecStruct g V R → SecStruct (purgeFuel n g) V R := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    simp only [purgeFuel]
    split
    · split
      · exact ih _ (sec_purgeRound h)
      · exact sec_purgeRound h
    · exact h

theorem sec_clean {g : GPathB} (h : SecStruct g V R) : SecStruct g.clean V R := sec_purgeFuel _ _ h

theorem sec_pairSweep {g : GPathB} (h : SecStruct g V R) : SecStruct g.pairSweep.1 V R := by
  unfold pairSweep
  dsimp only
  refine inv_foldl (fun g' => SecStruct g' V R) (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) _
    ?_ g h
  intro g' e he hc
  refine sec_removeEdge hc ?_
  intro hr
  have := (List.mem_filter.mp he).2
  rw [pairOk_of_sec h hr] at this
  exact Bool.noConfusion this

theorem sec_pairFuel : ∀ (n : Nat) (g : GPathB), SecStruct g V R → SecStruct (pairFuel n g) V R := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    simp only [pairFuel]
    split
    · split
      · exact ih _ (sec_clean (sec_dirty (sec_pairSweep h) _))
      · exact h
    · exact h

theorem sec_cleanPair {g : GPathB} (h : SecStruct g V R) : SecStruct g.cleanPair V R :=
  sec_pairFuel _ _ (sec_clean h)

theorem sec_pruneLinks {g : GPathB} (h : SecStruct g V R) : SecStruct g.pruneLinks V R := by
  unfold pruneLinks
  split
  · let f : PNodeB → PNodeB := fun n =>
      { n with parents := n.parents.filter (g.linkOk n.id), sons := n.sons.filter (g.linkOk n.id) }
    have hmap : ∀ x, (g.nodes.map f).find? (fun n => n.id == x) = (g.node? x).map f :=
      fun x => find?_map_id f (fun _ => rfl) x g.nodes
    have hlink : ∀ {y p}, V y → R y p → g.linkOk y p = true := by
      intro y p hy hyp
      obtain ⟨m, hm, _, _⟩ := h.node (h.dom hyp).2
      unfold linkOk
      rw [hm]
      simp only [Option.isSome_some, Bool.true_and]
      exact h.adj hyp
    have hback : ∀ {x m}, (g.node? x).map f = some m → ∃ n, g.node? x = some n ∧ m = f n := by
      intro x m hm
      cases hg : g.node? x with
      | none => rw [hg] at hm; cases hm
      | some n => rw [hg] at hm; cases hm; exact ⟨n, rfl, rfl⟩
    refine ⟨h.alive, h.refl, h.symm, h.dom, h.adj, h.pair, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨n, hn, hp, hs⟩ := h.node hy
      have hid := node?_id hn
      refine ⟨f n, by show List.find? _ (g.nodes.map f) = _; rw [hmap, hn]; rfl, ?_, ?_⟩
      · intro hr
        obtain ⟨p, hpm, hyp⟩ := hp hr
        exact ⟨p, List.mem_filter.mpr ⟨hpm, by rw [hid]; exact hlink hy hyp⟩, hyp⟩
      · intro hl
        obtain ⟨s, hsm, hys⟩ := hs hl
        exact ⟨s, List.mem_filter.mpr ⟨hsm, by rw [hid]; exact hlink hy hys⟩, hys⟩
    · intro x w m hr hxw hm hx1
      change List.find? _ (g.nodes.map f) = some m at hm
      rw [hmap] at hm
      obtain ⟨n, hn, rfl⟩ := hback hm
      have hid := node?_id hn
      obtain ⟨p, hpm, hxp, hpw⟩ := h.par hr hxw hn hx1
      exact ⟨p, List.mem_filter.mpr ⟨hpm, by rw [hid]; exact hlink (h.dom hr).1 hxp⟩, hxp, hpw⟩
    · intro x w m hr hxw hm hx1
      change List.find? _ (g.nodes.map f) = some m at hm
      rw [hmap] at hm
      obtain ⟨n, hn, rfl⟩ := hback hm
      have hid := node?_id hn
      obtain ⟨s, hsm, hxs, hsw⟩ := h.son hr hxw hn hx1
      exact ⟨s, List.mem_filter.mpr ⟨hsm, by rw [hid]; exact hlink (h.dom hr).1 hxs⟩, hxs, hsw⟩
  · exact h

-- ============================================================
-- Las pasadas
-- ============================================================

/-- El corte de un nodo cuyo selector apoya cada pareja suya de la estructura. -/
theorem sec_cutStep {g : GPathB} (h : SecStruct g V R) (sel : PNodeB → List PathNodeId) (n : PNodeB)
    (hsel : ∀ w, R n.id w → n.id ≠ w → ∃ p ∈ sel n, R p w) : SecStruct (cutStep sel g n) V R := by
  unfold cutStep cutSupport
  split
  · dsimp only
    have hfold := inv_foldl (fun g' => SecStruct g' V R) (fun h w => h.removeEdge n.id w)
      (g.alive.filter (fun w => w != n.id && g.adjb n.id w && !(sel n).any (fun p => g.adjb p w)))
      (fun _ w hw hc => by
        refine sec_removeEdge hc ?_
        intro hr
        have := (List.mem_filter.mp hw).2
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, bne_iff_ne, ne_eq] at this
        obtain ⟨⟨hne, _⟩, hno⟩ := this
        obtain ⟨p, hp, hpw⟩ := hsel w hr (Ne.symm hne)
        exact absurd (h.adj hpw) (by simpa [Adj] using hno p hp))
      g h
    split
    · exact sec_dirty hfold _
    · exact hfold
  · exact h

theorem sec_reviewNode {g : GPathB} (h : SecStruct g V R) (sel : PNodeB → List PathNodeId) (id : PathNodeId)
    (hsel : ∀ n, g.node? id = some n → ∀ w, R id w → id ≠ w → ∃ p ∈ sel n, R p w) :
    SecStruct (reviewNode sel g id) V R := by
  unfold reviewNode
  split
  · exact h
  · rename_i n hn
    have hid := node?_id hn
    have hc : SecStruct (cutStep sel g n) V R := sec_cutStep h sel n (by rw [hid]; exact hsel n hn)
    show SecStruct (if (cutStep sel g n).isValidNode n then cutStep sel g n
      else { (cutStep sel g n).removeNode id with dirty := true }) V R
    split
    · exact hc
    · rename_i hv
      have hn' : (cutStep sel g n).node? id = some n := by
        show List.find? _ (cutStep sel g n).nodes = _
        rw [nodes_cutStep]; exact hn
      exact sec_dirty (sec_removeNode hc (not_V_of_invalid hc hn' (by simpa using hv))) _

/-- La pasada del paso `k`, con el selector que la estructura apoya en ese paso. -/
theorem sec_reviewLine {g : GPathB} (h : SecStruct g V R) (sel : PNodeB → List PathNodeId) (k : Int)
    (hsel : ∀ g', SecStruct g' V R → g'.current_step = g.current_step → ∀ id n, id.id.step = k →
      g'.node? id = some n → ∀ w, R id w → id ≠ w → ∃ p ∈ sel n, R p w) :
    SecStruct (reviewLine sel g k) V R := by
  unfold reviewLine
  refine (inv_foldl (fun g' => SecStruct g' V R ∧ g'.current_step = g.current_step) (reviewNode sel) _ ?_ g
    ⟨h, rfl⟩).1
  intro g' id hid ⟨hc, hcs⟩
  refine ⟨sec_reviewNode hc sel id ?_, (step_of_shrinks (shrinks_reviewNode sel g' id)).trans hcs⟩
  intro n hn
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hid
  have hstep := (List.mem_filter.mp hm).2
  exact hsel g' hc hcs m.id n (by simpa using hstep) hn

theorem sec_reviewSteps (sel : PNodeB → List PathNodeId) (cs : Int) {ks : List Int}
    (hsel : ∀ k, ∀ g', SecStruct g' V R → g'.current_step = cs → ∀ id n, id.id.step = k →
      g'.node? id = some n → ∀ w, R id w → id ≠ w → k ∈ ks → ∃ p ∈ sel n, R p w) :
    ∀ (ks' : List Int) (g : GPathB), SecStruct g V R → g.current_step = cs → (∀ k ∈ ks', k ∈ ks) →
      SecStruct (reviewSteps sel g ks') V R := by
  intro ks'
  induction ks' with
  | nil => intro g h _ _; exact h
  | cons k ks' ih =>
    intro g h hcs hsub
    simp only [reviewSteps]
    have hk := hsub k (List.mem_cons_self ..)
    have h1 := sec_reviewLine h sel k (fun g' hc hcs' id n hid hn w hr hne =>
      hsel k g' hc (hcs'.trans hcs) id n hid hn w hr hne hk)
    have hcs1 : (reviewLine sel g k).current_step = cs :=
      (step_of_shrinks (shrinks_reviewLine _ g k)).trans hcs
    split
    · exact ih _ h1 hcs1 (fun k' hk' => hsub k' (List.mem_cons_of_mem _ hk'))
    · exact h1

theorem sec_reviewParents {g : GPathB} (h : SecStruct g V R) : SecStruct g.reviewParents V R := by
  unfold reviewParents
  split
  · refine sec_reviewSteps (ks := intRange 1 (g.current_step - 1)) _ g.current_step ?_ _ g h rfl (fun _ hk => hk)
    intro k g' hc _ id n hid hn w hr hne hk
    obtain ⟨p, hp, _, hpw⟩ := hc.par hr hne hn (by rw [hid]; exact (intRange_bounds hk).1)
    exact ⟨p, hp, hpw⟩
  · exact h

theorem sec_reviewSons {g : GPathB} (h : SecStruct g V R) : SecStruct g.reviewSons V R := by
  unfold reviewSons
  split
  · refine sec_reviewSteps (ks := (intRange 0 (g.current_step - 2)).reverse) _ g.current_step ?_ _ g h rfl
      (fun _ hk => hk)
    intro k g' hc hcs id n hid hn w hr hne hk
    have hk2 := (intRange_bounds (List.mem_reverse.mp hk)).2
    obtain ⟨s, hs, _, hsw⟩ := hc.son hr hne hn (by rw [hid, hcs]; omega)
    exact ⟨s, hs, hsw⟩
  · exact h

-- ============================================================
-- El review y el filtro
-- ============================================================

theorem sec_reviewPass {g : GPathB} (h : SecStruct g V R) : SecStruct g.reviewPass V R :=
  sec_pruneLinks (sec_reviewSons (sec_reviewParents (sec_pruneLinks (sec_cleanPair h))))

theorem sec_reviewFuel : ∀ (n : Nat) (g : GPathB), SecStruct g V R → SecStruct (reviewFuel n g) V R := by
  intro n
  induction n with
  | zero => intro g h; exact h
  | succ n ih =>
    intro g h
    simp only [reviewFuel]
    split
    · exact ih _ (sec_reviewPass (sec_dirty h _))
    · exact h

/-- **El review conserva toda estructura cerrada por las reglas.** -/
theorem secStruct_review {g : GPathB} (h : SecStruct g V R) : SecStruct g.review V R := sec_reviewFuel _ _ h

/-- **El pin de `b` la conserva si `V` concuerda con `b`.** -/
theorem secStruct_filterAll {g : GPathB} (h : SecStruct g V R) {b : NodeId} (ha : SecAgrees V b) :
    SecStruct (g.filterAll [b]) V R := by
  unfold filterAll
  exact secStruct_review (sec_filterRequire h ha)

-- ============================================================
-- SecInPin
-- ============================================================

/-- Una estructura no vacía deja el gpath válido. -/
theorem isValid_of_sec {g : GPathB} (h : SecStruct g V R) {y : PathNodeId} (hy : V y) : g.isValid = true := by
  unfold isValid
  rw [List.all_eq_true]
  intro k hk
  obtain ⟨h0, h1⟩ := intRange_bounds hk
  obtain ⟨r, hrl, hyr, _⟩ := h.pair (h.refl hy) k h0 (by omega)
  exact List.any_eq_true.mpr ⟨r, h.alive (h.dom hyr).2, by simp [hrl]⟩

/-- Toda pareja de una estructura que concuerda con `b` es una arista del pin de `b`. -/
theorem pinEdge_of_secStruct {g : GPathB} (h : SecStruct g V R) {b : NodeId} (ha : SecAgrees V b)
    {y w : PathNodeId} (hr : R y w) : PinEdge (g.filterAll [b]) y w := by
  have hp := secStruct_filterAll h ha
  exact ⟨isValid_of_sec hp (hp.dom hr).1, hp.alive (hp.dom hr).1, hp.alive (hp.dom hr).2, hp.adj hr⟩

/-- **Abierto**: toda sección de `b` está dentro de una estructura cerrada por las reglas que concuerda con `b`. -/
def SecStructAt (g : GPathB) (b : NodeId) : Prop :=
  ∀ R, SecClosed g b R → ∃ V R', SecStruct g V R' ∧ SecAgrees V b ∧ ∀ y w, R y w → R' y w

/-- **`SecStructAt` da `SecInPin`**: la mitad difícil de `PinEqSec` se reduce a los cierres de la sección. -/
theorem secInPin_of_secStructAt {g : GPathB} {b : NodeId} (h : SecStructAt g b) : SecInPin g b := by
  intro R hs y w _ hr
  obtain ⟨V, R', hst, ha, hsub⟩ := h R hs
  exact pinEdge_of_secStruct hst ha (hsub y w hr)

end GPathB

end AbsSatBingo.Model
