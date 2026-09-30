-- lean/improves_bingo/AbsSatBingo/Model/LiveUp.lean
import AbsSatBingo.Model.LiveExt

/-!
# `LiveExt` en el UP

El UP de la máquina es `review (addNode (filterAll g reqs) d)`. Aquí, dos de sus tres tramos:

* **La fila nueva** (`liveExt_addNode`): si el remitente cumple `LiveExt` con `F`, la fila nueva lo cumple con
  `upF g F d` (los tríos que hereda de sus padres, Julia `up_forbid!`). Una cadena viva que empieza en un nodo nuevo
  `t` sigue por su padre `p`, y debajo es una cadena viva del remitente; su alargamiento `q` es vecino de `t` a
  través de `p`, y el trío `(t, x, q)` no está prohibido porque `(p, x, q)` no lo está en el remitente.
* **Lo que conserva camarillas** (`liveExt_of_keep`): con `LiveExt`, toda cadena viva se completa hasta el paso 0
  (`liveChain_extend_full`), y una cadena completa es una camarilla (`carried_of_liveChain`). Una operación que
  conserva todas las camarillas y solo prohíbe tríos que ellas esquivan conserva `LiveExt`: **la revisión**
  (`liveExt_review`, por `carried_review`) y **la regla de los tríos** (`liveExt_forbidRound`).

Juntos: **`liveExt_up`**, el `up` (fila nueva + revisión) conserva `LiveExt` con `upF`, bajo invariantes de la
línea (documentos vivos, enlaces, ids únicos, raíces en el paso 0) y tríos sin degenerar.

**El filtro de requisitos** (`filterAll`) es un pin: no conserva todas las camarillas, solo las que concuerdan con
los requisitos. Lo que necesita es exactamente **`PinLive`**: toda cadena viva del estado filtrado se completa en el
remitente por una rama que concuerda con los requisitos (`liveExt_filterAll` y, al revés, `pinLive_of_liveExt`).
Con ella, **`liveExt_upFiltering`**: el UP entero conserva `LiveExt`. `PinLive` es la misma forma que el primer pin
del lector y que `PinKeeps`, pero relativa a una cadena viva; medida, 0 fallos (`probe_liveext.jl`, grupo `flt`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Machine (Below)

/-- Los nodos del paso 0 son raíces (en la máquina, la fila del paso 0 se crea sin padre). -/
def RootNone (g : GPathB) : Prop := ∀ x ∈ g.alive, x.id.step = 0 → x.parent_id = none

/-- Los tríos prohibidos son de tres nodos distintos (Julia solo prohíbe tríos de nodos de pasos distintos). -/
def NoDeg (F : Trios) : Prop := ∀ x y z, F x y z → x ≠ y ∧ x ≠ z ∧ y ≠ z

-- ============================================================
-- Cadenas vivas: lo básico
-- ============================================================

theorem liveChain_mono {g : GPathB} {F : Trios} {C : Int → PathNodeId} {j j' : Int} (h : LiveChain g F C j)
    (hj : j ≤ j') : LiveChain g F C j' :=
  ⟨⟨fun k h1 h2 => h.chain.node k (by omega) h2, fun k l h1 h2 h3 h4 => h.chain.adj k l (by omega) h2 (by omega) h4,
    fun k h1 h2 => h.chain.link k (by omega) h2⟩, fun a b c ha hab hbc hc => h.live a b c (by omega) hab hbc hc⟩

/-- **Con `LiveExt`, toda cadena viva se completa hasta el paso 0.** -/
theorem liveChain_extend_full {g : GPathB} {F : Trios} (hext : LiveExt g F) {C : Int → PathNodeId} {j : Int}
    (hC : LiveChain g F C j) (hj0 : 0 ≤ j) (hjt : j ≤ g.current_step - 1) :
    ∃ D, LiveChain g F D 0 ∧ ∀ k, j ≤ k → D k = C k := by
  have key : ∀ i : Nat, (i : Int) ≤ j → ∃ D, LiveChain g F D (j - i) ∧ ∀ k, j ≤ k → D k = C k := by
    intro i
    induction i with
    | zero => intro _; exact ⟨C, by simpa using hC, fun _ _ => rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨D, hD, hag⟩ := ih (by omega)
      obtain ⟨D', hD', hag'⟩ := hext D _ hD (by push_cast at hi; omega) (by omega)
      refine ⟨D', ?_, fun k hk => by rw [hag' k (by omega)]; exact hag k hk⟩
      have : j - ((i + 1 : Nat) : Int) = j - (i : Int) - 1 := by push_cast; omega
      rw [this]; exact hD'
  obtain ⟨D, hD, hag⟩ := key j.toNat (by omega)
  refine ⟨D, ?_, hag⟩
  have : j - (j.toNat : Int) = 0 := by omega
  rw [this] at hD; exact hD

/-- En una cadena viva, los tríos de tres pasos distintos no están prohibidos, en ningún orden. -/
theorem liveChain_not_F {g : GPathB} {F : Trios} {C : Int → PathNodeId} {j : Int} (h : LiveChain g F C j)
    {a b c : Int} (ha : j ≤ a) (hb : j ≤ b) (hc : j ≤ c) (ha' : a ≤ g.current_step - 1) (hb' : b ≤ g.current_step - 1)
    (hc' : c ≤ g.current_step - 1) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : ¬ F (C a) (C b) (C c) := by
  intro hf
  -- se ordenan los tres pasos
  rcases Int.lt_or_gt_of_ne hab with h1 | h1 <;> rcases Int.lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases Int.lt_or_gt_of_ne hbc with h3 | h3
  · exact h.live a b c ha h1 h3 hc' (by simp [Sym, hf])
  · exact h.live a c b ha h2 (by omega) hb' (by simp [Sym, hf])
  · omega
  · exact h.live c a b hc (by omega) h1 hb' (by simp [Sym, hf])
  · exact h.live b a c hb (by omega) h2 hc' (by simp [Sym, hf])
  · omega
  · exact h.live b c a hb h3 (by omega) ha' (by simp [Sym, hf])
  · exact h.live c b a hc (by omega) (by omega) ha' (by simp [Sym, hf])

/-- Una cadena viva completa esquiva `F` (con `F` sin tríos degenerados). -/
theorem avoids_of_liveChain {g : GPathB} {F : Trios} (hnd : NoDeg F) {D : Int → PathNodeId}
    (h : LiveChain g F D 0) : Avoids F g.current_step D := by
  intro a b c h0 h1 h2 h3 h4 h5 hf
  obtain ⟨n1, n2, n3⟩ := hnd _ _ _ hf
  refine liveChain_not_F h h0 h2 h4 (by omega) (by omega) (by omega) ?_ ?_ ?_ hf
  · intro e; subst e; exact n1 rfl
  · intro e; subst e; exact n2 rfl
  · intro e; subst e; exact n3 rfl

/-- Una rama llevada que esquiva `G` es una cadena viva desde cualquier paso `j ≥ 0`. -/
theorem liveChain_of_carried {h : GPathB} {G : Trios} {D : Int → PathNodeId} (hc : Carried h D)
    (hA : Avoids G h.current_step D) {j : Int} (hj : 0 ≤ j) : LiveChain h G D j := by
  refine ⟨⟨fun k h1 h2 => ⟨hc.step k (by omega) (by omega), hc.alive k (by omega) (by omega)⟩,
    fun k l h1 h2 h3 h4 => hc.adj k l (by omega) (by omega) (by omega) (by omega), fun k h1 h2 => ?_⟩, ?_⟩
  · obtain ⟨n, hn, hp, _⟩ := hc.node k (by omega) (by omega)
    exact ⟨n, hn, hp (by omega)⟩
  · intro a b c ha hab hbc hc' hs
    have r := fun x y z (hx : 0 ≤ x) (hx' : x < h.current_step) (hy : 0 ≤ y) (hy' : y < h.current_step)
      (hz : 0 ≤ z) (hz' : z < h.current_step) => hA x y z hx hx' hy hy' hz hz'
    unfold Sym at hs
    rcases hs with hs | hs | hs | hs | hs | hs
    · exact r a b c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hs
    · exact r a c b (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hs
    · exact r b a c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hs
    · exact r b c a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hs
    · exact r c a b (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hs
    · exact r c b a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hs

/-- **Una cadena viva completa es una camarilla** (sin pedir que el estado sea cerrado). -/
theorem carried_of_liveChain {g : GPathB} {F : Trios} (hdocs : AliveDocs g) (hli : LinksInv g) (hr : RootNone g)
    {D : Int → PathNodeId} (hD : LiveChain g F D 0) : Carried g D := by
  have hC := hD.chain
  refine ⟨fun k h0 h1 => (hC.node k h0 (by omega)).1, fun k h0 h1 => (hC.node k h0 (by omega)).2,
    fun k l h0 h1 h2 h3 => hC.adj k l h0 (by omega) h2 (by omega), fun hcs => ?_, ?_⟩
  · exact hr _ (hC.node 0 (Int.le_refl 0) (by omega)).2 (hC.node 0 (Int.le_refl 0) (by omega)).1
  · intro k h0 h1
    have hson : ∀ n, g.node? (D k) = some n → k + 1 < g.current_step → D (k + 1) ∈ n.sons := by
      intro n hn hk1
      obtain ⟨m, hm, hp⟩ := hC.link (k + 1) (by omega) (by omega)
      rw [show k + 1 - 1 = k by omega] at hp
      have hcomp := (hli.2.2 m (node?_mem hm)).1 _ hp
      rw [node?_id hm] at hcomp
      have hadj : g.Adj n.id (D (k + 1)) := by rw [node?_id hn]; exact hC.adj k (k + 1) h0 (by omega) (by omega) (by omega)
      rw [← node?_id hn] at hcomp
      exact (hli.2.1 n (node?_mem hn) (D (k + 1)) (hC.node (k + 1) (by omega) (by omega)).2 hadj).2 hcomp
    by_cases hk : 0 < k
    · obtain ⟨n, hn, hp⟩ := hC.link k hk (by omega)
      exact ⟨n, hn, fun _ => hp, hson n hn⟩
    · obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hdocs (hC.node k h0 (by omega)).2)
      exact ⟨n, hn, fun h => absurd h hk, hson n hn⟩

-- ============================================================
-- Lo que conserva camarillas conserva LiveExt
-- ============================================================

/-- En un subestado, el documento de un nodo tiene menos padres (con ids únicos en el estado mayor). -/
theorem node?_sub {h g : GPathB} (hs : Sub h g) (hnd : NodupIds g) {x : PathNodeId} {n : PNodeB}
    (hn : h.node? x = some n) : ∃ m, g.node? x = some m ∧ ∀ p ∈ n.parents, p ∈ m.parents := by
  obtain ⟨m, hm, hid, hp, _⟩ := hs.nodes n (node?_mem hn)
  refine ⟨m, find?_of_nodup_id g.nodes hnd m hm x (by rw [hid]; exact node?_id hn), hp⟩

/-- **Una cadena viva del subestado es viva en el estado mayor.** -/
theorem liveChain_sub {h g : GPathB} {F G : Trios} (hs : Sub h g) (hnd : NodupIds g)
    (hFG : ∀ x y z, F x y z → G x y z) {C : Int → PathNodeId} {j : Int} (hC : LiveChain h G C j) :
    LiveChain g F C j := by
  have hst := hs.step
  refine ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩, fun a b c ha hab hbc hc hf => ?_⟩
  · obtain ⟨a, b⟩ := hC.chain.node k h1 (by rw [hst]; exact h2); exact ⟨a, hs.alive _ b⟩
  · exact hs.adj _ _ (hC.chain.adj k l h1 (by rw [hst]; exact h2) h3 (by rw [hst]; exact h4))
  · obtain ⟨n, hn, hp⟩ := hC.chain.link k h1 (by rw [hst]; exact h2)
    obtain ⟨m, hm, hpm⟩ := node?_sub hs hnd hn
    exact ⟨m, hm, hpm _ hp⟩
  · apply hC.live a b c ha hab hbc (by rw [hst]; exact hc)
    unfold Sym at hf ⊢
    rcases hf with hf | hf | hf | hf | hf | hf
    · exact Or.inl (hFG _ _ _ hf)
    · exact Or.inr (Or.inl (hFG _ _ _ hf))
    · exact Or.inr (Or.inr (Or.inl (hFG _ _ _ hf)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hFG _ _ _ hf))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hFG _ _ _ hf)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hFG _ _ _ hf)))))

/-- **Conservar camarillas conserva `LiveExt`**: si `h` es un subestado de `g`, con más tríos prohibidos, y toda
camarilla de `g` que esquiva `F` es camarilla de `h` y esquiva `G`, entonces `LiveExt g F ⟹ LiveExt h G`. -/
theorem liveExt_of_keep {g h : GPathB} {F G : Trios} (hext : LiveExt g F) (hdocs : AliveDocs g) (hli : LinksInv g)
    (hr : RootNone g) (hnd : NodupIds g) (hnF : NoDeg F) (hs : Sub h g) (hFG : ∀ x y z, F x y z → G x y z)
    (hkeep : ∀ D, Carried g D → Avoids F g.current_step D → Carried h D ∧ Avoids G h.current_step D) :
    LiveExt h G := by
  intro C j hC hj1 hjt
  have hst := hs.step
  obtain ⟨D, hD, hag⟩ := liveChain_extend_full hext (liveChain_sub hs hnd hFG hC) (by omega) (by rw [← hst]; exact hjt)
  obtain ⟨hcD, hAD⟩ := hkeep D (carried_of_liveChain hdocs hli hr hD) (avoids_of_liveChain hnF hD)
  exact ⟨D, liveChain_of_carried hcD hAD (by omega), hag⟩

/-- **La revisión conserva `LiveExt`.** -/
theorem liveExt_review {g : GPathB} {F : Trios} (hext : LiveExt g F) (hdocs : AliveDocs g) (hli : LinksInv g)
    (hr : RootNone g) (hnd : NodupIds g) (hnF : NoDeg F) : LiveExt g.review F :=
  liveExt_of_keep hext hdocs hli hr hnd hnF (shrinks_review g).1 (fun _ _ _ h => h)
    (fun D hc hA => ⟨carried_review hc, by rw [(shrinks_review g).1.step]; exact hA⟩)

theorem shrinks_forbidSweep (g : GPathB) (F : Trios) : Shrinks (forbidSweep g F) g := by
  unfold forbidSweep
  exact shrinks_foldl _ (fun h (e : PathNodeId × PathNodeId) => shrinks_removeEdge h e.1 e.2) _ _

/-- **La regla de los tríos (una vuelta) conserva `LiveExt`**, con los tríos nuevos. -/
theorem liveExt_forbidRound {g : GPathB} {F : Trios} (hext : LiveExt g F) (hdocs : AliveDocs g) (hli : LinksInv g)
    (hr : RootNone g) (hnd : NodupIds g) (hnF : NoDeg F) :
    LiveExt (forbidSweep g (ruleF g F)) (ruleF g F) :=
  liveExt_of_keep hext hdocs hli hr hnd hnF (shrinks_forbidSweep g _).1 (fun _ _ _ h => Or.inl h)
    (fun _ hc hA => forbidRound_sound hc hA)

-- ============================================================
-- Los tríos siguen sin degenerar
-- ============================================================

theorem noDeg_ruleF {g : GPathB} {F : Trios} (h : NoDeg F) : NoDeg (ruleF g F) := by
  rintro x y z (hf | ⟨-, -, -, a, b, c, -⟩)
  · exact h _ _ _ hf
  · exact ⟨a, b, c⟩

theorem noDeg_upF {g : GPathB} {F : Trios} {d : NodeId} (h : NoDeg F) : NoDeg (upF g F d) := by
  rintro x y z (hf | ⟨hx, hy, hz, hyz, -⟩)
  · exact h _ _ _ hf
  · refine ⟨fun e => ?_, fun e => ?_, hyz⟩ <;> subst e <;> omega

theorem rootNone_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool} (hr : RootNone g)
    (hd : d.step = g.current_step) : RootNone (g.addNode d title forb) := by
  intro x hx hx0
  rcases List.mem_append.mp hx with h | h
  · exact hr x h hx0
  · have hs := (List.mem_filter.mp h).1
    unfold shiftRowIds at hs
    split at hs
    · rename_i hpos
      have := Machine.mapId_of_mem_shiftRowIds (g := g) (d := d) (by unfold shiftRowIds; rw [if_pos hpos]; exact hs)
      rw [this] at hx0; omega
    · rw [List.mem_singleton] at hs; subst hs; rfl

-- ============================================================
-- La fila nueva
-- ============================================================

section AddNode

variable {g : GPathB} {F : Trios} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- Un nodo nuevo tiene un padre vivo en el paso de abajo. -/
theorem exists_rowParent (hda : DocsAlive g) (hpos : 0 < g.current_step) {t : PathNodeId}
    (ht : t ∈ g.newRowIds d forb) : ∃ q ∈ g.rowParents d t, q ∈ g.alive ∧ q.id.step = g.current_step - 1 := by
  have hs := (List.mem_filter.mp ht).1
  unfold shiftRowIds at hs
  rw [if_pos hpos] at hs
  obtain ⟨q, hq, hqt⟩ := List.mem_map.mp ((mem_dedupPids _ _).mp hs)
  refine ⟨q, List.mem_filter.mpr ⟨hq, by simp [hqt]⟩, ?_⟩
  unfold newParents at hq
  rw [if_pos hpos] at hq
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hq
  have ⟨hnm, hns⟩ := List.mem_filter.mp hn
  exact ⟨hda n hnm, by simpa using hns⟩

/-- La arista de un nodo nuevo a un vivo viejo que posee uno de sus padres. -/
theorem adj_addNode_row {t w p : PathNodeId} (ht : t ∈ g.newRowIds d forb) (hw : w ∈ g.alive)
    (hlt : w.id.step < t.id.step) (hp : p ∈ g.rowParents d t) (hpw : g.Adj p w) :
    (g.addNode d title forb).Adj t w := by
  rw [adj_iff]
  refine Or.inr ⟨(t, w), List.mem_append_right _ ?_, Or.inl ⟨rfl, rfl⟩⟩
  refine List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨w, ?_, rfl⟩⟩
  refine List.mem_filter.mpr ⟨hw, ?_⟩
  rw [Bool.and_eq_true]
  exact ⟨by simpa using hlt, List.any_eq_true.mpr ⟨p, hp, hpw⟩⟩

theorem adj_addNode_mono {x w : PathNodeId} (h : g.Adj x w) : (g.addNode d title forb).Adj x w :=
  adj_mono (fun _ hq => List.mem_append_left _ hq) (fun _ he => List.mem_append_left _ he) _ _ h

/-- Entre nodos viejos, `upF` es `F`. -/
theorem sym_upF_old {x y z : PathNodeId} (hx : x.id.step < g.current_step) (hy : y.id.step < g.current_step)
    (hz : z.id.step < g.current_step) (h : Sym (upF g F d) x y z) : Sym F x y z := by
  unfold Sym upF at h
  unfold Sym
  rcases h with (h | ⟨e, -⟩) | (h | ⟨e, -⟩) | (h | ⟨e, -⟩) | (h | ⟨e, -⟩) | (h | ⟨e, -⟩) | (h | ⟨e, -⟩)
  all_goals first
    | omega
    | simp [h]

/-- **Un trío con el nodo nuevo `t`** no está prohibido si no lo está el de su padre `p`. -/
theorem not_sym_upF_top (hB : FBelow F g.current_step) {t x y p : PathNodeId} (ht : t.id.step = g.current_step)
    (hx : x.id.step < g.current_step) (hy : y.id.step < g.current_step) (hp : p ∈ g.rowParents d t)
    (h1 : ¬ SideForbids g F p x y) (h2 : ¬ SideForbids g F p y x) : ¬ Sym (upF g F d) x y t := by
  intro h
  unfold Sym upF at h
  rcases h with (h | ⟨e, -⟩) | (h | ⟨e, -⟩) | (h | ⟨e, -⟩) | (h | ⟨e, -⟩) | (h | ⟨-, -, -, -, hall⟩) |
      (h | ⟨-, -, -, -, hall⟩)
  all_goals first
    | omega
    | (obtain ⟨a, b, c⟩ := hB _ _ _ h; omega)
    | exact h1 (hall p hp)
    | exact h2 (hall p hp)

/-- **La fila nueva conserva `LiveExt`**, con los tríos que hereda de sus padres (`upF`). -/
theorem liveExt_addNode (hext : LiveExt g F) (hdocs : AliveDocs g) (hb : Below g) (hda : DocsAlive g)
    (hd : d.step = g.current_step) (hB : FBelow F g.current_step) (hnF : NoDeg F) :
    LiveExt (g.addNode d title forb) (upF g F d) := by
  intro C j hC hj1 hjt
  have e1 : (g.addNode d title forb).current_step - 1 = g.current_step := by
    show g.current_step + 1 - 1 = _; omega
  rw [e1] at hjt
  -- la cima
  obtain ⟨hts, hta⟩ := hC.chain.node g.current_step hjt (by rw [e1]; omega)
  have htnew : C g.current_step ∈ g.newRowIds d forb := by
    rcases alive_addNode_cases hdocs hb hd hta with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact h
  have hnodeT := node?_addNode_new (title := title) hb hd htnew
  -- los nodos viejos de la cadena
  have hold : ∀ k, j ≤ k → k < g.current_step → (C k).id.step = k ∧ C k ∈ g.alive := by
    intro k h1 h2
    obtain ⟨hs, ha⟩ := hC.chain.node k h1 (by rw [e1]; omega)
    rcases alive_addNode_cases hdocs hb hd ha with ⟨h, _⟩ | ⟨_, h⟩
    · exact ⟨hs, h⟩
    · omega
  by_cases hjT : j = g.current_step
  · -- la cadena es solo la cima: se baja a un padre vivo
    subst hjT
    obtain ⟨q, hqp, hqa, hqs⟩ := exists_rowParent hda (by omega) htnew
    classical
    let C' : Int → PathNodeId := fun k => if k = g.current_step - 1 then q else C k
    have hC'q : C' (g.current_step - 1) = q := by simp [C']
    have hC'T : C' g.current_step = C g.current_step := by simp [C']; intro h; exact absurd h (by omega)
    have hqT : (g.addNode d title forb).Adj (C g.current_step) q :=
      adj_addNode_row htnew hqa (by rw [hqs, hts]; omega) hqp (adj_refl _ _ hqa)
    refine ⟨C', ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩,
      fun a b c ha hab hbc hc => by rw [e1] at hc; omega⟩, fun k hk => by simp [C']; omega⟩
    · rw [e1] at h2
      by_cases hk : k = g.current_step - 1
      · rw [hk, hC'q]; exact ⟨hqs, List.mem_append_left _ hqa⟩
      · rw [show k = g.current_step by omega, hC'T]; exact ⟨hts, hta⟩
    · rw [e1] at h2 h4
      have hk : k = g.current_step - 1 ∨ k = g.current_step := by omega
      have hl : l = g.current_step - 1 ∨ l = g.current_step := by omega
      rcases hk with rfl | rfl <;> rcases hl with hl | hl <;> rw [hl]
      · rw [hC'q]; exact adj_refl _ _ (List.mem_append_left _ hqa)
      · rw [hC'q, hC'T]; exact (adj_symm _ _ _).mp hqT
      · rw [hC'q, hC'T]; exact hqT
      · rw [hC'T]; exact adj_refl _ _ hta
    · rw [e1] at h2
      rw [show k = g.current_step by omega, hC'T, show g.current_step - 1 = g.current_step - 1 from rfl, hC'q]
      exact ⟨_, hnodeT, hqp⟩
  · -- debajo de la cima, la cadena es una cadena viva del remitente
    have hjlt : j < g.current_step := by omega
    obtain ⟨n, hn, hpn⟩ := hC.chain.link g.current_step hjlt (by rw [e1]; omega)
    rw [hnodeT] at hn
    cases hn
    have hpar : C (g.current_step - 1) ∈ g.rowParents d (C g.current_step) := hpn
    have hCg : LiveChain g F C j := by
      refine ⟨⟨fun k h1 h2 => hold k h1 (by omega), fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩,
        fun a b c ha hab hbc hc hs => ?_⟩
      · exact adj_addNode_old hd (by rw [(hold k h1 (by omega)).1]; omega) (by rw [(hold l h3 (by omega)).1]; omega)
          (hC.chain.adj k l h1 (by rw [e1]; omega) h3 (by rw [e1]; omega))
      · obtain ⟨m, hm, hpm⟩ := hC.chain.link k h1 (by rw [e1]; omega)
        rw [node?_addNode_old hd (by rw [(hold k (by omega) (by omega)).1]; omega)] at hm
        cases hgk : g.node? (C k) with
        | none => rw [hgk] at hm; cases hm
        | some m' =>
          rw [hgk] at hm; cases hm
          exact ⟨m', rfl, hpm⟩
      · apply hC.live a b c ha hab hbc (by rw [e1]; omega)
        unfold Sym at hs ⊢; unfold upF
        rcases hs with h | h | h | h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    obtain ⟨D, hD, hag⟩ := hext C j hCg hj1 (by omega)
    classical
    let C' : Int → PathNodeId := fun k => if j ≤ k then C k else D k
    have hC'old : ∀ k, j - 1 ≤ k → k < g.current_step → C' k = D k := by
      intro k h1 h2
      by_cases hk : j ≤ k
      · simp [C', hk]; exact (hag k hk).symm
      · simp [C', hk]
    have hC'T : C' g.current_step = C g.current_step := by simp [C']; omega
    have hDn : ∀ k, j - 1 ≤ k → k < g.current_step → (D k).id.step = k ∧ D k ∈ g.alive :=
      fun k h1 h2 => hD.chain.node k h1 (by omega)
    have hDadj : ∀ k l, j - 1 ≤ k → k < g.current_step → j - 1 ≤ l → l < g.current_step → g.Adj (D k) (D l) :=
      fun k l h1 h2 h3 h4 => hD.chain.adj k l h1 (by omega) h3 (by omega)
    have hpD : D (g.current_step - 1) = C (g.current_step - 1) := hag _ (by omega)
    -- el nodo nuevo es vecino de todo lo viejo de la cadena, a través de su padre
    have htD : ∀ l, j - 1 ≤ l → l < g.current_step → (g.addNode d title forb).Adj (C g.current_step) (D l) := by
      intro l h1 h2
      refine adj_addNode_row htnew (hDn l h1 h2).2 (by rw [(hDn l h1 h2).1, hts]; exact h2) hpar ?_
      rw [← hpD]; exact hDadj _ _ (by omega) (by omega) h1 h2
    refine ⟨C', ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩,
      fun a b c ha hab hbc hc => ?_⟩, fun k hk => by simp [C', hk]⟩
    · rw [e1] at h2
      by_cases hk : k < g.current_step
      · rw [hC'old k h1 hk]; exact ⟨(hDn k h1 hk).1, List.mem_append_left _ (hDn k h1 hk).2⟩
      · rw [show k = g.current_step by omega, hC'T]; exact ⟨hts, hta⟩
    · rw [e1] at h2 h4
      by_cases hk : k < g.current_step <;> by_cases hl : l < g.current_step
      · rw [hC'old k h1 hk, hC'old l h3 hl]; exact adj_addNode_mono (hDadj k l h1 hk h3 hl)
      · rw [hC'old k h1 hk, show l = g.current_step by omega, hC'T]
        exact (adj_symm _ _ _).mp (htD k h1 hk)
      · rw [hC'old l h3 hl, show k = g.current_step by omega, hC'T]; exact htD l h3 hl
      · rw [show k = g.current_step by omega, show l = g.current_step by omega, hC'T]; exact adj_refl _ _ hta
    · rw [e1] at h2
      by_cases hk : k < g.current_step
      · rw [hC'old k (by omega) hk, hC'old (k - 1) (by omega) (by omega)]
        obtain ⟨m, hm, hpm⟩ := hD.chain.link k h1 (by omega)
        refine ⟨g.withGained d forb m, ?_, hpm⟩
        rw [node?_addNode_old hd (by rw [(hDn k (by omega) hk).1]; exact hk), hm]; rfl
      · rw [show k = g.current_step by omega, hC'T, hC'old _ (by omega) (by omega), hpD]
        exact ⟨_, hnodeT, hpar⟩
    · rw [e1] at hc
      by_cases hcT : c < g.current_step
      · rw [hC'old a ha (by omega), hC'old b (by omega) (by omega), hC'old c (by omega) hcT]
        intro hs
        exact hD.live a b c ha hab hbc (by omega)
          (sym_upF_old (by rw [(hDn a ha (by omega)).1]; omega) (by rw [(hDn b (by omega) (by omega)).1]; omega)
            (by rw [(hDn c (by omega) hcT).1]; exact hcT) hs)
      · rw [show c = g.current_step by omega, hC'T, hC'old a ha (by omega), hC'old b (by omega) (by omega)]
        have hxs := (hDn a ha (by omega)).1
        have hys := (hDn b (by omega) (by omega)).1
        -- el padre p = D (cima - 1): el trío (p, x, y) no está prohibido en el remitente
        have hnot : ∀ u v : Int, j - 1 ≤ u → u < g.current_step → j - 1 ≤ v → v < g.current_step → u ≠ v →
            ¬ SideForbids g F (C (g.current_step - 1)) (D u) (D v) := by
          intro u v h1 h2 h3 h4 huv
          rw [← hpD]
          rintro (hn | hf)
          · exact hn ⟨hDadj _ _ (by omega) (by omega) h1 h2, hDadj _ _ (by omega) (by omega) h3 h4,
              hDadj _ _ h1 h2 h3 h4⟩
          · by_cases hu : u = g.current_step - 1
            · subst hu; exact (hnF _ _ _ hf).1 rfl
            · by_cases hv : v = g.current_step - 1
              · subst hv; exact (hnF _ _ _ hf).2.1 rfl
              · exact liveChain_not_F hD (by omega) h1 h3 (by omega) (by omega) (by omega)
                  (fun e => hu e.symm) (fun e => hv e.symm) huv hf
        exact not_sym_upF_top hB hts (by rw [hxs]; omega) (by rw [hys]; omega) hpar
          (hnot a b ha (by omega) (by omega) (by omega) (by omega))
          (hnot b a (by omega) (by omega) ha (by omega) (by omega))

/-- Un trío con un nodo del paso `T` no está en una relación por debajo de `T`. -/
theorem not_sym_top {F : Trios} {T : Int} (hB : FBelow F T) {x y t : PathNodeId} (ht : t.id.step = T) :
    ¬ Sym F x y t := by
  intro h
  unfold Sym at h
  rcases h with h | h | h | h | h | h <;> (obtain ⟨a, b, c⟩ := hB _ _ _ h; omega)

/-- **La fila nueva conserva `LiveExt` con la misma relación**: heredar tríos no hace falta, porque los tríos con un
nodo nuevo nunca están en `F` (`FBelow`). (Sonda `ABL=noup`: sin herencia del UP, 0 callejones.) -/
theorem liveExt_addNode_same (hext : LiveExt g F) (hdocs : AliveDocs g) (hb : Below g) (hda : DocsAlive g)
    (hd : d.step = g.current_step) (hB : FBelow F g.current_step) :
    LiveExt (g.addNode d title forb) F := by
  intro C j hC hj1 hjt
  have e1 : (g.addNode d title forb).current_step - 1 = g.current_step := by
    show g.current_step + 1 - 1 = _; omega
  rw [e1] at hjt
  -- la cima
  obtain ⟨hts, hta⟩ := hC.chain.node g.current_step hjt (by rw [e1]; omega)
  have htnew : C g.current_step ∈ g.newRowIds d forb := by
    rcases alive_addNode_cases hdocs hb hd hta with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact h
  have hnodeT := node?_addNode_new (title := title) hb hd htnew
  -- los nodos viejos de la cadena
  have hold : ∀ k, j ≤ k → k < g.current_step → (C k).id.step = k ∧ C k ∈ g.alive := by
    intro k h1 h2
    obtain ⟨hs, ha⟩ := hC.chain.node k h1 (by rw [e1]; omega)
    rcases alive_addNode_cases hdocs hb hd ha with ⟨h, _⟩ | ⟨_, h⟩
    · exact ⟨hs, h⟩
    · omega
  by_cases hjT : j = g.current_step
  · -- la cadena es solo la cima: se baja a un padre vivo
    subst hjT
    obtain ⟨q, hqp, hqa, hqs⟩ := exists_rowParent hda (by omega) htnew
    classical
    let C' : Int → PathNodeId := fun k => if k = g.current_step - 1 then q else C k
    have hC'q : C' (g.current_step - 1) = q := by simp [C']
    have hC'T : C' g.current_step = C g.current_step := by simp [C']; intro h; exact absurd h (by omega)
    have hqT : (g.addNode d title forb).Adj (C g.current_step) q :=
      adj_addNode_row htnew hqa (by rw [hqs, hts]; omega) hqp (adj_refl _ _ hqa)
    refine ⟨C', ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩,
      fun a b c ha hab hbc hc => by rw [e1] at hc; omega⟩, fun k hk => by simp [C']; omega⟩
    · rw [e1] at h2
      by_cases hk : k = g.current_step - 1
      · rw [hk, hC'q]; exact ⟨hqs, List.mem_append_left _ hqa⟩
      · rw [show k = g.current_step by omega, hC'T]; exact ⟨hts, hta⟩
    · rw [e1] at h2 h4
      have hk : k = g.current_step - 1 ∨ k = g.current_step := by omega
      have hl : l = g.current_step - 1 ∨ l = g.current_step := by omega
      rcases hk with rfl | rfl <;> rcases hl with hl | hl <;> rw [hl]
      · rw [hC'q]; exact adj_refl _ _ (List.mem_append_left _ hqa)
      · rw [hC'q, hC'T]; exact (adj_symm _ _ _).mp hqT
      · rw [hC'q, hC'T]; exact hqT
      · rw [hC'T]; exact adj_refl _ _ hta
    · rw [e1] at h2
      rw [show k = g.current_step by omega, hC'T, show g.current_step - 1 = g.current_step - 1 from rfl, hC'q]
      exact ⟨_, hnodeT, hqp⟩
  · -- debajo de la cima, la cadena es una cadena viva del remitente
    have hjlt : j < g.current_step := by omega
    obtain ⟨n, hn, hpn⟩ := hC.chain.link g.current_step hjlt (by rw [e1]; omega)
    rw [hnodeT] at hn
    cases hn
    have hpar : C (g.current_step - 1) ∈ g.rowParents d (C g.current_step) := hpn
    have hCg : LiveChain g F C j := by
      refine ⟨⟨fun k h1 h2 => hold k h1 (by omega), fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩,
        fun a b c ha hab hbc hc hs => ?_⟩
      · exact adj_addNode_old hd (by rw [(hold k h1 (by omega)).1]; omega) (by rw [(hold l h3 (by omega)).1]; omega)
          (hC.chain.adj k l h1 (by rw [e1]; omega) h3 (by rw [e1]; omega))
      · obtain ⟨m, hm, hpm⟩ := hC.chain.link k h1 (by rw [e1]; omega)
        rw [node?_addNode_old hd (by rw [(hold k (by omega) (by omega)).1]; omega)] at hm
        cases hgk : g.node? (C k) with
        | none => rw [hgk] at hm; cases hm
        | some m' =>
          rw [hgk] at hm; cases hm
          exact ⟨m', rfl, hpm⟩
      · exact hC.live a b c ha hab hbc (by rw [e1]; omega) hs
    obtain ⟨D, hD, hag⟩ := hext C j hCg hj1 (by omega)
    classical
    let C' : Int → PathNodeId := fun k => if j ≤ k then C k else D k
    have hC'old : ∀ k, j - 1 ≤ k → k < g.current_step → C' k = D k := by
      intro k h1 h2
      by_cases hk : j ≤ k
      · simp [C', hk]; exact (hag k hk).symm
      · simp [C', hk]
    have hC'T : C' g.current_step = C g.current_step := by simp [C']; omega
    have hDn : ∀ k, j - 1 ≤ k → k < g.current_step → (D k).id.step = k ∧ D k ∈ g.alive :=
      fun k h1 h2 => hD.chain.node k h1 (by omega)
    have hDadj : ∀ k l, j - 1 ≤ k → k < g.current_step → j - 1 ≤ l → l < g.current_step → g.Adj (D k) (D l) :=
      fun k l h1 h2 h3 h4 => hD.chain.adj k l h1 (by omega) h3 (by omega)
    have hpD : D (g.current_step - 1) = C (g.current_step - 1) := hag _ (by omega)
    -- el nodo nuevo es vecino de todo lo viejo de la cadena, a través de su padre
    have htD : ∀ l, j - 1 ≤ l → l < g.current_step → (g.addNode d title forb).Adj (C g.current_step) (D l) := by
      intro l h1 h2
      refine adj_addNode_row htnew (hDn l h1 h2).2 (by rw [(hDn l h1 h2).1, hts]; exact h2) hpar ?_
      rw [← hpD]; exact hDadj _ _ (by omega) (by omega) h1 h2
    refine ⟨C', ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩,
      fun a b c ha hab hbc hc => ?_⟩, fun k hk => by simp [C', hk]⟩
    · rw [e1] at h2
      by_cases hk : k < g.current_step
      · rw [hC'old k h1 hk]; exact ⟨(hDn k h1 hk).1, List.mem_append_left _ (hDn k h1 hk).2⟩
      · rw [show k = g.current_step by omega, hC'T]; exact ⟨hts, hta⟩
    · rw [e1] at h2 h4
      by_cases hk : k < g.current_step <;> by_cases hl : l < g.current_step
      · rw [hC'old k h1 hk, hC'old l h3 hl]; exact adj_addNode_mono (hDadj k l h1 hk h3 hl)
      · rw [hC'old k h1 hk, show l = g.current_step by omega, hC'T]
        exact (adj_symm _ _ _).mp (htD k h1 hk)
      · rw [hC'old l h3 hl, show k = g.current_step by omega, hC'T]; exact htD l h3 hl
      · rw [show k = g.current_step by omega, show l = g.current_step by omega, hC'T]; exact adj_refl _ _ hta
    · rw [e1] at h2
      by_cases hk : k < g.current_step
      · rw [hC'old k (by omega) hk, hC'old (k - 1) (by omega) (by omega)]
        obtain ⟨m, hm, hpm⟩ := hD.chain.link k h1 (by omega)
        refine ⟨g.withGained d forb m, ?_, hpm⟩
        rw [node?_addNode_old hd (by rw [(hDn k (by omega) hk).1]; exact hk), hm]; rfl
      · rw [show k = g.current_step by omega, hC'T, hC'old _ (by omega) (by omega), hpD]
        exact ⟨_, hnodeT, hpar⟩
    · rw [e1] at hc
      by_cases hcT : c < g.current_step
      · rw [hC'old a ha (by omega), hC'old b (by omega) (by omega), hC'old c (by omega) hcT]
        intro hs
        exact hD.live a b c ha hab hbc (by omega)
          hs
      · rw [show c = g.current_step by omega, hC'T, hC'old a ha (by omega), hC'old b (by omega) (by omega)]
        have hxs := (hDn a ha (by omega)).1
        have hys := (hDn b (by omega) (by omega)).1
        -- el padre p = D (cima - 1): el trío (p, x, y) no está prohibido en el remitente
        exact not_sym_top hB hts

/-- **El UP sin el filtro conserva `LiveExt`**: la fila nueva y la revisión, con los tríos heredados (`upF`). -/
theorem liveExt_up (hext : LiveExt g F) (hv : g.isValid = true) (hdocs : AliveDocs g) (hb : Below g)
    (hda : DocsAlive g) (hli : LinksInv g) (hz : AboveZero g) (hnd : NodupIds g) (hr : RootNone g)
    (hd : d.step = g.current_step) (hB : FBelow F g.current_step) (hnF : NoDeg F) :
    LiveExt (g.up d title forb) (upF g F d) := by
  unfold up
  rw [if_pos hv]
  exact liveExt_review (liveExt_addNode hext hdocs hb hda hd hB hnF) (Machine.aliveDocs_addNode hdocs)
    (linksInv_addNode hli hb hz hd) (rootNone_addNode hr hd) (nodupIds_addNode hnd hb hd) (noDeg_upF hnF)

end AddNode

-- ============================================================
-- El filtro de requisitos (un pin)
-- ============================================================

/-- **`PinLive g F reqs`**: toda cadena viva del estado filtrado se completa, viva, en el remitente, por una rama que
concuerda con los requisitos. -/
def PinLive (g : GPathB) (F : Trios) (reqs : List NodeId) : Prop :=
  ∀ C j, LiveChain (g.filterAll reqs) F C j → 1 ≤ j → j ≤ g.current_step - 1 →
    ∃ D, LiveChain g F D 0 ∧ (∀ k, j ≤ k → D k = C k) ∧ ∀ r ∈ reqs, Agrees g.current_step D r

/-- **`PinLive` ⟹ el filtro conserva `LiveExt`.** La rama completa es camarilla del remitente, concuerda con los
requisitos, así que sobrevive al filtro (`carried_filterAll`). -/
theorem liveExt_filterAll {g : GPathB} {F : Trios} {reqs : List NodeId} (hpin : PinLive g F reqs)
    (hdocs : AliveDocs g) (hli : LinksInv g) (hr : RootNone g) (hnF : NoDeg F) : LiveExt (g.filterAll reqs) F := by
  intro C j hC hj1 hjt
  have hst : (g.filterAll reqs).current_step = g.current_step := (shrinks_filterAll g reqs).1.step
  obtain ⟨D, hD, hag, hagr⟩ := hpin C j hC hj1 (by rw [← hst]; exact hjt)
  have hc := carried_filterAll (carried_of_liveChain hdocs hli hr hD) reqs hagr
  have hA : Avoids F (g.filterAll reqs).current_step D := by rw [hst]; exact avoids_of_liveChain hnF hD
  exact ⟨D, liveChain_of_carried hc hA (by omega), hag⟩

/-- **Y al revés**: si el filtro deja un estado válido con `LiveExt`, vale `PinLive`. Así, `PinLive` es exactamente lo
que el filtro necesita. -/
theorem pinLive_of_liveExt {g : GPathB} {F : Trios} {reqs : List NodeId} (hext : LiveExt (g.filterAll reqs) F)
    (hv : (g.filterAll reqs).isValid = true) (hdocs : AliveDocs g) (hnd : NodupIds g) : PinLive g F reqs := by
  intro C j hC hj1 hjt
  have hs := (shrinks_filterAll g reqs).1
  obtain ⟨D, hD, hag⟩ := liveChain_extend_full hext hC (by omega) (by rw [hs.step]; exact hjt)
  refine ⟨D, liveChain_sub hs hnd (fun _ _ _ h => h) hD, hag, fun r hr h0 h1 => ?_⟩
  obtain ⟨hDs, hDa⟩ := hD.chain.node r.step h0 (by rw [hs.step]; omega)
  exact pinned_filterAll_list hdocs reqs hv r hr _ hDa hDs

/-- **El UP entero** (`upFiltering`: filtro, fila nueva y revisión) conserva `LiveExt` bajo `PinLive`. -/
theorem liveExt_upFiltering {g : GPathB} {F : Trios} {reqs : List NodeId} {d : NodeId} {title : String}
    {forb : PathNodeId → Bool} (hpin : PinLive g F reqs) (hdocs : AliveDocs g) (hli : LinksInv g) (hr : RootNone g)
    (hnF : NoDeg F) (hv' : (g.filterAll reqs).isValid = true) (hdocs' : AliveDocs (g.filterAll reqs))
    (hb' : Below (g.filterAll reqs)) (hda' : DocsAlive (g.filterAll reqs)) (hli' : LinksInv (g.filterAll reqs))
    (hz' : AboveZero (g.filterAll reqs)) (hnd' : NodupIds (g.filterAll reqs)) (hr' : RootNone (g.filterAll reqs))
    (hd : d.step = (g.filterAll reqs).current_step) (hB : FBelow F (g.filterAll reqs).current_step) :
    LiveExt (g.upFiltering reqs d title forb) (upF (g.filterAll reqs) F d) :=
  liveExt_up (liveExt_filterAll hpin hdocs hli hr hnF) hv' hdocs' hb' hda' hli' hz' hnd' hr' hd hB hnF

end GPathB

end AbsSatBingo.Model
