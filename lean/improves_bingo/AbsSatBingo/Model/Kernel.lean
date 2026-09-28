-- lean/improves_bingo/AbsSatBingo/Model/Kernel.lean
import AbsSatBingo.Model.MachineClique

/-!
# El review como núcleo: fijar es restringir a las estructuras cerradas

Base para `ReviewExact` (plan: `docs/plans/lean_bingo.md`). El review solo borra, y toda estructura cerrada por las
reglas (`SecStruct`) sobrevive a él (`secStruct_review`). Si además el estado que deja está cerrado (`ClosedState`,
**hipótesis**: el review del modelo solo corre las pasadas de padres e hijos con `dirty`, así que el cierre por
apoyo a la salida no lo da el mecanismo; medido: esas pasadas nunca cortan nada), entonces:

* **`pinEdge_iff_kernel`**: las aristas del pin de `P` son exactamente las parejas de las estructuras cerradas del
  estado original que concuerdan con `P` (el **núcleo** `Kernel g P`);
* **`pin_confluent`**: fijar `b₁` y luego `b₂` deja las mismas aristas que fijar los dos a la vez.

La herramienta es `secStruct_of_sub`: una estructura cerrada de un estado por debajo (con ids únicos arriba) lo es
también del estado de arriba.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

-- ============================================================
-- Ids únicos y node?
-- ============================================================

/-- Cada id tiene un solo documento. -/
def NodupIds (g : GPathB) : Prop := (g.nodes.map (·.id)).Nodup

theorem find?_of_nodup_id : ∀ (l : List PNodeB), (l.map (·.id)).Nodup → ∀ m ∈ l, ∀ x, m.id = x →
    l.find? (fun n => n.id == x) = some m := by
  intro l
  induction l with
  | nil => intro _ m hm; cases hm
  | cons a as ih =>
    intro hnd m hm x hmx
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp hm with rfl | hm'
    · simp [hmx]
    · have hax : (a.id == x) = false := by
        apply beq_false_of_ne
        intro hax
        exact hnd.1 (List.mem_map.mpr ⟨m, hm', by rw [hmx, hax]⟩)
      rw [hax]
      exact ih hnd.2 m hm' x hmx

theorem node?_of_nodup {g : GPathB} (hnd : NodupIds g) {m : PNodeB} (hm : m ∈ g.nodes) : g.node? m.id = some m :=
  find?_of_nodup_id g.nodes hnd m hm m.id rfl

-- ============================================================
-- Subir una estructura cerrada
-- ============================================================

variable {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- El documento de arriba de un nodo, con los enlaces del de abajo. -/
theorem up_doc {h g : GPathB} (hs : Sub h g) (hnd : NodupIds g) {y : PathNodeId} {n : PNodeB}
    (hn : h.node? y = some n) : ∃ m, g.node? y = some m ∧ (∀ p ∈ n.parents, p ∈ m.parents) ∧
      (∀ s ∈ n.sons, s ∈ m.sons) := by
  obtain ⟨m, hm, hid, hp, hs'⟩ := hs.nodes n (node?_mem hn)
  refine ⟨m, ?_, hp, hs'⟩
  rw [← node?_id hn, ← hid]
  exact node?_of_nodup hnd hm

/-- **Una estructura cerrada de un estado por debajo lo es del de arriba** (con ids únicos arriba). -/
theorem secStruct_of_sub {h g : GPathB} (hs : Sub h g) (hnd : NodupIds g) (hst : SecStruct h V R) :
    SecStruct g V R := by
  refine ⟨fun hy => hs.alive _ (hst.alive hy), hst.refl, hst.symm, hst.dom, fun hr => hs.adj _ _ (hst.adj hr),
    fun hr l h0 h1 => hst.pair hr l h0 (by rw [hs.step]; exact h1), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn, hp, hsn⟩ := hst.node hy
    obtain ⟨m, hm, hpm, hsm⟩ := up_doc hs hnd hn
    refine ⟨m, hm, fun hr => ?_, fun hl => ?_⟩
    · obtain ⟨p, hpn, hyp⟩ := hp hr
      exact ⟨p, hpm p hpn, hyp⟩
    · obtain ⟨s, hsn', hys⟩ := hsn (by rw [hs.step]; exact hl)
      exact ⟨s, hsm s hsn', hys⟩
  · intro x w m hr hxw hm hx1
    obtain ⟨n, hn, _, _⟩ := hst.node (hst.dom hr).1
    obtain ⟨m', hm', hpm, _⟩ := up_doc hs hnd hn
    rw [hm] at hm'; cases hm'
    obtain ⟨p, hpn, hxp, hpw⟩ := hst.par hr hxw hn hx1
    exact ⟨p, hpm p hpn, hxp, hpw⟩
  · intro x w m hr hxw hm hx1
    obtain ⟨n, hn, _, _⟩ := hst.node (hst.dom hr).1
    obtain ⟨m', hm', _, hsm⟩ := up_doc hs hnd hn
    rw [hm] at hm'; cases hm'
    obtain ⟨s, hsn, hxs, hsw⟩ := hst.son hr hxw hn (by rw [hs.step]; exact hx1)
    exact ⟨s, hsm s hsn, hxs, hsw⟩

-- ============================================================
-- El filtro por una lista de requisitos
-- ============================================================

theorem secStruct_filterAll_list {g : GPathB} (h : SecStruct g V R) (reqs : List NodeId)
    (ha : ∀ b ∈ reqs, SecAgrees V b) : SecStruct (g.filterAll reqs) V R := by
  unfold filterAll
  apply secStruct_review
  exact inv_foldl (fun g' => SecStruct g' V R) filterRequire reqs (fun g' b hb hc => sec_filterRequire hc (ha b hb)) g h

/-- Tras el filtro por `reqs` (válido), en el paso de cada requisito solo quedan vivos de él. -/
theorem pinned_filterAll_list {g : GPathB} (hd : AliveDocs g) (reqs : List NodeId)
    (hv : (g.filterAll reqs).isValid = true) :
    ∀ b ∈ reqs, ∀ q ∈ (g.filterAll reqs).alive, q.id.step = b.step → q.id = b := by
  have hsub := (shrinks_review (reqs.foldl filterRequire g)).1
  have hvf : (reqs.foldl filterRequire g).isValid = true := isValid_of_sub hsub hv
  intro b hb q hq hqs
  have hq' := hsub.alive q hq
  -- el requisito `b` mata a los de otro nodo del mapa; lo que sigue solo quita
  suffices ∀ (l : List NodeId) (g : GPathB), AliveDocs g → (l.foldl filterRequire g).isValid = true →
      ∀ q ∈ (l.foldl filterRequire g).alive, (b ∈ l → q.id.step = b.step → q.id = b) by
    exact this reqs g hd hvf q hq' hb hqs
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

-- ============================================================
-- El núcleo y la confluencia
-- ============================================================

/-- **Hipótesis**: el estado está cerrado por las reglas (sus vivos y sus posesiones forman una `SecStruct`). -/
def ClosedState (h : GPathB) : Prop :=
  SecStruct h (fun y => y ∈ h.alive) (fun y w => y ∈ h.alive ∧ w ∈ h.alive ∧ h.Adj y w)

/-- **El núcleo** de `g` fijado en `P`: parejas de estructuras cerradas de `g` que concuerdan con `P`. -/
def Kernel (g : GPathB) (P : List NodeId) (y w : PathNodeId) : Prop :=
  ∃ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct g V R ∧ (∀ b ∈ P, SecAgrees V b) ∧ R y w

theorem kernel_of_pinEdge {g : GPathB} {P : List NodeId} (hd : AliveDocs g) (hnd : NodupIds g)
    (hcl : ClosedState (g.filterAll P)) {y w : PathNodeId} (he : PinEdge (g.filterAll P) y w) : Kernel g P y w := by
  obtain ⟨hv, hy, hw, ha⟩ := he
  refine ⟨_, _, secStruct_of_sub (shrinks_filterAll g P).1 hnd hcl, ?_, hy, hw, ha⟩
  intro b hb q hq hqs
  exact pinned_filterAll_list hd P hv b hb q hq hqs

theorem pinEdge_of_kernel {g : GPathB} {P : List NodeId} {y w : PathNodeId} (hk : Kernel g P y w) :
    PinEdge (g.filterAll P) y w := by
  obtain ⟨V, R, hst, ha, hr⟩ := hk
  have hp := secStruct_filterAll_list hst P ha
  exact ⟨isValid_of_sec hp (hp.dom hr).1, hp.alive (hp.dom hr).1, hp.alive (hp.dom hr).2, hp.adj hr⟩

/-- **Las aristas del pin son el núcleo** (si el pin sale cerrado). -/
theorem pinEdge_iff_kernel {g : GPathB} {P : List NodeId} (hd : AliveDocs g) (hnd : NodupIds g)
    (hcl : ClosedState (g.filterAll P)) (y w : PathNodeId) : PinEdge (g.filterAll P) y w ↔ Kernel g P y w :=
  ⟨kernel_of_pinEdge hd hnd hcl, pinEdge_of_kernel⟩

/-- Fijar primero `b₁` y dentro `b₂` es fijar los dos en `g`, a nivel de núcleo. -/
theorem kernel_pin_iff {g : GPathB} {b₁ b₂ : NodeId} (hd : AliveDocs g) (hnd : NodupIds g) (y w : PathNodeId) :
    Kernel (g.filterAll [b₁]) [b₂] y w ↔ Kernel g [b₁, b₂] y w := by
  constructor
  · rintro ⟨V, R, hst, ha, hr⟩
    have hv1 : (g.filterAll [b₁]).isValid = true := isValid_of_sec hst (hst.dom hr).1
    refine ⟨V, R, secStruct_of_sub (shrinks_filterAll g [b₁]).1 hnd hst, ?_, hr⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · intro q hq hqs
      exact pinned_filterAll_list hd [b] hv1 b (List.mem_singleton_self _) q (hst.alive hq) hqs
    · exact ha b hb
  · rintro ⟨V, R, hst, ha, hr⟩
    refine ⟨V, R, secStruct_filterAll_list hst [b₁] (fun b hb => ha b (by simp at hb; simp [hb])), ?_, hr⟩
    intro b hb
    exact ha b (by simp at hb; simp [hb])

/-- **Confluencia**: fijar `b₁` y luego `b₂` deja las mismas aristas que fijar los dos a la vez (si los pins salen
cerrados). -/
theorem pin_confluent {g : GPathB} {b₁ b₂ : NodeId} (hd : AliveDocs g) (hnd : NodupIds g)
    (hnd₁ : NodupIds (g.filterAll [b₁])) (hcl₁ : ClosedState ((g.filterAll [b₁]).filterAll [b₂]))
    (hcl : ClosedState (g.filterAll [b₁, b₂])) (y w : PathNodeId) :
    PinEdge ((g.filterAll [b₁]).filterAll [b₂]) y w ↔ PinEdge (g.filterAll [b₁, b₂]) y w := by
  have hd₁ : AliveDocs (g.filterAll [b₁]) := aliveDocs_filterAll hd _
  rw [pinEdge_iff_kernel hd₁ hnd₁ hcl₁, kernel_pin_iff hd hnd, pinEdge_iff_kernel hd hnd hcl]

end GPathB

end AbsSatBingo.Model
