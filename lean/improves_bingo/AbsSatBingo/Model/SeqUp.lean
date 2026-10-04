-- lean/improves_bingo/AbsSatBingo/Model/SeqUp.lean
import AbsSatBingo.Model.SeqMachine
import AbsSatBingo.Model.KernelUp

/-!
# `SeqExact` en el review, el filtro y la fila nueva

Sigue `SeqMachine.lean` (pin y join). Aquí, el resto del UP. La herramienta es **bajar un pin**:

* si fijar `P` deja `h` válido y el resultado está cerrado (`ClosedState`, la contabilidad de siempre), sus vivos y
  sus posesiones son una estructura cerrada de `h`, y de todo estado por encima (`sec_of_pinSeq`);
* una estructura cerrada que concuerda con `P` sobrevive a fijar `P` (`sec_pinSeq`), y lo deja válido.

Con eso:
* **el review** conserva `SeqExact` (`seqExact_review`), y **el filtro por requisitos** también
  (`seqExact_filterAll`): las camarillas que concuerdan pasan de arriba abajo;
* **la fila nueva, sin ventana saltada**, conserva `SeqExact` (`seqExact_addNode`): la estructura del pin baja al
  estado anterior (`secStruct_addNode_down`), da allí un pin válido y una camarilla, y la camarilla se alarga con el
  hijo de su cima (`extend_through`).

Hipótesis de contabilidad: `ClosedState` de los pins válidos (`PinsClosed`) y las de `KernelUp`. Con ventana saltada
la fila no se alarga siempre: ahí haría falta la versión de existencia de `AvoidExact` (abierto).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid)

namespace GPathB

open Machine (Below)

variable {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}

/-- Los pins válidos de `h` están cerrados por las reglas. -/
def PinsClosed (h : GPathB) : Prop := ∀ P : List NodeId, (pinSeq h P).isValid = true → ClosedState (pinSeq h P)

-- ============================================================
-- Bajar un pin
-- ============================================================

/-- En un pin sucesivo válido, los vivos del paso de cada pin son de él. -/
theorem pinned_pinSeq : ∀ (P : List NodeId) (g : GPathB), AliveDocs g → (pinSeq g P).isValid = true →
    ∀ b ∈ P, ∀ q ∈ (pinSeq g P).alive, q.id.step = b.step → q.id = b := by
  intro P
  induction P with
  | nil => intro _ _ _ b hb; cases hb
  | cons c P ih =>
    intro g hd hv b hb q hq hqs
    change (pinSeq (g.filterAll [c]) P).isValid = true at hv
    change q ∈ (pinSeq (g.filterAll [c]) P).alive at hq
    rcases List.mem_cons.mp hb with rfl | hb'
    · have hsub := (shrinks_pinSeq P (g.filterAll [b])).1
      exact pinned_filterAll_list hd [b] (isValid_of_sub hsub hv) b (List.mem_singleton_self b) q
        (hsub.alive q hq) hqs
    · exact ih (g.filterAll [c]) (aliveDocs_filterAll hd [c]) hv b hb' q hq hqs

/-- **Un pin válido y cerrado es una estructura cerrada de todo estado por encima**, que concuerda con los pins. -/
theorem sec_of_pinSeq {h x : GPathB} {P : List NodeId} (hsub : Sub h x) (hnd : NodupIds x) (hd : AliveDocs h)
    (hv : (pinSeq h P).isValid = true) (hcl : ClosedState (pinSeq h P)) :
    SecStruct x (fun y => y ∈ (pinSeq h P).alive)
      (fun y w => y ∈ (pinSeq h P).alive ∧ w ∈ (pinSeq h P).alive ∧ (pinSeq h P).Adj y w) ∧
    ∀ b ∈ P, SecAgrees (fun y => y ∈ (pinSeq h P).alive) b :=
  ⟨secStruct_of_sub ((shrinks_pinSeq P h).1.trans hsub) hnd hcl,
   fun b hb _ hy hys => pinned_pinSeq P h hd hv b hb _ hy hys⟩

/-- **Una estructura cerrada que concuerda con los pins sobrevive a ellos.** -/
theorem sec_pinSeq : ∀ (P : List NodeId) {x : GPathB}, SecStruct x V R → (∀ b ∈ P, SecAgrees V b) →
    SecStruct (pinSeq x P) V R := by
  intro P
  induction P with
  | nil => intro x h _; exact h
  | cons b P ih =>
    intro x h ha
    refine ih (secStruct_filterAll_list h [b] (fun c hc => ?_)) (fun c hc => ha c (List.mem_cons_of_mem _ hc))
    rw [List.mem_singleton] at hc
    subst hc
    exact ha c (by simp)

/-- Un estado válido con paso positivo tiene un vivo en el paso 0. -/
theorem alive_zero_of_valid {g : GPathB} (hv : g.isValid = true) (hpos : 0 < g.current_step) :
    ∃ y ∈ g.alive, y.id.step = 0 := by
  unfold isValid at hv
  have := List.all_eq_true.mp hv 0 (mem_intRange (Int.le_refl 0) (by omega))
  obtain ⟨y, hy, hys⟩ := List.any_eq_true.mp this
  exact ⟨y, hy, by simpa using hys⟩

/-- Sin pasos, cualquier selección es una camarilla (vacía). -/
theorem carried_of_nonpos {g : GPathB} (h : ¬ 0 < g.current_step) (S : Int → PathNodeId) : Carried g S :=
  ⟨fun _ _ _ => by omega, fun _ _ _ => by omega, fun _ _ _ _ _ _ => by omega, fun h' => absurd h' h,
   fun _ _ _ => by omega⟩

/-- **Bajar `SeqExact`** a un estado por debajo, `h`, que fija además `Q` y conserva las camarillas que concuerdan
con `Q`. -/
theorem seqExact_down {h x : GPathB} (Q : List NodeId) (hsub : Sub h x) (hnd : NodupIds x) (hd : AliveDocs h)
    (hq : h.isValid = true → ∀ b ∈ Q, ∀ q ∈ h.alive, q.id.step = b.step → q.id = b)
    (hcl : PinsClosed h) (hkeep : ∀ S, Carried x S → (∀ r ∈ Q, Agrees x.current_step S r) → Carried h S)
    (hse : SeqExact x) : SeqExact h := by
  intro P hv
  by_cases hpos : 0 < h.current_step
  · have hsp := (shrinks_pinSeq P h).1
    have hvh : h.isValid = true := isValid_of_sub hsp hv
    obtain ⟨hst, ha⟩ := sec_of_pinSeq hsub hnd hd hv (hcl P hv)
    obtain ⟨y, hy, _⟩ := alive_zero_of_valid hv (by rw [step_pinSeq]; exact hpos)
    have hx := sec_pinSeq (Q ++ P) hst (by
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact fun hy' hys => hq hvh b hb _ (hsp.alive _ hy') hys
      · exact ha b hb)
    obtain ⟨S, hS, hag⟩ := hse (Q ++ P) (isValid_of_sec hx hy)
    refine ⟨S, hkeep S hS (fun r hr => hag r (List.mem_append_left _ hr)), ?_⟩
    rw [hsub.step]
    exact fun r hr => hag r (List.mem_append_right _ hr)
  · refine ⟨fun _ => ⟨⟨0, 0⟩, none, none⟩, carried_of_nonpos hpos _, fun r _ h0 h1 => ?_⟩
    omega

-- ============================================================
-- El review y el filtro
-- ============================================================

/-- **El review conserva `SeqExact`.** -/
theorem seqExact_review {x : GPathB} (hnd : NodupIds x) (hd : AliveDocs x) (hcl : PinsClosed x.review)
    (hse : SeqExact x) : SeqExact x.review :=
  seqExact_down [] (shrinks_review x).1 hnd (aliveDocs_review hd) (fun _ _ hb => by cases hb) hcl
    (fun _ hS _ => carried_review hS) hse

/-- **El filtro por requisitos conserva `SeqExact`.** -/
theorem seqExact_filterAll {x : GPathB} (Q : List NodeId) (hnd : NodupIds x) (hd : AliveDocs x)
    (hcl : PinsClosed (x.filterAll Q)) (hse : SeqExact x) : SeqExact (x.filterAll Q) :=
  seqExact_down Q (shrinks_filterAll x Q).1 hnd (aliveDocs_filterAll hd Q)
    (fun hv => pinned_filterAll_list hd Q hv) hcl (fun _ hS ha => carried_filterAll hS Q ha) hse

-- ============================================================
-- La fila nueva
-- ============================================================

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **La fila nueva, sin ventana saltada, conserva `SeqExact`.** -/
theorem seqExact_addNode (hse : SeqExact g) (hdocs : AliveDocs g) (hb : Below g) (hls : LinksStep g)
    (hpos : 0 < g.current_step) (hskip : g.skipsWindow d forb = false) (hd : d.step = g.current_step)
    (hnd' : NodupIds (g.addNode d title forb)) (hdocs' : AliveDocs (g.addNode d title forb))
    (hcl : PinsClosed (g.addNode d title forb)) : SeqExact (g.addNode d title forb) := by
  intro P hv
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  obtain ⟨hst, ha⟩ := sec_of_pinSeq (Sub.refl _) hnd' hdocs' hv (hcl P hv)
  have hdown := secStruct_addNode_down (title := title) (forb := forb) hdocs hb hls hd hst
  -- un vivo del pin en el paso 0, que es viejo
  obtain ⟨y, hy, hy0⟩ := alive_zero_of_valid hv (by rw [step_pinSeq, hcs]; omega)
  have hyo : y.id.step < g.current_step := by omega
  -- el pin baja: la estructura restringida concuerda con P y deja válido el pin en g
  have hx := sec_pinSeq P hdown (fun b hb' _ hq hqs => ha b hb' hq.1 hqs)
  obtain ⟨S, hS, hag⟩ := hse P (isValid_of_sec hx (y := y) ⟨hy, hyo⟩)
  -- lo que P fija en el paso nuevo es d: la estructura tiene un nodo allí, de la fila
  have hP : ∀ r ∈ P, r.step = g.current_step → r = d := by
    intro r hr hrs
    obtain ⟨q, hqs, hyq, _⟩ := hst.pair (hst.refl hy) g.current_step (by omega) (by rw [hcs]; omega)
    have hqV := (hst.dom hyq).2
    have hqd : q.id = d := by
      rcases alive_addNode_cases (title := title) hdocs hb hd (hst.alive hqV) with ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · exact Machine.mapId_of_mem_shiftRowIds (List.mem_filter.mp h).1
    rw [← hqd]
    exact (ha r hr hqV (by rw [hqs, hrs])).symm
  -- la camarilla se alarga con el hijo de su cima
  obtain ⟨hn, hp⟩ := son_in_row (d := d) (forb := forb) hpos hskip (top_newParents hS hpos)
  obtain ⟨hc', hag', _, _⟩ := extend_through (title := title) hS hpos hb hd hag hP hn hp
  exact ⟨_, hc', hag'⟩

end GPathB

end AbsSatBingo.Model
