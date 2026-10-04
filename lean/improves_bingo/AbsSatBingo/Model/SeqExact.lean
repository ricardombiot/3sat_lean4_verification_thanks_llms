-- lean/improves_bingo/AbsSatBingo/Model/SeqExact.lean
import AbsSatBingo.Model.PinKeeps
import AbsSatBingo.Model.Decode

/-!
# La hipótesis del lector, llevada al estado de partida (`SeqExact`)

`PinKeeps.lean` dejó la completitud del lector en `MapExact` sobre **cada estado que visita**. Aquí se lleva esa
hipótesis a **un solo estado**, el de partida, y en su versión de existencia:

* los estados del lector son **pins sucesivos** del de partida (`visited_pinSeq`);
* una camarilla del de partida que concuerda con los pins sobrevive a todos ellos (`carried_pinSeq`);
* **`SeqExact g`**: si fijar sucesivamente `P` deja `g` válido, alguna camarilla de `g` concuerda con `P`. Es la
  exactitud del review en su versión de existencia (no pide cada arista, como `KernelExact`), para pins sucesivos.

Resultado: **`readerVerdict_iff_of_seqExact`**: el veredicto del lector es la satisfacibilidad si los arranques del
lector (el review entero de cada estado de la línea final) cumplen `SeqExact`. Todo lo que queda es de la máquina.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

open Driver

/-- Fijar sucesivamente los nodos de mapa de `P`, cada uno con su review (como el lector). -/
def pinSeq (g : GPathB) (P : List NodeId) : GPathB := P.foldl (fun h b => h.filterAll [b]) g

/-- **La exactitud de existencia para pins sucesivos**: si fijar `P` deja `g` válido, alguna camarilla de `g`
concuerda con `P`. -/
def SeqExact (g : GPathB) : Prop :=
  ∀ P : List NodeId, (pinSeq g P).isValid = true → ∃ S, Carried g S ∧ ∀ r ∈ P, Agrees g.current_step S r

theorem pinSeq_append (g : GPathB) (P : List NodeId) (b : NodeId) :
    pinSeq g (P ++ [b]) = (pinSeq g P).filterAll [b] := by
  simp [pinSeq, List.foldl_append]

theorem step_pinSeq : ∀ (P : List NodeId) (g : GPathB), (pinSeq g P).current_step = g.current_step := by
  intro P
  induction P with
  | nil => intro g; rfl
  | cons b P ih =>
    intro g
    show (pinSeq (g.filterAll [b]) P).current_step = g.current_step
    rw [ih]
    exact (shrinks_filterAll g [b]).1.step

/-- **Una camarilla que concuerda con los pins sobrevive a todos.** -/
theorem carried_pinSeq {S : Int → PathNodeId} :
    ∀ (P : List NodeId) (g : GPathB), Carried g S → (∀ r ∈ P, Agrees g.current_step S r) → Carried (pinSeq g P) S := by
  intro P
  induction P with
  | nil => intro g hc _; exact hc
  | cons b P ih =>
    intro g hc ha
    show Carried (pinSeq (g.filterAll [b]) P) S
    have hs := (shrinks_filterAll g [b]).1.step
    refine ih _ (carried_filterAll hc [b] (fun r hr => ha r (by rw [List.mem_singleton] at hr; simp [hr]))) ?_
    intro r hr
    rw [hs]
    exact ha r (List.mem_cons_of_mem _ hr)

/-- **Los estados del lector son pins sucesivos del de partida.** -/
theorem visited_pinSeq {g₀ h : GPathB} (hv : Visited g₀ h) : ∃ P, h = pinSeq (reviewAll g₀) P := by
  induction hv with
  | start => exact ⟨[], rfl⟩
  | pin q _ ih =>
    obtain ⟨P, rfl⟩ := ih
    exact ⟨P ++ [q.id], (pinSeq_append _ P q.id).symm⟩

/-- **Bajo `SeqExact` del arranque, ningún estado del lector es un zombi.** -/
theorem noZombie_visited_of_seqExact {g₀ : GPathB} (hse : SeqExact (reviewAll g₀)) :
    ∀ h, Visited g₀ h → NoZombie h := by
  intro h hvis hv
  obtain ⟨P, rfl⟩ := visited_pinSeq hvis
  obtain ⟨S, hS, ha⟩ := hse P hv
  exact ⟨S, carried_pinSeq P _ hS ha⟩

-- ============================================================
-- El recíproco: SeqExact es exactamente «ningún zombi en el lector»
-- ============================================================

theorem shrinks_pinSeq : ∀ (P : List NodeId) (g : GPathB), Shrinks (pinSeq g P) g := by
  intro P
  induction P with
  | nil => intro g; exact Shrinks.refl g
  | cons b P ih => intro g; exact (ih (g.filterAll [b])).trans (shrinks_filterAll g [b])

/-- Todo pin sucesivo de un estado visitado es visitado (el lector puede fijar cualquier nodo de mapa). -/
theorem visited_of_pinSeq {g₀ : GPathB} : ∀ (P : List NodeId) (h : GPathB), Visited g₀ h → Visited g₀ (pinSeq h P) := by
  intro P
  induction P with
  | nil => intro h hv; exact hv
  | cons b P ih => intro h hv; exact ih _ (Visited.pin ⟨b, none, none⟩ hv)

/-- **Una camarilla de un pin sucesivo concuerda con los pins.** -/
theorem agrees_of_pinSeq {S : Int → PathNodeId} :
    ∀ (P : List NodeId) (g : GPathB), AliveDocs g → Carried (pinSeq g P) S → ∀ r ∈ P, Agrees g.current_step S r := by
  intro P
  induction P with
  | nil => intro _ _ _ r hr; cases hr
  | cons b P ih =>
    intro g hd hc r hr
    have hs := (shrinks_filterAll g [b]).1.step
    rcases List.mem_cons.mp hr with rfl | hr'
    · intro h0 h1
      have hsub := (shrinks_pinSeq P (g.filterAll [r])).1
      have hcs : r.step < (pinSeq (g.filterAll [r]) P).current_step := by
        rw [hsub.step, hs]; exact h1
      have hv : (g.filterAll [r]).isValid = true := isValid_of_sub hsub (isValid_of_carried hc)
      exact pinned_filterAll_list hd [r] hv r (List.mem_singleton_self r) (S r.step)
        (hsub.alive _ (hc.alive _ h0 hcs)) (hc.step _ h0 hcs)
    · have := ih (g.filterAll [b]) (aliveDocs_filterAll hd [b]) hc r hr'
      rw [hs] at this
      exact this

/-- **`SeqExact` del arranque ⇔ ningún estado que visita el lector es un zombi.** -/
theorem seqExact_iff_noZombie_visited {g₀ : GPathB} (hd : AliveDocs (reviewAll g₀)) (hnd : NodupIds (reviewAll g₀)) :
    SeqExact (reviewAll g₀) ↔ ∀ h, Visited g₀ h → NoZombie h := by
  refine ⟨noZombie_visited_of_seqExact, fun hnz P hv => ?_⟩
  obtain ⟨S, hS⟩ := hnz _ (visited_of_pinSeq P _ Visited.start) hv
  exact ⟨S, carried_of_sub (shrinks_pinSeq P _).1 hnd hS, agrees_of_pinSeq P _ hd hS⟩

/-- Y por tanto `PinKeeps` en todos ellos. -/
theorem pinKeeps_visited_of_seqExact {g₀ : GPathB} (hse : SeqExact (reviewAll g₀)) :
    ∀ h, Visited g₀ h → PinKeeps h := by
  intro h hvis _ q _ hv
  exact noZombie_visited_of_seqExact hse _ (Visited.pin q hvis) hv

end GPathB

namespace Machine

open GPathB Driver

/-- **El veredicto del lector es la satisfacibilidad bajo `SeqExact` en los arranques del lector.** -/
theorem readerVerdict_iff_of_seqExact {φ : Cnf} (hbd : Bounded φ)
    (H : ∀ kv ∈ run φ, SeqExact (reviewAll kv.2)) : readerVerdict φ = true ↔ Satisfiable φ :=
  Decode.readerVerdict_iff_of_noZombie hbd (fun kv hkv => noZombie_visited_of_seqExact (H kv hkv))

/-- **`PinFree` ⟹ `SeqExact`** en los arranques del lector: `SeqExact` queda por debajo de la hipótesis del teorema
principal. -/
theorem seqExact_of_hypsPin {φ : Cnf} (H : HypsPin φ) : ∀ kv ∈ run φ, SeqExact (reviewAll kv.2) := by
  intro kv hkv
  have hpos := stepCount_pos φ
  have hinv := lineInv_steps H (stepCount φ - 1).toNat
  have hrun : run φ = steps φ (stepCount φ - 1).toNat (init φ) := rfl
  rw [← hrun, show ((stepCount φ - 1).toNat : Int) + 1 = stepCount φ by rw [Int.toNat_of_nonneg (by omega)]; omega]
    at hinv
  obtain ⟨hl, hent, _, _⟩ := hinv
  obtain ⟨⟨hbk, _⟩, _⟩ := hent kv hkv
  have hd : AliveDocs (reviewAll kv.2) := aliveDocs_review (aliveDocs_dirty (hl kv hkv).docs _)
  have hnd : NodupIds (reviewAll kv.2) :=
    revPrims_filterAll revPrims_nodupIds _ [] (revPrims_nodupIds.dirty _ _ hbk.1)
  exact (seqExact_iff_noZombie_visited hd hnd).mpr (noZombie_visited_of_hypsPin H kv hkv)

end Machine

end AbsSatBingo.Model
