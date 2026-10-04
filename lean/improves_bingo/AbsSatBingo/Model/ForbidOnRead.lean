-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnRead.lean
import AbsSatBingo.Model.ForbidOnHelly

/-!
# El lector no se atasca

Los veredictos de `ForbidOnHelly` dicen que la máquina **decide**. Aquí se lee la solución: sobre un estado final, el
lector fija el color (el nodo del mapa) de un nodo vivo y revisa, una elección tras otra.

* **`RInv φ T P g`**: lo que el lector necesita de un estado: es válido, sus parejas de vecinos y sus triángulos sin
  prohibir son de ramas de `P` (`Snd3`), y lleva la rama de toda asignación de `P`.
* **`read_step`**: fijar el color de **cualquier** nodo vivo `q` y revisar deja un estado que cumple `RInv` para las
  asignaciones de `P` que eligen ese color. La validez no pide nada: `q` está en la rama de una asignación de `P`, y
  esa rama sobrevive entera. Que el invariante siga pide `PhantomFree` para ese color.
* **`Reading g R g'`**: `g'` sale de `g` fijando, en orden, los colores `R`, cada uno de un nodo vivo en su momento.
* **`reading_inv`**: toda lectura conserva `RInv`. **`reader_on`**: en la máquina, cualquier lectura de un estado
  final deja un estado válido que lleva la rama de una asignación que satisface `φ` y coincide con todas las
  elecciones. El lector no retrocede.

La hipótesis de la lectura (`HRead`) es, como `PhantomAt`, una propiedad de las soluciones de `φ`: sin familias
fantasma al fijar un color más, sea cual sea la lista de colores ya fijados (de pasos del estado). La mayoría la da (`hRead_of_maj`), así
que en las fórmulas con forma 2-CNF el lector no se atasca **sin hipótesis** (`reader_on_twoLike`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

/-- **Una rama sin ventanas prohibidas es la de una asignación que satisface la fórmula.** -/
theorem sat_of_validUpTo {φ : Cnf} {a : Assign} (h : ValidUpTo φ a (stepCount φ)) : Sat a φ := by
  intro c hc
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
  have hjlt : j < φ.clauses.length := by
    by_cases hlt : j < φ.clauses.length
    · exact hlt
    · rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  unfold SatClause
  cases h1 : litVal a c.l1
  · cases h2 : litVal a c.l2
    · cases h3 : litVal a c.l3
      · exfalso
        have := prohibited_of_false hj h1 h2 h3
        rw [h (clauseStep φ j 2) (by simp only [clauseStep, stepCount]; omega)] at this
        cases this
      · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

namespace GPathB

open Driver Machine MachineOn

variable {φ : Cnf}

/-- **Lo que el lector necesita de un estado.** -/
structure RInv (φ : Cnf) (T : Int) (P : Assign → Prop) (g : GPathB) : Prop where
  inv   : SInvB g
  ns    : NoSelf g
  ndt   : NoDegT g
  step  : g.current_step = T
  valid : g.isValid = true
  snd   : Snd3 φ P g
  comp  : ∀ a, P a → CT g (pidOfAssign φ a)

theorem rInv_congr {T : Int} {P Q : Assign → Prop} {g : GPathB} (h : RInv φ T P g) (hpq : ∀ a, P a ↔ Q a) :
    RInv φ T Q g :=
  ⟨h.inv, h.ns, h.ndt, h.step, h.valid, snd3_mono h.snd (fun a => (hpq a).mp), fun a ha => h.comp a ((hpq a).mpr ha)⟩

/-- **Una elección del lector.** Fijar el color de un nodo vivo y revisar: el estado sigue válido (la rama de una
asignación que pasa por el nodo sobrevive), y bajo `PhantomFree` para ese color el invariante sigue. -/
theorem read_step {T : Int} {P : Assign → Prop} {g : GPathB} (h : RInv φ T P g) {q : PathNodeId}
    (hq : q ∈ g.alive) (hq1 : 1 ≤ q.id.step)
    (hH : PhantomFree φ P (fun a => P a ∧ selOfAssign φ a q.id.step = q.id) T q.id.step) :
    RInv φ T (fun a => P a ∧ selOfAssign φ a q.id.step = q.id) (g.filterAllOn [q.id]) := by
  have hqT : q.id.step < T := by rw [← h.step]; exact alive_below h.inv.docs h.inv.below hq
  obtain ⟨a, hPa, hpa, _⟩ := h.snd.1 q q (adj_refl _ _ hq)
  have hsel : selOfAssign φ a q.id.step = q.id := by
    have := congrArg PathNodeId.id hpa
    rw [pid_id] at this; exact this
  have one : ∀ {b : Assign}, selOfAssign φ b q.id.step = q.id → ∀ r ∈ [q.id], selOfAssign φ b r.step = r := by
    intro b hb r hr; rw [List.mem_singleton] at hr; subst hr; exact hb
  have hvY : (g.filterAllOn [q.id]).isValid = true :=
    isValid_of_carried (comp_filter h.comp a ⟨hPa, one hsel⟩).1
  refine ⟨sInvB_filterAllOn h.inv _, noSelf_filterAllOn h.ns _, noDegT_filterAllOn h.ns h.ndt _,
    (step_filterAllOn g _).trans h.step, hvY, ?_, fun b hb => comp_filter h.comp b ⟨hb.1, one hb.2⟩⟩
  refine snd3_mono (snd3_filter h.inv h.ns h.ndt h.step h.valid (by simp) (fun r hr => ?_) (fun r hr => ?_) h.snd
    h.comp hvY) (fun b hb => ⟨hb.1, hb.2 _ (List.mem_singleton_self _)⟩)
  · rw [List.mem_singleton] at hr; subst hr; exact ⟨hq1, hqT⟩
  · rw [List.mem_singleton] at hr; subst hr; exact hH

/-- **Una lectura**: `g'` sale de `g` fijando en orden los colores de la lista, cada uno el de un nodo vivo (por
encima de la raíz) del estado de ese momento, y revisando tras cada uno. -/
inductive Reading : GPathB → List NodeId → GPathB → Prop
  | nil (g : GPathB) : Reading g [] g
  | cons {g g' : GPathB} {q : PathNodeId} {rs : List NodeId} : q ∈ g.alive → 1 ≤ q.id.step →
      Reading (g.filterAllOn [q.id]) rs g' → Reading g (q.id :: rs) g'

/-- Las asignaciones de `P` que eligen todos los colores de la lista. -/
def Pinned (φ : Cnf) (P : Assign → Prop) (R : List NodeId) (a : Assign) : Prop :=
  P a ∧ ∀ r ∈ R, selOfAssign φ a r.step = r

/-- **La hipótesis de la lectura**: sin familias fantasma al fijar un color más, tras cualquier lista de colores. -/
def HRead (φ : Cnf) (T : Int) (P : Assign → Prop) : Prop :=
  ∀ (R : List NodeId) (r : NodeId), (∀ x ∈ R, 1 ≤ x.step ∧ x.step < T) → 1 ≤ r.step → r.step < T →
    PhantomFree φ (Pinned φ P R) (fun a => Pinned φ P R a ∧ selOfAssign φ a r.step = r) T r.step

/-- **Toda lectura conserva el invariante**, con las asignaciones que eligen los colores leídos. -/
theorem reading_inv {T : Int} {P : Assign → Prop} (hH : HRead φ T P) {g g' : GPathB} {R : List NodeId}
    (hr : Reading g R g') : ∀ R0, (∀ x ∈ R0, 1 ≤ x.step ∧ x.step < T) → RInv φ T (Pinned φ P R0) g →
      RInv φ T (Pinned φ P (R0 ++ R)) g' := by
  induction hr with
  | nil g => intro R0 _ h; rw [List.append_nil]; exact h
  | @cons g g' q rs hq hq1 _ ih =>
    intro R0 hR0 h
    have hqT : q.id.step < T := by rw [← h.step]; exact alive_below h.inv.docs h.inv.below hq
    have h1 := read_step h hq hq1 (hH R0 q.id hR0 hq1 hqT)
    have h2 : RInv φ T (Pinned φ P (R0 ++ [q.id])) (g.filterAllOn [q.id]) := by
      refine rInv_congr h1 (fun a => ⟨fun ha => ⟨ha.1.1, fun r hr => ?_⟩, fun ha => ⟨⟨ha.1, fun r hr => ?_⟩, ?_⟩⟩)
      · rcases List.mem_append.mp hr with h' | h'
        · exact ha.1.2 r h'
        · rw [List.mem_singleton] at h'; subst h'; exact ha.2
      · exact ha.2 r (List.mem_append_left _ hr)
      · exact ha.2 q.id (List.mem_append_right _ (List.mem_singleton_self _))
    have := ih (R0 ++ [q.id]) (fun x hx => by
      rcases List.mem_append.mp hx with h' | h'
      · exact hR0 x h'
      · rw [List.mem_singleton] at h'; subst h'; exact ⟨hq1, hqT⟩) h2
    rw [List.append_assoc] at this
    exact this

/-- **La mayoría da la hipótesis de la lectura.** -/
theorem hRead_of_maj {T : Int} {P : Assign → Prop} (hP : ∀ a b c, P a → P b → P c → P (maj3 a b c)) :
    HRead φ T P := by
  intro R r _ hr1 hrT
  refine phantomFree_of_helly4 (by omega) hrT (helly4_of_maj (fun a b c ha hb hc => ?_))
  exact ⟨⟨hP _ _ _ ha.1.1 hb.1.1 hc.1.1, fun x hx => by
      rw [sel_maj_ab ((ha.1.2 x hx).trans (hb.1.2 x hx).symm)]; exact ha.1.2 x hx⟩,
    by rw [sel_maj_ab (ha.2.trans hb.2.symm)]; exact ha.2⟩

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {φ : Cnf}

/-- **El lector no se atasca.** En la máquina `:on`, sin familias fantasma en sus líneas (`PhantomAt`) ni en la
lectura (`HRead`), cualquier lectura de un estado final —cualquier sucesión de elecciones de nodos vivos, revisando
tras cada una— deja un estado válido que lleva la rama de una asignación que satisface `φ` y coincide con todas las
elecciones. -/
theorem reader_on (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAt φ T)
    (HR : ∀ k, HRead φ (stepCount φ) (SolE φ (stepCount φ) k)) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) := by
  have hpos := stepCount_pos φ
  have hn : (((stepCount φ - 1).toNat : Nat) : Int) + 1 = stepCount φ := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  have hl := lInvS3_steps hbd (stepCount φ - 1).toNat (fun T h1 _ => HA T h1)
  have hcomp := compLine_steps hbd (lInvS_of_s3 hl)
  rw [hn] at hl hcomp
  have hkv' : kv ∈ stepsM .on φ (stepCount φ - 1).toNat (initM .on φ) := hkv
  have hent := hl.on kv hkv'
  have h0 : RInv φ (stepCount φ) (Pinned φ (SolE φ (stepCount φ) kv.1) []) kv.2 :=
    rInv_congr (P := SolE φ (stepCount φ) kv.1)
      ⟨hl.inv kv hkv', hent.2.1, hl.ndt kv hkv', hent.1.step, hent.1.valid, hl.snd kv hkv', hcomp kv hkv'⟩
      (fun a => ⟨fun ha => ⟨ha, fun r hr => absurd hr List.not_mem_nil⟩, fun ha => ha.1⟩)
  have hfin := reading_inv (HR kv.1) hr [] (fun x hx => absurd hx List.not_mem_nil) h0
  rw [List.nil_append] at hfin
  refine ⟨hfin.valid, ?_⟩
  obtain ⟨q, hq, _⟩ := exists_alive_at hfin.valid (k := 0) (Int.le_refl 0) (by rw [hfin.step]; exact hpos)
  obtain ⟨a, ha, _, _⟩ := hfin.snd.1 q q (adj_refl _ _ hq)
  exact ⟨a, sat_of_validUpTo ha.1.1, ha.2, hfin.comp a ha⟩

/-- **El lector no se atasca en las fórmulas con forma 2-CNF**, sin hipótesis: cualquier lectura de un estado final
de la máquina `:on` deja un estado válido con la rama de una asignación que satisface `φ` y coincide con todas las
elecciones. -/
theorem reader_on_twoLike (hbd : Bounded φ) (h2 : TwoLike φ) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_on hbd (fun T hT => phantomAt_of_hellyAt hbd hT (hellyAt_of_majClosed (majClosed_twoLike h2) T))
    (fun k => hRead_of_maj (fun a b c ha hb hc =>
      ⟨majClosed_twoLike h2 _ a b c ha.1 hb.1 hc.1, by rw [sel_maj_ab (ha.2.trans hb.2.symm)]; exact ha.2⟩))
    hkv hr

end MachineOn

end AbsSatBingo.Model
