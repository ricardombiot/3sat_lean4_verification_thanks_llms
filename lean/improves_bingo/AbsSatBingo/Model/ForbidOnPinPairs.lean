-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnPinPairs.lean
import AbsSatBingo.Model.ForbidOnEdge

/-!
# El lector sin atasco por parejas con varios colores fijados

`ForbidOnEdge` reduce el lector a `HReadE` (fijar un color conserva `TriId`). Pero `TriId` en un estado es «aristas
exactas tras fijar un color más», así que pedir `HReadE` paso a paso es pedir aristas exactas en todos los estados de
lectura, y la inducción gira en redondo. La formulación sin círculo mira todos los colores de una vez:

* **`PinPairs φ P0 N`**: toda estructura cerrada (`PhStruct`: sus parejas y triángulos son de ramas de `P0`) cuyos
  nodos en los pasos de los colores fijados `Rp` son de esos colores tiene sus parejas en ramas de `P0` que eligen
  **todos** los colores de `Rp`. Es una condición de parejas con varias anclas, y sus hipótesis solo piden objetos
  exactos de `P0` (los da la exactitud del estado final).
* **`RInvP`**: el invariante de un estado leído: aristas exactas para las soluciones que eligen los colores leídos,
  completitud, nodos de los pasos leídos de su color, y aristas y tríos dentro de los del estado final.
* **`read_stepP`**, **`reading_invP`**: con `PinPairs`, cualquier elección conserva `RInvP`.
* **`reader_on_pinPairs`**: con las líneas (`PhantomAtW`) y `PinPairs` para las soluciones, el lector no se atasca y
  acaba en una solución que coincide con todas las elecciones.

Medido en `chain5_cross` (`probe_hard5_ne.jl`): en 262 estados leídos, 0 aristas fuera de camarilla, aunque haya
triángulos fantasma.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

namespace GPathB

open Driver Machine MachineOn

/-- **`PinPairs φ P0 N`**: sin parejas fantasma con varios colores fijados. -/
def PinPairs (φ : Cnf) (P0 : Assign → Prop) (N : Int) : Prop :=
  ∀ (Rp : List NodeId) (R : PathNodeId → PathNodeId → Prop) (Tf : Trios), PhStruct φ P0 N R Tf →
    (∀ r ∈ Rp, ∀ s, R s s → s.id.step = r.step → s.id = r) →
    ∀ y w, R y w → ∃ a, Pinned φ P0 Rp a ∧ pidOfAssign φ a y.id.step = y ∧ pidOfAssign φ a w.id.step = w

/-- **El invariante de un estado leído**, respecto del estado final `g0`. -/
structure RInvP (φ : Cnf) (T : Int) (P0 : Assign → Prop) (g0 : GPathB) (R : List NodeId) (g : GPathB) : Prop where
  inv   : SInvB g
  ns    : NoSelf g
  ndt   : NoDegT g
  step  : g.current_step = T
  valid : g.isValid = true
  snd   : Snd φ (Pinned φ P0 R) g
  comp  : ∀ a, Pinned φ P0 R a → CT g (pidOfAssign φ a)
  pins  : ∀ r ∈ R, ∀ s ∈ g.alive, s.id.step = r.step → s.id = r
  adj0  : ∀ x y, g.Adj x y → g0.Adj x y
  tf0   : ∀ x u w, g.Adj x u → TF g0 x u w → TF g x u w

/-- **Una elección del lector conserva el invariante**, con `PinPairs`. -/
theorem read_stepP {T : Int} {P0 : Assign → Prop} {g0 : GPathB} (hg0 : Snd3 φ P0 g0) (hPP : PinPairs φ P0 T)
    {R : List NodeId} {g : GPathB} (h : RInvP φ T P0 g0 R g) {q : PathNodeId} (hq : q ∈ g.alive)
    (hq1 : 1 ≤ q.id.step) : RInvP φ T P0 g0 (R ++ [q.id]) (g.filterAllOn [q.id]) := by
  have hqT : q.id.step < T := by rw [← h.step]; exact alive_below h.inv.docs h.inv.below hq
  obtain ⟨a, hPa, hpa, _⟩ := h.snd q q (adj_refl _ _ hq)
  have hsel : selOfAssign φ a q.id.step = q.id := by
    have := congrArg PathNodeId.id hpa
    rw [pid_id] at this; exact this
  have one : ∀ {b : Assign}, selOfAssign φ b q.id.step = q.id → ∀ r ∈ [q.id], selOfAssign φ b r.step = r := by
    intro b hb r hr; rw [List.mem_singleton] at hr; subst hr; exact hb
  have hvY : (g.filterAllOn [q.id]).isValid = true :=
    isValid_of_carried (comp_filter h.comp a ⟨hPa, one hsel⟩).1
  have hsh := (shrinks_filterAllOn g [q.id]).1
  have hpq : ∀ b, (Pinned φ P0 R b ∧ selOfAssign φ b q.id.step = q.id) ↔ Pinned φ P0 (R ++ [q.id]) b := by
    intro b
    refine ⟨fun hb => ⟨hb.1.1, fun r hr => ?_⟩, fun hb => ⟨⟨hb.1, fun r hr => hb.2 r (List.mem_append_left _ hr)⟩,
      hb.2 q.id (List.mem_append_right _ (List.mem_singleton_self _))⟩⟩
    rcases List.mem_append.mp hr with h' | h'
    · exact hb.1.2 r h'
    · rw [List.mem_singleton] at h'; subst h'; exact hb.2
  have adj' : ∀ x y, (g.filterAllOn [q.id]).Adj x y → g0.Adj x y := fun x y hxy => h.adj0 x y (hsh.adj _ _ hxy)
  have tf' : ∀ x u w, (g.filterAllOn [q.id]).Adj x u → TF g0 x u w → TF (g.filterAllOn [q.id]) x u w :=
    fun x u w hxu hf => tF_mono (trios_grow_filterAllOn g [q.id]) hxu (h.tf0 x u w (hsh.adj _ _ hxu) hf)
  have pinsOld : ∀ r ∈ R, ∀ s ∈ (g.filterAllOn [q.id]).alive, s.id.step = r.step → s.id = r :=
    fun r hr s hs hss => h.pins r hr s (hsh.alive s hs) hss
  -- las aristas, y el color nuevo en su paso
  have key : Snd φ (Pinned φ P0 (R ++ [q.id])) (g.filterAllOn [q.id]) ∧
      ∀ s ∈ (g.filterAllOn [q.id]).alive, s.id.step = q.id.step → s.id = q.id := by
    cases hd : ([q.id].foldl filterRequire g).dirty
    · -- el filtro no mata a nadie: todo nodo del paso es del color, y toda rama lo elige
      have hd' : (g.filterRequire q.id).dirty = false := hd
      have colG : ∀ s ∈ g.alive, s.id.step = q.id.step → s.id = q.id := by
        intro s hs hss
        obtain ⟨n, hn, hnid⟩ := h.inv.docs _ hs
        have hline : n ∈ g.line q.id.step := by
          unfold line
          refine List.mem_filter.mpr ⟨hn, ?_⟩
          rw [hnid, hss]; simp
        have := filterRequire_noVictims h.valid hd' n hline
        rw [hnid] at this
        exact this
      have agr : ∀ b, Pinned φ P0 R b → selOfAssign φ b q.id.step = q.id := by
        intro b hb
        have hD := h.comp b hb
        have hal := hD.1.alive q.id.step (by omega) (by rw [h.step]; exact hqT)
        have := colG _ hal (by rw [pid_id, selOfAssign_step])
        rw [pid_id] at this; exact this
      refine ⟨fun x w hxw => ?_, fun s hs hss => colG s (hsh.alive s hs) hss⟩
      obtain ⟨b, hb, h1, h2⟩ := h.snd x w (hsh.adj _ _ hxw)
      exact ⟨b, (hpq b).mp ⟨hb, agr b hb⟩, h1, h2⟩
    · have e : g.filterAllOn [q.id] = g.pinOn [q.id] := by
        unfold filterAllOn pinOn
        congr 1
        generalize [q.id].foldl filterRequire g = F at hd
        cases F
        simp_all
      rw [e] at hvY ⊢
      rw [e] at pinsOld adj' tf'
      have hiY : SInvB (g.pinOn [q.id]) := sInvB_pinOn h.inv [q.id]
      have hcl : ClosedState (g.pinOn [q.id]) := closedState_pinOn h.inv hvY (by rw [h.step]; omega)
      have hf : FixClosed (g.pinOn [q.id]) :=
        fixClosed_reviewOn (g := { [q.id].foldl filterRequire g with dirty := true }) rfl hvY
      have hg := trioGood_low hf (noDegT_pinOn h.ns h.ndt [q.id]) (Int.le_refl _)
      have hlt : ∀ {p : PathNodeId}, p ∈ (g.pinOn [q.id]).alive → p.id.step < (g.pinOn [q.id]).current_step :=
        fun hp => alive_below hiY.docs hiY.below hp
      have hR : ∀ {y z : PathNodeId}, (g.pinOn [q.id]).Adj y z →
          LowR (g.pinOn [q.id]) (g.pinOn [q.id]).current_step y z := fun hh =>
        ⟨⟨(hiY.edges _ _ hh).1, (hiY.edges _ _ hh).2, hh⟩, hlt (hiY.edges _ _ hh).1, hlt (hiY.edges _ _ hh).2⟩
      have pinned := pinned_pinOn h.inv.docs hvY q.id (List.mem_singleton_self _)
      have b0 : ∀ {p : PathNodeId}, p ∈ (g.pinOn [q.id]).alive → 0 ≤ p.id.step ∧ p.id.step < T := by
        intro p hp
        obtain ⟨n, hn, rfl⟩ := hiY.docs p hp
        have h1 := hiY.below n hn
        rw [step_pinOn, h.step] at h1
        exact ⟨hiY.zero n hn, h1⟩
      have hcT : (g.pinOn [q.id]).current_step = T := by rw [step_pinOn, h.step]
      -- la estructura del estado fijado
      have hS : PhStruct φ P0 T (LowR (g.pinOn [q.id]) (g.pinOn [q.id]).current_step) (TF (g.pinOn [q.id])) :=
        ⟨fun y w hh => ⟨hR (adj_refl _ _ hh.1.1), hR (adj_refl _ _ hh.1.2.1)⟩,
          fun y w hh => hR ((adj_symm _ _ _).mp hh.1.2.2),
          fun a b r h1 h2 h3 hT => hg.swap23 h1 h2 h3 hT,
          fun a b r h1 h2 h3 hT => hg.swap12 h1 h2 h3 hT,
          fun y w hh => b0 hh.1.1,
          fun y w hh l l0 l1 => by
            by_cases ee : y = w
            · obtain ⟨s, hss, hys, hws⟩ := hcl.pair (y := y) (w := w) hh.1 l l0 (by rw [hcT]; exact l1)
              exact ⟨s, hss, hR hys.2.2, hR hws.2.2, Or.inl ee⟩
            · obtain ⟨s, hss, hys, hws, hor⟩ := hg.edge hh ee l l0 (by rw [hcT]; exact l1)
              exact ⟨s, hss, hys, hws, Or.inr hor⟩,
          fun x u w h1 h2 h3 n1 n2 n3 hn l l0 l1 => hg.trio h1 h2 h3 n1 n2 n3 hn l l0 (by rw [hcT]; exact l1),
          fun y w hh => hg0.1 y w (adj' y w hh.1.2.2),
          fun x u w h1 h2 h3 n1 n2 n3 hn => hg0.2 x u w (adj' _ _ h1.1.2.2) (adj' _ _ h2.1.2.2) (adj' _ _ h3.1.2.2)
            n1 n2 n3 (fun hf => hn (tf' x u w h1.1.2.2 hf))⟩
      have pinsAll : ∀ r ∈ R ++ [q.id], ∀ s, LowR (g.pinOn [q.id]) (g.pinOn [q.id]).current_step s s →
          s.id.step = r.step → s.id = r := by
        intro r hr s hs hss
        rcases List.mem_append.mp hr with h' | h'
        · exact pinsOld r h' s hs.1.1 hss
        · rw [List.mem_singleton] at h'; subst h'; exact pinned s hs.1.1 hss
      refine ⟨fun x w hxw => hPP (R ++ [q.id]) _ _ hS pinsAll x w (hR hxw), fun s hs hss => pinned s hs hss⟩
  refine ⟨sInvB_filterAllOn h.inv _, noSelf_filterAllOn h.ns _, noDegT_filterAllOn h.ns h.ndt _,
    (step_filterAllOn g _).trans h.step, hvY, key.1, fun b hb => comp_filter h.comp b ⟨((hpq b).mpr hb).1, one ((hpq b).mpr hb).2⟩,
    fun r hr s hs hss => ?_, adj', tf'⟩
  rcases List.mem_append.mp hr with h' | h'
  · exact pinsOld r h' s hs hss
  · rw [List.mem_singleton] at h'; subst h'; exact key.2 s hs hss

/-- **Toda lectura conserva el invariante.** -/
theorem reading_invP {T : Int} {P0 : Assign → Prop} {g0 : GPathB} (hg0 : Snd3 φ P0 g0) (hPP : PinPairs φ P0 T)
    {g g' : GPathB} {R : List NodeId} (hr : Reading g R g') :
    ∀ R0, RInvP φ T P0 g0 R0 g → RInvP φ T P0 g0 (R0 ++ R) g' := by
  induction hr with
  | nil g => intro R0 h; rw [List.append_nil]; exact h
  | @cons g g' q rs hq hq1 _ ih =>
    intro R0 h
    have := ih (R0 ++ [q.id]) (read_stepP hg0 hPP h hq hq1)
    rw [List.append_assoc] at this
    exact this

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **El lector no se atasca**, con las líneas (`PhantomAtW`) y `PinPairs` para las soluciones de cada estado final:
cualquier lectura deja un estado válido que lleva la rama de una asignación que satisface `φ` y coincide con todas
las elecciones. No pide la exactitud del lector. -/
theorem reader_on_pinPairs (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T)
    (HP : ∀ k, PinPairs φ (SolE φ (stepCount φ) k) (stepCount φ)) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) := by
  have hpos := stepCount_pos φ
  have hn : (((stepCount φ - 1).toNat : Nat) : Int) + 1 = stepCount φ := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  have hl := lInvS3_stepsW hbd (stepCount φ - 1).toNat (fun T h1 _ => HA T h1)
  have hcomp := compLine_steps hbd (lInvS_of_s3 hl)
  rw [hn] at hl hcomp
  have hkv' : kv ∈ stepsM .on φ (stepCount φ - 1).toNat (initM .on φ) := hkv
  have hent := hl.on kv hkv'
  have hs3 : Snd3 φ (SolE φ (stepCount φ) kv.1) kv.2 := hl.snd kv hkv'
  have h0 : RInvP φ (stepCount φ) (SolE φ (stepCount φ) kv.1) kv.2 [] kv.2 :=
    ⟨hl.inv kv hkv', hent.2.1, hl.ndt kv hkv', hent.1.step, hent.1.valid,
      snd_mono hs3.1 (fun a ha => ⟨ha, fun r hr => absurd hr List.not_mem_nil⟩),
      fun a ha => hcomp kv hkv' a ha.1, fun r hr => absurd hr List.not_mem_nil, fun _ _ h => h, fun _ _ _ _ h => h⟩
  have hfin := reading_invP hs3 (HP kv.1) hr [] h0
  rw [List.nil_append] at hfin
  refine ⟨hfin.valid, ?_⟩
  obtain ⟨q, hq, _⟩ := exists_alive_at hfin.valid (k := 0) (Int.le_refl 0) (by rw [hfin.step]; exact hpos)
  obtain ⟨a, ha, _, _⟩ := hfin.snd q q (adj_refl _ _ hq)
  exact ⟨a, sat_of_validUpTo ha.1.1, ha.2, hfin.comp a ha⟩

end MachineOn

end AbsSatBingo.Model
