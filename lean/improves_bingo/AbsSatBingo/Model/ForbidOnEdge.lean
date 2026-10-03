-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnEdge.lean
import AbsSatBingo.Model.ForbidOnPrefix

/-!
# El invariante de aristas exactas para el lector

En cinco bloques el lector no es exacto en triángulos (`probe_hard5_read.jl`: en `chain5_cross`, 36 triángulos de
estados leídos fuera de toda camarilla), pero no se atasca (`probe_read_full.jl`: 40 lecturas completas, 0
atascos, 40 soluciones) y sus estados leídos tienen todos los nodos y aristas en camarillas (`probe_hard5_ne.jl`).

La razón: el lector fija **nodos del mapa** (`NodeId`), no ventanas. Tras fijar el color `r`, una arista `(x, w)` que
sobrevive tiene en el paso de `r` un testigo `s` (con `s.id = r`), y basta una rama que pase por `x` y por `w` y
**elija** `r` en ese paso, sea cual sea su ventana. No hace falta que pase por `s`.

* **`TriId φ P g`** (triángulos exactos salvo la ventana de un nodo): todo triángulo sin prohibir `(x, u, w)` tiene una
  rama de `P` que pasa por `x` y `u` y elige `w.id` en el paso de `w`. Es más débil que la mitad de triángulos de
  `Snd3`.
* **`snd_pin_of_triId`**: aristas exactas (`Snd`) y `TriId` antes de fijar un color dan aristas exactas después.
* **`RInvE`**: el invariante del lector con `Snd` (aristas) en lugar de `Snd3`.
* **`HReadE`**: la hipótesis del lector para este invariante: fijar un color más conserva `TriId`.
* **`reader_on_edge`**: con las líneas (`PhantomAtW`) y `HReadE`, el lector no se atasca y acaba en una solución que
  coincide con todas las elecciones.

Lo abierto es `HReadE`: que `TriId` pase de un estado leído al siguiente.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

namespace GPathB

open Driver Machine MachineOn

/-- **`TriId φ P g`**: todo triángulo sin prohibir del estado tiene una rama de `P` que pasa por dos de sus nodos y
elige el color del tercero (con cualquier ventana). -/
def TriId (φ : Cnf) (P : Assign → Prop) (g : GPathB) : Prop :=
  ∀ x u w, g.Adj x u → g.Adj x w → g.Adj u w → x ≠ u → x ≠ w → u ≠ w → ¬ TF g x u w →
    ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧ selOfAssign φ a w.id.step = w.id

/-- Los triángulos exactos dan `TriId`. -/
theorem triId_of_snd3 {P : Assign → Prop} {g : GPathB} (h : Snd3 φ P g) : TriId φ P g := by
  intro x u w h1 h2 h3 n1 n2 n3 hn
  obtain ⟨a, ha, e1, e2, e3⟩ := h.2 x u w h1 h2 h3 n1 n2 n3 hn
  refine ⟨a, ha, e1, e2, ?_⟩
  have := congrArg PathNodeId.id e3
  rwa [pid_id] at this

/-- **Fijar un color conserva las aristas exactas, bajo `TriId`.** Una arista que sobrevive tiene en el paso del color
un testigo vivo, que es de ese color; su triángulo da, por `TriId`, una rama que pasa por la arista y elige el color. -/
theorem snd_pin_of_triId {E : GPathB} {T : Int} {P0 : Assign → Prop} {r : NodeId} (hE : SInvB E) (hns : NoSelf E)
    (hndt : NoDegT E) (hcs : E.current_step = T) (hvE : E.isValid = true) (hr1 : 1 ≤ r.step) (hr2 : r.step < T)
    (hs : Snd φ P0 E) (ht : TriId φ P0 E) (hc : ∀ a, P0 a → CT E (pidOfAssign φ a))
    (hvY : (E.filterAllOn [r]).isValid = true) :
    Snd φ (fun a => P0 a ∧ selOfAssign φ a r.step = r) (E.filterAllOn [r]) := by
  have hsh := (shrinks_filterAllOn E [r]).1
  cases hd : ([r].foldl filterRequire E).dirty
  · -- el filtro no mata a nadie: toda rama de la entrada elige el color
    have hd' : (E.filterRequire r).dirty = false := hd
    have agr : ∀ a, P0 a → selOfAssign φ a r.step = r := by
      intro a hS
      have hD := hc a hS
      have hal := hD.1.alive r.step (by omega) (by rw [hcs]; exact hr2)
      obtain ⟨n, hn, hnid⟩ := hE.docs _ hal
      have hline : n ∈ E.line r.step := by
        unfold line
        refine List.mem_filter.mpr ⟨hn, ?_⟩
        rw [hnid, hD.1.step r.step (by omega) (by rw [hcs]; exact hr2)]
        simp
      have := filterRequire_noVictims hvE hd' n hline
      rw [hnid] at this
      exact this
    intro x w hxw
    obtain ⟨a, hS, h1, h2⟩ := hs x w (hsh.adj _ _ hxw)
    exact ⟨a, ⟨hS, agr a hS⟩, h1, h2⟩
  · have e : E.filterAllOn [r] = E.pinOn [r] := by
      unfold filterAllOn pinOn
      congr 1
      generalize [r].foldl filterRequire E = F at hd
      cases F
      simp_all
    rw [e] at hvY ⊢
    have hsub := sub_pinOn E [r]
    have hiY : SInvB (E.pinOn [r]) := sInvB_pinOn hE [r]
    have hcl : ClosedState (E.pinOn [r]) := closedState_pinOn hE hvY (by rw [hcs]; omega)
    have hf : FixClosed (E.pinOn [r]) :=
      fixClosed_reviewOn (g := { [r].foldl filterRequire E with dirty := true }) rfl hvY
    have hg := trioGood_low hf (noDegT_pinOn hns hndt [r]) (Int.le_refl _)
    have hlt : ∀ {q : PathNodeId}, q ∈ (E.pinOn [r]).alive → q.id.step < (E.pinOn [r]).current_step :=
      fun hq => alive_below hiY.docs hiY.below hq
    have hR : ∀ {y z : PathNodeId}, (E.pinOn [r]).Adj y z →
        LowR (E.pinOn [r]) (E.pinOn [r]).current_step y z := fun h =>
      ⟨⟨(hiY.edges _ _ h).1, (hiY.edges _ _ h).2, h⟩, hlt (hiY.edges _ _ h).1, hlt (hiY.edges _ _ h).2⟩
    have hσ2 : r.step < (E.pinOn [r]).current_step := by rw [step_pinOn, hcs]; exact hr2
    have pinned := pinned_pinOn hE.docs hvY r (List.mem_singleton_self _)
    have nE : ∀ {y z v : PathNodeId}, (E.pinOn [r]).Adj y z → ¬ TF (E.pinOn [r]) y z v → ¬ TF E y z v :=
      fun hyz hn hf => hn (tF_mono (trios_grow_pinOn E [r]) hyz hf)
    -- una rama que pasa por un nodo vivo `s` del paso del color elige el color
    have agS : ∀ {a : Assign} {s : PathNodeId}, s ∈ (E.pinOn [r]).alive → s.id.step = r.step →
        pidOfAssign φ a s.id.step = s → selOfAssign φ a r.step = r := by
      intro a s hsa hss hp
      have := congrArg PathNodeId.id hp
      rw [pid_id, hss] at this
      rw [this]; exact pinned s hsa hss
    -- el color de un nodo vivo del paso del color
    have colS : ∀ {s : PathNodeId}, s ∈ (E.pinOn [r]).alive → s.id.step = r.step → s.id = r :=
      fun hsa hss => pinned _ hsa hss
    intro x w hxw
    by_cases exw : x = w
    · subst exw
      obtain ⟨s, hss, hxs, _⟩ := hcl.pair (y := x) (w := x) (hR hxw).1 r.step (by omega) hσ2
      obtain ⟨a, hS, h1, h2⟩ := hs x s (hsub.adj _ _ hxs.2.2)
      exact ⟨a, ⟨hS, agS hxs.2.1 hss (by rw [hss]; rw [hss] at h2; exact h2)⟩, h1, h1⟩
    · obtain ⟨s, hss, hxs, hws, hor⟩ := hg.edge (hR hxw) exw r.step (by omega) hσ2
      have hsa : s ∈ (E.pinOn [r]).alive := hxs.1.2.1
      by_cases esx : s = x
      · obtain ⟨a, hS, h1, h2⟩ := hs x w (hsub.adj _ _ hxw)
        exact ⟨a, ⟨hS, agS (esx ▸ hsa) (by rw [← esx]; exact hss) h1⟩, h1, h2⟩
      by_cases esw : s = w
      · obtain ⟨a, hS, h1, h2⟩ := hs x w (hsub.adj _ _ hxw)
        exact ⟨a, ⟨hS, agS (esw ▸ hsa) (by rw [← esw]; exact hss) h2⟩, h1, h2⟩
      have hnT : ¬ TF (E.pinOn [r]) x w s := by
        rcases hor with h | h | h
        · exact absurd h esx
        · exact absurd h esw
        · exact h
      obtain ⟨a, hS, h1, h2, h3⟩ := ht x w s (hsub.adj _ _ hxw) (hsub.adj _ _ hxs.1.2.2) (hsub.adj _ _ hws.1.2.2)
        exw (Ne.symm esx) (Ne.symm esw) (nE hxw hnT)
      refine ⟨a, ⟨hS, ?_⟩, h1, h2⟩
      rw [← hss, h3, colS hsa hss]

-- ============================================================
-- El invariante del lector con aristas exactas
-- ============================================================

/-- **El invariante del lector con aristas exactas**: como `RInv`, con `Snd` y `TriId` en lugar de `Snd3`. -/
structure RInvE (φ : Cnf) (T : Int) (P : Assign → Prop) (g : GPathB) : Prop where
  inv   : SInvB g
  ns    : NoSelf g
  ndt   : NoDegT g
  step  : g.current_step = T
  valid : g.isValid = true
  snd   : Snd φ P g
  tri   : TriId φ P g
  comp  : ∀ a, P a → CT g (pidOfAssign φ a)

/-- **La hipótesis del lector para aristas exactas**: tras cualquier lectura, fijar un color más conserva `TriId`. Es
lo abierto. -/
def HReadE (φ : Cnf) (T : Int) (P : Assign → Prop) : Prop :=
  ∀ (R : List NodeId) (r : NodeId) (g : GPathB), RInvE φ T (Pinned φ P R) g → 1 ≤ r.step → r.step < T →
    (g.filterAllOn [r]).isValid = true →
    TriId φ (fun a => Pinned φ P R a ∧ selOfAssign φ a r.step = r) (g.filterAllOn [r])

theorem rInvE_congr {T : Int} {P Q : Assign → Prop} {g : GPathB} (h : RInvE φ T P g) (hpq : ∀ a, P a ↔ Q a) :
    RInvE φ T Q g := by
  have e : P = Q := funext fun a => propext (hpq a)
  subst e; exact h

/-- **Una elección del lector conserva el invariante de aristas**, con `HReadE` para los triángulos. -/
theorem read_stepE {T : Int} {P : Assign → Prop} (hH : HReadE φ T P) {R : List NodeId} {g : GPathB}
    (h : RInvE φ T (Pinned φ P R) g) {q : PathNodeId} (hq : q ∈ g.alive) (hq1 : 1 ≤ q.id.step) :
    RInvE φ T (Pinned φ P (R ++ [q.id])) (g.filterAllOn [q.id]) := by
  have hqT : q.id.step < T := by rw [← h.step]; exact alive_below h.inv.docs h.inv.below hq
  obtain ⟨a, hPa, hpa, _⟩ := h.snd q q (adj_refl _ _ hq)
  have hsel : selOfAssign φ a q.id.step = q.id := by
    have := congrArg PathNodeId.id hpa
    rw [pid_id] at this; exact this
  have one : ∀ {b : Assign}, selOfAssign φ b q.id.step = q.id → ∀ r ∈ [q.id], selOfAssign φ b r.step = r := by
    intro b hb r hr; rw [List.mem_singleton] at hr; subst hr; exact hb
  have hvY : (g.filterAllOn [q.id]).isValid = true :=
    isValid_of_carried (comp_filter h.comp a ⟨hPa, one hsel⟩).1
  have hpq : ∀ b, (Pinned φ P R b ∧ selOfAssign φ b q.id.step = q.id) ↔ Pinned φ P (R ++ [q.id]) b := by
    intro b
    refine ⟨fun hb => ⟨hb.1.1, fun r hr => ?_⟩, fun hb => ⟨⟨hb.1, fun r hr => hb.2 r (List.mem_append_left _ hr)⟩,
      hb.2 q.id (List.mem_append_right _ (List.mem_singleton_self _))⟩⟩
    rcases List.mem_append.mp hr with h' | h'
    · exact hb.1.2 r h'
    · rw [List.mem_singleton] at h'; subst h'; exact hb.2
  refine rInvE_congr ⟨sInvB_filterAllOn h.inv _, noSelf_filterAllOn h.ns _, noDegT_filterAllOn h.ns h.ndt _,
    (step_filterAllOn g _).trans h.step, hvY,
    snd_pin_of_triId h.inv h.ns h.ndt h.step h.valid hq1 hqT h.snd h.tri h.comp hvY,
    hH R q.id g h hq1 hqT hvY, fun b hb => comp_filter h.comp b ⟨hb.1, one hb.2⟩⟩ hpq

/-- **Toda lectura conserva el invariante de aristas.** -/
theorem reading_invE {T : Int} {P : Assign → Prop} (hH : HReadE φ T P) {g g' : GPathB} {R : List NodeId}
    (hr : Reading g R g') : ∀ R0, RInvE φ T (Pinned φ P R0) g → RInvE φ T (Pinned φ P (R0 ++ R)) g' := by
  induction hr with
  | nil g => intro R0 h; rw [List.append_nil]; exact h
  | @cons g g' q rs hq hq1 _ ih =>
    intro R0 h
    have := ih (R0 ++ [q.id]) (read_stepE hH h hq hq1)
    rw [List.append_assoc] at this
    exact this

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **El lector no se atasca**, con las líneas (`PhantomAtW`) y la hipótesis del lector para aristas exactas
(`HReadE`), que pide mucho menos que la exactitud del lector: cualquier lectura de un estado final deja un estado
válido que lleva la rama de una asignación que satisface `φ` y coincide con todas las elecciones. -/
theorem reader_on_edge (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T)
    (HR : ∀ k, HReadE φ (stepCount φ) (SolE φ (stepCount φ) k)) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
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
  have hs3 : Snd3 φ (Pinned φ (SolE φ (stepCount φ) kv.1) []) kv.2 :=
    snd3_mono (hl.snd kv hkv') (fun a ha => ⟨ha, fun r hr => absurd hr List.not_mem_nil⟩)
  have h0 : RInvE φ (stepCount φ) (Pinned φ (SolE φ (stepCount φ) kv.1) []) kv.2 :=
    ⟨hl.inv kv hkv', hent.2.1, hl.ndt kv hkv', hent.1.step, hent.1.valid, hs3.1, triId_of_snd3 hs3,
      fun a ha => hcomp kv hkv' a ha.1⟩
  have hfin := reading_invE (HR kv.1) hr [] h0
  rw [List.nil_append] at hfin
  refine ⟨hfin.valid, ?_⟩
  obtain ⟨q, hq, _⟩ := exists_alive_at hfin.valid (k := 0) (Int.le_refl 0) (by rw [hfin.step]; exact hpos)
  obtain ⟨a, ha, _, _⟩ := hfin.snd q q (adj_refl _ _ hq)
  exact ⟨a, sat_of_validUpTo ha.1.1, ha.2, hfin.comp a ha⟩

end MachineOn

end AbsSatBingo.Model
