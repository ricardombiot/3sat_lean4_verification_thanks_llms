-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnReadIff.lean
import AbsSatBingo.Model.ForbidOnTight

/-!
# La equivalencia para el lector, y el enlace con la escalera de niveles

* **`hypsTriKeep_of_phantomAt`**: sin familias fantasma, el filtro de cada llegada conserva los triángulos de cima;
  con la escalera de `ForbidOnExact`, también las aristas y los nodos (`hypsNodeKeep_of_phantomAt`). Las hipótesis de
  niveles del v221 son consecuencias de la condición sobre la fórmula.
* **`ReaderExact φ`**: todo estado al que llega una lectura de un estado final tiene sus parejas de vecinos y sus
  triángulos sin prohibir en ramas de soluciones que coinciden con las elecciones.
* **`readerExact_iff`**: con las líneas sin familias fantasma (`PhantomAt`), **el lector es exacto exactamente cuando
  la lectura no tiene familias fantasma** (`HRead`). El recíproco reconstruye, para cada lista de colores, la lectura
  que la fija: o algún color no tiene nodo vivo (y entonces ninguna solución elige esa lista), o la lectura existe y
  su estado es exacto.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

open Driver Machine MachineOn

variable {φ : Cnf}

-- ============================================================
-- La escalera de niveles sale de la condición sobre la fórmula
-- ============================================================

/-- **Sin familias fantasma, el filtro de cada llegada conserva `TopTri`.** -/
theorem hypsTriKeep_of_phantomAt (hb : Bounded φ) (H : ∀ T : Int, 1 ≤ T → PhantomAt φ T) : HypsTriKeep φ := by
  intro n kv hkv d hs _ _
  obtain ⟨hsY, _⟩ := ((machineExact_iff hb).mpr H n kv hkv).2 d hs.1
  have hS := hsY (valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2)
  have comp := comp_filter (reqs := reqOf φ d) (compLine_base hb n kv hkv)
  intro t _ hts u w htu htw huw ntu ntw nuw hn
  obtain ⟨a, hP, h1, h2, h3⟩ := hS.2 t u w htu htw huw ntu ntw nuw hn
  exact ⟨_, comp a hP, by rw [← hts]; exact h1, h2, h3⟩

/-- Y con la escalera, también las aristas y los nodos de cima: las hipótesis de niveles son consecuencias. -/
theorem hypsNodeKeep_of_phantomAt (hb : Bounded φ) (H : ∀ T : Int, 1 ≤ T → PhantomAt φ T) : HypsNodeKeep φ :=
  hypsNodeKeep_of_edgeKeep (hypsEdgeKeep_of_triKeep (hypsTriKeep_of_phantomAt hb H))

-- ============================================================
-- La lectura
-- ============================================================

/-- Una lectura se alarga por el final con el color de un nodo vivo del estado al que llegó. -/
theorem reading_snoc {g g' : GPathB} {R : List NodeId} (h : Reading g R g') {q : PathNodeId} (hq : q ∈ g'.alive)
    (hq1 : 1 ≤ q.id.step) : Reading g (R ++ [q.id]) (g'.filterAllOn [q.id]) := by
  induction h with
  | nil g => exact Reading.cons hq hq1 (Reading.nil _)
  | @cons g g' p rs hp hp1 _ ih => exact Reading.cons hp hp1 (ih hq)

/-- **El lector es exacto**: todo estado al que llega una lectura de un estado final tiene sus parejas de vecinos y
sus triángulos sin prohibir en ramas de soluciones que coinciden con las elecciones. -/
def ReaderExact (φ : Cnf) : Prop :=
  ∀ kv ∈ runM .on φ, ∀ (R : List NodeId) (g' : GPathB), Reading kv.2 R g' →
    Snd3 φ (Pinned φ (SolE φ (stepCount φ) kv.1) R) g'

section Reach

variable {kv : NodeId × GPathB} {T : Int}

/-- Un paso de lectura con la exactitud del estado nuevo dada de fuera: lo demás (validez, completitud, contabilidad)
no pide ninguna condición. -/
theorem rInv_step {P : Assign → Prop} {R0 : List NodeId} {g : GPathB} (h : RInv φ T (Pinned φ P R0) g)
    {q : PathNodeId} (hq : q ∈ g.alive)
    (hs : Snd3 φ (Pinned φ P (R0 ++ [q.id])) (g.filterAllOn [q.id])) :
    RInv φ T (Pinned φ P (R0 ++ [q.id])) (g.filterAllOn [q.id]) := by
  obtain ⟨a, hPa, hpa, _⟩ := h.snd.1 q q (adj_refl _ _ hq)
  have hsel : selOfAssign φ a q.id.step = q.id := by
    have := congrArg PathNodeId.id hpa
    rw [pid_id] at this; exact this
  have conv : ∀ b, Pinned φ P (R0 ++ [q.id]) b → (Pinned φ P R0 b ∧ ∀ r ∈ [q.id], selOfAssign φ b r.step = r) :=
    fun b hb => ⟨⟨hb.1, fun r hr => hb.2 r (List.mem_append_left _ hr)⟩,
      fun r hr => hb.2 r (List.mem_append_right _ hr)⟩
  have hvY : (g.filterAllOn [q.id]).isValid = true :=
    isValid_of_carried (comp_filter h.comp a ⟨hPa, fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hsel⟩).1
  exact ⟨sInvB_filterAllOn h.inv _, noSelf_filterAllOn h.ns _, noDegT_filterAllOn h.ns h.ndt _,
    (step_filterAllOn g _).trans h.step, hvY, hs, fun b hb => comp_filter h.comp b (conv b hb)⟩

/-- **Para cada lista de colores**: o ninguna solución la elige entera, o hay una lectura que la fija y su estado
cumple el invariante. La exactitud de cada estado nuevo se da de fuera (`hex`). -/
theorem reach {P : Assign → Prop}
    (hex : ∀ (R : List NodeId) (g' : GPathB), Reading kv.2 R g' → Snd3 φ (Pinned φ P R) g') :
    ∀ (R : List NodeId), (∀ x ∈ R, 1 ≤ x.step ∧ x.step < T) → ∀ (R0 : List NodeId) (g : GPathB),
      Reading kv.2 R0 g → RInv φ T (Pinned φ P R0) g →
      (∀ a, ¬ Pinned φ P (R0 ++ R) a) ∨
        ∃ g', Reading kv.2 (R0 ++ R) g' ∧ RInv φ T (Pinned φ P (R0 ++ R)) g' := by
  intro R
  induction R with
  | nil => intro _ R0 g hr h; exact Or.inr ⟨g, by rw [List.append_nil]; exact hr, by rw [List.append_nil]; exact h⟩
  | cons r1 rs ih =>
    intro hR R0 g hr h
    obtain ⟨hr1, hrT⟩ := hR r1 List.mem_cons_self
    by_cases hq : ∃ q ∈ g.alive, q.id = r1
    · obtain ⟨q, hqa, rfl⟩ := hq
      have hr' := reading_snoc hr hqa hr1
      have h' := rInv_step h hqa (hex _ _ hr')
      have := ih (fun x hx => hR x (List.mem_cons_of_mem _ hx)) (R0 ++ [q.id]) _ hr' h'
      rw [List.append_assoc] at this
      exact this
    · refine Or.inl (fun a ha => hq ?_)
      have hP0 : Pinned φ P R0 a := ⟨ha.1, fun x hx => ha.2 x (List.mem_append_left _ hx)⟩
      have hct := h.comp a hP0
      have hal := hct.1.alive r1.step (by omega) (by rw [h.step]; exact hrT)
      refine ⟨_, hal, ?_⟩
      rw [pid_id]
      exact ha.2 r1 (List.mem_append_right _ List.mem_cons_self)

end Reach

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {φ : Cnf}

/-- **El lector es exacto exactamente cuando la lectura no tiene familias fantasma.** -/
theorem readerExact_iff (hb : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAt φ T) :
    ReaderExact φ ↔ ∀ k, HRead φ (stepCount φ) (SolE φ (stepCount φ) k) := by
  have hpos := stepCount_pos φ
  have hn : (((stepCount φ - 1).toNat : Nat) : Int) + 1 = stepCount φ := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  have base := lInvBase_steps φ (stepCount φ - 1).toNat
  have hcomp := compLine_base hb (stepCount φ - 1).toNat
  rw [hn] at base hcomp
  -- el invariante del estado final, con su exactitud dada
  have start : ∀ kv ∈ runM .on φ, Snd3 φ (Pinned φ (SolE φ (stepCount φ) kv.1) []) kv.2 →
      RInv φ (stepCount φ) (Pinned φ (SolE φ (stepCount φ) kv.1) []) kv.2 := by
    intro kv hkv hs
    have hent := base.on kv hkv
    exact ⟨base.inv kv hkv, hent.2.1, base.ndt kv hkv, hent.1.step, hent.1.valid, hs,
      fun a ha => hcomp kv hkv a ha.1⟩
  constructor
  · intro hRE k R r hR hr1 hrT
    by_cases hent : ∃ kv ∈ runM .on φ, kv.1 = k
    · obtain ⟨kv, hkv, rfl⟩ := hent
      have h0 := start kv hkv (hRE kv hkv [] kv.2 (Reading.nil _))
      rcases reach (T := stepCount φ) (hRE kv hkv) R hR [] kv.2 (Reading.nil _) h0 with hemp | ⟨g, hread, hinv⟩
      · rw [List.nil_append] at hemp
        exact phantomFree_of_empty hemp
      · rw [List.nil_append] at hread hinv
        refine phantomFree_of_exact_filter hinv.ns hinv.ndt hinv.step hinv.comp (fun hv => ?_)
        -- el estado filtrado es válido: hay un nodo vivo del color, y la lectura sigue
        have hcsY : (g.filterAllOn [r]).current_step = stepCount φ := (step_filterAllOn g _).trans hinv.step
        obtain ⟨q, hqY, hqs⟩ := exists_alive_at hv (k := r.step) (by omega) (by rw [hcsY]; exact hrT)
        have hs1 : Sub (g.filterAllOn [r]) ([r].foldl filterRequire g) := (shrinks_reviewOn _).1
        have hqid : q.id = r :=
          pinned_foldl [r] g hinv.inv.docs (isValid_of_sub hs1 hv) q (hs1.alive q hqY) (List.mem_singleton_self _) hqs
        have hqg : q ∈ g.alive := (shrinks_filterAllOn g [r]).1.alive q hqY
        have hread' := reading_snoc hread hqg (by rw [hqid]; exact hr1)
        rw [hqid] at hread'
        exact snd3_mono (hRE kv hkv _ _ hread') (fun a ha =>
          ⟨⟨ha.1, fun x hx => ha.2 x (List.mem_append_left _ hx)⟩,
            ha.2 r (List.mem_append_right _ (List.mem_singleton_self _))⟩)
    · -- ninguna entrada final con esa clave: ninguna solución la elige
      refine phantomFree_of_empty (fun a ha => hent ?_)
      have hv : ValidUpTo φ a (((stepCount φ - 1).toNat : Nat) + 1 : Int) := by rw [hn]; exact ha.1.1
      obtain ⟨_, g, hf, _⟩ := comp_line hb a (stepCount φ - 1).toNat (by omega) hv
      refine ⟨_, List.mem_of_find?_eq_some hf, ?_⟩
      have e : (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
      show selOfAssign φ a ((stepCount φ - 1).toNat : Nat) = k
      rw [e]; exact ha.1.2
  · intro HR kv hkv R g' hr
    have hl := lInvS3_steps hb (stepCount φ - 1).toNat (fun T h1 _ => HA T h1)
    rw [hn] at hl
    have h0 := start kv hkv (snd3_mono (hl.snd kv hkv) (fun a ha => ⟨ha, fun r hr => absurd hr List.not_mem_nil⟩))
    have hfin := reading_inv (HR kv.1) hr [] (fun x hx => absurd hx List.not_mem_nil) h0
    rw [List.nil_append] at hfin
    exact hfin.snd

end MachineOn

end AbsSatBingo.Model
