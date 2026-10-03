-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain4R.lean
import AbsSatBingo.Model.ForbidOnChain4L

/-!
# El lector en cuatro bloques: separadores primero

`probe_hard4_read.jl` en `chain4_cross`: en 1 037 estados de lectura (todas las de un paso y 300 aleatorias de hasta
cuatro), ningún atasco y ningún triángulo fuera de camarilla; los triángulos del caso abierto (`v` dentro de un
bloque) aparecen (17 480) y todos se salvan. Aquí se demuestra para un lector que fija los separadores de la cadena
antes que las variables de dentro (con cualquier orden: `ForbidOnChain4W`):

* **`phantomFree_pinnedSeps`**: si todas las ramas de `P0` leen igual `s1`, `s2`, `s3`, los bloques ya no se ven y
  basta parchear el interior del bloque de `v` (`helly4_of_patch`), sin descenso.
* `reading_inv_on`: `reading_inv` pide la hipótesis del lector solo en los pasos de la lectura (`GoodAlong`).
* **`reader_on_chain4L`** (`GoodPin`): en toda fórmula `Chain4L`, una lectura en la que cada variable interior se fija
  después de los separadores de su cadena deja un estado válido con la rama de una solución que coincide con todas las
  elecciones. Sin hipótesis sobre la máquina.
* `reader_fourChainL`: en `fourChainL`, toda lectura que empieza fijando los tres separadores.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

theorem clIn_mono {B B' : Nat → Prop} {c : Clause} (h : ClIn B c) (hm : ∀ z, B z → B' z) : ClIn B' c :=
  ⟨hm _ h.1, hm _ h.2.1, hm _ h.2.2⟩

section Split

variable {s1 s2 s3 : Nat} {A M N C : Nat → Prop}

/-- Las variables de dentro del bloque de `v`. -/
def InnerOf (A M N C : Nat → Prop) (v z : Nat) : Prop := (A v ∧ A z) ∨ (M v ∧ M z) ∨ (N v ∧ N z) ∨ (C v ∧ C z)

/-- **Cada cláusula está entera fuera del interior del bloque de `v`, o entera en él y los separadores.** -/
theorem cl_split (D : Chain4Data φ s1 s2 s3 A M N C) (v : Nat) :
    ∀ c ∈ φ.clauses, ClIn (fun z => ¬ InnerOf A M N C v z) c ∨
      ClIn (fun z => InnerOf A M N C v z ∨ z = s1 ∨ z = s2 ∨ z = s3) c := by
  intro c hc
  -- dentro de un bloque cuyo interior no es el de `v`, ninguna variable es del interior de `v`
  have outA : ∀ z, (A z ∨ z = s1) → ¬ A v → ¬ InnerOf A M N C v z := by
    rintro z hz hav (⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hav h1
    · rcases hz with hz | hz
      · exact D.dAM z hz h2
      · rw [hz] at h2; exact D.mS1 h2
    · rcases hz with hz | hz
      · exact D.dAN z hz h2
      · rw [hz] at h2; exact D.nS1 h2
    · rcases hz with hz | hz
      · exact D.dAC z hz h2
      · rw [hz] at h2; exact D.cS1 h2
  have outM : ∀ z, (z = s1 ∨ M z ∨ z = s2) → ¬ M v → ¬ InnerOf A M N C v z := by
    rintro z hz hmv (⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rcases hz with hz | hz | hz
      · rw [hz] at h2; exact D.aS1 h2
      · exact D.dAM z h2 hz
      · rw [hz] at h2; exact D.aS2 h2
    · exact hmv h1
    · rcases hz with hz | hz | hz
      · rw [hz] at h2; exact D.nS1 h2
      · exact D.dMN z hz h2
      · rw [hz] at h2; exact D.nS2 h2
    · rcases hz with hz | hz | hz
      · rw [hz] at h2; exact D.cS1 h2
      · exact D.dMC z hz h2
      · rw [hz] at h2; exact D.cS2 h2
  have outN : ∀ z, (z = s2 ∨ N z ∨ z = s3) → ¬ N v → ¬ InnerOf A M N C v z := by
    rintro z hz hnv (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩)
    · rcases hz with hz | hz | hz
      · rw [hz] at h2; exact D.aS2 h2
      · exact D.dAN z h2 hz
      · rw [hz] at h2; exact D.aS3 h2
    · rcases hz with hz | hz | hz
      · rw [hz] at h2; exact D.mS2 h2
      · exact D.dMN z h2 hz
      · rw [hz] at h2; exact D.mS3 h2
    · exact hnv h1
    · rcases hz with hz | hz | hz
      · rw [hz] at h2; exact D.cS2 h2
      · exact D.dNC z hz h2
      · rw [hz] at h2; exact D.cS3 h2
  have outC : ∀ z, (C z ∨ z = s3) → ¬ C v → ¬ InnerOf A M N C v z := by
    rintro z hz hcv (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩)
    · rcases hz with hz | hz
      · exact D.dAC z h2 hz
      · rw [hz] at h2; exact D.aS3 h2
    · rcases hz with hz | hz
      · exact D.dMC z h2 hz
      · rw [hz] at h2; exact D.mS3 h2
    · rcases hz with hz | hz
      · exact D.dNC z h2 hz
      · rw [hz] at h2; exact D.nS3 h2
    · exact hcv h1
  have outO : ∀ z, ¬ InCh4 s1 s2 s3 A M N C z → ¬ InnerOf A M N C v z := by
    rintro z hz (⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩)
    · exact hz (Or.inl h2)
    · exact hz (Or.inr (Or.inl h2))
    · exact hz (Or.inr (Or.inr (Or.inl h2)))
    · exact hz (Or.inr (Or.inr (Or.inr (Or.inl h2))))
  rcases D.cl c hc with hi | hi | hi | hi | hi
  · exact Or.inl (clIn_mono hi outO)
  · by_cases hav : A v
    · refine Or.inr (clIn_mono hi (fun z hz => ?_))
      rcases hz with hz | hz
      · exact Or.inl (Or.inl ⟨hav, hz⟩)
      · exact Or.inr (Or.inl hz)
    · exact Or.inl (clIn_mono hi (fun z hz => outA z hz hav))
  · by_cases hmv : M v
    · refine Or.inr (clIn_mono hi (fun z hz => ?_))
      rcases hz with hz | hz | hz
      · exact Or.inr (Or.inl hz)
      · exact Or.inl (Or.inr (Or.inl ⟨hmv, hz⟩))
      · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inl (clIn_mono hi (fun z hz => outM z hz hmv))
  · by_cases hnv : N v
    · refine Or.inr (clIn_mono hi (fun z hz => ?_))
      rcases hz with hz | hz | hz
      · exact Or.inr (Or.inr (Or.inl hz))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨hnv, hz⟩)))
      · exact Or.inr (Or.inr (Or.inr hz))
    · exact Or.inl (clIn_mono hi (fun z hz => outN z hz hnv))
  · by_cases hcv : C v
    · refine Or.inr (clIn_mono hi (fun z hz => ?_))
      rcases hz with hz | hz
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hcv, hz⟩)))
      · exact Or.inr (Or.inr (Or.inr hz))
    · exact Or.inl (clIn_mono hi (fun z hz => outC z hz hcv))

/-- El interior del bloque de `v` no tiene tres variables distintas. -/
theorem innerOf_no3 (D : Chain4Data φ s1 s2 s3 A M N C) {v : Nat} (hin : A v ∨ M v ∨ N v ∨ C v) :
    No3 (InnerOf A M N C v) := by
  -- las tres están en el interior de `v`
  have side : ∀ {I : Nat → Prop}, I v → (∀ z, InnerOf A M N C v z → I z) → No3 I → No3 (InnerOf A M N C v) :=
    fun _ hI h3 => fun z1 z2 z3 a b c d e f => h3 z1 z2 z3 (hI z1 a) (hI z2 b) (hI z3 c) d e f
  rcases hin with h | h | h | h
  · refine side h (fun z hz => ?_) D.cardA
    rcases hz with ⟨_, hz⟩ | ⟨hm, _⟩ | ⟨hn, _⟩ | ⟨hc, _⟩
    · exact hz
    · exact absurd hm (fun hm => D.dAM v h hm)
    · exact absurd hn (fun hn => D.dAN v h hn)
    · exact absurd hc (fun hc => D.dAC v h hc)
  · refine side h (fun z hz => ?_) (GPathB.no3_of_le1 D.cardM)
    rcases hz with ⟨ha, _⟩ | ⟨_, hz⟩ | ⟨hn, _⟩ | ⟨hc, _⟩
    · exact absurd ha (fun ha => D.dAM v ha h)
    · exact hz
    · exact absurd hn (fun hn => D.dMN v h hn)
    · exact absurd hc (fun hc => D.dMC v h hc)
  · refine side h (fun z hz => ?_) (GPathB.no3_of_le1 D.cardN)
    rcases hz with ⟨ha, _⟩ | ⟨hm, _⟩ | ⟨_, hz⟩ | ⟨hc, _⟩
    · exact absurd ha (fun ha => D.dAN v ha h)
    · exact absurd hm (fun hm => D.dMN v hm h)
    · exact hz
    · exact absurd hc (fun hc => D.dNC v h hc)
  · refine side h (fun z hz => ?_) D.cardC
    rcases hz with ⟨ha, _⟩ | ⟨hm, _⟩ | ⟨hn, _⟩ | ⟨_, hz⟩
    · exact absurd ha (fun ha => D.dAC v ha h)
    · exact absurd hm (fun hm => D.dMC v hm h)
    · exact absurd hn (fun hn => D.dNC v hn h)
    · exact hz

theorem innerOf_self {v : Nat} (hin : A v ∨ M v ∨ N v ∨ C v) : InnerOf A M N C v v := by
  rcases hin with h | h | h | h
  · exact Or.inl ⟨h, h⟩
  · exact Or.inr (Or.inl ⟨h, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h, h⟩))

end Split

namespace GPathB

variable {P0 P : Assign → Prop} {Nn σ : Int}

/-- **Con los separadores fijados, sin familias fantasma**: si todas las ramas de `P0` leen igual `s1`, `s2` y `s3`,
basta parchear el interior del bloque de la variable fijada. -/
theorem phantomFree_pinnedSeps {s1 s2 s3 : Nat} {A M N C : Nat → Prop} (hl : LocPair φ P0 P σ)
    (D : Chain4Data φ s1 s2 s3 A M N C) {v : Nat} (hv : stepVar φ σ = some v) (hin : A v ∨ M v ∨ N v ∨ C v)
    (hsep : ∀ a b, P0 a → P0 b → a s1 = b s1 ∧ a s2 = b s2 ∧ a s3 = b s3) (hσ0 : 0 ≤ σ) (hσN : σ < Nn) :
    PhantomFree φ P0 P Nn σ := by
  refine phantomFree_of_helly4 hσ0 hσN (helly4_of_patch (InnerOf A M N C v)
    (fun z1 z2 z3 a b c d e f => absurd (innerOf_no3 D hin z1 z2 z3 a b c d e f) (fun h => h))
    (fun a0 a' h0 h' => ?_))
  have h0' := hl.sub _ h'
  -- en los separadores el parche lee como `a0`, que lee como `a'`
  have onS : ∀ {z : Nat}, (InnerOf A M N C v z ∨ z = s1 ∨ z = s2 ∨ z = s3) →
      patch (InnerOf A M N C v) a' a0 z = a' z := by
    intro z hz
    by_cases hi : InnerOf A M N C v z
    · exact patch_in hi
    · rw [patch_out hi]
      obtain ⟨e1, e2, e3⟩ := hsep a0 a' h0 h0'
      rcases hz with hz | hz | hz | hz
      · exact absurd hz hi
      · rw [hz]; exact e1
      · rw [hz]; exact e2
      · rw [hz]; exact e3
  have hP0 : P0 (patch (InnerOf A M N C v) a' a0) := by
    refine p0_of_sources hl ⟨a0, h0⟩ (fun z => ?_) (fun c hc => ?_)
    · by_cases hi : InnerOf A M N C v z
      · exact ⟨a', h0', patch_in hi⟩
      · exact ⟨a0, h0, patch_out hi⟩
    · rcases cl_split D v c hc with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩
      · exact ⟨a0, h0, patch_out o1, patch_out o2, patch_out o3⟩
      · exact ⟨a', h0', onS i1, onS i2, onS i3⟩
  refine p_of_sources hl hP0 (fun h => by rw [hv] at h; cases h) (fun z hz => ?_)
  rw [hv] at hz; cases hz
  refine ⟨⟨a', h', patch_in (innerOf_self hin)⟩, fun c hc hcv => ?_⟩
  rcases cl_split D v c hc with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩
  · exfalso
    rcases hcv with e | e | e
    · exact o1 (e ▸ innerOf_self hin)
    · exact o2 (e ▸ innerOf_self hin)
    · exact o3 (e ▸ innerOf_self hin)
  · exact ⟨a', h', onS i1, onS i2, onS i3⟩

end GPathB

-- ============================================================
-- Lecturas buenas
-- ============================================================

/-- `v` tiene datos que valen con cualquier lectura: separador, cadena de tres, o separador de una de cuatro. -/
def Struct4 (φ : Cnf) (v : Nat) : Prop :=
  (∃ s L Rr, SepData φ v s L Rr) ∨ (∃ s1 s2 A M C, ChainData φ v s1 s2 A M C) ∨ Chain4At φ v

/-- `v` está dentro de un bloque de una cadena de cuatro cuyos tres separadores ya lee alguna elección de `R0`. -/
def PinsSepsFor (φ : Cnf) (R0 : List NodeId) (v : Nat) : Prop :=
  ∃ s1 s2 s3 A M N C, Chain4Data φ s1 s2 s3 A M N C ∧ (A v ∨ M v ∨ N v ∨ C v) ∧
    ∀ s, (s = s1 ∨ s = s2 ∨ s = s3) → ∃ x ∈ R0, stepVar φ x.step = some s

/-- **Una elección buena**: la variable que fija tiene datos para cualquier lectura, o sus separadores ya están fijados. -/
def GoodPin (φ : Cnf) (R0 : List NodeId) (r : NodeId) : Prop :=
  ∀ v, stepVar φ r.step = some v → Struct4 φ v ∨ PinsSepsFor φ R0 v

/-- **Una lectura buena**: cada elección es buena con las anteriores. -/
def GoodAlong (φ : Cnf) : List NodeId → List NodeId → Prop
  | _, [] => True
  | R0, r :: rs => GoodPin φ R0 r ∧ GoodAlong φ (R0 ++ [r]) rs

namespace GPathB

open Driver Machine MachineOn

/-- **`reading_inv` con la hipótesis del lector solo en los pasos de la lectura.** -/
theorem reading_inv_on {T : Int} {P : Assign → Prop}
    (hH : ∀ R0 r, (∀ x ∈ R0, 1 ≤ x.step ∧ x.step < T) → 1 ≤ r.step → r.step < T → GoodPin φ R0 r →
      PhantomFree φ (Pinned φ P R0) (fun a => Pinned φ P R0 a ∧ selOfAssign φ a r.step = r) T r.step)
    {g g' : GPathB} {R : List NodeId} (hr : Reading g R g') : ∀ R0, (∀ x ∈ R0, 1 ≤ x.step ∧ x.step < T) →
      GoodAlong φ R0 R → RInv φ T (Pinned φ P R0) g → RInv φ T (Pinned φ P (R0 ++ R)) g' := by
  induction hr with
  | nil g => intro R0 _ _ h; rw [List.append_nil]; exact h
  | @cons g g' q rs hq hq1 _ ih =>
    intro R0 hR0 hgood h
    have hqT : q.id.step < T := by rw [← h.step]; exact alive_below h.inv.docs h.inv.below hq
    have h1 := read_step h hq hq1 (hH R0 q.id hR0 hq1 hqT hgood.1)
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
      · rw [List.mem_singleton] at h'; subst h'; exact ⟨hq1, hqT⟩) hgood.2 h2
    rw [List.append_assoc] at this
    exact this

/-- La hipótesis del lector en una elección buena, en una fórmula `Chain4L`. -/
theorem hRead_good {T : Int} (hN : midFusion φ < T) (k : NodeId) (R0 : List NodeId) (r : NodeId)
    (hr1 : 1 ≤ r.step) (hrT : r.step < T) (hg : GoodPin φ R0 r) :
    PhantomFree φ (Pinned φ (SolE φ T k) R0) (fun a => Pinned φ (SolE φ T k) R0 a ∧ selOfAssign φ a r.step = r) T
      r.step := by
  cases hv : stepVar φ r.step with
  | none => exact phantomFree_none (locPair_read T k R0 r) hv (by omega) hrT
  | some v =>
    rcases hg v hv with h | ⟨s1, s2, s3, A, M, N, C, D, hin, hpin⟩
    · exact phantomFree_of_struct4 (locPair_read T k R0 r) hv h (by omega) hrT hN
    · refine phantomFree_pinnedSeps (locPair_read T k R0 r) D hv hin (fun a b ha hb => ?_) (by omega) hrT
      have one : ∀ s, (s = s1 ∨ s = s2 ∨ s = s3) → a s = b s := by
        intro s hs
        obtain ⟨x, hx, hxs⟩ := hpin s hs
        exact var_eq_of_sel ((ha.2 x hx).trans (hb.2 x hx).symm) s hxs
      exact ⟨one s1 (Or.inl rfl), one s2 (Or.inr (Or.inl rfl)), one s3 (Or.inr (Or.inr rfl))⟩

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **El lector no se atasca en una fórmula `Chain4L` si fija los separadores de cada cadena antes que sus variables de
dentro.** Cualquier lectura buena de un estado final deja un estado válido que lleva la rama de una asignación que
satisface `φ` y coincide con todas las elecciones. Sin hipótesis sobre la máquina. -/
theorem reader_on_chain4L_good (hbd : Bounded φ) (hcl : Chain4L φ) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') (hg : GoodAlong φ [] R) :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) := by
  have HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T := fun T hT => phantomAtW_of_phantomAt (phantomAt_of_chain4L hbd hcl T hT)
  have hpos := stepCount_pos φ
  have hn : (((stepCount φ - 1).toNat : Nat) : Int) + 1 = stepCount φ := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  have hl := lInvS3_stepsW hbd (stepCount φ - 1).toNat (fun T h1 _ => HA T h1)
  have hcomp := compLine_steps hbd (lInvS_of_s3 hl)
  rw [hn] at hl hcomp
  have hkv' : kv ∈ stepsM .on φ (stepCount φ - 1).toNat (initM .on φ) := hkv
  have hent := hl.on kv hkv'
  have h0 : RInv φ (stepCount φ) (Pinned φ (SolE φ (stepCount φ) kv.1) []) kv.2 :=
    rInv_congr (P := SolE φ (stepCount φ) kv.1)
      ⟨hl.inv kv hkv', hent.2.1, hl.ndt kv hkv', hent.1.step, hent.1.valid, hl.snd kv hkv', hcomp kv hkv'⟩
      (fun a => ⟨fun ha => ⟨ha, fun r hr => absurd hr List.not_mem_nil⟩, fun ha => ha.1⟩)
  have hN : midFusion φ < stepCount φ := by unfold stepCount midFusion; omega
  have hfin := reading_inv_on (fun R0 r _ hr1 hrT hgp => hRead_good hN kv.1 R0 r hr1 hrT hgp) hr []
    (fun x hx => absurd hx List.not_mem_nil) hg h0
  rw [List.nil_append] at hfin
  refine ⟨hfin.valid, ?_⟩
  obtain ⟨q, hq, _⟩ := exists_alive_at hfin.valid (k := 0) (Int.le_refl 0) (by rw [hfin.step]; exact hpos)
  obtain ⟨a, ha, _, _⟩ := hfin.snd.1 q q (adj_refl _ _ hq)
  exact ⟨a, sat_of_validUpTo ha.1.1, ha.2, hfin.comp a ha⟩

end MachineOn

-- ============================================================
-- Un caso concreto
-- ============================================================

theorem struct4_fourChainL_sep {v : Nat} (h : v = 5 ∨ v = 6 ∨ v = 7) : Struct4 fourChainL v := by
  rcases h with rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, chain4Data_fourChainL_rev⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, chain4Data_fourChainL⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, chain4Data_fourChainL⟩))

/-- Una variable que no está en la fórmula: separador de sí misma, sin lados. -/
theorem struct4_fourChainL_out {v : Nat} (h : 9 ≤ v) : Struct4 fourChainL v := by
  refine Or.inl ⟨v, fun _ => False, fun _ => False, ⟨fun h => absurd rfl h, fun h => h, fun _ h _ => h, Or.inl rfl,
    fun _ _ _ h _ _ _ _ _ => h, fun _ _ _ h _ _ _ _ _ => h, fun h => absurd rfl h, fun c hc => ?_⟩⟩
  simp only [fourChainL, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩

theorem goodAlong_fourChainL : ∀ (rest R0 : List NodeId),
    (∀ s, (s = 5 ∨ s = 6 ∨ s = 7) → ∃ x ∈ R0, stepVar fourChainL x.step = some s) → GoodAlong fourChainL R0 rest := by
  intro rest
  induction rest with
  | nil => intro _ _; trivial
  | cons r rs ih =>
    intro R0 hR0
    refine ⟨fun v _ => ?_, ih _ (fun s hs => ?_)⟩
    · by_cases hs : v = 5 ∨ v = 6 ∨ v = 7
      · exact Or.inl (struct4_fourChainL_sep hs)
      by_cases h9 : 9 ≤ v
      · exact Or.inl (struct4_fourChainL_out h9)
      · refine Or.inr ⟨_, _, _, _, _, _, _, chain4Data_fourChainL, ?_, hR0⟩
        omega
    · obtain ⟨x, hx, hxs⟩ := hR0 s hs
      exact ⟨x, List.mem_append_left _ hx, hxs⟩

namespace MachineOn

open GPathB Driver Machine

/-- **El lector no se atasca en `fourChainL`** si sus tres primeras elecciones leen los tres separadores (en cualquier
orden); después, cualquier elección. -/
theorem reader_fourChainL {kv : NodeId × GPathB} (hkv : kv ∈ runM .on fourChainL) {r1 r2 r3 : NodeId}
    {rest : List NodeId} {g' : GPathB} (hr : Reading kv.2 (r1 :: r2 :: r3 :: rest) g')
    (h3 : ∀ x ∈ [r1, r2, r3], ∀ v, stepVar fourChainL x.step = some v → v = 5 ∨ v = 6 ∨ v = 7)
    (hs : ∀ s, (s = 5 ∨ s = 6 ∨ s = 7) → ∃ x ∈ [r1, r2, r3], stepVar fourChainL x.step = some s) :
    g'.isValid = true ∧ ∃ a, Sat a fourChainL ∧ (∀ r ∈ r1 :: r2 :: r3 :: rest, selOfAssign fourChainL a r.step = r) ∧
      CT g' (pidOfAssign fourChainL a) := by
  refine reader_on_chain4L_good bounded_fourChainL chain4L_fourChainL hkv hr ⟨fun v hv => ?_, fun v hv => ?_,
    fun v hv => ?_, goodAlong_fourChainL rest _ (fun s h => ?_)⟩
  · exact Or.inl (struct4_fourChainL_sep (h3 r1 (by simp) v hv))
  · exact Or.inl (struct4_fourChainL_sep (h3 r2 (by simp) v hv))
  · exact Or.inl (struct4_fourChainL_sep (h3 r3 (by simp) v hv))
  · obtain ⟨x, hx, hxs⟩ := hs s h
    exact ⟨x, by simpa using hx, hxs⟩

end MachineOn

end AbsSatBingo.Model
