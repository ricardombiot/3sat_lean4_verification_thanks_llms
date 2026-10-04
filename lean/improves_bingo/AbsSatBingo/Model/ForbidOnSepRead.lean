-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnSepRead.lean
import AbsSatBingo.Model.ForbidOnPinPairs

/-!
# El lector por separadores (informe v225)

El lector fija primero los separadores (las variables compartidas), en un orden fijo, y después el resto. Con todos los
separadores fijados, los bloques ya no se ven, y fijar una variable de dentro es un parche de su parte.

* **`SepCover φ S part`**: quitar los separadores `S` deja partes de a lo sumo dos variables, y cada cláusula tiene
  sus variables que no son separadores en una sola parte. Las cadenas de bloques la cumplen.
* **T1, `phantomFree_pinnedSepCover`**: si todas las ramas de `P0` leen igual los separadores, una variable que no es
  separador se fija sin familias fantasma (`helly4_of_patch` con su parte), con cualquier longitud de cadena.
* `phantomFree_fixedVar`: volver a fijar una variable que todas las ramas ya leen igual.
* **T2, `SepPinFree φ S T`** (la hipótesis que queda): fijar el separador `S[k]` con los anteriores fijados.
* `reading_inv_gen`: `reading_inv_on` para cualquier predicado de elecciones buenas.
* **T3, `reader_sep_on`**: con las líneas, una cobertura por separadores y T2, toda lectura que empieza por los
  separadores en el orden de `S` (`SepFirst`) deja un estado válido con la rama de una solución que coincide con todas
  las elecciones.

Medido (`probe_reader_sep.jl`): en `chain5_cross`, 0 triángulos fantasma en los estados del lector por separadores
(el lector en cualquier orden tenía 36).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- **Una cobertura por separadores.** -/
structure SepCover (φ : Cnf) (S : List Nat) (part : Nat → Nat) : Prop where
  cl   : ∀ c ∈ φ.clauses, ∀ z z', ClVar c z → ClVar c z' → z ∉ S → z' ∉ S → part z = part z'
  card : ∀ p z1 z2 z3, z1 ∉ S → z2 ∉ S → z3 ∉ S → part z1 = p → part z2 = p → part z3 = p →
    z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False

namespace GPathB

open Driver Machine MachineOn

variable {P0 P : Assign → Prop} {N σ : Int}

/-- **T1: con los separadores fijados, una variable de dentro.** -/
theorem phantomFree_pinnedSepCover {S : List Nat} {part : Nat → Nat} (hl : LocPair φ P0 P σ) (hc : SepCover φ S part)
    {v : Nat} (hv : stepVar φ σ = some v) (hvS : v ∉ S) (hsep : ∀ a b, P0 a → P0 b → ∀ s ∈ S, a s = b s)
    (hσ0 : 0 ≤ σ) (hσN : σ < N) : PhantomFree φ P0 P N σ := by
  -- la parte de `v`
  let B : Nat → Prop := fun z => z ∉ S ∧ part z = part v
  refine phantomFree_of_helly4 hσ0 hσN (helly4_of_patch B
    (fun z1 z2 z3 b1 b2 b3 d12 d13 d23 => absurd (hc.card (part v) z1 z2 z3 b1.1 b2.1 b3.1 b1.2 b2.2 b3.2 d12 d13 d23)
      (fun h => h)) (fun a0 a' h0 h' => ?_))
  have h0' := hl.sub _ h'
  -- en la parte y en los separadores el parche lee como `a'`
  have onS : ∀ {z : Nat}, (B z ∨ z ∈ S) → patch B a' a0 z = a' z := by
    intro z hz
    by_cases hb : B z
    · exact patch_in hb
    · rw [patch_out hb]
      rcases hz with hz | hz
      · exact absurd hz hb
      · exact hsep a0 a' h0 h0' z hz
  -- cada cláusula: entera fuera de la parte, o entera en la parte y los separadores
  have split : ∀ c ∈ φ.clauses, (∀ z, ClVar c z → ¬ B z) ∨ (∀ z, ClVar c z → B z ∨ z ∈ S) := by
    intro c hc'
    by_cases hex : ∃ z, ClVar c z ∧ B z
    · obtain ⟨z, hz, hbz⟩ := hex
      refine Or.inr (fun z' hz' => ?_)
      by_cases hs : z' ∈ S
      · exact Or.inr hs
      · exact Or.inl ⟨hs, (hc.cl c hc' z' z hz' hz hs hbz.1).trans hbz.2⟩
    · exact Or.inl (fun z hz hb => hex ⟨z, hz, hb⟩)
  have cl1 : ∀ {c : Clause}, ClVar c c.l1.v := Or.inl rfl
  have cl2 : ∀ {c : Clause}, ClVar c c.l2.v := Or.inr (Or.inl rfl)
  have cl3 : ∀ {c : Clause}, ClVar c c.l3.v := Or.inr (Or.inr rfl)
  have hP0 : P0 (patch B a' a0) := by
    refine p0_of_sources hl ⟨a0, h0⟩ (fun z => ?_) (fun c hc' => ?_)
    · by_cases hb : B z
      · exact ⟨a', h0', patch_in hb⟩
      · exact ⟨a0, h0, patch_out hb⟩
    · rcases split c hc' with ho | hi
      · exact ⟨a0, h0, patch_out (ho _ cl1), patch_out (ho _ cl2), patch_out (ho _ cl3)⟩
      · exact ⟨a', h0', onS (hi _ cl1), onS (hi _ cl2), onS (hi _ cl3)⟩
  have hBv : B v := ⟨hvS, rfl⟩
  refine p_of_sources hl hP0 (fun h => by rw [hv] at h; cases h) (fun z hz => ?_)
  rw [hv] at hz; cases hz
  refine ⟨⟨a', h', patch_in hBv⟩, fun c hc' hcv => ?_⟩
  rcases split c hc' with ho | hi
  · exact absurd hBv (ho v hcv)
  · exact ⟨a', h', onS (hi _ cl1), onS (hi _ cl2), onS (hi _ cl3)⟩

/-- **Volver a fijar una variable que todas las ramas leen igual**: sin familias fantasma. -/
theorem phantomFree_fixedVar {v : Nat} {r : NodeId} (hv : stepVar φ σ = some v)
    (hagree : ∀ a b, P0 a → P0 b → a v = b v) (hσ0 : 0 ≤ σ) (hσN : σ < N) :
    PhantomFree φ P0 (fun a => P0 a ∧ selOfAssign φ a σ = r) N σ := by
  intro R Tf hrefl hsymm hsw23 hsw12 hsteps hpair htrio hb2 hb3 hanch
  have hS : PhStruct φ P0 N R Tf := ⟨hrefl, hsymm, hsw23, hsw12, hsteps, hpair, htrio, hb2, hb3⟩
  -- si hay estructura, una de sus parejas da una rama que elige `r`, y entonces todas lo eligen
  have all : (∃ y w, R y w) → ∀ a, P0 a → selOfAssign φ a σ = r := by
    rintro ⟨y, w, hyw⟩ a ha
    obtain ⟨c, hc, _, _⟩ := pairs_of_struct hσ0 hσN hS hanch y w hyw
    exact (sel_eq_of_var (fun z hz => by rw [hv] at hz; cases hz; exact hagree a c ha hc.1)).trans hc.2
  refine ⟨fun y w hyw => ?_, fun x u w hxu hxw huw n1 n2 n3 hn => ?_⟩
  · obtain ⟨a, ha, h1, h2⟩ := hb2 y w hyw
    exact ⟨a, ⟨ha, all ⟨y, w, hyw⟩ a ha⟩, h1, h2⟩
  · obtain ⟨a, ha, h1, h2, h3⟩ := hb3 x u w hxu hxw huw n1 n2 n3 hn
    exact ⟨a, ⟨ha, all ⟨x, u, hxu⟩ a ha⟩, h1, h2, h3⟩

-- ============================================================
-- Lecturas buenas, para cualquier predicado
-- ============================================================

/-- Cada elección cumple `Good` con las anteriores. -/
def GoodAlongG (Good : List NodeId → NodeId → Prop) : List NodeId → List NodeId → Prop
  | _, [] => True
  | R0, r :: rs => Good R0 r ∧ GoodAlongG Good (R0 ++ [r]) rs

/-- **`reading_inv_on` para cualquier predicado de elecciones buenas.** -/
theorem reading_inv_gen {T : Int} {P : Assign → Prop} (Good : List NodeId → NodeId → Prop)
    (hH : ∀ R0 r, (∀ x ∈ R0, 1 ≤ x.step ∧ x.step < T) → 1 ≤ r.step → r.step < T → Good R0 r →
      PhantomFree φ (Pinned φ P R0) (fun a => Pinned φ P R0 a ∧ selOfAssign φ a r.step = r) T r.step)
    {g g' : GPathB} {R : List NodeId} (hr : Reading g R g') : ∀ R0, (∀ x ∈ R0, 1 ≤ x.step ∧ x.step < T) →
      GoodAlongG Good R0 R → RInv φ T (Pinned φ P R0) g → RInv φ T (Pinned φ P (R0 ++ R)) g' := by
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

-- ============================================================
-- El lector por separadores
-- ============================================================

/-- La variable que lee el paso de una elección. -/
def pinVar (φ : Cnf) (r : NodeId) : Option Nat := stepVar φ r.step

/-- **Separadores primero**: la elección `i`-ésima, mientras quedan separadores, lee el separador `S[i]`. -/
def SepFirst (φ : Cnf) (S : List Nat) (R : List NodeId) : Prop :=
  ∀ (i : Nat) (x : NodeId), i < S.length → R[i]? = some x → pinVar φ x = S[i]?

/-- Las elecciones de `R0` son los primeros separadores, en orden. -/
def SepPrefix (φ : Cnf) (S : List Nat) (R0 : List NodeId) : Prop :=
  ∀ (i : Nat) (x : NodeId), R0[i]? = some x → pinVar φ x = S[i]?

/-- **T2, la hipótesis que queda**: fijar el separador `S[k]` con los anteriores fijados no deja familias fantasma. -/
def SepPinFree (φ : Cnf) (S : List Nat) (T : Int) : Prop :=
  ∀ (k : NodeId) (R0 : List NodeId) (r : NodeId) (s : Nat),
    SepPrefix φ S R0 → S[R0.length]? = some s → pinVar φ r = some s → 1 ≤ r.step → r.step < T →
    PhantomFree φ (Pinned φ (SolE φ T k) R0) (fun a => Pinned φ (SolE φ T k) R0 a ∧ selOfAssign φ a r.step = r) T r.step

/-- Una elección buena del lector por separadores: el separador que toca, o cualquier cosa con todos fijados. -/
def SepGood (φ : Cnf) (S : List Nat) (R0 : List NodeId) (r : NodeId) : Prop :=
  (∃ s, SepPrefix φ S R0 ∧ S[R0.length]? = some s ∧ pinVar φ r = some s) ∨
    (∀ s ∈ S, ∃ x ∈ R0, pinVar φ x = some s)

/-- **Separadores primero da una lectura buena.** -/
theorem goodAlong_of_sepFirst (S : List Nat) : ∀ (R R0 : List NodeId), SepFirst φ S (R0 ++ R) →
    GoodAlongG (SepGood φ S) R0 R := by
  intro R
  induction R with
  | nil => intro _ _; trivial
  | cons r rs ih =>
    intro R0 h
    refine ⟨?_, ih (R0 ++ [r]) (by rw [List.append_assoc]; exact h)⟩
    by_cases hlt : R0.length < S.length
    · -- el separador que toca
      left
      refine ⟨S[R0.length], fun i x hx => ?_, List.getElem?_eq_getElem hlt, ?_⟩
      · have hi : i < R0.length := by
          rcases Nat.lt_or_ge i R0.length with h' | h'
          · exact h'
          · rw [List.getElem?_eq_none h'] at hx; cases hx
        exact h i x (by omega) (by rw [List.getElem?_append_left hi]; exact hx)
      · rw [← List.getElem?_eq_getElem hlt]
        exact h R0.length r hlt (by rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
    · -- todos los separadores ya están en `R0`
      right
      intro s hs
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
      have hi0 : i < R0.length := by omega
      refine ⟨R0[i], List.getElem_mem hi0, ?_⟩
      rw [h i R0[i] hi (by rw [List.getElem?_append_left hi0, List.getElem?_eq_getElem hi0]),
        List.getElem?_eq_getElem hi]

/-- Las ramas que eligen los colores de `R0` leen igual la variable de cada uno. -/
theorem agree_of_pins {P : Assign → Prop} {R0 : List NodeId} {s : Nat} (h : ∃ x ∈ R0, pinVar φ x = some s) :
    ∀ a b, Pinned φ P R0 a → Pinned φ P R0 b → a s = b s := by
  intro a b ha hb
  obtain ⟨x, hx, hxs⟩ := h
  exact var_eq_of_sel ((ha.2 x hx).trans (hb.2 x hx).symm) s hxs

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **T3: el lector por separadores no se atasca**, con las líneas, una cobertura por separadores y T2: toda lectura
que empieza por los separadores en el orden de `S` deja un estado válido que lleva la rama de una asignación que
satisface `φ` y coincide con todas las elecciones. -/
theorem reader_sep_on {S : List Nat} {part : Nat → Nat} (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T)
    (hc : SepCover φ S part) (h2 : SepPinFree φ S (stepCount φ)) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') (hsf : SepFirst φ S R) :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) := by
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
  -- cada elección buena, sin familias fantasma
  have hH : ∀ R0 r, (∀ x ∈ R0, 1 ≤ x.step ∧ x.step < stepCount φ) → 1 ≤ r.step → r.step < stepCount φ →
      SepGood φ S R0 r → PhantomFree φ (Pinned φ (SolE φ (stepCount φ) kv.1) R0)
        (fun a => Pinned φ (SolE φ (stepCount φ) kv.1) R0 a ∧ selOfAssign φ a r.step = r) (stepCount φ) r.step := by
    intro R0 r _ hr1 hrT hg
    rcases hg with ⟨s, hpre, hs, hrs⟩ | hall
    · exact h2 kv.1 R0 r s hpre hs hrs hr1 hrT
    · cases hv : stepVar φ r.step with
      | none => exact phantomFree_none (locPair_read _ kv.1 R0 r) hv (by omega) hrT
      | some v =>
        by_cases hvS : v ∈ S
        · exact phantomFree_fixedVar hv (agree_of_pins (hall v hvS)) (by omega) hrT
        · exact phantomFree_pinnedSepCover (locPair_read _ kv.1 R0 r) hc hv hvS
            (fun a b ha hb s hs => agree_of_pins (hall s hs) a b ha hb) (by omega) hrT
  have hfin := reading_inv_gen (SepGood φ S) hH hr [] (fun x hx => absurd hx List.not_mem_nil)
    (goodAlong_of_sepFirst S R [] (by rw [List.nil_append]; exact hsf)) h0
  rw [List.nil_append] at hfin
  refine ⟨hfin.valid, ?_⟩
  obtain ⟨q, hq, _⟩ := exists_alive_at hfin.valid (k := 0) (Int.le_refl 0) (by rw [hfin.step]; exact hpos)
  obtain ⟨a, ha, _, _⟩ := hfin.snd.1 q q (adj_refl _ _ hq)
  exact ⟨a, sat_of_validUpTo ha.1.1, ha.2, hfin.comp a ha⟩

end MachineOn

end AbsSatBingo.Model

-- ============================================================
-- `chain4_cross` con el lector por separadores
-- ============================================================

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

/-- Las partes de `chain4_cross` sin sus separadores `x5, x6, x7`: `{x0, x2}`, `{x4}`, `{x1}`, `{x3, x8}`. -/
def partChain4Cross (z : Nat) : Nat :=
  if z = 0 ∨ z = 2 then 0 else if z = 4 then 1 else if z = 1 then 2 else if z = 3 ∨ z = 8 then 3 else z + 10

theorem partChain4Cross_cases {z p : Nat} (h : partChain4Cross z = p) :
    (p = 0 ∧ (z = 0 ∨ z = 2)) ∨ (p = 1 ∧ z = 4) ∨ (p = 2 ∧ z = 1) ∨ (p = 3 ∧ (z = 3 ∨ z = 8)) ∨ p = z + 10 := by
  unfold partChain4Cross at h
  by_cases h1 : z = 0 ∨ z = 2
  · rw [if_pos h1] at h; exact Or.inl ⟨h.symm, h1⟩
  rw [if_neg h1] at h
  by_cases h2 : z = 4
  · rw [if_pos h2] at h; exact Or.inr (Or.inl ⟨h.symm, h2⟩)
  rw [if_neg h2] at h
  by_cases h3 : z = 1
  · rw [if_pos h3] at h; exact Or.inr (Or.inr (Or.inl ⟨h.symm, h3⟩))
  rw [if_neg h3] at h
  by_cases h4 : z = 3 ∨ z = 8
  · rw [if_pos h4] at h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.symm, h4⟩)))
  rw [if_neg h4] at h
  exact Or.inr (Or.inr (Or.inr (Or.inr h.symm)))

theorem sepCover_chain4Cross : SepCover chain4Cross [5, 6, 7] partChain4Cross := by
  refine ⟨fun c hc z z' hz hz' hzS hz'S => ?_, fun p z1 z2 z3 _ _ _ h1 h2 h3 d12 d13 d23 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hzS hz'S
    simp only [chain4Cross, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp only [ClVar] at hz hz' <;>
      rcases hz with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl <;> simp_all [partChain4Cross]
  · rcases partChain4Cross_cases h1 with ⟨e1, a1⟩ | ⟨e1, a1⟩ | ⟨e1, a1⟩ | ⟨e1, a1⟩ | e1 <;>
    rcases partChain4Cross_cases h2 with ⟨e2, a2⟩ | ⟨e2, a2⟩ | ⟨e2, a2⟩ | ⟨e2, a2⟩ | e2 <;>
    rcases partChain4Cross_cases h3 with ⟨e3, a3⟩ | ⟨e3, a3⟩ | ⟨e3, a3⟩ | ⟨e3, a3⟩ | e3 <;> omega

namespace MachineOn

open GPathB Driver Machine

/-- **T2 en `chain4_cross`**: fijar un separador, con lo que sea fijado antes, por los lemas de separador. -/
theorem sepPinFree_chain4Cross : SepPinFree chain4Cross [5, 6, 7] (stepCount chain4Cross) := by
  intro k R0 r s _ hs hrs hr1 hrT
  have hs' : s = 5 ∨ s = 6 ∨ s = 7 := by
    have := List.mem_of_getElem? hs
    simpa using this
  exact phantomFree_of_struct4 (locPair_read _ k R0 r) hrs (struct4_chain4Cross_sep hs') (by omega) hrT
    (by unfold stepCount midFusion; omega)

/-- **El lector por separadores no se atasca en `chain4_cross`**, sin ninguna hipótesis. -/
theorem reader_sep_chain4Cross {kv : NodeId × GPathB} (hkv : kv ∈ runM .on chain4Cross) {R : List NodeId}
    {g' : GPathB} (hr : Reading kv.2 R g') (hsf : SepFirst chain4Cross [5, 6, 7] R) :
    g'.isValid = true ∧ ∃ a, Sat a chain4Cross ∧ (∀ r ∈ R, selOfAssign chain4Cross a r.step = r) ∧
      CT g' (pidOfAssign chain4Cross a) :=
  reader_sep_on bounded_chain4Cross
    (fun T hT => phantomAtW_of_phantomAt (phantomAt_of_chain4L2 bounded_chain4Cross chain4L2_chain4Cross T hT))
    sepCover_chain4Cross sepPinFree_chain4Cross hkv hr hsf

end MachineOn

end AbsSatBingo.Model
