-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnWinRead.lean
import AbsSatBingo.Model.ForbidOnChainOrdI

/-!
# El lector por ventanas

El lector fija **ventanas**: el nodo del tercer paso de una cláusula, cuyo id lleva la cadena abuelo, padre, hijo, fija
los tres literales de la cláusula a la vez. Aquí cada ventana se modela como las tres elecciones de sus nodos de copia
(cada paso lee una variable), primero las de los separadores y después las de dentro: las mismas asignaciones que el
nodo de ventana, con un review tras cada elección.

* **`NearSep φ S part v s`**: el separador `s` comparte una cláusula con la parte de `v`.
* **T1 local, `phantomFree_pinnedNear`**: fijar una variable de dentro solo pide que las ramas lean igual los
  separadores que tocan su parte, no todos (como `phantomFree_pinnedSepCover`, con la misma cuenta del parche).
* **`SepPinAny φ S T`**: fijar un separador sin familias fantasma, **con cualquier cosa fijada antes**.
* **`WinGood`**: una elección de dentro llega con los separadores de su parte ya fijados.
* **`reader_win_on`**: con las líneas, una cobertura por separadores y `SepPinAny`, toda lectura buena deja un estado
  válido con la rama de una solución que coincide con todas las elecciones.
* **Las ventanas**: `WinSeq` (cada ventana, las variables de una cláusula con los separadores primero) y `OneWin` (la
  parte de dentro de cada variable está en una sola cláusula) dan una lectura buena (`goodAlong_of_winSeq`).
* **Las cadenas en orden** (`ChainOrdN`): `sepPinAny_of_local` (la bisección con los extremos de la cadena libres no
  mira lo fijado antes), `oneWin_of_chainOrd`, y **`reader_win_of_chainOrd`**: el lector por ventanas no se atasca, en
  cualquier orden de las ventanas, sin hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- **El separador `s` toca la parte de `v`**: comparte una cláusula con una variable de dentro de esa parte. -/
def NearSep (φ : Cnf) (S : List Nat) (part : Nat → Nat) (v s : Nat) : Prop :=
  ∃ c ∈ φ.clauses, ClVar c s ∧ ∃ z, ClVar c z ∧ z ∉ S ∧ part z = part v

namespace GPathB

open Driver Machine MachineOn

variable {P0 P : Assign → Prop} {N σ : Int}

/-- **T1 local**: con los separadores que tocan la parte de `v` fijados, fijar `v` no deja familias fantasma. -/
theorem phantomFree_pinnedNear {S : List Nat} {part : Nat → Nat} (hl : LocPair φ P0 P σ) (hc : SepCover φ S part)
    {v : Nat} (hv : stepVar φ σ = some v) (hvS : v ∉ S)
    (hsep : ∀ a b, P0 a → P0 b → ∀ s ∈ S, NearSep φ S part v s → a s = b s)
    (hσ0 : 0 ≤ σ) (hσN : σ < N) : PhantomFree φ P0 P N σ := by
  let B : Nat → Prop := fun z => z ∉ S ∧ part z = part v
  refine phantomFree_of_helly4 hσ0 hσN (helly4_of_patch B
    (fun z1 z2 z3 b1 b2 b3 d12 d13 d23 => absurd (hc.card (part v) z1 z2 z3 b1.1 b2.1 b3.1 b1.2 b2.2 b3.2 d12 d13 d23)
      (fun h => h)) (fun a0 a' h0 h' => ?_))
  have h0' := hl.sub _ h'
  -- cada cláusula: entera fuera de la parte, o con una variable de la parte y el resto en la parte o en `S`
  have split : ∀ c ∈ φ.clauses, (∀ z, ClVar c z → ¬ B z) ∨
      ((∃ z0, ClVar c z0 ∧ B z0) ∧ ∀ z, ClVar c z → B z ∨ z ∈ S) := by
    intro c hc'
    by_cases hex : ∃ z, ClVar c z ∧ B z
    · obtain ⟨z, hz, hbz⟩ := hex
      refine Or.inr ⟨⟨z, hz, hbz⟩, fun z' hz' => ?_⟩
      by_cases hs : z' ∈ S
      · exact Or.inr hs
      · exact Or.inl ⟨hs, (hc.cl c hc' z' z hz' hz hs hbz.1).trans hbz.2⟩
    · exact Or.inl (fun z hz hb => hex ⟨z, hz, hb⟩)
  -- en una cláusula que toca la parte, el parche lee como `a'`
  have onS : ∀ {c : Clause}, c ∈ φ.clauses → (∃ z0, ClVar c z0 ∧ B z0) → ∀ {z : Nat}, ClVar c z → (B z ∨ z ∈ S) →
      patch B a' a0 z = a' z := by
    intro c hc' ⟨z0, hz0, hb0⟩ z hzc hz
    by_cases hb : B z
    · exact patch_in hb
    · rw [patch_out hb]
      rcases hz with hz | hz
      · exact absurd hz hb
      · exact hsep a0 a' h0 h0' z hz ⟨c, hc', hzc, z0, hz0, hb0.1, hb0.2⟩
  have cl1 : ∀ {c : Clause}, ClVar c c.l1.v := Or.inl rfl
  have cl2 : ∀ {c : Clause}, ClVar c c.l2.v := Or.inr (Or.inl rfl)
  have cl3 : ∀ {c : Clause}, ClVar c c.l3.v := Or.inr (Or.inr rfl)
  have hP0 : P0 (patch B a' a0) := by
    refine p0_of_sources hl ⟨a0, h0⟩ (fun z => ?_) (fun c hc' => ?_)
    · by_cases hb : B z
      · exact ⟨a', h0', patch_in hb⟩
      · exact ⟨a0, h0, patch_out hb⟩
    · rcases split c hc' with ho | ⟨hx, hi⟩
      · exact ⟨a0, h0, patch_out (ho _ cl1), patch_out (ho _ cl2), patch_out (ho _ cl3)⟩
      · exact ⟨a', h0', onS hc' hx cl1 (hi _ cl1), onS hc' hx cl2 (hi _ cl2), onS hc' hx cl3 (hi _ cl3)⟩
  have hBv : B v := ⟨hvS, rfl⟩
  refine p_of_sources hl hP0 (fun h => by rw [hv] at h; cases h) (fun z hz => ?_)
  rw [hv] at hz; cases hz
  refine ⟨⟨a', h', patch_in hBv⟩, fun c hc' hcv => ?_⟩
  rcases split c hc' with ho | ⟨hx, hi⟩
  · exact absurd hBv (ho v hcv)
  · exact ⟨a', h', onS hc' hx cl1 (hi _ cl1), onS hc' hx cl2 (hi _ cl2), onS hc' hx cl3 (hi _ cl3)⟩

/-- **Un separador se fija sin familias fantasma, con cualquier cosa fijada antes.** -/
def SepPinAny (φ : Cnf) (S : List Nat) (T : Int) : Prop :=
  ∀ (k : NodeId) (R0 : List NodeId) (r : NodeId) (s : Nat), s ∈ S → pinVar φ r = some s → 1 ≤ r.step → r.step < T →
    PhantomFree φ (Pinned φ (SolE φ T k) R0) (fun a => Pinned φ (SolE φ T k) R0 a ∧ selOfAssign φ a r.step = r) T r.step

/-- **Una elección buena del lector por ventanas**: si lee una variable de dentro, los separadores que tocan su parte
ya están fijados. -/
def WinGood (φ : Cnf) (S : List Nat) (part : Nat → Nat) (R0 : List NodeId) (r : NodeId) : Prop :=
  ∀ v, pinVar φ r = some v → v ∉ S → ∀ s ∈ S, NearSep φ S part v s → ∃ x ∈ R0, pinVar φ x = some s

-- ============================================================
-- Las ventanas dan una lectura buena
-- ============================================================

theorem goodAlong_append {G : List NodeId → NodeId → Prop} : ∀ (l1 l2 R0 : List NodeId), GoodAlongG G R0 l1 →
    GoodAlongG G (R0 ++ l1) l2 → GoodAlongG G R0 (l1 ++ l2) := by
  intro l1
  induction l1 with
  | nil => intro l2 R0 _ h; rw [List.append_nil] at h; exact h
  | cons r rs ih =>
    intro l2 R0 h1 h2
    exact ⟨h1.1, ih l2 (R0 ++ [r]) h1.2 (by rw [List.append_assoc]; exact h2)⟩

/-- Cada elección es buena con todo lo que contenga lo anterior. -/
theorem goodAlong_all {G : List NodeId → NodeId → Prop} : ∀ (l R0 : List NodeId),
    (∀ R1 r, r ∈ l → (∀ x ∈ R0, x ∈ R1) → G R1 r) → GoodAlongG G R0 l := by
  intro l
  induction l with
  | nil => intro _ _; trivial
  | cons r rs ih =>
    intro R0 h
    refine ⟨h R0 r List.mem_cons_self (fun _ hx => hx), ih (R0 ++ [r]) (fun R1 r' hr' hsub => ?_)⟩
    exact h R1 r' (List.mem_cons_of_mem _ hr') (fun x hx => hsub x (List.mem_append_left _ hx))

/-- **Una ventana**: las elecciones de una cláusula `c`, primero las de separadores (`ws`, que leen todos los
separadores de `c`) y después las de sus variables (`wi`). -/
def WinOk (φ : Cnf) (S : List Nat) (w : List NodeId) : Prop :=
  ∃ c ∈ φ.clauses, ∃ ws wi, w = ws ++ wi ∧ (∀ x ∈ ws, ∃ s ∈ S, pinVar φ x = some s) ∧
    (∀ x ∈ wi, ∃ z, pinVar φ x = some z ∧ ClVar c z) ∧ (∀ s ∈ S, ClVar c s → ∃ x ∈ ws, pinVar φ x = some s)

/-- **La parte de dentro de cada variable está en una sola cláusula** (salvo cláusulas con los mismos
separadores). -/
def OneWin (φ : Cnf) (S : List Nat) (part : Nat → Nat) : Prop :=
  ∀ c ∈ φ.clauses, ∀ c' ∈ φ.clauses, ∀ v z, ClVar c v → v ∉ S → ClVar c' z → z ∉ S → part z = part v →
    ∀ s, ClVar c' s → ClVar c s

theorem goodAlong_win {S : List Nat} {part : Nat → Nat} (h1 : OneWin φ S part) {w : List NodeId} (hw : WinOk φ S w)
    (R0 : List NodeId) : GoodAlongG (WinGood φ S part) R0 w := by
  obtain ⟨c, hc, ws, wi, rfl, hws, hwi, hcov⟩ := hw
  refine goodAlong_append ws wi R0 (goodAlong_all ws R0 (fun R1 r hr _ v hv hvS => ?_))
    (goodAlong_all wi (R0 ++ ws) (fun R1 r hr hsub v hv hvS s hs hn => ?_))
  · obtain ⟨s, hs, hrs⟩ := hws r hr
    rw [hrs] at hv; cases hv
    exact absurd hs hvS
  · obtain ⟨z, hrz, hcz⟩ := hwi r hr
    rw [hrz] at hv
    have e : v = z := (Option.some.inj hv).symm
    subst e
    obtain ⟨c', hc', hsc', z', hz'c', hz'S, hpz⟩ := hn
    obtain ⟨x, hx, hxs⟩ := hcov s hs (h1 c hc c' hc' v z' hcz hvS hz'c' hz'S hpz s hsc')
    exact ⟨x, hsub x (List.mem_append_right _ hx), hxs⟩

/-- **Una sucesión de ventanas es una lectura buena**, en cualquier orden de las ventanas. -/
theorem goodAlong_of_winSeq {S : List Nat} {part : Nat → Nat} (h1 : OneWin φ S part) :
    ∀ (W : List (List NodeId)) (R0 : List NodeId), (∀ w ∈ W, WinOk φ S w) →
      GoodAlongG (WinGood φ S part) R0 W.flatten := by
  intro W
  induction W with
  | nil => intro _ _; trivial
  | cons w W ih =>
    intro R0 hW
    rw [List.flatten_cons]
    exact goodAlong_append w W.flatten R0 (goodAlong_win h1 (hW w List.mem_cons_self) R0)
      (ih (R0 ++ w) (fun w' hw' => hW w' (List.mem_cons_of_mem _ hw')))

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **El lector por ventanas no se atasca**, con las líneas, una cobertura por separadores y `SepPinAny`: toda lectura
buena deja un estado válido que lleva la rama de una asignación que satisface `φ` y coincide con todas las elecciones. -/
theorem reader_win_on {S : List Nat} {part : Nat → Nat} (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T)
    (hc : SepCover φ S part) (h2 : SepPinAny φ S (stepCount φ)) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') (hg : GoodAlongG (WinGood φ S part) [] R) :
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
  have hH : ∀ R0 r, (∀ x ∈ R0, 1 ≤ x.step ∧ x.step < stepCount φ) → 1 ≤ r.step → r.step < stepCount φ →
      WinGood φ S part R0 r → PhantomFree φ (Pinned φ (SolE φ (stepCount φ) kv.1) R0)
        (fun a => Pinned φ (SolE φ (stepCount φ) kv.1) R0 a ∧ selOfAssign φ a r.step = r) (stepCount φ) r.step := by
    intro R0 r _ hr1 hrT hg
    cases hv : stepVar φ r.step with
    | none => exact phantomFree_none (locPair_read _ kv.1 R0 r) hv (by omega) hrT
    | some v =>
      by_cases hvS : v ∈ S
      · exact h2 kv.1 R0 r v hvS hv hr1 hrT
      · exact phantomFree_pinnedNear (locPair_read _ kv.1 R0 r) hc hv hvS
          (fun a b ha hb s hs hn => agree_of_pins (hg v hv hvS s hs hn) a b ha hb) (by omega) hrT
  have hfin := reading_inv_gen (WinGood φ S part) hH hr [] (fun x hx => absurd hx List.not_mem_nil) hg h0
  rw [List.nil_append] at hfin
  refine ⟨hfin.valid, ?_⟩
  obtain ⟨q, hq, _⟩ := exists_alive_at hfin.valid (k := 0) (Int.le_refl 0) (by rw [hfin.step]; exact hpos)
  obtain ⟨a, ha, _, _⟩ := hfin.snd.1 q q (adj_refl _ _ hq)
  exact ⟨a, sat_of_validUpTo ha.1.1, ha.2, hfin.comp a ha⟩

end MachineOn

end AbsSatBingo.Model

/-! ## Las cadenas en orden -/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {n : Nat} {zone sv : Nat → Nat}

/-- **Un separador, con cualquier cosa fijada antes**: la bisección con los extremos de la cadena libres no mira lo
fijado. -/
theorem sepPinAny_of_local (D : ChainN φ n zone) (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    (hL : LocalReads φ n zone sv) {S : List Nat} (hS : ∀ z, z ∈ S ↔ SepN n zone z) :
    SepPinAny φ S (stepCount φ) := by
  intro k R0 r s hs hrs hr1 hrT
  have hsep := (hS s).mp hs
  unfold SepN at hsep
  have hmid : midFusion φ < stepCount φ := by unfold stepCount midFusion; omega
  exact phantomFree_bisectN (locPair_read (φ := φ) (stepCount φ) k R0 r) D hsv hrs (away_of_local hL (zone s - n))
    hmid (by omega) (m := zone s - n) (a := 0) (b := n) (by omega) (by omega) (by omega) (Nat.le_refl _)
    (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) (by omega) hrT

/-- **En una cadena en orden, la parte de dentro de cada variable está en una sola cláusula**: la de su bloque. -/
theorem oneWin_of_chainOrd (C : ChainOrdN φ n zone sv) {S : List Nat} (hS : ∀ z, z ∈ S ↔ SepN n zone z) :
    OneWin φ S (partN n zone) := by
  intro c hc c' hc' v z hcv hvS hcz hzS hpz s _
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
  obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.mp hc'
  have hin : i < n := by rw [← C.len]; exact (List.getElem?_eq_some_iff.mp hi).1
  have hin' : i' < n := by rw [← C.len]; exact (List.getElem?_eq_some_iff.mp hi').1
  have ev := blk_inner hin (clIn_var (C.blk i c hi) hcv) (fun h => hvS ((hS v).mpr h))
  have ez := blk_inner hin' (clIn_var (C.blk i' c' hi') hcz) (fun h => hzS ((hS z).mpr h))
  unfold partN at hpz
  rw [ev, ez, if_pos hin, if_pos hin'] at hpz
  subst hpz
  rw [hi] at hi'
  cases hi'
  assumption

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {φ : Cnf} {n : Nat} {zone sv : Nat → Nat}

/-- **El lector por ventanas no se atasca en ninguna cadena en orden**, de cualquier longitud, con cualquier lectura
buena: sin hipótesis. -/
theorem reader_good_of_chainOrd (hb : Bounded φ) (C : ChainOrdN φ n zone sv) {ord : List Nat}
    (hord : ∀ q ∈ ord, 1 ≤ q ∧ q < n) (hall : ∀ q, 1 ≤ q → q < n → q ∈ ord) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on φ) {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g')
    (hg : GoodAlongG (WinGood φ (ord.map sv) (partN n zone)) [] R) :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) := by
  have hS := mem_sep_iff' C.D C.hsv hord hall
  exact reader_win_on hb (fun T hT => phantomAtW_of_phantomAt (phantomAt_of_chainOrd hb C T hT))
    (sepCover_of_chainN C.D (fun _ hc => ordM_cl C.toM hc) hS)
    (sepPinAny_of_local C.D C.hsv (localReads_of C.hsv C.num C.lit) hS) hkv hr hg

/-- **El lector por ventanas en una cadena en orden**: toda sucesión de ventanas, en cualquier orden, deja un estado
válido con la rama de una solución que coincide con todas las elecciones. -/
theorem reader_win_of_chainOrd (hb : Bounded φ) (C : ChainOrdN φ n zone sv) {ord : List Nat}
    (hord : ∀ q ∈ ord, 1 ≤ q ∧ q < n) (hall : ∀ q, 1 ≤ q → q < n → q ∈ ord) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on φ) {W : List (List NodeId)} {g' : GPathB} (hr : Reading kv.2 W.flatten g')
    (hW : ∀ w ∈ W, WinOk φ (ord.map sv) w) :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ W.flatten, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_good_of_chainOrd hb C hord hall hkv hr
    (goodAlong_of_winSeq (oneWin_of_chainOrd C (mem_sep_iff' C.D C.hsv hord hall)) W [] hW)

end MachineOn

end AbsSatBingo.Model

/-! ## `chain12_order` con el lector por ventanas -/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace MachineOn

open GPathB Driver Machine

/-- **El lector por ventanas no se atasca en `chain12_order`**, en cualquier orden de las ventanas. -/
theorem reader_win_chain12O {kv : NodeId × GPathB} (hkv : kv ∈ runM .on chain12O) {W : List (List NodeId)}
    {g' : GPathB} (hr : Reading kv.2 W.flatten g') (hW : ∀ w ∈ W, WinOk chain12O ((List.range' 1 11).map sv12) w) :
    g'.isValid = true ∧ ∃ a, Sat a chain12O ∧ (∀ r ∈ W.flatten, selOfAssign chain12O a r.step = r) ∧
      CT g' (pidOfAssign chain12O a) :=
  reader_win_of_chainOrd bounded_chain12O chainOrd_chain12O
    (fun q hq => by rw [List.mem_range'_1] at hq; omega)
    (fun q h1 h2 => by rw [List.mem_range'_1]; omega) hkv hr hW

end MachineOn

end AbsSatBingo.Model
