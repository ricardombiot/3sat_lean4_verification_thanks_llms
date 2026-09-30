-- lean/improves_bingo/AbsSatBingo/Model/CliqueSound.lean
import AbsSatBingo.Model.PreClause

/-!
# La solidez de las familias fantasma con pins

**`AvoidV`**: la familia de una entrada de la línea, fijada con `R`, no prohíbe ningún trío de una selección válida
que termina en su clave y concuerda con `R`. Es `ForbidSound` para toda camarilla (no solo las ramas solución) y para
toda lista de pins. Vale para toda camarilla porque en la máquina ninguna mezcla los dos lados de un join: la
selección la lleva la llegada de su propio remitente (completitud, `steps_has_sel`), y en ese lado el trío es
triángulo y no está prohibido.

No usa `PinJoinSplitAll` ni ninguna forma de exactitud: solo la construcción de las familias, `FBelow` y la
completitud de la línea.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace PreClause

open GPathB Driver Machine CliqueSplit

variable {φ : Cnf}

/-- **La forma de una entrada, con sus remitentes**: en el caso de una sola llegada, es el único que envía. -/
theorem entry_shape2 {line : Line} (Fs : NodeId → FamT)
    (hlen : line = [] ∨ (∃ a, line = [a]) ∨ (∃ a b, line = [a, b])) (hnd : (line.map (·.1)).Nodup)
    {E : NodeId × GPathB} (hE : E ∈ advance φ line) :
    (∃ kv ∈ line, Sends φ kv E.1 ∧ E.2 = arrOf φ kv E.1 ∧ famsNext φ line Fs E.1 = shiftF φ Fs kv E.1 ∧
      ∀ c ∈ line, Sends φ c E.1 → c = kv) ∨
    (∃ a ∈ line, ∃ b ∈ line, a.1 ≠ b.1 ∧ Sends φ a E.1 ∧ Sends φ b E.1 ∧
      E.2 = doJoin (arrOf φ a E.1) (arrOf φ b E.1) ∧
      famsNext φ line Fs E.1 = joinFam (arrOf φ a E.1) (arrOf φ b E.1) (shiftF φ Fs a E.1) (shiftF φ Fs b E.1) ∧
      ∀ c ∈ line, c = a ∨ c = b) := by
  have h1 := lookup_of_mem (advance_nodup φ line) hE
  rw [lookup_advance] at h1
  rcases hlen with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · simp at h1
  · by_cases ha : Sends φ a E.1
    · simp only [List.foldl, stepS, ha, if_true, Option.some.injEq] at h1
      refine Or.inl ⟨a, by simp, ha, h1.symm, ?_, fun c hc _ => by simpa using hc⟩
      simp only [famsNext, List.foldl, stepF, ha, if_true]
    · simp [List.foldl, stepS, ha] at h1
  · have hab : a.1 ≠ b.1 := by simpa using hnd
    have hc2 : ∀ c ∈ [a, b], c = a ∨ c = b := fun c hc => by simpa using hc
    by_cases ha : Sends φ a E.1 <;> by_cases hb : Sends φ b E.1
    · simp only [List.foldl, stepS, ha, hb, if_true, Option.some.injEq] at h1
      refine Or.inr ⟨a, by simp, b, by simp, hab, ha, hb, h1.symm, ?_, hc2⟩
      simp only [famsNext, List.foldl, stepF, ha, hb, if_true]
    · simp only [List.foldl, stepS, ha, hb, if_true, if_false, Option.some.injEq] at h1
      refine Or.inl ⟨a, by simp, ha, h1.symm, ?_, fun c hc hs => ?_⟩
      · simp only [famsNext, List.foldl, stepF, ha, hb, if_true, if_false]
      · rcases hc2 c hc with rfl | rfl
        · rfl
        · exact absurd hs hb
    · simp only [List.foldl, stepS, ha, hb, if_true, if_false, Option.some.injEq] at h1
      refine Or.inl ⟨b, by simp, hb, h1.symm, ?_, fun c hc hs => ?_⟩
      · simp only [famsNext, List.foldl, stepF, ha, hb, if_true, if_false]
      · rcases hc2 c hc with rfl | rfl
        · exact absurd hs ha
        · rfl
    · simp [List.foldl, stepS, ha, hb] at h1

-- ============================================================
-- El invariante
-- ============================================================

/-- **`AvoidV`**: en la línea `n`, la familia de cada entrada fijada con `R` esquiva toda selección válida que termina
en su clave y concuerda con `R`. -/
def AvoidV (φ : Cnf) (n : Nat) (L : Line) (Fs : NodeId → FamT) : Prop :=
  ∀ kv ∈ L, ∀ R S, ValidSel φ n S → (S n).id = kv.1 → (∀ r ∈ R, Agrees ((n : Int) + 1) S r) →
    Avoids (Fs kv.1 R) ((n : Int) + 1) S

theorem avoidV_init : AvoidV φ 0 (init φ) (fun _ => botF) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h

/-- **La selección la lleva la entrada de su clave.** -/
theorem carried_sender (hbd : Bounded φ) (n : Nat) {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {S : Int → PathNodeId} (hv : ValidSel φ n S) (hid : (S n).id = kv.1) : Carried kv.2 S := by
  obtain ⟨_, _, hnd, _, _⟩ := line_facts hbd n
  obtain ⟨_, g, hf, hc⟩ := steps_has_sel n hv
  have hmem := List.mem_of_find?_eq_some hf
  have := eq_of_nodup_keys hnd hmem hkv (by rw [hid])
  rw [← this]; exact hc

/-- **Una llegada esquiva lo que esquivaba su remitente**: la selección concuerda con los requisitos del destino. -/
theorem avoid_arr {n : Nat} {L : Line} {Fs : NodeId → FamT} (hA : AvoidV φ n L Fs) {kv : NodeId × GPathB}
    (hkv : kv ∈ L) (hB : ∀ R, FBelow (Fs kv.1 R) ((n : Int) + 1)) {d : NodeId} {R : List NodeId}
    {S : Int → PathNodeId} (hv : ValidSel φ ((n : Int) + 1) S) (hd : (S ((n : Int) + 1)).id = d)
    (hid : (S n).id = kv.1) (hag : ∀ r ∈ R, Agrees ((n : Int) + 1 + 1) S r) :
    Avoids (shiftF φ Fs kv d R) ((n : Int) + 1 + 1) S := by
  have hreq : ∀ r ∈ reqOf φ d, Agrees ((n : Int) + 1) S r := by
    intro r hr h0 h1
    exact hv.req ((n : Int) + 1) (by omega) (Int.le_refl _) r (by rw [hd]; exact hr) h0 h1
  have hih := hA kv hkv (reqOf φ d ++ R) S (hv.mono (by omega)) hid (by
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact hreq r h
    · exact fun h0 h1 => hag r h h0 (by omega))
  intro i j k h0 h1 h2 h3 h4 h5 hf
  obtain ⟨si, sj, sk⟩ := hB _ _ _ _ hf
  rw [hv.step i h0 (by omega)] at si
  rw [hv.step j h2 (by omega)] at sj
  rw [hv.step k h4 (by omega)] at sk
  exact hih i j k h0 si h2 sj h4 sk hf

/-- **`AvoidV` pasa a la línea siguiente.** -/
theorem avoidV_next (hbd : Bounded φ) (n : Nat) {Fs : NodeId → FamT}
    (hL : LInv φ ((n : Int) + 1) (steps φ n (init φ)) Fs) (hA : AvoidV φ n (steps φ n (init φ)) Fs) :
    AvoidV φ (n + 1) (advance φ (steps φ n (init φ))) (famsNext φ (steps φ n (init φ)) Fs) := by
  intro E hE R S hv hid hag
  have hv' : ValidSel φ ((n : Int) + 1) S := by simpa using hv
  have hid' : (S ((n : Int) + 1)).id = E.1 := by simpa using hid
  have hag' : ∀ r ∈ R, Agrees ((n : Int) + 1 + 1) S r := by
    intro r hr; have := hag r hr; simpa using this
  rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
  -- el remitente de la selección
  obtain ⟨hl, _, _, _, _⟩ := line_facts hbd n
  obtain ⟨_, g0, hf, hc0⟩ := steps_has_sel n (hv'.mono (by omega))
  have hmem := List.mem_of_find?_eq_some hf
  let kv0 : NodeId × GPathB := ((S n).id, g0)
  have hok0 := hl _ hmem
  have hcar := carried_arrival (by omega) hv' hok0 hc0
  rw [hid'] at hcar
  have hson : E.1 ∈ sonsOfMap φ kv0.1 := by
    have := hv'.son ((n : Int) + 1) (by omega) (Int.le_refl _)
    rw [show (n : Int) + 1 - 1 = n by omega, hid'] at this; exact this
  have hs0 : Sends φ kv0 E.1 := ⟨hson, isValid_of_carried hcar⟩
  have hcarP : Carried (pinF (arrOf φ kv0 E.1) R) S := by
    refine carried_pinF hcar (fun r hr => ?_)
    show Agrees (arrOf φ kv0 E.1).current_step S r
    rw [(stateOk_arr hok0 hs0).step]; exact hag' r hr
  have hcs0 : (pinF (arrOf φ kv0 E.1) R).current_step = (n : Int) + 1 + 1 := by
    rw [step_pinF, (stateOk_arr hok0 hs0).step]
  have havoid0 : Avoids (shiftF φ Fs kv0 E.1 R) ((n : Int) + 1 + 1) S :=
    avoid_arr hA hmem (fun R => by have := (hL.good kv0 hmem).below R; rwa [hok0.step] at this) hv' hid' rfl hag'
  rcases entry_shape2 Fs (line_cases hL.nodup hL.keys) hL.nodup hE with
    ⟨kv, hkv, _, _, hfm, huniq⟩ | ⟨a, ha, b, hb, _, hsa, hsb, _, hfm, hall⟩
  · rw [hfm, ← huniq kv0 hmem hs0]; exact havoid0
  · rw [hfm]
    intro i j k h0 h1 h2 h3 h4 h5 hF
    have hns := not_sideForbids hcarP (by rw [hcs0]; exact havoid0) h0 (by rw [hcs0]; exact h1) h2
      (by rw [hcs0]; exact h3) h4 (by rw [hcs0]; exact h5)
    unfold joinFam at hF
    rcases hall kv0 hmem with h | h
    · -- el remitente es `a`
      rw [h] at hns hcarP havoid0
      have hvA : (pinF (arrOf φ a E.1) R).isValid = true := isValid_of_carried hcarP
      by_cases hvB : (pinF (arrOf φ b E.1) R).isValid = true
      · simp only [hvA, hvB, if_true] at hF
        exact hns hF.2.2.2.2.2.2.1
      · simp only [hvA, hvB, if_true] at hF
        exact havoid0 i j k h0 h1 h2 h3 h4 h5 hF
    · rw [h] at hns hcarP havoid0
      have hvB : (pinF (arrOf φ b E.1) R).isValid = true := isValid_of_carried hcarP
      by_cases hvA : (pinF (arrOf φ a E.1) R).isValid = true
      · simp only [hvA, hvB, if_true] at hF
        exact hns hF.2.2.2.2.2.2.2
      · simp only [hvA] at hF
        exact havoid0 i j k h0 h1 h2 h3 h4 h5 hF

/-- **`AvoidV` en toda la línea**, con el invariante de línea de cada paso. -/
theorem avoidV_steps (hbd : Bounded φ)
    (hL : ∀ n : Nat, LInv φ ((n : Int) + 1) (steps φ n (init φ)) (famsAt φ n)) :
    ∀ n : Nat, AvoidV φ n (steps φ n (init φ)) (famsAt φ n) := by
  intro n
  induction n with
  | zero => exact avoidV_init
  | succ n ih =>
    rw [steps_succ]
    exact avoidV_next hbd n (hL n) ih

-- ============================================================
-- `HMixed` desde la existencia de camarillas
-- ============================================================

/-- **`HClq`** (en la línea `m + 1`): un trío de una cadena de una entrada de la línea siguiente (fijada y válida) que
es triángulo en un remitente de otra entrada y triángulo en alguna de las llegadas que formaron ese remitente (fijados
y válidos) está en una selección válida que termina en la clave de la entrada y concuerda con los pins. Sin familias.
Medido: `probe_hnewcl.jl` (`PURE=1`), 68 000/68 000 en camarillas de las llegadas de la entrada. -/
def HClq (φ : Cnf) (m : Nat) : Prop :=
  ∀ E ∈ advance φ (steps φ (m + 1) (init φ)), ¬ IsNeg φ E.1 →
    ∀ kv ∈ steps φ (m + 1) (init φ), ∀ d₁, d₁ ≠ E.1 → Sends φ kv d₁ →
    ∀ R, (pinF E.2 R).isValid = true →
    ∀ C j p q r, OnChain3 (pinF E.2 R) C j p q r →
      (pinF kv.2 R).isValid = true → Tri (pinF kv.2 R) (C p) (C q) (C r) →
      ∀ c ∈ steps φ m (init φ), Sends φ c kv.1 → (pinF (arrOf φ c kv.1) R).isValid = true →
        Tri (pinF (arrOf φ c kv.1) R) (C p) (C q) (C r) →
      ∃ S, ValidSel φ ((m + 2 : Nat) : Int) S ∧ (S ((m + 2 : Nat) : Int)).id = E.1 ∧
        (∀ r' ∈ R, Agrees (((m + 2 : Nat) : Int) + 1) S r') ∧
        ∃ i k l, 0 ≤ i ∧ i < ((m + 2 : Nat) : Int) + 1 ∧ 0 ≤ k ∧ k < ((m + 2 : Nat) : Int) + 1 ∧
          0 ≤ l ∧ l < ((m + 2 : Nat) : Int) + 1 ∧ S i = C p ∧ S k = C q ∧ S l = C r

/-- **`HClq` da `HMixed`**: un trío de un solo lado está en una selección válida de la entrada, y la familia de la
entrada la esquiva (`AvoidV`), así que no lo prohíbe; uno prohibido es, pues, mezclado. -/
theorem mixed_of_clq (hbd : Bounded φ) (m : Nat) (hC : HClq φ m)
    (hA : AvoidV φ (m + 2) (advance φ (steps φ (m + 1) (init φ)))
      (famsNext φ (steps φ (m + 1) (init φ)) (famsAt φ (m + 1)))) : HMixed φ m := by
  intro E hE hneg kv hkv d₁ hd₁ hs R hvE C j p q r hoc hf hvD htri
  by_cases hpure : ∃ c ∈ steps φ m (init φ), Sends φ c kv.1 ∧ (pinF (arrOf φ c kv.1) R).isValid = true ∧
      Tri (pinF (arrOf φ c kv.1) R) (C p) (C q) (C r)
  · exfalso
    obtain ⟨c, hc, hsc, hvc, htc⟩ := hpure
    obtain ⟨S, hv, hid, hag, i, k, l, h0, h1, h2, h3, h4, h5, hi, hk, hl⟩ :=
      hC E hE hneg kv hkv d₁ hd₁ hs R hvE C j p q r hoc hvD htri c hc hsc hvc htc
    have := hA E hE R S hv hid hag i k l h0 h1 h2 h3 h4 h5
    rw [hi, hk, hl] at this
    exact this hf
  · have hnp : ∀ c ∈ steps φ m (init φ), Sends φ c kv.1 → (pinF (arrOf φ c kv.1) R).isValid = true →
        ¬ Tri (pinF (arrOf φ c kv.1) R) (C p) (C q) (C r) :=
      fun c hc hsc hvc htc => hpure ⟨c, hc, hsc, hvc, htc⟩
    obtain ⟨hl, _, hnd, hls, _⟩ := line_facts hbd m
    have hk : ∀ kv ∈ steps φ m (init φ), kv.1 ∈ mapNodes φ m := by
      intro kv hkv
      have := (hls kv hkv).2
      rwa [(hl kv hkv).key, show (m : Int) + 1 - 1 = m by omega] at this
    have hkv' : kv ∈ advance φ (steps φ m (init φ)) := by rw [← steps_succ]; exact hkv
    rcases entry_shape2 (famsAt φ m) (line_cases hnd hk) hnd hkv' with
      ⟨kv', hkv'', hs', he, _, _⟩ | ⟨a, ha, b, hb, hab, hsa, hsb, _, _, _⟩
    · exfalso
      rw [he] at hvD htri
      exact hnp kv' hkv'' hs' hvD htri
    · exact ⟨a, ha, b, hb, hab, hsa, hsb, hnp a ha hsa, hnp b hb hsb⟩

/-- **La inducción con `AvoidV`**: como `lInv_stepsG`, pero `HNew` puede usar también la solidez de la línea. -/
theorem lInv_stepsA (hbd : Bounded φ) (hsp : ∀ n : Nat, HSplit φ (steps φ n (init φ)))
    (hnw : ∀ n : Nat, midFusion φ + 1 < (n : Int) + 1 → (n : Int) + 1 < fusionTop φ →
      LInv φ ((n : Int) + 1) (steps φ n (init φ)) (famsAt φ n) → AvoidV φ n (steps φ n (init φ)) (famsAt φ n) →
      HNew φ (steps φ n (init φ)) (famsAt φ n)) :
    ∀ n : Nat, LInv φ ((n : Int) + 1) (steps φ n (init φ)) (famsAt φ n) ∧
      ((n : Int) ≤ midFusion φ + 1 → ∀ kv ∈ steps φ n (init φ), NoTriF kv.2 (famsAt φ n kv.1)) ∧
      AvoidV φ n (steps φ n (init φ)) (famsAt φ n) := by
  intro n
  induction n with
  | zero =>
    exact ⟨lInv_init φ, fun _ kv _ R _ x y z _ hf => hf, avoidV_init⟩
  | succ n ih =>
    obtain ⟨ih, ihN, ihA⟩ := ih
    have hN' : (n : Int) + 1 ≤ midFusion φ + 1 →
        ∀ E ∈ advance φ (steps φ n (init φ)), NoTriF E.2 (famsNext φ (steps φ n (init φ)) (famsAt φ n) E.1) := by
      intro hn
      by_cases hpre : (n : Int) + 1 ≤ midFusion φ
      · exact noTri_next hbd n hpre ih (ihN (by omega)) (hsp n)
      · have hk : (n : Int) = midFusion φ := by omega
        refine noTri_next_single ih (ihN (by omega)) (fun a ha b hb => ?_)
        have e1 := ih.keys a ha
        have e2 := ih.keys b hb
        rw [show (n : Int) + 1 - 1 = midFusion φ by omega, mapNodes_fusion φ _ (Or.inr (Or.inl rfl)),
          List.mem_singleton] at e1 e2
        rw [e1, e2]
    have hnew : HNew φ (steps φ n (init φ)) (famsAt φ n) := by
      by_cases hpost : midFusion φ + 1 < (n : Int) + 1
      · by_cases htop : (n : Int) + 1 < fusionTop φ
        · exact hnw n hpost htop ih ihA
        · exact hnew_top (by omega) ih (by omega)
      · exact hnew_of_noTri (hN' (by omega))
    have hL := lInv_advance (by omega) ih (hsp n) hnew
    have hA' := avoidV_next hbd n ih ihA
    rw [steps_succ]
    refine ⟨?_, fun hn kv hkv => hN' (by push_cast at hn; omega) kv hkv, hA'⟩
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact hL

/-- **Las hipótesis sin familias**: `PinJoinSplitAll` en los joins de la máquina y `HClq` en las líneas de cláusula
con dos remitentes. -/
def HypsLiveLineQ (φ : Cnf) : Prop :=
  (∀ n : Nat, HSplit φ (steps φ n (init φ))) ∧
  (∀ m : Nat, midFusion φ + 1 < (m : Int) + 2 → (m : Int) + 2 < fusionTop φ → HClq φ m)

theorem lInv_stepsQ (hbd : Bounded φ) (H : HypsLiveLineQ φ) :
    ∀ n : Nat, LInv φ ((n : Int) + 1) (steps φ n (init φ)) (famsAt φ n) := by
  intro n
  refine (lInv_stepsA hbd H.1 (fun n h1 h2 hL hA => ?_) n).1
  cases n with
  | zero => exfalso; unfold midFusion at h1; omega
  | succ m =>
    have hL' : LInv φ ((m : Int) + 2) (steps φ (m + 1) (init φ)) (famsAt φ (m + 1)) := by
      rw [show (m : Int) + 2 = ((m + 1 : Nat) : Int) + 1 by push_cast; omega]; exact hL
    have hA2 := avoidV_next hbd (m + 1) hL hA
    exact hnew_of_mixed hbd m (mixed_of_clq hbd m (H.2 m (by push_cast at h1; omega) (by push_cast at h2; omega)) hA2)
      hL' (H.1 m)

-- ============================================================
-- HClq desde la completitud de camarillas
-- ============================================================

/-- **`TriClq`** (en la línea `m + 1`): un trío de una cadena viva de una entrada de la línea siguiente, fijada y
válida, está en una camarilla de la entrada que concuerda con los pins. Es la mitad difícil de «prohibido ⟺ en ninguna
camarilla» (la otra es la solidez, `AvoidV`), sin las premisas de remitentes de `HClq`. Medido en la zona de
cláusulas: `probe_triexact.jl` (150 000 triángulos, 0 excepciones). -/
def TriClq (φ : Cnf) (m : Nat) : Prop :=
  ∀ E ∈ advance φ (steps φ (m + 1) (init φ)), ¬ IsNeg φ E.1 →
    ∀ R, (pinF E.2 R).isValid = true →
    ∀ C j p q r, OnChain3 (pinF E.2 R) C j p q r →
      ∃ S, Carried E.2 S ∧ (∀ r' ∈ R, Agrees E.2.current_step S r') ∧
        ∃ i k l, 0 ≤ i ∧ i < E.2.current_step ∧ 0 ≤ k ∧ k < E.2.current_step ∧
          0 ≤ l ∧ l < E.2.current_step ∧ S i = C p ∧ S k = C q ∧ S l = C r

/-- **`TriClq` da `HClq`**: la camarilla de la entrada es una selección válida (`validSel_of_carried`) que termina en
la clave de la entrada (los nodos de la cima llevan su id, `TopDocsId`). -/
theorem clq_of_triClq (hbd : Bounded φ) (m : Nat) (hT : TriClq φ m) : HClq φ m := by
  intro E hE hneg _ _ _ _ _ R hvE C j p q r hoc _ _ _ _ _ _ _
  obtain ⟨S, hc, hag, i, k, l, h0, h1, h2, h3, h4, h5, hi, hk, hl⟩ := hT E hE hneg R hvE C j p q r hoc
  have hE' : E ∈ steps φ (m + 2) (init φ) := by rw [steps_succ]; exact hE
  obtain ⟨hlo, hent, _, hls, hml⟩ := line_facts hbd (m + 2)
  have hcs : E.2.current_step = ((m + 2 : Nat) : Int) + 1 := (hlo E hE').step
  have hv : ValidSel φ (E.2.current_step - 1) S :=
    validSel_of_carried hbd (hls E hE').1 (hml E hE') hc (by rw [hcs]; omega)
  rw [hcs, show ((m + 2 : Nat) : Int) + 1 - 1 = ((m + 2 : Nat) : Int) by omega] at hv
  have htop : (S ((m + 2 : Nat) : Int)).id = E.1 := by
    obtain ⟨n, hn, _, _⟩ := hc.node ((m + 2 : Nat) : Int) (by omega) (by rw [hcs]; omega)
    have hid := node?_id hn
    have := (hent E hE').2 n (node?_mem hn) (by rw [hid, hc.step _ (by omega) (by rw [hcs]; omega), hcs]; omega)
    rw [hid] at this; exact this
  refine ⟨S, hv, htop, fun r' hr => by rw [← hcs]; exact hag r' hr, i, k, l, h0, ?_, h2, ?_, h4, ?_, hi, hk, hl⟩ <;>
    omega

/-- Las hipótesis con `TriClq` en lugar de `HClq`. -/
def HypsLiveLineT (φ : Cnf) : Prop :=
  (∀ n : Nat, HSplit φ (steps φ n (init φ))) ∧
  (∀ m : Nat, midFusion φ + 1 < (m : Int) + 2 → (m : Int) + 2 < fusionTop φ → TriClq φ m)

theorem hypsQ_of_hypsT (hbd : Bounded φ) (H : HypsLiveLineT φ) : HypsLiveLineQ φ :=
  ⟨H.1, fun m h1 h2 => clq_of_triClq hbd m (H.2 m h1 h2)⟩

end PreClause

namespace SecLine

open GPathB Driver PreClause

/-- **La espina con tríos decide la satisfacibilidad** bajo `PinJoinSplitAll` en los joins de la máquina y `HClq` en
las líneas de cláusula con dos remitentes: todo trío de cadena de un solo lado está en una camarilla de la entrada. Las
hipótesis ya no mencionan las familias de tríos. -/
theorem spineVerdict_iff_of_clq {φ : Cnf} (hbd : Bounded φ) (H : HypsLiveLineQ φ) :
    SpineVerdict φ ↔ Satisfiable φ := by
  apply spineVerdict_iff_of_liveExt hbd
  intro kv hkv hval
  exact ⟨_, ((lInv_stepsQ hbd H (stepCount φ - 1).toNat).good kv hkv).live [] hval⟩

/-- **La espina con tríos decide la satisfacibilidad** bajo `PinJoinSplitAll` en los joins de la máquina y `TriClq` en
las líneas de cláusula: todo trío de una cadena viva de una entrada fijada está en una camarilla de la entrada que
concuerda con los pins. -/
theorem spineVerdict_iff_of_triClq {φ : Cnf} (hbd : Bounded φ) (H : HypsLiveLineT φ) :
    SpineVerdict φ ↔ Satisfiable φ :=
  spineVerdict_iff_of_clq hbd (hypsQ_of_hypsT hbd H)

end SecLine

end AbsSatBingo.Model
