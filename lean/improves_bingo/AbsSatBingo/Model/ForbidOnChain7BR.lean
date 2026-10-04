-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain7BR.lean
import AbsSatBingo.Model.ForbidOnChain7BC

/-!
# Un lado libre de cuatro con el otro abierto, y el lector en bisección de siete bloques

Al fijar el primer separador de siete bloques, los lados son de tres y cuatro, los dos libres. El caso que no cerraba:
el lado de cuatro no lee ninguno de sus separadores y el otro está abierto, de modo que, al conservar el nodo del
otro, solo hay dos caras de `P` y el bloque de `v` (fusionado con su vecino) pide una en dos variables.

**El arreglo: el rango pesa el doble en el lado largo** (`2·frR + frL`). Cuando el lado largo no lee ninguno, su
testigo (la ventana del bloque `m + 2`) se usa con las caras completas, sin conservar nada: sus subtriangulaciones
bajan el lado largo de `4` a `≤ 2` (cuatro de rango), y el otro, que sube a lo sumo de `1` a `4`, no lo compensa
(`side_right4free`). El otro lado toma sus fuentes de esas mismas caras (todas de `P`) o de su propio testigo, con caras
completas también (el lado largo ya está en su máximo y no puede subir).

* **`phantomFree_bisectL`**: como `phantomFree_bisect`, con el lado derecho de hasta cuatro bloques libre.
* **`BisectOrderL`**, **`sepPinFree_of_bisectL`**: T2 con esos lados.
* **`bisectOrderL_7`**: `s3, s1, s2, s5, s4, s6` usa las ventanas de `B1`, `B4` y `B5`.
* **`reader_bisect_of_chain7BC`**: el lector en ese orden no se atasca en ninguna fórmula de la clase de siete bloques,
  sin hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop} {Nn σ : Int}

section Long

variable {n : Nat} {zone : Nat → Nat}

/-- **Fijar `v` con el lado derecho de hasta cuatro bloques libre.** -/
theorem phantomFree_bisectL (hl : LocPair φ P0 P σ) (D : ChainN φ n zone) {sv : Nat → Nat}
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    {v : Nat} (hv : stepVar φ σ = some v) {m a b : Nat}
    (hwR : m + 3 ≤ b → ∃ lam, 0 ≤ lam ∧ lam < Nn ∧ ReadsAt φ lam (sv (m + 1)) ∧ ReadsAt φ lam (sv (m + 2)))
    (hwR4 : m + 4 ≤ b → b = n → WinAt φ Nn (sv (m + 2)) (sv (m + 3)))
    (hwL : a + 3 ≤ m → ∃ lam, 0 ≤ lam ∧ lam < Nn ∧ ReadsAt φ lam (sv (m - 1)) ∧ ReadsAt φ lam (sv (m - 2)))
    (hmid : midFusion φ < Nn)
    (hzv : zone v = n + m) (hm1 : 1 ≤ m) (ham : a < m) (hmb : m < b) (hbn : b ≤ n)
    (hfa : 1 ≤ a → ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + a → c z = c' z)
    (hfb : FixedEnd n zone P0 b) (hLL : m - a ≤ 3 ∨ (1 ≤ a ∧ m - a ≤ 4))
    (hLR : b - m ≤ 3 ∨ (b < n ∧ b - m ≤ 4) ∨ (b = n ∧ b - m = 4))
    (hσ0 : 0 ≤ σ) (hσN : σ < Nn) : PhantomFree φ P0 P Nn σ := by
  have SR : SideData φ n zone sv P0 Nn m b := ⟨D, hsv, hwR, hmid, hm1, hmb, hbn, hfb, by
    rcases hLR with h | ⟨_, h⟩ | ⟨_, h⟩ <;> omega⟩
  have SL := sideData_left (P0 := P0) D hsv hwL hmid ham (by omega) hfa hLL
  have eqsv : ∀ {k z}, 1 ≤ k → k < n → zone z = n + k → z = sv k := fun {k z} a c h =>
    D.sep1 k a c z (sv k) h (hsv k a c)
  refine phantomFree_of_descent hσ0 hσN
    (fun x u w => 2 * frS φ sv m b x.id.step u.id.step w.id.step +
      frS φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step)
    (fun R Tf hS hanch x u w t ih => ?_)
  obtain ⟨a0, h0, hx0, hu0, hw0⟩ := t.b3 hS
  have hRp := frS_pos (φ := φ) (sv := sv) (i := x.id.step) (j := u.id.step) (l := w.id.step) hmb
  have hLp := frS_pos (φ := φ) (sv := fun k => sv (n - k)) (i := x.id.step) (j := u.id.step) (l := w.id.step)
    SL.mb
  have hRle := frS_le (φ := φ) (sv := sv) (m := m) (b := b) (i := x.id.step) (j := u.id.step) (l := w.id.step)
  have hLle := frS_le (φ := φ) (sv := fun k => sv (n - k)) (m := n - m) (b := n - a) (i := x.id.step)
    (j := u.id.step) (l := w.id.step)
  have h4L : frS φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step = 4 → n - a < n := fun h => by
    rcases hLL with h' | ⟨h', _⟩ <;> omega
  have pvC : ∀ {Q : Assign → Prop} {lam : Int}, SideCap φ P0 P Q x.id.step u.id.step w.id.step lam a0 →
      InW φ x.id.step u.id.step w.id.step v → ∃ c, P c ∧ c v = a0 v := by
    intro Q lam C hwv
    obtain ⟨d, qP, _, ag⟩ := C.pP (le1_eq v)
    exact ⟨d, qP, ag v rfl hwv⟩
  have glue := fun {sL sR : Nat → Assign}
      (OL : SideOut φ n (zoneRevN n zone) P0 P x.id.step u.id.step w.id.step a0 (n - m) (n - a) sL)
      (OR : SideOut φ n zone P0 P x.id.step u.id.step w.id.step a0 m b sR) hpv =>
    glue_sides_tri hl D hv hzv hm1 ham hmb hbn hfa hfb h0 hx0 hu0 hw0 OL OR hpv
  -- el otro lado abierto, con su testigo: el derecho no sube
  have ihL := fun (hL : 2 ≤ frS φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step) x' u' w'
      (t' : Tri R Tf x' u' w')
      (ha' : frS φ (fun k => sv (n - k)) (n - m) (n - a) x'.id.step u'.id.step w'.id.step ≤ 1)
      (hc' : frS φ sv m b x'.id.step u'.id.step w'.id.step ≤ frS φ sv m b x.id.step u.id.step w.id.step) =>
    ih x' u' w' t' (by omega)
  by_cases hmax : frS φ sv m b x.id.step u.id.step w.id.step = 4 ∧ b = n
  · -- **el lado largo sin leer ninguno**: su testigo, con caras completas
    obtain ⟨hf4, hbN⟩ := hmax
    have hb4 : b = m + 4 := by omega
    obtain ⟨lam, l0, lN, r2, r3⟩ := hwR4 (by omega) hbN
    have hno := frS_un (φ := φ) (sv := sv) SR.L4 (k := 2) (by omega) (i := x.id.step) (j := u.id.step)
      (l := w.id.step) (by omega)
    obtain ⟨Q, C, hQ⟩ := capFull hl hS t hx0 hu0 hw0 l0 lN r2 hno (fun x' u' w' t' h' => ih x' u' w' t' (by
      have a1 := frS_of (φ := φ) SR.L4 (k := 2) (by omega) (i := x'.id.step) (j := u'.id.step) (l := w'.id.step) h'
      have a2 := frS_le (φ := φ) (sv := fun k => sv (n - k)) (m := n - m) (b := n - a) (i := x'.id.step)
        (j := u'.id.step) (l := w'.id.step)
      rcases hLL with h | ⟨_, h⟩ <;> omega))
    have hun : ∀ k z, 1 ≤ k → k < 4 → zone z = n + (m + k) → ¬ InW φ x.id.step u.id.step w.id.step z :=
      fun k z a c hz => by rw [eqsv (by omega) (by omega) hz]; exact frS_un SR.L4 a (by omega)
    obtain ⟨sR, OR⟩ := side_right4free D hm1 (by omega) h0 C hQ
      (fun z hz => by rw [eqsv (by omega) (by omega) hz]; exact r2)
      (fun z hz => by rw [eqsv (by omega) (by omega) hz]; exact r3) hun
    rw [← hb4] at OR
    by_cases hL : 2 ≤ frS φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step
    · obtain ⟨⟨sL, OL⟩, _⟩ := open_cap hl hS t h0 hx0 hu0 hw0 SL SR hL h4L (ihL hL)
      exact glue OL OR (pvC C)
    · obtain ⟨d, qQ, ag⟩ := C.p0 SL.no3_res
      obtain ⟨sL, OL⟩ := side_res SL (by omega) h0 (hQ d qQ) (C.q0 d qQ) ag
      exact glue OL OR (pvC C)
  · -- lo de siempre, con el rango pesado
    have h4R : frS φ sv m b x.id.step u.id.step w.id.step = 4 → b < n := fun h => by
      rcases hLR with h' | ⟨h', _⟩ | ⟨h', _⟩
      · omega
      · exact h'
      · exact absurd ⟨h, h'⟩ hmax
    have ihR := fun (hR : 2 ≤ frS φ sv m b x.id.step u.id.step w.id.step) x' u' w' (t' : Tri R Tf x' u' w')
        (ha' : frS φ sv m b x'.id.step u'.id.step w'.id.step ≤ 1)
        (hc' : frS φ (fun k => sv (n - k)) (n - m) (n - a) x'.id.step u'.id.step w'.id.step ≤
          frS φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step) =>
      ih x' u' w' t' (by omega)
    by_cases hR : 2 ≤ frS φ sv m b x.id.step u.id.step w.id.step
    · obtain ⟨⟨sR, OR⟩, Q, lam, C, ex⟩ := open_cap hl hS t h0 hx0 hu0 hw0 SR SL hR h4R (ihR hR)
      by_cases hL : 2 ≤ frS φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step
      · obtain ⟨⟨sL, OL⟩, _⟩ := open_cap hl hS t h0 hx0 hu0 hw0 SL SR hL h4L (ihL hL)
        exact glue OL OR (pvC C)
      · obtain ⟨d, qP, q0, ag⟩ := res_of_cap SL (by omega) C ex
        obtain ⟨sL, OL⟩ := side_res SL (by omega) h0 qP q0 ag
        exact glue OL OR (pvC C)
    · by_cases hL : 2 ≤ frS φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step
      · obtain ⟨⟨sL, OL⟩, Q, lam, C, ex⟩ := open_cap hl hS t h0 hx0 hu0 hw0 SL SR hL h4L (ihL hL)
        obtain ⟨d, qP, q0, ag⟩ := res_of_cap SR (by omega) C ex
        obtain ⟨sR, OR⟩ := side_res SR (by omega) h0 qP q0 ag
        exact glue OL OR (pvC C)
      · rcases faces_sigma hS hanch hσ0 hσN t h0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
        · exact h
        obtain ⟨dR, qR, agR⟩ := F.pick SR.no3_res
        obtain ⟨dL, qL, agL⟩ := F.pick SL.no3_res
        obtain ⟨sR, OR⟩ := side_res SR (by omega) h0 qR (hl.sub _ qR) agR
        obtain ⟨sL, OL⟩ := side_res SL (by omega) h0 qL (hl.sub _ qL) agL
        exact glue OL OR (fun hwv => (F.inw hwv).elim (fun e => ⟨c1, F.q1, e⟩) (fun e => ⟨c2, F.q2, e⟩))

end Long

/-! ## T2 con un lado largo -/

/-- **Un orden de bisección con lados largos a la derecha**: el lado derecho puede ser de cuatro bloques libre (con
la ventana del bloque `q + 2`). -/
def BisectOrderL (n : Nat) (ord : List Nat) (Win : Nat → Prop) : Prop :=
  ∀ (k q : Nat), ord[k]? = some q → 1 ≤ q ∧ q < n ∧ ∃ a b : Nat, a < q ∧ q < b ∧ b ≤ n ∧
    (a = 0 ∨ ∃ i : Nat, i < k ∧ ord[i]? = some a) ∧ (b = n ∨ ∃ i : Nat, i < k ∧ ord[i]? = some b) ∧
    (q - a ≤ 3 ∨ (1 ≤ a ∧ q - a ≤ 4)) ∧ (b - q ≤ 3 ∨ (b < n ∧ b - q ≤ 4) ∨ (b = n ∧ b - q = 4)) ∧
    (q + 3 ≤ b → Win (q + 1)) ∧ (q + 4 ≤ b → b = n → Win (q + 2)) ∧ (a + 3 ≤ q → Win (q - 2))

theorem bisectOrder_of_L {n : Nat} {ord : List Nat} {Win : Nat → Prop} (h : BisectOrderL n ord Win) :
    ∀ (k q : Nat), ord[k]? = some q → 1 ≤ q ∧ q < n := fun k q hq => ⟨(h k q hq).1, (h k q hq).2.1⟩

section T2L

variable {n : Nat} {zone : Nat → Nat}

/-- **T2 con lados largos a la derecha.** -/
theorem sepPinFree_of_bisectL (D : ChainN φ n zone) {sv : Nat → Nat}
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k) {Win : Nat → Prop}
    (hw : ∀ p, Win p → ∃ lam, 0 ≤ lam ∧ lam < stepCount φ ∧ ReadsAt φ lam (sv p) ∧ ReadsAt φ lam (sv (p + 1)))
    {ord : List Nat} (hord : BisectOrderL n ord Win) : SepPinFree φ (ord.map sv) (stepCount φ) := by
  intro k R0 r s hpre hs hrs hr1 hrT
  rw [List.getElem?_map] at hs
  cases hq : ord[R0.length]? with
  | none => rw [hq] at hs; cases hs
  | some q =>
    rw [hq] at hs
    have hsq : sv q = s := Option.some.inj hs
    obtain ⟨q1, qn, a, b, ha, hb, hbn, hA, hB, hLL, hLR, hWR, hWR4, hWL⟩ := hord _ _ hq
    have hl := locPair_read (φ := φ) (stepCount φ) k R0 r
    have hv : stepVar φ r.step = some (sv q) := by rw [hsq]; exact hrs
    have fixOf : ∀ c, (c = 0 ∨ ∃ i, i < R0.length ∧ ord[i]? = some c) → 1 ≤ c → c < n →
        ∀ y y', Pinned φ (SolE φ (stepCount φ) k) R0 y → Pinned φ (SolE φ (stepCount φ) k) R0 y' →
          ∀ z, zone z = n + c → y z = y' z := by
      intro c hc h1 h2 y y' qy qy' z hz
      rcases hc with h | ⟨i, hi, ho⟩
      · omega
      rw [D.sep1 c h1 h2 z (sv c) hz (hsv c h1 h2)]
      exact fixed_of_prefix hpre hi ho y y' qy qy'
    have hmid : midFusion φ < stepCount φ := by unfold stepCount midFusion; omega
    refine phantomFree_bisectL hl D hsv hv (fun h => hw (q + 1) (hWR h))
      (fun h h' => by
        obtain ⟨lam, l0, lN, r1, r2⟩ := hw (q + 2) (hWR4 h h')
        exact ⟨lam, l0, lN, r1, by rw [show q + 3 = q + 2 + 1 by omega]; exact r2⟩)
      (fun h => by
        obtain ⟨lam, l0, lN, r1, r2⟩ := hw (q - 2) (hWL h)
        exact ⟨lam, l0, lN, by rw [show q - 1 = q - 2 + 1 by omega]; exact r2, r1⟩) hmid (hsv q q1 qn) q1 ha hb hbn
      (fun h1 => fixOf a hA h1 (by omega)) (fun h2 => fixOf b ?_ (by omega) h2) hLL hLR (by omega) hrT
    rcases hB with h | h
    · omega
    · exact Or.inr h

end T2L

/-- **El orden para siete bloques**: `s3` (lados de tres y cuatro libres), y luego cada mitad. Usa las ventanas de
`B1`, `B4` y `B5`. -/
theorem bisectOrderL_7 : BisectOrderL 7 [3, 1, 2, 5, 4, 6] (fun p => p = 1 ∨ p = 4 ∨ p = 5) := by
  intro k q h
  rcases k with _ | _ | _ | _ | _ | _ | k
  · have : q = 3 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 0, 7, by omega, by omega, by omega, Or.inl rfl, Or.inl rfl, Or.inl (by omega),
      Or.inr (Or.inr ⟨rfl, by omega⟩), fun _ => Or.inr (Or.inl rfl), fun _ _ => Or.inr (Or.inr rfl),
      fun _ => Or.inl rfl⟩
  · have : q = 1 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 0, 3, by omega, by omega, by omega, Or.inl rfl, Or.inr ⟨0, by omega, rfl⟩,
      Or.inl (by omega), Or.inl (by omega), fun h => absurd h (by omega), fun h => absurd h (by omega),
      fun h => absurd h (by omega)⟩
  · have : q = 2 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 1, 3, by omega, by omega, by omega, Or.inr ⟨1, by omega, rfl⟩,
      Or.inr ⟨0, by omega, rfl⟩, Or.inl (by omega), Or.inl (by omega), fun h => absurd h (by omega),
      fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  · have : q = 5 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 3, 7, by omega, by omega, by omega, Or.inr ⟨0, by omega, rfl⟩, Or.inl rfl,
      Or.inl (by omega), Or.inl (by omega), fun h => absurd h (by omega), fun h => absurd h (by omega),
      fun h => absurd h (by omega)⟩
  · have : q = 4 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 3, 5, by omega, by omega, by omega, Or.inr ⟨0, by omega, rfl⟩,
      Or.inr ⟨3, by omega, rfl⟩, Or.inl (by omega), Or.inl (by omega), fun h => absurd h (by omega),
      fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  · have : q = 6 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 5, 7, by omega, by omega, by omega, Or.inr ⟨3, by omega, rfl⟩, Or.inl rfl,
      Or.inl (by omega), Or.inl (by omega), fun h => absurd h (by omega), fun h => absurd h (by omega),
      fun h => absurd h (by omega)⟩
  · simp at h

variable {zone sv : Nat → Nat}

/-- **T2 para toda fórmula de la clase de siete bloques**, en el orden `s3, s1, s2, s5, s4, s6`. -/
theorem sepPinFree_of_chain7BC (C : Chain7BC φ zone sv) :
    SepPinFree φ ([3, 1, 2, 5, 4, 6].map sv) (stepCount φ) := by
  have h1 := C.cl (j := 1) (by omega)
  have h4 := C.cl (j := 4) (by omega)
  have h5 := C.cl (j := 5) (by omega)
  obtain ⟨a1, a2⟩ := C.w1 _ h1
  obtain ⟨a5, a6⟩ := C.w5 _ h4
  obtain ⟨b4, b5⟩ := C.w4 _ h5
  have kb : ∀ j, j < 7 → 0 ≤ clauseStep φ j 2 ∧ clauseStep φ j 2 < stepCount φ := fun j hj => by
    simp only [clauseStep, stepCount, C.len]; omega
  refine sepPinFree_of_bisectL C.D C.hsv (fun p hp => ?_) bisectOrderL_7
  rcases hp with rfl | rfl | rfl
  · exact ⟨clauseStep φ 1 2, (kb 1 (by omega)).1, (kb 1 (by omega)).2, readsAt_clause h1 a1,
      readsAt_clause h1 a2⟩
  · exact ⟨clauseStep φ 5 2, (kb 5 (by omega)).1, (kb 5 (by omega)).2,
      by rw [← b4]; exact readsAt_clause h5 (Or.inr (Or.inr rfl)), readsAt_clause h5 b5⟩
  · exact ⟨clauseStep φ 4 2, (kb 4 (by omega)).1, (kb 4 (by omega)).2, readsAt_clause h4 a5,
      readsAt_clause h4 a6⟩

/-- Toda cláusula de la clase está en un bloque. -/
theorem blocks_of_chain7BC (C : Chain7BC φ zone sv) : ∀ c ∈ φ.clauses, ∃ j, j < 7 ∧ ClIn (BlkN 7 zone j) c := by
  intro c hc
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
  have hjl : j < 7 := by
    rw [← C.len]
    by_cases h : j < φ.clauses.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  refine ⟨ord7 j, ?_, C.blk j c hj⟩
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ord7]

/-- La lista de separadores del orden de siete. -/
theorem mem_sep7 (C : Chain7BC φ zone sv) : ∀ z, z ∈ [3, 1, 2, 5, 4, 6].map sv ↔ SepN 7 zone z := by
  intro z
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    have : 1 ≤ q ∧ q < 7 := by simp at hq; omega
    unfold SepN; rw [C.hsv q this.1 this.2]; omega
  · intro h
    unfold SepN at h
    have e := C.D.sep1 (zone z - 7) (by omega) (by omega) z (sv (zone z - 7)) (by omega)
      (C.hsv _ (by omega) (by omega))
    rw [e]
    refine List.mem_map.mpr ⟨_, ?_, rfl⟩
    have : zone z - 7 = 1 ∨ zone z - 7 = 2 ∨ zone z - 7 = 3 ∨ zone z - 7 = 4 ∨ zone z - 7 = 5 ∨ zone z - 7 = 6 := by
      omega
    rcases this with e | e | e | e | e | e <;> rw [e] <;> simp

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {φ : Cnf} {zone sv : Nat → Nat}

/-- **El lector en orden de bisección no se atasca en ninguna cadena de siete bloques de la clase**: toda lectura que
empieza por `s3, s1, s2, s5, s4, s6` deja un estado válido con la rama de una solución que coincide con todas las
elecciones. Sin hipótesis. -/
theorem reader_bisect_of_chain7BC (hb : Bounded φ) (C : Chain7BC φ zone sv) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on φ) {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g')
    (hsf : SepFirst φ ([3, 1, 2, 5, 4, 6].map sv) R) :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_sep_on hb (fun T hT => phantomAtW_of_phantomAt (phantomAt_of_chain7BC hb C T hT))
    (sepCover_of_chainN C.D (blocks_of_chain7BC C) (mem_sep7 C)) (sepPinFree_of_chain7BC C) hkv hr hsf

end MachineOn

end AbsSatBingo.Model
