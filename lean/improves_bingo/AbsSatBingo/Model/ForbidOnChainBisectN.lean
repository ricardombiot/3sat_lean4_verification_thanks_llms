-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainBisectN.lean
import AbsSatBingo.Model.ForbidOnChainLocal

/-!
# Fijar un separador con los dos lados abiertos, de cualquier longitud (lecturas locales)

Con `LocalReads`, en cada lado abierto el testigo del paso de variable de `t_1` y dos regiones (`side_two`, `c = 1`)
bastan: la región de `v` es **un solo bloque** (una variable de dentro), así que basta una cara de `P` en una variable, y
la sirven también las caras que conservan el nodo del otro lado. El otro lado no sube (su nodo se conserva) o ya está en
su máximo. El rango es la **suma** de los primeros separadores leídos (`frN`, sin tope): sin pesos ni límites de
longitud.

* **`SideDataN`**: un lado de cualquier longitud con lecturas locales.
* `readsA`, `readsB`: lo que leen las dos regiones (una variable, dos variables).
* `side_windowN`, `side_resN`, `res_of_capN`, `open_capN`: como en `ForbidOnChainBisect`, con `frN`.
* `localReads_rev`, `sideDataN_left`: el lado izquierdo, de la cadena al revés.
* **`phantomFree_bisectN`**.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop} {Nn σ : Int} {R : PathNodeId → PathNodeId → Prop} {Tf : Trios}

/-- **Lecturas locales a partir del bloque `m + 1`** (lo que pide un lado). -/
def LocalReadsFrom (φ : Cnf) (n : Nat) (zone sv : Nat → Nat) (m : Nat) : Prop :=
  ∀ (k : Int) (z p : Nat), m + 1 ≤ p → p + 1 < n → zone z = p → ReadsAt φ k z →
    ReadsAt φ k (sv p) ∨ ReadsAt φ k (sv (p + 1))

/-- **Lecturas locales lejos de `v`** (el separador `m`): en todos los bloques de en medio salvo los dos pegados a
`v`. -/
def LocalReadsAway (φ : Cnf) (n : Nat) (zone sv : Nat → Nat) (m : Nat) : Prop :=
  ∀ (k : Int) (z p : Nat), (p + 2 ≤ m ∨ m + 1 ≤ p) → 1 ≤ p → p + 1 < n → zone z = p → ReadsAt φ k z →
    ReadsAt φ k (sv p) ∨ ReadsAt φ k (sv (p + 1))

theorem away_of_local {φ : Cnf} {n : Nat} {zone sv : Nat → Nat} (hL : LocalReads φ n zone sv) (m : Nat) :
    LocalReadsAway φ n zone sv m := fun k z p _ h1 h2 hz hr => hL k z p h1 h2 hz hr

/-- **Un lado de cualquier longitud con lecturas locales.** -/
structure SideDataN (φ : Cnf) (n : Nat) (zone sv : Nat → Nat) (P0 : Assign → Prop) (Nn : Int) (m b : Nat) :
    Prop where
  D   : ChainN φ n zone
  hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k
  mid : midFusion φ < Nn
  m1  : 1 ≤ m
  mb  : m < b
  bn  : b ≤ n
  fix : FixedEnd n zone P0 b
  loc : LocalReadsFrom φ n zone sv m

section SideN

variable {n : Nat} {zone sv : Nat → Nat} {m b : Nat}

theorem SideDataN.eqsv (S : SideDataN φ n zone sv P0 Nn m b) {k z : Nat} (hk : 1 ≤ k) (hkn : k < n)
    (hz : zone z = n + k) : z = sv k :=
  S.D.sep1 k hk hkn z (sv k) hz (S.hsv k hk hkn)

theorem SideDataN.no3_res (S : SideDataN φ n zone sv P0 Nn m b) :
    No3 (fun z => zone z = m ∨ (m + 1 < b ∧ zone z = n + (m + 1))) := by
  have := S.mb; have := S.bn
  by_cases h : m + 1 < b
  · intro y1 y2 y3 b1 b2 b3
    exact no3_mid_sep S.D S.m1 (by omega) y1 y2 y3 (b1.imp id (·.2)) (b2.imp id (·.2)) (b3.imp id (·.2))
  · intro y1 y2 y3 b1 b2 b3
    exact no3_last S.D S.m1 (by omega) y1 y2 y3 (b1.resolve_right (fun h' => h h'.1))
      (b2.resolve_right (fun h' => h h'.1)) (b3.resolve_right (fun h' => h h'.1))

/-- La región de `v` lee a lo sumo una variable: es un bloque de en medio. -/
theorem readsA (S : SideDataN φ n zone sv P0 Nn m b) {i j l : Int} (hf : 2 ≤ frN φ sv m b i j l) :
    Le1 (fun z => (m ≤ zone z ∧ zone z < m + 1) ∧ InW φ i j l z) := by
  have := frN_le (φ := φ) (sv := sv) (i := i) (j := j) (l := l) S.mb
  have := S.bn
  exact fun z z' h h' => S.D.cardM m S.m1 (by omega) z z' (by omega) (by omega)

/-- **La otra región lee a lo sumo dos variables**: las del bloque `m + r - 1` y `t_r`. -/
theorem readsB (S : SideDataN φ n zone sv P0 Nn m b) {i j l : Int} (hf : 2 ≤ frN φ sv m b i j l) :
    No3 (fun z => ((m + 1 ≤ zone z ∧ zone z < m + frN φ sv m b i j l) ∨
      (m + frN φ sv m b i j l < b ∧ zone z = n + (m + frN φ sv m b i j l))) ∧ InW φ i j l z) := by
  have hle := frN_le (φ := φ) (sv := sv) (i := i) (j := j) (l := l) S.mb
  have hb := S.bn
  generalize hrd : frN φ sv m b i j l = r at hf hle
  have hun : ∀ k, 1 ≤ k → k < r → ¬ InW φ i j l (sv (m + k)) := fun k a c => by
    rw [← hrd] at c; exact frN_un a c
  have inner : ∀ {z}, m + 1 ≤ zone z → zone z + 2 ≤ m + r → ¬ InW φ i j l z := by
    rintro z h1 h2 ⟨k, k', hk, hw, hz⟩
    rcases S.loc k z (zone z) (by omega) (by omega) rfl ⟨k', hw, hz⟩ with h | h
    · refine hun (zone z - m) (by omega) (by omega) ?_
      rw [show m + (zone z - m) = zone z by omega]; exact inW_of_reads hk h
    · refine hun (zone z + 1 - m) (by omega) (by omega) ?_
      rw [show m + (zone z + 1 - m) = zone z + 1 by omega]; exact inW_of_reads hk h
  have cl : ∀ {z}, (((m + 1 ≤ zone z ∧ zone z < m + r) ∨ (m + r < b ∧ zone z = n + (m + r))) ∧
      InW φ i j l z) → zone z = m + r - 1 ∨ (m + r < b ∧ zone z = n + (m + r)) := by
    rintro z ⟨h | h, hw⟩
    · by_cases e : zone z + 2 ≤ m + r
      · exact absurd hw (inner h.1 e)
      · exact Or.inl (by omega)
    · exact Or.inr h
  intro y1 y2 y3 a1 a2 a3 d12 d13 d23
  have c1 := cl a1; have c2 := cl a2; have c3 := cl a3
  by_cases hlast : m + r - 1 + 1 < n
  · have e1 : ∀ {y y'}, zone y = m + r - 1 → zone y' = m + r - 1 → y = y' := fun h h' =>
      S.D.cardM (m + r - 1) (by have := S.m1; omega) hlast _ _ h h'
    have e2 : ∀ {y y'}, zone y = n + (m + r) → zone y' = n + (m + r) → y = y' := fun h h' =>
      S.D.sep1 (m + r) (by omega) (by omega) _ _ h h'
    rcases c1 with h1 | ⟨_, h1⟩ <;> rcases c2 with h2 | ⟨_, h2⟩ <;> rcases c3 with h3 | ⟨_, h3⟩
    · exact d12 (e1 h1 h2)
    · exact d12 (e1 h1 h2)
    · exact d13 (e1 h1 h3)
    · exact d23 (e2 h2 h3)
    · exact d23 (e1 h2 h3)
    · exact d13 (e2 h1 h3)
    · exact d12 (e2 h1 h2)
    · exact d12 (e2 h1 h2)
  · have nt : ∀ {y}, (zone y = m + r - 1 ∨ (m + r < b ∧ zone y = n + (m + r))) → zone y = n - 1 := by
      intro y h; rcases h with h | ⟨h, _⟩ <;> omega
    exact S.D.cardL y1 y2 y3 (nt c1) (nt c2) (nt c3) d12 d13 d23

/-- **Un lado en `1`.** -/
theorem side_resN (S : SideDataN φ n zone sv P0 Nn m b) {i j l : Int} (hf : frN φ sv m b i j l = 1)
    {a0 : Assign} (h0 : P0 a0) {d : Assign} (qd : P d) (qd0 : P0 d)
    (ag : Agr φ i j l (fun z => zone z = m ∨ (m + 1 < b ∧ zone z = n + (m + 1))) d a0) :
    ∃ src, SideOut φ n zone P0 P i j l a0 m b src := by
  refine ⟨_, side_right1 (by have := S.mb; omega) S.fix h0 qd qd0 ag (fun h z hz => ?_)⟩
  have hb := S.bn
  rw [S.eqsv (by omega) (by omega) hz]
  have := frN_rd (φ := φ) (sv := sv) (i := i) (j := j) (l := l) S.mb (by omega)
  rwa [hf] at this

/-- **Un lado abierto**: el testigo del paso de variable de `t_1` y dos regiones. -/
theorem side_windowN (S : SideDataN φ n zone sv P0 Nn m b) {i j l : Int} (hf : 2 ≤ frN φ sv m b i j l)
    {a0 : Assign} (h0 : P0 a0) : ∃ lam, 0 ≤ lam ∧ lam < Nn ∧ ReadsAt φ lam (sv (m + 1)) ∧
      ∀ {Q : Assign → Prop}, SideCap φ P0 P Q i j l lam a0 → ∃ src, SideOut φ n zone P0 P i j l a0 m b src := by
  have hle := frN_le (φ := φ) (sv := sv) (i := i) (j := j) (l := l) S.mb
  have hb := S.bn
  have hsv1 : sv (m + 1) < φ.nVars := S.D.sepv _ (by rw [S.hsv _ (by omega) (by omega)]; omega)
    (by rw [S.hsv _ (by omega) (by omega)]; omega)
  have r1 : ReadsAt φ (varStep (sv (m + 1))) (sv (m + 1)) := reads_self (stepVar_var hsv1)
  have mid := S.mid
  refine ⟨varStep (sv (m + 1)), by simp only [varStep]; omega, by simp only [varStep, midFusion] at mid ⊢; omega,
    r1, fun C => side_two S.m1 (c := 1) (Nat.le_refl _) (by omega) (by omega) S.fix h0 C
      (fun z hz => by rw [S.eqsv (by omega) (by omega) hz]; exact r1)
      (fun k z a c hz => by rw [S.eqsv (by omega) (by omega) hz]; exact frN_un a c)
      (fun h z hz => by rw [S.eqsv (by omega) (by omega) hz]; exact frN_rd S.mb (by omega))
      (Or.inl (readsA S hf)) (readsB S hf)⟩

/-- **Un lado en `1`, con las caras del otro.** -/
theorem res_of_capN (S : SideDataN φ n zone sv P0 Nn m b) {i j l lam : Int} (hf : frN φ sv m b i j l = 1)
    {a0 : Assign} {Q : Assign → Prop} (C : SideCap φ P0 P Q i j l lam a0)
    (ex : (frN φ sv m b i j l < b - m ∧ ∀ {M : Nat → Prop}, Le1 M → ∃ d, P d ∧ Q d ∧ Agr φ i j l M d a0 ∧
        d (sv (m + frN φ sv m b i j l)) = a0 (sv (m + frN φ sv m b i j l))) ∨
      (frN φ sv m b i j l = b - m ∧ ∀ c, Q c → P c)) :
    ∃ d, P d ∧ P0 d ∧ Agr φ i j l (fun z => zone z = m ∨ (m + 1 < b ∧ zone z = n + (m + 1))) d a0 := by
  have hb := S.bn
  rcases ex with ⟨hlt, pk⟩ | ⟨_, hQ⟩
  · obtain ⟨d, qP, qQ, ag, ev⟩ := pk (S.D.cardM m S.m1 (by omega))
    rw [hf] at ev
    refine ⟨d, qP, C.q0 d qQ, fun z hz hw => ?_⟩
    rcases hz with h | ⟨_, h⟩
    · exact ag z h hw
    · rw [S.eqsv (by omega) (by omega) h]; exact ev
  · obtain ⟨d, qQ, ag⟩ := C.p0 S.no3_res
    exact ⟨d, hQ d qQ, C.q0 d qQ, ag⟩

/-- **Un lado abierto**: sus fuentes, y las caras de su testigo para el otro lado. -/
theorem open_capN (hl : LocPair φ P0 P σ) (hS : PhStruct φ P0 Nn R Tf) {x u w : PathNodeId} (t : Tri R Tf x u w)
    {a0 : Assign} (h0 : P0 a0) (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) {zA svA zB svB : Nat → Nat} {mA bA mB bB : Nat}
    (SA : SideDataN φ n zA svA P0 Nn mA bA) (SB : SideDataN φ n zB svB P0 Nn mB bB)
    (hf : 2 ≤ frN φ svA mA bA x.id.step u.id.step w.id.step)
    (ih : ∀ x' u' w', Tri R Tf x' u' w' → frN φ svA mA bA x'.id.step u'.id.step w'.id.step ≤ 1 →
      frN φ svB mB bB x'.id.step u'.id.step w'.id.step ≤ frN φ svB mB bB x.id.step u.id.step w.id.step →
      TriOf φ P x' u' w') :
    (∃ src, SideOut φ n zA P0 P x.id.step u.id.step w.id.step a0 mA bA src) ∧
    ∃ Q lam, SideCap φ P0 P Q x.id.step u.id.step w.id.step lam a0 ∧
      ((frN φ svB mB bB x.id.step u.id.step w.id.step < bB - mB ∧ ∀ {M : Nat → Prop}, Le1 M →
          ∃ d, P d ∧ Q d ∧ Agr φ x.id.step u.id.step w.id.step M d a0 ∧
            d (svB (mB + frN φ svB mB bB x.id.step u.id.step w.id.step)) =
              a0 (svB (mB + frN φ svB mB bB x.id.step u.id.step w.id.step))) ∨
        (frN φ svB mB bB x.id.step u.id.step w.id.step = bB - mB ∧ ∀ c, Q c → P c)) := by
  obtain ⟨lam, l0, lN, lr, hsrc⟩ := side_windowN (P := P) SA hf h0
  have hno := frN_un (φ := φ) (sv := svA) (m := mA) (b := bA) (k := 1) (Nat.le_refl _) (i := x.id.step)
    (j := u.id.step) (l := w.id.step) (by omega)
  have hA1 : ∀ x' u' w' : PathNodeId, InW φ x'.id.step u'.id.step w'.id.step (svA (mA + 1)) →
      frN φ svA mA bA x'.id.step u'.id.step w'.id.step ≤ 1 := fun x' u' w' h' => frN_of (Nat.le_refl _) h'
  have hBle := frN_le (φ := φ) (sv := svB) (i := x.id.step) (j := u.id.step) (l := w.id.step) SB.mb
  have hBpos := frN_pos (φ := φ) (sv := svB) (m := mB) (b := bB) (i := x.id.step) (j := u.id.step) (l := w.id.step)
  by_cases hk : frN φ svB mB bB x.id.step u.id.step w.id.step < bB - mB
  · obtain ⟨Q, C, pk⟩ := capKeep hl hS t hx0 hu0 hw0 l0 lN lr hno (frN_rd SB.mb hk) (fun x' u' w' t' h1 h2 =>
      ih x' u' w' t' (hA1 x' u' w' h2) (frN_of hBpos h1))
    exact ⟨hsrc C, Q, lam, C, Or.inl ⟨hk, pk⟩⟩
  · obtain ⟨Q, C, hQ⟩ := capFull hl hS t hx0 hu0 hw0 l0 lN lr hno (fun x' u' w' t' h2 => ih x' u' w' t'
      (hA1 x' u' w' h2) (by
        have b := frN_le (φ := φ) (sv := svB) (i := x'.id.step) (j := u'.id.step) (l := w'.id.step) SB.mb
        omega))
    exact ⟨hsrc C, Q, lam, C, Or.inr ⟨by omega, hQ⟩⟩

end SideN

/-! ## El lado izquierdo -/

section Two

variable {n : Nat} {zone : Nat → Nat}

/-- **Las lecturas locales, al revés**: las de la izquierda de `v` son las de la derecha del lado izquierdo. -/
theorem localReads_rev {sv : Nat → Nat} {m : Nat} (hmn : m < n) (hL : LocalReadsAway φ n zone sv m) :
    LocalReadsFrom φ n (zoneRevN n zone) (fun k => sv (n - k)) (n - m) := by
  intro k z p h1 h2 hz hr
  have hz' : zone z = n - 1 - p := (zoneRevN_blk (by omega)).mp hz
  rcases hL k z (n - 1 - p) (Or.inl (by omega)) (by omega) (by omega) hz' hr with h | h
  · refine Or.inr ?_
    show ReadsAt φ k (sv (n - (p + 1)))
    rw [show n - (p + 1) = n - 1 - p by omega]; exact h
  · refine Or.inl ?_
    show ReadsAt φ k (sv (n - p))
    rw [show n - p = n - 1 - p + 1 by omega]; exact h

/-- **El lado izquierdo**, de la cadena al revés. -/
theorem sideDataN_left (D : ChainN φ n zone) {sv : Nat → Nat} (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    {m a : Nat} (hL : LocalReadsAway φ n zone sv m) (hmid : midFusion φ < Nn) (ham : a < m) (hmn : m < n)
    (hfa : 1 ≤ a → ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + a → c z = c' z) :
    SideDataN φ n (zoneRevN n zone) (fun k => sv (n - k)) P0 Nn (n - m) (n - a) where
  D := chainN_rev D
  hsv := fun k h1 h2 => (zoneRevN_sep h1 h2).mpr (by rw [hsv (n - k) (by omega) (by omega)])
  mid := hmid
  m1 := by omega
  mb := by omega
  bn := by omega
  fix := fixedEnd_rev (by omega) hfa
  loc := localReads_rev hmn hL

/-- **Fijar `v` con los dos lados abiertos, de cualquier longitud**, con lecturas locales. -/
theorem phantomFree_bisectN (hl : LocPair φ P0 P σ) (D : ChainN φ n zone) {sv : Nat → Nat}
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    {v : Nat} (hv : stepVar φ σ = some v) {m a b : Nat} (hL : LocalReadsAway φ n zone sv m) (hmid : midFusion φ < Nn)
    (hzv : zone v = n + m) (hm1 : 1 ≤ m) (ham : a < m) (hmb : m < b) (hbn : b ≤ n)
    (hfa : 1 ≤ a → ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + a → c z = c' z)
    (hfb : FixedEnd n zone P0 b) (hσ0 : 0 ≤ σ) (hσN : σ < Nn) : PhantomFree φ P0 P Nn σ := by
  have SR : SideDataN φ n zone sv P0 Nn m b := ⟨D, hsv, hmid, hm1, hmb, hbn, hfb,
    fun k z p h1 h2 hz hr => hL k z p (Or.inr h1) (by omega) h2 hz hr⟩
  have SL := sideDataN_left (P0 := P0) D hsv hL hmid ham (by omega) hfa
  refine phantomFree_of_descent hσ0 hσN
    (fun x u w => frN φ sv m b x.id.step u.id.step w.id.step +
      frN φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step)
    (fun R Tf hS hanch x u w t ih => ?_)
  obtain ⟨a0, h0, hx0, hu0, hw0⟩ := t.b3 hS
  have hRp := frN_pos (φ := φ) (sv := sv) (m := m) (b := b) (i := x.id.step) (j := u.id.step) (l := w.id.step)
  have hLp := frN_pos (φ := φ) (sv := fun k => sv (n - k)) (m := n - m) (b := n - a) (i := x.id.step)
    (j := u.id.step) (l := w.id.step)
  have ihR := fun (hR : 2 ≤ frN φ sv m b x.id.step u.id.step w.id.step) x' u' w' (t' : Tri R Tf x' u' w')
      (ha' : frN φ sv m b x'.id.step u'.id.step w'.id.step ≤ 1)
      (hc' : frN φ (fun k => sv (n - k)) (n - m) (n - a) x'.id.step u'.id.step w'.id.step ≤
        frN φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step) =>
    ih x' u' w' t' (by omega)
  have ihL := fun (hL : 2 ≤ frN φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step) x' u' w'
      (t' : Tri R Tf x' u' w')
      (ha' : frN φ (fun k => sv (n - k)) (n - m) (n - a) x'.id.step u'.id.step w'.id.step ≤ 1)
      (hc' : frN φ sv m b x'.id.step u'.id.step w'.id.step ≤ frN φ sv m b x.id.step u.id.step w.id.step) =>
    ih x' u' w' t' (by omega)
  have pvC : ∀ {Q : Assign → Prop} {lam : Int}, SideCap φ P0 P Q x.id.step u.id.step w.id.step lam a0 →
      InW φ x.id.step u.id.step w.id.step v → ∃ c, P c ∧ c v = a0 v := by
    intro Q lam C hwv
    obtain ⟨d, qP, _, ag⟩ := C.pP (le1_eq v)
    exact ⟨d, qP, ag v rfl hwv⟩
  have glue := fun {sL sR : Nat → Assign}
      (OL : SideOut φ n (zoneRevN n zone) P0 P x.id.step u.id.step w.id.step a0 (n - m) (n - a) sL)
      (OR : SideOut φ n zone P0 P x.id.step u.id.step w.id.step a0 m b sR) hpv =>
    glue_sides_tri hl D hv hzv hm1 ham hmb hbn hfa hfb h0 hx0 hu0 hw0 OL OR hpv
  by_cases hR : 2 ≤ frN φ sv m b x.id.step u.id.step w.id.step
  · obtain ⟨⟨sR, OR⟩, Q, lam, C, ex⟩ := open_capN hl hS t h0 hx0 hu0 hw0 SR SL hR (ihR hR)
    by_cases hL : 2 ≤ frN φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step
    · obtain ⟨⟨sL, OL⟩, _⟩ := open_capN hl hS t h0 hx0 hu0 hw0 SL SR hL (ihL hL)
      exact glue OL OR (pvC C)
    · obtain ⟨d, qP, q0, ag⟩ := res_of_capN SL (by omega) C ex
      obtain ⟨sL, OL⟩ := side_resN SL (by omega) h0 qP q0 ag
      exact glue OL OR (pvC C)
  · by_cases hL : 2 ≤ frN φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step
    · obtain ⟨⟨sL, OL⟩, Q, lam, C, ex⟩ := open_capN hl hS t h0 hx0 hu0 hw0 SL SR hL (ihL hL)
      obtain ⟨d, qP, q0, ag⟩ := res_of_capN SR (by omega) C ex
      obtain ⟨sR, OR⟩ := side_resN SR (by omega) h0 qP q0 ag
      exact glue OL OR (pvC C)
    · rcases faces_sigma hS hanch hσ0 hσN t h0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
      · exact h
      obtain ⟨dR, qR, agR⟩ := F.pick SR.no3_res
      obtain ⟨dL, qL, agL⟩ := F.pick SL.no3_res
      obtain ⟨sR, OR⟩ := side_resN SR (by omega) h0 qR (hl.sub _ qR) agR
      obtain ⟨sL, OL⟩ := side_resN SL (by omega) h0 qL (hl.sub _ qL) agL
      exact glue OL OR (fun hwv => (F.inw hwv).elim (fun e => ⟨c1, F.q1, e⟩) (fun e => ⟨c2, F.q2, e⟩))

end Two

end GPathB

end AbsSatBingo.Model

/-! ## T2 en cualquier orden, y el lector -/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {n : Nat} {zone sv : Nat → Nat}

/-- **T2 en cualquier orden de los separadores**, con lecturas locales: cada uno se fija con los extremos de la
cadena como extremos libres. -/
theorem sepPinFree_of_local (D : ChainN φ n zone) (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    (hL : LocalReads φ n zone sv) {ord : List Nat} (hord : ∀ q ∈ ord, 1 ≤ q ∧ q < n) :
    SepPinFree φ (ord.map sv) (stepCount φ) := by
  intro k R0 r s _ hs hrs hr1 hrT
  rw [List.getElem?_map] at hs
  cases hq : ord[R0.length]? with
  | none => rw [hq] at hs; cases hs
  | some q =>
    rw [hq] at hs
    have hsq : sv q = s := Option.some.inj hs
    obtain ⟨q1, qn⟩ := hord q (List.mem_of_getElem? hq)
    have hv : stepVar φ r.step = some (sv q) := by rw [hsq]; exact hrs
    have hmid : midFusion φ < stepCount φ := by unfold stepCount midFusion; omega
    exact phantomFree_bisectN (locPair_read (φ := φ) (stepCount φ) k R0 r) D hsv hv (away_of_local hL q) hmid
      (hsv q q1 qn) q1
      (a := 0) (b := n) (by omega) qn (Nat.le_refl _) (fun h => absurd h (by omega)) (fun h => absurd h (by omega))
      (by omega) hrT

theorem mem_sep_iff' (D : ChainN φ n zone) (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    {ord : List Nat} (hord : ∀ q ∈ ord, 1 ≤ q ∧ q < n) (hall : ∀ q, 1 ≤ q → q < n → q ∈ ord) :
    ∀ z, z ∈ ord.map sv ↔ SepN n zone z := by
  intro z
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    obtain ⟨q1, qn⟩ := hord q hq
    unfold SepN; rw [hsv q q1 qn]; omega
  · intro h
    unfold SepN at h
    have e := D.sep1 (zone z - n) (by omega) (by omega) z (sv (zone z - n)) (by omega)
      (hsv _ (by omega) (by omega))
    rw [e]
    exact List.mem_map.mpr ⟨_, hall _ (by omega) (by omega), rfl⟩

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {φ : Cnf} {n : Nat} {zone sv : Nat → Nat}

/-- **El lector por separadores no se atasca en ninguna cadena con lecturas locales, de cualquier longitud y en
cualquier orden de los separadores**, dadas las líneas (`HA`) y las cláusulas en bloques. -/
theorem reader_sep_local (hbd : Bounded φ) (D : ChainN φ n zone) (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    (hL : LocalReads φ n zone sv) (hcl : ∀ c ∈ φ.clauses, ∃ j, j < n ∧ ClIn (BlkN n zone j) c)
    {ord : List Nat} (hord : ∀ q ∈ ord, 1 ≤ q ∧ q < n) (hall : ∀ q, 1 ≤ q → q < n → q ∈ ord)
    (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') (hsf : SepFirst φ (ord.map sv) R) :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_sep_on hbd HA (sepCover_of_chainN D hcl (mem_sep_iff' D hsv hord hall))
    (sepPinFree_of_local D hsv hL hord) hkv hr hsf

end MachineOn

end AbsSatBingo.Model
