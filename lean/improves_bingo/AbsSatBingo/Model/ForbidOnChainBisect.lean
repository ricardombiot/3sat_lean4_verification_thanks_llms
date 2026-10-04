-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainBisect.lean
import AbsSatBingo.Model.ForbidOnChainSide

/-!
# Fijar un separador con los dos lados abiertos

El paso del lector en orden de bisección: se fija el separador `v` (zona `n + m`) de una `ChainN` con los separadores
`a` y `b` de los lados ya fijados (o los extremos de la cadena). Cada lado es una **`SideData`** en el sentido del lado
derecho (el izquierdo, de la cadena al revés: `sideData_left`), con hasta tres bloques si su extremo es libre y cuatro
si es fijo.

**El rango** de un triángulo es la suma de los **primeros separadores leídos** de los dos lados (`frS`: `1` si lee
`t_1`, `2` si lee `t_2` y no `t_1`, …; la longitud del lado si no lee ninguno).

* Los dos lados en `1`: las caras del testigo de `σ`; una fuente por lado (`side_res`).
* Un lado abierto (`≥ 2`): el testigo de su ventana (`side_window`), cuyas subtriangulaciones leen su `t_1` y
  **conservan el nodo del primer separador leído del otro lado** (`capKeep`, con `faces_Pwx` en cualquier posición):
  ese lado baja a `1` y el otro no sube (`open_cap`). Si el otro lado no lee ninguno, basta `faces_Pw` (`capFull`).
* El otro lado, si está en `1`, toma su fuente de esas mismas caras (`res_of_cap`): una de `P` que pasa por el nodo
  conservado, y por tanto coincide con `a0` en su `t_1`.

`glue_sides_tri` pega los dos lados en `v`. Resultado: **`phantomFree_bisect`**.

**T2 en orden de bisección** (`BisectOrder`, `sepPinFree_of_bisect`): cada separador tiene a cada lado uno ya fijado
(o el extremo) a la distancia que admite su lado; los fijados por el prefijo leído los leen igual todas las ramas
(`fixed_of_prefix`). Con seis bloques, `[3, 1, 2, 4, 5]` (`bisectOrder_6`). **`reader_bisect`**: el lector en ese
orden no se atasca en toda `ChainN` con las cláusulas en bloques, dadas las líneas (`HA`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop} {Nn σ : Int} {R : PathNodeId → PathNodeId → Prop} {Tf : Trios}

/-! ## Permutar las ventanas -/

theorem agr_perm {i j l i' j' l' : Int} (hp : ∀ z, InW φ i' j' l' z → InW φ i j l z) {M : Nat → Prop}
    {c a0 : Assign} (h : Agr φ i j l M c a0) : Agr φ i' j' l' M c a0 := fun z hm hw => h z hm (hp z hw)

theorem SideCap.perm {Q : Assign → Prop} {i j l i' j' l' lam : Int} {a0 : Assign}
    (C : SideCap φ P0 P Q i j l lam a0) (hp : ∀ z, InW φ i' j' l' z → InW φ i j l z) :
    SideCap φ P0 P Q i' j' l' lam a0 where
  q0 := C.q0
  win := C.win
  p0 := fun hM => by obtain ⟨d, q, ag⟩ := C.p0 hM; exact ⟨d, q, agr_perm hp ag⟩
  pP := fun hM => by obtain ⟨d, q, q', ag⟩ := C.pP hM; exact ⟨d, q, q', agr_perm hp ag⟩

/-! ## Las caras -/

/-- **Las caras de un testigo conservando el nodo que lee `s'`**, esté donde esté. -/
theorem capKeep (hl : LocPair φ P0 P σ) (hS : PhStruct φ P0 Nn R Tf) {x u w : PathNodeId} (t : Tri R Tf x u w)
    {a0 : Assign} (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) {lam : Int} (h0 : 0 ≤ lam) (hN : lam < Nn) {s s' : Nat}
    (hs : ReadsAt φ lam s) (hno : ¬ InW φ x.id.step u.id.step w.id.step s)
    (hs' : InW φ x.id.step u.id.step w.id.step s')
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s' →
      InW φ x'.id.step u'.id.step w'.id.step s → TriOf φ P x' u' w') :
    ∃ Q, SideCap φ P0 P Q x.id.step u.id.step w.id.step lam a0 ∧
      ∀ {M : Nat → Prop}, Le1 M → ∃ d, P d ∧ Q d ∧ Agr φ x.id.step u.id.step w.id.step M d a0 ∧ d s' = a0 s' := by
  obtain ⟨k, k', hk, hw, hz⟩ := hs'
  rcases hk with e | e | e
  · have hx : ReadsAt φ x.id.step s' := by rw [← e]; exact ⟨k', hw, hz⟩
    obtain ⟨c1, c2, c3, F, q1, q2⟩ := faces_Pwx hl hS t hx0 hu0 hw0 h0 hN hs hno hx hP
    refine ⟨_, sideCap_of_facesX F q1 q2, fun hM => ?_⟩
    obtain ⟨d, qP, qQ, ag, ei⟩ := pick12 F q1 q2 hM
    exact ⟨d, qP, qQ, ag, var_of_reads ei hx⟩
  · have hx : ReadsAt φ u.id.step s' := by rw [← e]; exact ⟨k', hw, hz⟩
    have hp : ∀ z, InW φ x.id.step u.id.step w.id.step z → InW φ u.id.step x.id.step w.id.step z :=
      fun _ h => inW_swap12 h
    obtain ⟨c1, c2, c3, F, q1, q2⟩ := faces_Pwx hl hS (t.swap12 hS) hu0 hx0 hw0 h0 hN hs
      (fun h => hno (inW_swap12 h)) hx hP
    refine ⟨_, (sideCap_of_facesX F q1 q2).perm hp, fun hM => ?_⟩
    obtain ⟨d, qP, qQ, ag, ei⟩ := pick12 F q1 q2 hM
    exact ⟨d, qP, qQ, agr_perm hp ag, var_of_reads ei hx⟩
  · have hx : ReadsAt φ w.id.step s' := by rw [← e]; exact ⟨k', hw, hz⟩
    have hp : ∀ z, InW φ x.id.step u.id.step w.id.step z → InW φ w.id.step x.id.step u.id.step z :=
      fun _ h => inW_swap12 (inW_swap23 h)
    obtain ⟨c1, c2, c3, F, q1, q2⟩ := faces_Pwx hl hS ((t.swap23 hS).swap12 hS) hw0 hx0 hu0 h0 hN hs
      (fun h => hno (inW_swap23 (inW_swap12 h))) hx hP
    refine ⟨_, (sideCap_of_facesX F q1 q2).perm hp, fun hM => ?_⟩
    obtain ⟨d, qP, qQ, ag, ei⟩ := pick12 F q1 q2 hM
    exact ⟨d, qP, qQ, agr_perm hp ag, var_of_reads ei hx⟩

/-- **Las caras de un testigo** sin conservar nada: las tres de `P`. -/
theorem capFull (hl : LocPair φ P0 P σ) (hS : PhStruct φ P0 Nn R Tf) {x u w : PathNodeId} (t : Tri R Tf x u w)
    {a0 : Assign} (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) {lam : Int} (h0 : 0 ≤ lam) (hN : lam < Nn) {s : Nat}
    (hs : ReadsAt φ lam s) (hno : ¬ InW φ x.id.step u.id.step w.id.step s)
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → InW φ x'.id.step u'.id.step w'.id.step s → TriOf φ P x' u' w') :
    ∃ Q, SideCap φ P0 P Q x.id.step u.id.step w.id.step lam a0 ∧ ∀ c, Q c → P c := by
  obtain ⟨c1, c2, c3, F⟩ := faces_Pw hS t hx0 hu0 hw0 h0 hN hs hno hP
  exact ⟨_, sideCap_of_facesP hl F, fun _ h => h.1⟩

/-! ## Un lado -/

/-- **Un lado**, en el sentido del lado derecho: los bloques `m … b-1` de la cadena, con los separadores `sv k`
(zona `n + k`), la ventana de cada bloque de en medio y el extremo `b` libre o fijo. -/
structure SideData (φ : Cnf) (n : Nat) (zone sv : Nat → Nat) (P0 : Assign → Prop) (Nn : Int) (m b : Nat) : Prop where
  D   : ChainN φ n zone
  hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k
  hw  : ∀ p, 1 ≤ p → p + 1 < n → ∃ lam, 0 ≤ lam ∧ lam < Nn ∧ ReadsAt φ lam (sv p) ∧ ReadsAt φ lam (sv (p + 1))
  m1  : 1 ≤ m
  mb  : m < b
  bn  : b ≤ n
  fix : FixedEnd n zone P0 b
  len : b - m ≤ 3 ∨ (b < n ∧ b - m ≤ 4)

open Classical in
/-- **El primer separador leído** del lado (la longitud del lado si no lee ninguno). -/
noncomputable def frS (φ : Cnf) (sv : Nat → Nat) (m b : Nat) (i j l : Int) : Nat :=
  if m + 1 < b ∧ InW φ i j l (sv (m + 1)) then 1
  else if m + 2 < b ∧ InW φ i j l (sv (m + 2)) then 2
  else if m + 3 < b ∧ InW φ i j l (sv (m + 3)) then 3 else b - m

section Fr

variable {sv : Nat → Nat} {m b : Nat} {i j l : Int}

theorem frS_cases (sv : Nat → Nat) (m b : Nat) (i j l : Int) :
    (frS φ sv m b i j l = 1 ∧ m + 1 < b ∧ InW φ i j l (sv (m + 1))) ∨
    (frS φ sv m b i j l = 2 ∧ ¬ (m + 1 < b ∧ InW φ i j l (sv (m + 1))) ∧ m + 2 < b ∧ InW φ i j l (sv (m + 2))) ∨
    (frS φ sv m b i j l = 3 ∧ ¬ (m + 1 < b ∧ InW φ i j l (sv (m + 1))) ∧
      ¬ (m + 2 < b ∧ InW φ i j l (sv (m + 2))) ∧ m + 3 < b ∧ InW φ i j l (sv (m + 3))) ∨
    (frS φ sv m b i j l = b - m ∧ ¬ (m + 1 < b ∧ InW φ i j l (sv (m + 1))) ∧
      ¬ (m + 2 < b ∧ InW φ i j l (sv (m + 2))) ∧ ¬ (m + 3 < b ∧ InW φ i j l (sv (m + 3)))) := by
  unfold frS
  by_cases h1 : m + 1 < b ∧ InW φ i j l (sv (m + 1))
  · exact Or.inl ⟨if_pos h1, h1⟩
  rw [if_neg h1]
  by_cases h2 : m + 2 < b ∧ InW φ i j l (sv (m + 2))
  · exact Or.inr (Or.inl ⟨if_pos h2, h1, h2⟩)
  rw [if_neg h2]
  by_cases h3 : m + 3 < b ∧ InW φ i j l (sv (m + 3))
  · exact Or.inr (Or.inr (Or.inl ⟨if_pos h3, h1, h2, h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨if_neg h3, h1, h2, h3⟩))

theorem frS_pos (hmb : m < b) : 1 ≤ frS φ sv m b i j l := by
  rcases frS_cases (φ := φ) sv m b i j l with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> omega

theorem frS_le : frS φ sv m b i j l ≤ b - m := by
  rcases frS_cases (φ := φ) sv m b i j l with ⟨e, h, _⟩ | ⟨e, _, h, _⟩ | ⟨e, _, _, h, _⟩ | ⟨e, _⟩ <;> omega

theorem frS_un (hL : b - m ≤ 4) {k : Nat} (hk : 1 ≤ k) (hkf : k < frS φ sv m b i j l) :
    ¬ InW φ i j l (sv (m + k)) := by
  intro hw
  rcases frS_cases (φ := φ) sv m b i j l with ⟨e, _⟩ | ⟨e, n1, h, _⟩ | ⟨e, n1, n2, h, _⟩ | ⟨e, n1, n2, n3⟩
  · omega
  · have : k = 1 := by omega
    subst this; exact n1 ⟨by omega, hw⟩
  · rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
    · exact n1 ⟨by omega, hw⟩
    · exact n2 ⟨by omega, hw⟩
  · rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
    · exact n1 ⟨by omega, hw⟩
    · exact n2 ⟨by omega, hw⟩
    · exact n3 ⟨by omega, hw⟩

theorem frS_rd (h : frS φ sv m b i j l < b - m) : InW φ i j l (sv (m + frS φ sv m b i j l)) := by
  rcases frS_cases (φ := φ) sv m b i j l with ⟨e, _, h1⟩ | ⟨e, _, _, h1⟩ | ⟨e, _, _, _, h1⟩ | ⟨e, _⟩
  · rw [e]; exact h1
  · rw [e]; exact h1
  · rw [e]; exact h1
  · omega

theorem frS_of (hL : b - m ≤ 4) {k : Nat} (hk : 1 ≤ k) (hw : InW φ i j l (sv (m + k))) :
    frS φ sv m b i j l ≤ k := by
  exact Nat.le_of_not_lt (fun hc => frS_un hL hk hc hw)

end Fr

section Side

variable {n : Nat} {zone sv : Nat → Nat} {m b : Nat}

theorem SideData.eqsv (S : SideData φ n zone sv P0 Nn m b) {k z : Nat} (hk : 1 ≤ k) (hkn : k < n)
    (hz : zone z = n + k) : z = sv k :=
  S.D.sep1 k hk hkn z (sv k) hz (S.hsv k hk hkn)

theorem SideData.L4 (S : SideData φ n zone sv P0 Nn m b) : b - m ≤ 4 := by
  rcases S.len with h | ⟨_, h⟩ <;> omega

/-- El bloque `m` y su separador `t_1`. -/
theorem SideData.no3_res (S : SideData φ n zone sv P0 Nn m b) :
    No3 (fun z => zone z = m ∨ (m + 1 < b ∧ zone z = n + (m + 1))) := by
  have := S.mb; have := S.bn
  by_cases h : m + 1 < b
  · intro y1 y2 y3 b1 b2 b3
    exact no3_mid_sep S.D S.m1 (by omega) y1 y2 y3 (b1.imp id (·.2)) (b2.imp id (·.2)) (b3.imp id (·.2))
  · intro y1 y2 y3 b1 b2 b3
    exact no3_last S.D S.m1 (by omega) y1 y2 y3 (b1.resolve_right (fun h' => h h'.1))
      (b2.resolve_right (fun h' => h h'.1)) (b3.resolve_right (fun h' => h h'.1))

/-- **Un lado en `1`**: una fuente de `P` para su bloque `m`. -/
theorem side_res (S : SideData φ n zone sv P0 Nn m b) {i j l : Int} (hf : frS φ sv m b i j l = 1) {a0 : Assign}
    (h0 : P0 a0) {d : Assign} (qd : P d) (qd0 : P0 d)
    (ag : Agr φ i j l (fun z => zone z = m ∨ (m + 1 < b ∧ zone z = n + (m + 1))) d a0) :
    ∃ src, SideOut φ n zone P0 P i j l a0 m b src := by
  refine ⟨_, side_right1 (by have := S.mb; omega) S.fix h0 qd qd0 ag (fun h z hz => ?_)⟩
  have hb := S.bn
  rw [S.eqsv (by omega) (by omega) hz]
  have := frS_rd (φ := φ) (sv := sv) (i := i) (j := j) (l := l) (show frS φ sv m b i j l < b - m by omega)
  rwa [hf] at this

/-- **Un lado abierto, con las caras de su ventana**: la ventana, y las fuentes del lado para cualesquiera caras. -/
theorem side_window (S : SideData φ n zone sv P0 Nn m b) {i j l : Int} (hf : 2 ≤ frS φ sv m b i j l) {a0 : Assign}
    (h0 : P0 a0) : ∃ lam, 0 ≤ lam ∧ lam < Nn ∧ ReadsAt φ lam (sv (m + 1)) ∧
      ∀ {Q : Assign → Prop}, SideCap φ P0 P Q i j l lam a0 → ∃ src, SideOut φ n zone P0 P i j l a0 m b src := by
  have hle := frS_le (φ := φ) (sv := sv) (m := m) (b := b) (i := i) (j := j) (l := l)
  have hun : ∀ k z, 1 ≤ k → k < frS φ sv m b i j l → zone z = n + (m + k) → ¬ InW φ i j l z := by
    intro k z a c hz
    have := S.bn
    rw [S.eqsv (by omega) (by omega) hz]; exact frS_un S.L4 a c
  have hrd : m + frS φ sv m b i j l < b → ∀ z, zone z = n + (m + frS φ sv m b i j l) → InW φ i j l z := by
    intro h z hz
    have := S.bn
    rw [S.eqsv (by omega) (by omega) hz]; exact frS_rd (by omega)
  have hL := S.len; have hb := S.bn
  generalize frS φ sv m b i j l = f at hf hle hun hrd
  by_cases h2 : f = 2
  · subst h2
    obtain ⟨lam, l0, lN, _, r2⟩ := S.hw m S.m1 (by omega)
    refine ⟨lam, l0, lN, r2, fun C => side_right2 S.D S.m1 (by omega) S.bn S.fix h0 C (fun z hz => ?_)
      (fun z hz => hun 1 z (Nat.le_refl _) (by omega) hz) hrd⟩
    rw [S.eqsv (by omega) (by omega) hz]; exact r2
  · obtain ⟨lam, l0, lN, r1, r2⟩ := S.hw (m + 1) (by omega) (by omega)
    refine ⟨lam, l0, lN, r1, fun C => side_right3 S.D S.m1 (r := f) (by omega) (by omega) S.bn S.fix h0 C
      (fun z hz => ?_) (fun z hz => ?_) hun hrd⟩
    · rw [S.eqsv (by omega) (by omega) hz]; exact r1
    · rw [S.eqsv (by omega) (by omega) hz]; exact r2

/-- **Un lado en `1`, con las caras del otro**: si su `t_1` lo lee el nodo conservado, una cara de `P` que pasa por
él; si no tiene separadores, cualquier cara (todas de `P`). -/
theorem res_of_cap (S : SideData φ n zone sv P0 Nn m b) {i j l lam : Int} (hf : frS φ sv m b i j l = 1)
    {a0 : Assign} {Q : Assign → Prop} (C : SideCap φ P0 P Q i j l lam a0)
    (ex : (frS φ sv m b i j l < b - m ∧ ∀ {M : Nat → Prop}, Le1 M → ∃ d, P d ∧ Q d ∧ Agr φ i j l M d a0 ∧
        d (sv (m + frS φ sv m b i j l)) = a0 (sv (m + frS φ sv m b i j l))) ∨
      (frS φ sv m b i j l = b - m ∧ ∀ c, Q c → P c)) :
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

/-- **Un lado abierto**: sus fuentes, y las caras de su ventana para el otro lado. -/
theorem open_cap (hl : LocPair φ P0 P σ) (hS : PhStruct φ P0 Nn R Tf) {x u w : PathNodeId} (t : Tri R Tf x u w)
    {a0 : Assign} (h0 : P0 a0) (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) {zA svA zB svB : Nat → Nat} {mA bA mB bB : Nat}
    (SA : SideData φ n zA svA P0 Nn mA bA) (SB : SideData φ n zB svB P0 Nn mB bB)
    (hf : 2 ≤ frS φ svA mA bA x.id.step u.id.step w.id.step)
    (ih : ∀ x' u' w', Tri R Tf x' u' w' →
      frS φ svA mA bA x'.id.step u'.id.step w'.id.step + frS φ svB mB bB x'.id.step u'.id.step w'.id.step <
        frS φ svA mA bA x.id.step u.id.step w.id.step + frS φ svB mB bB x.id.step u.id.step w.id.step →
      TriOf φ P x' u' w') :
    (∃ src, SideOut φ n zA P0 P x.id.step u.id.step w.id.step a0 mA bA src) ∧
    ∃ Q lam, SideCap φ P0 P Q x.id.step u.id.step w.id.step lam a0 ∧
      ((frS φ svB mB bB x.id.step u.id.step w.id.step < bB - mB ∧ ∀ {M : Nat → Prop}, Le1 M →
          ∃ d, P d ∧ Q d ∧ Agr φ x.id.step u.id.step w.id.step M d a0 ∧
            d (svB (mB + frS φ svB mB bB x.id.step u.id.step w.id.step)) =
              a0 (svB (mB + frS φ svB mB bB x.id.step u.id.step w.id.step))) ∨
        (frS φ svB mB bB x.id.step u.id.step w.id.step = bB - mB ∧ ∀ c, Q c → P c)) := by
  obtain ⟨lam, l0, lN, lr, hsrc⟩ := side_window (P := P) SA hf h0
  have hno := frS_un (φ := φ) (sv := svA) SA.L4 (k := 1) (Nat.le_refl _) (i := x.id.step) (j := u.id.step)
    (l := w.id.step) (by omega)
  have hA1 : ∀ x' u' w' : PathNodeId, InW φ x'.id.step u'.id.step w'.id.step (svA (mA + 1)) →
      frS φ svA mA bA x'.id.step u'.id.step w'.id.step ≤ 1 := fun x' u' w' h' => by
    have := frS_le (φ := φ) (sv := svA) (m := mA) (b := bA) (i := x.id.step) (j := u.id.step) (l := w.id.step)
    exact frS_of SA.L4 (Nat.le_refl _) h'
  have hBle := frS_le (φ := φ) (sv := svB) (m := mB) (b := bB) (i := x.id.step) (j := u.id.step) (l := w.id.step)
  have hBpos := frS_pos (φ := φ) (sv := svB) (i := x.id.step) (j := u.id.step) (l := w.id.step) SB.mb
  by_cases hk : frS φ svB mB bB x.id.step u.id.step w.id.step < bB - mB
  · obtain ⟨Q, C, pk⟩ := capKeep hl hS t hx0 hu0 hw0 l0 lN lr hno (frS_rd hk) (fun x' u' w' t' h1 h2 => ih x' u' w' t' (by
      have a := hA1 x' u' w' h2
      have b := frS_of (φ := φ) SB.L4 hBpos h1
      omega))
    exact ⟨hsrc C, Q, lam, C, Or.inl ⟨hk, pk⟩⟩
  · obtain ⟨Q, C, hQ⟩ := capFull hl hS t hx0 hu0 hw0 l0 lN lr hno (fun x' u' w' t' h2 => ih x' u' w' t' (by
      have a := hA1 x' u' w' h2
      have b := frS_le (φ := φ) (sv := svB) (m := mB) (b := bB) (i := x'.id.step) (j := u'.id.step) (l := w'.id.step)
      omega))
    exact ⟨hsrc C, Q, lam, C, Or.inr ⟨by omega, hQ⟩⟩

end Side

/-! ## Los dos lados de `v` -/

section Two

variable {n : Nat} {zone : Nat → Nat}

/-- **El lado izquierdo**, de la cadena al revés. -/
theorem sideData_left (D : ChainN φ n zone) {sv : Nat → Nat} (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    (hw : ∀ p, 1 ≤ p → p + 1 < n → ∃ lam, 0 ≤ lam ∧ lam < Nn ∧ ReadsAt φ lam (sv p) ∧ ReadsAt φ lam (sv (p + 1)))
    {m a : Nat} (ham : a < m) (hmn : m < n)
    (hfa : 1 ≤ a → ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + a → c z = c' z)
    (hL : m - a ≤ 3 ∨ (1 ≤ a ∧ m - a ≤ 4)) :
    SideData φ n (zoneRevN n zone) (fun k => sv (n - k)) P0 Nn (n - m) (n - a) where
  D := chainN_rev D
  hsv := fun k h1 h2 => (zoneRevN_sep h1 h2).mpr (by rw [hsv (n - k) (by omega) (by omega)])
  hw := fun p h1 h2 => by
    obtain ⟨lam, l0, lN, r1, r2⟩ := hw (n - p - 1) (by omega) (by omega)
    refine ⟨lam, l0, lN, ?_, ?_⟩
    · rw [show n - p = n - p - 1 + 1 by omega]; exact r2
    · rw [show n - (p + 1) = n - p - 1 by omega]; exact r1
  m1 := by omega
  mb := by omega
  bn := by omega
  fix := fixedEnd_rev (by omega) hfa
  len := by
    rcases hL with h | ⟨h1, h⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩

/-- **Fijar `v` con los dos lados abiertos.** -/
theorem phantomFree_bisect (hl : LocPair φ P0 P σ) (D : ChainN φ n zone) {sv : Nat → Nat}
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    (hw : ∀ p, 1 ≤ p → p + 1 < n → ∃ lam, 0 ≤ lam ∧ lam < Nn ∧ ReadsAt φ lam (sv p) ∧ ReadsAt φ lam (sv (p + 1)))
    {v : Nat} (hv : stepVar φ σ = some v) {m a b : Nat} (hzv : zone v = n + m) (hm1 : 1 ≤ m) (ham : a < m)
    (hmb : m < b) (hbn : b ≤ n) (hfa : 1 ≤ a → ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + a → c z = c' z)
    (hfb : FixedEnd n zone P0 b) (hLL : m - a ≤ 3 ∨ (1 ≤ a ∧ m - a ≤ 4)) (hLR : b - m ≤ 3 ∨ (b < n ∧ b - m ≤ 4))
    (hσ0 : 0 ≤ σ) (hσN : σ < Nn) : PhantomFree φ P0 P Nn σ := by
  have SR : SideData φ n zone sv P0 Nn m b := ⟨D, hsv, hw, hm1, hmb, hbn, hfb, hLR⟩
  have SL := sideData_left (P0 := P0) D hsv hw ham (by omega) hfa hLL
  refine phantomFree_of_descent hσ0 hσN
    (fun x u w => frS φ sv m b x.id.step u.id.step w.id.step +
      frS φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step)
    (fun R Tf hS hanch x u w t ih => ?_)
  obtain ⟨a0, h0, hx0, hu0, hw0⟩ := t.b3 hS
  have hRp := frS_pos (φ := φ) (sv := sv) (i := x.id.step) (j := u.id.step) (l := w.id.step) hmb
  have hLp := frS_pos (φ := φ) (sv := fun k => sv (n - k)) (i := x.id.step) (j := u.id.step) (l := w.id.step)
    SL.mb
  have ih' : ∀ x' u' w', Tri R Tf x' u' w' →
      frS φ (fun k => sv (n - k)) (n - m) (n - a) x'.id.step u'.id.step w'.id.step +
        frS φ sv m b x'.id.step u'.id.step w'.id.step <
      frS φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step +
        frS φ sv m b x.id.step u.id.step w.id.step → TriOf φ P x' u' w' :=
    fun x' u' w' t' h => ih x' u' w' t' (by omega)
  -- `v` como en `a0`, de una cara de `P`
  have pvC : ∀ {Q : Assign → Prop} {lam : Int}, SideCap φ P0 P Q x.id.step u.id.step w.id.step lam a0 →
      InW φ x.id.step u.id.step w.id.step v → ∃ c, P c ∧ c v = a0 v := by
    intro Q lam C hwv
    obtain ⟨d, qP, _, ag⟩ := C.pP (le1_eq v)
    exact ⟨d, qP, ag v rfl hwv⟩
  have glue := fun {sL sR : Nat → Assign}
      (OL : SideOut φ n (zoneRevN n zone) P0 P x.id.step u.id.step w.id.step a0 (n - m) (n - a) sL)
      (OR : SideOut φ n zone P0 P x.id.step u.id.step w.id.step a0 m b sR) hpv =>
    glue_sides_tri hl D hv hzv hm1 ham hmb hbn hfa hfb h0 hx0 hu0 hw0 OL OR hpv
  by_cases hR : 2 ≤ frS φ sv m b x.id.step u.id.step w.id.step
  · obtain ⟨⟨sR, OR⟩, Q, lam, C, ex⟩ := open_cap hl hS t h0 hx0 hu0 hw0 SR SL hR ih
    by_cases hL : 2 ≤ frS φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step
    · obtain ⟨⟨sL, OL⟩, _⟩ := open_cap hl hS t h0 hx0 hu0 hw0 SL SR hL ih'
      exact glue OL OR (pvC C)
    · obtain ⟨d, qP, q0, ag⟩ := res_of_cap SL (by omega) C ex
      obtain ⟨sL, OL⟩ := side_res SL (by omega) h0 qP q0 ag
      exact glue OL OR (pvC C)
  · by_cases hL : 2 ≤ frS φ (fun k => sv (n - k)) (n - m) (n - a) x.id.step u.id.step w.id.step
    · obtain ⟨⟨sL, OL⟩, Q, lam, C, ex⟩ := open_cap hl hS t h0 hx0 hu0 hw0 SL SR hL ih'
      obtain ⟨d, qP, q0, ag⟩ := res_of_cap SR (by omega) C ex
      obtain ⟨sR, OR⟩ := side_res SR (by omega) h0 qP q0 ag
      exact glue OL OR (pvC C)
    · -- los dos lados en `1`: el testigo de `σ`
      rcases faces_sigma hS hanch hσ0 hσN t h0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
      · exact h
      obtain ⟨dR, qR, agR⟩ := F.pick SR.no3_res
      obtain ⟨dL, qL, agL⟩ := F.pick SL.no3_res
      obtain ⟨sR, OR⟩ := side_res SR (by omega) h0 qR (hl.sub _ qR) agR
      obtain ⟨sL, OL⟩ := side_res SL (by omega) h0 qL (hl.sub _ qL) agL
      exact glue OL OR (fun hwv => (F.inw hwv).elim (fun e => ⟨c1, F.q1, e⟩) (fun e => ⟨c2, F.q2, e⟩))

end Two

/-! ## T2 en orden de bisección -/

/-- **Un orden de bisección** de los separadores `1 … n-1`: cada uno tiene, a cada lado, un separador ya fijado (o el
extremo de la cadena) a distancia a lo sumo tres (cuatro si es un separador fijado). -/
def BisectOrder (n : Nat) (ord : List Nat) : Prop :=
  ∀ (k q : Nat), ord[k]? = some q → 1 ≤ q ∧ q < n ∧ ∃ a b : Nat, a < q ∧ q < b ∧ b ≤ n ∧
    (a = 0 ∨ ∃ i : Nat, i < k ∧ ord[i]? = some a) ∧ (b = n ∨ ∃ i : Nat, i < k ∧ ord[i]? = some b) ∧
    (q - a ≤ 3 ∨ (1 ≤ a ∧ q - a ≤ 4)) ∧ (b - q ≤ 3 ∨ (b < n ∧ b - q ≤ 4))

section T2

variable {n : Nat} {zone : Nat → Nat}

/-- Un separador fijado por el prefijo leído lo leen igual todas las ramas. -/
theorem fixed_of_prefix {sv : Nat → Nat} {ord : List Nat} {R0 : List NodeId} {X : Assign → Prop}
    (hpre : SepPrefix φ (ord.map sv) R0) {i a : Nat} (hi : i < R0.length) (ho : ord[i]? = some a) :
    ∀ c c', Pinned φ X R0 c → Pinned φ X R0 c' → c (sv a) = c' (sv a) := by
  refine agree_of_pins ⟨R0[i], List.getElem_mem hi, ?_⟩
  rw [hpre i R0[i] (List.getElem?_eq_getElem hi), List.getElem?_map, ho]; rfl

/-- **T2 en orden de bisección**, para toda cadena. -/
theorem sepPinFree_of_bisect (D : ChainN φ n zone) {sv : Nat → Nat}
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    (hw : ∀ p, 1 ≤ p → p + 1 < n → ∃ lam, 0 ≤ lam ∧ lam < stepCount φ ∧ ReadsAt φ lam (sv p) ∧
      ReadsAt φ lam (sv (p + 1)))
    {ord : List Nat} (hord : BisectOrder n ord) : SepPinFree φ (ord.map sv) (stepCount φ) := by
  intro k R0 r s hpre hs hrs hr1 hrT
  rw [List.getElem?_map] at hs
  cases hq : ord[R0.length]? with
  | none => rw [hq] at hs; cases hs
  | some q =>
    rw [hq] at hs
    have hsq : sv q = s := Option.some.inj hs
    obtain ⟨q1, qn, a, b, ha, hb, hbn, hA, hB, hLL, hLR⟩ := hord _ _ hq
    have hl := locPair_read (φ := φ) (stepCount φ) k R0 r
    have hv : stepVar φ r.step = some (sv q) := by rw [hsq]; exact hrs
    -- los extremos fijados
    have fixOf : ∀ c, (c = 0 ∨ ∃ i, i < R0.length ∧ ord[i]? = some c) → 1 ≤ c → c < n →
        ∀ y y', Pinned φ (SolE φ (stepCount φ) k) R0 y → Pinned φ (SolE φ (stepCount φ) k) R0 y' →
          ∀ z, zone z = n + c → y z = y' z := by
      intro c hc h1 h2 y y' qy qy' z hz
      rcases hc with h | ⟨i, hi, ho⟩
      · omega
      rw [D.sep1 c h1 h2 z (sv c) hz (hsv c h1 h2)]
      exact fixed_of_prefix hpre hi ho y y' qy qy'
    refine phantomFree_bisect hl D hsv hw hv (hsv q q1 qn) q1 ha hb hbn
      (fun h1 => fixOf a hA h1 (by omega)) (fun h2 => fixOf b ?_ (by omega) h2) hLL hLR (by omega) hrT
    rcases hB with h | h
    · omega
    · exact Or.inr h

/-- La lista de separadores, si el orden los recorre todos. -/
theorem mem_sep_iff (D : ChainN φ n zone) {sv : Nat → Nat} (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    {ord : List Nat} (hord : BisectOrder n ord) (hall : ∀ q, 1 ≤ q → q < n → q ∈ ord) :
    ∀ z, z ∈ ord.map sv ↔ SepN n zone z := by
  intro z
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
    obtain ⟨q1, qn, _⟩ := hord i q hi
    unfold SepN; rw [hsv q q1 qn]; omega
  · intro h
    unfold SepN at h
    have e := D.sep1 (zone z - n) (by omega) (by omega) z (sv (zone z - n)) (by omega)
      (hsv _ (by omega) (by omega))
    rw [e]
    exact List.mem_map.mpr ⟨_, hall _ (by omega) (by omega), rfl⟩

end T2

/-! ## El orden para seis bloques -/

theorem bisectOrder_6 : BisectOrder 6 [3, 1, 2, 4, 5] := by
  intro k q h
  rcases k with _ | _ | _ | _ | _ | k
  · have : q = 3 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 0, 6, by omega, by omega, by omega, Or.inl rfl, Or.inl rfl, Or.inl (by omega),
      Or.inl (by omega)⟩
  · have : q = 1 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 0, 3, by omega, by omega, by omega, Or.inl rfl, Or.inr ⟨0, by omega, rfl⟩,
      Or.inl (by omega), Or.inl (by omega)⟩
  · have : q = 2 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 1, 3, by omega, by omega, by omega, Or.inr ⟨1, by omega, rfl⟩,
      Or.inr ⟨0, by omega, rfl⟩, Or.inl (by omega), Or.inl (by omega)⟩
  · have : q = 4 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 3, 6, by omega, by omega, by omega, Or.inr ⟨0, by omega, rfl⟩, Or.inl rfl,
      Or.inl (by omega), Or.inl (by omega)⟩
  · have : q = 5 := by simp at h; omega
    subst this
    exact ⟨by omega, by omega, 4, 6, by omega, by omega, by omega, Or.inr ⟨3, by omega, rfl⟩, Or.inl rfl,
      Or.inl (by omega), Or.inl (by omega)⟩
  · simp at h

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **El lector en orden de bisección no se atasca** en una cadena de `n` bloques con un orden de bisección (hasta
seis bloques: `bisectOrder_6`), con las líneas (`HA`) y toda cláusula en un bloque. -/
theorem reader_bisect {n : Nat} {zone : Nat → Nat} (hbd : Bounded φ) (D : ChainN φ n zone) {sv : Nat → Nat}
    (hsv : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k)
    (hw : ∀ p, 1 ≤ p → p + 1 < n → ∃ lam, 0 ≤ lam ∧ lam < stepCount φ ∧ ReadsAt φ lam (sv p) ∧
      ReadsAt φ lam (sv (p + 1)))
    (hcl : ∀ c ∈ φ.clauses, ∃ j, j < n ∧ ClIn (BlkN n zone j) c)
    {ord : List Nat} (hord : BisectOrder n ord) (hall : ∀ q, 1 ≤ q → q < n → q ∈ ord)
    (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') (hsf : SepFirst φ (ord.map sv) R) :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_sep_on hbd HA (sepCover_of_chainN D hcl (mem_sep_iff D hsv hord hall))
    (sepPinFree_of_bisect D hsv hw hord) hkv hr hsf

end MachineOn

end AbsSatBingo.Model
