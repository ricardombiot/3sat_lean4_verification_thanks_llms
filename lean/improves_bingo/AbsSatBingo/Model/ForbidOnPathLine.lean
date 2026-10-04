-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnPathLine.lean
import AbsSatBingo.Model.ForbidOnPathSide

/-!
# Las líneas de un camino de unidades: un testigo que lo lee todo

`faces_Pw` pide la hipótesis de inducción en los triángulos que leen **una** variable `s` del testigo. Pero los
subtriángulos de las caras contienen el nodo del testigo: leen **todo** lo que lee su ventana. Con bloques anchos eso
importa, porque un corte puede tener dos variables y el descenso tiene que dejarlas leídas a la vez.

* **`faces_PwAll`**: las caras de `faces_Pw`, con la hipótesis de inducción solo en los triángulos que leen todo lo que
  lee la ventana `lam`.
* **`capFullAll`**: su `SideCap`, con todas las caras de `P`.

`probe_line_wide.jl` mide la condición de las líneas: un solo testigo por línea, con `X` = lo que lee salvo `v`, y las
regiones partidas en los cortes con `S_j \ {v} ⊆ X`. Vale en todas las líneas de anchura 1 y 2 medidas.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop} {Nn σ : Int} {R : PathNodeId → PathNodeId → Prop} {Tf : Trios}

/-- **Las caras de un testigo**, con la hipótesis de inducción en los triángulos que leen todo lo que lee `lam`. -/
theorem faces_PwAll (hS : PhStruct φ P0 Nn R Tf) {x u w : PathNodeId} (t : Tri R Tf x u w) {a0 : Assign}
    (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) {lam : Int} (h0 : 0 ≤ lam) (hN : lam < Nn) {s : Nat}
    (hs : ReadsAt φ lam s) (hno : ¬ InW φ x.id.step u.id.step w.id.step s)
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → (∀ z, ReadsAt φ lam z → InW φ x'.id.step u'.id.step w'.id.step z) →
      TriOf φ P x' u' w') :
    ∃ c1 c2 c3, Faces φ (fun c => P c ∧ pidOfAssign φ c lam = pidOfAssign φ c1 lam) a0 c1 c2 c3
      x.id.step u.id.step w.id.step := by
  obtain ⟨n, hns, hn⟩ := t.wit hS h0 hN
  rcases hn with hn | ⟨t1, t2, t3⟩
  · exfalso
    apply hno
    rcases hn with e | e | e
    · exact inW_of_reads (Or.inl rfl) (by rw [← e, hns]; exact hs)
    · exact inW_of_reads (Or.inr (Or.inl rfl)) (by rw [← e, hns]; exact hs)
    · exact inW_of_reads (Or.inr (Or.inr rfl)) (by rw [← e, hns]; exact hs)
  have fr : ∀ {y z : PathNodeId}, ∀ q, ReadsAt φ lam q → InW φ y.id.step z.id.step n.id.step q :=
    fun q hq => inW_of_reads (Or.inr (Or.inr rfl)) (by rw [hns]; exact hq)
  obtain ⟨c1, q1, c1x, c1u, c1n⟩ := hP x u n t1 fr
  obtain ⟨c2, q2, c2x, c2w, c2n⟩ := hP x w n t2 fr
  obtain ⟨c3, q3, c3u, c3w, c3n⟩ := hP u w n t3 fr
  rw [hns] at c1n c2n c3n
  exact ⟨c1, c2, c3, ⟨⟨q1, rfl⟩, ⟨q2, c2n.trans c1n.symm⟩, ⟨q3, c3n.trans c1n.symm⟩, c1x.trans hx0.symm,
    c2x.trans hx0.symm, c1u.trans hu0.symm, c3u.trans hu0.symm, c2w.trans hw0.symm, c3w.trans hw0.symm⟩⟩

/-- **Su `SideCap`**, todas de `P`. -/
theorem capFullAll (hl : LocPair φ P0 P σ) (hS : PhStruct φ P0 Nn R Tf) {x u w : PathNodeId} (t : Tri R Tf x u w)
    {a0 : Assign} (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) {lam : Int} (h0 : 0 ≤ lam) (hN : lam < Nn) {s : Nat}
    (hs : ReadsAt φ lam s) (hno : ¬ InW φ x.id.step u.id.step w.id.step s)
    (hP : ∀ x' u' w', Tri R Tf x' u' w' → (∀ z, ReadsAt φ lam z → InW φ x'.id.step u'.id.step w'.id.step z) →
      TriOf φ P x' u' w') :
    ∃ Q, SideCap φ P0 P Q x.id.step u.id.step w.id.step lam a0 ∧ ∀ c, Q c → P c := by
  obtain ⟨c1, c2, c3, F⟩ := faces_PwAll hS t hx0 hu0 hw0 h0 hN hs hno hP
  exact ⟨_, sideCap_of_facesP hl F, fun _ h => h.1⟩

/-! ## Las piezas de una línea -/

/-- La pieza de la unidad `p`: empieza en `f` o justo tras el último corte de pegado `G` antes de `p`. -/
noncomputable def stP (f : Nat) (G : Nat → Prop) : Nat → Nat
  | 0 => f
  | p + 1 => by
    classical
    exact if p + 1 ≤ f then f else if G p then p + 1 else stP f G p

theorem stP_le {f : Nat} {G : Nat → Prop} : ∀ {p}, p ≤ f → stP f G p = f
  | 0, _ => rfl
  | p + 1, h => by simp only [stP]; rw [if_pos h]

theorem stP_glue {f : Nat} {G : Nat → Prop} {p : Nat} (hf : f ≤ p) (hg : G p) : stP f G (p + 1) = p + 1 := by
  simp only [stP]; rw [if_neg (by omega), if_pos hg]

theorem stP_no {f : Nat} {G : Nat → Prop} {p : Nat} (hf : f ≤ p) (hg : ¬ G p) : stP f G (p + 1) = stP f G p := by
  simp only [stP]; rw [if_neg (by omega), if_neg hg]

/-- Lo que lee el testigo, salvo `v`. -/
def XW (φ : Cnf) (lam : Int) (v z : Nat) : Prop := ReadsAt φ lam z ∧ z ≠ v

/-- Un corte de pegado: todo lo suyo es `v` o lo lee el testigo. -/
def GlueAt (lo hi : Nat → Nat) (X : Nat → Prop) (v k : Nat) : Prop := ∀ z, lo z ≤ k → k + 1 ≤ hi z → z = v ∨ X z

/-- El trío lee entero el corte `k`. -/
def CutRead (φ : Cnf) (lo hi : Nat → Nat) (i j l : Int) (k : Nat) : Prop :=
  ∀ z, lo z ≤ k → k + 1 ≤ hi z → InW φ i j l z

/-- Las variables de la pieza `q`, salvo `v`. -/
def PieceV (n : Nat) (lo hi : Nat → Nat) (f : Nat) (G : Nat → Prop) (v q z : Nat) : Prop :=
  z ≠ v ∧ ∃ p, f ≤ p ∧ p < n ∧ stP f G p = q ∧ InU lo hi p z

/-- **La condición de la línea**, para un trío: una cola `f` (el principio, o tras un corte leído entero) y las piezas
sin `Bad3`. -/
def LineOK (φ : Cnf) (n : Nat) (lo hi : Nat → Nat) (v : Nat) (lam i j l : Int) : Prop :=
  ∃ f, (f = 0 ∨ CutRead φ lo hi i j l (f - 1)) ∧ f ≤ lo v ∧
    ∀ q, ¬ Bad3 φ i j l (PieceV n lo hi f (GlueAt lo hi (XW φ lam v) v) v q)

section Pieces

variable {n : Nat} {lo hi : Nat → Nat}

/-- **Cerrar el triángulo con una cara por pieza.** Las caras `Q` son de `P`; en los cortes de pegado coinciden porque
leen igual lo del testigo, o porque el trío lo lee todo y cada una coincide con `a0`. -/
theorem tri_of_pieces (hl : LocPair φ P0 P σ) (D : PathN φ n lo hi) {v : Nat} (hv : stepVar φ σ = some v)
    (hvin : ∃ j, j < n ∧ InU lo hi j v) {lam : Int} {x u w : PathNodeId} {a0 : Assign} (h0 : P0 a0)
    (hx0 : pidOfAssign φ a0 x.id.step = x) (hu0 : pidOfAssign φ a0 u.id.step = u)
    (hw0 : pidOfAssign φ a0 w.id.step = w) {f : Nat}
    (hf : f = 0 ∨ CutRead φ lo hi x.id.step u.id.step w.id.step (f - 1)) (hfv : f ≤ lo v)
    {Q : Assign → Prop} (hQP : ∀ c, Q c → P c)
    (hX : (∀ c c', Q c → Q c' → ∀ z, ReadsAt φ lam z → c z = c' z) ∨
      (∀ z, XW φ lam v z → InW φ x.id.step u.id.step w.id.step z))
    (hpk : ∀ q, ∃ c, Q c ∧ Agr φ x.id.step u.id.step w.id.step
      (PieceV n lo hi f (GlueAt lo hi (XW φ lam v) v) v q) c a0)
    (hpv : InW φ x.id.step u.id.step w.id.step v → ∃ c, P c ∧ c v = a0 v) : TriOf φ P x u w := by
  classical
  have sv : ∀ {c c'}, P c → P c' → c v = c' v := fun q q' => hl.sameVar hv q q'
  let G := GlueAt lo hi (XW φ lam v) v
  let d : Nat → Assign := fun q => Classical.choose (hpk q)
  have dQ : ∀ q, Q (d q) := fun q => (Classical.choose_spec (hpk q)).1
  have dA : ∀ q, Agr φ x.id.step u.id.step w.id.step (PieceV n lo hi f G v q) (d q) a0 :=
    fun q => (Classical.choose_spec (hpk q)).2
  let src : Nat → Assign := fun p => if p < f ∨ n ≤ p then a0 else d (stP f G p)
  have sA : ∀ p, (p < f ∨ n ≤ p) → src p = a0 := fun p h => by simp only [src]; rw [if_pos h]
  have sD : ∀ p, f ≤ p → p < n → src p = d (stP f G p) := fun p h h' => by
    simp only [src]; rw [if_neg (by omega)]
  -- lo de una unidad está en su pieza
  have inP : ∀ {p z}, f ≤ p → p < n → InU lo hi p z → z ≠ v → PieceV n lo hi f G v (stP f G p) z :=
    fun {p} {_} h1 h2 hu hz => ⟨hz, p, h1, h2, rfl, hu⟩
  have hs : ∀ j, j < n → P0 (src j) := by
    intro j hj
    by_cases h : j < f
    · rw [sA j (Or.inl h)]; exact h0
    · rw [sD j (by omega) hj]; exact hl.sub _ (hQP _ (dQ _))
  have hJ : JoinP lo hi src := by
    intro k z h1 h2
    have hzn : lo z < n → hi z < n := fun h => (D.ord z h).2
    by_cases c1 : k + 1 < f
    · rw [sA _ (Or.inl (by omega)), sA _ (Or.inl c1)]
    by_cases cn : n ≤ k
    · rw [sA _ (Or.inr cn), sA _ (Or.inr (by omega))]
    by_cases cn' : n ≤ k + 1
    · exfalso
      have := hzn (by omega); omega
    by_cases c2 : k + 1 = f
    · -- la cola: el corte `f - 1` está leído entero
      rw [sA _ (Or.inl (by omega)), sD _ (by omega) (by omega)]
      have hzv : z ≠ v := fun e => by subst e; omega
      rcases hf with e | hc
      · omega
      · have hr := hc z (by omega) (by omega)
        exact (dA _ z (inP (by omega) (by omega) (by unfold InU; omega) hzv) hr).symm
    rw [sD _ (by omega) (by omega), sD _ (by omega) (by omega)]
    by_cases hg : G k
    · rw [stP_glue (by omega) hg]
      rcases hg z h1 h2 with e | hx
      · subst e; exact sv (hQP _ (dQ _)) (hQP _ (dQ _))
      · rcases hX with hag | hrd
        · exact hag _ _ (dQ _) (dQ _) z hx.1
        · have hr := hrd z hx
          have hB : PieceV n lo hi f G v (k + 1) z := by
            have e := stP_glue (G := G) (show f ≤ k by omega) hg
            have := inP (p := k + 1) (by omega) (by omega) (by unfold InU; omega) hx.2
            rwa [e] at this
          rw [dA _ z (inP (by omega) (by omega) (by unfold InU; omega) hx.2) hr, dA _ z hB hr]
    · rw [stP_no (by omega) hg]
  have hvU : ∀ j, j < n → InU lo hi j v → P (src j) := by
    intro j hj h
    unfold InU at h
    rw [sD j (by omega) hj]; exact hQP _ (dQ _)
  refine GPathB.glueP_tri hl D hv hvin h0 hx0 hu0 hw0 hs hJ hvU (fun b hb z hz hw => ?_)
  by_cases h : b < f
  · rw [sA _ (Or.inl h)]
  rw [sD _ (by omega) hb]
  have hU : InU lo hi b z := by have := D.ord z (by omega); unfold InU; omega
  by_cases hzv : z = v
  · subst hzv
    obtain ⟨c, pc, ec⟩ := hpv hw
    rw [sv (hQP _ (dQ _)) pc]; exact ec
  · exact dA _ z (inP (by omega) hb hU hzv) hw

end Pieces

/-! ## El descenso de una línea -/

section Line

variable {n : Nat} {lo hi : Nat → Nat}

/-- Las caras de la base o del testigo dan la cara de cada pieza. -/
theorem pieces_of_faces {Q : Assign → Prop} {a0 c1 c2 c3 : Assign} {i j l : Int}
    (F : Faces φ Q a0 c1 c2 c3 i j l) {M : Nat → Nat → Prop} (hM : ∀ q, ¬ Bad3 φ i j l (M q)) :
    ∀ q, ∃ c, Q c ∧ Agr φ i j l (M q) c a0 := by
  intro q
  rcases F.pick3 (M q) with h | ⟨z1, z2, z3, m1, m2, m3, d12, d13, d23, r1, r2, r3⟩
  · exact h
  · exact absurd ⟨z1, z2, z3, m1, m2, m3, d12, d13, d23, r1, r2, r3⟩ (hM q)

theorem pv_of_faces {Q : Assign → Prop} {a0 c1 c2 c3 : Assign} {i j l : Int}
    (F : Faces φ Q a0 c1 c2 c3 i j l) (hQP : ∀ c, Q c → P c) {v : Nat} :
    InW φ i j l v → ∃ c, P c ∧ c v = a0 v := by
  intro hw
  rcases F.pick3 (fun z => z = v) with ⟨c, qc, ag⟩ | ⟨z1, z2, z3, m1, m2, _, d12, _, _, _⟩
  · exact ⟨c, hQP c qc, ag v rfl hw⟩
  · exact absurd (m1.trans m2.symm) d12

/-- **Una línea de un camino de unidades**: con un testigo `lam` y la condición `LineOK` en todo trío, `v` fijado no
deja triángulos fantasma. Un solo nivel de descenso: los subtriángulos del testigo leen todo lo que lee. -/
theorem phantomFree_lineP (hl : LocPair φ P0 P σ) (D : PathN φ n lo hi) {v : Nat} (hv : stepVar φ σ = some v)
    (hvin : ∃ j, j < n ∧ InU lo hi j v) {lam : Int} (l0 : 0 ≤ lam) (lN : lam < Nn) (hσ0 : 0 ≤ σ) (hσN : σ < Nn)
    (HL : ∀ i j l : Int, LineOK φ n lo hi v lam i j l) : PhantomFree φ P0 P Nn σ := by
  classical
  refine phantomFree_of_descent hσ0 hσN
    (fun x u w => if (∀ z, XW φ lam v z → InW φ x.id.step u.id.step w.id.step z) then 0 else 1)
    (fun R Tf hS hanch x u w t ih => ?_)
  obtain ⟨a0, h0, hx0, hu0, hw0⟩ := t.b3 hS
  obtain ⟨f, hf, hfv, hM⟩ := HL x.id.step u.id.step w.id.step
  by_cases hb : ∀ z, XW φ lam v z → InW φ x.id.step u.id.step w.id.step z
  · -- la base: las caras de `σ`
    rcases faces_sigma hS hanch hσ0 hσN t h0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
    · exact h
    exact tri_of_pieces hl D hv hvin h0 hx0 hu0 hw0 hf hfv (fun _ h => h) (Or.inr hb) (pieces_of_faces F hM)
      (pv_of_faces F (fun _ h => h))
  · -- el testigo: sus subtriángulos leen todo lo que lee, y caen en la base
    obtain ⟨s, hs, hno⟩ : ∃ s, XW φ lam v s ∧ ¬ InW φ x.id.step u.id.step w.id.step s :=
      Classical.byContradiction (fun hn => hb (fun z hz => Classical.byContradiction (fun hz' => hn ⟨z, hz, hz'⟩)))
    obtain ⟨c1, c2, c3, F⟩ := faces_PwAll hS t hx0 hu0 hw0 l0 lN hs.1 hno (fun x' u' w' t' hr => ih x' u' w' t' (by
      rw [if_pos (fun z hz => hr z hz.1), if_neg hb]; omega))
    exact tri_of_pieces hl D hv hvin h0 hx0 hu0 hw0 hf hfv (fun _ h => h.1)
      (Or.inl (fun _ _ h h' _ hz => agree_at h.2 h'.2 hz)) (pieces_of_faces F hM) (pv_of_faces F (fun _ h => h.1))

end Line

end GPathB

end AbsSatBingo.Model
