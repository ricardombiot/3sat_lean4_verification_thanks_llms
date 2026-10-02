-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnSep.lean
import AbsSatBingo.Model.ForbidOnWeak

/-!
# La composición: dos bloques que comparten una variable

Con dos cláusulas que comparten una variable la condición de un paso (`Helly4`) ya falla: en `(p ∨ q ∨ s)`,
`(¬s ∨ r ∨ v)`, los nodos `p = 0`, `q = 0`, `r = 0` van juntos en una rama, y dos a dos con `v = 0`, pero no los tres
con `v = 0`. Lo cierra la regla **en el paso de la variable compartida**, y aquí se demuestra con un argumento de dos
pasos sobre la estructura cerrada (`PhantomFree`, la condición de todos los pasos), sin máquina:

* **Paso de la variable compartida `s`** (`tri_glue`). El triángulo `(x, u, w)` tiene un testigo `t` en un paso que
  lee `s`, con las tres caras sin prohibir. Si las tres caras son de ramas de `P`, las tres leen `s` igual, y con `s`
  fijada los dos lados no se ven: se toma una rama para el lado izquierdo `L` y otra para el derecho `Rr`, cada una
  elegida entre las tres por la cuenta del parche (`three_cover`: un lado sin tres variables distintas), y se pegan
  (`glue`).
* **Las caras** (`tri_lam`). Una cara tiene un nodo en el paso de `s`, así que sus ramas ya leen `s` igual, y basta
  parchear el lado derecho con el testigo del paso fijado `σ`: al lado derecho, quitando `s` y la variable de `σ`,
  le queda a lo sumo una variable.

`phantomFree_sep` junta los dos pasos (y el caso en que la variable fijada es la propia `s`: el testigo de `σ` sirve de
separador). **`SepData φ v s L Rr`** es lo que se pide a la fórmula alrededor de la variable `v`: una variable `s` y dos
lados `L`, `Rr` sin `s`, disjuntos, cada uno sin tres variables distintas, con `v = s` o `v` en `Rr`, y cada cláusula
entera fuera, entera en `L ∪ {s}` o entera en `Rr ∪ {s}`. **`Sep2 φ`**: toda variable tiene esos datos. Lo cumplen los
bloques de `ForbidOnBlock` (`L` vacío, `s = v`) y los pares de cláusulas que comparten una sola variable.

Resultado, sin hipótesis sobre la máquina: `phantomAt_of_sep2`, `hRead_of_sep2`,

  `spineVerdictOn_iff_of_sep2`, `machineExact_of_sep2`, `reader_on_sep2`.

Bajo la primera ventana prohibida no hay nada que demostrar (`validUpTo_pre`: toda asignación vale, mayoría).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

-- ============================================================
-- La cuenta, y pegar dos lados
-- ============================================================

theorem patch_empty (a' a0 : Assign) : patch (fun _ => False) a' a0 = a0 :=
  funext fun _ => patch_out (fun h => h)

/-- `c` coincide con `a0` en las variables de `M` que lee la ventana del paso `k`. -/
def AgreeOn (φ : Cnf) (M : Nat → Prop) (c a0 : Assign) (k : Int) : Prop :=
  ∀ k' z, InWin k k' → stepVar φ k' = some z → M z → c z = a0 z

theorem agreeOn_of_pid (M : Nat → Prop) {c a0 : Assign} {k : Int} (h : pidOfAssign φ c k = pidOfAssign φ a0 k) :
    AgreeOn φ M c a0 k := fun _ _ hw hz _ => var_of_pid_eq h hw hz

/-- Una rama que coincide con `a0` en todas las variables de la ventana pasa por la ventana de `a0`. -/
theorem pid_of_agree {a a0 : Assign} {k : Int} (h : ∀ k' z, InWin k k' → stepVar φ k' = some z → a z = a0 z) :
    pidOfAssign φ a k = pidOfAssign φ a0 k :=
  pid_eq_of_sels (sel_eq_of_var fun z hz => h k z (Or.inl rfl) hz)
    (fun hk => sel_eq_of_var fun z hz => h _ z (Or.inr (Or.inl ⟨hk, rfl⟩)) hz)
    (fun hk => sel_eq_of_var fun z hz => h _ z (Or.inr (Or.inr ⟨hk, rfl⟩)) hz)

/-- **La cuenta del parche**: tres ramas que pasan cada una por dos de tres ventanas de `a0` (aquí solo hacen falta
`c1` por `i` y `j`, y `c2` por `i`); si `M` no tiene tres variables distintas, alguna coincide con `a0` en las
variables de `M` de la ventana que le falta. -/
theorem three_cover {M : Nat → Prop}
    (hM : ∀ z1 z2 z3, M z1 → M z2 → M z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False)
    {a0 c1 c2 c3 : Assign} {i j l : Int}
    (e1 : pidOfAssign φ c1 i = pidOfAssign φ a0 i) (e2 : pidOfAssign φ c2 i = pidOfAssign φ a0 i)
    (e3 : pidOfAssign φ c1 j = pidOfAssign φ a0 j) :
    AgreeOn φ M c1 a0 l ∨ AgreeOn φ M c2 a0 j ∨ AgreeOn φ M c3 a0 i := by
  have alt : ∀ (c : Assign) (k : Int), AgreeOn φ M c a0 k ∨
      ∃ k' z, InWin k k' ∧ stepVar φ k' = some z ∧ M z ∧ c z ≠ a0 z := by
    intro c k
    by_cases hex : ∃ k' z, InWin k k' ∧ stepVar φ k' = some z ∧ M z ∧ c z ≠ a0 z
    · exact Or.inr hex
    · left
      intro k' z hw hz hm
      by_cases he : c z = a0 z
      · exact he
      · exact absurd ⟨k', z, hw, hz, hm, he⟩ hex
  rcases alt c1 l with g | ⟨k1, z1, w1, v1, b1, n1⟩
  · exact Or.inl g
  rcases alt c2 j with g | ⟨k2, z2, w2, v2, b2, n2⟩
  · exact Or.inr (Or.inl g)
  rcases alt c3 i with g | ⟨k3, z3, w3, v3, b3, n3⟩
  · exact Or.inr (Or.inr g)
  exfalso
  have p12 : c1 z2 = a0 z2 := var_of_pid_eq e3 w2 v2
  have p13 : c1 z3 = a0 z3 := var_of_pid_eq e1 w3 v3
  have p23 : c2 z3 = a0 z3 := var_of_pid_eq e2 w3 v3
  exact hM z1 z2 z3 b1 b2 b3 (fun e => n1 (by rw [e]; exact p12)) (fun e => n1 (by rw [e]; exact p13))
    (fun e => n2 (by rw [e]; exact p23))

/-- **Pegar**: `c'` en el lado derecho, `c` en el izquierdo y en `s`, `a0` en lo demás. -/
noncomputable def glue (s : Nat) (L Rr : Nat → Prop) (c c' a0 : Assign) : Assign :=
  patch Rr c' (patch (fun z => L z ∨ z = s) c a0)

namespace GPathB

variable {P0 P : Assign → Prop} {N σ : Int} {R : PathNodeId → PathNodeId → Prop} {Tf : Trios}

-- ============================================================
-- Sobre una estructura cerrada
-- ============================================================

/-- Las parejas de una estructura cerrada son de ramas de `P`, sin más: el testigo del paso `σ` da un triángulo, y su
rama pasa por un nodo de `σ`. -/
theorem pairs_of_struct (hσ0 : 0 ≤ σ) (hσN : σ < N) (hS : PhStruct φ P0 N R Tf)
    (hanch : ∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a) :
    ∀ y w, R y w → ∃ a, P a ∧ pidOfAssign φ a y.id.step = y ∧ pidOfAssign φ a w.id.step = w := by
  intro y w hyw
  obtain ⟨s, hss, hys, hws, hor⟩ := hS.pair y w hyw σ hσ0 hσN
  by_cases e : y = w
  · subst e
    obtain ⟨a, ha, h1, h2⟩ := hS.b2 y s hys
    exact ⟨a, hanch a s ha (hS.refl y s hys).2 hss (by rw [← hss]; exact h2), h1, h1⟩
  · by_cases hsy : s = y
    · obtain ⟨a, ha, h1, h2⟩ := hS.b2 y w hyw
      exact ⟨a, hanch a s ha (hS.refl s s (by rw [hsy]; exact (hS.refl y w hyw).1)).1 hss
        (by rw [← hss, hsy]; exact h1), h1, h2⟩
    · by_cases hsw : s = w
      · obtain ⟨a, ha, h1, h2⟩ := hS.b2 y w hyw
        exact ⟨a, hanch a s ha (hS.refl s s (by rw [hsw]; exact (hS.refl y w hyw).2)).1 hss
          (by rw [← hss, hsw]; exact h2), h1, h2⟩
      · have hnT : ¬ Tf y w s := by
          rcases hor with h' | h' | h' | h'
          · exact absurd h' e
          · exact absurd h' hsy
          · exact absurd h' hsw
          · exact h'
        obtain ⟨a, ha, h1, h2, h3⟩ := hS.b3 y w s hyw hys hws e (Ne.symm hsy) (Ne.symm hsw) hnT
        exact ⟨a, hanch a s ha (hS.refl y s hys).2 hss (by rw [← hss]; exact h3), h1, h2⟩

/-- Un triángulo sin prohibir de la estructura, y «es de una rama de `P`». -/
def TriOf (φ : Cnf) (P : Assign → Prop) (x u w : PathNodeId) : Prop :=
  ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w

/-- Un triángulo con un nodo en el paso `σ` es de una rama de `P`: su rama de `P0` pasa por ese nodo. -/
theorem tri_anchor (hS : PhStruct φ P0 N R Tf)
    (hanch : ∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a) :
    ∀ x u w, R x u → R x w → R u w → x ≠ u → x ≠ w → u ≠ w → ¬ Tf x u w →
      (x.id.step = σ ∨ u.id.step = σ ∨ w.id.step = σ) → TriOf φ P x u w := by
  intro x u w hxu hxw huw nxu nxw nuw hn hor
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := hS.b3 x u w hxu hxw huw nxu nxw nuw hn
  rcases hor with h | h | h
  · exact ⟨a0, hanch a0 x hP0 (hS.refl x u hxu).1 h (by rw [← h]; exact hx0), hx0, hu0, hw0⟩
  · exact ⟨a0, hanch a0 u hP0 (hS.refl x u hxu).2 h (by rw [← h]; exact hu0), hx0, hu0, hw0⟩
  · exact ⟨a0, hanch a0 w hP0 (hS.refl x w hxw).2 h (by rw [← h]; exact hw0), hx0, hu0, hw0⟩

/-- **Las caras**: un triángulo con su primer nodo en un paso que lee `s`. El testigo del paso `σ` da dos ramas de `P`
por ese nodo, que leen `s` como `a0`; al lado derecho le queda una sola variable aparte de la de `σ`, y una de las
dos coincide con `a0` en ella. -/
theorem tri_lam {lam : Int} {s : Nat} {Rr : Nat → Prop} (hσ0 : 0 ≤ σ) (hσN : σ < N)
    (hsl : stepVar φ lam = some s)
    (hcard : ∀ z1 z2, Rr z1 → Rr z2 → z1 ≠ z2 → stepVar φ σ = some z1 ∨ stepVar φ σ = some z2)
    (hG0 : ∀ a0 a', P0 a0 → P a' → a' s = a0 s → P (patch Rr a' a0))
    (hS : PhStruct φ P0 N R Tf)
    (hanch : ∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a) :
    ∀ x u w, R x u → R x w → R u w → x ≠ u → x ≠ w → u ≠ w → ¬ Tf x u w → x.id.step = lam → TriOf φ P x u w := by
  intro x u w hxu hxw huw nxu nxw nuw hn hxl
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := hS.b3 x u w hxu hxw huw nxu nxw nuw hn
  obtain ⟨n, hns, hxn, hun, hwn, hor⟩ := hS.trio x u w hxu hxw huw nxu nxw nuw hn σ hσ0 hσN
  have hRn := (hS.refl x n hxn).2
  by_cases hnx : n = x
  · exact ⟨a0, hanch a0 n hP0 hRn hns (by rw [← hns, hnx]; exact hx0), hx0, hu0, hw0⟩
  by_cases hnu : n = u
  · exact ⟨a0, hanch a0 n hP0 hRn hns (by rw [← hns, hnu]; exact hu0), hx0, hu0, hw0⟩
  by_cases hnw : n = w
  · exact ⟨a0, hanch a0 n hP0 hRn hns (by rw [← hns, hnw]; exact hw0), hx0, hu0, hw0⟩
  obtain ⟨m1, m2, _⟩ : ¬ Tf x u n ∧ ¬ Tf x w n ∧ ¬ Tf u w n := by
    rcases hor with h' | h' | h' | h'
    · exact absurd h' hnx
    · exact absurd h' hnu
    · exact absurd h' hnw
    · exact h'
  obtain ⟨a1, hP1, hx1, hu1, hn1⟩ := hS.b3 x u n hxu hxn hun nxu (Ne.symm hnx) (Ne.symm hnu) m1
  obtain ⟨a2, hP2, hx2, hw2, hn2⟩ := hS.b3 x w n hxw hxn hwn nxw (Ne.symm hnx) (Ne.symm hnw) m2
  have q1 : P a1 := hanch a1 n hP1 hRn hns (by rw [← hns]; exact hn1)
  have q2 : P a2 := hanch a2 n hP2 hRn hns (by rw [← hns]; exact hn2)
  have e1x := hx1.trans hx0.symm
  have e1u := hu1.trans hu0.symm
  have e2x := hx2.trans hx0.symm
  have e2w := hw2.trans hw0.symm
  have s1 : a1 s = a0 s := var_of_pid_eq e1x (Or.inl rfl) (by rw [hxl]; exact hsl)
  have s2 : a2 s = a0 s := var_of_pid_eq e2x (Or.inl rfl) (by rw [hxl]; exact hsl)
  have sn : pidOfAssign φ a2 σ = pidOfAssign φ a1 σ := by rw [← hns]; exact hn2.trans hn1.symm
  rcases pid_patch_or (φ := φ) Rr a1 a0 w.id.step with g | ⟨k1, z1, w1, v1, b1, d1⟩
  · exact ⟨_, hG0 a0 a1 hP0 q1 s1, (pid_patch_of_pass Rr e1x).trans hx0, (pid_patch_of_pass Rr e1u).trans hu0,
      g.trans hw0⟩
  rcases pid_patch_or (φ := φ) Rr a2 a0 u.id.step with g | ⟨k2, z2, w2, v2, b2, d2⟩
  · exact ⟨_, hG0 a0 a2 hP0 q2 s2, (pid_patch_of_pass Rr e2x).trans hx0, g.trans hu0,
      (pid_patch_of_pass Rr e2w).trans hw0⟩
  exfalso
  have p21 : a2 z1 = a0 z1 := var_of_pid_eq e2w w1 v1
  have p12 : a1 z2 = a0 z2 := var_of_pid_eq e1u w2 v2
  have d12 : z1 ≠ z2 := fun e => d1 (by rw [e]; exact p12)
  rcases hcard z1 z2 b1 b2 d12 with hz | hz
  · exact d1 ((var_of_pid_eq sn (Or.inl rfl) hz).symm.trans p21)
  · exact d2 ((var_of_pid_eq sn (Or.inl rfl) hz).trans p12)

/-- Lo mismo con el nodo del paso de `s` en cualquiera de los tres sitios. -/
theorem tri_lam_any {lam : Int} {s : Nat} {Rr : Nat → Prop} (hσ0 : 0 ≤ σ) (hσN : σ < N)
    (hsl : stepVar φ lam = some s)
    (hcard : ∀ z1 z2, Rr z1 → Rr z2 → z1 ≠ z2 → stepVar φ σ = some z1 ∨ stepVar φ σ = some z2)
    (hG0 : ∀ a0 a', P0 a0 → P a' → a' s = a0 s → P (patch Rr a' a0))
    (hS : PhStruct φ P0 N R Tf)
    (hanch : ∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a) :
    ∀ x u w, R x u → R x w → R u w → x ≠ u → x ≠ w → u ≠ w → ¬ Tf x u w →
      (x.id.step = lam ∨ u.id.step = lam ∨ w.id.step = lam) → TriOf φ P x u w := by
  intro x u w hxu hxw huw nxu nxw nuw hn hor
  have base := tri_lam hσ0 hσN hsl hcard hG0 hS hanch
  rcases hor with h | h | h
  · exact base x u w hxu hxw huw nxu nxw nuw hn h
  · obtain ⟨a, ha, h1, h2, h3⟩ := base u x w (hS.symm _ _ hxu) huw hxw (Ne.symm nxu) nuw nxw
      (fun hf => hn (hS.sw12 u x w (hS.symm _ _ hxu) huw hxw hf)) h
    exact ⟨a, ha, h2, h1, h3⟩
  · obtain ⟨a, ha, h1, h2, h3⟩ := base w x u (hS.symm _ _ hxw) (hS.symm _ _ huw) hxu (Ne.symm nxw) (Ne.symm nuw) nxu
      (fun hf => hn (hS.sw23 x w u hxw hxu (hS.symm _ _ huw)
        (hS.sw12 w x u (hS.symm _ _ hxw) (hS.symm _ _ huw) hxu hf))) h
    exact ⟨a, ha, h2, h3, h1⟩

/-- **El paso de la variable compartida.** Si los triángulos con un nodo en un paso `lam` que lee `s` son de ramas de
`P`, todos lo son: el testigo del triángulo en `lam` da tres ramas de `P` que leen `s` igual; se elige una para cada
lado y se pegan. -/
theorem tri_glue {lam : Int} {s : Nat} {L Rr : Nat → Prop} (hl0 : 0 ≤ lam) (hlN : lam < N)
    (hsl : stepVar φ lam = some s)
    (hL : ∀ z1 z2 z3, L z1 → L z2 → L z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False)
    (hR : ∀ z1 z2 z3, Rr z1 → Rr z2 → Rr z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False)
    (hG : ∀ a0 c c', P0 a0 → P c → P c' → c s = c' s → P (glue s L Rr c c' a0))
    (hS : PhStruct φ P0 N R Tf)
    (h0 : ∀ x u w, R x u → R x w → R u w → x ≠ u → x ≠ w → u ≠ w → ¬ Tf x u w →
      (x.id.step = lam ∨ u.id.step = lam ∨ w.id.step = lam) → TriOf φ P x u w) :
    ∀ x u w, R x u → R x w → R u w → x ≠ u → x ≠ w → u ≠ w → ¬ Tf x u w → TriOf φ P x u w := by
  intro x u w hxu hxw huw nxu nxw nuw hn
  obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := hS.b3 x u w hxu hxw huw nxu nxw nuw hn
  obtain ⟨t, hts, hxt, hut, hwt, hor⟩ := hS.trio x u w hxu hxw huw nxu nxw nuw hn lam hl0 hlN
  by_cases htx : t = x
  · exact h0 x u w hxu hxw huw nxu nxw nuw hn (Or.inl (by rw [← htx]; exact hts))
  by_cases htu : t = u
  · exact h0 x u w hxu hxw huw nxu nxw nuw hn (Or.inr (Or.inl (by rw [← htu]; exact hts)))
  by_cases htw : t = w
  · exact h0 x u w hxu hxw huw nxu nxw nuw hn (Or.inr (Or.inr (by rw [← htw]; exact hts)))
  obtain ⟨m1, m2, m3⟩ : ¬ Tf x u t ∧ ¬ Tf x w t ∧ ¬ Tf u w t := by
    rcases hor with h' | h' | h' | h'
    · exact absurd h' htx
    · exact absurd h' htu
    · exact absurd h' htw
    · exact h'
  obtain ⟨c1, q1, c1x, c1u, c1t⟩ := h0 x u t hxu hxt hut nxu (Ne.symm htx) (Ne.symm htu) m1 (Or.inr (Or.inr hts))
  obtain ⟨c2, q2, c2x, c2w, c2t⟩ := h0 x w t hxw hxt hwt nxw (Ne.symm htx) (Ne.symm htw) m2 (Or.inr (Or.inr hts))
  obtain ⟨c3, q3, c3u, c3w, c3t⟩ := h0 u w t huw hut hwt nuw (Ne.symm htu) (Ne.symm htw) m3 (Or.inr (Or.inr hts))
  have e1 := c1x.trans hx0.symm
  have e2 := c2x.trans hx0.symm
  have e3 := c1u.trans hu0.symm
  have e4 := c3u.trans hu0.symm
  have e5 := c2w.trans hw0.symm
  have e6 := c3w.trans hw0.symm
  have s21 : c2 s = c1 s := var_of_pid_eq (c2t.trans c1t.symm) (Or.inl rfl) (by rw [hts]; exact hsl)
  have s31 : c3 s = c1 s := var_of_pid_eq (c3t.trans c1t.symm) (Or.inl rfl) (by rw [hts]; exact hsl)
  -- una rama para cada lado
  have pick : ∀ M : Nat → Prop, (∀ z1 z2 z3, M z1 → M z2 → M z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False) →
      ∃ c, P c ∧ c s = c1 s ∧ AgreeOn φ M c a0 x.id.step ∧ AgreeOn φ M c a0 u.id.step ∧
        AgreeOn φ M c a0 w.id.step := by
    intro M hM
    rcases three_cover (c3 := c3) (l := w.id.step) hM e1 e2 e3 with g | g | g
    · exact ⟨c1, q1, rfl, agreeOn_of_pid M e1, agreeOn_of_pid M e3, g⟩
    · exact ⟨c2, q2, s21, agreeOn_of_pid M e2, g, agreeOn_of_pid M e5⟩
    · exact ⟨c3, q3, s31, g, agreeOn_of_pid M e4, agreeOn_of_pid M e6⟩
  obtain ⟨cL, qL, sL, lx, lu, lw⟩ := pick L hL
  obtain ⟨cR, qR, sR, rx, ru, rw'⟩ := pick Rr hR
  -- `s` se lee igual en las ventanas del triángulo
  have sx : ∀ k', InWin x.id.step k' → stepVar φ k' = some s → c1 s = a0 s := fun _ hw hz => var_of_pid_eq e1 hw hz
  have su : ∀ k', InWin u.id.step k' → stepVar φ k' = some s → c1 s = a0 s := fun _ hw hz => var_of_pid_eq e3 hw hz
  have sw : ∀ k', InWin w.id.step k' → stepVar φ k' = some s → c1 s = a0 s := fun _ hw hz =>
    s21.symm.trans (var_of_pid_eq e5 hw hz)
  have win : ∀ k : Int, AgreeOn φ L cL a0 k → AgreeOn φ Rr cR a0 k →
      (∀ k', InWin k k' → stepVar φ k' = some s → c1 s = a0 s) →
      pidOfAssign φ (glue s L Rr cL cR a0) k = pidOfAssign φ a0 k := by
    intro k hl hr hs
    refine pid_of_agree (fun k' z hw hz => ?_)
    unfold glue
    by_cases h1 : Rr z
    · rw [patch_in h1]; exact hr k' z hw hz h1
    · rw [patch_out h1]
      by_cases h2 : L z ∨ z = s
      · rw [patch_in (B := fun z => L z ∨ z = s) h2]
        rcases h2 with h2 | h2
        · exact hl k' z hw hz h2
        · rw [h2]; exact sL.trans (hs k' hw (by rw [← h2]; exact hz))
      · exact patch_out (B := fun z => L z ∨ z = s) h2
  exact ⟨glue s L Rr cL cR a0, hG a0 cL cR hP0 qL qR (sL.trans sR.symm), (win _ lx rx sx).trans hx0,
    (win _ lu ru su).trans hu0, (win _ lw rw' sw).trans hw0⟩

/-- **Sin familias fantasma, por una variable que separa.** Con un paso `lam` que lee `s`, dos lados sin tres
variables distintas y la clausura por pegado; y, o bien `lam` es el propio paso fijado, o bien el lado derecho tiene
una sola variable aparte de la del paso fijado y `P` es cerrado por el parche del lado derecho con `s` igual. -/
theorem phantomFree_sep {lam : Int} {s : Nat} {L Rr : Nat → Prop} (hσ0 : 0 ≤ σ) (hσN : σ < N) (hl0 : 0 ≤ lam)
    (hlN : lam < N) (hsl : stepVar φ lam = some s)
    (hL : ∀ z1 z2 z3, L z1 → L z2 → L z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False)
    (hR : ∀ z1 z2 z3, Rr z1 → Rr z2 → Rr z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False)
    (hG : ∀ a0 c c', P0 a0 → P c → P c' → c s = c' s → P (glue s L Rr c c' a0))
    (h0 : lam = σ ∨ ((∀ z1 z2, Rr z1 → Rr z2 → z1 ≠ z2 → stepVar φ σ = some z1 ∨ stepVar φ σ = some z2) ∧
      ∀ a0 a', P0 a0 → P a' → a' s = a0 s → P (patch Rr a' a0))) : PhantomFree φ P0 P N σ := by
  intro R Tf hrefl hsymm hsw23 hsw12 hsteps hpair htrio hb2 hb3 hanch
  have hS : PhStruct φ P0 N R Tf := ⟨hrefl, hsymm, hsw23, hsw12, hsteps, hpair, htrio, hb2, hb3⟩
  refine ⟨pairs_of_struct hσ0 hσN hS hanch, tri_glue hl0 hlN hsl hL hR hG hS ?_⟩
  rcases h0 with h0 | ⟨hcard, hG0⟩
  · rw [h0]; exact tri_anchor hS hanch
  · exact tri_lam_any hσ0 hσN hsl hcard hG0 hS hanch

end GPathB

-- ============================================================
-- Lo que se pide a la fórmula
-- ============================================================

/-- **`SepData φ v s L Rr`**: alrededor de la variable `v`, una variable `s` que separa dos lados `L` y `Rr`. Cada
cláusula está entera fuera, entera en `L ∪ {s}` o entera en `Rr ∪ {s}`; cada lado no tiene tres variables distintas;
`v` es `s` o está en `Rr`, y en ese caso `Rr` no tiene otra variable más que una aparte de `v`. -/
structure SepData (φ : Cnf) (v s : Nat) (L Rr : Nat → Prop) : Prop where
  sv    : v ≠ s → s < φ.nVars
  nR    : ¬ Rr s
  disj  : ∀ z, L z → Rr z → False
  mem   : v = s ∨ Rr v
  cardL : ∀ z1 z2 z3, L z1 → L z2 → L z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False
  cardR : ∀ z1 z2 z3, Rr z1 → Rr z2 → Rr z3 → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 → False
  card0 : v ≠ s → ∀ z1 z2, Rr z1 → Rr z2 → z1 ≠ z2 → z1 = v ∨ z2 = v
  cl    : ∀ c ∈ φ.clauses,
    ((¬ (Rr c.l1.v ∨ L c.l1.v ∨ c.l1.v = s)) ∧ (¬ (Rr c.l2.v ∨ L c.l2.v ∨ c.l2.v = s)) ∧
      (¬ (Rr c.l3.v ∨ L c.l3.v ∨ c.l3.v = s))) ∨
    ((L c.l1.v ∨ c.l1.v = s) ∧ (L c.l2.v ∨ c.l2.v = s) ∧ (L c.l3.v ∨ c.l3.v = s)) ∨
    ((Rr c.l1.v ∨ c.l1.v = s) ∧ (Rr c.l2.v ∨ c.l2.v = s) ∧ (Rr c.l3.v ∨ c.l3.v = s))

/-- **`Sep2 φ`**: toda variable tiene una variable que separa dos lados pequeños. -/
def Sep2 (φ : Cnf) : Prop := ∀ v, ∃ s L Rr, SepData φ v s L Rr

section Glue

variable {v s : Nat} {L Rr : Nat → Prop} {c c' a0 : Assign}

theorem glue_Lp (D : SepData φ v s L Rr) {z : Nat} (h : L z ∨ z = s) : glue s L Rr c c' a0 z = c z := by
  have nr : ¬ Rr z := by
    rcases h with h | h
    · exact fun hr => D.disj z h hr
    · rw [h]; exact D.nR
  unfold glue
  rw [patch_out nr]
  exact patch_in (B := fun z => L z ∨ z = s) h

theorem glue_Rp (D : SepData φ v s L Rr) (hss : c s = c' s) {z : Nat} (h : Rr z ∨ z = s) :
    glue s L Rr c c' a0 z = c' z := by
  rcases h with h | h
  · exact patch_in h
  · rw [glue_Lp D (Or.inr h), h]; exact hss

theorem glue_out {z : Nat} (h1 : ¬ Rr z) (h2 : ¬ (L z ∨ z = s)) : glue s L Rr c c' a0 z = a0 z := by
  unfold glue
  rw [patch_out h1]
  exact patch_out (B := fun z => L z ∨ z = s) h2

/-- Donde las tres eligen lo mismo, la pegada también. -/
theorem sel_glue_all {k : Int} {x : NodeId} (hc : selOfAssign φ c k = x) (hc' : selOfAssign φ c' k = x)
    (h0 : selOfAssign φ a0 k = x) : selOfAssign φ (glue s L Rr c c' a0) k = x :=
  sel_patch_both _ hc' (sel_patch_both _ hc h0)

/-- En un paso que lee una variable de los lados o `s`, la pegada elige lo que eligen `c` y `c'`. -/
theorem sel_glue_at {k : Int} {x : NodeId} (hv : ∀ z, stepVar φ k = some z → Rr z ∨ L z ∨ z = s)
    (hc : selOfAssign φ c k = x) (hc' : selOfAssign φ c' k = x) : selOfAssign φ (glue s L Rr c c' a0) k = x := by
  rw [← hc']
  refine sel_eq_of_var (fun z hz => ?_)
  have ecc : c z = c' z := var_eq_of_sel (hc.trans hc'.symm) z hz
  by_cases h1 : Rr z
  · exact patch_in h1
  · have h2 : L z ∨ z = s := by
      rcases hv z hz with h | h
      · exact absurd h h1
      · exact h
    unfold glue
    rw [patch_out h1, patch_in (B := fun z => L z ∨ z = s) h2]
    exact ecc

/-- **La pegada no pisa ventanas prohibidas**: una cláusula está entera en un lado (con `s`) o entera fuera. -/
theorem not_prohibited_glue (D : SepData φ v s L Rr) (hss : c s = c' s) {k : Int}
    (hc : isProhibited φ (pidOfAssign φ c k) = false) (hc' : isProhibited φ (pidOfAssign φ c' k) = false)
    (h0 : isProhibited φ (pidOfAssign φ a0 k) = false ∨ ∃ z, stepVar φ k = some z ∧ (Rr z ∨ L z ∨ z = s)) :
    isProhibited φ (pidOfAssign φ (glue s L Rr c c' a0) k) = false := by
  cases hp : isProhibited φ (pidOfAssign φ (glue s L Rr c c' a0) k) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨j, cl, hj, e, m1, m2, m3⟩ := prohibited_clause hp
    rcases D.cl cl (List.mem_of_getElem? hj) with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩
    · have out : ∀ {z : Nat}, ¬ (Rr z ∨ L z ∨ z = s) → glue s L Rr c c' a0 z = a0 z := fun h =>
        glue_out (fun hr => h (Or.inl hr)) (fun hl => h (Or.inr hl))
      have pr := prohibited_of_false (a := a0) hj ((litVal_congr (out o1).symm).trans m1)
        ((litVal_congr (out o2).symm).trans m2) ((litVal_congr (out o3).symm).trans m3)
      rw [← e] at pr
      rcases h0 with h0 | ⟨z, hz, hin⟩
      · rw [h0] at pr; cases pr
      · have hs : stepVar φ k = some cl.l3.v := by rw [e]; exact stepVar_clause hj 2 (by omega)
        rw [hs] at hz; cases hz
        exact o3 hin
    · have pr := prohibited_of_false (a := c) hj ((litVal_congr (glue_Lp D i1).symm).trans m1)
        ((litVal_congr (glue_Lp D i2).symm).trans m2) ((litVal_congr (glue_Lp D i3).symm).trans m3)
      rw [← e, hc] at pr; cases pr
    · have pr := prohibited_of_false (a := c') hj ((litVal_congr (glue_Rp D hss i1).symm).trans m1)
        ((litVal_congr (glue_Rp D hss i2).symm).trans m2) ((litVal_congr (glue_Rp D hss i3).symm).trans m3)
      rw [← e, hc'] at pr; cases pr

/-- **El parche del lado derecho no pisa ventanas prohibidas**, si las dos ramas leen `s` igual. -/
theorem not_prohibited_patchR (D : SepData φ v s L Rr) {a' : Assign} (hss : a' s = a0 s) {k : Int}
    (h' : isProhibited φ (pidOfAssign φ a' k) = false)
    (h0 : isProhibited φ (pidOfAssign φ a0 k) = false ∨ ∃ z, stepVar φ k = some z ∧ Rr z) :
    isProhibited φ (pidOfAssign φ (patch Rr a' a0) k) = false := by
  cases hp : isProhibited φ (pidOfAssign φ (patch Rr a' a0) k) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨j, cl, hj, e, m1, m2, m3⟩ := prohibited_clause hp
    have inR : ∀ {z : Nat}, (Rr z ∨ z = s) → patch Rr a' a0 z = a' z := by
      intro z h
      rcases h with h | h
      · exact patch_in h
      · rw [h, patch_out D.nR]; exact hss.symm
    have outR : ∀ {z : Nat}, ¬ Rr z → patch Rr a' a0 z = a0 z := fun h => patch_out h
    have fin : ¬ Rr cl.l1.v → ¬ Rr cl.l2.v → ¬ Rr cl.l3.v → False := by
      intro o1 o2 o3
      have pr := prohibited_of_false (a := a0) hj ((litVal_congr (outR o1).symm).trans m1)
        ((litVal_congr (outR o2).symm).trans m2) ((litVal_congr (outR o3).symm).trans m3)
      rw [← e] at pr
      rcases h0 with h0 | ⟨z, hz, hin⟩
      · rw [h0] at pr; cases pr
      · have hs : stepVar φ k = some cl.l3.v := by rw [e]; exact stepVar_clause hj 2 (by omega)
        rw [hs] at hz; cases hz
        exact o3 hin
    have notR : ∀ {z : Nat}, (L z ∨ z = s) → ¬ Rr z := by
      intro z h hr
      rcases h with h | h
      · exact D.disj z h hr
      · rw [h] at hr; exact D.nR hr
    rcases D.cl cl (List.mem_of_getElem? hj) with ⟨o1, o2, o3⟩ | ⟨i1, i2, i3⟩ | ⟨i1, i2, i3⟩
    · exact fin (fun h => o1 (Or.inl h)) (fun h => o2 (Or.inl h)) (fun h => o3 (Or.inl h))
    · exact fin (notR i1) (notR i2) (notR i3)
    · have pr := prohibited_of_false (a := a') hj ((litVal_congr (inR i1).symm).trans m1)
        ((litVal_congr (inR i2).symm).trans m2) ((litVal_congr (inR i3).symm).trans m3)
      rw [← e, h'] at pr; cases pr

end Glue

theorem stepVar_var {s : Nat} (hs : s < φ.nVars) : stepVar φ (varStep s) = some s := by
  have h0 : ¬ varStep s ≤ 0 := by simp only [varStep]; omega
  have h1 : varStep s < midFusion φ := by simp only [varStep, midFusion]; omega
  simp only [stepVar, if_neg h0, if_pos h1, varOfStep_varStep]

namespace GPathB

open Driver Machine MachineOn

/-- **De los datos de la fórmula a sin familias fantasma**, para cualquier par de familias `P0`, `P` cerrado por la
pegada y por el parche del lado derecho (lo son las de las tres situaciones: filtro, UP y lectura). -/
theorem phantomFree_of_sep2 (hcl : Sep2 φ) {P0 P : Assign → Prop} {N σ : Int} (hσ0 : 0 ≤ σ) (hσN : σ < N)
    (hN : midFusion φ < N)
    (hglue : ∀ v s L Rr, stepVar φ σ = some v → SepData φ v s L Rr →
      ∀ a0 c c', P0 a0 → P c → P c' → c s = c' s → P (glue s L Rr c c' a0))
    (hpatch : ∀ v s L Rr, stepVar φ σ = some v → SepData φ v s L Rr → v ≠ s →
      ∀ a0 a', P0 a0 → P a' → a' s = a0 s → P (patch Rr a' a0))
    (hnone : stepVar φ σ = none → ∀ a0 a', P0 a0 → P a' → P a0) : PhantomFree φ P0 P N σ := by
  cases hv : stepVar φ σ with
  | none =>
    refine phantomFree_of_helly4 hσ0 hσN (helly4_of_patch (fun _ => False)
      (fun _ _ _ h _ _ _ _ _ => absurd h (fun h => h)) (fun a0 a' h0 h' => ?_))
    rw [patch_empty]; exact hnone hv a0 a' h0 h'
  | some v =>
    obtain ⟨s, L, Rr, D⟩ := hcl v
    by_cases hvs : v = s
    · subst hvs
      exact phantomFree_sep hσ0 hσN hσ0 hσN hv D.cardL D.cardR (hglue v v L Rr hv D) (Or.inl rfl)
    · have hs := D.sv hvs
      have hl0 : 0 ≤ varStep s := by simp only [varStep]; omega
      have hlN : varStep s < N := by
        have : varStep s < midFusion φ := by simp only [varStep, midFusion]; omega
        omega
      refine phantomFree_sep hσ0 hσN hl0 hlN (stepVar_var hs) D.cardL D.cardR (hglue v s L Rr hv D)
        (Or.inr ⟨fun z1 z2 b1 b2 d => ?_, hpatch v s L Rr hv D hvs⟩)
      rcases D.card0 hvs z1 z2 b1 b2 d with e | e
      · exact Or.inl (by rw [e]; exact hv)
      · exact Or.inr (by rw [e]; exact hv)

/-- La variable del paso fijado está en los lados o es `s`. -/
theorem sep_mem {v s : Nat} {L Rr : Nat → Prop} (D : SepData φ v s L Rr) {σ : Int} (hv : stepVar φ σ = some v) :
    ∀ z, stepVar φ σ = some z → Rr z ∨ L z ∨ z = s := by
  intro z hz
  rw [hv] at hz; cases hz
  rcases D.mem with h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h

/-- En el paso fijado, el parche del lado derecho elige lo que elige `a'` (cuando `v` está en `Rr`). -/
theorem sel_patchR_at {v s : Nat} {L Rr : Nat → Prop} (D : SepData φ v s L Rr) (hvs : v ≠ s) {σ : Int}
    (hv : stepVar φ σ = some v) (a' a0 : Assign) :
    selOfAssign φ (patch Rr a' a0) σ = selOfAssign φ a' σ := by
  refine sel_eq_of_var (fun z hz => ?_)
  rw [hv] at hz; cases hz
  rcases D.mem with h | h
  · exact absurd h hvs
  · exact patch_in h

/-- Un paso que no lee ninguna variable no es el tercero de una cláusula. -/
theorem not_prohibited_none {a : Assign} {k : Int} (h : stepVar φ k = none) :
    isProhibited φ (pidOfAssign φ a k) = false := by
  cases hp : isProhibited φ (pidOfAssign φ a k) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨j, cl, hj, e, _⟩ := prohibited_clause hp
    rw [e, stepVar_clause hj 2 (by omega)] at h
    cases h

/-- **Toda fórmula con separadores cumple la condición fuerte en todas sus líneas.** -/
theorem phantomAt_of_sep2 (hb : Bounded φ) (hcl : Sep2 φ) (T : Int) (hT : 1 ≤ T) : PhantomAt φ T := by
  by_cases hlow : T + 1 ≤ midFusion φ + 3
  · -- bajo la primera ventana prohibida toda asignación vale: mayoría
    refine phantomAt_of_hellyAt hb hT (fun k d _ _ => ?_)
    refine ⟨fun r _ => helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_), helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_)⟩
    · exact ⟨⟨validUpTo_pre _ (by omega), by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
    · exact ⟨⟨validUpTo_pre _ hlow, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
        by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
  · intro k d hk hd
    have hds : d.step = T := by
      have := sonsOfMap_step φ k d hd
      have hks := mapNodes_step φ (T - 1) k hk
      omega
    refine ⟨fun r hr => ?_, ?_⟩
    · -- el filtro
      obtain ⟨r1, r2⟩ := reqOf_range hb r hr
      rw [hds] at r2
      refine phantomFree_of_sep2 hcl (by omega) r2 (by omega) (fun v s L Rr hv D a0 c c' h0 hc hc' hss => ?_)
        (fun v s L Rr hv D hvs a0 a' h0 h' hss => ?_) (fun hv a0 a' h0 h' => ?_)
      · exact ⟨⟨fun q hq => not_prohibited_glue D hss (hc.1.1 q hq) (hc'.1.1 q hq) (Or.inl (h0.1 q hq)),
          sel_glue_all hc.1.2 hc'.1.2 h0.2⟩, sel_glue_at (sep_mem D hv) hc.2 hc'.2⟩
      · exact ⟨⟨fun q hq => not_prohibited_patchR D hss (h'.1.1 q hq) (Or.inl (h0.1 q hq)),
          sel_patch_both _ h'.1.2 h0.2⟩, (sel_patchR_at D hvs hv a' a0).trans h'.2⟩
      · exact ⟨h0, (sel_eq_of_var (fun z hz => by rw [hv] at hz; cases hz)).trans h'.2⟩
    · -- el UP
      refine phantomFree_of_sep2 hcl (by omega) (by omega) (by omega) (fun v s L Rr hv D a0 c c' h0 hc hc' hss => ?_)
        (fun v s L Rr hv D hvs a0 a' h0 h' hss => ?_) (fun hv a0 a' h0 h' => ?_)
      · have hcT : selOfAssign φ c T = d := by have := hc.1.2; rwa [Int.add_sub_cancel] at this
        have hcT' : selOfAssign φ c' T = d := by have := hc'.1.2; rwa [Int.add_sub_cancel] at this
        refine ⟨⟨fun q hq => not_prohibited_glue D hss (hc.1.1 q hq) (hc'.1.1 q hq) ?_, ?_⟩,
          sel_glue_all hc.2 hc'.2 h0.1.2⟩
        · by_cases hqT : q = T
          · rw [hqT]; exact Or.inr ⟨v, hv, sep_mem D hv v hv⟩
          · exact Or.inl (h0.1.1 q (by omega))
        · show selOfAssign φ _ (T + 1 - 1) = d
          rw [Int.add_sub_cancel]
          exact sel_glue_at (sep_mem D hv) hcT hcT'
      · have hT' : selOfAssign φ a' T = d := by have := h'.1.2; rwa [Int.add_sub_cancel] at this
        have hRv : Rr v := by
          rcases D.mem with h | h
          · exact absurd h hvs
          · exact h
        refine ⟨⟨fun q hq => not_prohibited_patchR D hss (h'.1.1 q hq) ?_, ?_⟩, sel_patch_both _ h'.2 h0.1.2⟩
        · by_cases hqT : q = T
          · rw [hqT]; exact Or.inr ⟨v, hv, hRv⟩
          · exact Or.inl (h0.1.1 q (by omega))
        · show selOfAssign φ _ (T + 1 - 1) = d
          rw [Int.add_sub_cancel]
          exact (sel_patchR_at D hvs hv a' a0).trans hT'
      · have hT' : selOfAssign φ a' T = d := by have := h'.1.2; rwa [Int.add_sub_cancel] at this
        refine ⟨⟨fun q hq => ?_, ?_⟩, h0.1.2⟩
        · by_cases hqT : q = T
          · rw [hqT]; exact not_prohibited_none hv
          · exact h0.1.1 q (by omega)
        · show selOfAssign φ _ (T + 1 - 1) = d
          rw [Int.add_sub_cancel]
          exact (sel_eq_of_var (fun z hz => by rw [hv] at hz; cases hz)).trans hT'

/-- **La hipótesis de la lectura vale en toda fórmula con separadores.** -/
theorem hRead_of_sep2 (hcl : Sep2 φ) {T : Int} (hN : midFusion φ < T) (k : NodeId) : HRead φ T (SolE φ T k) := by
  intro R r _ hr1 hrT
  refine phantomFree_of_sep2 hcl (by omega) hrT hN (fun v s L Rr hv D a0 c c' h0 hc hc' hss => ?_)
    (fun v s L Rr hv D hvs a0 a' h0 h' hss => ?_) (fun hv a0 a' h0 h' => ?_)
  · exact ⟨⟨⟨fun q hq => not_prohibited_glue D hss (hc.1.1.1 q hq) (hc'.1.1.1 q hq) (Or.inl (h0.1.1 q hq)),
        sel_glue_all hc.1.1.2 hc'.1.1.2 h0.1.2⟩,
      fun x hx => sel_glue_all (hc.1.2 x hx) (hc'.1.2 x hx) (h0.2 x hx)⟩, sel_glue_at (sep_mem D hv) hc.2 hc'.2⟩
  · exact ⟨⟨⟨fun q hq => not_prohibited_patchR D hss (h'.1.1.1 q hq) (Or.inl (h0.1.1 q hq)),
        sel_patch_both _ h'.1.1.2 h0.1.2⟩, fun x hx => sel_patch_both _ (h'.1.2 x hx) (h0.2 x hx)⟩,
      (sel_patchR_at D hvs hv a' a0).trans h'.2⟩
  · exact ⟨h0, (sel_eq_of_var (fun z hz => by rw [hv] at hz; cases hz)).trans h'.2⟩

end GPathB

-- ============================================================
-- Quién cumple la condición
-- ============================================================

/-- Las fórmulas de bloques (`ForbidOnBlock`) tienen separadores: `s = v`, sin lado izquierdo. -/
theorem sep2_of_blocks3 {E : Nat → Nat → Prop} (hb : Blocks3 φ E) : Sep2 φ := by
  intro v
  refine ⟨v, fun _ => False, fun z => E v z ∧ z ≠ v, ⟨fun h => absurd rfl h, fun h => h.2 rfl, fun _ h _ => h,
    Or.inl rfl, fun _ _ _ h _ _ _ _ _ => h, fun z1 z2 z3 h1 h2 h3 d12 d13 d23 => ?_, fun h => absurd rfl h,
    fun c hc => ?_⟩⟩
  · rcases hb.card v z1 z2 z3 h1.1 h2.1 h3.1 d12 d13 d23 with e | e | e
    · exact h1.2 e
    · exact h2.2 e
    · exact h3.2 e
  · by_cases h : E v c.l1.v ∨ E v c.l2.v ∨ E v c.l3.v
    · obtain ⟨i1, i2, i3⟩ := hb.cl c hc v h
      have t : ∀ z, E v z → (E v z ∧ z ≠ v) ∨ z = v := fun z hz => by
        by_cases e : z = v
        · exact Or.inr e
        · exact Or.inl ⟨hz, e⟩
      exact Or.inr (Or.inr ⟨t _ i1, t _ i2, t _ i3⟩)
    · have t : ∀ z, ¬ E v z → ¬ ((E v z ∧ z ≠ v) ∨ False ∨ z = v) := fun z hz h' => by
        rcases h' with h' | h' | h'
        · exact hz h'.1
        · exact h'
        · rw [h'] at hz; exact hz (hb.refl v)
      exact Or.inl ⟨t _ (fun e => h (Or.inl e)), t _ (fun e => h (Or.inr (Or.inl e))),
        t _ (fun e => h (Or.inr (Or.inr e)))⟩

/-- Dos cláusulas que comparten una variable: `(x0 ∨ x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ x4)`. -/
def twoShare : Cnf :=
  ⟨5, [⟨⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩⟩, ⟨⟨2, false⟩, ⟨3, true⟩, ⟨4, true⟩⟩]⟩

/-- **La condición no es vacía con variables compartidas**: la fórmula de dos cláusulas que comparten `x2` tiene
separadores (`s = x2`, y los lados `{x0, x1}` y `{x3, x4}`). -/
theorem sep2_twoShare : Sep2 twoShare := by
  intro v
  by_cases h2 : v = 2 ∨ (v = 3 ∨ v = 4)
  · refine ⟨2, fun z => z = 0 ∨ z = 1, fun z => z = 3 ∨ z = 4, ⟨fun _ => by decide, by omega,
      fun z a b => by omega, h2, fun z1 z2 z3 a b c d e f => by omega, fun z1 z2 z3 a b c d e f => by omega,
      fun hne z1 z2 a b d => by omega, fun c hc => ?_⟩⟩
    simp only [twoShare, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inr (by simp))
  · by_cases h01 : v = 0 ∨ v = 1
    · refine ⟨2, fun z => z = 3 ∨ z = 4, fun z => z = 0 ∨ z = 1, ⟨fun _ => by decide, by omega,
        fun z a b => by omega, Or.inr h01, fun z1 z2 z3 a b c d e f => by omega,
        fun z1 z2 z3 a b c d e f => by omega, fun hne z1 z2 a b d => by omega, fun c hc => ?_⟩⟩
      simp only [twoShare, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Or.inr (Or.inr (by simp))
      · exact Or.inr (Or.inl (by simp))
    · refine ⟨v, fun _ => False, fun _ => False, ⟨fun h => absurd rfl h, fun h => h, fun _ h _ => h, Or.inl rfl,
        fun _ _ _ h _ _ _ _ _ => h, fun _ _ _ h _ _ _ _ _ => h, fun h => absurd rfl h, fun c hc => ?_⟩⟩
      simp only [twoShare, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩
      · exact Or.inl ⟨by simp; omega, by simp; omega, by simp; omega⟩

theorem bounded_twoShare : Bounded twoShare := by
  intro c hc
  simp only [twoShare, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp [Clause.Bounded, twoShare]


namespace MachineOn

open GPathB Driver Machine

/-- **La espina `:on` decide toda fórmula con separadores**, sin hipótesis sobre la máquina. -/
theorem spineVerdictOn_iff_of_sep2 (hbd : Bounded φ) (hcl : Sep2 φ) : SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_phantomFree hbd (phantomAt_of_sep2 hbd hcl)

/-- **La máquina `:on` es exacta en toda fórmula con separadores.** -/
theorem machineExact_of_sep2 (hbd : Bounded φ) (hcl : Sep2 φ) : MachineExact φ :=
  (machineExact_iff hbd).2 (phantomAt_of_sep2 hbd hcl)

/-- **El lector no se atasca en ninguna fórmula con separadores.** -/
theorem reader_on_sep2 (hbd : Bounded φ) (hcl : Sep2 φ) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_on hbd (phantomAt_of_sep2 hbd hcl)
    (fun k => hRead_of_sep2 hcl (by unfold stepCount midFusion; omega) k) hkv hr

/-- **Un caso con variable compartida, sin ninguna hipótesis**: en `(x0 ∨ x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ x4)` la máquina
`:on` es exacta. -/
theorem machineExact_twoShare : MachineExact twoShare := machineExact_of_sep2 bounded_twoShare sep2_twoShare

end MachineOn

end AbsSatBingo.Model
