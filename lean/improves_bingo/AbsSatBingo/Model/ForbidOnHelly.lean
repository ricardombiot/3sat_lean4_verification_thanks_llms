-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnHelly.lean
import AbsSatBingo.Model.ForbidOnMaj

/-!
# El nivel de triángulos: el veredicto bajo una condición sobre la fórmula

`ForbidOnMaj` cierra la inducción con parejas porque la mayoría da «tres ramas que comparten nodos dos a dos ⟹ una
rama por los tres». Aquí el invariante sube un nivel y la hipótesis es la mínima que deja fuera a la máquina.

* **`Snd3 φ P g`**: toda pareja de vecinos y **todo triángulo sin prohibir** de `g` está en la rama de una asignación
  de `P`.
* **`PhantomFree φ P0 P N σ`** (sin familias fantasma, la condición de **todos los pasos**): toda estructura de
  nodos, parejas y tríos prohibidos, cerrada por la regla en los pasos `0 … N - 1` y hecha de ramas de `P0`, es de
  ramas de `P`; el ancla dice que una rama de `P0` por un nodo de la estructura en el paso `σ` es de `P`. Es una
  propiedad de conjuntos de asignaciones: **no menciona la máquina**.
* **`Helly4 φ P0 P N σ`** (la de **un paso**): una rama de `P0` por tres nodos y tres ramas de `P` por cada dos de
  ellos y por un mismo nodo del paso `σ` dan una rama de `P` por los tres. Da la anterior
  (`phantomFree_of_helly4`): basta mirar el testigo del paso `σ`.

La prueba solo pide `PhantomFree` en dos situaciones:

| operación | cuándo | `P0` → `P` | `σ` |
|---|---|---|---|
| filtro (`snd3_filter`) | el filtro mata algo | las ramas de la entrada → las que cumplen el requisito | el paso del requisito |
| UP (`snd3_upOn`) | la fila salta una ventana | las ramas del remitente filtrado → las de la llegada | el paso nuevo |

En las dos la estructura es el propio estado revisado: está cerrado por la regla (`ClosedState`, `trioGood_low`) y
sus objetos son de ramas de antes (`Snd3` de la entrada; en el UP, los que tienen un nodo de la fila bajan a un
padre, `upOn_face_parent`). El join no pide nada (`snd3_joinOn`).

**El resultado.** `PhantomAt φ T` reúne las dos condiciones de la línea `T` (para cada nodo `k` del paso `T - 1` y
cada hijo suyo `d` en el mapa), y

  `spineVerdictOn_iff_of_phantomFree : Bounded φ → (∀ T, 1 ≤ T → PhantomAt φ T) → (SpineVerdictOn φ ↔ Satisfiable φ)`.

La de un paso (`HellyAt`, `spineVerdictOn_iff_of_helly`) y la clausura por mayoría (`hellyAt_of_majClosed`) son casos
particulares, cada una más fuerte que la anterior:

  `MajClosed` ⟹ `HellyAt` ⟹ `PhantomAt` ⟹ veredicto.

`scripts/helly_formula.py` comprueba `HellyAt` por fuerza bruta sin ejecutar la máquina y, donde falla, `PhantomAt`
(calculando la mayor estructura cerrada). `scripts/cnf/parity_use.cnf` (una paridad de cuatro variables y después una
cláusula que lee una de ellas) incumple `HellyAt` en el UP, 768 veces.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

/-- **`Helly4`**: una rama de `P0` por tres nodos (pasos `i`, `j`, `l`, entre `0` y `N`) y tres ramas de `P` que pasan
cada una por dos de ellos y las tres por un mismo nodo del paso `σ` dan una rama de `P` por los tres nodos. -/
def Helly4 (φ : Cnf) (P0 P : Assign → Prop) (N σ : Int) : Prop :=
  ∀ a0 a1 a2 a3 : Assign, ∀ i j l : Int, 0 ≤ i → i < N → 0 ≤ j → j < N → 0 ≤ l → l < N →
    P0 a0 → P a1 → P a2 → P a3 →
    pidOfAssign φ a1 i = pidOfAssign φ a0 i → pidOfAssign φ a2 i = pidOfAssign φ a0 i →
    pidOfAssign φ a1 j = pidOfAssign φ a0 j → pidOfAssign φ a3 j = pidOfAssign φ a0 j →
    pidOfAssign φ a2 l = pidOfAssign φ a0 l → pidOfAssign φ a3 l = pidOfAssign φ a0 l →
    pidOfAssign φ a2 σ = pidOfAssign φ a1 σ → pidOfAssign φ a3 σ = pidOfAssign φ a1 σ →
    ∃ a, P a ∧ pidOfAssign φ a i = pidOfAssign φ a0 i ∧ pidOfAssign φ a j = pidOfAssign φ a0 j ∧
      pidOfAssign φ a l = pidOfAssign φ a0 l

/-- **`PhantomFree`**: sin familias fantasma. Toda estructura de nodos, parejas (`R`) y tríos prohibidos (`Tf`)
simétrica y **cerrada por la regla** en los pasos `0 … N - 1` (cada pareja tiene en cada paso un testigo bueno, y
cada triángulo sin prohibir también) cuyas parejas y triángulos sin prohibir son todos de ramas de `P0`, es de ramas de `P`; donde
una rama de `P0` que pasa por un nodo de la estructura en el paso `σ` es de `P` (el ancla).

Es la condición de **todos los pasos**: la de `Helly4` usa solo el testigo del paso `σ`. Sigue sin mencionar la
máquina. -/
def PhantomFree (φ : Cnf) (P0 P : Assign → Prop) (N σ : Int) : Prop :=
  ∀ (R : PathNodeId → PathNodeId → Prop) (Tf : GPathB.Trios),
    (∀ y w, R y w → R y y ∧ R w w) →
    (∀ y w, R y w → R w y) →
    (∀ a b r, R a b → R a r → R b r → Tf a b r → Tf a r b) →
    (∀ a b r, R a b → R a r → R b r → Tf a b r → Tf b a r) →
    (∀ y w, R y w → 0 ≤ y.id.step ∧ y.id.step < N) →
    (∀ y w, R y w → ∀ l, 0 ≤ l → l < N →
      ∃ s, s.id.step = l ∧ R y s ∧ R w s ∧ (y = w ∨ s = y ∨ s = w ∨ ¬ Tf y w s)) →
    (∀ x u w, R x u → R x w → R u w → x ≠ u → x ≠ w → u ≠ w → ¬ Tf x u w → ∀ l, 0 ≤ l → l < N →
      ∃ s, s.id.step = l ∧ R x s ∧ R u s ∧ R w s ∧
        (s = x ∨ s = u ∨ s = w ∨ (¬ Tf x u s ∧ ¬ Tf x w s ∧ ¬ Tf u w s))) →
    (∀ y w, R y w → ∃ a, P0 a ∧ pidOfAssign φ a y.id.step = y ∧ pidOfAssign φ a w.id.step = w) →
    (∀ x u w, R x u → R x w → R u w → x ≠ u → x ≠ w → u ≠ w → ¬ Tf x u w →
      ∃ a, P0 a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w) →
    (∀ a s, P0 a → R s s → s.id.step = σ → pidOfAssign φ a σ = s → P a) →
    (∀ y w, R y w → ∃ a, P a ∧ pidOfAssign φ a y.id.step = y ∧ pidOfAssign φ a w.id.step = w) ∧
    (∀ x u w, R x u → R x w → R u w → x ≠ u → x ≠ w → u ≠ w → ¬ Tf x u w →
      ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w)

/-- **La condición de un paso da la de todos**: basta mirar el testigo del paso `σ`. -/
theorem phantomFree_of_helly4 {φ : Cnf} {P0 P : Assign → Prop} {N σ : Int} (hσ0 : 0 ≤ σ) (hσN : σ < N)
    (h : Helly4 φ P0 P N σ) : PhantomFree φ P0 P N σ := by
  intro R Tf hrefl _ _ _ hsteps hpair htrio hb2 hb3 hanch
  refine ⟨fun y w hyw => ?_, fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
  · obtain ⟨s, hss, hys, hws, hor⟩ := hpair y w hyw σ hσ0 hσN
    by_cases e : y = w
    · subst e
      obtain ⟨a, ha, h1, h2⟩ := hb2 y s hys
      exact ⟨a, hanch a s ha (hrefl y s hys).2 hss (by rw [← hss]; exact h2), h1, h1⟩
    · by_cases hsy : s = y
      · obtain ⟨a, ha, h1, h2⟩ := hb2 y w hyw
        exact ⟨a, hanch a s ha (hrefl s s (by rw [hsy]; exact (hrefl y w hyw).1)).1 hss
          (by rw [← hss, hsy]; exact h1), h1, h2⟩
      · by_cases hsw : s = w
        · obtain ⟨a, ha, h1, h2⟩ := hb2 y w hyw
          exact ⟨a, hanch a s ha (hrefl s s (by rw [hsw]; exact (hrefl y w hyw).2)).1 hss
            (by rw [← hss, hsw]; exact h2), h1, h2⟩
        · have hnT : ¬ Tf y w s := by
            rcases hor with h' | h' | h' | h'
            · exact absurd h' e
            · exact absurd h' hsy
            · exact absurd h' hsw
            · exact h'
          obtain ⟨a, ha, h1, h2, h3⟩ := hb3 y w s hyw hys hws e (Ne.symm hsy) (Ne.symm hsw) hnT
          exact ⟨a, hanch a s ha (hrefl y s hys).2 hss (by rw [← hss]; exact h3), h1, h2⟩
  · obtain ⟨a0, hP0, hx0, hu0, hw0⟩ := hb3 x u w hxu hxw huw nxu nxw nuw hn
    obtain ⟨s, hss, hxs, hus, hws, hor⟩ := htrio x u w hxu hxw huw nxu nxw nuw hn σ hσ0 hσN
    have hRs := (hrefl x s hxs).2
    by_cases hsx : s = x
    · exact ⟨a0, hanch a0 s hP0 hRs hss (by rw [← hss, hsx]; exact hx0), hx0, hu0, hw0⟩
    · by_cases hsu : s = u
      · exact ⟨a0, hanch a0 s hP0 hRs hss (by rw [← hss, hsu]; exact hu0), hx0, hu0, hw0⟩
      · by_cases hsw : s = w
        · exact ⟨a0, hanch a0 s hP0 hRs hss (by rw [← hss, hsw]; exact hw0), hx0, hu0, hw0⟩
        · obtain ⟨n1, n2, n3⟩ : ¬ Tf x u s ∧ ¬ Tf x w s ∧ ¬ Tf u w s := by
            rcases hor with h' | h' | h' | h'
            · exact absurd h' hsx
            · exact absurd h' hsu
            · exact absurd h' hsw
            · exact h'
          obtain ⟨a1, hP1, hx1, hu1, hs1⟩ := hb3 x u s hxu hxs hus nxu (Ne.symm hsx) (Ne.symm hsu) n1
          obtain ⟨a2, hP2, hx2, hw2, hs2⟩ := hb3 x w s hxw hxs hws nxw (Ne.symm hsx) (Ne.symm hsw) n2
          obtain ⟨a3, hP3, hu3, hw3, hs3⟩ := hb3 u w s huw hus hws nuw (Ne.symm hsu) (Ne.symm hsw) n3
          have q1 := hanch a1 s hP1 hRs hss (by rw [← hss]; exact hs1)
          have q2 := hanch a2 s hP2 hRs hss (by rw [← hss]; exact hs2)
          have q3 := hanch a3 s hP3 hRs hss (by rw [← hss]; exact hs3)
          obtain ⟨bx0, bx1⟩ := hsteps x u hxu
          obtain ⟨bu0, bu1⟩ := hsteps u w huw
          obtain ⟨bw0, bw1⟩ := hsteps w w (hrefl u w huw).2
          obtain ⟨a, hP, e1, e2, e3⟩ := h a0 a1 a2 a3 x.id.step u.id.step w.id.step bx0 bx1 bu0 bu1 bw0 bw1
            hP0 q1 q2 q3 (hx1.trans hx0.symm) (hx2.trans hx0.symm) (hu1.trans hu0.symm) (hu3.trans hu0.symm)
            (hw2.trans hw0.symm) (hw3.trans hw0.symm)
            (by rw [← hss]; exact hs2.trans hs1.symm) (by rw [← hss]; exact hs3.trans hs1.symm)
          exact ⟨a, hP, e1.trans hx0, e2.trans hu0, e3.trans hw0⟩

/-- La condición de un paso con los tres nodos por debajo de `σ` da la misma con alguno en `σ`: si uno de los tres
nodos está en el paso `σ`, es el nodo común de las tres ramas, y una de ellas ya pasa por los tres. -/
theorem helly4_extend {φ : Cnf} {P0 P : Assign → Prop} {σ : Int} (h : Helly4 φ P0 P σ σ) :
    Helly4 φ P0 P (σ + 1) σ := by
  intro a0 a1 a2 a3 i j l i0 i1 j0 j1 l0 l1 h0 h1 h2 h3 e1 e2 e3 e4 e5 e6 e7 e8
  by_cases hi : i = σ
  · exact ⟨a3, h3, by rw [hi, e8, ← hi]; exact e1, e4, e6⟩
  · by_cases hj : j = σ
    · exact ⟨a2, h2, e2, by rw [hj, e7, ← hj]; exact e3, e5⟩
    · by_cases hl : l = σ
      · refine ⟨a1, h1, e1, e3, ?_⟩
        have : pidOfAssign φ a1 l = pidOfAssign φ a2 l := by rw [hl]; exact e7.symm
        rw [this]; exact e5
      · exact h a0 a1 a2 a3 i j l i0 (by omega) j0 (by omega) l0 (by omega) h0 h1 h2 h3 e1 e2 e3 e4 e5 e6 e7 e8

namespace GPathB

open Driver Machine MachineOn

variable {φ : Cnf}

/-- **`Snd3`**: parejas de vecinos y triángulos sin prohibir, en la rama de una asignación de `P`. -/
def Snd3 (φ : Cnf) (P : Assign → Prop) (g : GPathB) : Prop :=
  Snd φ P g ∧ ∀ x u w, g.Adj x u → g.Adj x w → g.Adj u w → x ≠ u → x ≠ w → u ≠ w → ¬ TF g x u w →
    ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w

theorem snd3_mono {P Q : Assign → Prop} {g : GPathB} (h : Snd3 φ P g) (hpq : ∀ a, P a → Q a) : Snd3 φ Q g := by
  refine ⟨snd_mono h.1 hpq, fun x u w h1 h2 h3 n1 n2 n3 hn => ?_⟩
  obtain ⟨a, ha, e1, e2, e3⟩ := h.2 x u w h1 h2 h3 n1 n2 n3 hn
  exact ⟨a, hpq a ha, e1, e2, e3⟩

/-- Un trío prohibido, leído en otro orden de sus tres nodos (vecinos dos a dos). -/
theorem tF_of_perm {g : GPathB} {x u w : PathNodeId} (hxu : g.Adj x u) (nxu : x ≠ u)
    (h : Sym (TF g) x u w) : TF g x u w := tF_of_sym_adj hxu nxu h

/-- **El join conserva `Snd3`**: un triángulo que la unión no prohíbe no lo corta alguno de los lados. -/
theorem snd3_joinOn {P : Assign → Prop} {A B : GPathB} (hA : Snd3 φ P A) (hB : Snd3 φ P B)
    (heA : EdgesAlive A) (heB : EdgesAlive B) : Snd3 φ P (joinOn A B) := by
  refine ⟨snd_joinOn hA.1 hB.1, fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
  have side : ∀ {g : GPathB}, ¬ SideForbids g (TF g) x u w → (g.Adj x u ∧ g.Adj x w ∧ g.Adj u w) ∧ ¬ TF g x u w :=
    fun hs => ⟨Classical.byContradiction (fun h => hs (Or.inl h)), fun h => hs (Or.inr h)⟩
  by_cases sA : SideForbids A (TF A) x u w
  · have sB : ¬ SideForbids B (TF B) x u w :=
      fun s => hn (tF_joinOn_of_cut heA heB hxu hxw huw nxu nxw nuw sA s)
    obtain ⟨⟨a1, a2, a3⟩, nf⟩ := side sB
    exact hB.2 x u w a1 a2 a3 nxu nxw nuw nf
  · obtain ⟨⟨a1, a2, a3⟩, nf⟩ := side sA
    exact hA.2 x u w a1 a2 a3 nxu nxw nuw nf

/-- **El filtro de un requisito conserva `Snd3`**, bajo `Helly4` en el paso del requisito. Las parejas no la piden:
su testigo bueno da un triángulo sin prohibir de la entrada. -/
theorem snd3_filter {E : GPathB} {T : Int} {P0 : Assign → Prop} {reqs : List NodeId} (hE : SInvB E) (hns : NoSelf E)
    (hndt : NoDegT E) (hcs : E.current_step = T) (hvE : E.isValid = true) (hlen : reqs.length ≤ 1)
    (hrange : ∀ r ∈ reqs, 1 ≤ r.step ∧ r.step < T)
    (hH : ∀ r ∈ reqs, PhantomFree φ P0 (fun a => P0 a ∧ selOfAssign φ a r.step = r) T r.step)
    (hs : Snd3 φ P0 E) (hc : ∀ a, P0 a → CT E (pidOfAssign φ a))
    (hvY : (E.filterAllOn reqs).isValid = true) :
    Snd3 φ (fun a => P0 a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r) (E.filterAllOn reqs) := by
  have hsh := (shrinks_filterAllOn E reqs).1
  match reqs, hlen, hrange, hH, hvY, hsh with
  | [], _, _, _, _, hsh =>
    refine ⟨fun x w hxw => ?_, fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
    · obtain ⟨a, hS, h1, h2⟩ := hs.1 x w (hsh.adj _ _ hxw)
      exact ⟨a, ⟨hS, fun r hr => absurd hr List.not_mem_nil⟩, h1, h2⟩
    · have hnE : ¬ TF E x u w := fun hf => hn (tF_mono (trios_grow_filterAllOn E []) hxu hf)
      obtain ⟨a, hS, h1, h2, h3⟩ := hs.2 x u w (hsh.adj _ _ hxu) (hsh.adj _ _ hxw) (hsh.adj _ _ huw) nxu nxw nuw hnE
      exact ⟨a, ⟨hS, fun r hr => absurd hr List.not_mem_nil⟩, h1, h2, h3⟩
  | [r], _, hrange, hH, hvY, hsh =>
    obtain ⟨hr1, hr2⟩ := hrange r (List.mem_singleton_self _)
    have one : ∀ {a : Assign}, selOfAssign φ a r.step = r → ∀ r' ∈ [r], selOfAssign φ a r'.step = r' := by
      intro a h r' hr'; rw [List.mem_singleton] at hr'; subst hr'; exact h
    cases hd : ([r].foldl filterRequire E).dirty
    · -- el filtro no mata a nadie: toda rama de la entrada cumple el requisito
      have hd' : (E.filterRequire r).dirty = false := hd
      have agr : ∀ a, P0 a → selOfAssign φ a r.step = r := by
        intro a hS
        have hD := hc a hS
        have hal := hD.1.alive r.step (by omega) (by rw [hcs]; exact hr2)
        obtain ⟨n, hn, hnid⟩ := hE.docs _ hal
        have hline : n ∈ E.line r.step := by
          unfold line
          refine List.mem_filter.mpr ⟨hn, ?_⟩
          rw [hnid, hD.1.step r.step (by omega) (by rw [hcs]; exact hr2)]
          simp
        have := filterRequire_noVictims hvE hd' n hline
        rw [hnid] at this
        exact this
      refine ⟨fun x w hxw => ?_, fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
      · obtain ⟨a, hS, h1, h2⟩ := hs.1 x w (hsh.adj _ _ hxw)
        exact ⟨a, ⟨hS, one (agr a hS)⟩, h1, h2⟩
      · have hnE : ¬ TF E x u w := fun hf => hn (tF_mono (trios_grow_filterAllOn E [r]) hxu hf)
        obtain ⟨a, hS, h1, h2, h3⟩ := hs.2 x u w (hsh.adj _ _ hxu) (hsh.adj _ _ hxw) (hsh.adj _ _ huw) nxu nxw nuw
          hnE
        exact ⟨a, ⟨hS, one (agr a hS)⟩, h1, h2, h3⟩
    · have e : E.filterAllOn [r] = E.pinOn [r] := by
        unfold filterAllOn pinOn
        congr 1
        generalize [r].foldl filterRequire E = F at hd
        cases F
        simp_all
      rw [e] at hvY ⊢
      have hsub := sub_pinOn E [r]
      have hiY : SInvB (E.pinOn [r]) := sInvB_pinOn hE [r]
      have hcl : ClosedState (E.pinOn [r]) := closedState_pinOn hE hvY (by rw [hcs]; omega)
      have hf : FixClosed (E.pinOn [r]) :=
        fixClosed_reviewOn (g := { [r].foldl filterRequire E with dirty := true }) rfl hvY
      have hg := trioGood_low hf (noDegT_pinOn hns hndt [r]) (Int.le_refl _)
      have hlt : ∀ {q : PathNodeId}, q ∈ (E.pinOn [r]).alive → q.id.step < (E.pinOn [r]).current_step :=
        fun hq => alive_below hiY.docs hiY.below hq
      have hR : ∀ {y z : PathNodeId}, (E.pinOn [r]).Adj y z →
          LowR (E.pinOn [r]) (E.pinOn [r]).current_step y z := fun h =>
        ⟨⟨(hiY.edges _ _ h).1, (hiY.edges _ _ h).2, h⟩, hlt (hiY.edges _ _ h).1, hlt (hiY.edges _ _ h).2⟩
      have hσ1 : (0 : Int) ≤ r.step := by omega
      have hσ2 : r.step < (E.pinOn [r]).current_step := by rw [step_pinOn, hcs]; exact hr2
      have pinned := pinned_pinOn hE.docs hvY r (List.mem_singleton_self _)
      have nE : ∀ {y z v : PathNodeId}, (E.pinOn [r]).Adj y z → ¬ TF (E.pinOn [r]) y z v → ¬ TF E y z v :=
        fun hyz hn hf => hn (tF_mono (trios_grow_pinOn E [r]) hyz hf)
      -- una rama por un nodo `s` del paso del requisito, vivo en el estado fijado, cumple el requisito
      have agS : ∀ {a : Assign} {s : PathNodeId}, s ∈ (E.pinOn [r]).alive → s.id.step = r.step →
          pidOfAssign φ a s.id.step = s → selOfAssign φ a r.step = r := by
        intro a s hsa hss hp
        have := congrArg PathNodeId.id hp
        rw [pid_id, hss] at this
        rw [this]; exact pinned s hsa hss
      have b0 : ∀ {q : PathNodeId}, q ∈ (E.pinOn [r]).alive → 0 ≤ q.id.step ∧ q.id.step < T := by
        intro q hq
        obtain ⟨n, hn, rfl⟩ := hiY.docs q hq
        have h1 := hiY.below n hn
        rw [step_pinOn, hcs] at h1
        exact ⟨hiY.zero n hn, h1⟩
      have hcT : (E.pinOn [r]).current_step = T := by rw [step_pinOn, hcs]
      -- la estructura del estado fijado: sus vivos, sus aristas y sus tríos
      obtain ⟨c2, c3⟩ := hH r (List.mem_singleton_self _)
        (LowR (E.pinOn [r]) (E.pinOn [r]).current_step) (TF (E.pinOn [r]))
        (fun y w h => ⟨hR (adj_refl _ _ h.1.1), hR (adj_refl _ _ h.1.2.1)⟩)
        (fun y w h => hR ((adj_symm _ _ _).mp h.1.2.2))
        (fun a b r h1 h2 h3 hT => hg.swap23 h1 h2 h3 hT)
        (fun a b r h1 h2 h3 hT => hg.swap12 h1 h2 h3 hT)
        (fun y w h => b0 h.1.1)
        (fun y w h l l0 l1 => by
          by_cases e : y = w
          · obtain ⟨s, hss, hys, hws⟩ := hcl.pair (y := y) (w := w) h.1 l l0 (by rw [hcT]; exact l1)
            exact ⟨s, hss, hR hys.2.2, hR hws.2.2, Or.inl e⟩
          · obtain ⟨s, hss, hys, hws, hor⟩ := hg.edge h e l l0 (by rw [hcT]; exact l1)
            exact ⟨s, hss, hys, hws, Or.inr hor⟩)
        (fun x u w h1 h2 h3 n1 n2 n3 hn l l0 l1 => hg.trio h1 h2 h3 n1 n2 n3 hn l l0 (by rw [hcT]; exact l1))
        (fun y w h => hs.1 y w (hsub.adj _ _ h.1.2.2))
        (fun x u w h1 h2 h3 n1 n2 n3 hn => hs.2 x u w (hsub.adj _ _ h1.1.2.2) (hsub.adj _ _ h2.1.2.2)
          (hsub.adj _ _ h3.1.2.2) n1 n2 n3 (nE h1.1.2.2 hn))
        (fun a s hS hss' hstep hp => ⟨hS, agS hss'.1.1 hstep (by rw [hstep]; exact hp)⟩)
      refine ⟨fun x w hxw => ?_, fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
      · obtain ⟨a, hP, h1, h2⟩ := c2 x w (hR hxw)
        exact ⟨a, ⟨hP.1, one hP.2⟩, h1, h2⟩
      · obtain ⟨a, hP, h1, h2, h3⟩ := c3 x u w (hR hxu) (hR hxw) (hR huw) nxu nxw nuw hn
        exact ⟨a, ⟨hP.1, one hP.2⟩, h1, h2, h3⟩

section Up

variable {Y : GPathB} {T : Int} {k d : NodeId} {title : String}

/-- **El UP conserva `Snd3`**, bajo `PhantomFree` y solo cuando la fila salta una ventana, hacia cualquier familia
`Pt` que contenga las ramas de la llegada (los objetos con un nodo de la fila son siempre de ramas de la llegada). Un triángulo con un nodo
de la fila baja a un padre que sostiene su cara (`upOn_face_parent`). Si la fila no saltó ninguna ventana, la rama de
todo objeto de nodos viejos se alarga. Si saltó alguna, la llegada revisada es una estructura cerrada por la regla
cuyos objetos son todos de ramas del remitente (los de nodos viejos, por `Snd3` del remitente; los que tienen un nodo
de la fila, por su padre), y una rama del remitente que pasa por un nodo de la fila es de la llegada: `PhantomFree`
da que todos son de ramas de la llegada. -/
theorem snd3_upOnG {Pt : Assign → Prop} (hPt : ∀ a, (SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) → Pt a)
    (hb : Bounded φ) (hiY : SInvB Y) (hnsY : NoSelf Y) (hndtY : NoDegT Y) (hcs : Y.current_step = T)
    (hT : 1 ≤ T) (hvY : Y.isValid = true) (hda : DocsAlive Y) (hdk : d ∈ sonsOfMap φ k) (hdm : d ∈ mapNodes φ T)
    (hH : PhantomFree φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) Pt (T + 1) T)
    (hs : Snd3 φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) Y)
    (hc : ∀ a, (SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) → CT Y (pidOfAssign φ a))
    (hvA : (Y.upOn d title (isProhibited φ)).isValid = true) :
    Snd3 φ Pt (Y.upOn d title (isProhibited φ)) := by
  have hd : d.step = Y.current_step := by rw [hcs]; exact mapNodes_step φ T d hdm
  have hsub := sub_upOn_addNode (d := d) (title := title) (forb := isProhibited φ) hvY
  have hiA : SInvB (Y.upOn d title (isProhibited φ)) := sInvB_upOn hiY hd (by rw [hd, hcs]; omega)
  have cls : ∀ {q : PathNodeId}, q ∈ (Y.upOn d title (isProhibited φ)).alive →
      (q ∈ Y.alive ∧ q.id.step < T) ∨ (q ∈ Y.newRowIds d (isProhibited φ) ∧ q.id.step = T) := by
    intro q hq
    have := alive_addNode_cases (title := title) (forb := isProhibited φ) hiY.docs hiY.below hd (hsub.alive q hq)
    rw [hcs] at this; exact this
  have oldAdj : ∀ {y z : PathNodeId}, y.id.step < T → z.id.step < T → (Y.upOn d title (isProhibited φ)).Adj y z →
      Y.Adj y z := fun hy hz h =>
    adj_addNode_old (title := title) (forb := isProhibited φ) hd (by rw [hcs]; exact hy) (by rw [hcs]; exact hz)
      (hsub.adj _ _ h)
  have twoNew : ∀ {y z : PathNodeId}, y.id.step = T → z.id.step = T → (Y.upOn d title (isProhibited φ)).Adj y z →
      y = z := fun hy hz h =>
    adj_addNode_new (title := title) (forb := isProhibited φ) hiY.docs hiY.below hiY.edges (by rw [hcs]; exact hy)
      (by rw [hcs]; exact hz) (hsub.adj _ _ h)
  -- subir una rama del remitente a un nodo de la fila, guardando la clave del remitente
  have liftA : ∀ {a : Assign} {q n : PathNodeId},
      (SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) → pidOfAssign φ a (T - 1) = q →
      q ∈ Y.rowParents d n → n ∈ Y.newRowIds d (isProhibited φ) →
      ∃ a', (SolE φ (T + 1) d a' ∧ selOfAssign φ a' (T - 1) = k) ∧ pidOfAssign φ a' T = n ∧
        ∀ j, j < T → pidOfAssign φ a' j = pidOfAssign φ a j := by
    intro a q n ha hq hqn hn
    obtain ⟨a', hS, hpT, hpl⟩ := lift_row hb hT hdk hdm ha hq hqn hn
    refine ⟨a', ⟨hS, ?_⟩, hpT, hpl⟩
    have := congrArg PathNodeId.id (hpl (T - 1) (by omega))
    rw [pid_id, pid_id] at this
    rw [this]; exact ha.1.2
  -- un nodo de la fila y un vecino viejo
  have newOld : ∀ {n w : PathNodeId}, n ∈ Y.newRowIds d (isProhibited φ) → w.id.step < T →
      (Y.upOn d title (isProhibited φ)).Adj n w →
      ∃ a, (SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) ∧ pidOfAssign φ a T = n ∧
        pidOfAssign φ a w.id.step = w := by
    intro n w hn hw hnw
    obtain ⟨q, hq, hqw⟩ := rowParent_of_newAdj (title := title) hiY.docs hiY.below hiY.edges hd hn
      (by rw [hcs]; exact hw) (hsub.adj _ _ hnw)
    obtain ⟨_, _, _, hqs⟩ := step_of_newParents (rowParents_sub hq)
    obtain ⟨a, ha, hq', hw'⟩ := hs.1 q w hqw
    rw [hqs, hcs] at hq'
    obtain ⟨a', hS, hpT, hpl⟩ := liftA ha hq' hq hn
    exact ⟨a', hS, hpT, by rw [hpl _ hw]; exact hw'⟩
  -- un nodo de la fila y dos vecinos viejos: la cara la sostiene un padre
  have newTri : ∀ {n x w : PathNodeId}, n ∈ (Y.upOn d title (isProhibited φ)).alive →
      n ∈ Y.newRowIds d (isProhibited φ) → n.id.step = T → x.id.step < T → w.id.step < T → x ≠ w →
      (Y.upOn d title (isProhibited φ)).Adj n x → (Y.upOn d title (isProhibited φ)).Adj n w →
      (Y.upOn d title (isProhibited φ)).Adj x w → ¬ TF (Y.upOn d title (isProhibited φ)) n x w →
      ∃ a, (SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) ∧ pidOfAssign φ a T = n ∧
        pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a w.id.step = w := by
    intro n x w hna hn hns hx hw nxw hnx hnw hxw hnf
    obtain ⟨p, hp, hpx, hpw, hxw', hnt⟩ := upOn_face_parent (title := title) (forb := isProhibited φ) hiY hd hvY hna
      (by rw [hns, hcs]) (hiA.edges _ _ hnx).2 (hiA.edges _ _ hnw).2 (by rw [hcs]; exact hx) (by rw [hcs]; exact hw)
      nxw hnx hnw hxw hnf
    obtain ⟨_, _, _, hps⟩ := step_of_newParents (rowParents_sub hp)
    have fin : ∀ a, (SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) → pidOfAssign φ a p.id.step = p →
        pidOfAssign φ a x.id.step = x → pidOfAssign φ a w.id.step = w →
        ∃ a', (SolE φ (T + 1) d a' ∧ selOfAssign φ a' (T - 1) = k) ∧ pidOfAssign φ a' T = n ∧
          pidOfAssign φ a' x.id.step = x ∧ pidOfAssign φ a' w.id.step = w := by
      intro a ha hp' hx' hw'
      rw [hps, hcs] at hp'
      obtain ⟨a', hS, hpT, hpl⟩ := liftA ha hp' hp hn
      exact ⟨a', hS, hpT, by rw [hpl _ hx]; exact hx', by rw [hpl _ hw]; exact hw'⟩
    by_cases hpx' : p = x
    · obtain ⟨a, ha, h1, h2⟩ := hs.1 p w hpw
      exact fin a ha h1 (by rw [← hpx']; exact h1) h2
    · by_cases hpw' : p = w
      · obtain ⟨a, ha, h1, h2⟩ := hs.1 p x hpx
        exact fin a ha h1 h2 (by rw [← hpw']; exact h1)
      · have hnfY : ¬ TF Y p x w := by
          intro hf
          have hd' := hf.2
          unfold deadTrio at hd'
          rw [Bool.and_eq_true] at hd'
          obtain ⟨τ, hτ, hti⟩ := List.any_eq_true.mp hd'.2
          rw [hnt hpx' hpw' τ hτ] at hti
          cases hti
        obtain ⟨a, ha, h1, h2, h3⟩ := hs.2 p x w hpx hpw hxw' hpx' hpw' nxw hnfY
        exact fin a ha h1 h2 h3
  -- lo que falta lo dan las parejas y los triángulos de nodos viejos, que dependen de si la fila saltó una ventana
  have main : ∀ (Q : Assign → Prop), (∀ a, (SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) → Q a) →
      (∀ {x w : PathNodeId}, x.id.step < T → w.id.step < T → (Y.upOn d title (isProhibited φ)).Adj x w →
        ∃ a, Q a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a w.id.step = w) →
      (∀ {x u w : PathNodeId}, x.id.step < T → u.id.step < T → w.id.step < T →
        (Y.upOn d title (isProhibited φ)).Adj x u → (Y.upOn d title (isProhibited φ)).Adj x w →
        (Y.upOn d title (isProhibited φ)).Adj u w → x ≠ u → x ≠ w → u ≠ w →
        ¬ TF (Y.upOn d title (isProhibited φ)) x u w →
        ∃ a, Q a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w) →
      Snd3 φ Q (Y.upOn d title (isProhibited φ)) := by
    intro Q hQ oo2 oo3
    refine ⟨fun x w hxw => ?_, fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
    · obtain ⟨hxa, hwa⟩ := hiA.edges x w hxw
      rcases cls hxa with ⟨_, hxs⟩ | ⟨hxn, hxs⟩ <;> rcases cls hwa with ⟨_, hws⟩ | ⟨hwn, hws⟩
      · exact oo2 hxs hws hxw
      · obtain ⟨a, hS, hpT, hpx⟩ := newOld hwn hxs ((adj_symm _ _ _).mp hxw)
        exact ⟨a, hQ a hS, hpx, by rw [hws]; exact hpT⟩
      · obtain ⟨a, hS, hpT, hpw⟩ := newOld hxn hws hxw
        exact ⟨a, hQ a hS, by rw [hxs]; exact hpT, hpw⟩
      · have e := twoNew hxs hws hxw
        subst e
        obtain ⟨q, hq, hqa, hqs⟩ := exists_rowParent (d := d) (forb := isProhibited φ) hda (by rw [hcs]; omega) hxn
        obtain ⟨a, ha, hq', _⟩ := hs.1 q q (adj_refl _ _ hqa)
        rw [hqs, hcs] at hq'
        obtain ⟨a', hS, hpT, _⟩ := liftA ha hq' hq hxn
        exact ⟨a', hQ a' hS, by rw [hxs]; exact hpT, by rw [hxs]; exact hpT⟩
    · obtain ⟨hxa, hua⟩ := hiA.edges x u hxu
      have hwa := (hiA.edges x w hxw).2
      have hux := (adj_symm _ _ _).mp hxu
      have hwx := (adj_symm _ _ _).mp hxw
      have hwu := (adj_symm _ _ _).mp huw
      rcases cls hxa with ⟨_, hxs⟩ | ⟨hxn, hxs⟩ <;> rcases cls hua with ⟨_, hus⟩ | ⟨hun, hus⟩ <;>
        rcases cls hwa with ⟨_, hws⟩ | ⟨hwn, hws⟩
      · exact oo3 hxs hus hws hxu hxw huw nxu nxw nuw hn
      · -- w es de la fila
        have hnf : ¬ TF (Y.upOn d title (isProhibited φ)) w x u := fun hf =>
          hn (tF_of_perm hxu nxu (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf))))))
        obtain ⟨a, hS, hpT, h1, h2⟩ := newTri hwa hwn hws hxs hus nxu hwx hwu hxu hnf
        exact ⟨a, hQ a hS, h1, h2, by rw [hws]; exact hpT⟩
      · -- u es de la fila
        have hnf : ¬ TF (Y.upOn d title (isProhibited φ)) u x w := fun hf =>
          hn (tF_of_perm hxu nxu (Or.inr (Or.inr (Or.inl hf))))
        obtain ⟨a, hS, hpT, h1, h2⟩ := newTri hua hun hus hxs hws nxw hux huw hxw hnf
        exact ⟨a, hQ a hS, h1, by rw [hus]; exact hpT, h2⟩
      · exact absurd (twoNew hus hws huw) nuw
      · -- x es de la fila
        obtain ⟨a, hS, hpT, h1, h2⟩ := newTri hxa hxn hxs hus hws nuw hxu hxw huw hn
        exact ⟨a, hQ a hS, by rw [hxs]; exact hpT, h1, h2⟩
      · exact absurd (twoNew hxs hws hxw) nxw
      · exact absurd (twoNew hxs hus hxu) nxu
      · exact absurd (twoNew hxs hus hxu) nxu
  cases hsk : Y.skipsWindow d (isProhibited φ)
  · -- ninguna ventana saltada: toda rama del remitente se alarga
    have ext : ∀ a, (SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) →
        ∃ a', (SolE φ (T + 1) d a' ∧ selOfAssign φ a' (T - 1) = k) ∧
          ∀ j, j < T → pidOfAssign φ a' j = pidOfAssign φ a j := by
      intro a0 ha0
      have hct := hc a0 ha0
      have hnpar : pidOfAssign φ a0 (T - 1) ∈ Y.newParents := by
        obtain ⟨n, hn, _, _⟩ := hct.1.node (T - 1) (by omega) (by rw [hcs]; omega)
        have hid := node?_id hn
        unfold newParents
        rw [if_pos (by rw [hcs]; omega)]
        refine List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨node?_mem hn, ?_⟩, hid⟩
        rw [hid, hcs]; simp [pid_step]
      have hrow : shiftPid (pidOfAssign φ a0 (T - 1)) d ∈ Y.shiftRowIds d := by
        unfold shiftRowIds
        rw [if_pos (by rw [hcs]; omega)]
        exact (mem_dedupPids _ _).mpr (List.mem_map.mpr ⟨_, hnpar, rfl⟩)
      have hnew : shiftPid (pidOfAssign φ a0 (T - 1)) d ∈ Y.newRowIds d (isProhibited φ) := by
        refine List.mem_filter.mpr ⟨hrow, ?_⟩
        unfold skipsWindow at hsk
        have := List.any_eq_false.mp hsk _ hrow
        simpa using this
      obtain ⟨a', hS, _, hpl⟩ := liftA ha0 rfl (List.mem_filter.mpr ⟨hnpar, by simp⟩) hnew
      exact ⟨a', hS, hpl⟩
    refine snd3_mono (main (fun a => SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) (fun _ h => h)
      (fun {x w} hxs hws hxw => ?_) (fun {x u w} hxs hus hws hxu hxw huw nxu nxw nuw hn => ?_)) hPt
    · obtain ⟨a0, ha0, hx0, hw0⟩ := hs.1 x w (oldAdj hxs hws hxw)
      obtain ⟨a', hS, hpl⟩ := ext a0 ha0
      exact ⟨a', hS, by rw [hpl _ hxs]; exact hx0, by rw [hpl _ hws]; exact hw0⟩
    · have hnY : ¬ TF Y x u w := fun hf => hn (tF_mono (trios_grow_upOn Y d title (isProhibited φ)) hxu hf)
      obtain ⟨a0, ha0, hx0, hu0, hw0⟩ := hs.2 x u w (oldAdj hxs hus hxu) (oldAdj hxs hws hxw) (oldAdj hus hws huw)
        nxu nxw nuw hnY
      obtain ⟨a', hS, hpl⟩ := ext a0 ha0
      exact ⟨a', hS, by rw [hpl _ hxs]; exact hx0, by rw [hpl _ hus]; exact hu0, by rw [hpl _ hws]; exact hw0⟩
  · -- alguna ventana saltada: la llegada revisada está cerrada y en el punto fijo de la regla
    obtain ⟨T', hT'⟩ := upOn_eq (d := d) (title := title) (forb := isProhibited φ) hvY
    have hiN : SInvB ((Y.addNode d title (isProhibited φ)).setT T') :=
      sInvB_setT (sInvB_addNode hiY hd (by rw [hd, hcs]; omega)) T'
    have hdirty : ((Y.addNode d title (isProhibited φ)).setT T').dirty = true := by
      show (Y.dirty || Y.skipsWindow d (isProhibited φ)) = true
      rw [hsk]; simp
    have hcsA : (Y.upOn d title (isProhibited φ)).current_step = T + 1 := by
      rw [hsub.step]; show Y.current_step + 1 = _; rw [hcs]
    have hcl : ClosedState (Y.upOn d title (isProhibited φ)) := by
      rw [hT'] at hvA ⊢
      exact closedState_reviewOn hdirty hvA hiN.docs hiN.nodup hiN.below hiN.zero
        (by show 2 ≤ Y.current_step + 1; rw [hcs]; omega)
    have hf : FixClosed (Y.upOn d title (isProhibited φ)) := by
      rw [hT'] at hvA ⊢
      exact fixClosed_reviewOn hdirty hvA
    have hg := trioGood_low hf (noDegT_upOn (d := d) (title := title) (forb := isProhibited φ) hnsY hndtY)
      (Int.le_refl _)
    have hR : ∀ {y z : PathNodeId}, (Y.upOn d title (isProhibited φ)).Adj y z →
        LowR (Y.upOn d title (isProhibited φ)) (Y.upOn d title (isProhibited φ)).current_step y z := fun h =>
      ⟨⟨(hiA.edges _ _ h).1, (hiA.edges _ _ h).2, h⟩, alive_below hiA.docs hiA.below (hiA.edges _ _ h).1,
        alive_below hiA.docs hiA.below (hiA.edges _ _ h).2⟩
    have topNew : ∀ {n : PathNodeId}, n ∈ (Y.upOn d title (isProhibited φ)).alive → n.id.step = T →
        n ∈ Y.newRowIds d (isProhibited φ) := by
      intro n hna hns
      rcases cls hna with ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · exact h
    have b0 : ∀ {q : PathNodeId}, q ∈ (Y.upOn d title (isProhibited φ)).alive → 0 ≤ q.id.step ∧ q.id.step < T + 1 := by
      intro q hq
      obtain ⟨m, hm, rfl⟩ := hiA.docs q hq
      have h1 := hiA.below m hm
      rw [hcsA] at h1
      exact ⟨hiA.zero m hm, h1⟩
    -- las ramas de la llegada son ramas del remitente filtrado
    have sub : ∀ a, (SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) →
        (SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) := by
      intro a ha
      have hd' : selOfAssign φ a T = d := by have := ha.1.2; rw [show T + 1 - 1 = T by omega] at this; exact this
      refine ⟨⟨validUpTo_mono ha.1.1 (by omega), ha.2⟩, fun r hr => ?_⟩
      have := reqSat_selOfAssign φ hb a T r (by rw [hd']; exact hr)
      exact this
    -- todo objeto de la llegada es de una rama del remitente
    have base := main (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) sub
      (fun {x w} hxs hws hxw => hs.1 x w (oldAdj hxs hws hxw))
      (fun {x u w} hxs hus hws hxu hxw huw nxu nxw nuw hn =>
        hs.2 x u w (oldAdj hxs hus hxu) (oldAdj hxs hws hxw) (oldAdj hus hws huw) nxu nxw nuw
          (fun hf => hn (tF_mono (trios_grow_upOn Y d title (isProhibited φ)) hxu hf)))
    obtain ⟨c2, c3⟩ := hH
      (LowR (Y.upOn d title (isProhibited φ)) (Y.upOn d title (isProhibited φ)).current_step)
      (TF (Y.upOn d title (isProhibited φ)))
      (fun y w h => ⟨hR (adj_refl _ _ h.1.1), hR (adj_refl _ _ h.1.2.1)⟩)
      (fun y w h => hR ((adj_symm _ _ _).mp h.1.2.2))
      (fun a b r h1 h2 h3 hT => hg.swap23 h1 h2 h3 hT)
      (fun a b r h1 h2 h3 hT => hg.swap12 h1 h2 h3 hT)
      (fun y w h => b0 h.1.1)
      (fun y w h l l0 l1 => by
        by_cases e : y = w
        · obtain ⟨s, hss, hys, hws⟩ := hcl.pair (y := y) (w := w) h.1 l l0 (by rw [hcsA]; exact l1)
          exact ⟨s, hss, hR hys.2.2, hR hws.2.2, Or.inl e⟩
        · obtain ⟨s, hss, hys, hws, hor⟩ := hg.edge h e l l0 (by rw [hcsA]; exact l1)
          exact ⟨s, hss, hys, hws, Or.inr hor⟩)
      (fun x u w h1 h2 h3 n1 n2 n3 hn l l0 l1 => hg.trio h1 h2 h3 n1 n2 n3 hn l l0 (by rw [hcsA]; exact l1))
      (fun y w h => base.1 y w h.1.2.2)
      (fun x u w h1 h2 h3 n1 n2 n3 hn => base.2 x u w h1.1.2.2 h2.1.2.2 h3.1.2.2 n1 n2 n3 hn)
      (fun a n ha hnn hstep hp => by
        have hnew := topNew hnn.1.1 hstep
        refine hPt a ⟨⟨validUpTo_succ ha.1.1 ?_, ?_⟩, ha.1.2⟩
        · rw [hp]
          have := (List.mem_filter.mp hnew).2
          simpa using this
        · rw [show T + 1 - 1 = T by omega, ← pid_id, hp]; exact newRow_id' hnew)
    refine ⟨fun x w hxw => ?_, fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
    · exact c2 x w (hR hxw)
    · exact c3 x u w (hR hxu) (hR hxw) (hR huw) nxu nxw nuw hn

/-- **El UP conserva `Snd3`** con las ramas de la propia llegada (el caso `Pt` = ramas de la llegada). -/
theorem snd3_upOn (hb : Bounded φ) (hiY : SInvB Y) (hnsY : NoSelf Y) (hndtY : NoDegT Y) (hcs : Y.current_step = T)
    (hT : 1 ≤ T) (hvY : Y.isValid = true) (hda : DocsAlive Y) (hdk : d ∈ sonsOfMap φ k) (hdm : d ∈ mapNodes φ T)
    (hH : PhantomFree φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r)
      (fun a => SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) (T + 1) T)
    (hs : Snd3 φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) Y)
    (hc : ∀ a, (SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) → CT Y (pidOfAssign φ a))
    (hvA : (Y.upOn d title (isProhibited φ)).isValid = true) :
    Snd3 φ (fun a => SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) (Y.upOn d title (isProhibited φ)) :=
  snd3_upOnG (fun _ h => h) hb hiY hnsY hndtY hcs hT hvY hda hdk hdm hH hs hc hvA

end Up

-- ============================================================
-- De la semántica a los niveles, sin clausura
-- ============================================================

/-- Con `Snd3` y la completitud, los niveles 2 y 3 son inmediatos: la rama es la camarilla. -/
theorem levels_of_snd3 {E : GPathB} {T : Int} {k : NodeId} (hs : Snd3 φ (SolE φ T k) E)
    (hc : ∀ a, SolE φ T k a → CT E (pidOfAssign φ a)) : TopEdge E ∧ TopTri E := by
  refine ⟨fun t _ hts w htw => ?_, fun t _ hts u w htu htw huw ntu ntw nuw hn => ?_⟩
  · obtain ⟨a, hS, ht, hw⟩ := hs.1 t w htw
    exact ⟨_, hc a hS, by rw [← hts]; exact ht, hw⟩
  · obtain ⟨a, hS, ht, hu, hw⟩ := hs.2 t u w htu htw huw ntu ntw nuw hn
    exact ⟨_, hc a hS, by rw [← hts]; exact ht, hu, hw⟩

-- ============================================================
-- La condición sobre la fórmula y el invariante de línea
-- ============================================================

/-- **`PhantomAt φ T`**: sin familias fantasma en la línea `T`, para cada nodo `k` del paso `T - 1` y cada hijo
suyo `d` en el mapa: al fijar el requisito de `d` (el filtro) y al añadir el paso nuevo (el UP). Solo habla de las
soluciones del prefijo de `φ`: no menciona la máquina. -/
def PhantomAt (φ : Cnf) (T : Int) : Prop :=
  ∀ k d : NodeId, k ∈ mapNodes φ (T - 1) → d ∈ sonsOfMap φ k →
    (∀ r ∈ reqOf φ d, PhantomFree φ (SolE φ T k) (fun a => SolE φ T k a ∧ selOfAssign φ a r.step = r) T r.step) ∧
    PhantomFree φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r)
      (fun a => SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) (T + 1) T

/-- **`HellyAt φ T`**: la condición de cuatro ramas en la línea `T` (la de un solo paso): en el paso del requisito
de `d` (el filtro) y en el paso nuevo (el UP). -/
def HellyAt (φ : Cnf) (T : Int) : Prop :=
  ∀ k d : NodeId, k ∈ mapNodes φ (T - 1) → d ∈ sonsOfMap φ k →
    (∀ r ∈ reqOf φ d, Helly4 φ (SolE φ T k) (fun a => SolE φ T k a ∧ selOfAssign φ a r.step = r) T r.step) ∧
    Helly4 φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r)
      (fun a => SolE φ (T + 1) d a ∧ selOfAssign φ a (T - 1) = k) T T

/-- **La condición de un paso da la de todos.** -/
theorem phantomAt_of_hellyAt (hb : Bounded φ) {T : Int} (hT : 1 ≤ T) (h : HellyAt φ T) : PhantomAt φ T := by
  intro k d hk hd
  obtain ⟨hF, hU⟩ := h k d hk hd
  refine ⟨fun r hr => ?_, phantomFree_of_helly4 (by omega) (by omega) (helly4_extend hU)⟩
  have hds : d.step = T := by
    have := sonsOfMap_step φ k d hd
    have hks := mapNodes_step φ (T - 1) k hk
    omega
  obtain ⟨r1, r2⟩ := reqOf_range hb r hr
  exact phantomFree_of_helly4 (by omega) (by rw [hds] at r2; exact r2) (hF r hr)

/-- **El invariante semántico de triángulos de la línea `:on`.** -/
structure LInvS3 (φ : Cnf) (T : Int) (line : Line) : Prop where
  on    : LineOn T line
  nodup : (line.map (·.1)).Nodup
  keys  : ∀ kv ∈ line, kv.1 ∈ mapNodes φ (T - 1)
  inv   : ∀ kv ∈ line, SInvB kv.2
  ndt   : ∀ kv ∈ line, NoDegT kv.2
  docs  : ∀ kv ∈ line, DocsAlive kv.2
  snd   : ∀ kv ∈ line, Snd3 φ (SolE φ T kv.1) kv.2

theorem lInvS_of_s3 {T : Int} {line : Line} (h : LInvS3 φ T line) : LInvS φ T line :=
  ⟨h.on, h.nodup, h.keys, h.inv, h.ndt, h.docs, fun kv hkv => (h.snd kv hkv).1⟩

/-- **El paso de la máquina bajo `PhantomAt`.** -/
theorem lInvS3_advance (hb : Bounded φ) {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvS3 φ T line)
    (hcomp : CompLine φ T line) (hH : PhantomAt φ T) : LInvS3 φ (T + 1) (advanceM .on φ line) := by
  have hlen := line_cases h.nodup h.keys
  have arr : ∀ kv ∈ line, ∀ d, SendsOn φ kv d →
      EntOn (T + 1) d (arrOn φ kv d) ∧ SInvB (arrOn φ kv d) ∧ NoDegT (arrOn φ kv d) ∧ DocsAlive (arrOn φ kv d) ∧
      Snd3 φ (SolE φ (T + 1) d) (arrOn φ kv d) ∧ d ∈ mapNodes φ T := by
    intro kv hkv d hs
    have hent := h.on kv hkv
    have hok := hent.1
    have hd : d.step = kv.2.current_step := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key, hok.step]; omega
    have hi := h.inv kv hkv
    have hcsY : (kv.2.filterAllOn (reqOf φ d)).current_step = T := by rw [step_filterAllOn]; exact hok.step
    have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by rw [step_filterAllOn]; exact hd
    have hvY : (kv.2.filterAllOn (reqOf φ d)).isValid = true :=
      valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
    have hiY := sInvB_filterAllOn hi (reqOf φ d)
    have hdaY := docsAlive_filterAllOn (h.docs kv hkv) (reqOf φ d) hvY
    have hdm : d ∈ mapNodes φ T := by
      have hk' : kv.1 ∈ mapNodes φ kv.1.step := by rw [hok.key]; exact h.keys kv hkv
      have := sonsOfMap_subset φ kv.1 hk' d hs.1
      rw [hok.key, show T - 1 + 1 = T by omega] at this
      exact this
    obtain ⟨hF, hU⟩ := hH kv.1 d (h.keys kv hkv) hs.1
    have sY := snd3_filter hi hent.2.1 (h.ndt kv hkv) hok.step hok.valid (reqOf_length_le_one φ d)
      (fun r hr => by have := reqOf_range hb r hr; rw [hd, hok.step] at this; exact this) hF
      (h.snd kv hkv) (hcomp kv hkv) hvY
    refine ⟨entOn_upFilteringOn hent hs.1 hs.2,
      sInvB_upOn hiY hdY (by rw [hd, hok.step]; omega),
      noDegT_upOn (noSelf_filterAllOn hent.2.1 _) (noDegT_filterAllOn hent.2.1 (h.ndt kv hkv) _),
      docsAlive_upOn hdaY hvY hs.2,
      snd3_mono (snd3_upOn hb hiY (noSelf_filterAllOn hent.2.1 _) (noDegT_filterAllOn hent.2.1 (h.ndt kv hkv) _)
        hcsY hT hvY hdaY hs.1 hdm hU sY (comp_filter (hcomp kv hkv)) hs.2) (fun a ha => ha.1), hdm⟩
  have ent : ∀ E ∈ advanceM .on φ line, SInvB E.2 ∧ NoDegT E.2 ∧ DocsAlive E.2 ∧
      Snd3 φ (SolE φ (T + 1) E.1) E.2 ∧ E.1 ∈ mapNodes φ T := by
    intro E hE
    rcases entry_shapeOn hlen h.nodup hE with ⟨kv, hkv, hs, he⟩ | ⟨a, ha, b, hb', _, hsa, hsb, he⟩
    · obtain ⟨_, hi, hn, hda, hp, hm⟩ := arr kv hkv E.1 hs
      rw [he]; exact ⟨hi, hn, hda, hp, hm⟩
    · obtain ⟨ea, ia, _, da, pa, hm⟩ := arr a ha E.1 hsa
      obtain ⟨eb, ib, _, db, pb, _⟩ := arr b hb' E.1 hsb
      have hcs : (arrOn φ a E.1).current_step = (arrOn φ b E.1).current_step := ea.1.step.trans eb.1.step.symm
      have hjoin : doJoinOn (arrOn φ a E.1) (arrOn φ b E.1) = joinOn (arrOn φ a E.1) (arrOn φ b E.1) := by
        unfold doJoinOn okJoin
        rw [if_pos (by simp [ea.1.step, eb.1.step, ea.1.mp, eb.1.mp, ea.1.valid, eb.1.valid])]
      rw [he, hjoin]
      exact ⟨sInvB_joinOn ia ib hcs, noDegT_joinOn ea.2.1 eb.2.1 ia.edges ib.edges, docsAlive_joinOn da db,
        snd3_joinOn pa pb ia.edges ib.edges, hm⟩
  exact ⟨lineOn_advance h.on, advanceOn_nodup φ line,
    fun E hE => by rw [show T + 1 - 1 = T by omega]; exact (ent E hE).2.2.2.2,
    fun E hE => (ent E hE).1, fun E hE => (ent E hE).2.1, fun E hE => (ent E hE).2.2.1,
    fun E hE => (ent E hE).2.2.2.1⟩

/-- **El caso base**: la semilla no tiene dos nodos distintos. -/
theorem lInvS3_init (φ : Cnf) : LInvS3 φ 1 (initM .on φ) := by
  have h0 := lInvS_init φ
  refine ⟨h0.on, h0.nodup, h0.keys, h0.inv, h0.ndt, h0.docs, fun kv hkv => ⟨h0.snd kv hkv, ?_⟩⟩
  intro x u w hxu _ _ nxu _ _ _
  exfalso
  have hi := h0.inv kv hkv
  have hcs : kv.2.current_step = 1 := (h0.on kv hkv).1.step
  obtain ⟨hxa, hua⟩ := hi.edges x u hxu
  have st : ∀ {q : PathNodeId}, q ∈ kv.2.alive → q.id.step = 0 := by
    intro q hq
    obtain ⟨n, hn, rfl⟩ := hi.docs q hq
    have h1 := hi.below n hn
    have h2 := hi.zero n hn
    rw [hcs] at h1
    omega
  obtain ⟨a, _, hx, hu⟩ := h0.snd kv hkv x u hxu
  rw [st hxa] at hx
  rw [st hua] at hu
  exact nxu (hx.symm.trans hu)

/-- **La inducción**: sin familias fantasma hasta la línea, el invariante de triángulos vale en ella. -/
theorem lInvS3_steps (hb : Bounded φ) : ∀ n : Nat, (∀ T : Int, 1 ≤ T → T ≤ n → PhantomAt φ T) →
    LInvS3 φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero => intro _; exact lInvS3_init φ
  | succ n ih =>
    intro hm
    have hl := ih (fun T h1 hT => hm T h1 (by push_cast; omega))
    rw [stepsM_succ]
    have := lInvS3_advance hb (by omega) hl (compLine_steps hb (lInvS_of_s3 hl)) (hm _ (by omega) (by push_cast; omega))
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

/-- **Sin familias fantasma, toda entrada de la máquina cumple los tres niveles.** -/
theorem levels_steps3 (hb : Bounded φ) (n : Nat) (hm : ∀ T : Int, 1 ≤ T → T ≤ n → PhantomAt φ T) :
    ∀ kv ∈ stepsM .on φ n (initM .on φ), TopCT kv.2 ∧ TopEdge kv.2 ∧ TopTri kv.2 := by
  intro kv hkv
  have hl := lInvS3_steps hb n hm
  obtain ⟨h2, h3⟩ := levels_of_snd3 (hl.snd kv hkv) (compLine_steps hb (lInvS_of_s3 hl) kv hkv)
  exact ⟨topCT_of_topEdge h2, h2, h3⟩

-- ============================================================
-- La mayoría da la condición
-- ============================================================

/-- Si `P` es cerrado por mayoría, la condición de cuatro ramas vale (y ni siquiera usa la rama de `P0`). -/
theorem helly4_of_maj {P0 P : Assign → Prop} {N σ : Int}
    (hP : ∀ a1 a2 a3, P a1 → P a2 → P a3 → P (maj3 a1 a2 a3)) : Helly4 φ P0 P N σ := by
  intro a0 a1 a2 a3 i j l _ _ _ _ _ _ _ h1 h2 h3 e1 e2 e3 e4 e5 e6 _ _
  exact ⟨maj3 a1 a2 a3, hP _ _ _ h1 h2 h3, (pid_maj_ab (e1.trans e2.symm)).trans e1,
    (pid_maj_ac (e3.trans e4.symm)).trans e3, (pid_maj_bc (e5.trans e6.symm)).trans e5⟩

/-- **La condición de cuatro ramas es más débil que la clausura por mayoría.** -/
theorem hellyAt_of_majClosed (hm : ∀ T : Int, MajClosed φ T) (T : Int) : HellyAt φ T := by
  intro k d _ _
  refine ⟨fun r _ => helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_), helly4_of_maj (fun a1 a2 a3 h1 h2 h3 => ?_)⟩
  · exact ⟨⟨hm T _ _ _ h1.1.1 h2.1.1 h3.1.1, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
      by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩
  · exact ⟨⟨hm (T + 1) _ _ _ h1.1.1 h2.1.1 h3.1.1, by rw [sel_maj_ab (h1.1.2.trans h2.1.2.symm)]; exact h1.1.2⟩,
      by rw [sel_maj_ab (h1.2.trans h2.2.symm)]; exact h1.2⟩

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {φ : Cnf}

/-- **La espina `:on` decide toda fórmula sin familias fantasma.** La hipótesis es una propiedad de las soluciones
de los prefijos de `φ` (toda estructura cerrada por la regla y hecha de ramas es de ramas que cumplen lo fijado); la
máquina no aparece en ella. -/
theorem spineVerdictOn_iff_of_phantomFree (hbd : Bounded φ) (H : ∀ T : Int, 1 ≤ T → PhantomAt φ T) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_finalTopCT hbd
    (fun kv hkv => (levels_steps3 hbd (stepCount φ - 1).toNat (fun T h1 _ => H T h1) kv hkv).1)

/-- **La espina `:on` decide toda fórmula que cumple la condición de cuatro ramas** (la de un solo paso). -/
theorem spineVerdictOn_iff_of_helly (hbd : Bounded φ) (H : ∀ T : Int, 1 ≤ T → HellyAt φ T) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_phantomFree hbd (fun T hT => phantomAt_of_hellyAt hbd hT (H T hT))

end MachineOn

end AbsSatBingo.Model
