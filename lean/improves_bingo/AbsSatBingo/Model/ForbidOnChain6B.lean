-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChain6B.lean
import AbsSatBingo.Model.ForbidOnChainBisect

/-!
# Seis bloques en orden de bisección

Con las cláusulas en orden de bisección de bloques (`B0, B1, B2 | B5, B4 | B3`, la unión al final) la máquina sale
exacta en la condición fuerte (`chain6_bisect*.cnf`, `probe_exact3.jl`). Aquí, las piezas de las líneas:

* **`phantomFree_fixedLoc`**: si todas las ramas de `P0` leen igual la variable del paso fijado (y el paso no es el
  tercero de una cláusula), no hay familias fantasma: `P0` y `P` tienen las mismas ramas.
* **`phantomFree_inner`**: la variable fijada `v` es la de dentro del bloque `m`, con el separador `m` fijado (todas las
  ramas de `P0` lo leen igual): un solo lado, los bloques `m … b-1`, con los lemas del lado (`side_res`,
  `side_window`, `capFull`) y `glue_one_tri`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop} {N Nn σ : Int}

/-- **Una variable que ya leen igual todas las ramas**, en un paso que no es el tercero de una cláusula. -/
theorem phantomFree_fixedLoc (hl : LocPair φ P0 P σ) {v : Nat} (hv : stepVar φ σ = some v)
    (h3 : isL3 φ σ = false) (hagree : ∀ a b, P0 a → P0 b → a v = b v) (hσ0 : 0 ≤ σ) (hσN : σ < N) :
    PhantomFree φ P0 P N σ := by
  intro R Tf hrefl hsymm hsw23 hsw12 hsteps hpair htrio hb2 hb3 hanch
  have hS : PhStruct φ P0 N R Tf := ⟨hrefl, hsymm, hsw23, hsw12, hsteps, hpair, htrio, hb2, hb3⟩
  -- si hay estructura, una de sus parejas da una rama de `P`, y entonces todas las de `P0` son de `P`
  have all : (∃ y w, R y w) → ∀ a, P0 a → P a := by
    rintro ⟨y, w, hyw⟩ a ha
    obtain ⟨c, hc, _, _⟩ := pairs_of_struct hσ0 hσN hS hanch y w hyw
    refine hl.anc a ha ⟨c, hc, ?_, fun h => by rw [h3] at h; cases h⟩
    exact sel_eq_of_var (fun z hz => by rw [hv] at hz; cases hz; exact hagree a c ha (hl.sub c hc))
  refine ⟨fun y w hyw => ?_, fun x u w hxu hxw huw n1 n2 n3 hn => ?_⟩
  · obtain ⟨a, ha, h1, h2⟩ := hb2 y w hyw
    exact ⟨a, all ⟨y, w, hyw⟩ a ha, h1, h2⟩
  · obtain ⟨a, ha, h1, h2, h3⟩ := hb3 x u w hxu hxw huw n1 n2 n3 hn
    exact ⟨a, all ⟨x, u, hxu⟩ a ha, h1, h2, h3⟩

section Inner

variable {n : Nat} {zone sv : Nat → Nat} {m b : Nat}

/-- **Pegar un solo lado**: `v` dentro del bloque `m`, el separador `m` fijado, el lado `m … b-1`, y `a0` fuera. -/
theorem glue_one_tri (hl : LocPair φ P0 P σ) (D : ChainN φ n zone) {v : Nat} (hv : stepVar φ σ = some v)
    (hzv : zone v = m) (hmb : m < b) (hbn : b ≤ n)
    (hfa : ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + m → c z = c' z) (hfb : FixedEnd n zone P0 b)
    {x u w : PathNodeId} {a0 : Assign} (h0 : P0 a0) (hx0 : pidOfAssign φ a0 x.id.step = x)
    (hu0 : pidOfAssign φ a0 u.id.step = u) (hw0 : pidOfAssign φ a0 w.id.step = w) {sR : Nat → Assign}
    (O : SideOut φ n zone P0 P x.id.step u.id.step w.id.step a0 m b sR) : TriOf φ P x u w := by
  have hmn : m < n := by omega
  let src : Nat → Assign := fun p => if p < m then a0 else if p < b then sR p else a0
  have sA : ∀ p, p < m → src p = a0 := fun p h => by simp only [src]; rw [if_pos h]
  have sRp : ∀ p, m ≤ p → p < b → src p = sR p := fun p h h' => by
    simp only [src]; rw [if_neg (by omega), if_pos h']
  have sB : ∀ p, b ≤ p → src p = a0 := fun p h => by
    simp only [src]; rw [if_neg (by omega), if_neg (by omega)]
  have hs : ∀ j, j < n → P0 (src j) := by
    intro j hj
    by_cases h1 : j < m
    · rw [sA j h1]; exact h0
    by_cases h2 : j < b
    · rw [sRp j (by omega) h2]; exact O.p0 _ (by omega) h2
    · rw [sB j (by omega)]; exact h0
  have hJ : JoinN n zone src := by
    intro q hq1 hqn z hz
    by_cases c1 : q < m
    · rw [sA _ (by omega), sA _ c1]
    by_cases c2 : q = m
    · subst c2
      rw [sA _ (by omega), sRp _ (Nat.le_refl _) hmb]
      exact hfa a0 _ h0 (O.p0 _ (Nat.le_refl _) hmb) z hz
    by_cases c3 : q < b
    · rw [sRp _ (by omega) (by omega), sRp _ (by omega) c3]
      exact O.join q (by omega) c3 z hz
    by_cases c4 : q = b
    · subst c4
      rw [sRp _ (by omega) (by omega), sB _ (Nat.le_refl _)]
      exact hfb hqn _ a0 (O.p0 _ (by omega) (by omega)) h0 z hz
    · rw [sB _ (by omega), sB _ (by omega)]
  have hP : ∀ j, j < n → BlkN n zone j v → P (src j) := by
    intro j hj hB
    have e : j = m := by rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    subst e; rw [sRp _ (Nat.le_refl _) hmb]; exact O.pm
  have ha : ∀ p, p < n → Agr φ x.id.step u.id.step w.id.step (OwnN n zone p) (src p) a0 := by
    intro p hp z hz hw
    by_cases c1 : p < m
    · rw [sA _ c1]
    by_cases c2 : p < b
    · rw [sRp _ (by omega) c2]
      have hB : BlkN n zone p z := by
        rcases hz with h | ⟨h1, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨h1, h⟩)
      refine O.agr p (by omega) c2 z hB (fun e => ?_) hw
      rcases hz with h | ⟨_, h⟩ <;> omega
    · rw [sB _ (by omega)]
  exact glueN_tri hl D hv ⟨m, hmn, Or.inl hzv⟩ h0 hx0 hu0 hw0 hs hJ hP ha

/-- **`v` dentro del bloque `m`, con el separador `m` fijado**: un solo lado. -/
theorem phantomFree_inner (hl : LocPair φ P0 P σ) (S : SideData φ n zone sv P0 Nn m b) {v : Nat}
    (hv : stepVar φ σ = some v) (hzv : zone v = m)
    (hfa : ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + m → c z = c' z) (hσ0 : 0 ≤ σ) (hσN : σ < Nn) :
    PhantomFree φ P0 P Nn σ := by
  refine phantomFree_of_descent hσ0 hσN (fun x u w => frS φ sv m b x.id.step u.id.step w.id.step)
    (fun R Tf hS hanch x u w t ih => ?_)
  obtain ⟨a0, h0, hx0, hu0, hw0⟩ := t.b3 hS
  have hpos := frS_pos (φ := φ) (sv := sv) (i := x.id.step) (j := u.id.step) (l := w.id.step) S.mb
  by_cases hf : 2 ≤ frS φ sv m b x.id.step u.id.step w.id.step
  · obtain ⟨lam, l0, lN, lr, hsrc⟩ := side_window (P := P) S hf h0
    have hno := frS_un (φ := φ) (sv := sv) S.L4 (k := 1) (Nat.le_refl _) (i := x.id.step) (j := u.id.step)
      (l := w.id.step) (by omega)
    obtain ⟨Q, C, _⟩ := capFull hl hS t hx0 hu0 hw0 l0 lN lr hno (fun x' u' w' t' h' => ih x' u' w' t' (by
      have := frS_of (φ := φ) S.L4 (Nat.le_refl _) (i := x'.id.step) (j := u'.id.step) (l := w'.id.step) h'
      omega))
    obtain ⟨sR, O⟩ := hsrc C
    exact glue_one_tri hl S.D hv hzv S.mb S.bn hfa S.fix h0 hx0 hu0 hw0 O
  · rcases faces_sigma hS hanch hσ0 hσN t h0 hx0 hu0 hw0 with h | ⟨c1, c2, c3, F⟩
    · exact h
    obtain ⟨d, qd, ag⟩ := F.pick S.no3_res
    obtain ⟨sR, O⟩ := side_res S (by omega) h0 qd (hl.sub _ qd) ag
    exact glue_one_tri hl S.D hv hzv S.mb S.bn hfa S.fix h0 hx0 hu0 hw0 O

end Inner


/-! ## Las líneas, con la variable que ya fija `k` -/

theorem litAt_lt (hb : Bounded φ) {c : Clause} (hc : c ∈ φ.clauses) (p : Nat) : (litAt c p).v < φ.nVars := by
  have h := hb c hc
  rcases p with _ | _ | p
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem binStep_lt_mid {l : Lit} (h : l.v < φ.nVars) : l.binStep < midFusion φ := by
  unfold Lit.binStep midFusion; split <;> omega

open Driver Machine MachineOn in
/-- **Una línea de una cláusula, sabiendo qué fija `k`**: como `phantomAt_of_lineLocal`, pero el caso recibe también
la posición `p` del literal, que las ramas de `P0` leen igual la variable del paso `T - 1` (la que fija `k`) y que el
paso fijado solo es el tercero de una cláusula si es el propio `T`. -/
theorem phantomAt_of_lineLocalF (hb : Bounded φ) {j0 : Nat} {c0 : Clause} (hj0 : φ.clauses[j0]? = some c0) {T : Int}
    (hT0 : clauseStep φ j0 0 ≤ T) (hT2 : T ≤ clauseStep φ j0 2) (hT : 1 ≤ T)
    (H : ∀ {P0 P : Assign → Prop} {σ N : Int} {v : Nat} (p : Nat), p < 3 → T = clauseStep φ j0 p →
      (litAt c0 p).v = v → LocPair φ P0 P σ → stepVar φ σ = some v → (isL3 φ σ = true → σ = T) →
      (∀ a b, P0 a → P0 b → ∀ w, stepVar φ (T - 1) = some w → a w = b w) →
      0 ≤ σ → σ < N → T ≤ N → PhantomFree φ P0 P N σ) : PhantomAt φ T := by
  intro k d hk hd
  have hds : d.step = T := by
    have := sonsOfMap_step φ k d hd
    have hks := mapNodes_step φ (T - 1) k hk
    omega
  have hmid : midFusion φ < T := by
    have : midFusion φ < clauseStep φ j0 0 := by simp only [clauseStep, midFusion]; omega
    omega
  have hjlt : j0 < φ.clauses.length := by
    by_cases h : j0 < φ.clauses.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hj0; cases hj0
  have hc0 : c0 ∈ φ.clauses := List.mem_of_getElem? hj0
  have fixK : ∀ a b, SolE φ T k a → SolE φ T k b → ∀ w, stepVar φ (T - 1) = some w → a w = b w :=
    fun a b ha hb' w hw => var_eq_of_sel (ha.2.trans hb'.2.symm) w hw
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨r1, r2⟩ := reqOf_range hb r hr
    rw [hds] at r2
    cases hv : stepVar φ r.step with
    | none => exact phantomFree_none (locPair_filter T k r) hv (by omega) r2
    | some v =>
      obtain ⟨j, c, p, hj, hp, e, hpv⟩ := req_lit hb hr hv (by rw [hds]; exact hmid)
      have hjj : j = j0 := by rw [hds] at e; simp only [clauseStep] at e hT0 hT2; omega
      subst hjj
      rw [hj0] at hj; cases hj
      -- el requisito está antes de la fusión: no es el tercer paso de una cláusula
      have hreq := reqOf_clause φ d j p c0 hp hjlt hj0 e
      rw [hreq] at hr
      have hrs : r.step = (litAt c0 p).binStep := by
        rw [List.mem_singleton] at hr; rw [hr]
      have hlow : r.step < midFusion φ := by rw [hrs]; exact binStep_lt_mid (litAt_lt hb hc0 p)
      have hL3 : isL3 φ r.step = true → r.step = T := by
        intro h
        simp only [isL3, Bool.and_eq_true, decide_eq_true_eq] at h
        omega
      exact H p hp (by rw [← hds]; exact e) hpv (locPair_filter T k r) hv hL3 fixK (by omega) r2 (Int.le_refl _)
  · cases hv : stepVar φ T with
    | none => exact phantomFree_none (locPair_up hb T k d) hv (by omega) (show T < T + 1 by omega)
    | some v =>
      obtain ⟨j, c, p, hj, hp, e, hpv⟩ := step_lit hv hmid
      have hjj : j = j0 := by simp only [clauseStep] at e hT0 hT2; omega
      subst hjj
      rw [hj0] at hj; cases hj
      exact H p hp e hpv (locPair_up hb T k d) hv (fun _ => rfl) (fun a b ha hb' => fixK a b ha.1 hb'.1)
        (by omega) (by omega) (by omega)


/-! ## Cadenas concretas: la zona como lista -/

/-- La zona de una cadena concreta: el valor de cada variable en una lista (fuera de ella, fuera de la cadena). -/
def zoneV (n : Nat) (vals : List Nat) (z : Nat) : Nat := vals.getD z (2 * n)

theorem zoneV_ge {n : Nat} {vals : List Nat} {z : Nat} (h : vals.length ≤ z) : zoneV n vals z = 2 * n := by
  simp [zoneV, List.getD, List.getElem?_eq_none h]

theorem zoneV_small {n : Nat} {vals : List Nat} {z k : Nat} (hz : zoneV n vals z = k) (hk : k < 2 * n) :
    z < vals.length :=
  Nat.lt_of_not_le (fun h => by rw [zoneV_ge h] at hz; omega)

instance decOutN (n : Nat) (zone : Nat → Nat) (z : Nat) : Decidable (OutN n zone z) :=
  inferInstanceAs (Decidable (zone z = n ∨ 2 * n ≤ zone z))

instance decBlkN (n : Nat) (zone : Nat → Nat) (j z : Nat) : Decidable (BlkN n zone j z) :=
  inferInstanceAs (Decidable (zone z = j ∨ (1 ≤ j ∧ zone z = n + j) ∨ (j + 1 < n ∧ zone z = n + j + 1)))

instance decClIn {B : Nat → Prop} [DecidablePred B] (c : Clause) : Decidable (ClIn B c) :=
  inferInstanceAs (Decidable (B c.l1.v ∧ B c.l2.v ∧ B c.l3.v))

/-- **Una cadena concreta**, con las condiciones acotadas a las variables de la lista (se comprueban con `decide`). -/
theorem chainN_of_vals {n : Nat} {vals : List Nat} (two : 2 ≤ n) (hlen : vals.length ≤ φ.nVars)
    (sep1 : ∀ i, i < n → 1 ≤ i → ∀ z, z < vals.length → ∀ z', z' < vals.length → zoneV n vals z = n + i →
      zoneV n vals z' = n + i → z = z')
    (card0 : ∀ z1, z1 < vals.length → ∀ z2, z2 < vals.length → ∀ z3, z3 < vals.length → zoneV n vals z1 = 0 →
      zoneV n vals z2 = 0 → zoneV n vals z3 = 0 → z1 = z2 ∨ z1 = z3 ∨ z2 = z3)
    (cardL : ∀ z1, z1 < vals.length → ∀ z2, z2 < vals.length → ∀ z3, z3 < vals.length → zoneV n vals z1 = n - 1 →
      zoneV n vals z2 = n - 1 → zoneV n vals z3 = n - 1 → z1 = z2 ∨ z1 = z3 ∨ z2 = z3)
    (cardM : ∀ j, j < n → 1 ≤ j → j + 1 < n → ∀ z, z < vals.length → ∀ z', z' < vals.length →
      zoneV n vals z = j → zoneV n vals z' = j → z = z')
    (cl : ∀ c ∈ φ.clauses, ClIn (OutN n (zoneV n vals)) c ∨ ∃ j, j < n ∧ ClIn (BlkN n (zoneV n vals) j) c) :
    ChainN φ n (zoneV n vals) := by
  refine ⟨two, fun z a b => by have := zoneV_small rfl b; omega, fun i h1 h2 z z' hz hz' => ?_,
    fun y1 y2 y3 a b c d12 d13 d23 => ?_, fun y1 y2 y3 a b c d12 d13 d23 => ?_,
    fun j h1 h2 z z' hz hz' => ?_, cl⟩
  · exact sep1 i h2 h1 z (zoneV_small hz (by omega)) z' (zoneV_small hz' (by omega)) hz hz'
  · rcases card0 y1 (zoneV_small a (by omega)) y2 (zoneV_small b (by omega)) y3 (zoneV_small c (by omega)) a b c
      with e | e | e
    · exact d12 e
    · exact d13 e
    · exact d23 e
  · rcases cardL y1 (zoneV_small a (by omega)) y2 (zoneV_small b (by omega)) y3 (zoneV_small c (by omega)) a b c
      with e | e | e
    · exact d12 e
    · exact d13 e
    · exact d23 e
  · exact cardM j (by omega) h1 h2 z (zoneV_small hz (by omega)) z' (zoneV_small hz' (by omega)) hz hz'

/-- Una zona con un solo valor `k` en la lista: la variable de esa zona. -/
theorem zoneV_eq {n : Nat} {vals : List Nat} {k y : Nat} (hk : k < 2 * n)
    (h : ∀ z, z < vals.length → zoneV n vals z = k → z = y) {z : Nat} (hz : zoneV n vals z = k) : z = y :=
  h z (zoneV_small hz hk) hz

end GPathB

end AbsSatBingo.Model
