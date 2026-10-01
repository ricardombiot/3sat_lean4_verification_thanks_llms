-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnArr.lean
import AbsSatBingo.Model.ForbidOnPin

/-!
# La llegada fijada con la regla activa: la dirección 1 y `good_arrivalOn`

Sea `E` un remitente, `A = upOn (filterAllOn E reqs) d` su llegada, `h = pinOn A R` la llegada fijada y
`X = pinOn E (reqs ++ R)` la entrada fijada.

**Dirección 1** (`ct_arrival_up`): una camarilla `D` de `X` que esquiva sus tríos, con una cima `D c` viva en `h` cuyo
documento en `h` tiene a `D (c-1)` por padre, es una camarilla de `h` que esquiva los suyos. Solo usa la solidez:
`D` sube a `E`, pasa el filtro (`ct_filterAllOn`), el UP (`ct_upOn`) y el pin (`ct_pinOn`).

**`liveExt_arrivalOn`**: `LiveExt` de la entrada fijada da `LiveExt` de la llegada fijada. Una cadena viva de `h` con
algún nodo bajo la cima baja a `X` (dirección 2, `liveChain_down`), se completa allí hasta el paso 0 y la completación
sube con la cima (dirección 1). La cadena de un solo nodo (la cima) se alarga con un padre, porque `h` está cerrado.

**`good_arrivalOn`**: `GoodOn E → GoodOn A`, con `GoodOn g` = `LiveExt` tras todo pin válido.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

-- ============================================================
-- Piezas genéricas
-- ============================================================

/-- **`GoodOn`**: `LiveExt` con los tríos reales tras todo pin válido (el `Good` de `:off`, sin familias). -/
def GoodOn (g : GPathB) : Prop := ∀ R, (g.pinOn R).isValid = true → LiveExt (g.pinOn R) (TF (g.pinOn R))

/-- Bajo `LiveExt`, una cadena viva baja hasta el paso 0 sin cambiar lo que ya tenía. -/
theorem liveChain_to_zero {g : GPathB} {F : Trios} (hext : LiveExt g F) {C : Int → PathNodeId} {j : Int}
    (hC : LiveChain g F C j) (hj0 : 0 ≤ j) (hj : j ≤ g.current_step - 1) :
    ∃ D, LiveChain g F D 0 ∧ ∀ k, j ≤ k → D k = C k := by
  have key : ∀ i : Nat, (i : Int) ≤ j → ∃ D, LiveChain g F D (j - i) ∧ ∀ k, j ≤ k → D k = C k := by
    intro i
    induction i with
    | zero => intro _; exact ⟨C, by simpa using hC, fun _ _ => rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨D, hD, hag⟩ := ih (by omega)
      obtain ⟨D', hD', hag'⟩ := hext D _ hD (by push_cast at hi; omega) (by omega)
      refine ⟨D', ?_, fun k hk => by rw [hag' k (by omega), hag k hk]⟩
      have : j - ((i + 1 : Nat) : Int) = j - (i : Int) - 1 := by push_cast; omega
      rw [this]; exact hD'
  obtain ⟨D, hD, hag⟩ := key j.toNat (by omega)
  refine ⟨D, ?_, hag⟩
  have : j - (j.toNat : Int) = 0 := by omega
  rw [this] at hD; exact hD

/-- **El pin `:on` conserva `CT`** si la rama cumple los requisitos. -/
theorem ct_pinOn {g : GPathB} {S : Int → PathNodeId} (h : CT g S) (R : List NodeId)
    (ha : ∀ r ∈ R, Agrees g.current_step S r) : CT (g.pinOn R) S := by
  unfold pinOn
  apply ct_reviewOn
  apply ct_dirty
  have key : ∀ (l : List NodeId) (x : GPathB), CT x S → x.current_step = g.current_step →
      (∀ r ∈ l, Agrees g.current_step S r) → CT (l.foldl filterRequire x) S := by
    intro l
    induction l with
    | nil => intro x hx _ _; exact hx
    | cons r rs ih =>
      intro x hx hxs hl
      rw [List.foldl_cons]
      exact ih _ (ct_filterRequire hx (by rw [hxs]; exact hl r List.mem_cons_self))
        ((shrinks_filterRequire x r).1.step.trans hxs) (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr'))
  exact key R g h rfl ha

/-- El pin `:on` de un estado de la línea, si es válido, está cerrado. -/
theorem closedState_pinOn {g : GPathB} (hg : SInvB g) {R : List NodeId} (hv : (g.pinOn R).isValid = true)
    (hcs : 2 ≤ g.current_step) : ClosedState (g.pinOn R) := by
  have hi := sInvB_dirty (sInvB_foldl hg R) true
  exact closedState_reviewOn (g := { R.foldl filterRequire g with dirty := true }) rfl hv
    hi.docs hi.nodup hi.below hi.zero (by
      show 2 ≤ (R.foldl filterRequire g).current_step
      rw [(shrinks_foldl filterRequire shrinks_filterRequire R g).1.step]; exact hcs)

-- ============================================================
-- La dirección 1
-- ============================================================

section Arr

variable {E : GPathB} {reqs R : List NodeId} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **Dirección 1**: una camarilla de la entrada fijada que esquiva sus tríos, más una cima viva en la llegada fijada
que la tiene por padre, es una camarilla de la llegada fijada que esquiva los suyos. -/
theorem ct_arrival_up (hE : SInvB E) (hns : NoSelf E) (htb : TB E)
    (hd : d.step = E.current_step) (hpos : 1 ≤ E.current_step)
    (hvh : (((E.filterAllOn reqs).upOn d title forb).pinOn R).isValid = true)
    {D : Int → PathNodeId} (hc : Carried (E.pinOn (reqs ++ R)) D)
    (hA : Avoids (TF (E.pinOn (reqs ++ R))) E.current_step D)
    (hts : (D E.current_step).id.step = E.current_step)
    (hta : D E.current_step ∈ (((E.filterAllOn reqs).upOn d title forb).pinOn R).alive)
    (hlk : ∃ n, (((E.filterAllOn reqs).upOn d title forb).pinOn R).node? (D E.current_step) = some n ∧
      D (E.current_step - 1) ∈ n.parents) :
    CT (((E.filterAllOn reqs).upOn d title forb).pinOn R) D := by
  let Y := E.filterAllOn reqs
  let A := Y.upOn d title forb
  let X := E.pinOn (reqs ++ R)
  have hcsY : Y.current_step = E.current_step := step_filterAllOn E reqs
  have hcsX : X.current_step = E.current_step := step_pinOn E _
  have hvA : A.isValid = true := isValid_of_sub (sub_pinOn A R) hvh
  have hvY : Y.isValid = true := valid_of_upOn hvA
  have hdY : d.step = Y.current_step := by rw [hcsY]; exact hd
  have hiY : SInvB Y := sInvB_filterAllOn hE reqs
  have hiA : SInvB A := sInvB_upOn hiY hdY (by omega)
  have hiYa : SInvB (Y.addNode d title forb) := sInvB_addNode hiY hdY (by omega)
  have hcsA : A.current_step = E.current_step + 1 := by
    rw [(sub_upOn_addNode hvY).step]; show Y.current_step + 1 = _; rw [hcsY]
  have hsubh : Sub (A.pinOn R) (Y.addNode d title forb) := (sub_pinOn A R).trans (sub_upOn_addNode hvY)
  have hvX : X.isValid = true := isValid_of_carried hc
  -- la rama sube al remitente
  have hcE : Carried E D := carried_of_sub (sub_pinOn E _) hE.nodup hc
  have hAE : Avoids (TF E) E.current_step D := by
    intro i j k h0 h1 h2 h3 h4 h5 hf
    exact hA i j k h0 h1 h2 h3 h4 h5
      (tF_mono (trios_grow_pinOn E _) (hc.adj i j h0 (by rw [hcsX]; exact h1) h2 (by rw [hcsX]; exact h3)) hf)
  have hctE : CT E D := ⟨hcE, hAE, hns⟩
  -- los pins que cumple la rama
  have hpin : ∀ r ∈ reqs ++ R, 0 ≤ r.step → r.step < E.current_step → (D r.step).id = r := fun r hr h0 h1 =>
    pinned_pinOn hE.docs hvX r hr (D r.step) (hc.alive r.step h0 (by rw [hcsX]; exact h1))
      (hc.step r.step h0 (by rw [hcsX]; exact h1))
  -- el filtro
  have hctY : CT Y D := ct_filterAllOn hctE reqs (fun r hr => hpin r (List.mem_append_left _ hr))
  -- el UP
  have hnew : D Y.current_step ∈ Y.newRowIds d forb := by
    rw [hcsY]
    rcases alive_addNode_cases hiY.docs hiY.below hdY (hsubh.alive _ hta) with ⟨_, h⟩ | ⟨h, _⟩
    · rw [hcsY] at h; omega
    · exact h
  have hpar : 0 < Y.current_step → D (Y.current_step - 1) ∈ Y.rowParents d (D Y.current_step) := by
    intro _
    obtain ⟨n, hn, hp⟩ := hlk
    obtain ⟨m, hm, hpm, _⟩ := up_doc hsubh hiYa.nodup hn
    have hm' := node?_addNode_new (title := title) hiY.below hdY hnew
    rw [hcsY] at hm' ⊢
    rw [hm'] at hm
    cases hm
    exact hpm _ hp
  have hctA : CT A D := ct_upOn hctY (tb_filterAllOn htb reqs) hnew hpar (by rw [hcsY]; exact hts) hiY.below
    (hc.root (by rw [hcsX]; omega))
  -- el pin
  refine ct_pinOn hctA R (fun r hr h0 h1 => ?_)
  rw [hcsA] at h1
  by_cases hlt : r.step < E.current_step
  · exact hpin r (List.mem_append_right _ hr) h0 hlt
  · have he : r.step = E.current_step := by omega
    rw [he]
    exact pinned_pinOn hiA.docs hvh r hr _ hta (by rw [hts, he])

/-- **La llegada**: `LiveExt` de la entrada fijada da `LiveExt` de la llegada fijada, con los tríos reales. -/
theorem liveExt_arrivalOn (hE : SInvB E) (hns : NoSelf E) (hndt : NoDegT E) (htb : TB E) (hlen : reqs.length ≤ 1)
    (hd : d.step = E.current_step) (hpos : 1 ≤ E.current_step)
    (hvh : (((E.filterAllOn reqs).upOn d title forb).pinOn R).isValid = true)
    (hext : LiveExt (E.pinOn (reqs ++ R)) (TF (E.pinOn (reqs ++ R)))) :
    LiveExt (((E.filterAllOn reqs).upOn d title forb).pinOn R)
      (TF (((E.filterAllOn reqs).upOn d title forb).pinOn R)) := by
  let Y := E.filterAllOn reqs
  let A := Y.upOn d title forb
  let h := A.pinOn R
  let X := E.pinOn (reqs ++ R)
  let c := E.current_step
  have hcsY : Y.current_step = c := step_filterAllOn E reqs
  have hcsX : X.current_step = c := step_pinOn E _
  have hvA : A.isValid = true := isValid_of_sub (sub_pinOn A R) hvh
  have hvY : Y.isValid = true := valid_of_upOn hvA
  have hdY : d.step = Y.current_step := by rw [hcsY]; exact hd
  have hiY : SInvB Y := sInvB_filterAllOn hE reqs
  have hiA : SInvB A := sInvB_upOn hiY hdY (by omega)
  have hcsA : A.current_step = c + 1 := by
    rw [(sub_upOn_addNode hvY).step]; show Y.current_step + 1 = _; rw [hcsY]
  have hcsh : h.current_step = c + 1 := (step_pinOn A R).trans hcsA
  have hih : SInvB h := sInvB_pinOn hiA R
  have hiX : SInvB X := sInvB_pinOn hE _
  intro C j hC hj1 hjt
  rw [hcsh] at hjt
  by_cases hjc : j = c
  · -- la cadena es solo la cima: se baja a un padre, porque la llegada fijada está cerrada
    subst hjc
    have hcl : ClosedState h := closedState_pinOn hiA hvh (by rw [hcsA]; omega)
    obtain ⟨hts, hta⟩ := hC.chain.node c (Int.le_refl _) (by rw [hcsh]; omega)
    obtain ⟨r, hrs, htr, _⟩ := hcl.pair (hcl.refl hta) (c - 1) (by omega) (by rw [hcsh]; omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hih.docs hta)
    have hne : C c ≠ r := by intro e; rw [← e, hts] at hrs; omega
    obtain ⟨p, hp, htp, _⟩ := hcl.par htr hne hn (by rw [hts]; exact hj1)
    have hps : p.id.step = c - 1 := by
      have := (hih.lstep n (node?_mem hn)).1 p hp
      rw [node?_id hn, hts] at this; omega
    classical
    let C' : Int → PathNodeId := fun k => if k = c - 1 then p else C k
    have hC'p : C' (c - 1) = p := by simp [C']
    have hC't : C' c = C c := by
      have : ¬ c = c - 1 := by omega
      simp [C', this]
    refine ⟨C', ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩,
      fun a b c' ha hab hbc hc => by rw [hcsh] at hc; omega⟩, fun k hk => ?_⟩
    · rw [hcsh] at h2
      rcases (show k = c - 1 ∨ k = c by omega) with rfl | rfl
      · rw [hC'p]; exact ⟨hps, htp.2.1⟩
      · rw [hC't]; exact ⟨hts, hta⟩
    · rw [hcsh] at h2 h4
      rcases (show k = c - 1 ∨ k = c by omega) with rfl | rfl <;>
        rcases (show l = c - 1 ∨ l = c by omega) with rfl | rfl
      · rw [hC'p]; exact adj_refl _ _ htp.2.1
      · rw [hC'p, hC't]; exact (adj_symm h _ _).mp htp.2.2
      · rw [hC'p, hC't]; exact htp.2.2
      · rw [hC't]; exact adj_refl _ _ hta
    · rw [hcsh] at h2
      have hk : k = c := by omega
      subst hk
      rw [hC't, hC'p]
      exact ⟨n, hn, hp⟩
    · have : ¬ k = c - 1 := by omega
      simp [C', this]
  · -- hay nodos bajo la cima: bajar, completar en la entrada fijada y subir
    have hjlt : j ≤ c - 1 := by omega
    have hX : LiveChain X (TF X) C j := liveChain_down hE hns hndt hlen hd hpos hvh hC
    obtain ⟨D, hD, hag⟩ := liveChain_to_zero hext hX (by omega) (by rw [hcsX]; exact hjlt)
    have hcX : Carried X D := carried_of_liveChain hiX.docs hiX.links hiX.root hD
    have hAX : Avoids (TF X) c D := by
      have := avoids_of_liveChain (noDeg_TF (noDegT_pinOn hns hndt (reqs ++ R))) hD
      rw [hcsX] at this; exact this
    obtain ⟨hts, hta⟩ := hC.chain.node c (by omega) (by rw [hcsh]; omega)
    obtain ⟨n, hn, hp⟩ := hC.chain.link c (by omega) (by rw [hcsh]; omega)
    have e1 : D c = C c := hag c (by omega)
    have e2 : D (c - 1) = C (c - 1) := hag (c - 1) hjlt
    have hct : CT h D := ct_arrival_up hE hns htb hd hpos hvh hcX hAX (by rw [e1]; exact hts)
      (by rw [e1]; exact hta) ⟨n, by rw [e1]; exact hn, by rw [e2]; exact hp⟩
    exact ⟨D, liveChain_of_carried hct.1 hct.2.1 (by omega), fun k hk => hag k hk⟩

/-- La entrada fijada es válida si lo es la llegada fijada. -/
theorem valid_down (hE : SInvB E) (hns : NoSelf E) (hndt : NoDegT E) (hlen : reqs.length ≤ 1)
    (hd : d.step = E.current_step) (hpos : 1 ≤ E.current_step)
    (hvh : (((E.filterAllOn reqs).upOn d title forb).pinOn R).isValid = true) :
    (E.pinOn (reqs ++ R)).isValid = true := by
  have hX := downInv_arrival hE hns hndt hlen hd hpos hvh
  have hvA := isValid_of_sub (sub_pinOn ((E.filterAllOn reqs).upOn d title forb) R) hvh
  have hcsh : (((E.filterAllOn reqs).upOn d title forb).pinOn R).current_step = E.current_step + 1 := by
    rw [step_pinOn, (sub_upOn_addNode (valid_of_upOn hvA)).step]
    show (E.filterAllOn reqs).current_step + 1 = _
    rw [step_filterAllOn]
  obtain ⟨q, hq, hqs⟩ := exists_alive_at hvh (k := 0) (Int.le_refl 0) (by rw [hcsh]; omega)
  exact isValid_of_sec hX.sec (y := q) ⟨hq, by rw [hqs]; omega⟩

/-- **`good_arrivalOn`**: si la entrada cumple `LiveExt` tras todo pin válido, su llegada también. -/
theorem good_arrivalOn (hE : SInvB E) (hns : NoSelf E) (hndt : NoDegT E) (htb : TB E) (hlen : reqs.length ≤ 1)
    (hd : d.step = E.current_step) (hpos : 1 ≤ E.current_step) (hg : GoodOn E) :
    GoodOn ((E.filterAllOn reqs).upOn d title forb) := fun R hvh =>
  liveExt_arrivalOn hE hns hndt htb hlen hd hpos hvh (hg (reqs ++ R) (valid_down hE hns hndt hlen hd hpos hvh))

end Arr

end GPathB

end AbsSatBingo.Model
