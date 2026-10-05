-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnWinBridge.lean
import AbsSatBingo.Model.ForbidOnTwoWitness

/-!
# El puente: la ventana entera con el ancla en el paso del nodo de ventana

`snd3_filterL` aplica `PhantomFree` una vez por requisito. Con un nodo de ventana basta **una sola vez**, con el ancla
en el paso `σ` del nodo de ventana y la familia que cumple los tres requisitos a la vez: en el estado fijado, una rama
de `P0` que pasa por un nodo vivo `s` del paso `σ` lee en `σ - 1` y `σ - 2` lo mismo que la rama de cualquier pareja
de `s` con un vivo de esos pasos (`sels_of_pid_eq`), y esos vivos están fijados a los requisitos.

* **`snd3_filterW`**, `read_stepW`.
* **`WinPinFreeW φ T`**: con cualesquiera ventanas antes, fijar la ventana entera no deja familias fantasma con el
  ancla en `σ`. `winPinFreeW_of_twoWitnessF`: H2′ la da.
* **`reader_winNode_of_winPinFreeW`** y **`reader_winNode_of_twoWitnessF`**: el lector por nodos de ventana no se
  atasca con las líneas (`PhantomAtW`) y H2′ para cada ventana. Sin condiciones de forma.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

open Driver Machine MachineOn

variable {φ : Cnf}

theorem snd3_filterW {E : GPathB} {T σ : Int} {P0 : Assign → Prop} {reqs : List NodeId} (hE : SInvB E)
    (hns : NoSelf E) (hndt : NoDegT E) (hcs : E.current_step = T) (hvE : E.isValid = true)
    (hrange : ∀ r ∈ reqs, 1 ≤ r.step ∧ r.step < T)
    (hwin : ∀ r ∈ reqs, r.step = σ ∨ r.step = σ - 1 ∨ r.step = σ - 2) (hσ2 : 2 ≤ σ) (hσT : σ < T)
    (hH : PhantomFree φ P0 (fun a => P0 a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r) T σ)
    (hs : Snd3 φ P0 E) (hc : ∀ a, P0 a → CT E (pidOfAssign φ a))
    (hvY : (E.filterAllOn reqs).isValid = true) :
    Snd3 φ (fun a => P0 a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r) (E.filterAllOn reqs) := by
  have hsh := (shrinks_filterAllOn E reqs).1
  cases hd : (reqs.foldl filterRequire E).dirty
  · -- los filtros no matan a nadie: toda rama de la entrada cumple los requisitos
    obtain ⟨_, hnv⟩ := foldl_clean reqs hd
    have agr : ∀ a, P0 a → ∀ r ∈ reqs, selOfAssign φ a r.step = r := by
      intro a hS r hr
      obtain ⟨hr1, hr2⟩ := hrange r hr
      have hD := hc a hS
      have hal := hD.1.alive r.step (by omega) (by rw [hcs]; exact hr2)
      obtain ⟨n, hn, hnid⟩ := hE.docs _ hal
      have hline : n ∈ E.line r.step := by
        unfold line
        refine List.mem_filter.mpr ⟨hn, ?_⟩
        rw [hnid, hD.1.step r.step (by omega) (by rw [hcs]; exact hr2)]
        simp
      have := hnv hvE r hr n hline
      rw [hnid] at this
      exact this
    refine ⟨fun x w hxw => ?_, fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
    · obtain ⟨a, hS, h1, h2⟩ := hs.1 x w (hsh.adj _ _ hxw)
      exact ⟨a, ⟨hS, agr a hS⟩, h1, h2⟩
    · have hnE : ¬ TF E x u w := fun hf => hn (tF_mono (trios_grow_filterAllOn E reqs) hxu hf)
      obtain ⟨a, hS, h1, h2, h3⟩ := hs.2 x u w (hsh.adj _ _ hxu) (hsh.adj _ _ hxw) (hsh.adj _ _ huw) nxu nxw nuw hnE
      exact ⟨a, ⟨hS, agr a hS⟩, h1, h2, h3⟩
  · cases reqs with
    | nil =>
      exact snd3_filter hE hns hndt hcs hvE (by simp) hrange (fun r hr => absurd hr List.not_mem_nil) hs hc hvY
    | cons r0 rs0 =>
    have hT2 : 2 ≤ T := by have := hrange r0 List.mem_cons_self; omega
    generalize hreqs : r0 :: rs0 = reqs at *
    have e : E.filterAllOn reqs = E.pinOn reqs := by
      unfold filterAllOn pinOn
      congr 1
      generalize reqs.foldl filterRequire E = F at hd
      cases F
      simp_all
    rw [e] at hvY ⊢
    have hsub := sub_pinOn E reqs
    have hiY : SInvB (E.pinOn reqs) := sInvB_pinOn hE reqs
    have hcl : ClosedState (E.pinOn reqs) := closedState_pinOn hE hvY (by rw [hcs]; exact hT2)
    have hf : FixClosed (E.pinOn reqs) :=
      fixClosed_reviewOn (g := { reqs.foldl filterRequire E with dirty := true }) rfl hvY
    have hg := trioGood_low hf (noDegT_pinOn hns hndt reqs) (Int.le_refl _)
    have hlt : ∀ {q : PathNodeId}, q ∈ (E.pinOn reqs).alive → q.id.step < (E.pinOn reqs).current_step :=
      fun hq => alive_below hiY.docs hiY.below hq
    have hR : ∀ {y z : PathNodeId}, (E.pinOn reqs).Adj y z →
        LowR (E.pinOn reqs) (E.pinOn reqs).current_step y z := fun h =>
      ⟨⟨(hiY.edges _ _ h).1, (hiY.edges _ _ h).2, h⟩, hlt (hiY.edges _ _ h).1, hlt (hiY.edges _ _ h).2⟩
    have pinned := pinned_pinOn hE.docs hvY
    have nE : ∀ {y z v : PathNodeId}, (E.pinOn reqs).Adj y z → ¬ TF (E.pinOn reqs) y z v → ¬ TF E y z v :=
      fun hyz hn hf => hn (tF_mono (trios_grow_pinOn E reqs) hyz hf)
    have agS : ∀ {r : NodeId}, r ∈ reqs → ∀ {a : Assign} {s : PathNodeId}, s ∈ (E.pinOn reqs).alive →
        s.id.step = r.step → pidOfAssign φ a s.id.step = s → selOfAssign φ a r.step = r := by
      intro r hr a s hsa hss hp
      have := congrArg PathNodeId.id hp
      rw [pid_id, hss] at this
      rw [this]; exact pinned r hr s hsa hss
    have b0 : ∀ {q : PathNodeId}, q ∈ (E.pinOn reqs).alive → 0 ≤ q.id.step ∧ q.id.step < T := by
      intro q hq
      obtain ⟨n, hn, rfl⟩ := hiY.docs q hq
      have h1 := hiY.below n hn
      rw [step_pinOn, hcs] at h1
      exact ⟨hiY.zero n hn, h1⟩
    have hcT : (E.pinOn reqs).current_step = T := by rw [step_pinOn, hcs]
    -- lo que da la estructura del estado fijado, para cualquier par de familias
    let L := LowR (E.pinOn reqs) (E.pinOn reqs).current_step
    let B2 : (Assign → Prop) → Prop := fun Q => ∀ y w, L y w →
      ∃ a, Q a ∧ pidOfAssign φ a y.id.step = y ∧ pidOfAssign φ a w.id.step = w
    let B3 : (Assign → Prop) → Prop := fun Q => ∀ x u w, L x u → L x w → L u w → x ≠ u → x ≠ w → u ≠ w →
      ¬ TF (E.pinOn reqs) x u w →
      ∃ a, Q a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w
    have use : ∀ {Pa Pb : Assign → Prop} {σ : Int}, PhantomFree φ Pa Pb T σ → B2 Pa → B3 Pa →
        (∀ a s, Pa a → L s s → s.id.step = σ → pidOfAssign φ a σ = s → Pb a) → B2 Pb ∧ B3 Pb := by
      intro Pa Pb σ hPF h2 h3 hanch
      exact hPF L (TF (E.pinOn reqs))
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
        h2 h3 hanch
    -- el ancla en `σ`: una rama de `P0` por un nodo `s` vivo del paso `σ` cumple los tres requisitos de la ventana
    have anch : ∀ a s, P0 a → L s s → s.id.step = σ → pidOfAssign φ a σ = s →
        P0 a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r := by
      intro a s ha hLs hstep hp
      -- una rama de `P0` por `s` y por un vivo del paso `l` lee allí el requisito de ese paso
      have via : ∀ {r : NodeId}, r ∈ reqs → r.step < σ → selOfAssign φ a r.step = r := by
        intro r hr hlt
        have l0 : 0 ≤ r.step := by have := hrange r hr; omega
        obtain ⟨q, hqs, hsq, _⟩ := hcl.pair (y := s) (w := s) hLs.1 r.step l0 (by rw [hcT]; omega)
        have hq : q.id = r := pinned r hr q hsq.2.1 hqs
        obtain ⟨b, _, hb1, hb2⟩ := hs.1 s q (hsub.adj _ _ hsq.2.2)
        have hpb : pidOfAssign φ a σ = pidOfAssign φ b σ := by rw [hp, ← hstep, hb1]
        obtain ⟨_, e1, e2⟩ := sels_of_pid_eq hpb
        have hbq : selOfAssign φ b r.step = r := by
          have := congrArg PathNodeId.id hb2
          rw [pid_id, hqs] at this; rw [this, hq]
        rcases hwin r hr with e | e | e
        · omega
        · rw [e, e1 (by omega), ← e]; exact hbq
        · rw [e, e2 (by omega), ← e]; exact hbq
      refine ⟨ha, fun r hr => ?_⟩
      rcases hwin r hr with e | e | e
      · have := congrArg PathNodeId.id hp
        rw [pid_id, ← hstep] at this
        rw [e, ← hstep, this]; exact pinned r hr s hLs.1.1 (by rw [hstep, e])
      · exact via hr (by omega)
      · exact via hr (by omega)
    have h2 : B2 P0 := fun y w h => hs.1 y w (hsub.adj _ _ h.1.2.2)
    have h3 : B3 P0 := fun x u w h1 h2 h3 n1 n2 n3 hn => hs.2 x u w (hsub.adj _ _ h1.1.2.2) (hsub.adj _ _ h2.1.2.2)
      (hsub.adj _ _ h3.1.2.2) n1 n2 n3 (nE h1.1.2.2 hn)
    obtain ⟨c2, c3⟩ := use hH h2 h3 anch
    refine ⟨fun x w hxw => c2 x w (hR hxw), fun x u w hxu hxw huw nxu nxw nuw hn =>
      c3 x u w (hR hxu) (hR hxw) (hR huw) nxu nxw nuw hn⟩

/-- **Un paso de lectura con la ventana entera**: una sola condición, con el ancla en `σ`. -/
theorem read_stepW {T σ : Int} {P : Assign → Prop} {g : GPathB} (h : RInv φ T P g) {reqs : List NodeId}
    (hw : ∃ a, P a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r) (hrange : ∀ r ∈ reqs, 1 ≤ r.step ∧ r.step < T)
    (hwin : ∀ r ∈ reqs, r.step = σ ∨ r.step = σ - 1 ∨ r.step = σ - 2) (hσ2 : 2 ≤ σ) (hσT : σ < T)
    (hH : PhantomFree φ P (fun a => P a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r) T σ) :
    RInv φ T (fun a => P a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r) (g.filterAllOn reqs) := by
  obtain ⟨a, hPa, hra⟩ := hw
  have hvY : (g.filterAllOn reqs).isValid = true := isValid_of_carried (comp_filter h.comp a ⟨hPa, hra⟩).1
  exact ⟨sInvB_filterAllOn h.inv _, noSelf_filterAllOn h.ns _, noDegT_filterAllOn h.ns h.ndt _,
    (step_filterAllOn g _).trans h.step, hvY,
    snd3_filterW h.inv h.ns h.ndt h.step h.valid hrange hwin hσ2 hσT hH h.snd h.comp hvY,
    fun b hb => comp_filter h.comp b hb⟩

/-- **`WinPinFreeW φ T`**: con cualesquiera ventanas fijadas antes, fijar una ventana entera no deja familias fantasma,
con el ancla en el paso de su nodo de ventana. -/
def WinPinFreeW (φ : Cnf) (T : Int) : Prop :=
  ∀ (k : NodeId) (W0 : List (List NodeId)) (j : Nat) (gp p x : NodeId), (∀ v ∈ W0, WinTriple φ v) →
    j < φ.clauses.length → gp.step = clauseStep φ j 0 → p.step = clauseStep φ j 1 → x.step = clauseStep φ j 2 →
    PhantomFree φ (Pinned φ (SolE φ T k) W0.flatten)
      (fun a => Pinned φ (SolE φ T k) W0.flatten a ∧ ∀ r ∈ [gp, p, x], selOfAssign φ a r.step = r) T x.step

/-- **H2′ para cada ventana da `WinPinFreeW`.** -/
theorem winPinFreeW_of_twoWitnessF {T : Int}
    (h : ∀ (k : NodeId) (W0 : List (List NodeId)) (j : Nat) (gp p x : NodeId), (∀ v ∈ W0, WinTriple φ v) →
      j < φ.clauses.length → gp.step = clauseStep φ j 0 → p.step = clauseStep φ j 1 → x.step = clauseStep φ j 2 →
      TwoWitnessF φ (Pinned φ (SolE φ T k) W0.flatten)
        (fun a => Pinned φ (SolE φ T k) W0.flatten a ∧ ∀ r ∈ [gp, p, x], selOfAssign φ a r.step = r) T)
    (hT : ∀ j, j < φ.clauses.length → clauseStep φ j 2 < T) : WinPinFreeW φ T := by
  intro k W0 j gp p x hW0 hj s0 s1 s2
  exact phantomFree_of_twoWitnessF (by rw [s2]; simp only [clauseStep]; omega) (by rw [s2]; exact hT j hj)
    (h k W0 j gp p x hW0 hj s0 s1 s2)

end GPathB

end AbsSatBingo.Model

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace MachineOn

open GPathB Driver Machine

variable {φ : Cnf}

/-- **El lector por nodos de ventana no se atasca** con las líneas (`PhantomAtW`) y `WinPinFreeW`: cada nodo de
ventana se fija en un solo filtro y la condición se pide una sola vez por ventana, con el ancla en su paso. -/
theorem reader_winNode_of_winPinFreeW (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T)
    (hW : WinPinFreeW φ (stepCount φ)) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ) {W : List (List NodeId)}
    {g' : GPathB} (hr : WinReading φ kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ W.flatten, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) := by
  have hpos := stepCount_pos φ
  have hn : (((stepCount φ - 1).toNat : Nat) : Int) + 1 = stepCount φ := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  have hl := lInvS3_stepsW hbd (stepCount φ - 1).toNat (fun T h1 _ => HA T h1)
  have hcomp := compLine_steps hbd (lInvS_of_s3 hl)
  rw [hn] at hl hcomp
  have hkv' : kv ∈ stepsM .on φ (stepCount φ - 1).toNat (initM .on φ) := hkv
  have hent := hl.on kv hkv'
  let P := SolE φ (stepCount φ) kv.1
  have h0 : RInv φ (stepCount φ) (Pinned φ P ([] : List (List NodeId)).flatten) kv.2 :=
    rInv_congr (P := SolE φ (stepCount φ) kv.1)
      ⟨hl.inv kv hkv', hent.2.1, hl.ndt kv hkv', hent.1.step, hent.1.valid, hl.snd kv hkv', hcomp kv hkv'⟩
      (fun a => ⟨fun ha => ⟨ha, fun r hr => absurd hr List.not_mem_nil⟩, fun ha => ha.1⟩)
  have main : ∀ {g g' : GPathB} {W : List (List NodeId)}, WinReading φ g W g' → ∀ W0 : List (List NodeId),
      (∀ v ∈ W0, WinTriple φ v) → RInv φ (stepCount φ) (Pinned φ P W0.flatten) g →
      RInv φ (stepCount φ) (Pinned φ P (W0 ++ W).flatten) g' := by
    intro g g' W hw
    induction hw with
    | nil g => intro W0 _ h; rw [List.append_nil]; exact h
    | @cons g g' q j p gp W hq hj hk hp hgp _ ih =>
      intro W0 hW0 h
      obtain ⟨hwit, s0, s1, hkT⟩ := win_sels h hq hk hp hgp
      have htri : WinTriple φ [gp, p, q.id] := ⟨j, gp, p, q.id, hj, rfl, s0, s1, hk⟩
      have hrange : ∀ r ∈ [gp, p, q.id], 1 ≤ r.step ∧ r.step < stepCount φ := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [hk] at hkT
        rcases hr with rfl | rfl | rfl
        · rw [s0]; simp only [clauseStep] at hkT ⊢; omega
        · rw [s1]; simp only [clauseStep] at hkT ⊢; omega
        · rw [hk]; simp only [clauseStep] at hkT ⊢; omega
      have hwin : ∀ r ∈ [gp, p, q.id], r.step = q.id.step ∨ r.step = q.id.step - 1 ∨ r.step = q.id.step - 2 := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · right; right; rw [s0, hk]; simp only [clauseStep]; omega
        · right; left; rw [s1, hk]; simp only [clauseStep]; omega
        · left; rfl
      have h1 := read_stepW h hwit hrange hwin (by rw [hk]; simp only [clauseStep]; omega) hkT
        (hW kv.1 W0 j gp p q.id hW0 hj s0 s1 hk)
      have h1' : RInv φ (stepCount φ) (Pinned φ P (W0 ++ [[gp, p, q.id]]).flatten) (g.filterAllOn [gp, p, q.id]) := by
        refine rInv_congr h1 (fun a => ⟨fun ha => ⟨ha.1.1, fun r hr => ?_⟩, fun ha => ⟨⟨ha.1, fun r hr => ?_⟩,
          fun r hr => ?_⟩⟩)
        · rw [List.flatten_append, List.flatten_singleton] at hr
          exact (List.mem_append.mp hr).elim (ha.1.2 r) (ha.2 r)
        · exact ha.2 r (by rw [List.flatten_append]; exact List.mem_append_left _ hr)
        · exact ha.2 r (by rw [List.flatten_append, List.flatten_singleton]; exact List.mem_append_right _ hr)
      have := ih (W0 ++ [[gp, p, q.id]]) (fun v hv => by
        rcases List.mem_append.mp hv with hv | hv
        · exact hW0 v hv
        · rw [List.mem_singleton] at hv; subst hv; exact htri) h1'
      rw [List.append_assoc, List.singleton_append] at this
      exact this
  have hfin := main hr [] (fun v hv => absurd hv List.not_mem_nil) h0
  rw [List.nil_append] at hfin
  refine ⟨hfin.valid, ?_⟩
  obtain ⟨q, hq, _⟩ := exists_alive_at hfin.valid (k := 0) (Int.le_refl 0) (by rw [hfin.step]; exact hpos)
  obtain ⟨a, ha, _, _⟩ := hfin.snd.1 q q (adj_refl _ _ hq)
  exact ⟨a, sat_of_validUpTo ha.1.1, ha.2, hfin.comp a ha⟩

/-- **El lector por nodos de ventana no se atasca con las líneas y H2′ en cada ventana**: ninguna condición de forma
sobre la fórmula. -/
theorem reader_winNode_of_twoWitnessF (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T)
    (h2 : ∀ (k : NodeId) (W0 : List (List NodeId)) (j : Nat) (gp p x : NodeId), (∀ v ∈ W0, WinTriple φ v) →
      j < φ.clauses.length → gp.step = clauseStep φ j 0 → p.step = clauseStep φ j 1 → x.step = clauseStep φ j 2 →
      TwoWitnessF φ (Pinned φ (SolE φ (stepCount φ) k) W0.flatten)
        (fun a => Pinned φ (SolE φ (stepCount φ) k) W0.flatten a ∧ ∀ r ∈ [gp, p, x], selOfAssign φ a r.step = r)
        (stepCount φ))
    {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ) {W : List (List NodeId)} {g' : GPathB}
    (hr : WinReading φ kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ W.flatten, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) :=
  reader_winNode_of_winPinFreeW hbd HA
    (winPinFreeW_of_twoWitnessF h2 (fun j hj => by simp only [clauseStep, stepCount]; omega)) hkv hr

end MachineOn

end AbsSatBingo.Model
