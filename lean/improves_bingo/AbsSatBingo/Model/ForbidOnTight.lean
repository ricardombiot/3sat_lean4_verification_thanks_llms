-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnTight.lean
import AbsSatBingo.Model.ForbidOnRead

/-!
# La condición es la justa: la máquina es exacta ⟺ la fórmula no tiene familias fantasma

`ForbidOnHelly` demuestra que `PhantomFree` basta para que el filtro y el UP conserven la exactitud. Aquí, el
recíproco, y con él la equivalencia.

La razón es la técnica del punto fijo (`DownInv`): una estructura cerrada por la regla y hecha de ramas de antes
**vive dentro del estado** como estructura cerrada completa —sus enlaces padre–hijo salen de la rama que realiza cada
pareja (`Carried.node`)—, cumple lo que se fija (el ancla), y por eso **sobrevive** al filtro y al review
(`struct_survives_filter`) y a la fila nueva y su review (`struct_survives_up`). Lo que sobrevive en un estado exacto
es de ramas que cumplen lo fijado; y si el estado no es válido, no hay estructura que sobreviva (`valid_of_sec`).

* `phantomFree_of_exact_filter`, `phantomFree_of_exact_up`: exactitud tras la operación ⟹ `PhantomFree`.
* `snd3_filter_iff`: con la entrada exacta, el estado filtrado es exacto ⟺ `PhantomFree`.
* **`machineExact_iff`**: `MachineExact φ ↔ ∀ T ≥ 1, PhantomAt φ T`. La máquina es exacta en todos sus estados
  (entradas, remitentes filtrados y llegadas) exactamente cuando la fórmula no tiene familias fantasma.

El lado derecho no menciona la máquina: la corrección de la máquina con tríos queda **equivalente** a un enunciado
sobre las soluciones de los prefijos de la fórmula. La hipótesis de los veredictos de `ForbidOnHelly` no es más fuerte
de lo necesario para la exactitud.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Driver Machine MachineOn

variable {φ : Cnf}

/-- **Una estructura de `PhantomFree`**: simétrica, cerrada por la regla en los pasos `0 … N - 1`, con sus parejas y
sus triángulos sin prohibir en ramas de `P0`. -/
structure PhStruct (φ : Cnf) (P0 : Assign → Prop) (N : Int) (R : PathNodeId → PathNodeId → Prop) (Tf : Trios) :
    Prop where
  refl  : ∀ y w, R y w → R y y ∧ R w w
  symm  : ∀ y w, R y w → R w y
  sw23  : ∀ a b r, R a b → R a r → R b r → Tf a b r → Tf a r b
  sw12  : ∀ a b r, R a b → R a r → R b r → Tf a b r → Tf b a r
  steps : ∀ y w, R y w → 0 ≤ y.id.step ∧ y.id.step < N
  pair  : ∀ y w, R y w → ∀ l, 0 ≤ l → l < N →
            ∃ s, s.id.step = l ∧ R y s ∧ R w s ∧ (y = w ∨ s = y ∨ s = w ∨ ¬ Tf y w s)
  trio  : ∀ x u w, R x u → R x w → R u w → x ≠ u → x ≠ w → u ≠ w → ¬ Tf x u w → ∀ l, 0 ≤ l → l < N →
            ∃ s, s.id.step = l ∧ R x s ∧ R u s ∧ R w s ∧
              (s = x ∨ s = u ∨ s = w ∨ (¬ Tf x u s ∧ ¬ Tf x w s ∧ ¬ Tf u w s))
  b2    : ∀ y w, R y w → ∃ a, P0 a ∧ pidOfAssign φ a y.id.step = y ∧ pidOfAssign φ a w.id.step = w
  b3    : ∀ x u w, R x u → R x w → R u w → x ≠ u → x ≠ w → u ≠ w → ¬ Tf x u w →
            ∃ a, P0 a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧
              pidOfAssign φ a w.id.step = w

/-- Sin ramas en `P0` no hay estructura: `PhantomFree` vale. -/
theorem phantomFree_of_empty {P0 P : Assign → Prop} {N σ : Int} (h : ∀ a, ¬ P0 a) : PhantomFree φ P0 P N σ := by
  intro R Tf _ _ _ _ _ _ _ hb2 _ _
  refine ⟨fun y w hyw => ?_, fun x u w hxu _ _ _ _ _ _ => ?_⟩
  · obtain ⟨a, ha, _⟩ := hb2 y w hyw; exact absurd ha (h a)
  · obtain ⟨a, ha, _⟩ := hb2 x u hxu; exact absurd ha (h a)

/-- Un estado que contiene una estructura cerrada no vacía es válido: tiene un vivo en cada paso. -/
theorem valid_of_sec {g : GPathB} {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    (h : SecStruct g V R) {y : PathNodeId} (hy : V y) : g.isValid = true := by
  unfold isValid
  rw [List.all_eq_true]
  intro k hk
  obtain ⟨h0, h1⟩ := intRange_bounds hk
  obtain ⟨r, hr, hyr, _⟩ := h.pair (h.refl hy) k h0 (by omega)
  exact List.any_eq_true.mpr ⟨r, h.alive (h.dom hyr).2, by simp [hr]⟩

/-- **Una estructura cerrada, hecha de ramas de la entrada y anclada en el requisito, sobrevive al filtro y al
review.** -/
theorem struct_survives_filter {E : GPathB} {T : Int} {P0 : Assign → Prop} {r : NodeId} (hns : NoSelf E)
    (hndt : NoDegT E) (hcs : E.current_step = T) (hc : ∀ a, P0 a → CT E (pidOfAssign φ a))
    {R : PathNodeId → PathNodeId → Prop} {Tf : Trios} (S : PhStruct φ P0 T R Tf)
    (hanch : ∀ a s, P0 a → R s s → s.id.step = r.step → pidOfAssign φ a r.step = s → selOfAssign φ a r.step = r) :
    DownInv (fun y => R y y) R Tf T (E.filterAllOn [r]) := by
  obtain ⟨hrefl, hsymm, hsw23, hsw12, hsteps, hpair, htrio, hb2, hb3⟩ := S
  -- el rango de los pasos de la estructura
  have rng : ∀ {y w : PathNodeId}, R y w →
      (0 ≤ y.id.step ∧ y.id.step < E.current_step) ∧ (0 ≤ w.id.step ∧ w.id.step < E.current_step) := by
    intro y w h
    have h1 := hsteps y w h
    have h2 := hsteps w w (hrefl y w h).2
    rw [hcs]; exact ⟨h1, h2⟩
  -- la rama que realiza una pareja, llevada por la entrada
  have carr : ∀ {y w : PathNodeId}, R y w → ∃ a, CT E (pidOfAssign φ a) ∧ pidOfAssign φ a y.id.step = y ∧
      pidOfAssign φ a w.id.step = w := by
    intro y w h
    obtain ⟨a, ha, h1, h2⟩ := hb2 y w h
    exact ⟨a, hc a ha, h1, h2⟩
  -- los enlaces: un vecino en el paso anterior (siguiente) es padre (hijo) en el documento
  have linkP : ∀ {x s : PathNodeId} {n : PNodeB}, R x s → s.id.step = x.id.step - 1 → E.node? x = some n →
      s ∈ n.parents := by
    intro x s n h hs hn
    obtain ⟨a, hct, hx, hs'⟩ := carr h
    obtain ⟨⟨x0, x1⟩, ⟨s0, _⟩⟩ := rng h
    obtain ⟨n', hn', hp, _⟩ := hct.1.node x.id.step x0 x1
    rw [hx, hn] at hn'
    have e : n' = n := (Option.some.inj hn').symm
    have := hp (by omega)
    rw [← hs, hs', e] at this
    exact this
  have linkS : ∀ {x s : PathNodeId} {n : PNodeB}, R x s → s.id.step = x.id.step + 1 → E.node? x = some n →
      s ∈ n.sons := by
    intro x s n h hs hn
    obtain ⟨a, hct, hx, hs'⟩ := carr h
    obtain ⟨⟨x0, x1⟩, ⟨_, s1⟩⟩ := rng h
    obtain ⟨n', hn', _, hson⟩ := hct.1.node x.id.step x0 x1
    rw [hx, hn] at hn'
    have e : n' = n := (Option.some.inj hn').symm
    have := hson (by omega)
    rw [← hs, hs', e] at this
    exact this
  -- la estructura vive dentro de la entrada
  have hsec : SecStruct E (fun y => R y y) R := by
    refine ⟨fun {y} hy => ?_, fun hy => hy, fun h => hsymm _ _ h, fun h => hrefl _ _ h, fun {y w} h => ?_,
      fun {y w} h l l0 l1 => ?_, fun {y} hy => ?_, fun {x w n} h hne hn hx1 => ?_, fun {x w n} h hne hn hx1 => ?_⟩
    · obtain ⟨a, hct, h1, _⟩ := carr hy
      have := hct.1.alive y.id.step (rng hy).1.1 (rng hy).1.2
      rw [h1] at this; exact this
    · obtain ⟨a, hct, h1, h2⟩ := carr h
      have := hct.1.adj y.id.step w.id.step (rng h).1.1 (rng h).1.2 (rng h).2.1 (rng h).2.2
      rw [h1, h2] at this; exact this
    · obtain ⟨s, hs, h1, h2, _⟩ := hpair y w h l l0 (by rw [← hcs]; exact l1)
      exact ⟨s, hs, h1, h2⟩
    · obtain ⟨a, hct, h1, _⟩ := carr hy
      obtain ⟨n, hn, _, _⟩ := hct.1.node y.id.step (rng hy).1.1 (rng hy).1.2
      rw [h1] at hn
      refine ⟨n, hn, fun hpar => ?_, fun hstep => ?_⟩
      · have hk : 0 < y.id.step := by
          by_cases hk : 0 < y.id.step
          · exact hk
          · exfalso
            have e := congrArg PathNodeId.parent_id h1
            simp only [pidOfAssign, if_neg hk] at e
            rw [← e] at hpar
            simp at hpar
        obtain ⟨s, hs, h1', _, _⟩ := hpair y y hy (y.id.step - 1) (by omega) (by have := (rng hy).1.2; rw [hcs] at this; omega)
        exact ⟨s, linkP h1' hs hn, h1'⟩
      · obtain ⟨s, hs, h1', _, _⟩ := hpair y y hy (y.id.step + 1) (by have := (rng hy).1.1; omega)
          (by have := (rng hy).1.2; rw [hcs] at this hstep; omega)
        exact ⟨s, linkS h1' hs hn, h1'⟩
    · obtain ⟨s, hs, h1, h2, _⟩ := hpair x w h (x.id.step - 1) (by omega)
        (by have := (rng h).1.2; rw [hcs] at this; omega)
      exact ⟨s, linkP h1 hs hn, h1, hsymm _ _ h2⟩
    · obtain ⟨s, hs, h1, h2, _⟩ := hpair x w h (x.id.step + 1) (by have := (rng h).1.1; omega)
        (by rw [hcs] at hx1; exact hx1)
      exact ⟨s, linkS h1 hs hn, h1, hsymm _ _ h2⟩
  have hD : DownInv (fun y => R y y) R Tf T E := by
    refine ⟨hsec, hns, hcs, fun {a b c} hab hac hbc hf => ?_⟩
    apply Classical.byContradiction
    intro hn
    obtain ⟨d1, d2, d3⟩ := noDeg_TF hndt a b c hf
    obtain ⟨asg, ha, h1, h2, h3⟩ := hb3 a b c hab hac hbc d1 d2 d3 hn
    have hA := (hc asg ha).2.1 a.id.step b.id.step c.id.step (rng hab).1.1 (rng hab).1.2 (rng hab).2.1
      (rng hab).2.2 (rng hac).2.1 (rng hac).2.2
    rw [h1, h2, h3] at hA
    exact hA hf
  have hTG : TrioGood (fun y => R y y) R Tf T := by
    refine ⟨fun {a b} hab hne l l0 l1 => ?_, fun {a b c} hab hac hbc n1 n2 n3 hn l l0 l1 =>
      htrio a b c hab hac hbc n1 n2 n3 hn l l0 l1, fun {a b c} h1 h2 h3 hT => hsw23 a b c h1 h2 h3 hT,
      fun {a b c} h1 h2 h3 hT => hsw12 a b c h1 h2 h3 hT⟩
    obtain ⟨s, hs, h1, h2, hor⟩ := hpair a b hab l l0 l1
    refine ⟨s, hs, h1, h2, ?_⟩
    rcases hor with h | h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hagr : SecAgrees (fun y => R y y) r := by
    intro y hy hstep
    obtain ⟨a, ha, h1, _⟩ := hb2 y y hy
    have hP := hanch a y ha hy hstep (by rw [← hstep]; exact h1)
    have := congrArg PathNodeId.id h1
    rw [pid_id, hstep] at this
    rw [← this]; exact hP
  -- sobrevive al filtro y al review
  exact downInv_reviewOn (downInv_filterRequire hD hagr) hTG (fun h => hsymm _ _ h)

/-- **Exactitud tras el filtro ⟹ sin familias fantasma.** Si el estado filtrado, cuando es válido, es exacto, toda
estructura cerrada hecha de ramas de `P0` y anclada en el requisito es de ramas que lo cumplen: sobrevive dentro del
estado filtrado (y si el estado no es válido, no hay ninguna). -/
theorem phantomFree_of_exact_filter {E : GPathB} {T : Int} {P0 : Assign → Prop} {r : NodeId} (hns : NoSelf E)
    (hndt : NoDegT E) (hcs : E.current_step = T) (hc : ∀ a, P0 a → CT E (pidOfAssign φ a))
    (hsY : (E.filterAllOn [r]).isValid = true →
      Snd3 φ (fun a => P0 a ∧ selOfAssign φ a r.step = r) (E.filterAllOn [r])) :
    PhantomFree φ P0 (fun a => P0 a ∧ selOfAssign φ a r.step = r) T r.step := by
  intro R Tf hrefl hsymm hsw23 hsw12 hsteps hpair htrio hb2 hb3 hanch
  have hY := struct_survives_filter hns hndt hcs hc ⟨hrefl, hsymm, hsw23, hsw12, hsteps, hpair, htrio, hb2, hb3⟩
    (fun a s ha hs hst hp => (hanch a s ha hs hst hp).2)
  have ex : ∀ {y w : PathNodeId}, R y w → Snd3 φ (fun a => P0 a ∧ selOfAssign φ a r.step = r) (E.filterAllOn [r]) :=
    fun h => hsY (valid_of_sec hY.sec (hrefl _ _ h).1)
  refine ⟨fun y w h => (ex h).1 y w (hY.sec.adj h), fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
  exact (ex hxu).2 x u w (hY.sec.adj hxu) (hY.sec.adj hxw) (hY.sec.adj huw) nxu nxw nuw
    (fun hf => hn (hY.tri hxu hxw huw hf))

/-- **El filtro es exacto exactamente cuando no hay familias fantasma.** Con la entrada exacta (`Snd3` y la
completitud para `P0`) y el estado filtrado válido: sus parejas y sus triángulos sin prohibir son de ramas de `P0`
que cumplen el requisito si y solo si `PhantomFree`. -/
theorem snd3_filter_iff {E : GPathB} {T : Int} {P0 : Assign → Prop} {r : NodeId} (hE : SInvB E) (hns : NoSelf E)
    (hndt : NoDegT E) (hcs : E.current_step = T) (hvE : E.isValid = true) (hr : 1 ≤ r.step ∧ r.step < T)
    (hs : Snd3 φ P0 E) (hc : ∀ a, P0 a → CT E (pidOfAssign φ a)) (hvY : (E.filterAllOn [r]).isValid = true) :
    Snd3 φ (fun a => P0 a ∧ selOfAssign φ a r.step = r) (E.filterAllOn [r]) ↔
      PhantomFree φ P0 (fun a => P0 a ∧ selOfAssign φ a r.step = r) T r.step := by
  refine ⟨fun h => phantomFree_of_exact_filter hns hndt hcs hc (fun _ => h), fun hH => ?_⟩
  refine snd3_mono (snd3_filter hE hns hndt hcs hvE (by simp) (fun r' hr' => ?_) (fun r' hr' => ?_) hs hc hvY)
    (fun a ha => ⟨ha.1, ha.2 _ (List.mem_singleton_self _)⟩)
  · rw [List.mem_singleton] at hr'; subst hr'; exact hr
  · rw [List.mem_singleton] at hr'; subst hr'; exact hH

-- ============================================================
-- El UP
-- ============================================================

section Up

variable {Y : GPathB} {T : Int} {d : NodeId} {title : String} {P0 P : Assign → Prop}

/-- **Una estructura cerrada, hecha de ramas del remitente y anclada en la fila nueva, sobrevive al UP.** Vive
dentro de la fila recién añadida (antes de su review): sus objetos de nodos viejos, por la rama del remitente que los
realiza; los que tienen un nodo de la fila, por una rama que el ancla pone en la llegada y que la fila lleva entera
(`carried_addNode`). Sus triángulos sin prohibir no están entre los tríos que escribe el UP. Y sobrevive al review. -/
theorem struct_survives_up (hiY : SInvB Y) (hnsY : NoSelf Y) (hndtY : NoDegT Y) (htbY : TB Y)
    (hcs : Y.current_step = T) (hT : 1 ≤ T) (hvY : Y.isValid = true) (hds : d.step = T)
    (hc : ∀ a, P0 a → CT Y (pidOfAssign φ a))
    (hP : ∀ a, P a → ValidUpTo φ a (T + 1) ∧ selOfAssign φ a T = d)
    {R : PathNodeId → PathNodeId → Prop} {Tf : Trios} (S : PhStruct φ P0 (T + 1) R Tf)
    (hanch : ∀ a s, P0 a → R s s → s.id.step = T → pidOfAssign φ a T = s → P a) :
    DownInv (fun y => R y y) R Tf (T + 1) (Y.upOn d title (isProhibited φ)) := by
  obtain ⟨hrefl, hsymm, hsw23, hsw12, hsteps, hpair, htrio, hb2, hb3⟩ := S
  have hd : d.step = Y.current_step := by rw [hcs]; exact hds
  -- lo que hace falta para subir una rama de `P0 ∩ P` por la fila
  have bundle : ∀ a, P0 a → P a →
      pidOfAssign φ a Y.current_step ∈ Y.newRowIds d (isProhibited φ) ∧
      (0 < Y.current_step → pidOfAssign φ a (Y.current_step - 1) ∈ Y.rowParents d (pidOfAssign φ a Y.current_step)) := by
    intro a h0 hp
    have hct := hc a h0
    have hnpar : pidOfAssign φ a (T - 1) ∈ Y.newParents := by
      obtain ⟨n, hn, _, _⟩ := hct.1.node (T - 1) (by omega) (by rw [hcs]; omega)
      have hid := node?_id hn
      unfold newParents
      rw [if_pos (by rw [hcs]; omega)]
      refine List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨node?_mem hn, ?_⟩, hid⟩
      rw [hid, hcs]; simp [pid_step]
    have hshift : shiftPid (pidOfAssign φ a (T - 1)) d = pidOfAssign φ a T := by
      have := shift_pid φ a T (by omega)
      rw [(hP a hp).2] at this; exact this
    rw [hcs]
    refine ⟨List.mem_filter.mpr ⟨?_, ?_⟩, fun _ => List.mem_filter.mpr ⟨hnpar, by simp [hshift]⟩⟩
    · unfold shiftRowIds
      rw [if_pos (by rw [hcs]; omega)]
      exact (mem_dedupPids _ _).mpr (List.mem_map.mpr ⟨_, hnpar, hshift⟩)
    · simp [(hP a hp).1 T (by omega)]
  have cN : ∀ a, P0 a → P a → Carried (Y.addNode d title (isProhibited φ)) (pidOfAssign φ a) := fun a h0 hp =>
    carried_addNode (title := title) (hc a h0).1 (bundle a h0 hp).1 (bundle a h0 hp).2 (pid_step φ a _) hiY.below
      (pid_root φ a)
  have cA : ∀ a, P0 a → P a → CT (Y.upOn d title (isProhibited φ)) (pidOfAssign φ a) := fun a h0 hp =>
    ct_upOn (hc a h0) htbY (bundle a h0 hp).1 (bundle a h0 hp).2 (pid_step φ a _) hiY.below (pid_root φ a)
  have hcsN : (Y.addNode d title (isProhibited φ)).current_step = T + 1 := by
    show Y.current_step + 1 = T + 1; rw [hcs]
  have rng : ∀ {y w : PathNodeId}, R y w → (0 ≤ y.id.step ∧ y.id.step < T + 1) ∧ (0 ≤ w.id.step ∧ w.id.step < T + 1) :=
    fun h => ⟨hsteps _ _ h, hsteps _ _ (hrefl _ _ h).2⟩
  -- la rama que realiza una pareja: o la fila la lleva entera, o es de nodos viejos y la lleva el remitente
  have real : ∀ {y w : PathNodeId}, R y w → ∃ a, pidOfAssign φ a y.id.step = y ∧ pidOfAssign φ a w.id.step = w ∧
      (Carried (Y.addNode d title (isProhibited φ)) (pidOfAssign φ a) ∨
        (Carried Y (pidOfAssign φ a) ∧ y.id.step < T ∧ w.id.step < T)) := by
    intro y w h
    obtain ⟨a, ha, h1, h2⟩ := hb2 y w h
    by_cases hy : y.id.step = T
    · exact ⟨a, h1, h2, Or.inl (cN a ha (hanch a y ha (hrefl y w h).1 hy (by rw [← hy]; exact h1)))⟩
    · by_cases hw : w.id.step = T
      · exact ⟨a, h1, h2, Or.inl (cN a ha (hanch a w ha (hrefl y w h).2 hw (by rw [← hw]; exact h2)))⟩
      · have := rng h
        exact ⟨a, h1, h2, Or.inr ⟨(hc a ha).1, by omega, by omega⟩⟩
  have oldNode : ∀ {x : PathNodeId} {n0 : PNodeB}, x.id.step < T → Y.node? x = some n0 →
      (Y.addNode d title (isProhibited φ)).node? x = some (Y.withGained d (isProhibited φ) n0) := by
    intro x n0 hx hn0
    rw [node?_addNode_old (title := title) (forb := isProhibited φ) hd (by rw [hcs]; exact hx), hn0]; rfl
  have linkP : ∀ {x s : PathNodeId} {n : PNodeB}, R x s → s.id.step = x.id.step - 1 →
      (Y.addNode d title (isProhibited φ)).node? x = some n → s ∈ n.parents := by
    intro x s n h hs hn
    obtain ⟨a, hx, hs', hC | ⟨hC, hxT, _⟩⟩ := real h
    · obtain ⟨n', hn', hp, _⟩ := hC.node x.id.step (rng h).1.1 (by rw [hcsN]; exact (rng h).1.2)
      rw [hx, hn] at hn'
      have e : n' = n := (Option.some.inj hn').symm
      have := hp (by have := (rng h).2.1; omega)
      rw [← hs, hs', e] at this
      exact this
    · obtain ⟨n0, hn0, hp, _⟩ := hC.node x.id.step (rng h).1.1 (by rw [hcs]; exact hxT)
      rw [hx] at hn0
      have e := oldNode hxT hn0
      rw [hn] at e
      have e' : n = Y.withGained d (isProhibited φ) n0 := Option.some.inj e
      have := hp (by have := (rng h).2.1; omega)
      rw [← hs, hs'] at this
      rw [e']; exact this
  have linkS : ∀ {x s : PathNodeId} {n : PNodeB}, R x s → s.id.step = x.id.step + 1 →
      (Y.addNode d title (isProhibited φ)).node? x = some n → s ∈ n.sons := by
    intro x s n h hs hn
    obtain ⟨a, hx, hs', hC | ⟨hC, hxT, hsT⟩⟩ := real h
    · obtain ⟨n', hn', _, hson⟩ := hC.node x.id.step (rng h).1.1 (by rw [hcsN]; exact (rng h).1.2)
      rw [hx, hn] at hn'
      have e : n' = n := (Option.some.inj hn').symm
      have := hson (by rw [hcsN]; have := (rng h).2.2; omega)
      rw [← hs, hs', e] at this
      exact this
    · obtain ⟨n0, hn0, _, hson⟩ := hC.node x.id.step (rng h).1.1 (by rw [hcs]; exact hxT)
      rw [hx] at hn0
      have e := oldNode hxT hn0
      rw [hn] at e
      have e' : n = Y.withGained d (isProhibited φ) n0 := Option.some.inj e
      have := hson (by rw [hcs]; omega)
      rw [← hs, hs'] at this
      rw [e']; exact List.mem_append_left _ this
  -- la estructura vive dentro de la fila
  have hsec : SecStruct (Y.addNode d title (isProhibited φ)) (fun y => R y y) R := by
    refine ⟨fun {y} hy => ?_, fun hy => hy, fun h => hsymm _ _ h, fun h => hrefl _ _ h, fun {y w} h => ?_,
      fun {y w} h l l0 l1 => ?_, fun {y} hy => ?_, fun {x w n} h hne hn hx1 => ?_, fun {x w n} h hne hn hx1 => ?_⟩
    · obtain ⟨a, h1, _, hC | ⟨hC, hyT, _⟩⟩ := real hy
      · have := hC.alive y.id.step (rng hy).1.1 (by rw [hcsN]; exact (rng hy).1.2)
        rw [h1] at this; exact this
      · have := hC.alive y.id.step (rng hy).1.1 (by rw [hcs]; exact hyT)
        rw [h1] at this; exact List.mem_append_left _ this
    · obtain ⟨a, h1, h2, hC | ⟨hC, hyT, hwT⟩⟩ := real h
      · have := hC.adj y.id.step w.id.step (rng h).1.1 (by rw [hcsN]; exact (rng h).1.2) (rng h).2.1
          (by rw [hcsN]; exact (rng h).2.2)
        rw [h1, h2] at this; exact this
      · have := hC.adj y.id.step w.id.step (rng h).1.1 (by rw [hcs]; exact hyT) (rng h).2.1 (by rw [hcs]; exact hwT)
        rw [h1, h2] at this; exact adj_addNode_mono this
    · obtain ⟨s, hs, h1, h2, _⟩ := hpair y w h l l0 (by rw [← hcsN]; exact l1)
      exact ⟨s, hs, h1, h2⟩
    · -- el documento de `y` en la fila, y sus enlaces
      have hnode : ∃ n, (Y.addNode d title (isProhibited φ)).node? y = some n := by
        obtain ⟨a, h1, _, hC | ⟨hC, hyT, _⟩⟩ := real hy
        · obtain ⟨n, hn, _, _⟩ := hC.node y.id.step (rng hy).1.1 (by rw [hcsN]; exact (rng hy).1.2)
          rw [h1] at hn; exact ⟨n, hn⟩
        · obtain ⟨n0, hn0, _, _⟩ := hC.node y.id.step (rng hy).1.1 (by rw [hcs]; exact hyT)
          rw [h1] at hn0; exact ⟨_, oldNode hyT hn0⟩
      obtain ⟨n, hn⟩ := hnode
      refine ⟨n, hn, fun hpar => ?_, fun hstep => ?_⟩
      · have hk : 0 < y.id.step := by
          by_cases hk : 0 < y.id.step
          · exact hk
          · exfalso
            obtain ⟨a, h1, _, _⟩ := real hy
            have e := congrArg PathNodeId.parent_id h1
            simp only [pidOfAssign, if_neg hk] at e
            rw [← e] at hpar
            simp at hpar
        obtain ⟨s, hs, h1', _, _⟩ := hpair y y hy (y.id.step - 1) (by omega) (by have := (rng hy).1.2; omega)
        exact ⟨s, linkP h1' hs hn, h1'⟩
      · obtain ⟨s, hs, h1', _, _⟩ := hpair y y hy (y.id.step + 1) (by have := (rng hy).1.1; omega)
          (by have := (rng hy).1.2; rw [hcsN] at hstep; omega)
        exact ⟨s, linkS h1' hs hn, h1'⟩
    · obtain ⟨s, hs, h1, h2, _⟩ := hpair x w h (x.id.step - 1) (by omega) (by have := (rng h).1.2; omega)
      exact ⟨s, linkP h1 hs hn, h1, hsymm _ _ h2⟩
    · obtain ⟨s, hs, h1, h2, _⟩ := hpair x w h (x.id.step + 1) (by have := (rng h).1.1; omega)
        (by rw [hcsN] at hx1; exact hx1)
      exact ⟨s, linkS h1 hs hn, h1, hsymm _ _ h2⟩
  -- el estado antes del review: la fila con los tríos del remitente y los del UP
  have hX : Y.upOn d title (isProhibited φ) =
      (((Y.addNode d title (isProhibited φ)).setT Y.trios).upForbidRow (Y.newRowIds d (isProhibited φ))).reviewOn := by
    unfold upOn; rw [if_pos hvY]
  obtain ⟨T', hT'⟩ := upForbidRow_eq ((Y.addNode d title (isProhibited φ)).setT Y.trios)
    (Y.newRowIds d (isProhibited φ))
  have hns0 : NoSelf ((Y.addNode d title (isProhibited φ)).setT Y.trios) := noSelf_addNode (title := title) hnsY
  have hndt0 := noDegT_upForbidRow (d := d) (title := title) (forb := isProhibited φ) hns0 hndtY
  have hD : DownInv (fun y => R y y) R Tf (T + 1)
      (((Y.addNode d title (isProhibited φ)).setT Y.trios).upForbidRow (Y.newRowIds d (isProhibited φ))) := by
    refine ⟨by rw [hT']; exact secStruct_setT' (secStruct_setT' hsec Y.trios) T', by rw [hT']; exact hns0,
      by rw [hT']; exact hcsN, fun {a b c} hab hac hbc hf => ?_⟩
    apply Classical.byContradiction
    intro hn
    obtain ⟨d1, d2, d3⟩ := noDeg_TF hndt0 a b c hf
    obtain ⟨asg, ha, h1, h2, h3⟩ := hb3 a b c hab hac hbc d1 d2 d3 hn
    by_cases htop : a.id.step = T ∨ b.id.step = T ∨ c.id.step = T
    · -- con un nodo de la fila, la rama es de la llegada y esquiva sus tríos
      have hp : P asg := by
        rcases htop with h | h | h
        · exact hanch asg a ha (hrefl a b hab).1 h (by rw [← h]; exact h1)
        · exact hanch asg b ha (hrefl a b hab).2 h (by rw [← h]; exact h2)
        · exact hanch asg c ha (hrefl a c hac).2 h (by rw [← h]; exact h3)
      have hct := cA asg ha hp
      have hcsA : (Y.upOn d title (isProhibited φ)).current_step = T + 1 := by
        rw [(sub_upOn_addNode (d := d) (title := title) (forb := isProhibited φ) hvY).step]; exact hcsN
      have hadj := hct.1.adj a.id.step b.id.step (rng hab).1.1 (by rw [hcsA]; exact (rng hab).1.2) (rng hab).2.1
        (by rw [hcsA]; exact (rng hab).2.2)
      rw [h1, h2] at hadj
      have hA := hct.2.1 a.id.step b.id.step c.id.step (rng hab).1.1 (by rw [hcsA]; exact (rng hab).1.2)
        (rng hab).2.1 (by rw [hcsA]; exact (rng hab).2.2) (rng hac).2.1 (by rw [hcsA]; exact (rng hac).2.2)
      rw [h1, h2, h3] at hA
      rw [hX] at hA hadj
      exact hA (tF_mono (trios_grow_reviewOn _) hadj hf)
    · -- de nodos viejos: el trío sería del remitente (los del UP llevan un nodo de la fila)
      have hold : a.id.step < T ∧ b.id.step < T ∧ c.id.step < T := by
        have := rng hab; have := rng hac; omega
      have hct := hc asg ha
      have hd' := hf.2
      unfold deadTrio at hd'
      rw [Bool.and_eq_true] at hd'
      obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd'.2
      unfold upForbidRow at ht
      rcases mem_addTrios _ _ _ t ht with hY | hU
      · have hadj := hct.1.adj a.id.step b.id.step (rng hab).1.1 (by rw [hcs]; exact hold.1) (rng hab).2.1
          (by rw [hcs]; exact hold.2.1)
        rw [h1, h2] at hadj
        have hA := hct.2.1 a.id.step b.id.step c.id.step (rng hab).1.1 (by rw [hcs]; exact hold.1) (rng hab).2.1
          (by rw [hcs]; exact hold.2.1) (rng hac).2.1 (by rw [hcs]; exact hold.2.2)
        rw [h1, h2, h3] at hA
        exact hA ⟨d1, by
          unfold deadTrio; rw [Bool.and_eq_true]
          exact ⟨hasEdge_of_adj hadj d1, List.any_eq_true.mpr ⟨t, hY, hti⟩⟩⟩
      · obtain ⟨n, hnm, htn⟩ := List.mem_flatMap.mp hU
        unfold upForbidTodo at htn
        obtain ⟨wr, _, rfl⟩ := List.mem_map.mp htn
        have hns := newRow_step hd hnm
        rw [hcs] at hns
        obtain ⟨c1, _, _⟩ := trioIs_mem hti
        simp only at c1
        rcases c1 with e | e | e
        · rw [e] at hns; omega
        · rw [e] at hns; omega
        · rw [e] at hns; omega
  have hTG : TrioGood (fun y => R y y) R Tf (T + 1) := by
    refine ⟨fun {a b} hab hne l l0 l1 => ?_, fun {a b c} hab hac hbc n1 n2 n3 hn l l0 l1 =>
      htrio a b c hab hac hbc n1 n2 n3 hn l l0 l1, fun {a b c} h1 h2 h3 hT => hsw23 a b c h1 h2 h3 hT,
      fun {a b c} h1 h2 h3 hT => hsw12 a b c h1 h2 h3 hT⟩
    obtain ⟨s, hs, h1, h2, hor⟩ := hpair a b hab l l0 l1
    refine ⟨s, hs, h1, h2, ?_⟩
    rcases hor with h | h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rw [hX]; exact downInv_reviewOn hD hTG (fun h => hsymm _ _ h)

/-- **Exactitud tras el UP ⟹ sin familias fantasma.** -/
theorem phantomFree_of_exact_up (hiY : SInvB Y) (hnsY : NoSelf Y) (hndtY : NoDegT Y) (htbY : TB Y)
    (hcs : Y.current_step = T) (hT : 1 ≤ T) (hvY : Y.isValid = true) (hds : d.step = T)
    (hc : ∀ a, P0 a → CT Y (pidOfAssign φ a))
    (hP : ∀ a, P a → ValidUpTo φ a (T + 1) ∧ selOfAssign φ a T = d)
    (hsA : (Y.upOn d title (isProhibited φ)).isValid = true → Snd3 φ P (Y.upOn d title (isProhibited φ))) :
    PhantomFree φ P0 P (T + 1) T := by
  intro R Tf hrefl hsymm hsw23 hsw12 hsteps hpair htrio hb2 hb3 hanch
  have hA := struct_survives_up (title := title) hiY hnsY hndtY htbY hcs hT hvY hds hc hP
    ⟨hrefl, hsymm, hsw23, hsw12, hsteps, hpair, htrio, hb2, hb3⟩ hanch
  have ex : ∀ {y w : PathNodeId}, R y w → Snd3 φ P (Y.upOn d title (isProhibited φ)) :=
    fun h => hsA (valid_of_sec hA.sec (hrefl _ _ h).1)
  refine ⟨fun y w h => (ex h).1 y w (hA.sec.adj h), fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
  exact (ex hxu).2 x u w (hA.sec.adj hxu) (hA.sec.adj hxw) (hA.sec.adj huw) nxu nxw nuw
    (fun hf => hn (hA.tri hxu hxw huw hf))

end Up

-- ============================================================
-- La equivalencia en la máquina
-- ============================================================

/-- La contabilidad de las líneas, que no depende de ninguna hipótesis. -/
theorem lInvBase_steps (φ : Cnf) :
    ∀ n : Nat, LInvP (fun _ => True) φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) :=
  lInvP_steps ⟨fun _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ => trivial⟩
    (let h := lInvX_init φ; ⟨h.on, h.nodup, h.keys, h.inv, h.ndt, h.docs, fun _ _ => trivial⟩)
    (fun _ _ _ _ _ _ => trivial)

/-- La completitud de las líneas, sin hipótesis. -/
theorem compLine_base (hb : Bounded φ) (n : Nat) :
    CompLine φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
  have h := lInvBase_steps φ n
  intro kv hkv a ha
  have hn : (n : Int) < stepCount φ := by
    have hk := h.keys kv hkv
    rw [show (n : Int) + 1 - 1 = n by omega] at hk
    by_cases hc : stepCount φ ≤ (n : Int)
    · unfold mapNodes at hk
      rw [if_neg (by omega), if_pos hc] at hk
      exact absurd hk List.not_mem_nil
    · omega
  obtain ⟨_, g, hf, hct⟩ := comp_line hb a n hn ha.1
  have hkey : selOfAssign φ a n = kv.1 := by have := ha.2; rw [show (n : Int) + 1 - 1 = n by omega] at this; exact this
  have hl := lookup_of_mem h.nodup hkv
  unfold lookup at hl
  rw [hkey] at hf
  rw [hf] at hl
  simp only [Option.map_some, Option.some.injEq] at hl
  rw [← hl]; exact hct

/-- **La máquina es exacta**: en cada línea, cada entrada, cada remitente filtrado válido y cada llegada válida
tienen sus parejas de vecinos y sus triángulos sin prohibir en ramas de sus soluciones. Son los estados que mide
`probe_exact3.jl` (entradas, `flt`, `arr`). -/
def MachineExact (φ : Cnf) : Prop :=
  ∀ n : Nat, ∀ kv ∈ stepsM .on φ n (initM .on φ),
    Snd3 φ (SolE φ ((n : Int) + 1) kv.1) kv.2 ∧
    ∀ d ∈ sonsOfMap φ kv.1,
      ((kv.2.filterAllOn (reqOf φ d)).isValid = true →
        Snd3 φ (fun a => SolE φ ((n : Int) + 1) kv.1 a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r)
          (kv.2.filterAllOn (reqOf φ d))) ∧
      ((arrOn φ kv d).isValid = true →
        Snd3 φ (fun a => SolE φ ((n : Int) + 1 + 1) d a ∧ selOfAssign φ a ((n : Int) + 1 - 1) = kv.1) (arrOn φ kv d))

/-- **La máquina es exacta exactamente en las fórmulas sin familias fantasma.** El lado derecho solo habla de las
soluciones de los prefijos de `φ`. -/
theorem machineExact_iff (hb : Bounded φ) : MachineExact φ ↔ ∀ T : Int, 1 ≤ T → PhantomAt φ T := by
  constructor
  · -- exacta ⟹ sin familias fantasma
    intro hM T hT k d hk hd
    obtain ⟨n, rfl⟩ : ∃ n : Nat, T = (n : Int) + 1 := ⟨(T - 1).toNat, by omega⟩
    have hk' : k ∈ mapNodes φ n := by rw [show (n : Int) + 1 - 1 = n by omega] at hk; exact hk
    have base := lInvBase_steps φ n
    by_cases hent : ∃ kv ∈ stepsM .on φ n (initM .on φ), kv.1 = k
    · obtain ⟨kv, hkv, rfl⟩ := hent
      have hE := base.on kv hkv
      have hok := hE.1
      have hi := base.inv kv hkv
      have comp := compLine_base hb n kv hkv
      obtain ⟨_, hops⟩ := hM n kv hkv
      obtain ⟨hY, hA⟩ := hops d hd
      refine ⟨fun r hr => ?_, ?_⟩
      · have hreq : reqOf φ d = [r] := by
          have hlen := reqOf_length_le_one φ d
          cases hq : reqOf φ d with
          | nil => rw [hq] at hr; cases hr
          | cons x xs =>
            rw [hq] at hlen hr
            have hxs : xs = [] := by
              cases xs with
              | nil => rfl
              | cons _ _ => simp at hlen
            subst hxs
            rw [List.mem_singleton] at hr
            rw [hr]
        rw [hreq] at hY
        exact phantomFree_of_exact_filter hE.2.1 (base.ndt kv hkv) hok.step comp
          (fun hv => snd3_mono (hY hv) (fun a ha => ⟨ha.1, ha.2 r (List.mem_singleton_self _)⟩))
      · by_cases hvY : (kv.2.filterAllOn (reqOf φ d)).isValid = true
        · have hds : d.step = (n : Int) + 1 := by rw [sonsOfMap_step φ kv.1 d hd, hok.key]; omega
          exact phantomFree_of_exact_up (title := "") (sInvB_filterAllOn hi _) (noSelf_filterAllOn hE.2.1 _)
            (noDegT_filterAllOn hE.2.1 (base.ndt kv hkv) _) (tb_filterAllOn hE.2.2 _)
            ((step_filterAllOn kv.2 _).trans hok.step) (by omega) hvY hds (comp_filter comp)
            (fun a ha => ⟨ha.1.1, by have := ha.1.2; rw [show (n : Int) + 1 + 1 - 1 = (n : Int) + 1 by omega] at this; exact this⟩)
            hA
        · exact phantomFree_of_empty (fun a ha => hvY (isValid_of_carried (comp_filter comp a ha).1))
    · -- ninguna entrada con esa clave: ninguna solución del prefijo la elige
      have hempty : ∀ a, ¬ SolE φ ((n : Int) + 1) k a := by
        intro a ha
        have hn : (n : Int) < stepCount φ := by
          by_cases hc : stepCount φ ≤ (n : Int)
          · unfold mapNodes at hk'
            rw [if_neg (by omega), if_pos hc] at hk'
            exact absurd hk' List.not_mem_nil
          · omega
        obtain ⟨_, g, hf, _⟩ := comp_line hb a n hn ha.1
        have hkey : selOfAssign φ a n = k := by
          have := ha.2; rw [show (n : Int) + 1 - 1 = n by omega] at this; exact this
        exact hent ⟨_, List.mem_of_find?_eq_some hf, hkey⟩
      exact ⟨fun r _ => phantomFree_of_empty hempty, phantomFree_of_empty (fun a ha => hempty a ha.1)⟩
  · -- sin familias fantasma ⟹ exacta
    intro H n kv hkv
    have hl := lInvS3_steps hb n (fun T h1 _ => H T h1)
    refine ⟨hl.snd kv hkv, fun d hd => ?_⟩
    have hent := hl.on kv hkv
    have hok := hent.1
    have hi := hl.inv kv hkv
    have hcomp := compLine_steps hb (lInvS_of_s3 hl) kv hkv
    have hdk : d.step = kv.2.current_step := by rw [sonsOfMap_step φ kv.1 d hd, hok.key, hok.step]; omega
    have hdm : d ∈ mapNodes φ ((n : Int) + 1) := by
      have hk' : kv.1 ∈ mapNodes φ kv.1.step := by rw [hok.key]; exact hl.keys kv hkv
      have := sonsOfMap_subset φ kv.1 hk' d hd
      rw [hok.key, show (n : Int) + 1 - 1 + 1 = (n : Int) + 1 by omega] at this
      exact this
    obtain ⟨hF, hU⟩ := H ((n : Int) + 1) (by omega) kv.1 d (hl.keys kv hkv) hd
    have sY : (kv.2.filterAllOn (reqOf φ d)).isValid = true →
        Snd3 φ (fun a => SolE φ ((n : Int) + 1) kv.1 a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r)
          (kv.2.filterAllOn (reqOf φ d)) := fun hvY =>
      snd3_filter hi hent.2.1 (hl.ndt kv hkv) hok.step hok.valid (reqOf_length_le_one φ d)
        (fun r hr => by have := reqOf_range hb r hr; rw [hdk, hok.step] at this; exact this) hF
        (hl.snd kv hkv) hcomp hvY
    refine ⟨sY, fun hvA => ?_⟩
    have hvY : (kv.2.filterAllOn (reqOf φ d)).isValid = true :=
      valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hvA
    exact snd3_upOn hb (sInvB_filterAllOn hi _) (noSelf_filterAllOn hent.2.1 _)
      (noDegT_filterAllOn hent.2.1 (hl.ndt kv hkv) _) ((step_filterAllOn kv.2 _).trans hok.step) (by omega) hvY
      (docsAlive_filterAllOn (hl.docs kv hkv) (reqOf φ d) hvY) hd hdm hU (sY hvY) (comp_filter hcomp) hvA

end GPathB

end AbsSatBingo.Model
