-- lean_project/AbsSat/GraphPath/Model/OneStep.lean
import AbsSat.GraphPath.Model.PairHelly
import AbsSat.GraphPath.Model.OwnersInvariants

/-!
# `PairHelly` paso a paso (informe v187, piezas 1 y 2)

`row-degree onestep` (86 pines, 60.734 extensiones): tras `cleanPair`, todo tramo se alarga un paso
—hacia arriba con un hijo de su extremo superior, hacia abajo con un padre del inferior— con un nodo
que todos sus miembros poseen; en el 88 % hay un solo candidato, y en el resto casi siempre dos.

* **Pieza 1** (`segGood_of_oneStep`): si todo tramo se alarga un paso en cada dirección, repitiendo se
  llega a un tramo de `0` a `current_step - 1`, y su nodo en cada paso es la entrada común del tramo de
  partida: `SegGood`. De ahí `PairHelly` (`pairHelly_of_oneStep`), sin pasar por `SegThroughPin`.
* **Pieza 2** (`helly_two`, `extUp_of_two`, `extDown_of_two`): Helly con uno o dos candidatos es un
  lema de dos elementos. Con él, alargar un paso se reduce a que **cada dos miembros compartan un
  candidato** —el «triángulo con el extremo», medido sin fallos— cuando hay como mucho dos candidatos.
-/

namespace AbsSat.GraphPath.Model.OneStep

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.Threaded (OwnSymmetric)
open AbsSat.GraphPath.Model.TopGoodUp (SegGood)
open AbsSat.GraphPath.Model.Extendable (PartialChain)
open AbsSat.GraphPath.Model.PairHelly (PairHelly)

-- ============================================================
-- Tramos y extensiones de un paso
-- ============================================================

/-- Un tramo: cadena de `lo` a `hi` cuyos miembros se poseen dos a dos (la hipótesis de `SegGood`). -/
def Seg (C : GPathM) (sel : Int → PathNodeId) (lo hi : Int) : Prop :=
  PartialChain C sel lo hi ∧
    ∀ i j, lo ≤ i → lo ≤ j → i ≤ hi → j ≤ hi → i ≠ j →
      ∀ nj, C.node? (sel j) = some nj → sel i ∈ nj.owners

/-- `r` alarga el tramo un paso hacia arriba: nodo vivo del paso siguiente, hijo del extremo, en la
tabla de todo miembro y con todo miembro en su tabla. -/
def ExtUp (C : GPathM) (sel : Int → PathNodeId) (lo hi : Int) (r : PathNodeId) : Prop :=
  (C.node? r).isSome ∧ r.id.step = hi + 1 ∧ sel hi ∈ ((C.node? r).map PNodeM.parents).getD [] ∧
    (∀ j, lo ≤ j → j ≤ hi → ∀ nj, C.node? (sel j) = some nj → r ∈ nj.owners) ∧
    (∀ nr, C.node? r = some nr → ∀ j, lo ≤ j → j ≤ hi → sel j ∈ nr.owners)

/-- `p` alarga el tramo un paso hacia abajo: nodo vivo del paso anterior, padre del extremo. -/
def ExtDown (C : GPathM) (sel : Int → PathNodeId) (lo hi : Int) (p : PathNodeId) : Prop :=
  (C.node? p).isSome ∧ p.id.step = lo - 1 ∧ p ∈ ((C.node? (sel lo)).map PNodeM.parents).getD [] ∧
    (∀ j, lo ≤ j → j ≤ hi → ∀ nj, C.node? (sel j) = some nj → p ∈ nj.owners) ∧
    (∀ np, C.node? p = some np → ∀ j, lo ≤ j → j ≤ hi → sel j ∈ np.owners)

/-- **Todo tramo se alarga un paso hacia arriba.** -/
def OneStepUp (C : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi + 1 ≤ C.current_step - 1 →
    Seg C sel lo hi → ∃ r, ExtUp C sel lo hi r

/-- **Todo tramo se alarga un paso hacia abajo.** -/
def OneStepDown (C : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 1 ≤ lo → lo ≤ hi → hi ≤ C.current_step - 1 →
    Seg C sel lo hi → ∃ p, ExtDown C sel lo hi p

/-- La elección `sel` con `r` en el paso `k`. -/
def upd (sel : Int → PathNodeId) (k : Int) (r : PathNodeId) : Int → PathNodeId :=
  fun i => if i = k then r else sel i

theorem upd_of_ne (sel : Int → PathNodeId) (k : Int) (r : PathNodeId) (i : Int) (h : i ≠ k) :
    upd sel k r i = sel i := by simp [upd, h]

theorem upd_self (sel : Int → PathNodeId) (k : Int) (r : PathNodeId) : upd sel k r k = r := by
  simp [upd]

-- ============================================================
-- Pieza 1: un paso más sigue siendo un tramo
-- ============================================================

theorem seg_up (C : GPathM) (sel : Int → PathNodeId) (lo hi : Int) (r : PathNodeId)
    (h : Seg C sel lo hi) (he : ExtUp C sel lo hi r) : Seg C (upd sel (hi + 1) r) lo (hi + 1) := by
  obtain ⟨⟨hnode, hlink⟩, hown⟩ := h
  obtain ⟨hrn, hrs, hrp, hr1, hr2⟩ := he
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hlo hhi
    by_cases hk : i = hi + 1
    · rw [hk, upd_self]; exact ⟨hrn, hrs⟩
    · rw [upd_of_ne _ _ _ _ hk]; exact hnode i hlo (by omega)
  · intro i hlo hhi
    by_cases hk : i = hi
    · rw [hk, upd_of_ne sel (hi + 1) r hi (by omega), upd_self sel (hi + 1) r]; exact hrp
    · rw [upd_of_ne sel (hi + 1) r i (by omega), upd_of_ne sel (hi + 1) r (i + 1) (by omega)]
      exact hlink i hlo (by omega)
  · intro i j hli hlj hi' hj' hij nj hnj
    by_cases hjk : j = hi + 1
    · rw [hjk, upd_self] at hnj
      rw [upd_of_ne _ _ _ _ (by omega)]
      exact hr2 nj hnj i hli (by omega)
    · rw [upd_of_ne _ _ _ _ hjk] at hnj
      by_cases hik : i = hi + 1
      · rw [hik, upd_self]; exact hr1 j hlj (by omega) nj hnj
      · rw [upd_of_ne _ _ _ _ hik]; exact hown i j hli hlj (by omega) (by omega) hij nj hnj

theorem seg_down (C : GPathM) (sel : Int → PathNodeId) (lo hi : Int) (p : PathNodeId)
    (h : Seg C sel lo hi) (he : ExtDown C sel lo hi p) : Seg C (upd sel (lo - 1) p) (lo - 1) hi := by
  obtain ⟨⟨hnode, hlink⟩, hown⟩ := h
  obtain ⟨hpn, hps, hpp, hp1, hp2⟩ := he
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hlo hhi
    by_cases hk : i = lo - 1
    · rw [hk, upd_self]; exact ⟨hpn, hps⟩
    · rw [upd_of_ne _ _ _ _ hk]; exact hnode i (by omega) hhi
  · intro i hlo hhi
    by_cases hk : i = lo - 1
    · rw [hk, upd_self sel (lo - 1) p, show lo - 1 + 1 = lo by omega,
        upd_of_ne sel (lo - 1) p lo (by omega)]; exact hpp
    · rw [upd_of_ne sel (lo - 1) p i hk, upd_of_ne sel (lo - 1) p (i + 1) (by omega)]
      exact hlink i (by omega) hhi
  · intro i j hli hlj hi' hj' hij nj hnj
    by_cases hjk : j = lo - 1
    · rw [hjk, upd_self] at hnj
      rw [upd_of_ne _ _ _ _ (by omega)]
      exact hp2 nj hnj i (by omega) hi'
    · rw [upd_of_ne _ _ _ _ hjk] at hnj
      by_cases hik : i = lo - 1
      · rw [hik, upd_self]; exact hp1 j (by omega) hj' nj hnj
      · rw [upd_of_ne _ _ _ _ hik]; exact hown i j (by omega) (by omega) hi' hj' hij nj hnj

/-- Alargando hacia arriba hasta el último paso. -/
theorem extend_up (C : GPathM) (hU : OneStepUp C) :
    ∀ (n : Nat) (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi ≤ C.current_step - 1 →
      C.current_step - 1 - hi = n → Seg C sel lo hi →
      ∃ s, Seg C s lo (C.current_step - 1) ∧ ∀ j, lo ≤ j → j ≤ hi → s j = sel j := by
  intro n
  induction n with
  | zero =>
    intro sel lo hi _ _ _ hn h
    have : hi = C.current_step - 1 := by omega
    subst this
    exact ⟨sel, h, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro sel lo hi hlo hlh hhi hn h
    obtain ⟨r, hr⟩ := hU sel lo hi hlo hlh (by omega) h
    obtain ⟨s, hs, hagree⟩ := ih (upd sel (hi + 1) r) lo (hi + 1) hlo (by omega) (by omega) (by omega)
      (seg_up C sel lo hi r h hr)
    exact ⟨s, hs, fun j hj1 hj2 => by rw [hagree j hj1 (by omega), upd_of_ne _ _ _ _ (by omega)]⟩

/-- Alargando hacia abajo hasta el paso 0. -/
theorem extend_down (C : GPathM) (hD : OneStepDown C) :
    ∀ (n : Nat) (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi ≤ C.current_step - 1 →
      lo = n → Seg C sel lo hi →
      ∃ s, Seg C s 0 hi ∧ ∀ j, lo ≤ j → j ≤ hi → s j = sel j := by
  intro n
  induction n with
  | zero =>
    intro sel lo hi _ _ _ hn h
    have : lo = 0 := by omega
    subst this
    exact ⟨sel, h, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro sel lo hi hlo hlh hhi hn h
    obtain ⟨p, hp⟩ := hD sel lo hi (by omega) hlh hhi h
    obtain ⟨s, hs, hagree⟩ := ih (upd sel (lo - 1) p) (lo - 1) hi (by omega) (by omega) hhi (by omega)
      (seg_down C sel lo hi p h hp)
    exact ⟨s, hs, fun j hj1 hj2 => by rw [hagree j (by omega) hj2, upd_of_ne _ _ _ _ (by omega)]⟩

/-- **Pieza 1: si todo tramo se alarga un paso en cada dirección, vale `SegGood`.** El tramo se alarga
hasta cubrir todos los pasos; su nodo en cada paso lo poseen todos los miembros del de partida. -/
theorem segGood_of_oneStep (C : GPathM) (hU : OneStepUp C) (hD : OneStepDown C) : SegGood C := by
  intro sel lo hi hlo hlh hhi hpc hpo i hi0 hi1 hout
  have h0 : Seg C sel lo hi := ⟨hpc, hpo⟩
  obtain ⟨s1, hs1, ha1⟩ := extend_up C hU _ sel lo hi hlo hlh hhi
    (Int.toNat_of_nonneg (by omega : (0:Int) ≤ C.current_step - 1 - hi)).symm h0
  obtain ⟨s, hs, ha⟩ := extend_down C hD _ s1 lo (C.current_step - 1) hlo (by omega) (Int.le_refl _)
    (Int.toNat_of_nonneg hlo).symm hs1
  refine ⟨s i, (hs.1.1 i hi0 hi1).2, ?_⟩
  intro j hj0 hj1 nj hnj
  have hsj : s j = sel j := by rw [ha j hj0 (by omega), ha1 j hj0 hj1]
  rw [← hsj] at hnj
  have hij : i ≠ j := by omega
  exact hs.2 i j hi0 (by omega) hi1 (by omega) hij nj hnj

/-- **Y por tanto `PairHelly`**, sobre el estado tras la limpieza con parejas. -/
theorem pairHelly_of_oneStep (C : GPathM) (hU : OneStepUp C) (hD : OneStepDown C) : PairHelly C :=
  fun _ _ => segGood_of_oneStep C hU hD

/-- info: 'AbsSat.GraphPath.Model.OneStep.pairHelly_of_oneStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairHelly_of_oneStep

-- ============================================================
-- Pieza 2: Helly con uno o dos candidatos
-- ============================================================

/-- En un dominio de dos elementos, dos cosas distintas de un tercero son iguales. -/
theorem two_elim {α : Type} (a b c x y : α) (hc : c = a ∨ c = b) (hx : x = a ∨ x = b)
    (hy : y = a ∨ y = b) (hxc : x ≠ c) (hyc : y ≠ c) : y = x := by
  rcases hc with hc | hc <;> rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact absurd (hx.trans hc.symm) hxc
  · exact absurd (hx.trans hc.symm) hxc
  · exact absurd (hy.trans hc.symm) hyc
  · exact hy.trans hx.symm
  · exact hy.trans hx.symm
  · exact absurd (hy.trans hc.symm) hyc
  · exact absurd (hx.trans hc.symm) hxc
  · exact absurd (hx.trans hc.symm) hxc

/-- Si no todos cumplen, alguno no cumple (sin lógica clásica: la lista es finita). -/
theorem exists_of_all_false {ι : Type} (J : List ι) (f : ι → Bool) (h : J.all f = false) :
    ∃ j ∈ J, f j = false := by
  induction J with
  | nil => simp at h
  | cons j rest ih =>
    cases hj : f j with
    | false => exact ⟨j, List.mem_cons_self, hj⟩
    | true =>
      simp only [List.all_cons, hj, Bool.true_and] at h
      obtain ⟨k, hk, hkf⟩ := ih h
      exact ⟨k, List.mem_cons_of_mem _ hk, hkf⟩

/-- **Helly de dos elementos.** Una familia no vacía (indexada por una lista) de subconjuntos de un
dominio `Q` con como mucho dos elementos (`a`, `b`), que se cortan dos a dos dentro de `Q`, tiene un
elemento común en `Q`. -/
theorem helly_two {ι α : Type} (J : List ι) (P : ι → α → Bool) (Q : α → Prop) (a b : α)
    (hab : ∀ x, Q x → x = a ∨ x = b) (j0 : ι) (hj0 : j0 ∈ J)
    (hpair : ∀ j ∈ J, ∀ k ∈ J, ∃ x, Q x ∧ P j x = true ∧ P k x = true) :
    ∃ x, Q x ∧ ∀ j ∈ J, P j x = true := by
  obtain ⟨c, hQc, _, _⟩ := hpair j0 hj0 j0 hj0
  cases hall : J.all (fun j => P j c) with
  | true => exact ⟨c, hQc, fun j hj => List.all_eq_true.mp hall j hj⟩
  | false =>
    obtain ⟨j1, hj1, hnc⟩ : ∃ j1 ∈ J, P j1 c = false := exists_of_all_false J _ hall
    -- every witness of a pair with `j1` avoids `c`, so it is the other element of the domain
    have hne : ∀ x, P j1 x = true → x ≠ c := fun x hx he => by rw [he, hnc] at hx; exact absurd hx (by decide)
    obtain ⟨x, hQx, hx1, _⟩ := hpair j1 hj1 j1 hj1
    refine ⟨x, hQx, fun k hk => ?_⟩
    obtain ⟨y, hQy, hy1, hyk⟩ := hpair j1 hj1 k hk
    have hxy : y = x := two_elim a b c x y (hab c hQc) (hab x hQx) (hab y hQy) (hne x hx1) (hne y hy1)
    rw [← hxy]; exact hyk

/-- Posesión como booleano. -/
def ownsB (C : GPathM) (u r : PathNodeId) : Bool :=
  match C.node? u with
  | some n => n.owners.contains r
  | none => false

theorem ownsB_of (C : GPathM) (u r : PathNodeId) (nu : PNodeM) (hu : C.node? u = some nu) :
    ownsB C u r = true ↔ r ∈ nu.owners := by
  simp [ownsB, hu]

/-- Los candidatos de arriba: nodos vivos del paso siguiente con el extremo como padre. -/
def IsCandUp (C : GPathM) (sel : Int → PathNodeId) (hi : Int) (r : PathNodeId) : Prop :=
  (C.node? r).isSome ∧ r.id.step = hi + 1 ∧ sel hi ∈ ((C.node? r).map PNodeM.parents).getD []

/-- Los de abajo: nodos vivos del paso anterior entre los padres del extremo inferior. -/
def IsCandDown (C : GPathM) (sel : Int → PathNodeId) (lo : Int) (p : PathNodeId) : Prop :=
  (C.node? p).isSome ∧ p.id.step = lo - 1 ∧ p ∈ ((C.node? (sel lo)).map PNodeM.parents).getD []

/-- **El triángulo con el extremo, hacia arriba**: cada dos miembros comparten un candidato. -/
def TriTopUp (C : GPathM) (sel : Int → PathNodeId) (lo hi : Int) : Prop :=
  ∀ j, lo ≤ j → j ≤ hi → ∀ k, lo ≤ k → k ≤ hi →
    ∃ r, IsCandUp C sel hi r ∧ ownsB C (sel j) r = true ∧ ownsB C (sel k) r = true

/-- Hacia abajo. -/
def TriTopDown (C : GPathM) (sel : Int → PathNodeId) (lo hi : Int) : Prop :=
  ∀ j, lo ≤ j → j ≤ hi → ∀ k, lo ≤ k → k ≤ hi →
    ∃ p, IsCandDown C sel lo p ∧ ownsB C (sel j) p = true ∧ ownsB C (sel k) p = true

/-- Un candidato poseído por todos los miembros, con la simetría, lo alarga. -/
theorem ext_of_common (C : GPathM) (hsym : OwnSymmetric C) (sel : Int → PathNodeId) (lo hi : Int)
    (h : Seg C sel lo hi) (x : PathNodeId)
    (hall : ∀ j, lo ≤ j → j ≤ hi → ownsB C (sel j) x = true) :
    (∀ j, lo ≤ j → j ≤ hi → ∀ nj, C.node? (sel j) = some nj → x ∈ nj.owners) ∧
      (∀ nx, C.node? x = some nx → ∀ j, lo ≤ j → j ≤ hi → sel j ∈ nx.owners) := by
  have hmem : ∀ j, lo ≤ j → j ≤ hi → ∀ nj, C.node? (sel j) = some nj → x ∈ nj.owners :=
    fun j h1 h2 nj hnj => (ownsB_of C (sel j) x nj hnj).mp (hall j h1 h2)
  refine ⟨hmem, fun nx hnx j h1 h2 => ?_⟩
  obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp (h.1.1 j h1 h2).1
  exact hsym (sel j) nj x nx hnj hnx (hmem j h1 h2 nj hnj)

/-- **Pieza 2, hacia arriba**: con como mucho dos candidatos (`a`, `b`), el triángulo con el extremo y
la simetría de las tablas, el tramo se alarga un paso. -/
theorem extUp_of_two (C : GPathM) (hsym : OwnSymmetric C) (sel : Int → PathNodeId) (lo hi : Int)
    (hlh : lo ≤ hi) (h : Seg C sel lo hi) (a b : PathNodeId)
    (hab : ∀ r, IsCandUp C sel hi r → r = a ∨ r = b) (hT : TriTopUp C sel lo hi) :
    ∃ r, ExtUp C sel lo hi r := by
  have hJ : ∀ j, j ∈ intRange lo hi ↔ lo ≤ j ∧ j ≤ hi := fun j =>
    ⟨fun hj => ⟨mem_intRange_lower hj, mem_intRange_upper hj⟩, fun ⟨h1, h2⟩ => mem_intRange h1 h2⟩
  obtain ⟨x, ⟨hxn, hxs, hxp⟩, hall⟩ := helly_two (intRange lo hi) (fun j r => ownsB C (sel j) r)
    (IsCandUp C sel hi) a b hab lo ((hJ lo).mpr ⟨Int.le_refl _, hlh⟩)
    (fun j hj k hk => hT j ((hJ j).mp hj).1 ((hJ j).mp hj).2 k ((hJ k).mp hk).1 ((hJ k).mp hk).2)
  obtain ⟨h1, h2⟩ := ext_of_common C hsym sel lo hi h x
    (fun j hj1 hj2 => hall j ((hJ j).mpr ⟨hj1, hj2⟩))
  exact ⟨x, hxn, hxs, hxp, h1, h2⟩

/-- **Pieza 2, hacia abajo.** -/
theorem extDown_of_two (C : GPathM) (hsym : OwnSymmetric C) (sel : Int → PathNodeId) (lo hi : Int)
    (hlh : lo ≤ hi) (h : Seg C sel lo hi) (a b : PathNodeId)
    (hab : ∀ p, IsCandDown C sel lo p → p = a ∨ p = b) (hT : TriTopDown C sel lo hi) :
    ∃ p, ExtDown C sel lo hi p := by
  have hJ : ∀ j, j ∈ intRange lo hi ↔ lo ≤ j ∧ j ≤ hi := fun j =>
    ⟨fun hj => ⟨mem_intRange_lower hj, mem_intRange_upper hj⟩, fun ⟨h1, h2⟩ => mem_intRange h1 h2⟩
  obtain ⟨x, ⟨hxn, hxs, hxp⟩, hall⟩ := helly_two (intRange lo hi) (fun j r => ownsB C (sel j) r)
    (IsCandDown C sel lo) a b hab lo ((hJ lo).mpr ⟨Int.le_refl _, hlh⟩)
    (fun j hj k hk => hT j ((hJ j).mp hj).1 ((hJ j).mp hj).2 k ((hJ k).mp hk).1 ((hJ k).mp hk).2)
  obtain ⟨h1, h2⟩ := ext_of_common C hsym sel lo hi h x
    (fun j hj1 hj2 => hall j ((hJ j).mpr ⟨hj1, hj2⟩))
  exact ⟨x, hxn, hxs, hxp, h1, h2⟩

/-- **Cada paso es pequeño o cumple Helly**: o hay como mucho dos candidatos, o alguno lo poseen
todos los miembros (los pasos de cláusula con 3 o más filas vivas; medido: un 1 %, sin fallos). -/
def SmallOrHellyUp (C : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi + 1 ≤ C.current_step - 1 →
    Seg C sel lo hi →
    (∃ a b, ∀ r, IsCandUp C sel hi r → r = a ∨ r = b) ∨ ∃ r, ExtUp C sel lo hi r

def SmallOrHellyDown (C : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 1 ≤ lo → lo ≤ hi → hi ≤ C.current_step - 1 →
    Seg C sel lo hi →
    (∃ a b, ∀ p, IsCandDown C sel lo p → p = a ∨ p = b) ∨ ∃ p, ExtDown C sel lo hi p

/-- **El triángulo con el extremo** en todo tramo, en las dos direcciones. -/
def TriTop (C : GPathM) : Prop :=
  (∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi + 1 ≤ C.current_step - 1 →
    Seg C sel lo hi → TriTopUp C sel lo hi) ∧
  (∀ (sel : Int → PathNodeId) (lo hi : Int), 1 ≤ lo → lo ≤ hi → hi ≤ C.current_step - 1 →
    Seg C sel lo hi → TriTopDown C sel lo hi)

theorem oneStepUp_of (C : GPathM) (hsym : OwnSymmetric C) (hT : TriTop C) (hS : SmallOrHellyUp C) :
    OneStepUp C := by
  intro sel lo hi hlo hlh hhi h
  rcases hS sel lo hi hlo hlh hhi h with ⟨a, b, hab⟩ | hext
  · exact extUp_of_two C hsym sel lo hi hlh h a b hab (hT.1 sel lo hi hlo hlh hhi h)
  · exact hext

theorem oneStepDown_of (C : GPathM) (hsym : OwnSymmetric C) (hT : TriTop C)
    (hS : SmallOrHellyDown C) : OneStepDown C := by
  intro sel lo hi hlo hlh hhi h
  rcases hS sel lo hi hlo hlh hhi h with ⟨a, b, hab⟩ | hext
  · exact extDown_of_two C hsym sel lo hi hlh h a b hab (hT.2 sel lo hi hlo hlh hhi h)
  · exact hext

/-- **`PairHelly` desde el triángulo con el extremo**: con tablas simétricas, si cada dos miembros de
un tramo comparten un candidato para alargarlo (`TriTop`) y cada paso tiene como mucho dos candidatos
o cumple Helly (`SmallOrHelly…`), el estado cumple `PairHelly`. -/
theorem pairHelly_of_triTop (C : GPathM) (hsym : OwnSymmetric C) (hT : TriTop C)
    (hU : SmallOrHellyUp C) (hD : SmallOrHellyDown C) : PairHelly C :=
  pairHelly_of_oneStep C (oneStepUp_of C hsym hT hU) (oneStepDown_of C hsym hT hD)

/-- info: 'AbsSat.GraphPath.Model.OneStep.pairHelly_of_triTop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairHelly_of_triTop

-- ============================================================
-- Pieza 3: los pasos de cláusula, por cajas
-- ============================================================

/-- **Helly por cajas.** Cada miembro `j` admite un candidato `x` exactamente cuando los tres bits de
`x` (`co x p`) caen en sus valores permitidos (`W j p`): una caja. Si se cortan dos a dos, cada
coordenada es un Helly de dos elementos, así que hay un valor común por literal; si además algún
candidato vivo cae en esa intersección (`hlive`, lo que excluye el hueco 000 y las filas muertas), ese
candidato es común a todos. -/
theorem helly_box {ι α : Type} (J : List ι) (j0 : ι) (hj0 : j0 ∈ J) (P : ι → α → Bool)
    (Q : α → Prop) (co : α → Nat → Bool) (W : ι → Nat → Bool → Bool)
    (hbox : ∀ j ∈ J, ∀ x, Q x → (P j x = true ↔ ∀ p, p < 3 → W j p (co x p) = true))
    (hpair : ∀ j ∈ J, ∀ k ∈ J, ∃ x, Q x ∧ P j x = true ∧ P k x = true)
    (hlive : (∀ p, p < 3 → ∃ v, ∀ j ∈ J, W j p v = true) →
      ∃ x, Q x ∧ ∀ p, p < 3 → ∀ j ∈ J, W j p (co x p) = true) :
    ∃ x, Q x ∧ ∀ j ∈ J, P j x = true := by
  have hcoord : ∀ p, p < 3 → ∃ v, ∀ j ∈ J, W j p v = true := by
    intro p hp
    obtain ⟨v, _, hv⟩ := helly_two J (fun j v => W j p v) (fun _ => True) false true
      (fun v _ => by cases v <;> simp) j0 hj0
      (fun j hj k hk => by
        obtain ⟨x, hQx, h1, h2⟩ := hpair j hj k hk
        exact ⟨co x p, trivial, ((hbox j hj x hQx).mp h1) p hp, ((hbox k hk x hQx).mp h2) p hp⟩)
    exact ⟨v, hv⟩
  obtain ⟨x, hQx, hx⟩ := hlive hcoord
  exact ⟨x, hQx, fun j hj => (hbox j hj x hQx).mpr (fun p hp => hx p hp j hj)⟩

/-- info: 'AbsSat.GraphPath.Model.OneStep.helly_box' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms helly_box

/-- El bit `p` (0, 1, 2 = literales 1, 2, 3) de una fila de cláusula. -/
def rowBit (r : Int) (p : Nat) : Bool :=
  (if p == 0 then r / 4 % 2 else if p == 1 then r / 2 % 2 else r % 2) == 1

/-- **Cajas de un paso de cláusula, hacia arriba, sin hueco.** Hay, para cada miembro `j` y cada literal
`p`, un conjunto de valores permitidos `W j p` tal que el miembro posee un candidato exactamente
cuando los bits de su fila caen en ellos (su `B_u` es una caja), y si todos admiten algún valor en cada
literal, algún candidato vivo cae en la intersección (sin hueco 000 ni filas muertas).

Las cajas **no** son las que se leen de la tabla literal a literal (medido: 30 de 463 casos de la
semilla 7 tienen una caja así mayor que `B_u`, por exclusiones exactas a través de otras variables);
son las de las coordenadas que el propio `B_u` fija (medido: 0 fallos). Por eso `W` es existencial. -/
def BoxHellyUp (C : GPathM) (sel : Int → PathNodeId) (lo hi : Int) : Prop :=
  ∃ W : Int → Nat → Bool → Bool,
    (∀ j, lo ≤ j → j ≤ hi → ∀ r, IsCandUp C sel hi r →
      (ownsB C (sel j) r = true ↔ ∀ p, p < 3 → W j p (rowBit r.id.index p) = true)) ∧
    ((∀ p, p < 3 → ∃ v, ∀ j ∈ intRange lo hi, W j p v = true) →
      ∃ r, IsCandUp C sel hi r ∧ ∀ p, p < 3 → ∀ j ∈ intRange lo hi, W j p (rowBit r.id.index p) = true)

/-- **Pieza 3, hacia arriba**: con cajas sin hueco, el triángulo con el extremo y la simetría, el tramo
se alarga un paso. -/
theorem extUp_of_boxes (C : GPathM) (hsym : OwnSymmetric C) (sel : Int → PathNodeId) (lo hi : Int)
    (hlh : lo ≤ hi) (h : Seg C sel lo hi) (hB : BoxHellyUp C sel lo hi) (hT : TriTopUp C sel lo hi) :
    ∃ r, ExtUp C sel lo hi r := by
  have hJ : ∀ j, j ∈ intRange lo hi ↔ lo ≤ j ∧ j ≤ hi := fun j =>
    ⟨fun hj => ⟨mem_intRange_lower hj, mem_intRange_upper hj⟩, fun ⟨h1, h2⟩ => mem_intRange h1 h2⟩
  obtain ⟨W, hbox, hlive⟩ := hB
  obtain ⟨x, ⟨hxn, hxs, hxp⟩, hall⟩ := helly_box (intRange lo hi) lo ((hJ lo).mpr ⟨Int.le_refl _, hlh⟩)
    (fun j r => ownsB C (sel j) r) (IsCandUp C sel hi) (fun r p => rowBit r.id.index p) W
    (fun j hj x hx => hbox j ((hJ j).mp hj).1 ((hJ j).mp hj).2 x hx)
    (fun j hj k hk => hT j ((hJ j).mp hj).1 ((hJ j).mp hj).2 k ((hJ k).mp hk).1 ((hJ k).mp hk).2)
    hlive
  obtain ⟨h1, h2⟩ := ext_of_common C hsym sel lo hi h x (fun j hj1 hj2 => hall j ((hJ j).mpr ⟨hj1, hj2⟩))
  exact ⟨x, hxn, hxs, hxp, h1, h2⟩

/-- info: 'AbsSat.GraphPath.Model.OneStep.extUp_of_boxes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms extUp_of_boxes

/-- **La mitad «⊆» de las cajas, en general**: en un estado donde la regla de parejas no quita nada,
con los nodos válidos y las tablas filtradas por los requisitos (`ReqFiltered`, invariante de la
máquina), si `u` posee a `r`, la tabla de `u` contiene cada nodo que `r` requiere. Los dos comparten
entrada en el paso del requisito, y en la tabla de `r` esa entrada solo puede ser la requerida. -/
theorem req_shared (reqOf : NodeId → List NodeId) (C : GPathM)
    (hRF : ReqFiltered reqOf C) (hP : PairHelly.PairFixed C)
    (hval : ∀ n ∈ C.nodes, isValidNode C n = true)
    (u : PathNodeId) (nu : PNodeM) (hu : C.node? u = some nu)
    (r : PathNodeId) (nr : PNodeM) (hr : C.node? r = some nr) (hur : r ∈ nu.owners) (hne : r ≠ u)
    (req : NodeId) (hreq : req ∈ reqOf r.id) (h0 : 0 ≤ req.step) (h1 : req.step < C.current_step) :
    ∃ q ∈ nu.owners, q.id = req := by
  have hsh := PairHelly.pairOk_of_fixed C hP u nu r hu hur hne nr hr
  unfold pairShares at hsh
  have hk : req.step ∈ intRange 0 (C.current_step - 1) := mem_intRange h0 (by omega)
  have hkk := List.all_eq_true.mp hsh req.step hk
  have hvu := owners_ok_of_isValidNode C nu (hval nu (List.mem_of_find?_eq_some hu))
  have hvr := owners_ok_of_isValidNode C nr (hval nr (List.mem_of_find?_eq_some hr))
  rw [List.all_eq_true.mp hvu req.step hk, List.all_eq_true.mp hvr req.step hk] at hkk
  simp only [Bool.not_true, Bool.false_or] at hkk
  obtain ⟨q, hq, hqr⟩ := List.any_eq_true.mp hkk
  have hq' := List.mem_filter.mp hq
  have hqr' : q ∈ nr.owners := List.contains_iff_mem.mp hqr
  have hrid : nr.id = r := node?_id_eq C r nr hr
  have hreq' : req ∈ reqOf nr.id.id := by rw [hrid]; exact hreq
  refine ⟨q, hq'.1, hRF nr (List.mem_of_find?_eq_some hr) req hreq' q hqr' ?_⟩
  exact eq_of_beq hq'.2

/-- info: 'AbsSat.GraphPath.Model.OneStep.req_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms req_shared

/-- **La pieza 3 da el paso grande**: si en todo tramo el paso siguiente tiene como mucho dos
candidatos o sus `B_u` son cajas sin hueco, y vale el triángulo con el extremo, vale
`SmallOrHellyUp`. -/
theorem smallOrHellyUp_of_boxes (C : GPathM) (hsym : OwnSymmetric C) (hT : TriTop C)
    (hSB : ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi + 1 ≤ C.current_step - 1 →
      Seg C sel lo hi →
      (∃ a b, ∀ r, IsCandUp C sel hi r → r = a ∨ r = b) ∨ BoxHellyUp C sel lo hi) :
    SmallOrHellyUp C := by
  intro sel lo hi hlo hlh hhi h
  rcases hSB sel lo hi hlo hlh hhi h with hab | hbox
  · exact Or.inl hab
  · exact Or.inr (extUp_of_boxes C hsym sel lo hi hlh h hbox (hT.1 sel lo hi hlo hlh hhi h))

end AbsSat.GraphPath.Model.OneStep
