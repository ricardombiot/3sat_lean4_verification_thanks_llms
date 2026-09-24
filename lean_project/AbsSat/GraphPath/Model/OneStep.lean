-- lean_project/AbsSat/GraphPath/Model/OneStep.lean
import AbsSat.GraphPath.Model.PairHelly
import AbsSat.GraphPath.Model.SegExact
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

-- ============================================================
-- Pieza 4: el triángulo con el extremo, cuando el extremo es de la pareja
-- ============================================================

/-- Una entrada común de dos tablas en el paso `k`, en un estado donde la regla no quita nada y los
nodos son válidos. -/
theorem shared_at (C : GPathM) (hP : PairHelly.PairFixed C)
    (hval : ∀ n ∈ C.nodes, isValidNode C n = true)
    (x : PathNodeId) (nx : PNodeM) (hx : C.node? x = some nx)
    (w : PathNodeId) (nw : PNodeM) (hw : C.node? w = some nw) (hxw : w ∈ nx.owners) (hne : w ≠ x)
    (k : Int) (h0 : 0 ≤ k) (h1 : k < C.current_step) :
    ∃ q ∈ nx.owners, q.id.step = k ∧ q ∈ nw.owners := by
  have hsh := PairHelly.pairOk_of_fixed C hP x nx w hx hxw hne nw hw
  unfold pairShares at hsh
  have hk : k ∈ intRange 0 (C.current_step - 1) := mem_intRange h0 (by omega)
  have hkk := List.all_eq_true.mp hsh k hk
  have hvx := owners_ok_of_isValidNode C nx (hval nx (List.mem_of_find?_eq_some hx))
  have hvw := owners_ok_of_isValidNode C nw (hval nw (List.mem_of_find?_eq_some hw))
  rw [List.all_eq_true.mp hvx k hk, List.all_eq_true.mp hvw k hk] at hkk
  simp only [Bool.not_true, Bool.false_or] at hkk
  obtain ⟨q, hq, hqw⟩ := List.any_eq_true.mp hkk
  have hq' := List.mem_filter.mp hq
  exact ⟨q, hq'.1, eq_of_beq hq'.2, List.contains_iff_mem.mp hqw⟩

/-- Una entrada propia en el paso `k` (nodo válido). -/
theorem own_at (C : GPathM) (hval : ∀ n ∈ C.nodes, isValidNode C n = true)
    (x : PathNodeId) (nx : PNodeM) (hx : C.node? x = some nx)
    (k : Int) (h0 : 0 ≤ k) (h1 : k < C.current_step) : ∃ q ∈ nx.owners, q.id.step = k := by
  have hvx := owners_ok_of_isValidNode C nx (hval nx (List.mem_of_find?_eq_some hx))
  have hk : k ∈ intRange 0 (C.current_step - 1) := mem_intRange h0 (by omega)
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hvx k hk)
  exact ⟨q, hq, eq_of_beq hqs⟩

/-- Una entrada del extremo `t` en el paso siguiente es un candidato (I1-hijos, hijos vivos, SMP
invertido por `PMS`). -/
theorem candUp_of_top_entry (C : GPathM) (hi1s : PassPlain.I1s C) (hsl : PassCtx.SLive C)
    (hpms : Sons.PMS C) (sel : Int → PathNodeId) (hi : Int) (nt : PNodeM)
    (ht : C.node? (sel hi) = some nt) (hts : (sel hi).id.step = hi)
    (q : PathNodeId) (hq : q ∈ nt.owners) (hqs : q.id.step = hi + 1) (hq0 : 0 ≤ hi + 1)
    (hq1 : hi + 1 ≤ C.current_step - 1) : IsCandUp C sel hi q := by
  have hson : q ∈ nt.sons := hi1s (sel hi) nt ht q hq (by omega) (by omega) (by omega)
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (hsl (sel hi) nt ht q hson)
  have hpar := hpms nt (List.mem_of_find?_eq_some ht) q hson nq (List.mem_of_find?_eq_some hnq)
    (node?_id_eq C q nq hnq)
  rw [node?_id_eq C (sel hi) nt ht] at hpar
  refine ⟨by rw [hnq]; rfl, hqs, ?_⟩
  rw [hnq]; exact hpar

/-- Y una del extremo inferior en el paso anterior, un candidato de abajo (I1, padres vivos). -/
theorem candDown_of_bottom_entry (C : GPathM) (hi1 : PassPlain.I1 C) (hpl : PassCtx.PLive C)
    (sel : Int → PathNodeId) (lo : Int) (nb : PNodeM)
    (hb : C.node? (sel lo) = some nb) (hbs : (sel lo).id.step = lo)
    (q : PathNodeId) (hq : q ∈ nb.owners) (hqs : q.id.step = lo - 1) (hq0 : 0 ≤ lo - 1)
    (hq1 : lo - 1 ≤ C.current_step - 1) : IsCandDown C sel lo q := by
  have hpar : q ∈ nb.parents := hi1 (sel lo) nb hb q hq (by omega) (by omega) (by omega)
  refine ⟨hpl (sel lo) nb hb q hpar, hqs, ?_⟩
  rw [hb]; exact hpar

/-- **El triángulo con el extremo, cuando el extremo está en la pareja** (hacia arriba). La regla de
parejas da una entrada común del extremo y del otro miembro en el paso siguiente, y las entradas del
extremo allí son sus hijos. Así `TriTopUp` se reduce a las parejas de **miembros interiores**. -/
theorem triTopUp_of_inner (C : GPathM) (hP : PairHelly.PairFixed C)
    (hval : ∀ n ∈ C.nodes, isValidNode C n = true) (hi1s : PassPlain.I1s C)
    (hsl : PassCtx.SLive C) (hpms : Sons.PMS C)
    (sel : Int → PathNodeId) (lo hi : Int) (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi + 1 ≤ C.current_step - 1) (h : Seg C sel lo hi)
    (hin : ∀ j, lo ≤ j → j < hi → ∀ k, lo ≤ k → k < hi →
      ∃ r, IsCandUp C sel hi r ∧ ownsB C (sel j) r = true ∧ ownsB C (sel k) r = true) :
    TriTopUp C sel lo hi := by
  obtain ⟨nt, ht⟩ := Option.isSome_iff_exists.mp (h.1.1 hi hlh (Int.le_refl _)).1
  have hts := (h.1.1 hi hlh (Int.le_refl _)).2
  -- the pair (top, member j): a son of the top owned by both
  have htop : ∀ j, lo ≤ j → j ≤ hi →
      ∃ r, IsCandUp C sel hi r ∧ ownsB C (sel hi) r = true ∧ ownsB C (sel j) r = true := by
    intro j hj0 hj1
    obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp (h.1.1 j hj0 hj1).1
    by_cases hjt : j = hi
    · subst hjt
      obtain ⟨q, hq, hqs⟩ := own_at C hval (sel j) nt ht (j + 1) (by omega) (by omega)
      have hc := candUp_of_top_entry C hi1s hsl hpms sel j nt ht hts q hq hqs (by omega) hhi
      have ho : ownsB C (sel j) q = true := (ownsB_of C (sel j) q nt ht).mpr hq
      exact ⟨q, hc, ho, ho⟩
    · have hjne : sel j ≠ sel hi := by
        intro he
        have := (h.1.1 j hj0 hj1).2
        rw [he, hts] at this; omega
      have hjt' : sel j ∈ nt.owners := h.2 j hi hj0 hlh hj1 (Int.le_refl _) hjt nt ht
      obtain ⟨q, hq, hqs, hqj⟩ := shared_at C hP hval (sel hi) nt ht (sel j) nj hnj hjt' hjne
        (hi + 1) (by omega) (by omega)
      exact ⟨q, candUp_of_top_entry C hi1s hsl hpms sel hi nt ht hts q hq hqs (by omega) hhi,
        (ownsB_of C (sel hi) q nt ht).mpr hq, (ownsB_of C (sel j) q nj hnj).mpr hqj⟩
  intro j hj0 hj1 k hk0 hk1
  by_cases hjt : j = hi
  · subst hjt; exact htop k hk0 hk1
  · by_cases hkt : k = hi
    · subst hkt
      obtain ⟨r, hr, h1, h2⟩ := htop j hj0 hj1
      exact ⟨r, hr, h2, h1⟩
    · exact hin j hj0 (by omega) k hk0 (by omega)

/-- info: 'AbsSat.GraphPath.Model.OneStep.triTopUp_of_inner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms triTopUp_of_inner

/-- **Lo mismo hacia abajo**: `TriTopDown` se reduce a las parejas de miembros por encima del extremo
inferior. -/
theorem triTopDown_of_inner (C : GPathM) (hP : PairHelly.PairFixed C)
    (hval : ∀ n ∈ C.nodes, isValidNode C n = true) (hi1 : PassPlain.I1 C) (hpl : PassCtx.PLive C)
    (sel : Int → PathNodeId) (lo hi : Int) (hlo : 1 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi ≤ C.current_step - 1) (h : Seg C sel lo hi)
    (hin : ∀ j, lo < j → j ≤ hi → ∀ k, lo < k → k ≤ hi →
      ∃ p, IsCandDown C sel lo p ∧ ownsB C (sel j) p = true ∧ ownsB C (sel k) p = true) :
    TriTopDown C sel lo hi := by
  obtain ⟨nb, hb⟩ := Option.isSome_iff_exists.mp (h.1.1 lo (Int.le_refl _) hlh).1
  have hbs := (h.1.1 lo (Int.le_refl _) hlh).2
  have hbot : ∀ j, lo ≤ j → j ≤ hi →
      ∃ p, IsCandDown C sel lo p ∧ ownsB C (sel lo) p = true ∧ ownsB C (sel j) p = true := by
    intro j hj0 hj1
    obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp (h.1.1 j hj0 hj1).1
    by_cases hjb : j = lo
    · subst hjb
      obtain ⟨q, hq, hqs⟩ := own_at C hval (sel j) nb hb (j - 1) (by omega) (by omega)
      have hc := candDown_of_bottom_entry C hi1 hpl sel j nb hb hbs q hq hqs (by omega) (by omega)
      have ho : ownsB C (sel j) q = true := (ownsB_of C (sel j) q nb hb).mpr hq
      exact ⟨q, hc, ho, ho⟩
    · have hjne : sel j ≠ sel lo := by
        intro he
        have := (h.1.1 j hj0 hj1).2
        rw [he, hbs] at this; omega
      have hjb' : sel j ∈ nb.owners := h.2 j lo hj0 (Int.le_refl _) hj1 hlh hjb nb hb
      obtain ⟨q, hq, hqs, hqj⟩ := shared_at C hP hval (sel lo) nb hb (sel j) nj hnj hjb' hjne
        (lo - 1) (by omega) (by omega)
      exact ⟨q, candDown_of_bottom_entry C hi1 hpl sel lo nb hb hbs q hq hqs (by omega) (by omega),
        (ownsB_of C (sel lo) q nb hb).mpr hq, (ownsB_of C (sel j) q nj hnj).mpr hqj⟩
  intro j hj0 hj1 k hk0 hk1
  by_cases hjb : j = lo
  · subst hjb; exact hbot k hk0 hk1
  · by_cases hkb : k = lo
    · subst hkb
      obtain ⟨p, hp, h1, h2⟩ := hbot j hj0 hj1
      exact ⟨p, hp, h2, h1⟩
    · exact hin j (by omega) hj1 k (by omega) hk1

/-- **Helly de tres, en el paso contiguo al tercero**: tres nodos que se poseen mutuamente comparten
una entrada en el paso inmediatamente por encima o por debajo del tercero (`c`). Es lo único que usa
la extensión de un paso: `c` es el extremo del tramo. -/
def Tri3 (C : GPathM) : Prop :=
  ∀ a na b nb c nc, C.node? a = some na → C.node? b = some nb → C.node? c = some nc →
    b ∈ na.owners → c ∈ na.owners → c ∈ nb.owners →
    ∀ k, (k = c.id.step + 1 ∨ k + 1 = c.id.step) → 0 ≤ k → k < C.current_step →
      ∃ q ∈ na.owners, q.id.step = k ∧ q ∈ nb.owners ∧ q ∈ nc.owners

/-- **Pieza 4 desde `Tri3`, hacia arriba**: dos miembros interiores y el extremo se poseen mutuamente;
su entrada común en el paso siguiente es una entrada del extremo, luego un candidato. -/
theorem triTopUp_of_tri3 (C : GPathM) (hP : PairHelly.PairFixed C)
    (hval : ∀ n ∈ C.nodes, isValidNode C n = true) (hi1s : PassPlain.I1s C)
    (hsl : PassCtx.SLive C) (hpms : Sons.PMS C) (h3 : Tri3 C)
    (sel : Int → PathNodeId) (lo hi : Int) (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi + 1 ≤ C.current_step - 1) (h : Seg C sel lo hi) : TriTopUp C sel lo hi := by
  obtain ⟨nt, ht⟩ := Option.isSome_iff_exists.mp (h.1.1 hi hlh (Int.le_refl _)).1
  have hts := (h.1.1 hi hlh (Int.le_refl _)).2
  refine triTopUp_of_inner C hP hval hi1s hsl hpms sel lo hi hlo hlh hhi h ?_
  intro j hj0 hj1 k hk0 hk1
  obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp (h.1.1 j hj0 (by omega)).1
  obtain ⟨nk, hnk⟩ := Option.isSome_iff_exists.mp (h.1.1 k hk0 (by omega)).1
  have htj : sel hi ∈ nj.owners := h.2 hi j hlh hj0 (Int.le_refl _) (by omega) (by omega) nj hnj
  have htk : sel hi ∈ nk.owners := h.2 hi k hlh hk0 (Int.le_refl _) (by omega) (by omega) nk hnk
  by_cases hjk : j = k
  · subst hjk
    have hjt : sel j ∈ nt.owners := h.2 j hi hj0 hlh (by omega) (Int.le_refl _) (by omega) nt ht
    have hne : sel j ≠ sel hi := by
      intro he; have := (h.1.1 j hj0 (by omega)).2; rw [he, hts] at this; omega
    obtain ⟨q, hq, hqs, hqj⟩ := shared_at C hP hval (sel hi) nt ht (sel j) nj hnj hjt hne
      (hi + 1) (by omega) (by omega)
    have ho : ownsB C (sel j) q = true := (ownsB_of C (sel j) q nj hnj).mpr hqj
    exact ⟨q, candUp_of_top_entry C hi1s hsl hpms sel hi nt ht hts q hq hqs (by omega) hhi, ho, ho⟩
  · have hkj : sel k ∈ nj.owners := h.2 k j hk0 hj0 (by omega) (by omega) (Ne.symm hjk) nj hnj
    obtain ⟨q, hqj, hqs, hqk, hqt⟩ := h3 (sel j) nj (sel k) nk (sel hi) nt hnj hnk ht hkj htj htk
      (hi + 1) (Or.inl (by rw [hts])) (by omega) (by omega)
    exact ⟨q, candUp_of_top_entry C hi1s hsl hpms sel hi nt ht hts q hqt hqs (by omega) hhi,
      (ownsB_of C (sel j) q nj hnj).mpr hqj, (ownsB_of C (sel k) q nk hnk).mpr hqk⟩

/-- **Y hacia abajo.** -/
theorem triTopDown_of_tri3 (C : GPathM) (hP : PairHelly.PairFixed C)
    (hval : ∀ n ∈ C.nodes, isValidNode C n = true) (hi1 : PassPlain.I1 C) (hpl : PassCtx.PLive C)
    (h3 : Tri3 C) (sel : Int → PathNodeId) (lo hi : Int) (hlo : 1 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi ≤ C.current_step - 1) (h : Seg C sel lo hi) : TriTopDown C sel lo hi := by
  obtain ⟨nb, hb⟩ := Option.isSome_iff_exists.mp (h.1.1 lo (Int.le_refl _) hlh).1
  have hbs := (h.1.1 lo (Int.le_refl _) hlh).2
  refine triTopDown_of_inner C hP hval hi1 hpl sel lo hi hlo hlh hhi h ?_
  intro j hj0 hj1 k hk0 hk1
  obtain ⟨nj, hnj⟩ := Option.isSome_iff_exists.mp (h.1.1 j (by omega) hj1).1
  obtain ⟨nk, hnk⟩ := Option.isSome_iff_exists.mp (h.1.1 k (by omega) hk1).1
  have hbj : sel lo ∈ nj.owners := h.2 lo j (Int.le_refl _) (by omega) hlh hj1 (by omega) nj hnj
  have hbk : sel lo ∈ nk.owners := h.2 lo k (Int.le_refl _) (by omega) hlh hk1 (by omega) nk hnk
  by_cases hjk : j = k
  · subst hjk
    have hjb : sel j ∈ nb.owners := h.2 j lo (by omega) (Int.le_refl _) hj1 hlh (by omega) nb hb
    have hne : sel j ≠ sel lo := by
      intro he; have := (h.1.1 j (by omega) hj1).2; rw [he, hbs] at this; omega
    obtain ⟨q, hq, hqs, hqj⟩ := shared_at C hP hval (sel lo) nb hb (sel j) nj hnj hjb hne
      (lo - 1) (by omega) (by omega)
    have ho : ownsB C (sel j) q = true := (ownsB_of C (sel j) q nj hnj).mpr hqj
    exact ⟨q, candDown_of_bottom_entry C hi1 hpl sel lo nb hb hbs q hq hqs (by omega) (by omega),
      ho, ho⟩
  · have hkj : sel k ∈ nj.owners := h.2 k j (by omega) (by omega) hk1 hj1 (Ne.symm hjk) nj hnj
    obtain ⟨q, hqj, hqs, hqk, hqb⟩ := h3 (sel j) nj (sel k) nk (sel lo) nb hnj hnk hb hkj hbj hbk
      (lo - 1) (Or.inr (by rw [hbs]; omega)) (by omega) (by omega)
    exact ⟨q, candDown_of_bottom_entry C hi1 hpl sel lo nb hb hbs q hqb hqs (by omega) (by omega),
      (ownsB_of C (sel j) q nj hnj).mpr hqj, (ownsB_of C (sel k) q nk hnk).mpr hqk⟩

/-- **`TriTop` desde `Tri3`.** -/
theorem triTop_of_tri3 (C : GPathM) (hP : PairHelly.PairFixed C)
    (hval : ∀ n ∈ C.nodes, isValidNode C n = true) (hi1 : PassPlain.I1 C) (hi1s : PassPlain.I1s C)
    (hpl : PassCtx.PLive C) (hsl : PassCtx.SLive C) (hpms : Sons.PMS C) (h3 : Tri3 C) : TriTop C :=
  ⟨fun sel lo hi hlo hlh hhi h => triTopUp_of_tri3 C hP hval hi1s hsl hpms h3 sel lo hi hlo hlh hhi h,
   fun sel lo hi hlo hlh hhi h => triTopDown_of_tri3 C hP hval hi1 hpl h3 sel lo hi hlo hlh hhi h⟩

/-- info: 'AbsSat.GraphPath.Model.OneStep.triTop_of_tri3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms triTop_of_tri3

-- ============================================================
-- Por la historia: el testigo del estado del lector (v188)
-- ============================================================

/-- **Testigo de `g` hacia arriba** para un tramo: un hijo del extremo en `g` que todos los miembros
poseen en `g`. -/
def WitUp (g : GPathM) (sel : Int → PathNodeId) (lo hi : Int) (w : PathNodeId) : Prop :=
  IsCandUp g sel hi w ∧ ∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → w ∈ nj.owners

/-- **Y hacia abajo**: un padre del extremo inferior en `g` que todos poseen en `g`. -/
def WitDown (g : GPathM) (sel : Int → PathNodeId) (lo hi : Int) (w : PathNodeId) : Prop :=
  IsCandDown g sel lo w ∧ ∀ j, lo ≤ j → j ≤ hi → ∀ nj, g.node? (sel j) = some nj → w ∈ nj.owners

/-- **Parte 1: el testigo existe en `g`.** Un tramo de un estado `C` podado de `g` es tramo de `g`
(`seg_before`); con `SegExact g` se extiende a una cadena completa de `g`, y su nodo del paso siguiente
es hijo del extremo y lo poseen todos los miembros. Sin Helly. -/
theorem witUp_of_segExact (g C : GPathM) (hpr : Pruned g C) (hnd : NodupIds g)
    (hE : SegExact.SegExact g) (sel : Int → PathNodeId) (lo hi : Int) (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi + 1 ≤ C.current_step - 1) (h : Seg C sel lo hi) : ∃ w, WitUp g sel lo hi w := by
  obtain ⟨hpc, hpo⟩ := SegExact.seg_before g C hpr hnd sel lo hi h.1 h.2
  have hcs : C.current_step = g.current_step := hpr.step_eq
  obtain ⟨s, hs, hagree⟩ := hE sel lo hi hlo hlh (by omega) hpc hpo
  obtain ⟨⟨⟨hnode, hlink⟩, hown⟩, _⟩ := hs
  refine ⟨s (hi + 1), ⟨(hnode (hi + 1) (by omega) (by omega)).1,
    (hnode (hi + 1) (by omega) (by omega)).2, ?_⟩, ?_⟩
  · have := hlink hi (by omega) (by omega)
    rw [hagree hi hlh (Int.le_refl _)] at this
    exact this
  · intro j hj0 hj1 nj hnj
    rw [← hagree j hj0 hj1] at hnj
    exact hown (hi + 1) j (by omega) (by omega) (by omega) (by omega) (by omega) nj hnj

theorem witDown_of_segExact (g C : GPathM) (hpr : Pruned g C) (hnd : NodupIds g)
    (hE : SegExact.SegExact g) (sel : Int → PathNodeId) (lo hi : Int) (hlo : 1 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi ≤ C.current_step - 1) (h : Seg C sel lo hi) : ∃ w, WitDown g sel lo hi w := by
  obtain ⟨hpc, hpo⟩ := SegExact.seg_before g C hpr hnd sel lo hi h.1 h.2
  have hcs : C.current_step = g.current_step := hpr.step_eq
  obtain ⟨s, hs, hagree⟩ := hE sel lo hi (by omega) hlh (by omega) hpc hpo
  obtain ⟨⟨⟨hnode, hlink⟩, hown⟩, _⟩ := hs
  refine ⟨s (lo - 1), ⟨(hnode (lo - 1) (by omega) (by omega)).1,
    (hnode (lo - 1) (by omega) (by omega)).2, ?_⟩, ?_⟩
  · have := hlink (lo - 1) (by omega) (by omega)
    rw [show lo - 1 + 1 = lo by omega, hagree lo (Int.le_refl _) hlh] at this
    exact this
  · intro j hj0 hj1 nj hnj
    rw [← hagree j hj0 hj1] at hnj
    exact hown (lo - 1) j (by omega) (by omega) (by omega) (by omega) (by omega) nj hnj

/-- info: 'AbsSat.GraphPath.Model.OneStep.witUp_of_segExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms witUp_of_segExact

/-- **Parte 2, la hipótesis de supervivencia (arriba)**: de los testigos que `g` da (parte 1), alguno
sigue en `C`: vivo, hijo del extremo y en la tabla de todo miembro. Medido (`tri3x`, 33.403 tramos):
el pin nunca mata todos los testigos de `g` de un tramo que sobrevive, y aunque la regla le quite
alguno a un miembro (58 tramos), siempre queda otro. Sustituye a las piezas 3 y 4. -/
def SurvivesUp (g C : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 0 ≤ lo → lo ≤ hi → hi + 1 ≤ C.current_step - 1 →
    Seg C sel lo hi →
    ∃ w, WitUp g sel lo hi w ∧ IsCandUp C sel hi w ∧ ∀ j, lo ≤ j → j ≤ hi → ownsB C (sel j) w = true

/-- **Y abajo.** -/
def SurvivesDown (g C : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo hi : Int), 1 ≤ lo → lo ≤ hi → hi ≤ C.current_step - 1 →
    Seg C sel lo hi →
    ∃ w, WitDown g sel lo hi w ∧ IsCandDown C sel lo w ∧ ∀ j, lo ≤ j → j ≤ hi → ownsB C (sel j) w = true

theorem oneStepUp_of_survives (g C : GPathM) (hsym : OwnSymmetric C) (hS : SurvivesUp g C) :
    OneStepUp C := by
  intro sel lo hi hlo hlh hhi h
  obtain ⟨w, _, ⟨hwn, hws, hwp⟩, hall⟩ := hS sel lo hi hlo hlh hhi h
  obtain ⟨h1, h2⟩ := ext_of_common C hsym sel lo hi h w hall
  exact ⟨w, hwn, hws, hwp, h1, h2⟩

theorem oneStepDown_of_survives (g C : GPathM) (hsym : OwnSymmetric C) (hS : SurvivesDown g C) :
    OneStepDown C := by
  intro sel lo hi hlo hlh hhi h
  obtain ⟨w, _, ⟨hwn, hws, hwp⟩, hall⟩ := hS sel lo hi hlo hlh hhi h
  obtain ⟨h1, h2⟩ := ext_of_common C hsym sel lo hi h w hall
  exact ⟨w, hwn, hws, hwp, h1, h2⟩

/-- **`PairHelly` por la historia**: con tablas simétricas, si algún testigo del estado del lector
sobrevive en cada tramo, en las dos direcciones, vale `PairHelly`. Sin cajas, sin hueco, sin `Tri3`. -/
theorem pairHelly_of_survives (g C : GPathM) (hsym : OwnSymmetric C) (hU : SurvivesUp g C)
    (hD : SurvivesDown g C) : PairHelly C :=
  pairHelly_of_oneStep C (oneStepUp_of_survives g C hsym hU) (oneStepDown_of_survives g C hsym hD)

/-- info: 'AbsSat.GraphPath.Model.OneStep.pairHelly_of_survives' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairHelly_of_survives

/-- **Parte 1 con `SegGood`** (lo que la escalera da del estado del lector): la entrada común del paso
siguiente está en la tabla del extremo, así que es un hijo suyo. -/
theorem witUp_of_segGood (g C : GPathM) (hpr : Pruned g C) (hnd : NodupIds g) (hG : SegGood g)
    (hi1s : PassPlain.I1s g) (hsl : PassCtx.SLive g) (hpms : Sons.PMS g)
    (sel : Int → PathNodeId) (lo hi : Int) (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi + 1 ≤ C.current_step - 1) (h : Seg C sel lo hi) : ∃ w, WitUp g sel lo hi w := by
  obtain ⟨hpc, hpo⟩ := SegExact.seg_before g C hpr hnd sel lo hi h.1 h.2
  have hcs : C.current_step = g.current_step := hpr.step_eq
  obtain ⟨r, hrs, hall⟩ := hG sel lo hi hlo hlh (by omega) hpc hpo (hi + 1) (by omega) (by omega)
    (Or.inr (by omega))
  obtain ⟨nt, ht⟩ := Option.isSome_iff_exists.mp (hpc.1 hi hlh (Int.le_refl _)).1
  have hts := (hpc.1 hi hlh (Int.le_refl _)).2
  exact ⟨r, candUp_of_top_entry g hi1s hsl hpms sel hi nt ht hts r (hall hi hlh (Int.le_refl _) nt ht)
    hrs (by omega) (by omega), hall⟩

/-- **`PairHelly` tras la limpieza con parejas, por la historia**: con la simetría de `cleanPair`
(`OwnSymmetric_cleanPair`) y la supervivencia de un testigo del estado del lector. -/
theorem pairHelly_cleanPair_of_survives (g X : GPathM) (hr : SymInvariant.RevOk X)
    (hU : SurvivesUp g (cleanPair X)) (hD : SurvivesDown g (cleanPair X)) :
    PairHelly (cleanPair X) := fun hv _ =>
  let hsym := (SymInvariant.OwnSymmetric_cleanPair X hr.nd hr.sh hr.sym hv).2
  segGood_of_oneStep _ (oneStepUp_of_survives g _ hsym hU) (oneStepDown_of_survives g _ hsym hD)

open AbsSat.Cnf in
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeak) in
/-- **El lector sin retroceso decide 3-SAT**, con `hStart` y, en cada pin del lector (estado `g`,
estado pinchado `X`): **un testigo de `g` sobrevive en cada tramo** tras `cleanPair X`, hacia arriba y
hacia abajo (`SurvivesUp`, `SurvivesDown`); el resto de `PStateG` tras la limpieza (`CleanRest`); y las
vueltas siguientes listas (`LaterValid`). Sin cajas, sin hueco, sin `Tri3`. -/
theorem readerVerdictW_iff_of_survives
    (hStart : ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ,
      isValid (AggressiveReview.filterAllAgg kv.2 []) = true →
        SegExact.SegExact (AggressiveReview.filterAllAgg kv.2 []))
    (hPin : ∀ φ : Cnf, WF φ → ∀ kv ∈ PureDriverImproves.pureRunW φ, ∀ g k q,
      PinAliveChain.ReadFromR (AggressiveReview.filterAllAgg kv.2 []) g → isValid g = true →
      ReaderExec.firstChoice g = some k → q ∈ ownersAt g.gowners k →
      SurvivesUp g (cleanPair (filterWeak g (q.id.step, [q.id]))) ∧
        SurvivesDown g (cleanPair (filterWeak g (q.id.step, [q.id]))) ∧
        PairHelly.CleanRest (filterWeak g (q.id.step, [q.id])) ∧
        PinDoomed.LaterValid (filterWeak g (q.id.step, [q.id])))
    (φ : Cnf) (hwf : WF φ) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine PairHelly.readerVerdictW_iff_of_pairHelly hStart ?_ φ hwf
  intro φ' hwf' kv hkv g k q hR hv hk hq
  obtain ⟨hU, hD, hC, hL⟩ := hPin φ' hwf' kv hkv g k q hR hv hk hq
  obtain ⟨hm, hcs, _⟩ := ReaderAggRun.pureRunW_state φ' hwf' kv hkv
  refine ⟨?_, hC, hL⟩
  intro hvC hfix
  -- the symmetry of the pinned state, from the reader state's fixpoint
  have hpos : 0 < kv.2.current_step := by rw [hcs]; exact ConservationCore.stepCount_pos φ'
  have ctx₀ : PinAliveChain.DCtx (AggressiveReview.filterAllAgg kv.2 []) :=
    { rd := ⟨kv.2, [], hm.rctx, rfl⟩
      pms := AggInvariants.PMS_filterAllAgg kv.2 [] hm.pms
      sn := AggInvariants.SN_filterAllAgg kv.2 [] hm.sn
      smp := AnchoredSurvive.SMP_filterAllAgg kv.2 hm.smp hm.rctx.shape.notroot []
      pos := by rw [(AggressiveReview.pruned_filterAllAgg kv.2 []).step_eq]; exact hpos }
  have ctx := TopGoodLadder.dctx_of_readFromR _ ctx₀ g hR
  have hsymX : Threaded.OwnSymmetric (filterWeak g (q.id.step, [q.id])) :=
    PinDoomed.ownSymmetric_filterWeak g _ (PinExactBoundary.ownSymmetric_of_aggOk g (by
      obtain ⟨g₀, reqs, _, hg⟩ := ctx.rd
      rw [hg] at hv ⊢
      exact AggFixpoint.aggOk_reviewAgg _ hv) (ReaderAgg.RCtx_of_readableAgg g ctx.rd).snn
      (ReaderAgg.RCtx_of_readableAgg g ctx.rd).below
      (AdjacentOwners.adj_of_readable g ctx.rd hv ctx.pms ctx.sn).ctx.nodeval)
  have hrX : SymInvariant.RevOk (filterWeak g (q.id.step, [q.id])) :=
    ⟨(ReaderAgg.RCtx_of_readableAgg g ctx.rd).nodup,
     ⟨(ReaderAgg.RCtx_of_readableAgg g ctx.rd).oos, (ReaderAgg.RCtx_of_readableAgg g ctx.rd).snn,
      (ReaderAgg.RCtx_of_readableAgg g ctx.rd).below⟩, hsymX⟩
  exact pairHelly_cleanPair_of_survives g _ hrX hU hD hvC hfix

/-- info: 'AbsSat.GraphPath.Model.OneStep.readerVerdictW_iff_of_survives' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_survives

-- ============================================================
-- (W2) El criterio salva de la purga
-- ============================================================

/-- **Exactitud de las tablas por parejas**: cada entrada viva de una tabla está en una cadena sana con
su dueño. Medido (`pairexact`, 43 estados del lector, 50.517 parejas): sin fallos. -/
def PairExact (g : GPathM) : Prop :=
  ∀ x nx w, g.node? x = some nx → w ∈ nx.owners → (g.node? w).isSome = true →
    ∃ sel, ChainSound g sel ∧ Fabric.Passes g sel x ∧ Fabric.Passes g sel w

open AbsSat.GraphPath.Model.PureDriverImproves (filterWeak) in
/-- **(W2): un nodo que posee un nodo pinchado sobrevive al pin y a la limpieza con parejas.** Por la
exactitud por parejas, el nodo `r` y el nodo `p` que posee están en una cadena sana de `g`; esa cadena
pasa por el nodo del mapa pinchado (el de `p`), así que sigue sana tras el pin débil
(`chainSound_filterWeak`) y tras `cleanPair` (`ChainSound_cleanPair`), y con ella `r`. -/
theorem survives_of_pinned_owner (g : GPathM) (hPE : PairExact g) (qid : NodeId)
    (r : PathNodeId) (nr : PNodeM) (hr : g.node? r = some nr)
    (p : PathNodeId) (hp : p ∈ nr.owners) (hpl : (g.node? p).isSome = true) (hpid : p.id = qid) :
    ((cleanPair (filterWeak g (p.id.step, [qid]))).node? r).isSome = true := by
  obtain ⟨sel, hC, ⟨i, hi0, hi1, hir⟩, ⟨j, hj0, hj1, hjp⟩⟩ := hPE r nr p hr hp hpl
  have hjs : (sel j).id.step = j := (hC.chain.1.1 j hj0 hj1).2
  have hjk : j = p.id.step := by rw [← hjs, hjp]
  have hX : ChainSound (filterWeak g (p.id.step, [qid])) sel :=
    PairHelly.chainSound_filterWeak g p.id.step qid sel hC (fun _ _ => by rw [← hjk, hjp, hpid])
  have hCP := ChainSound_cleanPair _ sel hX
  have hstep : (cleanPair (filterWeak g (p.id.step, [qid]))).current_step = g.current_step :=
    (pruned_cleanPair _).step_eq
  have := (hCP.chain.1.1 i hi0 (by rw [hstep]; exact hi1)).1
  rw [hir] at this
  exact this

/-- info: 'AbsSat.GraphPath.Model.OneStep.survives_of_pinned_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms survives_of_pinned_owner

end AbsSat.GraphPath.Model.OneStep
