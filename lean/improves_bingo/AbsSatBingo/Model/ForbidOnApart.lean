-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnApart.lean
import AbsSatBingo.Model.ForbidOnFam

/-!
# Vecinos distintos, pasos distintos; y las dos primeras líneas sin hipótesis

`AdjApart g`: dos nodos distintos vecinos en `g` están en pasos distintos. La fila nueva solo crea aristas hacia pasos
anteriores, el join une y el review quita, así que es un invariante de la máquina (`arrOn_adjApart`,
`lineAp_advance`).

Con él, en un estado de **tres pasos** `StarDAt` es trivial (`starDAt_of_le3`): los vecinos de la cima ocupan pasos
distintos por debajo de ella, así que una cara `(a, b, t)` llena los tres pasos (el testigo en cada paso es uno de sus
nodos) y no caben los tres nodos de una base. Los joins de la segunda línea son estados de tres pasos, de modo que
`StarDAt` vale allí sin hipótesis (`hStarDOn_line1`).

Queda `HypsStarDLowOn` reducida a su parte desde la tercera línea (`hypsStarDLowOn_of_low`,
`spineVerdictOn_iff_of_starDLowOnly`).

Y otra forma de la hipótesis, separada por pins (`HStarPinOn`, `spineVerdictOn_iff_of_starPin`): con pins basta
`StarTriAt`, y sin pins se pide `TopSideAt` directamente.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Driver Machine MachineOn

-- ============================================================
-- El invariante
-- ============================================================

/-- **Dos vecinos distintos están en pasos distintos.** -/
def AdjApart (g : GPathB) : Prop := ∀ y w, g.Adj y w → y.id.step = w.id.step → y = w

theorem adjApart_of_sub {h g : GPathB} (hs : Sub h g) (hg : AdjApart g) : AdjApart h :=
  fun y w h1 h2 => hg y w (hs.adj _ _ h1) h2

theorem adjApart_join {e g : GPathB} (he : AdjApart e) (hg : AdjApart g) : AdjApart (join e g) := by
  intro y w h h2
  rcases adj_join_cases h with h | h
  · exact he y w h h2
  · exact hg y w h h2

theorem adjApart_setT {g : GPathB} (hg : AdjApart g) (T : List (PathNodeId × PathNodeId × PathNodeId)) :
    AdjApart (g.setT T) := fun y w h h2 => hg y w h h2

/-- La fila nueva solo crea aristas de un nodo nuevo a nodos de pasos anteriores. -/
theorem adjApart_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool} (hg : AdjApart g) :
    AdjApart (g.addNode d title forb) := by
  intro x s h h2
  rw [adj_iff] at h
  rcases h with ⟨rfl, _⟩ | ⟨e, he, hj⟩
  · rfl
  · rcases List.mem_append.mp he with hold | hnew
    · exact hg x s ((adj_iff g x s).mpr (Or.inr ⟨e, hold, hj⟩)) h2
    · exfalso
      obtain ⟨pid, _, he'⟩ := List.mem_flatMap.mp hnew
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp he'
      have ⟨_, hw2⟩ := List.mem_filter.mp hw'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw2
      obtain ⟨hlt, _⟩ := hw2
      rcases hj with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have e1 : pid = x := e1
        have e2 : w' = s := e2
        subst e1; subst e2
        omega
      · have e1 : pid = s := e1
        have e2 : w' = x := e2
        subst e1; subst e2
        omega

/-- La llegada `:on` conserva `AdjApart`. -/
theorem arrOn_adjApart {φ : Cnf} {kv : NodeId × GPathB} (hap : AdjApart kv.2) {d : NodeId} (hs : SendsOn φ kv d) :
    AdjApart (arrOn φ kv d) := by
  have hvY : (kv.2.filterAllOn (reqOf φ d)).isValid = true :=
    valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
  have hapY : AdjApart (kv.2.filterAllOn (reqOf φ d)) :=
    adjApart_of_sub (shrinks_filterAllOn kv.2 (reqOf φ d)).1 hap
  obtain ⟨T', hT'⟩ := upOn_eq (g := kv.2.filterAllOn (reqOf φ d)) (d := d) (title := "") (forb := isProhibited φ) hvY
  have e : arrOn φ kv d = (((kv.2.filterAllOn (reqOf φ d)).addNode d "" (isProhibited φ)).setT T').reviewOn := hT'
  rw [e]
  exact adjApart_of_sub (shrinks_reviewOn _).1 (adjApart_setT (adjApart_addNode hapY) T')

/-- `AdjApart` en todas las entradas de una línea. -/
def LineAp (line : Line) : Prop := ∀ kv ∈ line, AdjApart kv.2

theorem lineAp_init (φ : Cnf) : LineAp (initM .on φ) := by
  rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
  obtain ⟨T', hT'⟩ := upOn_eq (g := GPathB.empty) (d := (⟨0, 0⟩ : NodeId)) (title := "")
    (forb := fun _ => false) (by rfl)
  have e : initSeedOn (⟨0, 0⟩ : NodeId) "" = ((GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)).setT T').reviewOn :=
    hT'
  show AdjApart (initSeedOn (⟨0, 0⟩ : NodeId) "")
  rw [e]
  have h0 : AdjApart GPathB.empty := fun y w h _ => (empty_noAdj h).elim
  exact adjApart_of_sub (shrinks_reviewOn _).1 (adjApart_setT (adjApart_addNode h0) T')

theorem lineAp_advance {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (hap : LineAp line) : LineAp (advanceM .on φ line) := by
  intro E hE
  rcases entry_shapeOn (line_cases h.nodup h.keys) h.nodup hE with ⟨kv, hkv, hs, he⟩ |
    ⟨a, ha, b, hb, _, hsa, hsb, he⟩
  · rw [he]; exact arrOn_adjApart (hap kv hkv) hs
  · obtain ⟨ea, _⟩ := arrTop_facts hT h ha hsa
    obtain ⟨eb, _⟩ := arrTop_facts hT h hb hsb
    have hjoin : doJoinOn (arrOn φ a E.1) (arrOn φ b E.1) = joinOn (arrOn φ a E.1) (arrOn φ b E.1) := by
      unfold doJoinOn okJoin
      rw [if_pos (by simp [ea.1.step, eb.1.step, ea.1.mp, eb.1.mp, ea.1.valid, eb.1.valid])]
    obtain ⟨T', hT'⟩ := joinOn_eq (arrOn φ a E.1) (arrOn φ b E.1)
    rw [he, hjoin, hT']
    exact adjApart_setT (adjApart_join (arrOn_adjApart (hap a ha) hsa) (arrOn_adjApart (hap b hb) hsb)) T'

-- ============================================================
-- Un estado de tres pasos
-- ============================================================

/-- **En una unión de tres pasos `StarDAt` es trivial**: los vecinos de la cima están en pasos distintos por debajo de
ella, así que cada cara llena los tres pasos y no hay bases. -/
theorem starDAt_of_le3 {S J : GPathB} {Rp : List NodeId} (hJ : SInvB J) (hap : AdjApart J)
    (hc : J.current_step ≤ 3) : StarDAt S J Rp := by
  intro _ t ht hts _
  have hiu : SInvB (J.pinOn Rp) := sInvB_pinOn hJ Rp
  have hapu : AdjApart (J.pinOn Rp) := adjApart_of_sub (sub_pinOn J Rp) hap
  have usymm : ∀ {y w}, (J.pinOn Rp).Adj y w → (J.pinOn Rp).Adj w y := fun h => (adj_symm _ _ _).mp h
  -- los pasos de un vivo
  have rng : ∀ {q : PathNodeId}, q ∈ (J.pinOn Rp).alive → 0 ≤ q.id.step ∧ q.id.step < J.current_step := by
    intro q hq
    have h1 := alive_below hiu.docs hiu.below hq
    rw [step_pinOn] at h1
    obtain ⟨n, hn, hnid⟩ := hiu.docs q hq
    have h2 := hiu.zero n hn
    rw [hnid] at h2
    exact ⟨h2, h1⟩
  have ne : ∀ {y w : PathNodeId}, (J.pinOn Rp).Adj y w → y ≠ w → y.id.step ≠ w.id.step :=
    fun h hne e => hne (hapu _ _ h e)
  constructor
  · intro a b hat hbt nab hta htb hab _ l h0 h1
    have haa := (hiu.edges t a hta).2
    have hba := (hiu.edges t b htb).2
    have r1 := rng haa
    have r2 := rng hba
    have n1 := ne hta (Ne.symm hat)
    have n2 := ne htb (Ne.symm hbt)
    have n3 := ne hab nab
    by_cases la : l = a.id.step
    · exact ⟨a, la.symm, adj_refl _ a haa, usymm hab, hta, Or.inl rfl⟩
    by_cases lb : l = b.id.step
    · exact ⟨b, lb.symm, hab, adj_refl _ b hba, htb, Or.inr (Or.inl rfl)⟩
    by_cases lt : l = t.id.step
    · exact ⟨t, lt.symm, usymm hta, usymm htb, adj_refl _ t ht, Or.inr (Or.inr (Or.inl rfl))⟩
    exfalso
    omega
  · intro a b r ⟨nat, nbt, nrt, nab, nar, nbr, hta, htb, htr, hab, har, hbr, _⟩ _ _
    exfalso
    have r1 := rng (hiu.edges t a hta).2
    have r2 := rng (hiu.edges t b htb).2
    have r3 := rng (hiu.edges t r htr).2
    have n1 := ne hta (Ne.symm nat)
    have n2 := ne htb (Ne.symm nbt)
    have n3 := ne htr (Ne.symm nrt)
    have n4 := ne hab nab
    have n5 := ne har nar
    have n6 := ne hbr nbr
    omega

-- ============================================================
-- La segunda línea, sin hipótesis
-- ============================================================

/-- **`StarDAt` en los joins de la segunda línea**, sin hipótesis: son uniones de tres pasos. -/
theorem hStarDOn_line1 (φ : Cnf) : HStarDOn φ (advanceM .on φ (initM .on φ)) := by
  have hT : (1 : Int) ≤ 1 := by omega
  have hT1 : (1 : Int) ≤ 1 + 1 := by omega
  have hl0 := lInvTop_init φ
  have hbk0 := lineBk_init φ
  have hl1 := lInvTop_advance hT hl0 (hTopOn_of_starD hT hl0 hbk0 (hStarDOn_init φ))
  have hap1 := lineAp_advance hT hl0 (lineAp_init φ)
  intro a ha b hb _ d hsa hsb R _
  obtain ⟨ea, ia, _, _, _⟩ := arrTop_facts hT1 hl1 ha hsa
  obtain ⟨eb, ib, _, _, _⟩ := arrTop_facts hT1 hl1 hb hsb
  have hJ : SInvB (joinOn (arrOn φ a d) (arrOn φ b d)) := sInvB_joinOn ia ib (ea.1.step.trans eb.1.step.symm)
  obtain ⟨T', hT'⟩ := joinOn_eq (arrOn φ a d) (arrOn φ b d)
  have hapJ : AdjApart (joinOn (arrOn φ a d) (arrOn φ b d)) := by
    rw [hT']
    exact adjApart_setT (adjApart_join (arrOn_adjApart (hap1 a ha) hsa) (arrOn_adjApart (hap1 b hb) hsb)) T'
  have hc : (joinOn (arrOn φ a d) (arrOn φ b d)).current_step ≤ 3 := by
    rw [step_joinOn, ea.1.step]; omega
  exact ⟨starDAt_of_le3 hJ hapJ hc, starDAt_of_le3 hJ hapJ hc⟩

/-- **`HypsStarDLowOn` sale de su parte desde la tercera línea.** -/
theorem hypsStarDLowOn_of_low {φ : Cnf}
    (hn : ∀ n : Nat, HStarDLowOn φ (advanceM .on φ (advanceM .on φ (stepsM .on φ n (initM .on φ))))) :
    HypsStarDLowOn φ :=
  ⟨hStarDOn_init φ, hStarDOn_line1 φ, hn⟩

-- ============================================================
-- Con pins, `StarTriAt`; sin pins, `TopSideAt` directamente
-- ============================================================

/-- **La hipótesis separada por pins.** En cada join de la línea y para cada lista de pins de `PinsFrom`:

* sin pins (`R = []`): `TopSideAt`, es decir, una cima viva de la unión revisada está viva en su lado revisado;
* con pins (`R ≠ []`): `StarTriAt` en los dos lados, es decir, una base viva en la unión fijada bajo una cima con sus
  tres caras vivas no está en los tríos del lado fijado.

`StarTriAt` es falsa sin pins en `v7` (una base prohibida en un lado revive en la unión), pero ahí no hace falta: los
fallos medidos están todos en uniones sin pins (`probe_topdead.jl`, columnas `rev`, `revP` frente a `p_rev`,
`p_revP`). -/
def HStarPinOn (φ : Cnf) (line : Line) : Prop :=
  ∀ a ∈ line, ∀ b ∈ line, a.1 ≠ b.1 → ∀ d, SendsOn φ a d → SendsOn φ b d → ∀ R, PinsFrom φ d R →
    (R = [] → TopSideAt (arrOn φ a d) (arrOn φ b d) []) ∧
    (R ≠ [] → StarTriAt (arrOn φ a d) (joinOn (arrOn φ a d) (arrOn φ b d)) R ∧
      StarTriAt (arrOn φ b d) (joinOn (arrOn φ a d) (arrOn φ b d)) R)

theorem hTopOn_of_starPin {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (hbk : LineBk line) (hp : HStarPinOn φ line) : HTopOn φ line := by
  intro a ha b hb hab d hsa hsb R hR
  obtain ⟨h0, h1⟩ := hp a ha b hb hab d hsa hsb R hR
  by_cases hR0 : R = []
  · rw [hR0]; exact h0 hR0
  · obtain ⟨ea, ia, na, _, _⟩ := arrTop_facts hT h ha hsa
    obtain ⟨eb, ib, nb, _, _⟩ := arrTop_facts hT h hb hsb
    obtain ⟨fa, _⟩ := arrOn_tops hT (h.on a ha) (hbk a ha).1 hsa
    obtain ⟨fb, _⟩ := arrOn_tops hT (h.on b hb) (hbk b hb).1 hsb
    obtain ⟨pa, _⟩ := arrOn_adjPar (h.on a ha) (h.inv a ha) (hbk a ha).2.1 (hbk a ha).2.2 hsa
    obtain ⟨pb, _⟩ := arrOn_adjPar (h.on b hb) (h.inv b hb) (hbk b hb).2.1 (hbk b hb).2.2 hsb
    obtain ⟨hsA, hsB⟩ := h1 hR0
    exact topSideAt_of_starTri ia ib ea.2.1 eb.2.1 na nb (ea.1.step.trans eb.1.step.symm) (by rw [ea.1.step]; omega)
      hab fa fb pa pb hsA hsB

/-- **La hipótesis separada por pins**, en cada línea de la máquina `:on`. -/
def HypsStarPinOn (φ : Cnf) : Prop := ∀ n : Nat, HStarPinOn φ (stepsM .on φ n (initM .on φ))

theorem hypsTopOn_of_starPin {φ : Cnf} (H : HypsStarPinOn φ) : HypsTopOn φ := by
  have hs := lInvBk_steps (φ := φ) (fun n hl hbk => hTopOn_of_starPin (by omega) hl hbk (H n))
  exact fun n => hTopOn_of_starPin (by omega) (hs n).1 (hs n).2 (H n)

end GPathB

namespace MachineOn

open GPathB Driver

/-- **El veredicto desde la parte baja, sin las dos primeras líneas**: la espina `:on` decide la satisfacibilidad si,
en los joins de la máquina desde la tercera línea, vale `StarDAt` por debajo del paso de los padres de cada cima y no
hay padres complementarios sobre bases vivas. Las dos primeras líneas están demostradas (`hStarDOn_init`,
`hStarDOn_line1`). -/
theorem spineVerdictOn_iff_of_starDLowOnly {φ : Cnf} (hbd : Bounded φ)
    (H : ∀ n : Nat, HStarDLowOn φ (advanceM .on φ (advanceM .on φ (stepsM .on φ n (initM .on φ))))) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_starDLow hbd (hypsStarDLowOn_of_low H)

/-- **El veredicto con la hipótesis separada por pins**: la espina `:on` decide la satisfacibilidad si, en los joins de
la máquina, sin pins una cima viva de la unión revisada está viva en su lado revisado, y con pins una base viva en la
unión fijada bajo una cima con sus tres caras vivas no está en los tríos del lado fijado. -/
theorem spineVerdictOn_iff_of_starPin {φ : Cnf} (hbd : Bounded φ) (H : HypsStarPinOn φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_topOn hbd (hypsTopOn_of_starPin H)

end MachineOn

end AbsSatBingo.Model
