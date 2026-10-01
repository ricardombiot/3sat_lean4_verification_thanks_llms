-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnTop.lean
import AbsSatBingo.Model.ForbidOnDriver
import AbsSatBingo.Model.ForbidOnSide

/-!
# El invariante de cimas con la regla activa: el veredicto bajo una hipótesis de nodos

El veredicto de la espina solo necesita que un estado final válido tenga una camarilla; no que toda cadena viva se
alargue (`LiveExt`). El invariante mínimo es **`TopAt g R`**: toda cima viva de `pinOn g R` está en una camarilla de
`pinOn g R` que esquiva sus tríos.

* **La llegada lo conserva sin hipótesis** (`topAt_arrival`): la cima tiene un padre en la llegada fijada (está
  cerrada); la pareja baja a la entrada fijada (dirección 2, `liveChain_down`), donde el padre es cima y está en una
  camarilla; esa camarilla sube con la cima (dirección 1, `ct_arrival_up`).
* **El join lo conserva bajo `TopSideAt`** (`topAt_join`): una cima viva de la unión fijada está viva en uno de sus
  dos lados fijados. Es el caso de un solo nodo de `PinSideAt` (`topSideAt_of_pinSideAt`), y se mide comparando cimas,
  sin recorrer cadenas.
* **El veredicto** (`spineVerdictOn_iff_of_topOn`): la espina `:on` decide la satisfacibilidad bajo `TopSideAt` en los
  joins de la máquina, para los pins de `PinsFrom`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

open Driver Machine MachineOn

-- ============================================================
-- Piezas
-- ============================================================

/-- `CT` solo mira la rama por debajo del paso actual. -/
theorem ct_congr {g : GPathB} {S S' : Int → PathNodeId} (h : CT g S)
    (he : ∀ k, 0 ≤ k → k < g.current_step → S' k = S k) : CT g S' := by
  obtain ⟨hc, hA, hns⟩ := h
  refine ⟨⟨fun k h0 h1 => by rw [he k h0 h1]; exact hc.step k h0 h1,
    fun k h0 h1 => by rw [he k h0 h1]; exact hc.alive k h0 h1,
    fun k l h0 h1 h2 h3 => by rw [he k h0 h1, he l h2 h3]; exact hc.adj k l h0 h1 h2 h3,
    fun h0 => by rw [he 0 (Int.le_refl 0) h0]; exact hc.root h0, ?_⟩, ?_, hns⟩
  · intro k h0 h1
    obtain ⟨n, hn, hp, hs⟩ := hc.node k h0 h1
    refine ⟨n, by rw [he k h0 h1]; exact hn, fun hk => ?_, fun hk => ?_⟩
    · rw [he (k - 1) (by omega) (by omega)]; exact hp hk
    · rw [he (k + 1) (by omega) hk]; exact hs hk
  · intro i j k h0 h1 h2 h3 h4 h5
    rw [he i h0 h1, he j h2 h3, he k h4 h5]
    exact hA i j k h0 h1 h2 h3 h4 h5

/-- **`TopAt`**: toda cima viva del estado fijado en `R` (válido) está en una camarilla suya que esquiva sus tríos. -/
def TopAt (g : GPathB) (R : List NodeId) : Prop :=
  (g.pinOn R).isValid = true → ∀ t ∈ (g.pinOn R).alive, t.id.step = g.current_step - 1 →
    ∃ D, CT (g.pinOn R) D ∧ D (g.current_step - 1) = t

/-- **`TopSideAt`**: toda cima viva de la unión fijada está viva en un lado fijado (válido). -/
def TopSideAt (A B : GPathB) (R : List NodeId) : Prop :=
  ((joinOn A B).pinOn R).isValid = true → ∀ t ∈ ((joinOn A B).pinOn R).alive, t.id.step = A.current_step - 1 →
    ((A.pinOn R).isValid = true ∧ t ∈ (A.pinOn R).alive) ∨ ((B.pinOn R).isValid = true ∧ t ∈ (B.pinOn R).alive)

/-- `TopSideAt` es el caso de un solo nodo de `PinSideAt`. -/
theorem topSideAt_of_pinSideAt {A B : GPathB} {R : List NodeId} (hcs : A.current_step = B.current_step)
    (hcs2 : 2 ≤ A.current_step) (h : PinSideAt A B R) : TopSideAt A B R := by
  intro hv t ht hts
  have hcsu : ((joinOn A B).pinOn R).current_step = A.current_step := (step_pinOn _ R).trans (step_joinOn A B)
  have hC : LiveChain ((joinOn A B).pinOn R) (TF ((joinOn A B).pinOn R)) (fun _ => t) (A.current_step - 1) :=
    ⟨⟨fun k hk1 hk2 => ⟨by rw [hcsu] at hk2; rw [hts]; omega, ht⟩, fun _ _ _ _ _ _ => adj_refl _ _ ht,
      fun k hk1 hk2 => by rw [hcsu] at hk2; omega⟩, fun a b c ha hab hbc hc => by rw [hcsu] at hc; omega⟩
  rcases h hv _ _ hC (by omega) (Int.le_refl _) with ⟨hvA, hA⟩ | ⟨hvB, hB⟩
  · exact Or.inl ⟨hvA, (hA.chain.node (A.current_step - 1) (Int.le_refl _)
      (by rw [step_pinOn]; exact Int.le_refl _)).2⟩
  · exact Or.inr ⟨hvB, (hB.chain.node (A.current_step - 1) (Int.le_refl _)
      (by rw [step_pinOn, hcs]; exact Int.le_refl _)).2⟩

/-- **El join `:on` conserva `TopAt` bajo `TopSideAt`.** -/
theorem topAt_join {A B : GPathB} {R : List NodeId} (hA : SInvB A) (hB : SInvB B) (hnsA : NoSelf A)
    (hnsB : NoSelf B) (hcs : A.current_step = B.current_step) (gA : TopAt A R) (gB : TopAt B R)
    (hs : TopSideAt A B R) : TopAt (joinOn A B) R := by
  intro hv t ht hts
  rw [step_joinOn] at hts ⊢
  rcases hs hv t ht hts with ⟨hvA, htA⟩ | ⟨hvB, htB⟩
  · obtain ⟨D, hct, hD⟩ := gA hvA t htA hts
    obtain ⟨hctA, hagr⟩ := ct_of_pinOn hA hnsA hct.1 hct.2.1
    exact ⟨D, ct_pinOn (ct_joinOn_left hctA hnsB) R (fun r hr => by rw [step_joinOn]; exact hagr r hr), hD⟩
  · obtain ⟨D, hct, hD⟩ := gB hvB t htB (by rw [← hcs]; exact hts)
    obtain ⟨hctB, hagr⟩ := ct_of_pinOn hB hnsB hct.1 hct.2.1
    exact ⟨D, ct_pinOn (ct_joinOn_right hcs hctB hnsA) R (fun r hr => by rw [step_joinOn, hcs]; exact hagr r hr),
      by rw [hcs]; exact hD⟩

section Arr

variable {E : GPathB} {reqs R : List NodeId} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **La llegada `:on` conserva `TopAt`**, sin hipótesis. -/
theorem topAt_arrival (hE : SInvB E) (hns : NoSelf E) (hndt : NoDegT E) (htb : TB E) (hlen : reqs.length ≤ 1)
    (hd : d.step = E.current_step) (hpos : 1 ≤ E.current_step) (hg : TopAt E (reqs ++ R)) :
    TopAt ((E.filterAllOn reqs).upOn d title forb) R := by
  intro hvh t hta hts
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
  have hts' : t.id.step = c := by rw [hts, hcsA]; omega
  -- la cima tiene un padre en la llegada fijada, que está cerrada
  have hcl : ClosedState h := closedState_pinOn hiA hvh (by rw [hcsA]; omega)
  obtain ⟨r, hrs, htr, _⟩ := hcl.pair (hcl.refl hta) (c - 1) (by omega) (by rw [hcsh]; omega)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hih.docs hta)
  have hne : t ≠ r := by intro e; rw [← e, hts'] at hrs; omega
  obtain ⟨p, hp, htp, _⟩ := hcl.par htr hne hn (by rw [hts']; exact hpos)
  have hps : p.id.step = c - 1 := by
    have := (hih.lstep n (node?_mem hn)).1 p hp
    rw [node?_id hn, hts'] at this; omega
  -- la pareja (padre, cima) es una cadena viva de la llegada fijada
  classical
  let C : Int → PathNodeId := fun k => if k = c - 1 then p else t
  have hCp : C (c - 1) = p := by simp [C]
  have hCt : C c = t := by
    have : ¬ c = c - 1 := by omega
    simp [C, this]
  have hC : LiveChain h (TF h) C (c - 1) := by
    refine ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩,
      fun a b c' ha hab hbc hc => by rw [hcsh] at hc; omega⟩
    · rw [hcsh] at h2
      rcases (show k = c - 1 ∨ k = c by omega) with rfl | rfl
      · rw [hCp]; exact ⟨hps, htp.2.1⟩
      · rw [hCt]; exact ⟨hts', hta⟩
    · rw [hcsh] at h2 h4
      rcases (show k = c - 1 ∨ k = c by omega) with rfl | rfl <;>
        rcases (show l = c - 1 ∨ l = c by omega) with rfl | rfl
      · rw [hCp]; exact adj_refl _ _ htp.2.1
      · rw [hCp, hCt]; exact (adj_symm h _ _).mp htp.2.2
      · rw [hCp, hCt]; exact htp.2.2
      · rw [hCt]; exact adj_refl _ _ hta
    · rw [hcsh] at h2
      have hk : k = c := by omega
      subst hk
      rw [hCt, hCp]
      exact ⟨n, hn, hp⟩
  -- el padre es cima viva de la entrada fijada
  have hX : LiveChain X (TF X) C (c - 1) := liveChain_down hE hns hndt hlen hd hpos hvh hC
  have hpX : p ∈ X.alive := by
    have := (hX.chain.node (c - 1) (Int.le_refl _) (by rw [hcsX]; exact Int.le_refl _)).2
    rw [hCp] at this; exact this
  have hvX : X.isValid = true := valid_down hE hns hndt hlen hd hpos hvh
  obtain ⟨D, hct, hD⟩ := hg hvX p hpX hps
  -- la camarilla sube con la cima
  let D' : Int → PathNodeId := fun k => if k = c then t else D k
  have hD't : D' c = t := by simp [D']
  have hD'p : D' (c - 1) = p := by
    have : ¬ c - 1 = c := by omega
    simp only [D', this, if_false]; exact hD
  have hct' : CT X D' := ct_congr hct (fun k _ hk => by
    rw [hcsX] at hk
    have : ¬ k = c := by omega
    simp [D', this])
  have hAv : Avoids (TF X) c D' := by have := hct'.2.1; rw [hcsX] at this; exact this
  refine ⟨D', ?_, by rw [hcsA, show c + 1 - 1 = c by omega]; exact hD't⟩
  exact ct_arrival_up hE hns htb hd hpos hvh hct'.1 hAv (by rw [hD't]; exact hts') (by rw [hD't]; exact hta)
    ⟨n, by rw [hD't]; exact hn, by rw [hD'p]; exact hp⟩

end Arr

-- ============================================================
-- El invariante de línea
-- ============================================================

/-- **El invariante de cimas de la línea `:on`** del paso `T`. -/
structure LInvTop (φ : Cnf) (T : Int) (line : Line) : Prop where
  on    : LineOn T line
  nodup : (line.map (·.1)).Nodup
  keys  : ∀ kv ∈ line, kv.1 ∈ mapNodes φ (T - 1)
  inv   : ∀ kv ∈ line, SInvB kv.2
  ndt   : ∀ kv ∈ line, NoDegT kv.2
  top   : ∀ kv ∈ line, ∀ R, PinsFrom φ kv.1 R → TopAt kv.2 R

theorem seedRow_alive :
    (GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)).alive = [{ id := ⟨0, 0⟩, parent_id := none, gparent_id := none }] := by
  rfl

/-- **El caso base**: la semilla; su única cima es la raíz, que está en la rama de cualquier asignación. -/
theorem lInvTop_init (φ : Cnf) : LInvTop φ 1 (initM .on φ) := by
  have h0 := lInvOn_init φ
  refine ⟨h0.on, h0.nodup, h0.keys, h0.inv, h0.ndt, ?_⟩
  obtain ⟨hl, g, hf, hct⟩ := initOn_inv φ (fun _ => false)
  rw [initM_eq] at hf
  let d : NodeId := ⟨0, 0⟩
  have hg : g = initSeedOn d "" := by
    have := List.mem_of_find?_eq_some hf
    rw [List.mem_singleton] at this
    exact (Prod.mk.inj this).2
  subst hg
  rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
  intro R _ hv t ht hts
  have hmem : (d, initSeedOn d "") ∈ initM .on φ := by rw [initM_eq]; exact List.mem_singleton_self _
  have hent := hl _ hmem
  have hstep : (initSeedOn d "").current_step = 1 := hent.1.step
  -- la raíz es el único vivo de la semilla
  have hsub : Sub (initSeedOn d "") (GPathB.empty.addNode d "" (fun _ => false)) :=
    sub_upOn_addNode (g := GPathB.empty) (by rfl)
  have huniq : ∀ q ∈ (initSeedOn d "").alive, q = { id := ⟨0, 0⟩, parent_id := none, gparent_id := none } := by
    intro q hq
    have := hsub.alive q hq
    rw [seedRow_alive] at this
    exact List.mem_singleton.mp this
  have hS0 : pidOfAssign φ (fun _ => false) 0 = t :=
    (huniq _ (hct.1.alive 0 (Int.le_refl 0) (by rw [hstep]; omega))).trans
      (huniq _ ((sub_pinOn _ R).alive t ht)).symm
  refine ⟨pidOfAssign φ (fun _ => false), ct_pinOn hct R (fun r hr h0' h1' => ?_), by rw [hstep]; exact hS0⟩
  rw [hstep] at h1'
  have hr0 : r.step = 0 := by omega
  rw [hr0, hS0]
  exact pinned_pinOn hent.1.docs hv r hr t ht (by rw [hts, hstep, hr0]; rfl)

/-- **`TopSideAt` en los joins de la máquina**, para los pins que la máquina usa desde el destino (`PinsFrom`). -/
def HTopOn (φ : Cnf) (line : Line) : Prop :=
  ∀ a ∈ line, ∀ b ∈ line, a.1 ≠ b.1 → ∀ d, SendsOn φ a d → SendsOn φ b d →
    ∀ R, PinsFrom φ d R → TopSideAt (arrOn φ a d) (arrOn φ b d) R

/-- Lo que se sabe de una llegada válida de una entrada de la línea. -/
theorem arrTop_facts {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    {kv : NodeId × GPathB} (hkv : kv ∈ line) {d : NodeId} (hs : SendsOn φ kv d) :
    EntOn (T + 1) d (arrOn φ kv d) ∧ SInvB (arrOn φ kv d) ∧ NoDegT (arrOn φ kv d) ∧
    (∀ R, PinsFrom φ d R → TopAt (arrOn φ kv d) R) ∧ d ∈ mapNodes φ T := by
  have hent := h.on kv hkv
  have hok := hent.1
  have hd : d.step = kv.2.current_step := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key, hok.step]; omega
  have hi := h.inv kv hkv
  have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by rw [step_filterAllOn]; exact hd
  refine ⟨entOn_upFilteringOn hent hs.1 hs.2,
    sInvB_upOn (sInvB_filterAllOn hi _) hdY (by rw [hd, hok.step]; omega),
    noDegT_upOn (noSelf_filterAllOn hent.2.1 _) (noDegT_filterAllOn hent.2.1 (h.ndt kv hkv) _),
    fun R hR => topAt_arrival hi hent.2.1 (h.ndt kv hkv) hent.2.2 (reqOf_length_le_one φ d) hd
      (by rw [hok.step]; exact hT) (h.top kv hkv _ (PinsFrom.cons hs.1 hR)), ?_⟩
  have hk : kv.1 ∈ mapNodes φ kv.1.step := by rw [hok.key]; exact h.keys kv hkv
  have := sonsOfMap_subset φ kv.1 hk d hs.1
  rw [hok.key, show T - 1 + 1 = T by omega] at this
  exact this

/-- **El paso de la máquina `:on`**: el invariante de cimas pasa a la línea siguiente bajo `HTopOn`. -/
theorem lInvTop_advance {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (hj : HTopOn φ line) : LInvTop φ (T + 1) (advanceM .on φ line) := by
  have hlen := line_cases h.nodup h.keys
  have ent : ∀ E ∈ advanceM .on φ line, SInvB E.2 ∧ NoDegT E.2 ∧ (∀ R, PinsFrom φ E.1 R → TopAt E.2 R) ∧
      E.1 ∈ mapNodes φ T := by
    intro E hE
    rcases entry_shapeOn hlen h.nodup hE with ⟨kv, hkv, hs, he⟩ | ⟨a, ha, b, hb, hab, hsa, hsb, he⟩
    · obtain ⟨_, hi, hn, hg, hk⟩ := arrTop_facts hT h hkv hs
      rw [he]; exact ⟨hi, hn, hg, hk⟩
    · obtain ⟨ea, ia, _, ga, hk⟩ := arrTop_facts hT h ha hsa
      obtain ⟨eb, ib, _, gb, _⟩ := arrTop_facts hT h hb hsb
      have hcs : (arrOn φ a E.1).current_step = (arrOn φ b E.1).current_step := ea.1.step.trans eb.1.step.symm
      have hjoin : doJoinOn (arrOn φ a E.1) (arrOn φ b E.1) = joinOn (arrOn φ a E.1) (arrOn φ b E.1) := by
        unfold doJoinOn okJoin
        rw [if_pos (by simp [ea.1.step, eb.1.step, ea.1.mp, eb.1.mp, ea.1.valid, eb.1.valid])]
      rw [he, hjoin]
      exact ⟨sInvB_joinOn ia ib hcs, noDegT_joinOn ea.2.1 eb.2.1 ia.edges ib.edges,
        fun R hR => topAt_join ia ib ea.2.1 eb.2.1 hcs (ga R hR) (gb R hR) (hj a ha b hb hab E.1 hsa hsb R hR), hk⟩
  exact ⟨lineOn_advance h.on, advanceOn_nodup φ line,
    fun E hE => by rw [show T + 1 - 1 = T by omega]; exact (ent E hE).2.2.2,
    fun E hE => (ent E hE).1, fun E hE => (ent E hE).2.1, fun E hE => (ent E hE).2.2.1⟩

/-- **La hipótesis de cimas**: en cada línea de la máquina `:on`, `TopSideAt` en sus joins, para los pins de `PinsFrom`. -/
def HypsTopOn (φ : Cnf) : Prop := ∀ n : Nat, HTopOn φ (stepsM .on φ n (initM .on φ))

theorem lInvTop_steps {φ : Cnf} (H : HypsTopOn φ) :
    ∀ n : Nat, LInvTop φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero => exact lInvTop_init φ
  | succ n ih =>
    rw [stepsM_succ]
    have := lInvTop_advance (by omega) ih (H n)
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

/-- La hipótesis de cadenas da la de cimas. -/
theorem hypsTopOn_of_joinOn {φ : Cnf} (H : HypsJoinOn φ) : HypsTopOn φ := by
  intro n a ha b hb hab d hsa hsb R hR
  have hl := lInvOn_steps H n
  obtain ⟨ea, _⟩ := arrOn_facts (by omega) hl ha hsa
  obtain ⟨eb, _⟩ := arrOn_facts (by omega) hl hb hsb
  exact topSideAt_of_pinSideAt (ea.1.step.trans eb.1.step.symm) (by rw [ea.1.step]; omega)
    (H n a ha b hb hab d hsa hsb R hR)

end GPathB

namespace MachineOn

open GPathB Driver Machine Struct

/-- **La espina con la regla activa decide la satisfacibilidad** bajo `TopSideAt` en los joins de la máquina: toda cima
viva de una unión fijada está viva en una de sus dos llegadas fijadas, para los pins que la máquina usa. Una hipótesis
de nodos, no de cadenas. -/
theorem spineVerdictOn_iff_of_topOn {φ : Cnf} (hbd : Bounded φ) (H : HypsTopOn φ) :
    SpineVerdictOn φ ↔ Satisfiable φ := by
  constructor
  · rintro ⟨kv, hkv, hval⟩
    obtain ⟨hlo, hls⟩ := lineOn_run_shape hbd
    have hent := hlo kv hkv
    have hsh := hls kv hkv
    have hsc : 2 ≤ stepCount φ := by unfold stepCount; omega
    have hcs0 : kv.2.current_step = stepCount φ := hent.1.step
    have hval' : (kv.2.pinOn []).isValid = true := hval
    have hcs : (kv.2.pinOn []).current_step = stepCount φ := (step_pinOn kv.2 []).trans hcs0
    obtain ⟨t, ht, hts⟩ := exists_alive_at hval' (k := stepCount φ - 1) (by omega) (by rw [hcs]; omega)
    obtain ⟨S, hct, _⟩ := (lInvTop_steps H (stepCount φ - 1).toNat).top kv hkv [] (PinsFrom.nil _) hval' t ht
      (by rw [hts, hcs0])
    have hstr : Struct φ (kv.2.pinOn []) :=
      struct_of_sub (sub_pinOn kv.2 []) ⟨hsh.2.2.1.pmp, hsh.2.2.1.gpmp, hsh.2.2.1.noforb, hsh.2.2.1.onmap,
        hsh.2.2.1.req⟩
    exact ⟨Decode.decode S, Decode.sat_of_carried hbd hstr hct.1 hcs⟩
  · rintro ⟨a, ha⟩
    obtain ⟨g, hf, hct, _⟩ := run_carriesOn hbd a ha
    refine ⟨_, List.mem_of_find?_eq_some hf, ?_⟩
    exact isValid_of_carried (ct_reviewOn (ct_dirty hct true)).1

end MachineOn

end AbsSatBingo.Model
