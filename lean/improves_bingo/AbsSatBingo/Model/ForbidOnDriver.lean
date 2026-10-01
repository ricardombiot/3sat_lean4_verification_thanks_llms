-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnDriver.lean
import AbsSatBingo.Model.ForbidOnGood
import AbsSatBingo.Model.LiveDriver

/-!
# La inducción de línea con la regla activa: el veredicto bajo el join

El análogo `:on` de `LiveDriver`, sin familias fantasma: la relación de tríos de cada estado es la suya (`TF`).

* **La entrada de una clave tras `advanceM .on`** es una sola llegada o la unión de las llegadas de dos remitentes
  (`entry_shapeOn`).
* **El invariante de línea** (`LInvOn`): contabilidad (`LineOn`, `SInvB`, `NoDegT`) y `GoodOn` en cada entrada.
* **El paso**: las entradas de una llegada, por `good_arrivalOn`, sin hipótesis; las de dos, por `good_joinOn`, bajo
  `PinSideAt` entre las dos llegadas (`HJoinOn`).
* **El veredicto** (`spineVerdictOn_iff_of_joinOn`): la espina `:on` decide la satisfacibilidad bajo `PinSideAt` en los
  joins de la máquina, y nada más; solo para los pins que la máquina usa de verdad (`PinsFrom`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Driver Machine MachineOn

-- ============================================================
-- La entrada de una clave tras `advanceM .on`
-- ============================================================

/-- La llegada `:on` de una entrada de la línea a un destino. -/
def arrOn (φ : Cnf) (kv : NodeId × GPathB) (d : NodeId) : GPathB :=
  kv.2.upFilteringOn (reqOf φ d) d "" (isProhibited φ)

/-- La entrada `kv` envía a `d` y su llegada `:on` es válida. -/
def SendsOn (φ : Cnf) (kv : NodeId × GPathB) (d : NodeId) : Prop :=
  d ∈ sonsOfMap φ kv.1 ∧ (arrOn φ kv d).isValid = true

instance (φ : Cnf) (kv : NodeId × GPathB) (d : NodeId) : Decidable (SendsOn φ kv d) := by
  unfold SendsOn; infer_instance

/-- Un paso del pliegue de las llegadas `:on` a `d`. -/
def stepSOn (φ : Cnf) (d : NodeId) (o : Option GPathB) (kv : NodeId × GPathB) : Option GPathB :=
  if SendsOn φ kv d then
    some (match o with
      | none => arrOn φ kv d
      | some e => doJoinOn e (arrOn φ kv d))
  else o

theorem lookup_insertOn (l : Line) (key : NodeId) (g : GPathB) (d : NodeId) :
    lookup (insertM .on l key g) d =
      if key = d then some (match lookup l d with
        | none => g
        | some e => doJoinOn e g)
      else lookup l d := by
  unfold insertM lookup
  split
  · rename_i k' e hfind
    have hk' : k' = key := by simpa using List.find?_some hfind
    subst hk'
    rw [List.find?_map]
    by_cases hkd : k' = d
    · subst hkd
      rw [if_pos rfl]
      have : ((fun kv : NodeId × GPathB => kv.1 == k') ∘
          fun kv => if (kv.1 == k') = true then (k', doJoinM .on e g) else kv) = fun kv => kv.1 == k' := by
        funext kv; simp only [Function.comp]; split <;> simp_all
      rw [this, hfind]
      simp [doJoinM]
    · rw [if_neg hkd]
      have : ((fun kv : NodeId × GPathB => kv.1 == d) ∘
          fun kv => if (kv.1 == k') = true then (k', doJoinM .on e g) else kv) = fun kv => kv.1 == d := by
        funext kv; simp only [Function.comp]; split
        · rename_i h; rw [beq_iff_eq.mp h]
        · rfl
      rw [this]
      cases hf : l.find? (fun kv => kv.1 == d) with
      | none => rfl
      | some x =>
        have hx : x.1 = d := by simpa using List.find?_some hf
        simp only [Option.map_some, Option.some.injEq]
        rw [if_neg (by rw [hx]; simpa using Ne.symm hkd)]
  · rename_i hnone
    rw [List.find?_append]
    by_cases hkd : key = d
    · subst hkd
      rw [if_pos rfl, hnone]
      simp
    · rw [if_neg hkd]
      have : [(key, g)].find? (fun kv => kv.1 == d) = none := by simp [hkd]
      rw [this, Option.or_none]

theorem lookup_sendToOn (φ : Cnf) (kv : NodeId × GPathB) (next : Line) (d' d : NodeId) :
    lookup (sendToM .on φ kv.2 next d') d =
      if d' = d ∧ (arrOn φ kv d').isValid = true then some (match lookup next d with
        | none => arrOn φ kv d'
        | some e => doJoinOn e (arrOn φ kv d'))
      else lookup next d := by
  unfold sendToM
  dsimp only
  by_cases hv : (arrOn φ kv d').isValid = true
  · have hv' : (upFilteringM .on kv.2 (reqOf φ d') d' "" (isProhibited φ)).isValid = true := hv
    rw [if_pos hv', lookup_insertOn]
    by_cases hd : d' = d
    · rw [if_pos hd, if_pos ⟨hd, hv⟩]; rfl
    · rw [if_neg hd, if_neg (fun h => hd h.1)]
  · have hv' : ¬ (upFilteringM .on kv.2 (reqOf φ d') d' "" (isProhibited φ)).isValid = true := hv
    rw [if_neg hv', if_neg (fun h => hv h.2)]

theorem lookup_foldl_sendToOn (φ : Cnf) (kv : NodeId × GPathB) (d : NodeId) :
    ∀ (ss : List NodeId) (next : Line), ss.Nodup →
      lookup (ss.foldl (sendToM .on φ kv.2) next) d =
        if d ∈ ss ∧ (arrOn φ kv d).isValid = true then some (match lookup next d with
          | none => arrOn φ kv d
          | some e => doJoinOn e (arrOn φ kv d))
        else lookup next d := by
  intro ss
  induction ss with
  | nil => intro next _; simp
  | cons s rest ih =>
    intro next hnd
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons, ih _ hnd.2, lookup_sendToOn]
    by_cases hsd : s = d
    · subst hsd
      have hnr : s ∉ rest := hnd.1
      simp only [hnr, false_and, if_false, true_and, List.mem_cons_self]
    · have hne : ¬ (s = d ∧ (arrOn φ kv s).isValid = true) := fun h => hsd h.1
      rw [if_neg hne]
      by_cases hr : d ∈ rest ∧ (arrOn φ kv d).isValid = true
      · rw [if_pos hr, if_pos ⟨List.mem_cons_of_mem _ hr.1, hr.2⟩]
      · rw [if_neg hr, if_neg]
        rintro ⟨hm, hv⟩
        rcases List.mem_cons.mp hm with h | h
        · exact hsd h.symm
        · exact hr ⟨h, hv⟩

theorem lookup_sendAllOn (φ : Cnf) (kv : NodeId × GPathB) (next : Line) (d : NodeId) :
    lookup (sendAllM .on φ kv next) d = stepSOn φ d (lookup next d) kv := by
  unfold sendAllM stepSOn SendsOn
  rw [lookup_foldl_sendToOn φ kv d _ next (sonsOfMap_nodup φ kv.1)]

/-- **La entrada de `d` tras `advanceM .on`** es el pliegue de las llegadas válidas a `d`. -/
theorem lookup_advanceOn (φ : Cnf) (line : Line) (d : NodeId) :
    lookup (advanceM .on φ line) d = line.foldl (stepSOn φ d) none := by
  unfold advanceM
  have : ∀ (l : Line) (next : Line), lookup (l.foldl (fun next kv => sendAllM .on φ kv next) next) d =
      l.foldl (stepSOn φ d) (lookup next d) := by
    intro l
    induction l with
    | nil => intro next; rfl
    | cons kv rest ih => intro next; rw [List.foldl_cons, List.foldl_cons, ih, lookup_sendAllOn]
  rw [this]; rfl

theorem nodup_insertOn {line : Line} {key : NodeId} {g : GPathB} (hl : (line.map (·.1)).Nodup) :
    ((insertM .on line key g).map (·.1)).Nodup := by
  unfold insertM
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    rw [List.map_map]
    have : ((·.1) ∘ fun kv : NodeId × GPathB => if (kv.1 == key) = true then (key, doJoinM .on e g) else kv) =
        (·.1 : NodeId × GPathB → NodeId) := by
      funext kv; simp only [Function.comp]; split
      · rename_i h; exact (beq_iff_eq.mp h).symm
      · rfl
    rw [this]; exact hl
  · rename_i hnone
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hl, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb hab
    rw [List.map_singleton, List.mem_singleton] at hb
    subst hb; subst hab
    obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp ha
    have := List.find?_eq_none.mp hnone kv hkv
    simp at this

/-- **Las claves de `advanceM .on` son únicas.** -/
theorem advanceOn_nodup (φ : Cnf) (line : Line) : ((advanceM .on φ line).map (·.1)).Nodup := by
  unfold advanceM
  refine foldl_pres _ (fun next : Line => (next.map (·.1)).Nodup) line ?_ [] List.nodup_nil
  intro next kv _ hn
  unfold sendAllM
  refine foldl_pres _ (fun next : Line => (next.map (·.1)).Nodup) _ ?_ next hn
  intro y d _ hy
  unfold sendToM
  dsimp only
  split
  · exact nodup_insertOn hy
  · exact hy

/-- **La forma de una entrada de `advanceM .on`**: una sola llegada o la unión de las llegadas de dos remitentes. -/
theorem entry_shapeOn {φ : Cnf} {line : Line}
    (hlen : line = [] ∨ (∃ a, line = [a]) ∨ (∃ a b, line = [a, b])) (hnd : (line.map (·.1)).Nodup)
    {E : NodeId × GPathB} (hE : E ∈ advanceM .on φ line) :
    (∃ kv ∈ line, SendsOn φ kv E.1 ∧ E.2 = arrOn φ kv E.1) ∨
    (∃ a ∈ line, ∃ b ∈ line, a.1 ≠ b.1 ∧ SendsOn φ a E.1 ∧ SendsOn φ b E.1 ∧
      E.2 = doJoinOn (arrOn φ a E.1) (arrOn φ b E.1)) := by
  have h1 := lookup_of_mem (advanceOn_nodup φ line) hE
  rw [lookup_advanceOn] at h1
  rcases hlen with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · simp at h1
  · by_cases ha : SendsOn φ a E.1
    · simp only [List.foldl, stepSOn, ha, if_true, Option.some.injEq] at h1
      exact Or.inl ⟨a, by simp, ha, h1.symm⟩
    · simp [List.foldl, stepSOn, ha] at h1
  · have hab : a.1 ≠ b.1 := by simpa using hnd
    by_cases ha : SendsOn φ a E.1 <;> by_cases hb : SendsOn φ b E.1
    · simp only [List.foldl, stepSOn, ha, hb, if_true, Option.some.injEq] at h1
      exact Or.inr ⟨a, by simp, b, by simp, hab, ha, hb, h1.symm⟩
    · simp only [List.foldl, stepSOn, ha, hb, if_true, if_false, Option.some.injEq] at h1
      exact Or.inl ⟨a, by simp, ha, h1.symm⟩
    · simp only [List.foldl, stepSOn, ha, hb, if_true, if_false, Option.some.injEq] at h1
      exact Or.inl ⟨b, by simp, hb, h1.symm⟩
    · simp [List.foldl, stepSOn, ha, hb] at h1

-- ============================================================
-- El invariante de línea
-- ============================================================

/-- **Los pins que la máquina usa de verdad** desde el nodo de mapa `k`: los requisitos de un camino del mapa que sale
de `k`, concatenados. El veredicto solo mira `R = []` en la línea final, y cada llegada a `d` pide a su remitente
`reqOf φ d ++ R`. -/
inductive PinsFrom (φ : Cnf) : NodeId → List NodeId → Prop
  | nil (k : NodeId) : PinsFrom φ k []
  | cons {k d : NodeId} {R : List NodeId} : d ∈ sonsOfMap φ k → PinsFrom φ d R → PinsFrom φ k (reqOf φ d ++ R)

/-- **El invariante de la línea `:on`** del paso `T`. -/
structure LInvOn (φ : Cnf) (T : Int) (line : Line) : Prop where
  on    : LineOn T line
  nodup : (line.map (·.1)).Nodup
  keys  : ∀ kv ∈ line, kv.1 ∈ mapNodes φ (T - 1)
  inv   : ∀ kv ∈ line, SInvB kv.2
  ndt   : ∀ kv ∈ line, NoDegT kv.2
  good  : ∀ kv ∈ line, ∀ R, PinsFrom φ kv.1 R → GoodAt kv.2 R

/-- **El caso base**: la semilla. -/
theorem lInvOn_init (φ : Cnf) : LInvOn φ 1 (initM .on φ) := by
  have hl := (initOn_inv φ (fun _ => false)).1
  let d : NodeId := ⟨0, 0⟩
  have hmem : (d, initSeedOn d "") ∈ initM .on φ := by rw [initM_eq]; exact List.mem_singleton_self _
  have hstep : (initSeedOn d "").current_step = 1 := (hl _ hmem).1.step
  have hns0 : NoSelf GPathB.empty := fun _ he => absurd he List.not_mem_nil
  refine ⟨hl, by rw [initM_eq]; simp, ?_, ?_, ?_, ?_⟩
  · rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    rw [show (1 : Int) - 1 = 0 by omega, mapNodes_fusion φ 0 (Or.inl rfl)]
    exact List.mem_singleton_self _
  · rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    exact sInvB_upOn (g := GPathB.empty) (d := d) (title := "") (forb := fun _ => false) sInvB_empty (by rfl)
      (by decide)
  · rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    exact noDegT_upOn (g := GPathB.empty) (d := d) (title := "") (forb := fun _ => false) hns0
      (fun _ ht => absurd ht List.not_mem_nil)
  · rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    exact fun R _ _ => liveExt_small (by rw [step_pinOn, hstep]; omega)

/-- **`PinSideAt` en los joins de la máquina**: en cada destino `d`, entre las llegadas de dos remitentes, para los
pins que la máquina usa desde `d` (`PinsFrom`). -/
def HJoinOn (φ : Cnf) (line : Line) : Prop :=
  ∀ a ∈ line, ∀ b ∈ line, a.1 ≠ b.1 → ∀ d, SendsOn φ a d → SendsOn φ b d →
    ∀ R, PinsFrom φ d R → PinSideAt (arrOn φ a d) (arrOn φ b d) R

/-- Lo que se sabe de una llegada válida de una entrada de la línea. -/
theorem arrOn_facts {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvOn φ T line)
    {kv : NodeId × GPathB} (hkv : kv ∈ line) {d : NodeId} (hs : SendsOn φ kv d) :
    EntOn (T + 1) d (arrOn φ kv d) ∧ SInvB (arrOn φ kv d) ∧ NoDegT (arrOn φ kv d) ∧
    (∀ R, PinsFrom φ d R → GoodAt (arrOn φ kv d) R) ∧ d ∈ mapNodes φ T := by
  have hent := h.on kv hkv
  have hok := hent.1
  have hd : d.step = kv.2.current_step := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key, hok.step]; omega
  have hi := h.inv kv hkv
  have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by rw [step_filterAllOn]; exact hd
  refine ⟨entOn_upFilteringOn hent hs.1 hs.2,
    sInvB_upOn (sInvB_filterAllOn hi _) hdY (by rw [hd, hok.step]; omega),
    noDegT_upOn (noSelf_filterAllOn hent.2.1 _) (noDegT_filterAllOn hent.2.1 (h.ndt kv hkv) _),
    fun R hR => good_arrivalAt hi hent.2.1 (h.ndt kv hkv) hent.2.2 (reqOf_length_le_one φ d) hd
      (by rw [hok.step]; exact hT) (h.good kv hkv _ (PinsFrom.cons hs.1 hR)), ?_⟩
  have hk : kv.1 ∈ mapNodes φ kv.1.step := by rw [hok.key]; exact h.keys kv hkv
  have := sonsOfMap_subset φ kv.1 hk d hs.1
  rw [hok.key, show T - 1 + 1 = T by omega] at this
  exact this

/-- **El paso de la máquina `:on`**: el invariante pasa a la línea siguiente bajo `HJoinOn`. -/
theorem lInvOn_advance {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvOn φ T line)
    (hj : HJoinOn φ line) : LInvOn φ (T + 1) (advanceM .on φ line) := by
  have hlen := line_cases h.nodup h.keys
  have ent : ∀ E ∈ advanceM .on φ line, SInvB E.2 ∧ NoDegT E.2 ∧ (∀ R, PinsFrom φ E.1 R → GoodAt E.2 R) ∧
      E.1 ∈ mapNodes φ T := by
    intro E hE
    rcases entry_shapeOn hlen h.nodup hE with ⟨kv, hkv, hs, he⟩ | ⟨a, ha, b, hb, hab, hsa, hsb, he⟩
    · obtain ⟨_, hi, hn, hg, hk⟩ := arrOn_facts hT h hkv hs
      rw [he]; exact ⟨hi, hn, hg, hk⟩
    · obtain ⟨ea, ia, na, ga, hk⟩ := arrOn_facts hT h ha hsa
      obtain ⟨eb, ib, nb, gb, _⟩ := arrOn_facts hT h hb hsb
      have hcs : (arrOn φ a E.1).current_step = (arrOn φ b E.1).current_step := ea.1.step.trans eb.1.step.symm
      have hjoin : doJoinOn (arrOn φ a E.1) (arrOn φ b E.1) = joinOn (arrOn φ a E.1) (arrOn φ b E.1) := by
        unfold doJoinOn okJoin
        rw [if_pos (by simp [ea.1.step, eb.1.step, ea.1.mp, eb.1.mp, ea.1.valid, eb.1.valid])]
      rw [he, hjoin]
      exact ⟨sInvB_joinOn ia ib hcs, noDegT_joinOn ea.2.1 eb.2.1 ia.edges ib.edges,
        fun R hR => good_joinAt ia ib ea.2.1 eb.2.1 na nb hcs (ga R hR) (gb R hR) (hj a ha b hb hab E.1 hsa hsb R hR),
        hk⟩
  exact ⟨lineOn_advance h.on, advanceOn_nodup φ line,
    fun E hE => by rw [show T + 1 - 1 = T by omega]; exact (ent E hE).2.2.2,
    fun E hE => (ent E hE).1, fun E hE => (ent E hE).2.1, fun E hE => (ent E hE).2.2.1⟩

-- ============================================================
-- La máquina entera y el veredicto
-- ============================================================

theorem stepsM_succ (m : Mode) (φ : Cnf) :
    ∀ (n : Nat) (L : Line), stepsM m φ (n + 1) L = advanceM m φ (stepsM m φ n L) := by
  intro n
  induction n with
  | zero => intro L; rfl
  | succ n ih => intro L; show stepsM m φ (n + 1) (advanceM m φ L) = advanceM m φ (stepsM m φ (n + 1) L); rw [ih]; rfl

/-- **La hipótesis**: en cada línea de la máquina `:on`, `PinSideAt` en sus joins, para los pins de `PinsFrom`. -/
def HypsJoinOn (φ : Cnf) : Prop := ∀ n : Nat, HJoinOn φ (stepsM .on φ n (initM .on φ))

theorem lInvOn_steps {φ : Cnf} (H : HypsJoinOn φ) :
    ∀ n : Nat, LInvOn φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero => exact lInvOn_init φ
  | succ n ih =>
    rw [stepsM_succ]
    have := lInvOn_advance (by omega) ih (H n)
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

/-- **Todo estado final de la máquina `:on` cumple `GoodAt` sin pins** bajo `PinSideAt` en sus joins. -/
theorem goodAt_run {φ : Cnf} (H : HypsJoinOn φ) : ∀ kv ∈ runM .on φ, GoodAt kv.2 [] := fun kv hkv =>
  (lInvOn_steps H (stepCount φ - 1).toNat).good kv hkv [] (PinsFrom.nil _)

end GPathB

namespace MachineOn

open GPathB Driver

/-- **La espina con la regla activa decide la satisfacibilidad** bajo `PinSideAt` en los joins de la máquina: toda
cadena viva de una unión fijada es cadena viva de una de sus dos llegadas fijadas, con sus tríos; y solo para los pins
que la máquina usa (los requisitos de un camino del mapa desde el destino). Es la única hipótesis. -/
theorem spineVerdictOn_iff_of_joinOn {φ : Cnf} (hbd : Bounded φ) (H : HypsJoinOn φ) :
    SpineVerdictOn φ ↔ Satisfiable φ := by
  apply spineVerdictOn_iff_of_liveExt hbd
  intro kv hkv hval
  exact goodAt_run H kv hkv hval

end MachineOn

end AbsSatBingo.Model
