-- lean/improves_bingo/AbsSatBingo/Model/LiveDriver.lean
import AbsSatBingo.Model.LiveLine
import AbsSatBingo.Model.LineInduction

/-!
# La inducción de línea con pins extra sobre la máquina real (etapa 3)

* **La entrada de una clave tras `advance`** es el pliegue de las llegadas válidas de los remitentes, en el orden de la
  línea (`lookup_advance`); en el mapa bin hay como mucho dos remitentes por destino, así que cada entrada es una sola
  llegada o la unión de dos (`entry_shape`).
* **Las familias fantasma** (`famsAt`) se pliegan igual: una llegada lleva la familia de su remitente desplazada por
  sus requisitos, una unión la `joinFam` de sus dos llegadas.
* **El invariante de línea** (`LInv`): contabilidad, cada entrada `Good` y `FamMono` con su familia, y `CrossClosed`
  entre las entradas fijadas.
* **El veredicto**: bajo `PinJoinSplitAll` en los joins de la máquina y `NoNewClose` hacia los remitentes de las otras
  entradas (`HypsLiveLine`), la espina con tríos decide la satisfacibilidad (`spineVerdict_iff_of_liveLine`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Driver Machine

-- ============================================================
-- La entrada de una clave tras `advance`
-- ============================================================

/-- La llegada de una entrada de la línea a un destino. -/
def arrOf (φ : Cnf) (kv : NodeId × GPathB) (d : NodeId) : GPathB :=
  kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)

/-- La entrada `kv` envía a `d` y su llegada es válida. -/
def Sends (φ : Cnf) (kv : NodeId × GPathB) (d : NodeId) : Prop :=
  d ∈ sonsOfMap φ kv.1 ∧ (arrOf φ kv d).isValid = true

instance (φ : Cnf) (kv : NodeId × GPathB) (d : NodeId) : Decidable (Sends φ kv d) := by
  unfold Sends; infer_instance

/-- El estado de una clave en una línea (la primera entrada con esa clave). -/
def lookup (l : Line) (d : NodeId) : Option GPathB := (l.find? (fun kv => kv.1 == d)).map (·.2)

/-- Un paso del pliegue de las llegadas a `d`. -/
def stepS (φ : Cnf) (d : NodeId) (o : Option GPathB) (kv : NodeId × GPathB) : Option GPathB :=
  if Sends φ kv d then
    some (match o with
      | none => arrOf φ kv d
      | some e => doJoin e (arrOf φ kv d))
  else o

theorem lookup_insert (l : Line) (key : NodeId) (g : GPathB) (d : NodeId) :
    lookup (Driver.insert l key g) d =
      if key = d then some (match lookup l d with
        | none => g
        | some e => doJoin e g)
      else lookup l d := by
  unfold Driver.insert lookup
  split
  · rename_i k' e hfind
    have hk' : k' = key := by simpa using List.find?_some hfind
    subst hk'
    rw [List.find?_map]
    by_cases hkd : k' = d
    · subst hkd
      rw [if_pos rfl]
      have : ((fun kv : NodeId × GPathB => kv.1 == k') ∘
          fun kv => if (kv.1 == k') = true then (k', doJoin e g) else kv) = fun kv => kv.1 == k' := by
        funext kv; simp only [Function.comp]; split <;> simp_all
      rw [this, hfind]
      simp
    · rw [if_neg hkd]
      have : ((fun kv : NodeId × GPathB => kv.1 == d) ∘
          fun kv => if (kv.1 == k') = true then (k', doJoin e g) else kv) = fun kv => kv.1 == d := by
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

theorem lookup_sendTo (φ : Cnf) (kv : NodeId × GPathB) (next : Line) (d' d : NodeId) :
    lookup (sendTo φ kv.2 next d') d =
      if d' = d ∧ (arrOf φ kv d').isValid = true then some (match lookup next d with
        | none => arrOf φ kv d'
        | some e => doJoin e (arrOf φ kv d'))
      else lookup next d := by
  unfold sendTo
  dsimp only
  by_cases hv : (arrOf φ kv d').isValid = true
  · have hv' : (kv.2.upFiltering (reqOf φ d') d' "" (isProhibited φ)).isValid = true := hv
    rw [if_pos hv', lookup_insert]
    by_cases hd : d' = d
    · rw [if_pos hd, if_pos ⟨hd, hv⟩]; rfl
    · rw [if_neg hd, if_neg (fun h => hd h.1)]
  · have hv' : ¬ (kv.2.upFiltering (reqOf φ d') d' "" (isProhibited φ)).isValid = true := hv
    rw [if_neg hv', if_neg (fun h => hv h.2)]

theorem lookup_foldl_sendTo (φ : Cnf) (kv : NodeId × GPathB) (d : NodeId) :
    ∀ (ss : List NodeId) (next : Line), ss.Nodup →
      lookup (ss.foldl (sendTo φ kv.2) next) d =
        if d ∈ ss ∧ (arrOf φ kv d).isValid = true then some (match lookup next d with
          | none => arrOf φ kv d
          | some e => doJoin e (arrOf φ kv d))
        else lookup next d := by
  intro ss
  induction ss with
  | nil => intro next _; simp
  | cons s rest ih =>
    intro next hnd
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons, ih _ hnd.2, lookup_sendTo]
    by_cases hsd : s = d
    · subst hsd
      have hnr : s ∉ rest := hnd.1
      simp only [hnr, false_and, if_false, true_and, List.mem_cons_self]
    · have hne : ¬ (s = d ∧ (arrOf φ kv s).isValid = true) := fun h => hsd h.1
      rw [if_neg hne]
      by_cases hr : d ∈ rest ∧ (arrOf φ kv d).isValid = true
      · rw [if_pos hr, if_pos ⟨List.mem_cons_of_mem _ hr.1, hr.2⟩]
      · rw [if_neg hr, if_neg]
        rintro ⟨hm, hv⟩
        rcases List.mem_cons.mp hm with h | h
        · exact hsd h.symm
        · exact hr ⟨h, hv⟩

theorem mapNodes_nodup (φ : Cnf) (k : Int) : (mapNodes φ k).Nodup := by
  unfold mapNodes
  repeat' split
  all_goals simp

theorem sonsOfMap_nodup (φ : Cnf) (k : NodeId) : (sonsOfMap φ k).Nodup := by
  unfold sonsOfMap
  split
  · simp
  · exact mapNodes_nodup φ _

theorem lookup_sendAll (φ : Cnf) (kv : NodeId × GPathB) (next : Line) (d : NodeId) :
    lookup (sendAll φ kv next) d = stepS φ d (lookup next d) kv := by
  unfold sendAll stepS Sends
  rw [lookup_foldl_sendTo φ kv d _ next (sonsOfMap_nodup φ kv.1)]

/-- **La entrada de `d` tras `advance`** es el pliegue de las llegadas válidas a `d`. -/
theorem lookup_advance (φ : Cnf) (line : Line) (d : NodeId) :
    lookup (advance φ line) d = line.foldl (stepS φ d) none := by
  unfold advance
  have : ∀ (l : Line) (next : Line), lookup (l.foldl (fun next kv => sendAll φ kv next) next) d =
      l.foldl (stepS φ d) (lookup next d) := by
    intro l
    induction l with
    | nil => intro next; rfl
    | cons kv rest ih => intro next; rw [List.foldl_cons, List.foldl_cons, ih, lookup_sendAll]
  rw [this]; rfl

theorem lookup_of_mem {l : Line} (hnd : (l.map (·.1)).Nodup) {kv : NodeId × GPathB} (h : kv ∈ l) :
    lookup l kv.1 = some kv.2 := by
  unfold lookup
  cases hf : l.find? (fun x => x.1 == kv.1) with
  | none => exact absurd (List.find?_eq_none.mp hf kv h) (by simp)
  | some x =>
    have hx : x.1 = kv.1 := by simpa using List.find?_some hf
    rw [eq_of_nodup_keys hnd (List.mem_of_find?_eq_some hf) h hx]
    rfl

-- ============================================================
-- Las familias fantasma
-- ============================================================

/-- La relación vacía. -/
def botF : FamT := fun _ _ _ _ => False

/-- La familia de una llegada: la de su remitente con sus requisitos delante. -/
def shiftF (φ : Cnf) (Fs : NodeId → FamT) (kv : NodeId × GPathB) (d : NodeId) : FamT :=
  fun R => Fs kv.1 (reqOf φ d ++ R)

/-- Un paso del pliegue de las llegadas a `d`, con sus familias. -/
def stepF (φ : Cnf) (Fs : NodeId → FamT) (d : NodeId) (o : Option (GPathB × FamT)) (kv : NodeId × GPathB) :
    Option (GPathB × FamT) :=
  if Sends φ kv d then
    some (match o with
      | none => (arrOf φ kv d, shiftF φ Fs kv d)
      | some (e, Fe) => (doJoin e (arrOf φ kv d), joinFam e (arrOf φ kv d) Fe (shiftF φ Fs kv d)))
  else o

/-- Las familias de la línea siguiente. -/
def famsNext (φ : Cnf) (line : Line) (Fs : NodeId → FamT) : NodeId → FamT := fun d =>
  match line.foldl (stepF φ Fs d) none with
  | some (_, F) => F
  | none => botF

/-- **Las familias fantasma de la máquina**, paso a paso. -/
def famsAt (φ : Cnf) : Nat → NodeId → FamT
  | 0 => fun _ => botF
  | n + 1 => famsNext φ (steps φ n (init φ)) (famsAt φ n)

-- ============================================================
-- La forma de una entrada
-- ============================================================

theorem nodeId_eq {x y : NodeId} (h1 : x.step = y.step) (h2 : x.index = y.index) : x = y := by
  cases x; cases y; simp_all

/-- **Una línea del mapa bin tiene como mucho dos entradas.** -/
theorem line_cases {φ : Cnf} {k : Int} {line : Line} (hnd : (line.map (·.1)).Nodup)
    (hk : ∀ kv ∈ line, kv.1 ∈ mapNodes φ k) : line = [] ∨ (∃ a, line = [a]) ∨ (∃ a b, line = [a, b]) := by
  match line, hnd, hk with
  | [], _, _ => exact Or.inl rfl
  | [a], _, _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _, _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  | a :: b :: c :: rest, hnd, hk =>
    exfalso
    have ha := hk a (by simp); have hb := hk b (by simp); have hc := hk c (by simp)
    have sa := mapNodes_step φ k _ ha; have sb := mapNodes_step φ k _ hb; have sc := mapNodes_step φ k _ hc
    have ia := mapNodes_index φ k _ ha; have ib := mapNodes_index φ k _ hb; have ic := mapNodes_index φ k _ hc
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨⟨hab, hac, _⟩, ⟨hbc, _⟩, _⟩ := hnd
    rcases ia with ia | ia <;> rcases ib with ib | ib <;> rcases ic with ic | ic
    all_goals first
      | exact hab (nodeId_eq (by omega) (by omega))
      | exact hac (nodeId_eq (by omega) (by omega))
      | exact hbc (nodeId_eq (by omega) (by omega))

/-- **La forma de una entrada de `advance`**: una sola llegada o la unión de las llegadas de dos remitentes. -/
theorem entry_shape {φ : Cnf} {line : Line} (Fs : NodeId → FamT)
    (hlen : line = [] ∨ (∃ a, line = [a]) ∨ (∃ a b, line = [a, b])) (hnd : (line.map (·.1)).Nodup)
    {E : NodeId × GPathB} (hE : E ∈ advance φ line) :
    (∃ kv ∈ line, Sends φ kv E.1 ∧ E.2 = arrOf φ kv E.1 ∧ famsNext φ line Fs E.1 = shiftF φ Fs kv E.1) ∨
    (∃ a ∈ line, ∃ b ∈ line, a.1 ≠ b.1 ∧ Sends φ a E.1 ∧ Sends φ b E.1 ∧
      E.2 = doJoin (arrOf φ a E.1) (arrOf φ b E.1) ∧
      famsNext φ line Fs E.1 = joinFam (arrOf φ a E.1) (arrOf φ b E.1) (shiftF φ Fs a E.1) (shiftF φ Fs b E.1)) := by
  have h1 := lookup_of_mem (advance_nodup φ line) hE
  rw [lookup_advance] at h1
  rcases hlen with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · simp at h1
  · by_cases ha : Sends φ a E.1
    · simp only [List.foldl, stepS, ha, if_true, Option.some.injEq] at h1
      refine Or.inl ⟨a, by simp, ha, h1.symm, ?_⟩
      simp only [famsNext, List.foldl, stepF, ha, if_true]
    · simp [List.foldl, stepS, ha] at h1
  · have hab : a.1 ≠ b.1 := by simpa using hnd
    by_cases ha : Sends φ a E.1 <;> by_cases hb : Sends φ b E.1
    · simp only [List.foldl, stepS, ha, hb, if_true, Option.some.injEq] at h1
      refine Or.inr ⟨a, by simp, b, by simp, hab, ha, hb, h1.symm, ?_⟩
      simp only [famsNext, List.foldl, stepF, ha, hb, if_true]
    · simp only [List.foldl, stepS, ha, hb, if_true, if_false, Option.some.injEq] at h1
      refine Or.inl ⟨a, by simp, ha, h1.symm, ?_⟩
      simp only [famsNext, List.foldl, stepF, ha, hb, if_true, if_false]
    · simp only [List.foldl, stepS, ha, hb, if_true, if_false, Option.some.injEq] at h1
      refine Or.inl ⟨b, by simp, hb, h1.symm, ?_⟩
      simp only [famsNext, List.foldl, stepF, ha, hb, if_true, if_false]
    · simp [List.foldl, stepS, ha, hb] at h1

/-- Una llegada válida de una entrada de la línea: su estado de la línea siguiente. -/
theorem stateOk_arr {φ : Cnf} {T : Int} {kv : NodeId × GPathB} (hok : StateOk T kv.1 kv.2) {d : NodeId}
    (hs : Sends φ kv d) : StateOk (T + 1) d (arrOf φ kv d) :=
  stateOk_upFiltering hok hs.1 hs.2

/-- **La máquina une las dos llegadas**: mismo paso, mismo nodo de mapa, las dos válidas. -/
theorem doJoin_arr {φ : Cnf} {T : Int} {a b : NodeId × GPathB} (ha : StateOk T a.1 a.2) (hb : StateOk T b.1 b.2)
    {d : NodeId} (hsa : Sends φ a d) (hsb : Sends φ b d) :
    doJoin (arrOf φ a d) (arrOf φ b d) = join (arrOf φ a d) (arrOf φ b d) := by
  have oa := stateOk_arr ha hsa
  have ob := stateOk_arr hb hsb
  unfold doJoin okJoin
  rw [if_pos (by simp [oa.step, ob.step, oa.mp, ob.mp, oa.valid, ob.valid])]

-- ============================================================
-- El invariante de línea
-- ============================================================

theorem sInvB_empty : SInvB GPathB.empty := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [AliveDocs, LinksComplete, LinksCompat, NodupIds, Below, AboveZero, LinksStep, EdgesAlive, RootNone,
      GPathB.empty, Adj, adjb, hasEdge, isAlive]

/-- Con un solo paso no hay cadena que alargar. -/
theorem liveExt_small {g : GPathB} {F : Trios} (h : g.current_step ≤ 1) : LiveExt g F :=
  fun _ _ _ h1 h2 => absurd h2 (by omega)

/-- Con dos pasos no hay trío en una cadena (`NoDeg`). -/
theorem crossClosed_small {A B : GPathB} {FA FB : Trios} (hi : SInvB A) (hcs : A.current_step ≤ 2)
    (hF : NoDeg FA) : CrossClosed A FA B FB := by
  intro C j hC p q r h1 h2 h3 h4 h5 h6 hf
  exfalso
  obtain ⟨n1, n2, n3⟩ := hF _ _ _ hf
  have hj : 0 ≤ j := by
    obtain ⟨hs, ha⟩ := hC.node j (Int.le_refl j) (by omega)
    obtain ⟨n, hn, hnid⟩ := hi.docs _ ha
    have := hi.zero n hn
    rw [hnid, hs] at this; exact this
  rcases (show p = q ∨ p = r ∨ q = r by omega) with e | e | e
  · exact n1 (by rw [e])
  · exact n2 (by rw [e])
  · exact n3 (by rw [e])

/-- **El invariante de la línea** del paso `T`, con las familias de sus claves. -/
structure LInv (φ : Cnf) (T : Int) (line : Line) (Fs : NodeId → FamT) : Prop where
  ok    : LineOk T line
  nodup : (line.map (·.1)).Nodup
  keys  : ∀ kv ∈ line, kv.1 ∈ mapNodes φ (T - 1)
  good  : ∀ kv ∈ line, Good kv.2 (Fs kv.1)
  mono  : ∀ kv ∈ line, FamMono kv.2 (Fs kv.1)
  tid   : ∀ kv ∈ line, TopDocsId kv.2 kv.1
  cc    : ∀ a ∈ line, ∀ b ∈ line, a.1 ≠ b.1 → ∀ R, (pinF a.2 R).isValid = true → (pinF b.2 R).isValid = true →
    CrossClosed (pinF a.2 R) (Fs a.1 R) (pinF b.2 R) (Fs b.1 R)

/-- **El caso base**: la semilla, con la relación vacía. -/
theorem lInv_init (φ : Cnf) : LInv φ 1 (init φ) (fun _ => botF) := by
  have hl := (init_inv φ (fun _ => false)).1
  let d : NodeId := ⟨0, 0⟩
  have hi : SInvB (initSeed d "") := sInvB_up sInvB_empty (by rfl) (by decide)
  have hmem : (d, initSeed d "") ∈ init φ := by rw [init_eq]; exact List.mem_singleton_self _
  have hstep : (initSeed d "").current_step = 1 := (hl _ hmem).step
  have htid : TopDocsId (initSeed d "") d := by
    have hup : initSeed d "" = (GPathB.empty.addNode d "" (fun _ => false)).review := by
      show up GPathB.empty d "" (fun _ => false) = _
      unfold up; rw [if_pos (show GPathB.empty.isValid = true by rfl)]
    rw [hup]
    exact topDocsId_of_shrinks (shrinks_review _) (topDocsId_addNode (fun n hn => absurd hn List.not_mem_nil))
  refine ⟨hl, by rw [init_eq]; simp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [init_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    rw [show (1 : Int) - 1 = 0 by omega, mapNodes_fusion φ 0 (Or.inl rfl)]
    exact List.mem_singleton_self _
  · rw [init_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    exact ⟨hi, by rw [hstep]; omega, fun R _ => liveExt_small (by rw [step_pinF, hstep]; omega),
      fun _ _ _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩
  · rw [init_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    exact fun _ _ _ _ _ _ _ h => h.elim
  · rw [init_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
    exact htid
  · rw [init_eq]; intro a ha b hb hab
    rw [List.mem_singleton] at ha hb; subst ha; subst hb
    exact absurd rfl hab

-- ============================================================
-- Las hipótesis sobre la línea
-- ============================================================

/-- **`PinJoinSplitAll` en los joins de la máquina**: en cada destino, entre las llegadas de dos remitentes. -/
def HSplit (φ : Cnf) (line : Line) : Prop :=
  ∀ a ∈ line, ∀ b ∈ line, a.1 ≠ b.1 → ∀ d, Sends φ a d → Sends φ b d → PinJoinSplitAll (arrOf φ a d) (arrOf φ b d)

/-- **`NoNewClose` hacia los remitentes de las otras entradas**: un trío de una cadena de una entrada de la línea
siguiente que su familia prohíbe ya lo cortaba (con los mismos pins) cada remitente que envía a otra entrada. -/
def HNew (φ : Cnf) (line : Line) (Fs : NodeId → FamT) : Prop :=
  ∀ E ∈ advance φ line, ∀ kv ∈ line, ∀ d₁, d₁ ≠ E.1 → Sends φ kv d₁ →
    ∀ R C j p q r, OnChain3 (pinF E.2 R) C j p q r → famsNext φ line Fs E.1 R (C p) (C q) (C r) →
      SideForbids (pinF kv.2 R) (Fs kv.1 R) (C p) (C q) (C r)

-- ============================================================
-- El paso
-- ============================================================

/-- Lo que se sabe de una llegada válida de una entrada de la línea. -/
theorem arr_facts {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} {Fs : NodeId → FamT} (h : LInv φ T line Fs)
    {kv : NodeId × GPathB} (hkv : kv ∈ line) {d : NodeId} (hs : Sends φ kv d) :
    d.step = kv.2.current_step ∧ (kv.2.filterAll (reqOf φ d)).isValid = true ∧
    Good (arrOf φ kv d) (shiftF φ Fs kv d) ∧ FamMono (arrOf φ kv d) (shiftF φ Fs kv d) ∧
    TopDocsId (arrOf φ kv d) d ∧ TopsFrom (arrOf φ kv d) (fun x => x = kv.1) ∧ d ∈ mapNodes φ T := by
  have hok := h.ok kv hkv
  have hd : d.step = kv.2.current_step := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key, hok.step]; omega
  have hvY : (kv.2.filterAll (reqOf φ d)).isValid = true := valid_of_up (d := d) (title := "")
    (forb := isProhibited φ) hs.2
  have hsf := shrinks_filterAll kv.2 (reqOf φ d)
  have hb : Below (kv.2.filterAll (reqOf φ d)) := below_of_shrinks hsf hok.below
  have hdf : d.step = (kv.2.filterAll (reqOf φ d)).current_step := by rw [hsf.1.step]; exact hd
  have hup : arrOf φ kv d = ((kv.2.filterAll (reqOf φ d)).addNode d "" (isProhibited φ)).review := by
    unfold arrOf upFiltering up; rw [if_pos hvY]
  refine ⟨hd, hvY, good_arrival (h.good kv hkv) hd hvY, famMono_arrival (h.good kv hkv) (h.mono kv hkv) hd, ?_, ?_, ?_⟩
  · rw [hup]; exact topDocsId_of_shrinks (shrinks_review _) (topDocsId_addNode hb)
  · rw [hup]
    exact revPrims_review (revPrims_topsFrom _) _ (topsFrom_addNode (sInvB_filterAll (h.good kv hkv).inv _).docs hb
      hdf (by rw [hsf.1.step, hok.step]; omega) (topDocsId_of_shrinks hsf (h.tid kv hkv)))
  · have hk : kv.1 ∈ mapNodes φ kv.1.step := by rw [hok.key]; exact h.keys kv hkv
    have := sonsOfMap_subset φ kv.1 hk d hs.1
    rw [hok.key, show T - 1 + 1 = T by omega] at this
    exact this

/-- **El paso de la máquina**: el invariante pasa a la línea siguiente bajo `HSplit` y `HNew`. -/
theorem lInv_advance {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} {Fs : NodeId → FamT} (h : LInv φ T line Fs)
    (hsplit : HSplit φ line) (hnew : HNew φ line Fs) : LInv φ (T + 1) (advance φ line) (famsNext φ line Fs) := by
  have hlen := line_cases h.nodup h.keys
  have hl' := lineOk_advance (φ := φ) h.ok
  -- lo que se sabe de cada entrada nueva
  have ent : ∀ E ∈ advance φ line, Good E.2 (famsNext φ line Fs E.1) ∧ FamMono E.2 (famsNext φ line Fs E.1) ∧
      TopDocsId E.2 E.1 ∧ E.1 ∈ mapNodes φ T ∧ E.1.step = T ∧ E.2.current_step ≤ T + 1 ∧
      (∀ u ∈ E.2.alive, u.id.step = T → u.id = E.1) := by
    intro E hE
    rcases entry_shape Fs hlen h.nodup hE with ⟨kv, hkv, hs, he, hf⟩ | ⟨a, ha, b, hb, hab, hsa, hsb, he, hf⟩
    · obtain ⟨hd, _, hg, hm, htid, _, hkey⟩ := arr_facts hT h hkv hs
      have hok := h.ok kv hkv
      obtain ⟨hsc, hsid⟩ := src_arrival (reqs := reqOf φ E.1) (title := "") (forb := isProhibited φ)
        (h.good kv hkv).inv hd
      rw [he, hf]
      refine ⟨hg, hm, htid, hkey, by rw [hd, hok.step], ?_, ?_⟩
      · have : (arrOf φ kv E.1).current_step ≤ kv.2.current_step + 1 := hsc
        rw [hok.step] at this; exact this
      · intro u hu hus
        exact hsid u hu (by rw [hok.step]; exact hus)
    · have oka := h.ok a ha
      have okb := h.ok b hb
      obtain ⟨hda, _, hA, hmA, htA, tfA, hkey⟩ := arr_facts hT h ha hsa
      obtain ⟨hdb, _, hB, hmB, htB, tfB, _⟩ := arr_facts hT h hb hsb
      have hcs : a.2.current_step = b.2.current_step := oka.step.trans okb.step.symm
      have hcsA : (arrOf φ a E.1).current_step = (arrOf φ b E.1).current_step :=
        (stateOk_arr oka hsa).step.trans (stateOk_arr okb hsb).step.symm
      have sAB : TopsSep (arrOf φ a E.1) (arrOf φ b E.1) :=
        topsSep_of_from tfA tfB hcsA (fun x h1 h2 => hab (h1.symm.trans h2))
      have sBA : TopsSep (arrOf φ b E.1) (arrOf φ a E.1) :=
        topsSep_of_from tfB tfA hcsA.symm (fun x h1 h2 => hab (h2.symm.trans h1))
      have hcc : ∀ R, (pinF (arrOf φ a E.1) R).isValid = true → (pinF (arrOf φ b E.1) R).isValid = true →
          CrossClosed (pinF (arrOf φ a E.1) R) (shiftF φ Fs a E.1 R) (pinF (arrOf φ b E.1) R) (shiftF φ Fs b E.1 R) ∧
          CrossClosed (pinF (arrOf φ b E.1) R) (shiftF φ Fs b E.1 R) (pinF (arrOf φ a E.1) R) (shiftF φ Fs a E.1 R) :=
        fun R hvA hvB =>
          ⟨cc_arrivals (h.good a ha) (h.good b hb) hcs hda (fun R' h1 h2 => h.cc a ha b hb hab R' h1 h2) R hvA hvB,
           cc_arrivals (h.good b hb) (h.good a ha) hcs.symm hdb (fun R' h1 h2 => h.cc b hb a ha (Ne.symm hab) R' h1 h2)
             R hvB hvA⟩
      have hsp := hsplit a ha b hb hab E.1 hsa hsb
      obtain ⟨hsc, hsid⟩ := src_join (reqs := reqOf φ E.1) (title := "") (forb := isProhibited φ)
        (h.good a ha).inv (h.good b hb).inv hcs hda
      rw [he, doJoin_arr oka okb hsa hsb, hf]
      refine ⟨good_join hA hB hcsA (fun t ht hts hb' => sAB t hts ht hb') (fun t ht hts ha' => sBA t hts ht ha') hcc hsp,
        famMono_join hA hB hmA hmB hcsA (by rw [(stateOk_arr oka hsa).step]; omega) hsp,
        topDocsId_join htA htB hcsA, hkey, by rw [hda, oka.step], ?_, ?_⟩
      · have : (join (arrOf φ a E.1) (arrOf φ b E.1)).current_step ≤ a.2.current_step + 1 := hsc
        rw [oka.step] at this; exact this
      · intro u hu hus
        exact hsid u hu (by rw [oka.step]; exact hus)
  refine ⟨hl', advance_nodup φ line, fun E hE => by rw [show T + 1 - 1 = T by omega]; exact (ent E hE).2.2.2.1,
    fun E hE => (ent E hE).1, fun E hE => (ent E hE).2.1, fun E hE => (ent E hE).2.2.1, ?_⟩
  -- CrossClosed entre las entradas nuevas
  intro E hE E' hE' hne R hv hv'
  obtain ⟨gE, _, _, _, hEs, hEcs, hEid⟩ := ent E hE
  by_cases hT1 : T = 1
  · exact crossClosed_small (sInvB_pinF gE.inv R) (by rw [step_pinF, (hl' E hE).step]; omega) (gE.nodeg R)
  have hT2 : 2 ≤ T := by omega
  rcases entry_shape Fs hlen h.nodup hE' with ⟨kv, hkv, hs, he, hf⟩ | ⟨a, ha, b, hb, hab, hsa, hsb, he, hf⟩
  · have hok := h.ok kv hkv
    obtain ⟨hd, _⟩ := arr_facts hT h hkv hs
    rw [he] at hv' ⊢
    rw [hf]
    exact cc_to_single (h.good kv hkv) (h.mono kv hkv) (by rw [hok.step]; exact hT2) hd hne
      (S := E.2) (GS := famsNext φ line Fs E.1) (by rw [hok.step]; exact hEcs)
      (fun u hu hus => hEid u hu (by rw [← hok.step]; exact hus))
      (fun R C j p q r hoc hf' => hnew E hE kv hkv E'.1 (Ne.symm hne) hs R C j p q r hoc hf') R hv'
  · have oka := h.ok a ha
    have okb := h.ok b hb
    obtain ⟨hda, hvYa, _⟩ := arr_facts hT h ha hsa
    obtain ⟨_, hvYb, _⟩ := arr_facts hT h hb hsb
    have hcs : a.2.current_step = b.2.current_step := oka.step.trans okb.step.symm
    rw [he, doJoin_arr oka okb hsa hsb] at hv' ⊢
    rw [hf]
    exact cc_gen (h.good a ha) (h.good b hb) (h.mono a ha) (h.mono b hb) hcs (by rw [hEs, oka.step]) hda hne
      (by rw [oka.step]; exact hT2) gE (by rw [oka.step]; exact hEcs)
      (fun u hu hus => hEid u hu (by rw [← oka.step]; exact hus)) (hsplit a ha b hb hab E'.1 hsa hsb) hvYa hvYb
      (fun R C j p q r hoc hf' => ⟨hnew E hE a ha E'.1 (Ne.symm hne) hsa R C j p q r hoc hf',
        hnew E hE b hb E'.1 (Ne.symm hne) hsb R C j p q r hoc hf'⟩) R hv'

-- ============================================================
-- La máquina entera y el veredicto
-- ============================================================

/-- **Las hipótesis**: en cada línea de la máquina, `PinJoinSplitAll` en sus joins y `NoNewClose` hacia los remitentes
de las otras entradas. -/
def HypsLiveLine (φ : Cnf) : Prop :=
  ∀ n : Nat, HSplit φ (steps φ n (init φ)) ∧ HNew φ (steps φ n (init φ)) (famsAt φ n)

theorem lInv_steps {φ : Cnf} (H : HypsLiveLine φ) :
    ∀ n : Nat, LInv φ ((n : Int) + 1) (steps φ n (init φ)) (famsAt φ n) := by
  intro n
  induction n with
  | zero => exact lInv_init φ
  | succ n ih =>
    rw [steps_succ]
    have := lInv_advance (by omega) ih (H n).1 (H n).2
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

end GPathB

namespace SecLine

open GPathB Driver

/-- **La espina con tríos decide la satisfacibilidad** bajo `PinJoinSplitAll` en los joins de la máquina y `NoNewClose`
hacia los remitentes de las otras entradas, con las familias fantasma de la máquina. -/
theorem spineVerdict_iff_of_liveLine {φ : Cnf} (hbd : Bounded φ) (H : HypsLiveLine φ) :
    SpineVerdict φ ↔ Satisfiable φ := by
  apply spineVerdict_iff_of_liveExt hbd
  intro kv hkv hval
  exact ⟨_, ((lInv_steps H (stepCount φ - 1).toNat).good kv hkv).live [] hval⟩

end SecLine

end AbsSatBingo.Model
