-- lean/improves_bingo/AbsSatBingo/Model/SepLine.lean
import AbsSatBingo.Model.SecSplitParts
import AbsSatBingo.Model.LineInduction

/-!
# `SepAt` sale de la línea: los remitentes de un join no se comparten

`HypsSecParts` pedía `SepAt e g (T - 2)` en cada join: ningún nodo del mapa del paso de origen está vivo en los dos
lados. Es contabilidad de la línea, y aquí se demuestra:

* **`OriginIn h k A`**: los vivos de `h` en el paso `k` son de nodos del mapa de `A`.
* La llegada de un remitente `kv` tiene sus vivos del paso de origen en `kv.1` (`originIn_upFiltering`: el viejo
  paso de la cima solo tiene documentos de la clave, `TopDocsId`).
* En `advance`, cada remitente se procesa una vez (claves únicas) y envía una vez a cada hijo (`sonsOfMap_nodup`). Al
  unir su llegada a un estado del destino, ese estado solo tiene orígenes de remitentes anteriores, así que
  **`SepAt`** (`sepAt_of_origin`).

Y la versión de dos lados (`readerVerdict_iff_of_two`): en el mapa bin hay como mucho dos nodos del mapa por paso, las
claves son distintas, así que **cada join une dos estados de un color cada uno** (`joinProv_two`), y basta
`SplitSat2`: fijar el color de un lado o el del otro deja algo.

Resultado: **`readerVerdict_iff_of_exist`**, el veredicto del lector bajo `SplitSat`, `SideSat` (en joins separados) y
`AvoidSat`; y `readerVerdict_iff_of_noSep` con `SideEdgesAt` en lugar de `SideSat`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Machine (Below)

/-- Los vivos de `h` en el paso `k` son de nodos del mapa de `A`. -/
def OriginIn (h : GPathB) (k : Int) (A : NodeId → Prop) : Prop := ∀ q ∈ h.alive, q.id.step = k → A q.id

theorem originIn_mono {h : GPathB} {k : Int} {A B : NodeId → Prop} (ho : OriginIn h k A) (hab : ∀ a, A a → B a) :
    OriginIn h k B := fun q hq hk => hab _ (ho q hq hk)

theorem originIn_of_sub {h g : GPathB} {k : Int} {A : NodeId → Prop} (hs : Sub h g) (ho : OriginIn g k A) :
    OriginIn h k A := fun q hq hk => ho q (hs.alive q hq) hk

theorem originIn_doJoin {e g : GPathB} {k : Int} {A B : NodeId → Prop} (he : OriginIn e k A) (hg : OriginIn g k B) :
    OriginIn (doJoin e g) k (fun a => A a ∨ B a) := by
  unfold doJoin; split
  · intro q hq hk
    rcases (alive_join e g q).mp hq with h | h
    · exact Or.inl (he q h hk)
    · exact Or.inr (hg q h hk)
  · exact originIn_mono he (fun _ h => Or.inl h)

/-- **Separación por el origen**: si los orígenes de `e` están en `A`, los de `g` son `s`, y `s ∉ A`. -/
theorem sepAt_of_origin {e g : GPathB} {k : Int} {A : NodeId → Prop} {s : NodeId} (he : OriginIn e k A)
    (hg : OriginIn g k (· = s)) (hs : ¬ A s) : SepAt e g k := by
  intro b hb
  by_cases hbs : b = s
  · subst hbs
    exact Or.inr (fun q hq hqb => hs (hqb ▸ he q hq (by rw [hqb, hb])))
  · exact Or.inl (fun q hq hqb => hbs (hqb ▸ hg q hq (by rw [hqb, hb])))

/-- **La llegada de un remitente tiene su origen en él.** -/
theorem originIn_upFiltering {φ : Cnf} {T : Int} {kv : NodeId × GPathB} {d : NodeId}
    (hok : Machine.StateOk T kv.1 kv.2) (htd : TopDocsId kv.2 kv.1) (hd : d ∈ sonsOfMap φ kv.1) :
    OriginIn (kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)) (T - 1) (· = kv.1) := by
  have hs := shrinks_filterAll kv.2 (reqOf φ d)
  -- en el estado del remitente, los vivos del paso de la cima son de la clave
  have h0 : OriginIn kv.2 (T - 1) (· = kv.1) := by
    intro q hq hk
    obtain ⟨n, hn, hnid⟩ := hok.docs q hq
    rw [← hnid]
    exact htd n hn (by rw [hnid, hk, hok.step])
  have hf : OriginIn (kv.2.filterAll (reqOf φ d)) (T - 1) (· = kv.1) := originIn_of_sub hs.1 h0
  have hstep : (kv.2.filterAll (reqOf φ d)).current_step = T := hs.1.step.trans hok.step
  have hdstep : d.step = (kv.2.filterAll (reqOf φ d)).current_step := by
    rw [hstep, Machine.sonsOfMap_step φ kv.1 d hd, hok.key]; omega
  unfold upFiltering up
  split
  · refine originIn_of_sub (shrinks_review _).1 ?_
    intro q hq hk
    rcases alive_addNode_cases (title := "") (forb := isProhibited φ) (aliveDocs_filterAll hok.docs _)
      (Machine.below_of_shrinks hs hok.below) hdstep hq with ⟨h, _⟩ | ⟨_, h⟩
    · exact hf q h hk
    · omega
  · exact hf

end GPathB

theorem sonsOfMap_nodup (φ : Cnf) (d : NodeId) : (sonsOfMap φ d).Nodup := by
  unfold sonsOfMap
  split
  · simp
  · unfold mapNodes
    repeat' split
    all_goals simp

namespace SecLine

open GPathB Driver Machine Final

/-- **Las hipótesis sin `SepAt`**: `SplitSat` y `SideEdgesAt` en los joins, `AvoidSat` en las ventanas saltadas. -/
structure HypsNoSep (φ : Cnf) : Prop where
  split : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → SplitSat (join e g) (T - 2)
  side  : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → SideEdgesAt e g (T - 2)
  skip  : SkipHyp φ

/-- **Las hipótesis de existencia**: `SplitSat` en los joins; `SideSat` en los joins separados por el origen (la
separación está demostrada); `AvoidSat` en las ventanas saltadas. -/
structure HypsExist (φ : Cnf) : Prop where
  split : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → SplitSat (join e g) (T - 2)
  side  : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → SepAt e g (T - 2) →
            SideSat (join e g) e g (T - 2)
  skip  : SkipHyp φ

/-- `SideEdgesAt` (con la separación) da `SideSat`. -/
theorem hypsExist_of_noSep {φ : Cnf} (H : HypsNoSep φ) : HypsExist φ := by
  refine ⟨H.split, fun T key e g hT he hg hke hkg hsep => ?_, H.skip⟩
  have hcs : e.current_step = g.current_step := he.step.trans hg.step.symm
  exact sideSat_of_sidePinned (sidePinned_of_sideEdges (by omega) (by rw [he.step]; omega) hcs hke.2.2.2.2.2.2
    hkg.2.2.2.2.2.2 hke.2.2.1 hkg.2.2.1 hsep (H.side T key e g hT he hg hke hkg))

/-- El join de la línea con la separación ya demostrada. -/
theorem sInv_doJoin_sep {φ : Cnf} (H : HypsExist φ) {U : Int} (hU : 2 ≤ U) {key : NodeId} {e g : GPathB}
    (he : StateOk U key e) (hg : StateOk U key g) (hke : SInv e) (hkg : SInv g) (hsep : SepAt e g (U - 2)) :
    SInv (doJoin e g) := by
  exact sInv_doJoin_of (secSplit_of_splitSat_sideSat (H.split U key e g hU he hg hke hkg)
    (H.side U key e g hU he hg hke hkg hsep)) hke hkg

/-- Una clave del paso `k`: índice 0 o 1 (los nodos del mapa bin). -/
def Key (k : Int) (a : NodeId) : Prop := a.step = k ∧ (a.index = 0 ∨ a.index = 1)

/-- **Quien resuelve el join** de la línea, con lo que la inducción sabe en ese momento: el estado del destino tiene
sus orígenes en remitentes anteriores (`A`, claves del paso de origen), y la llegada los tiene en su remitente `s`. -/
def JoinProv (U : Int) : Prop :=
  ∀ (key s : NodeId) (e g : GPathB) (A : NodeId → Prop), StateOk U key e → StateOk U key g → SInv e → SInv g →
    OriginIn e (U - 2) A → OriginIn g (U - 2) (· = s) → ¬ A s → (∀ a, A a → Key (U - 2) a) → Key (U - 2) s →
    SInv (doJoin e g)

theorem joinProv_exist {φ : Cnf} (H : HypsExist φ) {U : Int} (hU : 2 ≤ U) : JoinProv U :=
  fun _ _ _ _ _ he hg hke hkg hoe hog hsA _ _ => sInv_doJoin_sep H hU he hg hke hkg (sepAt_of_origin hoe hog hsA)

/-- **Insertar una llegada**, llevando los orígenes: el estado del destino solo tiene orígenes anteriores. -/
theorem lineO_insert {U : Int} (J : JoinProv U) {line : Line} {key s : NodeId}
    {g : GPathB} {A : NodeId → Prop} {done : List NodeId}
    (hl : LineOk U line) (hlk : LineS line)
    (ho : ∀ kv ∈ line, OriginIn kv.2 (U - 2) (fun a => A a ∨ (a = s ∧ kv.1 ∈ done)))
    (hkey : key ∉ done) (hsA : ¬ A s) (hAk : ∀ a, A a → Key (U - 2) a) (hsk : Key (U - 2) s)
    (hg : StateOk U key g) (hk : SInv g) (hog : OriginIn g (U - 2) (· = s)) :
    LineS (Driver.insert line key g) ∧
      ∀ kv ∈ Driver.insert line key g, OriginIn kv.2 (U - 2) (fun a => A a ∨ (a = s ∧ kv.1 ∈ key :: done)) := by
  have wk : ∀ {h : GPathB} {k' : NodeId}, OriginIn h (U - 2) (fun a => A a ∨ (a = s ∧ k' ∈ done)) →
      OriginIn h (U - 2) (fun a => A a ∨ (a = s ∧ k' ∈ key :: done)) :=
    fun h => originIn_mono h (fun _ h' => h'.imp_right (fun ⟨h1, h2⟩ => ⟨h1, List.mem_cons_of_mem _ h2⟩))
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have hkey' : key' = key := by simpa using List.find?_some hfind
    subst hkey'
    have hmem := List.mem_of_find?_eq_some hfind
    -- los orígenes de e son anteriores
    have hoe : OriginIn e (U - 2) A := by
      refine originIn_mono (ho _ hmem) (fun a h => ?_)
      rcases h with h | ⟨_, h⟩
      · exact h
      · exact absurd h hkey
    refine ⟨?_, ?_⟩
    · intro kv hkv
      obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
      split
      · exact J _ s e g A (hl _ hmem) hg (hlk _ hmem) hk hoe hog hsA hAk hsk
      · exact hlk kv0 hkv0
    · intro kv hkv
      obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
      split
      · refine originIn_mono (originIn_doJoin hoe hog) (fun a h => ?_)
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, List.mem_cons_self ..⟩
      · exact wk (ho kv0 hkv0)
  · refine ⟨?_, ?_⟩
    · intro kv hkv
      rcases List.mem_append.mp hkv with h | h
      · exact hlk kv h
      · rw [List.mem_singleton] at h; subst h; exact hk
    · intro kv hkv
      rcases List.mem_append.mp hkv with h | h
      · exact wk (ho kv h)
      · rw [List.mem_singleton] at h; subst h
        exact originIn_mono hog (fun a h => Or.inr ⟨h, List.mem_cons_self ..⟩)

/-- **El paso de la máquina sin `SepAt`**: cada remitente, una vez; cada hijo, una vez. -/
theorem lineO_advance {φ : Cnf} (Hs : SkipHyp φ) {T : Int} (J : JoinProv (T + 1)) (hT : 1 ≤ T) {line : Line}
    (hl : LineOk T line) (hlk : LineS line) (hent : ∀ kv ∈ line, EntOk kv) (hnd : (line.map (·.1)).Nodup)
    (hidx : ∀ kv ∈ line, kv.1.index = 0 ∨ kv.1.index = 1) :
    LineS (advance φ line) := by
  have hk2 : T + 1 - 2 = T - 1 := by omega
  have hkey : ∀ kv ∈ line, Key (T - 1) kv.1 := fun kv hkv => ⟨(hl kv hkv).key, hidx kv hkv⟩
  -- los envíos de un remitente kv, con orígenes A ∨ kv.1 en los destinos ya servidos
  have hsend : ∀ (kv : NodeId × GPathB), kv ∈ line → ∀ (A : NodeId → Prop), ¬ A kv.1 →
      (∀ a, A a → Key (T - 1) a) →
      ∀ (ds : List NodeId) (done : List NodeId), ds.Nodup → (∀ d ∈ ds, d ∉ done) →
      (∀ d ∈ ds, d ∈ sonsOfMap φ kv.1) → ∀ nx, LineOk (T + 1) nx → LineS nx →
      (∀ kv' ∈ nx, OriginIn kv'.2 (T - 1) (fun a => A a ∨ (a = kv.1 ∧ kv'.1 ∈ done))) →
      LineOk (T + 1) (ds.foldl (sendTo φ kv.2) nx) ∧ LineS (ds.foldl (sendTo φ kv.2) nx) ∧
        ∀ kv' ∈ ds.foldl (sendTo φ kv.2) nx, OriginIn kv'.2 (T - 1) (fun a => A a ∨ a = kv.1) := by
    intro kv hkv A hA hAk ds
    have hAk' : ∀ a, A a → Key (T + 1 - 2) a := fun a h => hk2 ▸ hAk a h
    have hsk' : Key (T + 1 - 2) kv.1 := hk2 ▸ hkey kv hkv
    induction ds with
    | nil =>
      intro done _ _ _ nx a b c
      exact ⟨a, b, fun kv' h => originIn_mono (c kv' h) (fun _ h' => h'.imp_right (·.1))⟩
    | cons d ds ihd =>
      intro done hnd' hdone hds nx a b c
      have hd := hds d (List.mem_cons_self ..)
      have hdnd := List.nodup_cons.mp hnd'
      simp only [List.foldl_cons]
      unfold sendTo
      dsimp only
      split
      · rename_i hv
        have hok := stateOk_upFiltering (hl kv hkv) hd hv
        have hog := originIn_upFiltering (hl kv hkv) (hent kv hkv).2 hd
        rw [← hk2] at hog c
        obtain ⟨b', c'⟩ := lineO_insert J a b c (hdone d (List.mem_cons_self ..)) hA hAk' hsk' hok
          (sInv_upFiltering Hs (hl kv hkv) (hlk kv hkv) hT hd hv) hog
        rw [hk2] at c'
        exact ihd (d :: done) hdnd.2
          (fun d' hd' hmem => by
            rcases List.mem_cons.mp hmem with h | h
            · exact hdnd.1 (h ▸ hd')
            · exact hdone d' (List.mem_cons_of_mem _ hd') h)
          (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd'))
          _ (lineOk_insert a hok) b' c'
      · exact ihd done hdnd.2 (fun d' hd' => hdone d' (List.mem_cons_of_mem _ hd'))
          (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd')) nx a b c
  have key : ∀ (l : Line), (∀ kv ∈ l, kv ∈ line) → (l.map (·.1)).Nodup → ∀ (A : NodeId → Prop),
      (∀ kv ∈ l, ¬ A kv.1) → (∀ a, A a → Key (T - 1) a) → ∀ next, LineOk (T + 1) next → LineS next →
      (∀ kv ∈ next, OriginIn kv.2 (T - 1) A) →
      LineS (l.foldl (fun next kv => sendAll φ kv next) next) := by
    intro l
    induction l with
    | nil => intro _ _ _ _ _ next _ h2 _; exact h2
    | cons kv rest ih =>
      intro hsub hndl A hA hAk next h1 h2 h3
      have hkv := hsub kv (List.mem_cons_self ..)
      have hndl' := List.nodup_cons.mp hndl
      simp only [List.foldl_cons]
      obtain ⟨a, b, c⟩ := hsend kv hkv A (hA kv (List.mem_cons_self ..)) hAk (sonsOfMap φ kv.1) []
        (sonsOfMap_nodup φ kv.1) (fun _ _ h => absurd h List.not_mem_nil) (fun _ h => h) next h1 h2
        (fun kv' h => originIn_mono (h3 kv' h) (fun _ h' => Or.inl h'))
      refine ih (fun kv' h => hsub kv' (List.mem_cons_of_mem _ h)) hndl'.2 (fun a => A a ∨ a = kv.1) ?_
        (fun a h => h.elim (hAk a) (fun h' => h' ▸ hkey kv hkv)) _ a b c
      intro kv' hkv' hor
      rcases hor with h | h
      · exact hA kv' (List.mem_cons_of_mem _ hkv') h
      · exact hndl'.1 (List.mem_map.mpr ⟨kv', hkv', h⟩)
  exact key line (fun _ h => h) hnd (fun _ => False) (fun _ _ h => h) (fun _ h => h.elim) []
    (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)

-- ============================================================
-- Las claves son nodos del mapa bin (índice 0 o 1)
-- ============================================================

theorem sonsOfMap_index {φ : Cnf} {k d : NodeId} (hk : k.index = 0 ∨ k.index = 1) (hd : d ∈ sonsOfMap φ k) :
    d.index = 0 ∨ d.index = 1 := by
  unfold sonsOfMap at hd
  split at hd
  · rw [List.mem_singleton] at hd; subst hd; simp only; omega
  · unfold mapNodes at hd
    repeat' split at hd
    all_goals simp at hd
    all_goals (try rcases hd with rfl | rfl) <;> (try subst hd) <;> simp

theorem mem_insert_keys {line : Line} {key : NodeId} {g : GPathB} {kv : NodeId × GPathB}
    (h : kv ∈ Driver.insert line key g) : kv ∈ line ∨ kv.1 = key := by
  unfold Driver.insert at h
  split at h
  · obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp h
    split
    · exact Or.inr rfl
    · exact Or.inl hkv0
  · rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · rw [List.mem_singleton] at h; subst h; exact Or.inr rfl

theorem advance_index (φ : Cnf) {line : Line} (h : ∀ kv ∈ line, kv.1.index = 0 ∨ kv.1.index = 1) :
    ∀ kv ∈ advance φ line, kv.1.index = 0 ∨ kv.1.index = 1 := by
  unfold advance
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, kv.1.index = 0 ∨ kv.1.index = 1) line ?_ []
    (fun _ h => absurd h List.not_mem_nil)
  intro next kv hkv hn
  unfold sendAll
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, kv.1.index = 0 ∨ kv.1.index = 1) _ ?_ next hn
  intro y d hd hy
  unfold sendTo
  dsimp only
  split
  · intro kv' hkv'
    rcases mem_insert_keys hkv' with h' | h'
    · exact hy kv' h'
    · rw [h']; exact sonsOfMap_index (h kv hkv) hd
  · exact hy

-- ============================================================
-- La máquina entera, con quien resuelve los joins
-- ============================================================

/-- El invariante de la línea sin `SepAt`: `SInv`, la contabilidad de las entradas, las claves únicas y del mapa. -/
def LineP (T : Int) (line : Line) : Prop :=
  LineOk T line ∧ LineS line ∧ (∀ kv ∈ line, EntOk kv) ∧ (line.map (·.1)).Nodup ∧
    ∀ kv ∈ line, kv.1.index = 0 ∨ kv.1.index = 1

theorem lineP_init (φ : Cnf) : LineP 1 (init φ) := by
  obtain ⟨hl, hent, hnd, _⟩ := lineInv_init φ
  refine ⟨hl, ?_, fun kv hkv => (hent kv hkv).1, hnd, ?_⟩
  · rw [init_eq]
    intro kv hkv
    rw [List.mem_singleton] at hkv; subst hkv
    exact sInv_initSeed
  · rw [init_eq]
    intro kv hkv
    rw [List.mem_singleton] at hkv; subst hkv
    exact Or.inl rfl

theorem lineP_steps {φ : Cnf} (Hs : SkipHyp φ) (J : ∀ U : Int, 2 ≤ U → JoinProv U) :
    ∀ n : Nat, LineP ((n : Int) + 1) (steps φ n (init φ)) := by
  intro n
  induction n with
  | zero => exact lineP_init φ
  | succ n ih =>
    obtain ⟨hl, hs, he, hnd, hidx⟩ := ih
    rw [steps_succ]
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact ⟨lineOk_advance hl, lineO_advance Hs (J _ (by omega)) (by omega) hl hs he hnd hidx,
      advance_entOk (by omega) hl he, advance_nodup φ _, advance_index φ hidx⟩

theorem run_sInv_prov {φ : Cnf} (Hs : SkipHyp φ) (J : ∀ U : Int, 2 ≤ U → JoinProv U) :
    ∀ kv ∈ run φ, StateOk (stepCount φ) kv.1 kv.2 ∧ SInv kv.2 := by
  have hpos := stepCount_pos φ
  obtain ⟨hl, hs, _, _, _⟩ := lineP_steps Hs J (stepCount φ - 1).toNat
  have hrun : run φ = steps φ (stepCount φ - 1).toNat (init φ) := rfl
  rw [← hrun, show ((stepCount φ - 1).toNat : Int) + 1 = stepCount φ by rw [Int.toNat_of_nonneg (by omega)]; omega]
    at hl
  rw [← hrun] at hs
  exact fun kv hkv => ⟨hl kv hkv, hs kv hkv⟩

/-- **El veredicto del lector es la satisfacibilidad bajo las hipótesis de existencia** `SplitSat`, `SideSat` (solo
en joins separados) y `AvoidSat`. -/
theorem readerVerdict_iff_of_exist {φ : Cnf} (hbd : Bounded φ) (H : HypsExist φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (run_sInv_prov H.skip (fun _ hU => joinProv_exist H hU))

/-- **El veredicto del lector es la satisfacibilidad bajo `SplitSat`, `SideEdgesAt` y `AvoidSat`** (la separación
por el origen, demostrada). -/
theorem readerVerdict_iff_of_noSep {φ : Cnf} (hbd : Bounded φ) (H : HypsNoSep φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_exist hbd (hypsExist_of_noSep H)

-- ============================================================
-- Dos lados, un color cada uno
-- ============================================================

/-- **La versión de dos lados de `SplitSat`**: una estructura cerrada no vacía de `u` que concuerda con `P` sobrevive
a fijar el color `a` o el color `s`. -/
def SplitSat2 (u : GPathB) (a s : NodeId) : Prop :=
  ∀ (P : List NodeId) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop),
    SecStruct u V R → (∀ b ∈ P, SecAgrees V b) → (∃ y, V y) →
    (∃ (V' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
        SecStruct u V' R' ∧ (∀ c ∈ P ++ [a], SecAgrees V' c) ∧ ∃ y, V' y) ∨
    (∃ (V' : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop),
        SecStruct u V' R' ∧ (∀ c ∈ P ++ [s], SecAgrees V' c) ∧ ∃ y, V' y)

theorem splitSat_of_two {u : GPathB} {k : Int} {a s : NodeId} (ha : a.step = k) (hs : s.step = k)
    (h : SplitSat2 u a s) : SplitSat u k := by
  intro P V R hst hag hne
  rcases h P V R hst hag hne with h' | h'
  · exact ⟨a, ha, h'⟩
  · exact ⟨s, hs, h'⟩

/-- **`SplitSat ⟹ SplitSat2`** cuando los vivos del paso de origen son de `a` o de `s`: fijar otro color no deja nada
(el testigo del paso de origen de un nodo de la estructura tendría ese color). -/
theorem splitSat2_of_splitSat {u : GPathB} {k : Int} {a s : NodeId} (hk0 : 0 ≤ k) (hkc : k < u.current_step)
    (ho : OriginIn u k (fun c => c = a ∨ c = s)) (h : SplitSat u k) : SplitSat2 u a s := by
  intro P V R hst hag hne
  obtain ⟨b, hbk, V', R', h1, h2, y, hy⟩ := h P V R hst hag hne
  obtain ⟨r, hrs, hyr, _⟩ := h1.pair (h1.refl hy) k hk0 hkc
  have hrb : r.id = b := h2 b (by simp) (h1.dom hyr).2 (by rw [hrs, hbk])
  rcases ho r (h1.alive (h1.dom hyr).2) hrs with hra | hrs'
  · exact Or.inl ⟨V', R', h1, by rw [← hrb, hra] at h2; exact h2, y, hy⟩
  · exact Or.inr ⟨V', R', h1, by rw [← hrb, hrs'] at h2; exact h2, y, hy⟩

/-- **Color = lado**: en la unión, una posesión con un nodo del color `a` (que `g` no tiene vivo) es de `e`, y sus dos
extremos viven en `e`. -/
theorem colour_side {e g : GPathB} {a : NodeId} (hoff : OffSide g a) (hee : EdgesAlive e) (heg : EdgesAlive g)
    {y r : PathNodeId} (hr : r.id = a) (h : (join e g).Adj y r) : e.Adj y r ∧ y ∈ e.alive ∧ r ∈ e.alive := by
  have hrg : r ∉ g.alive := fun h' => hoff r h' hr
  have he := adj_left_of_dead heg hrg h
  exact ⟨he, hee y r he⟩

/-- **Una pareja con un testigo del color `a` vive en `e`**: sus dos extremos y las posesiones con el testigo. Así, en
una estructura cerrada de la unión, las parejas que solo tienen testigos de `a` son de `e` en sus extremos, y las que
solo tienen testigos de `s`, de `g`: la «mezcla» de `SplitSat2` está en las posesiones entre extremos compartidos. -/
theorem pair_side_of_witness {e g : GPathB} {a : NodeId} (hoff : OffSide g a) (hee : EdgesAlive e)
    (heg : EdgesAlive g) {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    (hst : SecStruct (join e g) V R) {y w r : PathNodeId} (hr : r.id = a) (hyr : R y r) (hwr : R w r) :
    y ∈ e.alive ∧ w ∈ e.alive ∧ e.Adj y r ∧ e.Adj w r := by
  obtain ⟨h1, h2, _⟩ := colour_side hoff hee heg hr (hst.adj hyr)
  obtain ⟨h3, h4, _⟩ := colour_side hoff hee heg hr (hst.adj hwr)
  exact ⟨h2, h4, h1, h3⟩

/-- **Las hipótesis de dos lados**: `SplitSat2` en cada join, con los colores de los dos lados (uno cada uno,
distintos); `SideSat` en los joins separados; `AvoidSat` en las ventanas saltadas. -/
structure HypsTwo (φ : Cnf) : Prop where
  split : ∀ T key e g a s, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → Key (T - 2) a →
            Key (T - 2) s → a ≠ s → OriginIn e (T - 2) (· = a) → OriginIn g (T - 2) (· = s) →
            SplitSat2 (join e g) a s
  side  : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInv e → SInv g → SepAt e g (T - 2) →
            SideSat (join e g) e g (T - 2)
  skip  : SkipHyp φ

/-- El otro color del mismo paso. -/
def other (s : NodeId) : NodeId := ⟨s.step, 1 - s.index⟩

theorem eq_other {k : Int} {a s : NodeId} (ha : Key k a) (hs : Key k s) (hne : a ≠ s) : a = other s := by
  obtain ⟨as, ai⟩ := a
  obtain ⟨ss, si⟩ := s
  simp only [Key, other] at ha hs ⊢
  have : ¬ (as = ss ∧ ai = si) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  congr 1 <;> omega

/-- **En cada join, el estado del destino tiene un solo color, el otro.** -/
theorem joinProv_two {φ : Cnf} (H : HypsTwo φ) {U : Int} (hU : 2 ≤ U) : JoinProv U := by
  intro key s e g A he hg hke hkg hoe hog hsA hAk hsk
  have hne : ∀ c, A c → c ≠ s := fun c hc h => hsA (h ▸ hc)
  have hoe' : OriginIn e (U - 2) (· = other s) :=
    originIn_mono hoe (fun c hc => eq_other (hAk c hc) hsk (hne c hc))
  have hos : other s ≠ s := by
    intro h
    have := congrArg NodeId.index h
    simp only [other] at this
    rcases hsk.2 with h' | h' <;> omega
  have hok : Key (U - 2) (other s) := by
    refine ⟨hsk.1, ?_⟩
    simp only [other]
    rcases hsk.2 with h' | h' <;> omega
  have hcs : e.current_step = g.current_step := he.step.trans hg.step.symm
  have hsp : SplitSat (join e g) (U - 2) :=
    splitSat_of_two hok.1 hsk.1 (H.split U key e g (other s) s hU he hg hke hkg hok hsk hos hoe' hog)
  exact sInv_doJoin_of (secSplit_of_splitSat_sideSat hsp
    (H.side U key e g hU he hg hke hkg (sepAt_of_origin hoe hog hsA))) hke hkg

/-- **`HypsExist ⟹ HypsTwo`**: la versión de dos lados es más débil. -/
theorem hypsTwo_of_exist {φ : Cnf} (H : HypsExist φ) : HypsTwo φ := by
  refine ⟨fun T key e g a s hT he hg hke hkg _ _ _ hoe hog => ?_, H.side, H.skip⟩
  refine splitSat2_of_splitSat (by omega) (by show T - 2 < e.current_step; rw [he.step]; omega) ?_
    (H.split T key e g hT he hg hke hkg)
  intro q hq hk
  rcases (alive_join e g q).mp hq with h | h
  · exact Or.inl (hoe q h hk)
  · exact Or.inr (hog q h hk)

/-- **El veredicto del lector es la satisfacibilidad bajo las hipótesis de dos lados.** -/
theorem readerVerdict_iff_of_two {φ : Cnf} (hbd : Bounded φ) (H : HypsTwo φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (run_sInv_prov H.skip (fun _ hU => joinProv_two H hU))

end SecLine

end AbsSatBingo.Model
