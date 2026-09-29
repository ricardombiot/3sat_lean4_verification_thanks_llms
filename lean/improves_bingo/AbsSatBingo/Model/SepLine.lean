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

Resultado: **`readerVerdict_iff_of_noSep`**, el veredicto del lector bajo `SplitSat`, `SideEdgesAt` y `AvoidSat`.
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

/-- El join de la línea con la separación ya demostrada. -/
theorem sInv_doJoin_sep {φ : Cnf} (H : HypsNoSep φ) {U : Int} (hU : 2 ≤ U) {key : NodeId} {e g : GPathB}
    (he : StateOk U key e) (hg : StateOk U key g) (hke : SInv e) (hkg : SInv g) (hsep : SepAt e g (U - 2)) :
    SInv (doJoin e g) := by
  have hcs : e.current_step = g.current_step := he.step.trans hg.step.symm
  exact sInv_doJoin_of (secSplit_of_splitSat (H.split U key e g hU he hg hke hkg)
    (sidePinned_of_sideEdges (by omega) (by rw [he.step]; omega) hcs hke.2.2.2.2.2.2 hkg.2.2.2.2.2.2
      hke.2.2.1 hkg.2.2.1 hsep (H.side U key e g hU he hg hke hkg))) hke hkg

/-- **Insertar una llegada**, llevando los orígenes: el estado del destino solo tiene orígenes anteriores. -/
theorem lineO_insert {φ : Cnf} (H : HypsNoSep φ) {U : Int} (hU : 2 ≤ U) {line : Line} {key s : NodeId}
    {g : GPathB} {A : NodeId → Prop} {done : List NodeId}
    (hl : LineOk U line) (hlk : LineS line)
    (ho : ∀ kv ∈ line, OriginIn kv.2 (U - 2) (fun a => A a ∨ (a = s ∧ kv.1 ∈ done)))
    (hkey : key ∉ done) (hsA : ¬ A s) (hg : StateOk U key g) (hk : SInv g) (hog : OriginIn g (U - 2) (· = s)) :
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
    have hsep := sepAt_of_origin hoe hog hsA
    refine ⟨?_, ?_⟩
    · intro kv hkv
      obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
      split
      · exact sInv_doJoin_sep H hU (hl _ hmem) hg (hlk _ hmem) hk hsep
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
theorem lineO_advance {φ : Cnf} (H : HypsNoSep φ) {T : Int} (hT : 1 ≤ T) {line : Line} (hl : LineOk T line)
    (hlk : LineS line) (hent : ∀ kv ∈ line, EntOk kv) (hnd : (line.map (·.1)).Nodup) :
    LineS (advance φ line) := by
  have hU : (2 : Int) ≤ T + 1 := by omega
  have hk2 : T + 1 - 2 = T - 1 := by omega
  -- los envíos de un remitente kv, con orígenes A ∨ kv.1 en los destinos ya servidos
  have hsend : ∀ (kv : NodeId × GPathB), kv ∈ line → ∀ (A : NodeId → Prop), ¬ A kv.1 →
      ∀ (ds : List NodeId) (done : List NodeId), ds.Nodup → (∀ d ∈ ds, d ∉ done) →
      (∀ d ∈ ds, d ∈ sonsOfMap φ kv.1) → ∀ nx, LineOk (T + 1) nx → LineS nx →
      (∀ kv' ∈ nx, OriginIn kv'.2 (T - 1) (fun a => A a ∨ (a = kv.1 ∧ kv'.1 ∈ done))) →
      LineOk (T + 1) (ds.foldl (sendTo φ kv.2) nx) ∧ LineS (ds.foldl (sendTo φ kv.2) nx) ∧
        ∀ kv' ∈ ds.foldl (sendTo φ kv.2) nx, OriginIn kv'.2 (T - 1) (fun a => A a ∨ a = kv.1) := by
    intro kv hkv A hA ds
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
        obtain ⟨b', c'⟩ := lineO_insert H hU a b c (hdone d (List.mem_cons_self ..)) hA hok
          (sInv_upFiltering H.skip (hl kv hkv) (hlk kv hkv) hT hd hv) hog
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
      (∀ kv ∈ l, ¬ A kv.1) → ∀ next, LineOk (T + 1) next → LineS next →
      (∀ kv ∈ next, OriginIn kv.2 (T - 1) A) →
      LineS (l.foldl (fun next kv => sendAll φ kv next) next) := by
    intro l
    induction l with
    | nil => intro _ _ _ _ next _ h2 _; exact h2
    | cons kv rest ih =>
      intro hsub hndl A hA next h1 h2 h3
      have hkv := hsub kv (List.mem_cons_self ..)
      have hndl' := List.nodup_cons.mp hndl
      simp only [List.foldl_cons]
      obtain ⟨a, b, c⟩ := hsend kv hkv A (hA kv (List.mem_cons_self ..)) (sonsOfMap φ kv.1) []
        (sonsOfMap_nodup φ kv.1) (fun _ _ h => absurd h List.not_mem_nil) (fun _ h => h) next h1 h2
        (fun kv' h => originIn_mono (h3 kv' h) (fun _ h' => Or.inl h'))
      refine ih (fun kv' h => hsub kv' (List.mem_cons_of_mem _ h)) hndl'.2 (fun a => A a ∨ a = kv.1) ?_ _ a b c
      intro kv' hkv' hor
      rcases hor with h | h
      · exact hA kv' (List.mem_cons_of_mem _ hkv') h
      · exact hndl'.1 (List.mem_map.mpr ⟨kv', hkv', h⟩)
  exact key line (fun _ h => h) hnd (fun _ => False) (fun _ _ h => h) [] (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)

/-- El invariante de la línea sin `SepAt`: `SInv`, la contabilidad de las entradas y las claves únicas. -/
def LineP (T : Int) (line : Line) : Prop :=
  LineOk T line ∧ LineS line ∧ (∀ kv ∈ line, EntOk kv) ∧ (line.map (·.1)).Nodup

theorem lineP_init (φ : Cnf) : LineP 1 (init φ) := by
  obtain ⟨hl, hent, hnd, _⟩ := lineInv_init φ
  refine ⟨hl, ?_, fun kv hkv => (hent kv hkv).1, hnd⟩
  rw [init_eq]
  intro kv hkv
  rw [List.mem_singleton] at hkv; subst hkv
  exact sInv_initSeed

theorem lineP_steps {φ : Cnf} (H : HypsNoSep φ) :
    ∀ n : Nat, LineP ((n : Int) + 1) (steps φ n (init φ)) := by
  intro n
  induction n with
  | zero => exact lineP_init φ
  | succ n ih =>
    obtain ⟨hl, hs, he, hnd⟩ := ih
    rw [steps_succ]
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact ⟨lineOk_advance hl, lineO_advance H (by omega) hl hs he hnd, advance_entOk (by omega) hl he,
      advance_nodup φ _⟩

theorem run_sInv_noSep {φ : Cnf} (H : HypsNoSep φ) :
    ∀ kv ∈ run φ, StateOk (stepCount φ) kv.1 kv.2 ∧ SInv kv.2 := by
  have hpos := stepCount_pos φ
  obtain ⟨hl, hs, _, _⟩ := lineP_steps H (stepCount φ - 1).toNat
  have hrun : run φ = steps φ (stepCount φ - 1).toNat (init φ) := rfl
  rw [← hrun, show ((stepCount φ - 1).toNat : Int) + 1 = stepCount φ by rw [Int.toNat_of_nonneg (by omega)]; omega]
    at hl
  rw [← hrun] at hs
  exact fun kv hkv => ⟨hl kv hkv, hs kv hkv⟩

/-- **El veredicto del lector es la satisfacibilidad bajo `SplitSat`, `SideEdgesAt` y `AvoidSat`** (la separación
por el origen, demostrada). -/
theorem readerVerdict_iff_of_noSep {φ : Cnf} (hbd : Bounded φ) (H : HypsNoSep φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (run_sInv_noSep H)

end SecLine

end AbsSatBingo.Model
