-- lean/improves_bingo/AbsSatBingo/Model/LineCtxT.lean
import AbsSatBingo.Model.LineCtx

/-!
# La inducción de la línea con la procedencia de cada join

Como `LineCtx` (`JoinProvT`, `run_provT`), pero quien resuelve el join recibe la **procedencia**: la línea es
`steps φ n (init φ)` con `U = n + 2`, el estado del destino `e` es un árbol de llegadas desde ella y la llegada `g`
es la de un remitente `kv` de la línea (`g = arr φ kv key`, con `kv.1 = s`). `CSplit` sale de ahí
(`cliqueSplitTree`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace SecLine

open GPathB Driver Machine CliqueSplit

/-- **Quien resuelve el join, sabiendo la procedencia.** -/
def JoinProvT (φ : Cnf) (I : GPathB → Prop) (U : Int) : Prop :=
  ∀ (key s : NodeId) (e g : GPathB) (A : NodeId → Prop), StateOk U key e → StateOk U key g → I e → I g →
    OriginIn e (U - 2) A → OriginIn g (U - 2) (· = s) → ¬ A s → (∀ a, A a → Key (U - 2) a) → Key (U - 2) s →
    ∀ (n : Nat), U = (n : Int) + 1 + 1 → (∀ kv, kv ∈ steps φ n (init φ) → I kv.2) → ArrTree φ n key e →
    ∀ kv, kv ∈ steps φ n (init φ) → kv.1 = s → key ∈ sonsOfMap φ kv.1 → g = arr φ kv key → I (doJoin e g)

/-- Un predicado de las entradas que se conserva al insertar. -/
theorem insert_presT (Q : NodeId → GPathB → Prop) {line : Line} {key : NodeId} {g : GPathB}
    (hl : ∀ kv ∈ line, Q kv.1 kv.2) (hg : Q key g) (hj : ∀ e, Q key e → Q key (doJoin e g)) :
    ∀ kv ∈ Driver.insert line key g, Q kv.1 kv.2 := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have hkey' : key' = key := by simpa using List.find?_some hfind
    subst hkey'
    have hmem := List.mem_of_find?_eq_some hfind
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact hj e (hl _ hmem)
    · exact hl kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton] at h; subst h; exact hg

/-- **Insertar una llegada**, como `lineO_insert`, con `CSplit` para el join. -/
theorem lineO_insertT {φ : Cnf} {I : GPathB → Prop} {U : Int} (J : JoinProvT φ I U) {line : Line} {key s : NodeId}
    {g : GPathB} {A : NodeId → Prop} {done : List NodeId}
    (hl : LineOk U line) (hlk : ∀ kv ∈ line, I kv.2)
    (ho : ∀ kv ∈ line, OriginIn kv.2 (U - 2) (fun a => A a ∨ (a = s ∧ kv.1 ∈ done)))
    (hkey : key ∉ done) (hsA : ¬ A s) (hAk : ∀ a, A a → Key (U - 2) a) (hsk : Key (U - 2) s)
    (hg : StateOk U key g) (hk : I g) (hog : OriginIn g (U - 2) (· = s))
    (n : Nat) (hUn : U = (n : Int) + 1 + 1) (hIl : ∀ kv, kv ∈ steps φ n (init φ) → I kv.2)
    (htr : ∀ e, (key, e) ∈ line → ArrTree φ n key e)
    (kvS : NodeId × GPathB) (hkvS : kvS ∈ steps φ n (init φ)) (hks : kvS.1 = s) (hkd : key ∈ sonsOfMap φ kvS.1)
    (hga : g = arr φ kvS key) :
    (∀ kv ∈ Driver.insert line key g, I kv.2) ∧
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
    have hoe : OriginIn e (U - 2) A := by
      refine originIn_mono (ho _ hmem) (fun a h => ?_)
      rcases h with h | ⟨_, h⟩
      · exact h
      · exact absurd h hkey
    refine ⟨?_, ?_⟩
    · intro kv hkv
      obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
      split
      · exact J _ s e g A (hl _ hmem) hg (hlk _ hmem) hk hoe hog hsA hAk hsk n hUn hIl (htr e hmem) kvS hkvS hks hkd hga
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

/-- **El paso de la máquina**, como `lineO_advance`, con los árboles de llegadas para `CSplit`. -/
theorem lineO_advanceT {φ : Cnf} (_hbd : Bounded φ) {I : GPathB → Prop} (Hup : UpProv φ I) (n : Nat)
    (J : JoinProvT φ I ((n : Int) + 1 + 1)) (hT : 1 ≤ (n : Int) + 1)
    (hl : LineOk ((n : Int) + 1) (steps φ n (init φ))) (hlk : ∀ kv ∈ steps φ n (init φ), I kv.2)
    (hent : ∀ kv ∈ steps φ n (init φ), EntOk kv) (hnd : ((steps φ n (init φ)).map (·.1)).Nodup)
    (hidx : ∀ kv ∈ steps φ n (init φ), kv.1.index = 0 ∨ kv.1.index = 1) :
    ∀ kv ∈ advance φ (steps φ n (init φ)), I kv.2 := by
  generalize hline : steps φ n (init φ) = line at *
  generalize hTe : (n : Int) + 1 = T at *
  have hk2 : T + 1 - 2 = T - 1 := by omega
  have hkey : ∀ kv ∈ line, Key (T - 1) kv.1 := fun kv hkv => ⟨(hl kv hkv).key, hidx kv hkv⟩
  have hsend : ∀ (kv : NodeId × GPathB), kv ∈ line → ∀ (A : NodeId → Prop), ¬ A kv.1 →
      (∀ a, A a → Key (T - 1) a) →
      ∀ (ds : List NodeId) (done : List NodeId), ds.Nodup → (∀ d ∈ ds, d ∉ done) →
      (∀ d ∈ ds, d ∈ sonsOfMap φ kv.1) → ∀ nx, LineOk (T + 1) nx → (∀ kv' ∈ nx, I kv'.2) →
      (∀ kv' ∈ nx, OriginIn kv'.2 (T - 1) (fun a => A a ∨ (a = kv.1 ∧ kv'.1 ∈ done))) →
      (∀ kv' ∈ nx, ArrTree φ n kv'.1 kv'.2) →
      LineOk (T + 1) (ds.foldl (sendTo φ kv.2) nx) ∧ (∀ kv' ∈ ds.foldl (sendTo φ kv.2) nx, I kv'.2) ∧
        (∀ kv' ∈ ds.foldl (sendTo φ kv.2) nx, OriginIn kv'.2 (T - 1) (fun a => A a ∨ a = kv.1)) ∧
        ∀ kv' ∈ ds.foldl (sendTo φ kv.2) nx, ArrTree φ n kv'.1 kv'.2 := by
    intro kv hkv A hA hAk ds
    have hAk' : ∀ a, A a → Key (T + 1 - 2) a := fun a h => hk2 ▸ hAk a h
    have hsk' : Key (T + 1 - 2) kv.1 := hk2 ▸ hkey kv hkv
    have hkvl : kv ∈ steps φ n (init φ) := hline ▸ hkv
    induction ds with
    | nil =>
      intro done _ _ _ nx a b c t
      exact ⟨a, b, fun kv' h => originIn_mono (c kv' h) (fun _ h' => h'.imp_right (·.1)), t⟩
    | cons d ds ihd =>
      intro done hnd' hdone hds nx a b c t
      have hd := hds d (List.mem_cons_self ..)
      have hdnd := List.nodup_cons.mp hnd'
      simp only [List.foldl_cons]
      unfold sendTo
      dsimp only
      split
      · rename_i hv
        have hok := stateOk_upFiltering (hl kv hkv) hd hv
        have hog := originIn_upFiltering (hl kv hkv) (hent kv hkv).2 hd
        have hleaf : ArrTree φ n d (kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)) :=
          ArrTree.leaf kv hkvl hd hv
        rw [← hk2] at hog c
        obtain ⟨b', c'⟩ := lineO_insertT J a b c (hdone d (List.mem_cons_self ..)) hA hAk' hsk' hok
          (Hup _ _ _ _ (hl kv hkv) (hlk kv hkv) hT hd hv) hog n (by rw [← hTe]) (fun kv' h => hlk kv' (hline ▸ h)) (fun e he => t _ he)
          kv hkvl rfl hd rfl
        have t' := insert_presT (fun k x => ArrTree φ n k x) t hleaf (fun e he => ArrTree.node he hleaf)
        rw [hk2] at c'
        exact ihd (d :: done) hdnd.2
          (fun d' hd' hmem => by
            rcases List.mem_cons.mp hmem with h | h
            · exact hdnd.1 (h ▸ hd')
            · exact hdone d' (List.mem_cons_of_mem _ hd') h)
          (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd'))
          _ (lineOk_insert a hok) b' c' t'
      · exact ihd done hdnd.2 (fun d' hd' => hdone d' (List.mem_cons_of_mem _ hd'))
          (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd')) nx a b c t
  have key : ∀ (l : Line), (∀ kv ∈ l, kv ∈ line) → (l.map (·.1)).Nodup → ∀ (A : NodeId → Prop),
      (∀ kv ∈ l, ¬ A kv.1) → (∀ a, A a → Key (T - 1) a) → ∀ next, LineOk (T + 1) next → (∀ kv ∈ next, I kv.2) →
      (∀ kv ∈ next, OriginIn kv.2 (T - 1) A) → (∀ kv ∈ next, ArrTree φ n kv.1 kv.2) →
      ∀ kv ∈ l.foldl (fun next kv => sendAll φ kv next) next, I kv.2 := by
    intro l
    induction l with
    | nil => intro _ _ _ _ _ next _ h2 _ _; exact h2
    | cons kv rest ih =>
      intro hsub hndl A hA hAk next h1 h2 h3 h4
      have hkv := hsub kv (List.mem_cons_self ..)
      have hndl' := List.nodup_cons.mp hndl
      simp only [List.foldl_cons]
      obtain ⟨a, b, c, t⟩ := hsend kv hkv A (hA kv (List.mem_cons_self ..)) hAk (sonsOfMap φ kv.1) []
        (sonsOfMap_nodup φ kv.1) (fun _ _ h => absurd h List.not_mem_nil) (fun _ h => h) next h1 h2
        (fun kv' h => originIn_mono (h3 kv' h) (fun _ h' => Or.inl h')) h4
      refine ih (fun kv' h => hsub kv' (List.mem_cons_of_mem _ h)) hndl'.2 (fun a => A a ∨ a = kv.1) ?_
        (fun a h => h.elim (hAk a) (fun h' => h' ▸ hkey kv hkv)) _ a b c t
      intro kv' hkv' hor
      rcases hor with h | h
      · exact hA kv' (List.mem_cons_of_mem _ hkv') h
      · exact hndl'.1 (List.mem_map.mpr ⟨kv', hkv', h⟩)
  exact key line (fun _ h => h) hnd (fun _ => False) (fun _ _ h => h) (fun _ h => h.elim) []
    (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil)

theorem lineP_stepsT {φ : Cnf} (hbd : Bounded φ) {I : GPathB → Prop} (Hup : UpProv φ I)
    (J : ∀ U : Int, 2 ≤ U → JoinProvT φ I U) (hseed : I (initSeed (⟨0, 0⟩ : NodeId) "")) :
    ∀ n : Nat, LineP I ((n : Int) + 1) (steps φ n (init φ)) := by
  intro n
  induction n with
  | zero => exact lineP_init φ hseed
  | succ n ih =>
    obtain ⟨hl, hs, he, hnd, hidx⟩ := ih
    have hadv := lineO_advanceT hbd Hup n (J _ (by omega)) (by omega) hl hs he hnd hidx
    rw [steps_succ]
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact ⟨lineOk_advance hl, hadv, advance_entOk (by omega) hl he, advance_nodup φ _, advance_index φ hidx⟩

theorem run_provT {φ : Cnf} (hbd : Bounded φ) {I : GPathB → Prop} (Hup : UpProv φ I)
    (J : ∀ U : Int, 2 ≤ U → JoinProvT φ I U) (hseed : I (initSeed (⟨0, 0⟩ : NodeId) "")) :
    ∀ kv ∈ run φ, StateOk (stepCount φ) kv.1 kv.2 ∧ I kv.2 := by
  have hpos := stepCount_pos φ
  obtain ⟨hl, hs, _, _, _⟩ := lineP_stepsT hbd Hup J hseed (stepCount φ - 1).toNat
  have hrun : run φ = steps φ (stepCount φ - 1).toNat (init φ) := rfl
  rw [← hrun, show ((stepCount φ - 1).toNat : Int) + 1 = stepCount φ by rw [Int.toNat_of_nonneg (by omega)]; omega]
    at hl
  rw [← hrun] at hs
  exact fun kv hkv => ⟨hl kv hkv, hs kv hkv⟩

end SecLine

end AbsSatBingo.Model
