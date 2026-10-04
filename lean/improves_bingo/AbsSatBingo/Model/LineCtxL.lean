-- lean/improves_bingo/AbsSatBingo/Model/LineCtxL.lean
import AbsSatBingo.Model.LineCtxT

/-!
# La inducción de la línea con un UP que conoce la línea

Como `LineCtxT` (`run_provT`), pero el UP (`UpProvL`) recibe también que el remitente es una entrada de la línea del
nivel `n`. Así una hipótesis sobre las entradas de la línea se puede usar en el UP.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace SecLine

open GPathB Driver Machine CliqueSplit

/-- **El UP, sabiendo que el remitente es una entrada de la línea.** -/
def UpProvL (φ : Cnf) (I : GPathB → Prop) : Prop :=
  ∀ (n : Nat) (kv : NodeId × GPathB) (d : NodeId), kv ∈ steps φ n (init φ) → StateOk ((n : Int) + 1) kv.1 kv.2 →
    I kv.2 → d ∈ sonsOfMap φ kv.1 → (kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)).isValid = true →
    I (kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ))

theorem lineO_advanceL {φ : Cnf} (_hbd : Bounded φ) {I : GPathB → Prop} (Hup : UpProvL φ I) (n : Nat)
    (J : JoinProvT φ I ((n : Int) + 1 + 1)) (_hT : 1 ≤ (n : Int) + 1)
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
          (Hup n kv d hkvl (hTe ▸ hl kv hkv) (hlk kv hkv) hd hv) hog n (by rw [← hTe]) (fun kv' h => hlk kv' (hline ▸ h)) (fun e he => t _ he)
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

theorem lineP_stepsL {φ : Cnf} (hbd : Bounded φ) {I : GPathB → Prop} (Hup : UpProvL φ I)
    (J : ∀ U : Int, 2 ≤ U → JoinProvT φ I U) (hseed : I (initSeed (⟨0, 0⟩ : NodeId) "")) :
    ∀ n : Nat, LineP I ((n : Int) + 1) (steps φ n (init φ)) := by
  intro n
  induction n with
  | zero => exact lineP_init φ hseed
  | succ n ih =>
    obtain ⟨hl, hs, he, hnd, hidx⟩ := ih
    have hadv := lineO_advanceL hbd Hup n (J _ (by omega)) (by omega) hl hs he hnd hidx
    rw [steps_succ]
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact ⟨lineOk_advance hl, hadv, advance_entOk (by omega) hl he, advance_nodup φ _, advance_index φ hidx⟩

theorem run_provL {φ : Cnf} (hbd : Bounded φ) {I : GPathB → Prop} (Hup : UpProvL φ I)
    (J : ∀ U : Int, 2 ≤ U → JoinProvT φ I U) (hseed : I (initSeed (⟨0, 0⟩ : NodeId) "")) :
    ∀ kv ∈ run φ, StateOk (stepCount φ) kv.1 kv.2 ∧ I kv.2 := by
  have hpos := stepCount_pos φ
  obtain ⟨hl, hs, _, _, _⟩ := lineP_stepsL hbd Hup J hseed (stepCount φ - 1).toNat
  have hrun : run φ = steps φ (stepCount φ - 1).toNat (init φ) := rfl
  rw [← hrun, show ((stepCount φ - 1).toNat : Int) + 1 = stepCount φ by rw [Int.toNat_of_nonneg (by omega)]; omega]
    at hl
  rw [← hrun] at hs
  exact fun kv hkv => ⟨hl kv hkv, hs kv hkv⟩

end SecLine

end AbsSatBingo.Model
