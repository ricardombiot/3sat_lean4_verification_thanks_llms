-- lean/improves_bingo/AbsSatBingo/Model/DriverFam.lean
import AbsSatBingo.Model.LineStep
import AbsSatBingo.Model.ReaderTop

/-!
# `advance` en familia

Los hechos de construcción que usa el paso por la línea (`LineStep.lean`), demostrados sobre `Driver.advance`:
* una llegada válida es `arrival` (`upFiltering_eq_arrival`);
* cada llegada válida lleva sus camarillas a la entrada de su destino (`advance_lineUpC`, con `Has`);
* las entradas de `advance` están cubiertas por las llegadas (`advance_covers`);
* las claves de `advance` son únicas (`advance_nodup`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Driver Machine

/-- **Una llegada válida es `arrival`**, y su copia filtrada es válida. -/
theorem upFiltering_eq_arrival {φ : Cnf} {kv : NodeId × GPathB} {d : NodeId}
    (hv : (kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)).isValid = true) :
    (kv.2.filterAll (reqOf φ d)).isValid = true ∧
      kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ) = arrival (reqOf φ) "" (isProhibited φ) kv d := by
  unfold upFiltering up at hv ⊢
  by_cases hf : (kv.2.filterAll (reqOf φ d)).isValid = true
  · rw [if_pos hf]; exact ⟨hf, rfl⟩
  · rw [if_neg hf] at hv; exact absurd hv hf

-- ============================================================
-- Las camarillas de las llegadas llegan a su entrada
-- ============================================================

theorem advance_lineUpC {φ : Cnf} {T : Int} {line : Line} (hl : LineOk T line) {kv : NodeId × GPathB}
    (hkv : kv ∈ line) {d : NodeId} (hd : d ∈ sonsOfMap φ kv.1)
    (hv : (kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)).isValid = true) {S : Int → PathNodeId}
    (hc : Carried (kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)) S) : Has S d (advance φ line) := by
  have hok : StateOk T kv.1 kv.2 := hl kv hkv
  have hok2 := stateOk_upFiltering hok hd hv
  unfold advance
  refine foldl_establish _ (fun next => Has S d next) (LineOk (T + 1)) line
    (fun _ kv' hkv' hx => lineOk_sendAll (hl kv' hkv') hx)
    (fun _ kv' _ _ hx => by
      unfold sendAll
      exact foldl_pres _ (fun next => Has S d next) _ (fun y d' _ hy => has_sendTo hy) _ hx)
    kv ?_ hkv [] (fun _ h => absurd h List.not_mem_nil)
  intro x hx
  unfold sendAll
  refine foldl_establish _ (fun next => Has S d next) (LineOk (T + 1)) _
    (fun y d' hd' hy => lineOk_sendTo hok d' hd' hy)
    (fun y d' _ _ hy => has_sendTo hy) d ?_ hd x hx
  intro y hy
  unfold sendTo
  dsimp only
  rw [if_pos hv]
  exact has_insert_self hy hok2 hc

theorem mem_of_has {S : Int → PathNodeId} {key : NodeId} {line : Line} (h : Has S key line) :
    ∃ kv ∈ line, kv.1 = key ∧ Carried kv.2 S := by
  obtain ⟨g, hf, hc⟩ := h
  exact ⟨(key, g), List.mem_of_find?_eq_some hf, rfl, hc⟩

-- ============================================================
-- Cobertura y claves únicas
-- ============================================================

theorem covers_pair {F : GPathB → Prop} {e g : GPathB} (he : Covers (· = e) F) (hg : Covers (· = g) F) :
    Covers (fun h => h = e ∨ h = g) F := by
  rintro h (rfl | rfl)
  · exact he _ rfl
  · exact hg _ rfl

theorem covers_doJoin {F : GPathB → Prop} {e g : GPathB} (he : Covers (· = e) F) (hg : Covers (· = g) F) :
    Covers (· = doJoin e g) F := by
  unfold doJoin
  split
  · exact covers_trans (covers_join e g) (covers_pair he hg)
  · exact he

theorem covers_insert {F : GPathB → Prop} {line : Line} {key : NodeId} {g : GPathB}
    (hl : ∀ kv ∈ line, Covers (· = kv.2) F) (hg : Covers (· = g) F) :
    ∀ kv ∈ Driver.insert line key g, Covers (· = kv.2) F := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have he := hl _ (List.mem_of_find?_eq_some hfind)
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact covers_doJoin he hg
    · exact hl kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton] at h; subst h; exact hg

theorem nodup_insert {line : Line} {key : NodeId} {g : GPathB} (hl : (line.map (·.1)).Nodup) :
    ((Driver.insert line key g).map (·.1)).Nodup := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    rw [List.map_map]
    have : ((·.1) ∘ fun kv : NodeId × GPathB => if (kv.1 == key) = true then (key, doJoin e g) else kv) =
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

/-- La familia de las llegadas de una línea de la máquina. -/
abbrev ArrOf (φ : Cnf) (line : Line) : GPathB → Prop :=
  Arrivals (reqOf φ) "" (isProhibited φ) (· ∈ line) (fun k d => d ∈ sonsOfMap φ k)

/-- **Las entradas de `advance` están cubiertas por las llegadas.** -/
theorem advance_covers (φ : Cnf) (line : Line) :
    ∀ kv ∈ advance φ line, Covers (· = kv.2) (ArrOf φ line) := by
  unfold advance
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, Covers (· = kv.2) (ArrOf φ line)) line ?_ []
    (fun _ h => absurd h List.not_mem_nil)
  intro next kv hkv hn
  unfold sendAll
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, Covers (· = kv.2) (ArrOf φ line)) _ ?_ next hn
  intro y d hd hy
  unfold sendTo
  dsimp only
  split
  · rename_i hv
    obtain ⟨hf, heq⟩ := upFiltering_eq_arrival (kv := kv) hv
    refine covers_insert hy ?_
    rw [heq]
    exact covers_of_sub (fun g hg => ⟨kv, d, hkv, hd, hf, hg⟩)
  · exact hy

/-- **Las claves de `advance` son únicas.** -/
theorem advance_nodup (φ : Cnf) (line : Line) : ((advance φ line).map (·.1)).Nodup := by
  unfold advance
  refine foldl_pres _ (fun next : Line => (next.map (·.1)).Nodup) line ?_ [] List.nodup_nil
  intro next kv _ hn
  unfold sendAll
  refine foldl_pres _ (fun next : Line => (next.map (·.1)).Nodup) _ ?_ next hn
  intro y d _ hy
  unfold sendTo
  dsimp only
  split
  · exact nodup_insert hy
  · exact hy

theorem eq_of_nodup_keys {line : Line} (h : (line.map (·.1)).Nodup) {a b : NodeId × GPathB} (ha : a ∈ line)
    (hb : b ∈ line) (hab : a.1 = b.1) : a = b := by
  induction line with
  | nil => exact absurd ha List.not_mem_nil
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (hab ▸ List.mem_map.mpr ⟨b, hb', rfl⟩) h.1
    · exact absurd (hab.symm ▸ List.mem_map.mpr ⟨a, ha', rfl⟩) h.1
    · exact ih h.2 ha' hb'

end GPathB

end AbsSatBingo.Model
