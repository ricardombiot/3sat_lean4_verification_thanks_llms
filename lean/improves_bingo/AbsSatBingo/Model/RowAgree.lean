-- lean/improves_bingo/AbsSatBingo/Model/RowAgree.lean
import AbsSatBingo.Model.LineInduction
import AbsSatBingo.Model.StarCore

/-!
# La contabilidad de la fila: lo que posee una cima cumple los requisitos de su fila

**`RowAgree`**: los vivos de una entrada de la línea concuerdan con los requisitos de su clave. Se conserva por la
llegada (filtrar por `rq d`, la fila nueva va por encima de los requisitos y el review solo quita), por el join y por
`advance` (`advance_rowAgree`). Con las claves de las cimas (`TopDocsId`) y `EdgesAlive` da la hipótesis de
contabilidad de `pinFreeF_of_topStarF` (`rowOwn_line`). Resultado: **`readerVerdict_iff_of_starCore`**, el
veredicto del lector bajo `StarCoreH` en cada línea como única hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Driver Machine

/-- **Los requisitos de una fila están por debajo de ella.** -/
theorem reqOf_step_lt {φ : Cnf} (hbd : Bounded φ) (d : NodeId) : ∀ b ∈ reqOf φ d, b.step < d.step := by
  intro b hb
  unfold reqOf at hb
  split at hb
  · exact absurd hb List.not_mem_nil
  split at hb
  · split at hb
    · exact absurd hb List.not_mem_nil
    · rw [List.mem_singleton] at hb; subst hb; show d.step - 1 < d.step; omega
  split at hb
  · exact absurd hb List.not_mem_nil
  split at hb
  · exact absurd hb List.not_mem_nil
  rename_i h0 h1 h2 h3
  split at hb
  · exact absurd hb List.not_mem_nil
  · rename_i c p hcp
    rw [List.mem_singleton] at hb; subst hb
    dsimp only [clauseOf] at hcp
    split at hcp
    · cases hcp
    · rename_i c' hc'
      cases hcp
      obtain ⟨h1', h2', h3'⟩ := hbd c (List.mem_of_getElem? hc')
      have hv : (litAt c ((d.step - midFusion φ - 1) % 3).toNat).v < φ.nVars := by
        unfold litAt; split <;> assumption
      have := (lit_step_bounds φ _ hv).2
      show (litAt c _).binStep < d.step
      omega

/-- **`RowAgree`**: los vivos de la entrada concuerdan con los requisitos de su clave. -/
def RowAgree (rq : NodeId → List NodeId) (kv : NodeId × GPathB) : Prop :=
  ∀ y ∈ kv.2.alive, ∀ b ∈ rq kv.1, y.id.step = b.step → y.id = b

/-- **La llegada concuerda con los requisitos de su destino.** -/
theorem rowAgree_upFiltering {φ : Cnf} (hbd : Bounded φ) {T : Int} {kv : NodeId × GPathB}
    (hok : StateOk T kv.1 kv.2) {d : NodeId} (hd : d ∈ sonsOfMap φ kv.1)
    (hv : (kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)).isValid = true) :
    RowAgree (reqOf φ) (d, kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)) := by
  obtain ⟨hf, heq⟩ := upFiltering_eq_arrival (kv := kv) hv
  intro y hy b hb hys
  change y ∈ (kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)).alive at hy
  rw [heq] at hy
  unfold arrival at hy
  let f := kv.2.filterAll (reqOf φ d)
  have hfs : f.current_step = T := (shrinks_filterAll _ _).1.step.trans hok.step
  have hds : d.step = f.current_step := by rw [hfs, sonsOfMap_step φ kv.1 d hd, hok.key]; omega
  have hb' : Below f := below_of_shrinks (shrinks_filterAll _ _) hok.below
  have hy' := (shrinks_review _).1.alive y hy
  rcases alive_addNode_cases (aliveDocs_filterAll hok.docs _) hb' hds hy' with ⟨hya, _⟩ | ⟨_, hyst⟩
  · exact pinned_filterAll_list hok.docs (reqOf φ d) hf b hb y hya hys
  · have := reqOf_step_lt hbd d b hb
    have hds' : d.step = (kv.2.filterAll (reqOf φ d)).current_step := hds
    omega

theorem rowAgree_doJoin {rq : NodeId → List NodeId} {key : NodeId} {e g : GPathB} (he : RowAgree rq (key, e))
    (hg : RowAgree rq (key, g)) : RowAgree rq (key, doJoin e g) := by
  intro y hy
  change y ∈ (doJoin e g).alive at hy
  unfold doJoin at hy
  split at hy
  · rcases (alive_join e g y).mp hy with h | h
    · exact he y h
    · exact hg y h
  · exact he y hy

theorem rowAgree_insert {rq : NodeId → List NodeId} {line : Line} {key : NodeId} {g : GPathB}
    (hl : ∀ kv ∈ line, RowAgree rq kv) (hg : RowAgree rq (key, g)) : ∀ kv ∈ Driver.insert line key g, RowAgree rq kv := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    subst hkey
    have he := hl _ (List.mem_of_find?_eq_some hfind)
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · rename_i hk
      have : kv0.1 = key' := by simpa using hk
      have hr := rowAgree_doJoin he hg
      intro y hy b hb hys
      exact hr y hy b (by simpa [this] using hb) hys
    · exact hl kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton] at h; subst h; exact hg

/-- **`advance` conserva `RowAgree`** (sin hipótesis sobre la línea de partida: cada entrada nueva es una llegada o
un join de llegadas a la misma clave). -/
theorem advance_rowAgree {φ : Cnf} (hbd : Bounded φ) {T : Int} {line : Line} (hl : LineOk T line) :
    ∀ kv ∈ advance φ line, RowAgree (reqOf φ) kv := by
  unfold advance
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, RowAgree (reqOf φ) kv) line ?_ []
    (fun _ h => absurd h List.not_mem_nil)
  intro next kv hkv hn
  unfold sendAll
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, RowAgree (reqOf φ) kv) _ ?_ next hn
  intro y d hd hy
  unfold sendTo
  dsimp only
  split
  · rename_i hv
    exact rowAgree_insert hy (rowAgree_upFiltering hbd (hl kv hkv) hd hv)
  · exact hy

/-- **La contabilidad de la fila en una línea**: lo que posee una cima de la línea concuerda con los requisitos de su
fila (la hipótesis `hag` de `pinFreeF_of_topStarF`). -/
theorem rowOwn_line {rq : NodeId → List NodeId} {T : Int} {line : Line} (hl : LineOk T line)
    (he : ∀ kv ∈ line, EntOk kv) (hr : ∀ kv ∈ line, RowAgree rq kv) :
    ∀ (t y : PathNodeId), t.id.step = T - 1 → (∃ g, famOf (· ∈ line) g ∧ g.Adj t y) →
      ∀ b ∈ rq t.id, y.id.step = b.step → y.id = b := by
  rintro t y hts ⟨g, ⟨kv, hkv, rfl⟩, hadj⟩ b hb hys
  obtain ⟨hta, hya⟩ := (he kv hkv).1.2.1 t y hadj
  obtain ⟨n, hn, hnid⟩ := (hl kv hkv).docs t hta
  have hkey : t.id = kv.1 := by
    rw [← hnid]; exact (he kv hkv).2 n hn (by rw [hnid, (hl kv hkv).step]; exact hts)
  exact hr kv hkv y hya b (by rw [← hkey]; exact hb) hys

/-- La contabilidad (`LineOk`, `EntOk`) de cada línea de la máquina, sin hipótesis. -/
theorem lineOk_entOk_steps (φ : Cnf) :
    ∀ n : Nat, LineOk ((n : Int) + 1) (steps φ n (init φ)) ∧ ∀ kv ∈ steps φ n (init φ), EntOk kv := by
  intro n
  induction n with
  | zero =>
    obtain ⟨hl, hent, _, _⟩ := lineInv_init φ
    exact ⟨hl, fun kv h => (hent kv h).1⟩
  | succ n ih =>
    rw [steps_succ]
    refine ⟨?_, advance_entOk (by omega) ih.1 ih.2⟩
    have := lineOk_advance (φ := φ) ih.1
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

/-- **La hipótesis**: en cada línea de la máquina, el núcleo por parejas de la estrella de cada cima la conserva y
cumple los enlaces. -/
def HypsStarCore (φ : Cnf) : Prop :=
  ∀ n : Nat, StarCoreH (famOf (· ∈ steps φ (n + 1) (init φ))) ((n : Int) + 2)

theorem hypsPin_of_starCore {φ : Cnf} (hbd : Bounded φ) (H : HypsStarCore φ) : HypsPin φ := by
  intro n
  obtain ⟨hl, he⟩ := lineOk_entOk_steps φ (n + 1)
  have hr : ∀ kv ∈ steps φ (n + 1) (init φ), RowAgree (reqOf φ) kv := by
    rw [steps_succ]; exact advance_rowAgree hbd (lineOk_entOk_steps φ n).1
  have hc : ((n + 1 : Nat) : Int) + 1 = (n : Int) + 2 := by push_cast; omega
  rw [hc] at hl
  exact pinFreeF_of_topStarF (topStarF_of_starCore (H n)) (rowOwn_line hl he hr)

/-- **El veredicto del lector es la satisfacibilidad bajo `StarCoreH` en cada línea como única hipótesis.** -/
theorem readerVerdict_iff_of_starCore {φ : Cnf} (hbd : Bounded φ) (H : HypsStarCore φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_pinFree hbd (hypsPin_of_starCore hbd H)

end GPathB

end AbsSatBingo.Model
