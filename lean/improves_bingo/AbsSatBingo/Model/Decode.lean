-- lean/improves_bingo/AbsSatBingo/Model/Decode.lean
import AbsSatBingo.Model.Struct

/-!
# De una camarilla a una solución, y el veredicto del lector (fase L7, parte 2)

**`sat_of_carried`**: una camarilla llevada por un estado con la estructura de la máquina (`Struct`), en el último
paso, se lee como una asignación que satisface `φ`. Es el argumento de `CnfChain` de `lean/improves_bin`, con las
tablas cambiadas por aristas:

1. **Un literal.** La camarilla está en `⟨Lₚ, bₚ⟩`; su requisito pone a la camarilla en el literal con el mismo
   índice, porque **la arista entre los dos nodos de la camarilla respeta el requisito** (`ReqEdges`). Un literal
   negado da un segundo salto por el requisito del nodo de negación.
2. **La ventana.** Por `PMP`/`GPMP` y los enlaces de la camarilla, su nodo en `L3` es la ventana `(L3, L2, L1)`.
3. **No prohibida.** Ningún nodo es una ventana prohibida (`NoForb`), así que la ventana no es `(0,0,0)`.

Y con esto, el teorema del plan: **`readerVerdict_iff_of_noZombie`** — si ningún estado que visita el lector es un
zombi, el veredicto del lector es exactamente la satisfacibilidad.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace Decode

open GPathB Driver Machine Struct

variable {φ : Cnf}

/-- La lectura: una variable es cierta si la camarilla está en el índice 1 en su paso. -/
def decode (S : Int → PathNodeId) : Assign := fun v => ((S (varStep v)).id.index == 1)

/-- **Los requisitos, leídos en la camarilla**: la arista entre dos nodos de la camarilla respeta el requisito. -/
theorem reqSat_of_carried (hbd : Bounded φ) {g : GPathB} {S : Int → PathNodeId} (hs : Struct φ g)
    (hc : Carried g S) (k : Int) (hk0 : 0 ≤ k) (hk1 : k < g.current_step) (r : NodeId)
    (hr : r ∈ reqOf φ (S k).id) (hr0 : 0 ≤ r.step) (hr1 : r.step < g.current_step) : (S r.step).id = r := by
  have hback := reqOf_backward φ hbd _ r hr
  rw [hc.step k hk0 hk1] at hback
  refine hs.req (S k) (S r.step) (hc.adj k r.step hk0 hk1 hr0 hr1) ?_ r hr (hc.step r.step hr0 hr1)
  intro he
  have h1 := hc.step k hk0 hk1
  rw [he, hc.step r.step hr0 hr1] at h1
  omega

theorem onMap_of_carried {g : GPathB} {S : Int → PathNodeId} (hs : Struct φ g) (hc : Carried g S) (k : Int)
    (hk0 : 0 ≤ k) (hk1 : k < g.current_step) : (S k).id ∈ mapNodes φ k := by
  obtain ⟨n, hn, _, _⟩ := hc.node k hk0 hk1
  have hid := node?_id hn
  have := hs.onmap n (node?_mem hn)
  rw [hid, hc.step k hk0 hk1] at this
  exact this

/-- **El valor de un literal es el índice de la camarilla en su paso.** -/
theorem litVal_of_node (hbd : Bounded φ) {g : GPathB} {S : Int → PathNodeId} (hs : Struct φ g)
    (hc : Carried g S) (hcs : g.current_step = stepCount φ)
    (l : Lit) (hl : l.v < φ.nVars) (b : Int) (hb : b = 0 ∨ b = 1)
    (hat : (S l.binStep).id = ⟨l.binStep, b⟩) :
    litVal (decode S) l = (b == 1) := by
  cases hp : l.pos with
  | true =>
    have hstep : l.binStep = varStep l.v := varStep_eq l hp
    have : (S (varStep l.v)).id.index = b := by rw [← hstep, hat]
    simp only [litVal, hp, decode, this]
    rfl
  | false =>
    have hstep : l.binStep = negStep l.v := negStep_eq l hp
    have hk0 : (0 : Int) ≤ negStep l.v := by simp only [negStep]; omega
    have hk1 : negStep l.v < g.current_step := by
      rw [hcs]; simp only [negStep, stepCount]; omega
    have hnegstep : (S (negStep l.v)).id.step = negStep l.v := by rw [← hstep, hat]
    have hreqs := reqOf_neg φ (S (negStep l.v)).id l.v hl hnegstep
    have hidx : (S (negStep l.v)).id.index = b := by rw [← hstep, hat]
    rw [hidx] at hreqs
    have hsecond := reqSat_of_carried hbd hs hc (negStep l.v) hk0 hk1 { step := varStep l.v, index := 1 - b }
      (by rw [hreqs]; exact List.mem_cons_self)
      (by simp only [varStep]; omega)
      (by rw [hcs]; simp only [varStep, stepCount]; omega)
    have hv : (S (varStep l.v)).id.index = 1 - b := by rw [hsecond]
    simp only [litVal, hp, decode, hv]
    rcases hb with rfl | rfl <;> rfl

/-- El id del padre (y del abuelo) de un nodo de la camarilla es el nodo anterior (y el de antes). -/
theorem parent_of_carried {g : GPathB} {S : Int → PathNodeId} (hs : Struct φ g) (hc : Carried g S) (k : Int)
    (hk0 : 0 < k) (hk1 : k < g.current_step) :
    (S k).parent_id = some (S (k - 1)).id ∧ (S k).gparent_id = (S (k - 1)).parent_id := by
  obtain ⟨n, hn, hp, _⟩ := hc.node k (by omega) hk1
  have hid := node?_id hn
  have h1 := hs.pmp n (node?_mem hn) _ (hp hk0)
  have h2 := hs.gpmp n (node?_mem hn) _ (hp hk0)
  rw [hid] at h1 h2
  exact ⟨h1.symm, h2⟩

theorem satClause_of_carried (hbd : Bounded φ) {g : GPathB} {S : Int → PathNodeId} (hs : Struct φ g)
    (hc : Carried g S) (hcs : g.current_step = stepCount φ)
    (j : Nat) (hjlt : j < φ.clauses.length) (c : Clause) (hj : φ.clauses[j]? = some c) :
    SatClause (decode S) c := by
  have pick : ∀ p, p < 3 →
      ∃ b : Int, (b = 0 ∨ b = 1) ∧ (S (clauseStep φ j p)).id = ⟨clauseStep φ j p, b⟩ ∧
        litVal (decode S) (litAt c p) = (b == 1) := by
    intro p hp
    have hk0 : (0 : Int) ≤ clauseStep φ j p := by simp only [clauseStep]; omega
    have hk : clauseStep φ j p < g.current_step := by
      rw [hcs]; simp only [clauseStep, stepCount]; omega
    have hstep := hc.step _ hk0 hk
    have hon := onMap_of_carried hs hc _ hk0 hk
    rw [mapNodes_two φ _ (by simp only [clauseStep]; omega)
      (by simp only [clauseStep, midFusion]; omega)
      (by simp only [clauseStep, fusionTop]; omega)] at hon
    obtain ⟨b, hb, hid⟩ : ∃ b : Int, (b = 0 ∨ b = 1) ∧
        (S (clauseStep φ j p)).id = ⟨clauseStep φ j p, b⟩ := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hon
      rcases hon with h | h
      · exact ⟨0, Or.inl rfl, h⟩
      · exact ⟨1, Or.inr rfl, h⟩
    refine ⟨b, hb, hid, ?_⟩
    have hreqs := reqOf_clause φ (S (clauseStep φ j p)).id j p c hp hjlt hj hstep
    have hidx : (S (clauseStep φ j p)).id.index = b := by rw [hid]
    rw [hidx] at hreqs
    obtain ⟨h1, h2, h3⟩ := hbd c (List.mem_of_getElem? hj)
    have hv : (litAt c p).v < φ.nVars := by unfold litAt; split <;> assumption
    have hlo : (0 : Int) ≤ (litAt c p).binStep := by have := (lit_step_bounds φ _ hv).1; omega
    have hhi : (litAt c p).binStep < g.current_step := by
      have := (lit_step_bounds φ _ hv).2
      rw [hcs]; simp only [midFusion, stepCount] at this ⊢; omega
    have hat := reqSat_of_carried hbd hs hc _ hk0 hk { step := (litAt c p).binStep, index := b }
      (by rw [hreqs]; exact List.mem_cons_self) hlo hhi
    exact litVal_of_node hbd hs hc hcs (litAt c p) hv b hb hat
  obtain ⟨b0, hb0, hid0, hv0⟩ := pick 0 (by omega)
  obtain ⟨b1, hb1, hid1, hv1⟩ := pick 1 (by omega)
  obtain ⟨b2, hb2, hid2, hv2⟩ := pick 2 (by omega)
  -- la ventana de la camarilla en L3
  have e21 : clauseStep φ j 2 - 1 = clauseStep φ j 1 := by simp only [clauseStep]; omega
  have e10 : clauseStep φ j 1 - 1 = clauseStep φ j 0 := by simp only [clauseStep]; omega
  have hhi2 : clauseStep φ j 2 < g.current_step := by
    rw [hcs]; simp only [clauseStep, stepCount]; omega
  obtain ⟨hpar2, hgp2⟩ := parent_of_carried hs hc (clauseStep φ j 2) (by simp only [clauseStep]; omega) hhi2
  obtain ⟨hpar1, _⟩ := parent_of_carried hs hc (clauseStep φ j 1) (by simp only [clauseStep]; omega)
    (by omega)
  rw [e21] at hpar2 hgp2
  rw [e10] at hpar1
  have hwin : S (clauseStep φ j 2) = clauseWindow φ j b0 b1 b2 := by
    have e : ∀ p : PathNodeId, p = ⟨p.id, p.parent_id, p.gparent_id⟩ := fun _ => rfl
    rw [e (S (clauseStep φ j 2)), hid2, hpar2, hgp2, hpar1, hid1, hid0]
    rfl
  -- y no está prohibida
  have hnot : isProhibited φ (S (clauseStep φ j 2)) = false := by
    obtain ⟨n, hn, _, _⟩ := hc.node _ (by simp only [clauseStep]; omega) hhi2
    have := hs.noforb n (node?_mem hn)
    rw [node?_id hn] at this
    exact this
  rw [hwin] at hnot
  have hne : ¬ (b0 = 0 ∧ b1 = 0 ∧ b2 = 0) := by
    intro hz
    have := (clauseWindow_prohibited_iff φ j hjlt b0 b1 b2).mpr hz
    rw [hnot] at this
    exact Bool.false_ne_true this
  simp only [SatClause]
  simp only [litAt] at hv0 hv1 hv2
  rw [hv0, hv1, hv2]
  rcases hb0 with rfl | rfl <;> rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl <;>
    first | (exfalso; exact hne ⟨rfl, rfl, rfl⟩) | decide

/-- **La decodificación**: una camarilla llevada por un estado con la estructura de la máquina, en el último paso,
es una solución. -/
theorem sat_of_carried (hbd : Bounded φ) {g : GPathB} {S : Int → PathNodeId} (hs : Struct φ g)
    (hc : Carried g S) (hcs : g.current_step = stepCount φ) : Sat (decode S) φ := by
  intro c hc'
  obtain ⟨j, hjlt, hj⟩ := exists_index_of_mem φ.clauses c hc'
  exact satClause_of_carried hbd hs hc hcs j hjlt c hj

-- ============================================================
-- El veredicto del lector
-- ============================================================

theorem lineOk_run (φ : Cnf) : LineOk (stepCount φ) (run φ) := by
  have hpos := stepCount_pos φ
  have hl := (init_inv φ (fun _ => false)).1
  have : ∀ (n : Nat) (T : Int) (line : Line), LineOk T line → LineOk (T + n) (steps φ n line) := by
    intro n
    induction n with
    | zero =>
      intro T line h
      simp only [steps]
      rw [show T + ((0 : Nat) : Int) = T by omega]
      exact h
    | succ n ih =>
      intro T line h
      have := ih (T + 1) _ (lineOk_advance (φ := φ) h)
      rw [show T + 1 + (n : Int) = T + ((n + 1 : Nat) : Int) by omega] at this
      exact this
  have h := this (stepCount φ - 1).toNat 1 (init φ) hl
  rw [Int.toNat_of_nonneg (by omega), show 1 + (stepCount φ - 1) = stepCount φ by omega] at h
  exact h

/-- Lo que el lector deja al terminar: un estado válido que visitó. -/
theorem readLoop_visited (g₀ : GPathB) :
    ∀ (n : Nat) (g h : GPathB), Visited g₀ g → g.isValid = true → readLoop n g = some h →
      Visited g₀ h ∧ h.isValid = true := by
  intro n
  induction n with
  | zero =>
    intro g h hv hval hr
    simp only [readLoop] at hr
    split at hr
    · cases hr
    · cases hr; exact ⟨hv, hval⟩
  | succ n ih =>
    intro g h hv hval hr
    simp only [readLoop] at hr
    split at hr
    · cases hr; exact ⟨hv, hval⟩
    · rename_i k _
      split at hr
      · cases hr
      · rename_i h' hh'
        unfold tryPins at hh'
        obtain ⟨q, _, hqf⟩ := List.exists_of_findSome?_eq_some hh'
        dsimp only at hqf
        split at hqf
        · rename_i hvq
          cases hqf
          exact ih _ h (Visited.pin q hv) hvq hr
        · cases hqf

/-- **Solidez del lector bajo `NoZombie`**: si el lector dice SAT y el estado en el que termina no es un zombi, la
fórmula es satisfacible. -/
theorem readerVerdict_sound_of_noZombie (hbd : Bounded φ) (h : readerVerdict φ = true)
    (hnz : ∀ kv ∈ run φ, ∀ h, Visited kv.2 h → NoZombie h) : Satisfiable φ := by
  unfold readerVerdict at h
  obtain ⟨kv, hkv, hs⟩ := List.any_eq_true.mp h
  unfold readG at hs
  dsimp only at hs
  split at hs
  · rename_i hv
    obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨hvis, hval⟩ := readLoop_visited kv.2 _ _ res Visited.start hv hres
    obtain ⟨S, hc⟩ := hnz kv hkv res hvis hval
    have hstr : Struct φ res := struct_visited hvis (struct_run hbd kv hkv)
    have hcs : res.current_step = stepCount φ := by
      rw [(shrinks_visited hvis).1.step]; exact (lineOk_run φ kv hkv).step
    exact ⟨decode S, sat_of_carried hbd hstr hc hcs⟩
  · cases hs

/-- **El veredicto del lector es la satisfacibilidad, si no hay zombis.** La meta del plan
`docs/plans/lean_bingo.md`: la única hipótesis abierta del lector es `NoZombie` en los estados que visita. -/
theorem readerVerdict_iff_of_noZombie (hbd : Bounded φ)
    (hnz : ∀ kv ∈ run φ, ∀ h, Visited kv.2 h → NoZombie h) : readerVerdict φ = true ↔ Satisfiable φ :=
  ⟨fun h => readerVerdict_sound_of_noZombie hbd h hnz,
   fun hs => readerVerdict_of_sat_noZombie φ hbd hs hnz⟩

end Decode

end AbsSatBingo.Model
