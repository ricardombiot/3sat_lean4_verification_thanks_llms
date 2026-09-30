-- lean/improves_bingo/AbsSatBingo/Model/PreClause.lean
import AbsSatBingo.Model.LiveDriver
import AbsSatBingo.Model.CliqueSplit
import AbsSatBingo.Model.EdgeCliqueUp

/-!
# Antes de las cláusulas

Hasta la fusión central el mapa no tiene ventanas prohibidas y los únicos requisitos son los de negación (la cima del
propio remitente). Allí una selección válida es exactamente la rama de una asignación (`validSel_pid`,
`pid_of_validSel`), y un nodo solo depende de las variables de su ventana (`pid_agree`, `vars_of_pid_eq`). Con eso,
**parcheo** (`patch`): asignaciones que concuerdan dos a dos en las variables que cada una fija se juntan en una sola.
Es Helly para asignaciones parciales, y es lo que hace que tres nodos compatibles dos a dos estén en una misma rama.

* `EdgeClique` en toda la línea antes de las cláusulas (`pre_line`): el filtro no toca nada y no hay ventanas
  saltadas.
* **`triSplit`**: un triángulo de la unión de dos llegadas fijadas es triángulo de una de ellas (parcheo de sus nodos
  y sus pins; la rama parcheada la lleva el remitente de su clave, `steps_has_sel`).
* **`NoTriF`**: la familia fantasma no prohíbe ningún triángulo del estado fijado; pasa la llegada y la unión
  (`noTri_next`), así que antes de las cláusulas `HNew` se cumple sin más (`hnew_of_noTri`).
* **`spineVerdict_iff_of_liveLineC`**: el veredicto de la espina bajo `PinJoinSplitAll` y `NoNewClose` solo en las
  líneas de cláusula con dos remitentes (la línea de la fusión central tiene un solo remitente; desde la fusión final no
  hay otra entrada).
* **`HMixed`** y **`spineVerdict_iff_of_mixed`**: `NoNewClose` sale de que un trío de cadena prohibido en una entrada
  que es triángulo en un remitente sea un triángulo mezclado del join de ese remitente (no es triángulo en ninguna de
  sus dos llegadas fijadas); la familia del remitente lo prohíbe por definición (`hnew_of_mixed`). Medido:
  `probe_hnewcl.jl`, 18/18 y 48/48.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (shiftPid)

namespace PreClause

open GPathB Driver Machine CliqueSplit

variable {φ : Cnf}

-- ============================================================
-- Selecciones y asignaciones
-- ============================================================

/-- La asignación de una selección: el valor de cada variable en su paso. -/
def aOf (S : Int → PathNodeId) : Assign := fun v => (S (varStep v)).id.index == 1

theorem shift_pid (a : Assign) {j : Int} (hj : 1 ≤ j) :
    shiftPid (pidOfAssign φ a (j - 1)) (selOfAssign φ a j) = pidOfAssign φ a j := by
  simp only [shiftPid, pidOfAssign]
  congr 1
  · rw [if_pos (by omega)]
  · by_cases h : 0 < j - 1
    · rw [if_pos h, if_pos (by omega), show j - 1 - 1 = j - 2 by omega]
    · rw [if_neg h, if_neg (by omega)]

theorem mid_lt_stepCount (φ : Cnf) : midFusion φ < stepCount φ := by
  unfold midFusion stepCount; omega

/-- **Toda asignación da una selección válida** hasta la fusión central (no hay ventanas prohibidas). -/
theorem validSel_pid (hbd : Bounded φ) (a : Assign) {t : Int} (ht : t ≤ midFusion φ) :
    ValidSel φ t (pidOfAssign φ a) := by
  have hsc := mid_lt_stepCount φ
  refine ⟨fun j _ _ => selOfAssign_step φ a j, ?_, fun j h1 _ => shift_pid a h1, ?_, ?_, ?_⟩
  · simp [pidOfAssign, selOfAssign, root]
  · intro j h1 h2
    have := selOfAssign_son φ a (j - 1) (by omega) (by omega)
    rw [show j - 1 + 1 = j by omega] at this
    exact this
  · intro j _ _ r hr _ _
    exact reqSat_selOfAssign φ hbd a j r hr
  · intro j _ h2
    have hs : (pidOfAssign φ a j).id.step = j := selOfAssign_step φ a j
    unfold isProhibited isL3
    rw [hs, decide_eq_false (show ¬ midFusion φ < j by omega)]
    rfl

theorem bit_index {i : Int} (h : i = 0 ∨ i = 1) : bit (i == 1) = i := by
  rcases h with rfl | rfl <;> rfl

/-- **Toda selección válida es la rama de su asignación**, hasta la fusión central. -/
theorem pid_of_validSel {t : Int} {S : Int → PathNodeId} (hv : ValidSel φ t S) (ht : t ≤ midFusion φ) :
    ∀ k, 0 ≤ k → k ≤ t → S k = pidOfAssign φ (aOf S) k := by
  have key : ∀ n : Nat, (n : Int) ≤ t → S n = pidOfAssign φ (aOf S) n := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [show ((0 : Nat) : Int) = 0 by rfl, hv.root]
      simp [pidOfAssign, selOfAssign, root]
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hj1 : (1 : Int) ≤ ((n + 1 : Nat) : Int) := by omega
      have hsh := hv.shift _ hj1 hn
      have hson := hv.son _ hj1 hn
      rw [show ((n + 1 : Nat) : Int) - 1 = (n : Int) by push_cast; omega] at hsh hson
      rw [ih'] at hsh hson
      -- el id del paso n + 1
      suffices hid : (S ((n + 1 : Nat) : Int)).id = selOfAssign φ (aOf S) ((n + 1 : Nat) : Int) by
        rw [← hsh, hid, show (n : Int) = ((n + 1 : Nat) : Int) - 1 by push_cast; omega]
        exact shift_pid _ hj1
      have hstep : (S ((n + 1 : Nat) : Int)).id.step = ((n + 1 : Nat) : Int) := hv.step _ (by omega) hn
      have hsn : (pidOfAssign φ (aOf S) (n : Int)).id.step = n := selOfAssign_step φ _ _
      unfold sonsOfMap at hson
      have hm : ((n + 1 : Nat) : Int) ≤ midFusion φ := by omega
      by_cases hodd : 0 < (n : Int) ∧ (n : Int) < midFusion φ ∧ (n : Int) % 2 = 1
      · -- paso de negación: el hijo del valor de la variable
        rw [hsn, if_pos hodd, List.mem_singleton] at hson
        rw [hson]
        have hlt : ((n + 1 : Nat) : Int) < midFusion φ := by unfold midFusion at hm ⊢; omega
        unfold selOfAssign
        rw [if_neg (by omega), if_pos hlt, if_neg (by omega)]
        have hn' : (pidOfAssign φ (aOf S) (n : Int)).id = ⟨n, bit (aOf S (varOfStep n))⟩ := by
          show selOfAssign φ (aOf S) (n : Int) = _
          unfold selOfAssign; rw [if_neg (by omega), if_pos hodd.2.1, if_pos hodd.2.2]
        rw [hn', bit_not]
        simp only [NodeId.mk.injEq]
        refine ⟨by push_cast; omega, ?_⟩
        congr 3
        unfold varOfStep; omega
      · rw [hsn, if_neg hodd] at hson
        by_cases hmid : ((n + 1 : Nat) : Int) = midFusion φ
        · -- la fusión central
          rw [show (n : Int) + 1 = midFusion φ by push_cast at hmid; omega,
            mapNodes_fusion φ _ (Or.inr (Or.inl rfl)), List.mem_singleton] at hson
          rw [hson]
          unfold selOfAssign
          rw [if_neg (by omega), if_neg (by omega), if_pos hmid, hmid]
        · -- paso de variable: los dos valores
          have hlt : ((n + 1 : Nat) : Int) < midFusion φ := by omega
          have hodd' : ((n + 1 : Nat) : Int) % 2 = 1 := by
            have : ¬ ((0 : Int) < n ∧ (n : Int) < midFusion φ ∧ (n : Int) % 2 = 1) := hodd
            unfold midFusion at hlt this; omega
          rw [mapNodes_two φ _ (by omega) (by push_cast at hmid; omega) (by unfold midFusion at hlt; unfold fusionTop; omega)]
            at hson
          have hidx : (S ((n + 1 : Nat) : Int)).id.index = 0 ∨ (S ((n + 1 : Nat) : Int)).id.index = 1 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hson
            rcases hson with h | h <;> rw [h] <;> simp
          unfold selOfAssign
          rw [if_neg (by omega), if_pos hlt, if_pos hodd']
          have hv' : varStep (varOfStep ((n + 1 : Nat) : Int)) = ((n + 1 : Nat) : Int) := by
            unfold varStep varOfStep; omega
          show _ = NodeId.mk ((n + 1 : Nat) : Int)
            (bit ((S (varStep (varOfStep ((n + 1 : Nat) : Int)))).id.index == 1))
          rw [hv', bit_index hidx]
          exact nodeId_eq hstep rfl
  intro k hk0 hkt
  have := key k.toNat (by omega)
  rwa [Int.toNat_of_nonneg hk0] at this

-- ============================================================
-- Un nodo solo depende de las variables de su ventana
-- ============================================================

/-- `v` es una variable de la ventana del paso `k`: la de `k`, `k - 1` o `k - 2` (entre la raíz y la fusión). -/
def VarsAt (φ : Cnf) (k : Int) (v : Nat) : Prop :=
  ∃ i, (i = k ∨ i = k - 1 ∨ i = k - 2) ∧ 0 < i ∧ i < midFusion φ ∧ v = varOfStep i

theorem sel_local {a a' : Assign} {i : Int} (hi : i ≤ midFusion φ)
    (h : 0 < i → i < midFusion φ → a (varOfStep i) = a' (varOfStep i)) : selOfAssign φ a i = selOfAssign φ a' i := by
  unfold selOfAssign
  by_cases h0 : i ≤ 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases hm : i < midFusion φ
    · rw [if_pos hm, if_pos hm, h (by omega) hm]
    · rw [if_neg hm, if_neg hm, if_pos (by omega), if_pos (by omega)]

theorem sel_inj {a a' : Assign} {i : Int} (h0 : 0 < i) (hm : i < midFusion φ)
    (h : selOfAssign φ a i = selOfAssign φ a' i) : a (varOfStep i) = a' (varOfStep i) := by
  unfold selOfAssign at h
  rw [if_neg (show ¬ i ≤ 0 by omega), if_neg (show ¬ i ≤ 0 by omega), if_pos hm, if_pos hm] at h
  split at h
  · simp only [NodeId.mk.injEq, true_and] at h
    cases hb : a (varOfStep i) <;> cases hb' : a' (varOfStep i) <;> simp_all [bit]
  · simp only [NodeId.mk.injEq, true_and] at h
    cases hb : a (varOfStep i) <;> cases hb' : a' (varOfStep i) <;> simp_all [bit]

/-- **Un nodo de la rama solo depende de las variables de su ventana.** -/
theorem pid_agree {a a' : Assign} {k : Int} (hk : k ≤ midFusion φ) (h : ∀ v, VarsAt φ k v → a v = a' v) :
    pidOfAssign φ a k = pidOfAssign φ a' k := by
  have hs : ∀ i, (i = k ∨ i = k - 1 ∨ i = k - 2) → selOfAssign φ a i = selOfAssign φ a' i := by
    intro i hi
    exact sel_local (by omega) (fun h0 hm => h _ ⟨i, hi, h0, hm, rfl⟩)
  unfold pidOfAssign
  rw [hs k (Or.inl rfl), hs (k - 1) (Or.inr (Or.inl rfl)), hs (k - 2) (Or.inr (Or.inr rfl))]

/-- **Y las determina**: dos ramas con el mismo nodo en `k` coinciden en las variables de su ventana. -/
theorem vars_of_pid_eq {a a' : Assign} {k : Int} (h : pidOfAssign φ a k = pidOfAssign φ a' k) {v : Nat}
    (hv : VarsAt φ k v) : a v = a' v := by
  obtain ⟨i, hi, h0, hm, rfl⟩ := hv
  apply sel_inj h0 hm
  unfold pidOfAssign at h
  simp only [PathNodeId.mk.injEq] at h
  obtain ⟨e0, e1, e2⟩ := h
  rcases hi with rfl | rfl | rfl
  · exact e0
  · rw [if_pos (by omega), if_pos (by omega)] at e1; exact Option.some.inj e1
  · rw [if_pos (by omega), if_pos (by omega)] at e2; exact Option.some.inj e2

-- ============================================================
-- Parcheo
-- ============================================================

/-- **Parcheo** (Helly para asignaciones parciales): asignaciones que concuerdan dos a dos en las variables que cada
una fija se juntan en una sola que concuerda con todas. -/
theorem patch {ι : Type} (l : List ι) (A : ι → Assign) (V : ι → Nat → Prop)
    (h : ∀ i ∈ l, ∀ j ∈ l, ∀ v, V i v → V j v → A i v = A j v) :
    ∃ a : Assign, ∀ i ∈ l, ∀ v, V i v → a v = A i v := by
  classical
  refine ⟨fun v => if hv : ∃ i ∈ l, V i v then A hv.choose v else false, ?_⟩
  intro i hi v hvi
  have hex : ∃ i ∈ l, V i v := ⟨i, hi, hvi⟩
  simp only [dif_pos hex]
  exact h _ hex.choose_spec.1 i hi v hex.choose_spec.2 hvi

-- ============================================================
-- `EdgeClique` en la línea antes de las cláusulas
-- ============================================================

theorem edgeClique_review {g : GPathB} (h : EdgeClique g) : EdgeClique g.review := by
  intro y w ha
  have hs := (shrinks_review g).1
  obtain ⟨S, hc, hy, hw⟩ := h y w (hs.adj _ _ ha)
  refine ⟨S, carried_review hc, ?_, ?_⟩ <;> rw [hs.step] <;> assumption

/-- Antes de las cláusulas no se salta ninguna ventana. -/
theorem skips_pre {g : GPathB} {d : NodeId} (hd : d.step ≤ midFusion φ) :
    g.skipsWindow d (isProhibited φ) = false := by
  unfold skipsWindow
  rw [List.any_eq_false]
  intro pid hp
  have hid := mapId_of_mem_shiftRowIds hp
  have h1 : decide (midFusion φ < pid.id.step) = false := decide_eq_false (by rw [hid]; omega)
  simp [isProhibited, isL3, h1]

/-- Antes de las cláusulas, fuera de la negación no hay requisitos. -/
theorem reqOf_pre_nil {d : NodeId} (hn : ¬ IsNeg φ d) (hd : d.step ≤ midFusion φ) : reqOf φ d = [] := by
  unfold reqOf
  by_cases h0 : d.step ≤ 0
  · rw [if_pos h0]
  rw [if_neg h0]
  by_cases hm : d.step < midFusion φ
  · rw [if_pos hm, if_pos]
    exact Classical.byContradiction fun h => hn ⟨by omega, hm, by omega⟩
  · rw [if_neg hm, if_pos (by omega)]

/-- **Antes de las cláusulas el filtro de la llegada no toca nada**: sin requisitos, o el pin de la propia cima. -/
theorem foldl_req_pre {kv : NodeId × GPathB} (htid : TopDocsId kv.2 kv.1)
    (hcs : kv.2.current_step = kv.1.step + 1) {d : NodeId} (hs : d ∈ sonsOfMap φ kv.1) (hd : d.step ≤ midFusion φ) :
    (reqOf φ d).foldl filterRequire kv.2 = kv.2 := by
  by_cases hn : IsNeg φ d
  · obtain ⟨hk, _⟩ := sons_neg hn hs
    rw [reqOf_negd hn, ← hk]
    exact filterRequire_noop (fun n hn hst => htid n hn (by rw [hcs]; omega))
  · rw [reqOf_pre_nil hn hd]; rfl

/-- **La llegada conserva `EdgeClique` y `DocsAlive`** antes de las cláusulas. -/
theorem edgeClique_arr {kv : NodeId × GPathB} {T : Int} (hok : StateOk T kv.1 kv.2) (hT : 1 ≤ T)
    (htid : TopDocsId kv.2 kv.1) (he : EdgeClique kv.2) (hda : DocsAlive kv.2) {d : NodeId} (hs : Sends φ kv d)
    (hd : d.step ≤ midFusion φ) : EdgeClique (arrOf φ kv d) ∧ DocsAlive (arrOf φ kv d) := by
  have hcs : kv.2.current_step = kv.1.step + 1 := by rw [hok.step, hok.key]; omega
  have hvY : (kv.2.filterAll (reqOf φ d)).isValid = true :=
    valid_of_up (d := d) (title := "") (forb := isProhibited φ) hs.2
  have hf : kv.2.filterAll (reqOf φ d) = kv.2.review := by unfold filterAll; rw [foldl_req_pre htid hcs hs.1 hd]
  have hsf := shrinks_filterAll kv.2 (reqOf φ d)
  have hdf : d.step = (kv.2.filterAll (reqOf φ d)).current_step := by
    rw [hsf.1.step, sonsOfMap_step φ kv.1 d hs.1, hcs]
  have heF : EdgeClique (kv.2.filterAll (reqOf φ d)) := by rw [hf]; exact edgeClique_review he
  have hdaF : DocsAlive (kv.2.filterAll (reqOf φ d)) := docsAlive_filterAll hda _ hvY
  have hb : Below (kv.2.filterAll (reqOf φ d)) := below_of_shrinks hsf hok.below
  have hup : arrOf φ kv d = ((kv.2.filterAll (reqOf φ d)).addNode d "" (isProhibited φ)).review := by
    unfold arrOf upFiltering up; rw [if_pos hvY]
  have hva := hs.2
  rw [hup] at hva ⊢
  exact ⟨edgeClique_review (edgeClique_addNode heF (by rw [hsf.1.step, hok.step]; omega) (skips_pre hd) hdf hb hdaF),
    docsAlive_review hva (Or.inl (docsAlive_addNode hdaF))⟩

theorem insert_pres (P : GPathB → Prop) (hdj : ∀ e g, P e → P g → P (doJoin e g)) {line : Line} {key : NodeId}
    {g : GPathB} (hl : ∀ kv ∈ line, P kv.2) (hg : P g) : ∀ kv ∈ Driver.insert line key g, P kv.2 := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have he := hl _ (List.mem_of_find?_eq_some hfind)
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact hdj _ _ he hg
    · exact hl kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton] at h; subst h; exact hg

/-- Una propiedad que conservan los joins y tienen las llegadas válidas la tienen todas las entradas de `advance`. -/
theorem advance_pres (P : GPathB → Prop) (hdj : ∀ e g, P e → P g → P (doJoin e g)) {line : Line}
    (harr : ∀ kv ∈ line, ∀ d, Sends φ kv d → P (arrOf φ kv d)) : ∀ E ∈ advance φ line, P E.2 := by
  unfold advance
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, P kv.2) line ?_ [] (fun _ h => absurd h List.not_mem_nil)
  intro next kv hkv hn
  unfold sendAll
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, P kv.2) _ ?_ next hn
  intro y d hd hy
  unfold sendTo
  dsimp only
  split
  · rename_i hv
    exact insert_pres P hdj hy (harr kv hkv d ⟨hd, hv⟩)
  · exact hy

theorem seed_eq : initSeed (⟨0, 0⟩ : NodeId) "" = (GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)).review := by
  show up GPathB.empty ⟨0, 0⟩ "" (fun _ => false) = _
  unfold up; rw [if_pos (show GPathB.empty.isValid = true by rfl)]

theorem seed_alive : (GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)).alive = [CliqueSplit.root] := by rfl
theorem seed_edges : (GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)).edges = [] := by rfl

/-- **La semilla**: su único vivo es la raíz, que está en la rama de cualquier asignación. -/
theorem edgeClique_seed (φ : Cnf) : EdgeClique (initSeed (⟨0, 0⟩ : NodeId) "") ∧ DocsAlive (initSeed ⟨0, 0⟩ "") := by
  obtain ⟨hl, g, hf, hc⟩ := init_inv φ (fun _ => false)
  rw [init_eq] at hf
  have hg : g = initSeed ⟨0, 0⟩ "" := by
    simp only [List.find?, selOfAssign] at hf
    simp at hf; exact hf.symm
  subst hg
  have hmem : ((⟨0, 0⟩ : NodeId), initSeed (⟨0, 0⟩ : NodeId) "") ∈ init φ := by
    rw [init_eq]; exact List.mem_singleton_self _
  have hv := (hl _ hmem).valid
  have hsub : Sub (initSeed (⟨0, 0⟩ : NodeId) "") (GPathB.empty.addNode ⟨0, 0⟩ "" (fun _ => false)) := by
    rw [seed_eq]; exact (shrinks_review _).1
  refine ⟨fun y w ha => ?_, ?_⟩
  · have ha' := hsub.adj _ _ ha
    rw [adj_iff, seed_alive, seed_edges] at ha'
    simp only [List.mem_singleton, List.not_mem_nil, false_and, exists_false, or_false] at ha'
    obtain ⟨rfl, rfl⟩ := ha'
    have h0 : pidOfAssign φ (fun _ => false) 0 = CliqueSplit.root := by
      simp [pidOfAssign, selOfAssign, CliqueSplit.root]
    exact ⟨_, hc, ⟨0, Int.le_refl 0, by rw [(hl _ hmem).step]; omega, h0⟩, ⟨0, Int.le_refl 0, by rw [(hl _ hmem).step]; omega, h0⟩⟩
  · rw [seed_eq] at hv ⊢
    exact docsAlive_review hv (Or.inl (docsAlive_addNode (fun n hn => absurd hn List.not_mem_nil)))

theorem docsAlive_doJoin {e g : GPathB} (he : DocsAlive e) (hg : DocsAlive g) : DocsAlive (doJoin e g) := by
  unfold doJoin; split
  · exact docsAlive_join he hg
  · exact he

/-- **Toda entrada de la línea antes de las cláusulas tiene `EdgeClique`** (y `DocsAlive`). -/
theorem pre_line (hbd : Bounded φ) : ∀ n : Nat, (n : Int) ≤ midFusion φ →
    ∀ kv ∈ steps φ n (init φ), EdgeClique kv.2 ∧ DocsAlive kv.2 := by
  intro n
  induction n with
  | zero =>
    intro _ kv hkv
    rw [show steps φ 0 (init φ) = init φ from rfl, init_eq, List.mem_singleton] at hkv
    subst hkv
    exact edgeClique_seed φ
  | succ n ih =>
    intro hn
    rw [steps_succ]
    have ih' := ih (by omega)
    obtain ⟨hl, hent, _⟩ := line_facts hbd n
    refine advance_pres (fun g => EdgeClique g ∧ DocsAlive g)
      (fun e g he hg => ⟨edgeClique_doJoin he.1 hg.1, docsAlive_doJoin he.2 hg.2⟩) ?_
    intro kv hkv d hs
    have hok := hl kv hkv
    have hd : d.step = (n : Int) + 1 := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key]; omega
    exact edgeClique_arr hok (by omega) (hent kv hkv).2 (ih' kv hkv).1 (ih' kv hkv).2 hs (by push_cast at hn; omega)

-- ============================================================
-- Piezas del parcheo: nodos y pins
-- ============================================================

theorem carried_pinF {g : GPathB} {S : Int → PathNodeId} (h : Carried g S) {R : List NodeId}
    (ha : ∀ r ∈ R, Agrees g.current_step S r) : Carried (pinF g R) S := by
  have key : ∀ (R : List NodeId) (g : GPathB), Carried g S → (∀ r ∈ R, Agrees g.current_step S r) →
      Carried (R.foldl filterRequire g) S := by
    intro R
    induction R with
    | nil => intro g h _; exact h
    | cons r rs ih =>
      intro g h ha
      rw [List.foldl_cons]
      refine ih _ (carried_filterRequire h (ha r List.mem_cons_self)) ?_
      intro r' hr'
      rw [(shrinks_filterRequire g r).1.step]; exact ha r' (List.mem_cons_of_mem _ hr')
  exact carried_review (carried_dirty (key R g h ha) true)

/-- Una pieza del parcheo: un nodo (fija su ventana) o un pin (fija el id de su paso). -/
abbrev Item := PathNodeId ⊕ NodeId

def Holds (φ : Cnf) (c : Assign) : Item → Prop
  | .inl x => pidOfAssign φ c x.id.step = x
  | .inr r => selOfAssign φ c r.step = r

def IV (φ : Cnf) : Item → Nat → Prop
  | .inl x => VarsAt φ x.id.step
  | .inr r => fun v => 0 < r.step ∧ r.step < midFusion φ ∧ v = varOfStep r.step

def stepOf : Item → Int
  | .inl x => x.id.step
  | .inr r => r.step

open Classical in
/-- La asignación de una pieza (una cualquiera en la que vale). -/
noncomputable def IA (φ : Cnf) (i : Item) : Assign :=
  if h : ∃ a, Holds φ a i then h.choose else fun _ => false

theorem IA_spec {i : Item} (hex : ∃ a, Holds φ a i) : Holds φ (IA φ i) i := by
  unfold IA; rw [dif_pos hex]; exact hex.choose_spec

theorem agree_of_holds {c : Assign} {i : Item} (h : Holds φ c i) : ∀ v, IV φ i v → c v = IA φ i v := by
  have hc := IA_spec ⟨c, h⟩
  intro v hv
  cases i with
  | inl x => exact vars_of_pid_eq (h.trans hc.symm) hv
  | inr r => obtain ⟨h0, hm, rfl⟩ := hv; exact sel_inj h0 hm (h.trans hc.symm)

theorem holds_of_agree {b : Assign} {i : Item} (hex : ∃ a, Holds φ a i) (hs : stepOf i ≤ midFusion φ)
    (h : ∀ v, IV φ i v → b v = IA φ i v) : Holds φ b i := by
  have hc := IA_spec hex
  cases i with
  | inl x => exact (pid_agree hs h).trans hc
  | inr r => exact (sel_local hs (fun h0 hm => h _ ⟨h0, hm, rfl⟩)).trans hc

theorem compat_of_common {i j : Item} (h : ∃ c, Holds φ c i ∧ Holds φ c j) :
    ∀ v, IV φ i v → IV φ j v → IA φ i v = IA φ j v := by
  obtain ⟨c, hi, hj⟩ := h
  intro v h1 h2
  rw [← agree_of_holds hi v h1, agree_of_holds hj v h2]

/-- Una camarilla de un estado de la máquina antes de las cláusulas da una asignación en la que valen sus nodos y sus
ids. -/
theorem holds_clique (hbd : Bounded φ) {X : GPathB} (hs : Struct.Struct φ X) (hml : MapLinks φ X)
    (hpos : 0 < X.current_step) (hT : X.current_step - 1 ≤ midFusion φ) {S : Int → PathNodeId} (hc : Carried X S)
    {q : PathNodeId} (hq : OnS X.current_step S q) :
    Holds φ (aOf S) (.inl q) ∧ Holds φ (aOf S) (.inr q.id) := by
  have hv := validSel_of_carried hbd hs hml hc hpos
  obtain ⟨k, hk0, hk, rfl⟩ := hq
  have he := pid_of_validSel hv hT k hk0 (by omega)
  have hst : (S k).id.step = k := hc.step k hk0 hk
  refine ⟨?_, ?_⟩
  · show pidOfAssign φ (aOf S) (S k).id.step = S k
    rw [hst]; exact he.symm
  · show selOfAssign φ (aOf S) (S k).id.step = (S k).id
    rw [hst, he]; rfl

/-- Los hechos de un lado (una llegada) de una unión antes de las cláusulas, fijado con `R`. -/
structure SideOK (φ : Cnf) (T : Int) (X : GPathB) (R : List NodeId) (d : NodeId) : Prop where
  st    : Struct.Struct φ X
  ml    : MapLinks φ X
  ec    : EdgeClique X
  inv   : SInvB X
  cs    : X.current_step = T + 1
  pre   : T ≤ midFusion φ
  one   : 1 ≤ T
  dstep : d.step = T
  valid : (pinF X R).isValid = true
  pin   : ∀ r ∈ R, ∀ q ∈ (pinF X R).alive, q.id.step = r.step → q.id = r
  top   : ∀ q ∈ (pinF X R).alive, q.id.step = T → q.id = d

theorem SideOK.pinId {T : Int} {X : GPathB} {R : List NodeId} {d : NodeId} (h : SideOK φ T X R d) {r : NodeId}
    (hr : r ∈ d :: R) {q : PathNodeId} (hq : q ∈ (pinF X R).alive) (hs : q.id.step = r.step) :
    q.id = r := by
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.top q hq (by rw [hs, h.dstep])
  · exact h.pin r hr q hq hs

theorem SideOK.clique {T : Int} {X : GPathB} {R : List NodeId} {d : NodeId} (h : SideOK φ T X R d) (hbd : Bounded φ)
    {u w : PathNodeId} (ha : (pinF X R).Adj u w) :
    ∃ c, (Holds φ c (.inl u) ∧ Holds φ c (.inr u.id)) ∧ (Holds φ c (.inl w) ∧ Holds φ c (.inr w.id)) := by
  obtain ⟨S, hc, hu, hw⟩ := h.ec u w ((sub_pinF X R).adj _ _ ha)
  have hp : 0 < X.current_step := by rw [h.cs]; have := h.one; omega
  have hT : X.current_step - 1 ≤ midFusion φ := by rw [h.cs]; have := h.pre; omega
  exact ⟨_, holds_clique hbd h.st h.ml hp hT hc hu, holds_clique hbd h.st h.ml hp hT hc hw⟩

theorem SideOK.closed {T : Int} {X : GPathB} {R : List NodeId} {d : NodeId} (h : SideOK φ T X R d) :
    ClosedState (pinF X R) :=
  closedState_pinF h.inv h.valid (by rw [h.cs]; have := h.one; omega)

/-- **Un nodo y un pin**: el nodo tiene un vecino en el paso del pin, y ese vecino lleva el id del pin. -/
theorem SideOK.node_pin {T : Int} {X : GPathB} {R : List NodeId} {d : NodeId} (h : SideOK φ T X R d)
    (hbd : Bounded φ) {u : PathNodeId} (hu : u ∈ (pinF X R).alive) {r : NodeId} (hr : r ∈ d :: R) (h0 : 0 ≤ r.step)
    (hrT : r.step ≤ T) : ∃ c, Holds φ c (.inl u) ∧ Holds φ c (.inr r) := by
  have hcl := h.closed
  have hcs : (pinF X R).current_step = T + 1 := by rw [step_pinF, h.cs]
  obtain ⟨q, hqs, hR, _⟩ := hcl.pair ⟨hu, hu, adj_refl _ _ hu⟩ r.step h0 (by omega)
  obtain ⟨_, hqa, hadj⟩ := hR
  obtain ⟨c, ⟨hcu, _⟩, ⟨_, hcq⟩⟩ := h.clique hbd hadj
  rw [h.pinId hr hqa hqs] at hcq
  exact ⟨c, hcu, hcq⟩

/-- **Dos pins**: un vivo del paso del primero tiene un vecino en el paso del segundo. -/
theorem SideOK.pin_pin {T : Int} {X : GPathB} {R : List NodeId} {d : NodeId} (h : SideOK φ T X R d)
    (hbd : Bounded φ) {r r' : NodeId} (hr : r ∈ d :: R) (h0 : 0 ≤ r.step) (hrT : r.step ≤ T) (hr' : r' ∈ d :: R)
    (h0' : 0 ≤ r'.step) (hrT' : r'.step ≤ T) : ∃ c, Holds φ c (.inr r) ∧ Holds φ c (.inr r') := by
  have hcs : (pinF X R).current_step = T + 1 := by rw [step_pinF, h.cs]
  obtain ⟨q, hq, hqs⟩ := exists_alive_at h.valid h0 (by omega)
  obtain ⟨c, hcq, hcr'⟩ := h.node_pin hbd hq hr' h0' hrT'
  refine ⟨c, ?_, hcr'⟩
  have : Holds φ c (.inr q.id) := by
    show selOfAssign φ c q.id.step = q.id
    have hq' : pidOfAssign φ c q.id.step = q := hcq
    exact congrArg PathNodeId.id hq'
  rw [h.pinId hr hq hqs] at this
  exact this

-- ============================================================
-- Un triángulo de la unión fijada es triángulo de un lado
-- ============================================================

/-- Tres nodos vecinos dos a dos. -/
def Tri (g : GPathB) (x y z : PathNodeId) : Prop := g.Adj x y ∧ g.Adj x z ∧ g.Adj y z

/-- **El núcleo del parcheo**: si toda asignación que respeta el destino y los pins la lleva algún lado fijado, un
triángulo de la unión de los lados fijados es triángulo de un lado. -/
theorem triSplit_core (hbd : Bounded φ) {T : Int} {A B : GPathB} {R : List NodeId} {d : NodeId}
    (hA : SideOK φ T A R d) (hB : SideOK φ T B R d) {x y z : PathNodeId}
    (hU : Tri (join (pinF A R) (pinF B R)) x y z)
    (hcomp : ∀ b : Assign, selOfAssign φ b d.step = d →
      (∀ r ∈ R, 0 ≤ r.step → r.step ≤ T → selOfAssign φ b r.step = r) →
      Carried (pinF A R) (pidOfAssign φ b) ∨ Carried (pinF B R) (pidOfAssign φ b)) :
    Tri (pinF A R) x y z ∨ Tri (pinF B R) x y z := by
  obtain ⟨hxy, hxz, hyz⟩ := hU
  let A' := pinF A R
  let B' := pinF B R
  -- las parejas de nodos, vecinas en un lado
  have hsym : ∀ u w, (join A' B').Adj u w → (join A' B').Adj w u := fun u w h => (adj_symm _ _ _).mp h
  have hside : ∀ u w, (join A' B').Adj u w → A'.Adj u w ∨ B'.Adj u w := fun u w h => adj_join_cases h
  have heA := (sInvB_pinF hA.inv R).edges
  have heB := (sInvB_pinF hB.inv R).edges
  have halive : ∀ u w, (join A' B').Adj u w → u ∈ A'.alive ∨ u ∈ B'.alive := by
    intro u w h
    rcases hside u w h with h | h
    · exact Or.inl (heA _ _ h).1
    · exact Or.inr (heB _ _ h).1
  have hrefl : ∀ u w, (join A' B').Adj u w → (join A' B').Adj u u := by
    intro u w h
    rcases halive u w h with h | h
    · exact (adj_iff _ _ _).mpr (Or.inl ⟨rfl, (alive_join A' B' u).mpr (Or.inl h)⟩)
    · exact (adj_iff _ _ _).mpr (Or.inl ⟨rfl, (alive_join A' B' u).mpr (Or.inr h)⟩)
  let nodes : List PathNodeId := [x, y, z]
  have hadjN : ∀ u ∈ nodes, ∀ w ∈ nodes, (join A' B').Adj u w := by
    have hx := hrefl x y hxy
    have hy := hrefl y z hyz
    have hz := hrefl z y (hsym _ _ hyz)
    intro u hu w hw
    simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hu hw
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    all_goals first | assumption | exact hsym _ _ (by assumption)
  -- las piezas
  let pins : List NodeId := (d :: R).filter (fun r => decide (0 ≤ r.step ∧ r.step ≤ T))
  let l : List Item := nodes.map .inl ++ pins.map .inr
  have hpins : ∀ r ∈ pins, r ∈ d :: R ∧ 0 ≤ r.step ∧ r.step ≤ T := by
    intro r hr
    have := List.mem_filter.mp hr
    exact ⟨this.1, by simpa using this.2⟩
  have hdpin : d ∈ pins := List.mem_filter.mpr ⟨List.mem_cons_self, by
    have := hA.one; have := hA.dstep; simp; omega⟩
  have hnodeSide : ∀ u ∈ nodes, u ∈ A'.alive ∨ u ∈ B'.alive := fun u hu => halive u u (hadjN u hu u hu)
  have hcommon : ∀ i ∈ l, ∀ j ∈ l, ∃ c, Holds φ c i ∧ Holds φ c j := by
    have hnp : ∀ u ∈ nodes, ∀ r ∈ pins, ∃ c, Holds φ c (.inl u) ∧ Holds φ c (.inr r) := by
      intro u hu r hr
      obtain ⟨hr1, hr2, hr3⟩ := hpins r hr
      rcases hnodeSide u hu with h | h
      · exact hA.node_pin hbd h hr1 hr2 hr3
      · exact hB.node_pin hbd h hr1 hr2 hr3
    intro i hi j hj
    rcases List.mem_append.mp hi with hi | hi <;> rcases List.mem_append.mp hj with hj | hj
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hj
      rcases hside u w (hadjN u hu w hw) with h | h
      · obtain ⟨c, ⟨h1, _⟩, ⟨h2, _⟩⟩ := hA.clique hbd h; exact ⟨c, h1, h2⟩
      · obtain ⟨c, ⟨h1, _⟩, ⟨h2, _⟩⟩ := hB.clique hbd h; exact ⟨c, h1, h2⟩
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hj
      exact hnp u hu r hr
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hi
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hj
      obtain ⟨c, h1, h2⟩ := hnp u hu r hr
      exact ⟨c, h2, h1⟩
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hi
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hj
      obtain ⟨a1, a2, a3⟩ := hpins r hr
      obtain ⟨b1, b2, b3⟩ := hpins r' hr'
      exact hA.pin_pin hbd a1 a2 a3 b1 b2 b3
  -- el parcheo
  obtain ⟨b, hb⟩ := patch l (IA φ) (IV φ) (fun i hi j hj => compat_of_common (hcommon i hi j hj))
  have hstepN : ∀ u ∈ nodes, 0 ≤ u.id.step ∧ u.id.step < T + 1 := by
    intro u hu
    rcases hnodeSide u hu with h | h
    · have hi := sInvB_pinF hA.inv R
      have := step_range_of_alive hi.docs hi.below hi.zero h
      rw [step_pinF, hA.cs] at this; exact this
    · have hi := sInvB_pinF hB.inv R
      have := step_range_of_alive hi.docs hi.below hi.zero h
      rw [step_pinF, hB.cs] at this; exact this
  have hholds : ∀ i ∈ l, Holds φ b i := by
    intro i hi
    obtain ⟨c, hc, _⟩ := hcommon i hi i hi
    refine holds_of_agree ⟨c, hc⟩ ?_ (hb i hi)
    rcases List.mem_append.mp hi with h | h
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
      have := hstepN u hu; have := hA.pre; show u.id.step ≤ _; omega
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      have := (hpins r hr).2.2; have := hA.pre; show r.step ≤ _; omega
  have hN : ∀ u ∈ nodes, pidOfAssign φ b u.id.step = u :=
    fun u hu => hholds (.inl u) (List.mem_append_left _ (List.mem_map.mpr ⟨u, hu, rfl⟩))
  have hP : ∀ r ∈ pins, selOfAssign φ b r.step = r :=
    fun r hr => hholds (.inr r) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
  have hcar := hcomp b (hP d hdpin) (fun r hr h0 h1 =>
    hP r (List.mem_filter.mpr ⟨List.mem_cons_of_mem _ hr, by simp; omega⟩))
  -- el triángulo en el lado que lleva la rama
  have htri : ∀ X : GPathB, X.current_step = T + 1 → Carried X (pidOfAssign φ b) → Tri X x y z := by
    intro X hX hc
    have hadj : ∀ u ∈ nodes, ∀ w ∈ nodes, X.Adj u w := by
      intro u hu w hw
      have h1 := hstepN u hu
      have h2 := hstepN w hw
      have := hc.adj u.id.step w.id.step h1.1 (by omega) h2.1 (by omega)
      rwa [hN u hu, hN w hw] at this
    exact ⟨hadj x (by simp [nodes]) y (by simp [nodes]), hadj x (by simp [nodes]) z (by simp [nodes]),
      hadj y (by simp [nodes]) z (by simp [nodes])⟩
  rcases hcar with h | h
  · exact Or.inl (htri _ (by rw [step_pinF, hA.cs]) h)
  · exact Or.inr (htri _ (by rw [step_pinF, hB.cs]) h)

/-- En una línea del mapa bin, dos entradas de claves distintas son todas las que hay. -/
theorem two_senders {k : Int} {line : Line} (hnd : (line.map (·.1)).Nodup) (hk : ∀ kv ∈ line, kv.1 ∈ mapNodes φ k)
    {a b c : NodeId × GPathB} (ha : a ∈ line) (hb : b ∈ line) (hab : a.1 ≠ b.1) (hc : c ∈ line) : c = a ∨ c = b := by
  rcases line_cases hnd hk with rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩
  · exact absurd ha List.not_mem_nil
  · rw [List.mem_singleton] at ha hb; exact absurd (by rw [ha, hb]) hab
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> simp_all

/-- **Una llegada de la línea antes de las cláusulas cumple `SideOK`.** -/
theorem sideOK_arr (hbd : Bounded φ) (n : Nat) (hn : (n : Int) + 1 ≤ midFusion φ)
    {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ)) (hi : SInvB kv.2) {d : NodeId} (hs : Sends φ kv d)
    {R : List NodeId} (hv : (pinF (arrOf φ kv d) R).isValid = true) : SideOK φ ((n : Int) + 1) (arrOf φ kv d) R d := by
  obtain ⟨hl, hent, _, hls, hml⟩ := line_facts hbd n
  have hok := hl kv hkv
  have hd : d.step = (n : Int) + 1 := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key]; omega
  have hpre := pre_line hbd n (by omega) kv hkv
  have hcs : kv.2.current_step = (n : Int) + 1 := hok.step
  have hdY : d.step = (kv.2.filterAll (reqOf φ d)).current_step := by
    rw [(shrinks_filterAll kv.2 (reqOf φ d)).1.step, hcs, hd]
  have hiX : SInvB (arrOf φ kv d) := sInvB_up (sInvB_filterAll hi _) hdY (by omega)
  refine ⟨Struct.struct_upFiltering hbd hok (hls kv hkv).1 (hls kv hkv).2 hs.1,
    mapLinks_upFiltering (by omega) hok (hml kv hkv) (hent kv hkv).2 hs.1,
    (edgeClique_arr hok (by omega) (hent kv hkv).2 hpre.1 hpre.2 hs (by omega)).1, hiX,
    (stateOk_arr hok hs).step, by omega, by omega, hd, hv, pinned_pinF hiX.docs hv, ?_⟩
  intro q hq hqs
  exact arrival_top_id hi (by rw [hd, hcs]) ((sub_pinF _ R).alive q hq) (by rw [hqs, hcs])

/-- **Antes de las cláusulas, un triángulo de la unión de dos llegadas fijadas es triángulo de una de ellas.** -/
theorem triSplit (hbd : Bounded φ) (n : Nat) (hn : (n : Int) + 1 ≤ midFusion φ)
    {a b : NodeId × GPathB} (ha : a ∈ steps φ n (init φ)) (hb : b ∈ steps φ n (init φ)) (hab : a.1 ≠ b.1)
    (hia : SInvB a.2) (hib : SInvB b.2) {d : NodeId} (hsa : Sends φ a d) (hsb : Sends φ b d) {R : List NodeId}
    (hvA : (pinF (arrOf φ a d) R).isValid = true) (hvB : (pinF (arrOf φ b d) R).isValid = true)
    {x y z : PathNodeId} (hU : Tri (join (pinF (arrOf φ a d) R) (pinF (arrOf φ b d) R)) x y z) :
    Tri (pinF (arrOf φ a d) R) x y z ∨ Tri (pinF (arrOf φ b d) R) x y z := by
  obtain ⟨hl, _, hnd, hls, _⟩ := line_facts hbd n
  have sA := sideOK_arr hbd n hn ha hia hsa hvA
  have sB := sideOK_arr hbd n hn hb hib hsb hvB
  refine triSplit_core hbd sA sB hU ?_
  intro bb hbd' hR
  have hv : ValidSel φ ((n : Int) + 1) (pidOfAssign φ bb) := validSel_pid hbd bb hn
  obtain ⟨_, g0, hf, hc0⟩ := steps_has_sel n (hv.mono (by omega))
  have hmem := List.mem_of_find?_eq_some hf
  have hok0 := hl _ hmem
  have hcar := carried_arrival (by omega) hv hok0 hc0
  have hdid : (pidOfAssign φ bb ((n : Int) + 1)).id = d := by
    show selOfAssign φ bb ((n : Int) + 1) = d
    rw [← sA.dstep]; exact hbd'
  rw [hdid] at hcar
  have hson : d ∈ sonsOfMap φ ((pidOfAssign φ bb (n : Int)).id) := by
    have := hv.son ((n : Int) + 1) (by omega) (Int.le_refl _)
    rw [show (n : Int) + 1 - 1 = n by omega, hdid] at this; exact this
  let kv0 : NodeId × GPathB := ((pidOfAssign φ bb (n : Int)).id, g0)
  have hsends : Sends φ kv0 d := ⟨hson, isValid_of_carried hcar⟩
  have hcarP : Carried (pinF (arrOf φ kv0 d) R) (pidOfAssign φ bb) := by
    refine carried_pinF hcar (fun r hr h0 h1 => ?_)
    have hcs0 : (arrOf φ kv0 d).current_step = (n : Int) + 1 + 1 := (stateOk_arr hok0 hsends).step
    have h1' : r.step < (arrOf φ kv0 d).current_step := h1
    exact hR r hr h0 (by rw [hcs0] at h1'; omega)
  have hk : ∀ kv ∈ steps φ n (init φ), kv.1 ∈ mapNodes φ n := by
    intro kv hkv
    have := (hls kv hkv).2
    rwa [(hl kv hkv).key, show (n : Int) + 1 - 1 = n by omega] at this
  rcases two_senders hnd hk ha hb hab hmem with h | h
  · exact Or.inl (by rw [← h]; exact hcarP)
  · exact Or.inr (by rw [← h]; exact hcarP)

-- ============================================================
-- La familia no prohíbe ningún triángulo antes de las cláusulas
-- ============================================================

/-- **`NoTriF`**: la familia no prohíbe ningún triángulo del estado fijado. -/
def NoTriF (g : GPathB) (F : FamT) : Prop :=
  ∀ R, (pinF g R).isValid = true → ∀ x y z, Tri (pinF g R) x y z → ¬ F R x y z

variable {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **La llegada conserva `NoTriF`**: un trío prohibido está por debajo de la cima, donde las aristas son las del
remitente fijado. -/
theorem noTri_arr {D : GPathB} {F : FamT} {reqs : List NodeId} (hD : Good D F) (hN : NoTriF D F)
    (hd : d.step = D.current_step) : NoTriF ((D.filterAll reqs).up d title forb) (fun R => F (reqs ++ R)) := by
  intro R hvA x y z hT hf
  obtain ⟨hvX, halive, hadj⟩ := arrival_pin_commute (title := title) (forb := forb) hD.inv
    (by have := hD.pos; omega) hd hvA
  obtain ⟨sx, sy, sz⟩ := hD.below _ x y z hf
  have hcsX : (pinF D (reqs ++ R)).current_step = D.current_step := step_pinF _ _
  have hiA := sInvB_pinF (sInvB_up (sInvB_filterAll hD.inv reqs) (d := d) (title := title) (forb := forb)
    (by rw [(shrinks_filterAll D reqs).1.step]; exact hd) (by have := hD.pos; omega)) R
  have hsub := sub_upR (pinF D (reqs ++ R)) d title forb
  have hdX : d.step = (pinF D (reqs ++ R)).current_step := by rw [hcsX]; exact hd
  have hold : ∀ u v, u.id.step < D.current_step → v.id.step < D.current_step →
      (pinF ((D.filterAll reqs).up d title forb) R).Adj u v → (pinF D (reqs ++ R)).Adj u v := by
    intro u v hu hv ha
    have ha' := (hadj u v (hiA.edges _ _ ha).1 (hiA.edges _ _ ha).2).mp ha
    exact adj_addNode_old hdX (by rw [hcsX]; exact hu) (by rw [hcsX]; exact hv) (hsub.adj _ _ ha')
  obtain ⟨a, b, c⟩ := hT
  exact hN (reqs ++ R) hvX x y z ⟨hold _ _ sx sy a, hold _ _ sx sz b, hold _ _ sy sz c⟩ hf

theorem tri_same {U V : GPathB} (hs : SameGraph U V) (hea : EdgesAlive U) {x y z : PathNodeId} (h : Tri U x y z) :
    Tri V x y z := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨(hs.2 _ _ (hea _ _ a).1 (hea _ _ a).2).mp a, (hs.2 _ _ (hea _ _ b).1 (hea _ _ b).2).mp b,
    (hs.2 _ _ (hea _ _ c).1 (hea _ _ c).2).mp c⟩

/-- **La unión conserva `NoTriF`** si sus triángulos fijados caen en un lado. -/
theorem noTri_join {A B : GPathB} {FA FB : FamT} (hNA : NoTriF A FA) (hNB : NoTriF B FB) (hiU : SInvB (join A B))
    (hsplit : PinJoinSplitAll A B)
    (htri : ∀ R, (pinF A R).isValid = true → (pinF B R).isValid = true → ∀ x y z,
      Tri (join (pinF A R) (pinF B R)) x y z → Tri (pinF A R) x y z ∨ Tri (pinF B R) x y z) :
    NoTriF (join A B) (joinFam A B FA FB) := by
  intro R hv x y z hT hf
  obtain ⟨hsame, hone⟩ := hsplit R hv
  have hT' := tri_same hsame (sInvB_pinF hiU R).edges hT
  unfold pinJoin at hT'
  unfold joinFam at hf
  by_cases hvA : (pinF A R).isValid = true <;> by_cases hvB : (pinF B R).isValid = true
  · simp only [hvA, hvB, if_true] at hT' hf
    obtain ⟨_, _, _, _, _, _, sA, sB⟩ := hf
    rcases htri R hvA hvB x y z hT' with h | h
    · rcases sA with hn | hF
      · exact hn h
      · exact hNA R hvA x y z h hF
    · rcases sB with hn | hF
      · exact hn h
      · exact hNB R hvB x y z h hF
  · simp only [hvA, hvB, if_true] at hT' hf
    exact hNA R hvA x y z hT' hf
  · simp only [hvA, hvB, if_true] at hT' hf
    exact hNB R hvB x y z hT' hf
  · exact absurd hone (by simp [hvA, hvB])

/-- **`NoTriF` pasa a la línea siguiente** antes de las cláusulas. -/
theorem noTri_next (hbd : Bounded φ) (n : Nat) (hn : (n : Int) + 1 ≤ midFusion φ) {Fs : NodeId → FamT}
    (h : LInv φ ((n : Int) + 1) (steps φ n (init φ)) Fs) (hN : ∀ kv ∈ steps φ n (init φ), NoTriF kv.2 (Fs kv.1))
    (hsplit : HSplit φ (steps φ n (init φ))) :
    ∀ E ∈ advance φ (steps φ n (init φ)), NoTriF E.2 (famsNext φ (steps φ n (init φ)) Fs E.1) := by
  have hlen := line_cases h.nodup h.keys
  intro E hE
  have harr : ∀ kv ∈ steps φ n (init φ), ∀ d, Sends φ kv d → NoTriF (arrOf φ kv d) (shiftF φ Fs kv d) := by
    intro kv hkv d hs
    have hd : d.step = kv.2.current_step := by
      rw [sonsOfMap_step φ kv.1 d hs.1, (h.ok kv hkv).key, (h.ok kv hkv).step]; omega
    exact noTri_arr (h.good kv hkv) (hN kv hkv) hd
  rcases entry_shape Fs hlen h.nodup hE with ⟨kv, hkv, hs, he, hf⟩ | ⟨a, ha, b, hb, hab, hsa, hsb, he, hf⟩
  · rw [he, hf]; exact harr kv hkv _ hs
  · have oka := h.ok a ha
    have okb := h.ok b hb
    rw [he, doJoin_arr oka okb hsa hsb, hf]
    have hda : E.1.step = a.2.current_step := by
      rw [sonsOfMap_step φ a.1 _ hsa.1, oka.key, oka.step]; omega
    have hdb : E.1.step = b.2.current_step := by
      rw [sonsOfMap_step φ b.1 _ hsb.1, okb.key, okb.step]; omega
    have hiA : SInvB (arrOf φ a E.1) := sInvB_up (sInvB_filterAll (h.good a ha).inv _)
      (by rw [(shrinks_filterAll a.2 _).1.step]; exact hda) (by rw [hda, oka.step]; omega)
    have hiB : SInvB (arrOf φ b E.1) := sInvB_up (sInvB_filterAll (h.good b hb).inv _)
      (by rw [(shrinks_filterAll b.2 _).1.step]; exact hdb) (by rw [hdb, okb.step]; omega)
    have hcs : (arrOf φ a E.1).current_step = (arrOf φ b E.1).current_step :=
      (stateOk_arr oka hsa).step.trans (stateOk_arr okb hsb).step.symm
    exact noTri_join (harr a ha _ hsa) (harr b hb _ hsb) (sInvB_join hiA hiB hcs) (hsplit a ha b hb hab _ hsa hsb)
      (fun R hvA hvB x y z hT => triSplit hbd n hn ha hb hab (h.good a ha).inv (h.good b hb).inv hsa hsb hvA hvB hT)

/-- **Con `NoTriF` en la línea siguiente, `HNew` se cumple sin más**: un trío de una cadena es un triángulo. -/
theorem hnew_of_noTri {L : Line} {Fs : NodeId → FamT}
    (hN : ∀ E ∈ advance φ L, NoTriF E.2 (famsNext φ L Fs E.1)) : HNew φ L Fs := by
  intro E hE _ kv _ d₁ _ _ R hvE C j p q r hoc hf _ _ _ _
  exfalso
  obtain ⟨hC, h1, h2, h3, h4, h5, h6⟩ := hoc
  exact hN E hE R hvE _ _ _ ⟨hC.adj p q h1 h2 h3 h4, hC.adj p r h1 h2 h5 h6, hC.adj q r h3 h4 h5 h6⟩ hf

/-- **Con un solo remitente, `NoTriF` pasa sin más**: cada entrada es una sola llegada. -/
theorem noTri_next_single {L : Line} {T : Int} {Fs : NodeId → FamT} (h : LInv φ T L Fs)
    (hN : ∀ kv ∈ L, NoTriF kv.2 (Fs kv.1)) (hone : ∀ a ∈ L, ∀ b ∈ L, a.1 = b.1) :
    ∀ E ∈ advance φ L, NoTriF E.2 (famsNext φ L Fs E.1) := by
  intro E hE
  rcases entry_shape Fs (line_cases h.nodup h.keys) h.nodup hE with ⟨kv, hkv, hs, he, hf⟩ | ⟨a, ha, b, hb, hab, _⟩
  · rw [he, hf]
    have hd : E.1.step = kv.2.current_step := by
      rw [sonsOfMap_step φ kv.1 _ hs.1, (h.ok kv hkv).key, (h.ok kv hkv).step]; omega
    exact noTri_arr (h.good kv hkv) (hN kv hkv) hd
  · exact absurd (hone a ha b hb) hab

theorem mapNodes_top_eq {k : Int} (hk : fusionTop φ ≤ k) {u v : NodeId} (hu : u ∈ mapNodes φ k)
    (hv : v ∈ mapNodes φ k) : u = v := by
  unfold mapNodes at hu hv
  have hm : ¬ k = midFusion φ := by unfold midFusion; unfold fusionTop at hk; omega
  have h0 : ¬ k = 0 := by unfold fusionTop at hk; omega
  have hn : ¬ k < 0 := by unfold fusionTop at hk; omega
  rw [if_neg hn, if_neg h0, if_neg hm] at hu hv
  by_cases hs : stepCount φ ≤ k
  · rw [if_pos hs] at hu; exact absurd hu List.not_mem_nil
  · rw [if_neg hs, if_pos hk, List.mem_singleton] at hu hv
    rw [hu, hv]

/-- **Desde la fusión final `HNew` no pide nada**: hay un solo nodo por paso, así que no hay otra entrada. -/
theorem hnew_top {L : Line} {T : Int} (hT : 1 ≤ T) {Fs : NodeId → FamT} (h : LInv φ T L Fs) (hk : fusionTop φ ≤ T) :
    HNew φ L Fs := by
  intro E hE _ kv hkv d₁ hne hs
  exfalso
  have hmem₁ := (arr_facts hT h hkv hs).2.2.2.2.2.2
  rcases entry_shape Fs (line_cases h.nodup h.keys) h.nodup hE with ⟨kv', hkv', hs', _⟩ | ⟨a, ha, _, _, _, hsa, _⟩
  · exact hne (mapNodes_top_eq hk hmem₁ (arr_facts hT h hkv' hs').2.2.2.2.2.2)
  · exact hne (mapNodes_top_eq hk hmem₁ (arr_facts hT h ha hsa).2.2.2.2.2.2)

-- ============================================================
-- La máquina entera, con `NoNewClose` solo en las líneas de cláusula
-- ============================================================

/-- **Las hipótesis**: `PinJoinSplitAll` en los joins de la máquina y `NoNewClose` solo en las líneas de cláusula con
dos remitentes (la línea siguiente entre el segundo literal de la primera cláusula y la fusión final). -/
def HypsLiveLineC (φ : Cnf) : Prop :=
  ∀ n : Nat, HSplit φ (steps φ n (init φ)) ∧
    (midFusion φ + 1 < (n : Int) + 1 → (n : Int) + 1 < fusionTop φ → HNew φ (steps φ n (init φ)) (famsAt φ n))

/-- La inducción, con `HNew` dada a partir del invariante de la línea. -/
theorem lInv_stepsG (hbd : Bounded φ) (hsp : ∀ n : Nat, HSplit φ (steps φ n (init φ)))
    (hnw : ∀ n : Nat, midFusion φ + 1 < (n : Int) + 1 → (n : Int) + 1 < fusionTop φ →
      LInv φ ((n : Int) + 1) (steps φ n (init φ)) (famsAt φ n) → HNew φ (steps φ n (init φ)) (famsAt φ n)) :
    ∀ n : Nat, LInv φ ((n : Int) + 1) (steps φ n (init φ)) (famsAt φ n) ∧
      ((n : Int) ≤ midFusion φ + 1 → ∀ kv ∈ steps φ n (init φ), NoTriF kv.2 (famsAt φ n kv.1)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨lInv_init φ, fun _ kv _ R _ x y z _ hf => hf⟩
  | succ n ih =>
    obtain ⟨ih, ihN⟩ := ih
    have hN' : (n : Int) + 1 ≤ midFusion φ + 1 →
        ∀ E ∈ advance φ (steps φ n (init φ)), NoTriF E.2 (famsNext φ (steps φ n (init φ)) (famsAt φ n) E.1) := by
      intro hn
      by_cases hpre : (n : Int) + 1 ≤ midFusion φ
      · exact noTri_next hbd n hpre ih (ihN (by omega)) (hsp n)
      · -- la línea de la fusión central: un solo remitente
        have hk : (n : Int) = midFusion φ := by omega
        refine noTri_next_single ih (ihN (by omega)) (fun a ha b hb => ?_)
        have e1 := ih.keys a ha
        have e2 := ih.keys b hb
        rw [show (n : Int) + 1 - 1 = midFusion φ by omega, mapNodes_fusion φ _ (Or.inr (Or.inl rfl)),
          List.mem_singleton] at e1 e2
        rw [e1, e2]
    have hnew : HNew φ (steps φ n (init φ)) (famsAt φ n) := by
      by_cases hpost : midFusion φ + 1 < (n : Int) + 1
      · by_cases htop : (n : Int) + 1 < fusionTop φ
        · exact hnw n hpost htop ih
        · exact hnew_top (by omega) ih (by omega)
      · exact hnew_of_noTri (hN' (by omega))
    have hL := lInv_advance (by omega) ih (hsp n) hnew
    rw [steps_succ]
    refine ⟨?_, fun hn kv hkv => hN' (by push_cast at hn; omega) kv hkv⟩
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact hL

theorem lInv_stepsC (hbd : Bounded φ) (H : HypsLiveLineC φ) :
    ∀ n : Nat, LInv φ ((n : Int) + 1) (steps φ n (init φ)) (famsAt φ n) :=
  fun n => (lInv_stepsG hbd (fun n => (H n).1) (fun n h1 h2 _ => (H n).2 h1 h2) n).1

-- ============================================================
-- `NoNewClose` desde el triángulo mezclado del join del remitente
-- ============================================================

/-- **`HMixed`** (en la línea `m + 1`, cuyos remitentes vienen de la línea `m`): un trío de una cadena de una entrada
de la línea siguiente que su familia prohíbe, y que es triángulo en un remitente de otra entrada (fijado y válido), es
un **triángulo mezclado del join de ese remitente**: el remitente es la unión de las llegadas de dos remitentes de la
línea `m`, y el trío no es triángulo en ninguna de las dos llegadas fijadas que quedan válidas. -/
def HMixed (φ : Cnf) (m : Nat) : Prop :=
  ∀ E ∈ advance φ (steps φ (m + 1) (init φ)), ¬ IsNeg φ E.1 →
    ∀ kv ∈ steps φ (m + 1) (init φ), ∀ d₁, d₁ ≠ E.1 → Sends φ kv d₁ →
    ∀ R, (pinF E.2 R).isValid = true →
    ∀ C j p q r, OnChain3 (pinF E.2 R) C j p q r →
      famsNext φ (steps φ (m + 1) (init φ)) (famsAt φ (m + 1)) E.1 R (C p) (C q) (C r) →
      (pinF kv.2 R).isValid = true → Tri (pinF kv.2 R) (C p) (C q) (C r) →
      ∃ a ∈ steps φ m (init φ), ∃ b ∈ steps φ m (init φ), a.1 ≠ b.1 ∧ Sends φ a kv.1 ∧ Sends φ b kv.1 ∧
        ((pinF (arrOf φ a kv.1) R).isValid = true → ¬ Tri (pinF (arrOf φ a kv.1) R) (C p) (C q) (C r)) ∧
        ((pinF (arrOf φ b kv.1) R).isValid = true → ¬ Tri (pinF (arrOf φ b kv.1) R) (C p) (C q) (C r))

theorem nodeg_famsNext {L : Line} {T : Int} {Fs : NodeId → FamT} (h : LInv φ T L Fs) {E : NodeId × GPathB}
    (hE : E ∈ advance φ L) (R : List NodeId) : NoDeg (famsNext φ L Fs E.1 R) := by
  rcases entry_shape Fs (line_cases h.nodup h.keys) h.nodup hE with ⟨kv, hkv, _, _, hf⟩ | ⟨a, ha, b, hb, _, _, _, _, hf⟩
  · rw [hf]; exact (h.good kv hkv).nodeg _
  · rw [hf]; unfold joinFam; split
    · split
      · exact fun x y z ⟨a, b, c, _⟩ => ⟨a, b, c⟩
      · exact (h.good a ha).nodeg _
    · exact (h.good b hb).nodeg _

/-- **`HNew` desde `HMixed`**: un triángulo mezclado del join del remitente lo prohíbe su familia por definición. -/
theorem hnew_of_mixed (hbd : Bounded φ) (m : Nat) (hm : HMixed φ m)
    (h₁ : LInv φ ((m : Int) + 2) (steps φ (m + 1) (init φ)) (famsAt φ (m + 1)))
    (hsplit : HSplit φ (steps φ m (init φ))) :
    HNew φ (steps φ (m + 1) (init φ)) (famsAt φ (m + 1)) := by
  intro E hE hneg kv hkv d₁ hd₁ hs R hvE C j p q r hoc hf hvD t1 t2 t3
  obtain ⟨a, ha, b, hb, hab, hsa, hsb, na, nb⟩ := hm E hE hneg kv hkv d₁ hd₁ hs R hvE C j p q r hoc hf hvD ⟨t1, t2, t3⟩
  obtain ⟨hl, _, hnd, hls, _⟩ := line_facts hbd m
  have hk : ∀ kv ∈ steps φ m (init φ), kv.1 ∈ mapNodes φ m := by
    intro kv hkv
    have := (hls kv hkv).2
    rwa [(hl kv hkv).key, show (m : Int) + 1 - 1 = m by omega] at this
  have hlen := line_cases hnd hk
  have hkv' : kv ∈ advance φ (steps φ m (init φ)) := by rw [← steps_succ]; exact hkv
  have hFs : famsAt φ (m + 1) = famsNext φ (steps φ m (init φ)) (famsAt φ m) := rfl
  -- los nodos del trío están por debajo del paso del remitente
  have hiD := sInvB_pinF (h₁.good kv hkv).inv R
  have hstep : ∀ u, (pinF kv.2 R).Adj u u → u.id.step < kv.2.current_step := by
    intro u hu
    have := (step_range_of_alive hiD.docs hiD.below hiD.zero (hiD.edges _ _ hu).1).2
    rwa [step_pinF] at this
  have ha1 : (pinF kv.2 R).Adj (C p) (C p) := adj_refl _ _ (hiD.edges _ _ t1).1
  have ha2 : (pinF kv.2 R).Adj (C q) (C q) := adj_refl _ _ (hiD.edges _ _ t1).2
  have ha3 : (pinF kv.2 R).Adj (C r) (C r) := adj_refl _ _ (hiD.edges _ _ t2).2
  have hdist := nodeg_famsNext h₁ hE R _ _ _ hf
  -- la forma del remitente
  rw [hFs]
  rcases entry_shape (famsAt φ m) hlen hnd hkv' with ⟨kv', hkv'', hs', he, hfm⟩ | ⟨a', ha', b', hb', hab', hsa', hsb', he, hfm⟩
  · -- una sola llegada: es la de `a` o la de `b`, donde el trío no es triángulo
    exfalso
    rw [he] at hvD t1 t2 t3
    rcases two_senders hnd hk ha hb hab hkv'' with rfl | rfl
    · exact na hvD ⟨t1, t2, t3⟩
    · exact nb hvD ⟨t1, t2, t3⟩
  · have oka := hl a' ha'
    have okb := hl b' hb'
    rw [he, doJoin_arr oka okb hsa' hsb'] at hvD t1 t2 t3
    rw [hfm]
    have hcsA : (arrOf φ a' kv.1).current_step = kv.2.current_step := by
      rw [he, doJoin_arr oka okb hsa' hsb']; rfl
    -- en cada lado fijado válido el trío no es triángulo
    have side : ∀ c ∈ steps φ m (init φ), c = a' ∨ c = b' → (pinF (arrOf φ c kv.1) R).isValid = true →
        ¬ Tri (pinF (arrOf φ c kv.1) R) (C p) (C q) (C r) := by
      intro c hc _ hv
      rcases two_senders hnd hk ha hb hab hc with rfl | rfl
      · exact na hv
      · exact nb hv
    have nA := side a' ha' (Or.inl rfl)
    have nB := side b' hb' (Or.inr rfl)
    obtain ⟨hsame, hone⟩ := hsplit a' ha' b' hb' hab' kv.1 hsa' hsb' R hvD
    unfold pinJoin at hsame
    have hiD' : SInvB (pinF (join (arrOf φ a' kv.1) (arrOf φ b' kv.1)) R) := by
      rw [← doJoin_arr oka okb hsa' hsb', ← he]; exact hiD
    have hlt : ∀ u, (pinF kv.2 R).Adj u u → u.id.step < (pinF (arrOf φ a' kv.1) R).current_step := by
      intro u hu; rw [step_pinF, hcsA]; exact hstep u hu
    unfold joinFam
    by_cases hvA : (pinF (arrOf φ a' kv.1) R).isValid = true <;>
      by_cases hvB : (pinF (arrOf φ b' kv.1) R).isValid = true
    · simp only [hvA, hvB, if_true]
      exact ⟨hdist.1, hdist.2.1, hdist.2.2, hlt _ ha1, hlt _ ha2, hlt _ ha3, Or.inl (nA hvA), Or.inl (nB hvB)⟩
    · simp only [hvA, hvB, if_true] at hsame ⊢
      exact absurd (tri_same hsame hiD'.edges ⟨t1, t2, t3⟩) (nA hvA)
    · simp only [hvA, hvB, if_true] at hsame ⊢
      exact absurd (tri_same hsame hiD'.edges ⟨t1, t2, t3⟩) (nB hvB)
    · exact absurd hone (by simp [hvA, hvB])

/-- **Las hipótesis, sin familias en las conclusiones**: `PinJoinSplitAll` en los joins de la máquina y `HMixed` en las
líneas de cláusula con dos remitentes. -/
def HypsLiveLineM (φ : Cnf) : Prop :=
  (∀ n : Nat, HSplit φ (steps φ n (init φ))) ∧
  (∀ m : Nat, midFusion φ + 1 < (m : Int) + 2 → (m : Int) + 2 < fusionTop φ → HMixed φ m)

theorem lInv_stepsM (hbd : Bounded φ) (H : HypsLiveLineM φ) :
    ∀ n : Nat, LInv φ ((n : Int) + 1) (steps φ n (init φ)) (famsAt φ n) := by
  intro n
  refine (lInv_stepsG hbd H.1 (fun n h1 h2 hL => ?_) n).1
  cases n with
  | zero => exfalso; unfold midFusion at h1; omega
  | succ m =>
    refine hnew_of_mixed hbd m (H.2 m (by push_cast at h1; omega) (by push_cast at h2; omega)) ?_ (H.1 m)
    rw [show (m : Int) + 2 = ((m + 1 : Nat) : Int) + 1 by push_cast; omega]
    exact hL

end PreClause

namespace SecLine

open GPathB Driver PreClause

/-- **La espina con tríos decide la satisfacibilidad** bajo `PinJoinSplitAll` en los joins de la máquina y
`NoNewClose` solo en las líneas de cláusula con dos remitentes: antes, los tríos prohibidos no tocan ningún triángulo
(`NoTriF`), y desde la fusión final no hay otra entrada. -/
theorem spineVerdict_iff_of_liveLineC {φ : Cnf} (hbd : Bounded φ) (H : HypsLiveLineC φ) :
    SpineVerdict φ ↔ Satisfiable φ := by
  apply spineVerdict_iff_of_liveExt hbd
  intro kv hkv hval
  exact ⟨_, ((lInv_stepsC hbd H (stepCount φ - 1).toNat).good kv hkv).live [] hval⟩

/-- **La espina con tríos decide la satisfacibilidad** bajo `PinJoinSplitAll` en los joins de la máquina y `HMixed`
en las líneas de cláusula con dos remitentes: un trío de cadena prohibido en una entrada que es triángulo en un
remitente es un triángulo mezclado del join de ese remitente. -/
theorem spineVerdict_iff_of_mixed {φ : Cnf} (hbd : Bounded φ) (H : HypsLiveLineM φ) :
    SpineVerdict φ ↔ Satisfiable φ := by
  apply spineVerdict_iff_of_liveExt hbd
  intro kv hkv hval
  exact ⟨_, ((lInv_stepsM hbd H (stepCount φ - 1).toNat).good kv hkv).live [] hval⟩

end SecLine

end AbsSatBingo.Model
