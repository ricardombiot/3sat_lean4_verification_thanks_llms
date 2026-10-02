-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnMaj.lean
import AbsSatBingo.Model.ForbidOnExact

/-!
# La regeneración por mayoría: la ventana prohibida es la única dificultad

Cada paso del mapa bin lee **una sola variable** (`stepVar`): el valor de una variable, su negación, o la copia de un
literal. Por eso la mayoría de tres asignaciones (`maj3`) pasa por cualquier nodo por el que pasen dos de ellas
(`pid_maj_ab`, …): las copias y los requisitos son igualdades y la mayoría las conserva. Lo único que la mayoría puede
romper es la **ventana prohibida** de una cláusula.

## El invariante semántico

* `ValidUpTo φ a T`: la rama de `a` no pisa ninguna ventana prohibida por debajo del paso `T` (las soluciones del
  prefijo de la fórmula leído hasta `T`). `comp_line`: la máquina `:on` lleva la rama de toda asignación así (la
  completitud de `run_carriesOn`, que solo usaba `Sat` para la ventana del paso que se añade).
* `Snd φ P g`: toda pareja de vecinos de `g` está en la rama de una asignación de `P`. Con la completitud, el grafo
  de la entrada es exactamente el de sus soluciones.
* `MajClosed φ T`: las soluciones del prefijo son cerradas por mayoría.

Bajo `MajClosed`, `Snd` pasa las tres operaciones:

| operación | lema | idea |
|---|---|---|
| join | `snd_joinOn` | una arista de la unión es de un lado |
| filtro | `snd_filter` | la pareja tiene un testigo común en el paso del requisito; la mayoría de las tres ramas pasa por los dos nodos y cumple el requisito |
| UP | `snd_upOn` | un nodo de la fila baja a un padre (`lift_row`, con el ajuste `adjust`); dos nodos viejos tienen una cima testigo si la fila saltó una ventana |

y con `Snd` y la completitud los tres niveles de `ForbidOnExact` salen **a la vez** (`levels_of_snd`): no hay
escalera, la mayoría de las tres ramas de un triángulo pasa por sus tres nodos.

## Lo que se demuestra, sin hipótesis

* **`levels_before_first_window`**: hasta la línea del segundo literal de la primera cláusula, toda entrada cumple
  `TopCT`, `TopEdge` y `TopTri`. Dos filtros lejanos (dos copias) no han consumido ningún nivel: sin ventanas
  prohibidas las ramas son todas las asignaciones, y son cerradas por mayoría (`majClosed_pre`).
* **`spineVerdictOn_iff_of_majClosed`**: la espina `:on` decide toda fórmula cuyas soluciones de prefijo son cerradas
  por mayoría.
* **`spineVerdictOn_iff_of_twoLike`**: en particular, las fórmulas con forma 2-CNF (`TwoLike`: segundo y tercer
  literal iguales en cada cláusula), por `majClosed_twoLike` (con `prohibited_clause` / `prohibited_of_false`: una
  ventana prohibida de la rama es una cláusula con sus tres literales falsos).

La mayoría se usa en dos sitios, el filtro y el UP que salta una ventana, y en los dos solo para esto: **tres ramas
que comparten nodos dos a dos dan una rama por los tres nodos**. Para 3-CNF general esa propiedad falla (la mayoría
de `100`, `010`, `001` es la ventana prohibida `000`); lo que habría que poner en su lugar es el contenido de
`PinTetra`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

-- ============================================================
-- La mayoría de tres asignaciones
-- ============================================================

/-- La mayoría, variable a variable. -/
def maj3 (a b c : Assign) : Assign := fun v => (a v && b v) || (a v && c v) || (b v && c v)

theorem maj3_ab {a b c : Assign} {v : Nat} (h : a v = b v) : maj3 a b c v = a v := by
  unfold maj3; rw [← h]; cases a v <;> cases c v <;> rfl

theorem maj3_ac {a b c : Assign} {v : Nat} (h : a v = c v) : maj3 a b c v = a v := by
  unfold maj3; rw [← h]; cases a v <;> cases b v <;> rfl

theorem maj3_bc {a b c : Assign} {v : Nat} (h : b v = c v) : maj3 a b c v = b v := by
  unfold maj3; rw [← h]; cases a v <;> cases b v <;> rfl

-- ============================================================
-- Cada paso lee una sola variable
-- ============================================================

/-- La variable que lee el paso `k`, si lee alguna. -/
def stepVar (φ : Cnf) (k : Int) : Option Nat :=
  if k ≤ 0 then none
  else if k < midFusion φ then some (varOfStep k)
  else if k = midFusion φ then none
  else if fusionTop φ ≤ k then none
  else
    match clauseOf φ k with
    | none => none
    | some (c, p) => some (litAt c p).v

theorem bit_inj {x y : Bool} (h : bit x = bit y) : x = y := by
  cases x <;> cases y <;> simp_all [bit]

theorem litVal_congr {a b : Assign} {l : Lit} (h : a l.v = b l.v) : litVal a l = litVal b l := by
  unfold litVal; rw [h]

theorem litVal_inj {a b : Assign} {l : Lit} (h : litVal a l = litVal b l) : a l.v = b l.v := by
  unfold litVal at h
  split at h
  · exact h
  · cases ha : a l.v <;> cases hb : b l.v <;> simp_all

/-- Dos asignaciones que coinciden en la variable del paso eligen el mismo nodo del mapa. -/
theorem sel_eq_of_var {φ : Cnf} {a b : Assign} {k : Int} (h : ∀ v, stepVar φ k = some v → a v = b v) :
    selOfAssign φ a k = selOfAssign φ b k := by
  unfold stepVar at h
  unfold selOfAssign
  split
  · rfl
  · rename_i h0
    rw [if_neg h0] at h
    split
    · rename_i h1
      rw [if_pos h1] at h
      rw [h _ rfl]
    · rename_i h1
      rw [if_neg h1] at h
      split
      · rfl
      · rename_i h2
        rw [if_neg h2] at h
        split
        · rfl
        · rename_i h3
          rw [if_neg h3] at h
          split
          · rfl
          · rename_i c p hc
            rw [hc] at h
            rw [litVal_congr (h _ rfl)]

/-- Y al revés: si eligen el mismo nodo, coinciden en la variable del paso. -/
theorem var_eq_of_sel {φ : Cnf} {a b : Assign} {k : Int} (h : selOfAssign φ a k = selOfAssign φ b k) :
    ∀ v, stepVar φ k = some v → a v = b v := by
  intro v hv
  unfold stepVar at hv
  unfold selOfAssign at h
  by_cases h0 : k ≤ 0
  · rw [if_pos h0] at hv; cases hv
  · rw [if_neg h0] at hv
    simp only [if_neg h0] at h
    by_cases h1 : k < midFusion φ
    · rw [if_pos h1] at hv
      simp only [if_pos h1] at h
      cases hv
      by_cases hodd : k % 2 = 1
      · simp only [if_pos hodd] at h
        exact bit_inj (congrArg NodeId.index h)
      · simp only [if_neg hodd] at h
        have := bit_inj (congrArg NodeId.index h)
        cases ha : a (varOfStep k) <;> cases hb : b (varOfStep k) <;> simp_all
    · rw [if_neg h1] at hv
      simp only [if_neg h1] at h
      by_cases h2 : k = midFusion φ
      · rw [if_pos h2] at hv; cases hv
      · rw [if_neg h2] at hv
        simp only [if_neg h2] at h
        by_cases h3 : fusionTop φ ≤ k
        · rw [if_pos h3] at hv; cases hv
        · rw [if_neg h3] at hv
          simp only [if_neg h3] at h
          cases hc : clauseOf φ k with
          | none => rw [hc] at hv; cases hv
          | some cp =>
            obtain ⟨c, p⟩ := cp
            rw [hc] at hv
            simp only [hc] at h
            cases hv
            exact litVal_inj (bit_inj (congrArg NodeId.index h))

theorem sel_maj_ab {φ : Cnf} {a b c : Assign} {k : Int} (h : selOfAssign φ a k = selOfAssign φ b k) :
    selOfAssign φ (maj3 a b c) k = selOfAssign φ a k :=
  sel_eq_of_var (fun v hv => maj3_ab (var_eq_of_sel h v hv))

theorem sel_maj_ac {φ : Cnf} {a b c : Assign} {k : Int} (h : selOfAssign φ a k = selOfAssign φ c k) :
    selOfAssign φ (maj3 a b c) k = selOfAssign φ a k :=
  sel_eq_of_var (fun v hv => maj3_ac (var_eq_of_sel h v hv))

theorem sel_maj_bc {φ : Cnf} {a b c : Assign} {k : Int} (h : selOfAssign φ b k = selOfAssign φ c k) :
    selOfAssign φ (maj3 a b c) k = selOfAssign φ b k :=
  sel_eq_of_var (fun v hv => maj3_bc (var_eq_of_sel h v hv))

/-- La ventana de la rama en el paso `k` depende de los nodos elegidos en `k`, `k - 1` y `k - 2`. -/
theorem pid_eq_of_sels {φ : Cnf} {a b : Assign} {k : Int} (h0 : selOfAssign φ a k = selOfAssign φ b k)
    (h1 : 0 < k → selOfAssign φ a (k - 1) = selOfAssign φ b (k - 1))
    (h2 : 1 < k → selOfAssign φ a (k - 2) = selOfAssign φ b (k - 2)) :
    pidOfAssign φ a k = pidOfAssign φ b k := by
  unfold pidOfAssign
  rw [h0]
  congr 1
  · by_cases h : 0 < k
    · rw [if_pos h, if_pos h, h1 h]
    · rw [if_neg h, if_neg h]
  · by_cases h : 1 < k
    · rw [if_pos h, if_pos h, h2 h]
    · rw [if_neg h, if_neg h]

theorem sels_of_pid_eq {φ : Cnf} {a b : Assign} {k : Int} (h : pidOfAssign φ a k = pidOfAssign φ b k) :
    selOfAssign φ a k = selOfAssign φ b k ∧ (0 < k → selOfAssign φ a (k - 1) = selOfAssign φ b (k - 1)) ∧
      (1 < k → selOfAssign φ a (k - 2) = selOfAssign φ b (k - 2)) := by
  have e0 := congrArg PathNodeId.id h
  have e1 := congrArg PathNodeId.parent_id h
  have e2 := congrArg PathNodeId.gparent_id h
  simp only [pidOfAssign] at e0 e1 e2
  refine ⟨e0, fun hk => ?_, fun hk => ?_⟩
  · rw [if_pos hk, if_pos hk] at e1; exact Option.some.inj e1
  · rw [if_pos hk, if_pos hk] at e2; exact Option.some.inj e2

/-- **La mayoría pasa por todo nodo por el que pasan dos de las tres.** -/
theorem pid_maj_ab {φ : Cnf} {a b c : Assign} {k : Int} (h : pidOfAssign φ a k = pidOfAssign φ b k) :
    pidOfAssign φ (maj3 a b c) k = pidOfAssign φ a k := by
  obtain ⟨h0, h1, h2⟩ := sels_of_pid_eq h
  exact pid_eq_of_sels (sel_maj_ab h0) (fun hk => sel_maj_ab (h1 hk)) (fun hk => sel_maj_ab (h2 hk))

theorem pid_maj_ac {φ : Cnf} {a b c : Assign} {k : Int} (h : pidOfAssign φ a k = pidOfAssign φ c k) :
    pidOfAssign φ (maj3 a b c) k = pidOfAssign φ a k := by
  obtain ⟨h0, h1, h2⟩ := sels_of_pid_eq h
  exact pid_eq_of_sels (sel_maj_ac h0) (fun hk => sel_maj_ac (h1 hk)) (fun hk => sel_maj_ac (h2 hk))

theorem pid_maj_bc {φ : Cnf} {a b c : Assign} {k : Int} (h : pidOfAssign φ b k = pidOfAssign φ c k) :
    pidOfAssign φ (maj3 a b c) k = pidOfAssign φ b k := by
  obtain ⟨h0, h1, h2⟩ := sels_of_pid_eq h
  exact pid_eq_of_sels (sel_maj_bc h0) (fun hk => sel_maj_bc (h1 hk)) (fun hk => sel_maj_bc (h2 hk))

-- ============================================================
-- Las soluciones del prefijo y la completitud de la máquina para ellas
-- ============================================================

/-- **`ValidUpTo φ a T`**: la rama de `a` no pisa ninguna ventana prohibida por debajo del paso `T`. -/
def ValidUpTo (φ : Cnf) (a : Assign) (T : Int) : Prop :=
  ∀ k, k < T → isProhibited φ (pidOfAssign φ a k) = false

theorem validUpTo_mono {φ : Cnf} {a : Assign} {T T' : Int} (h : ValidUpTo φ a T) (hT : T' ≤ T) : ValidUpTo φ a T' :=
  fun k hk => h k (by omega)

theorem validUpTo_succ {φ : Cnf} {a : Assign} {T : Int} (h : ValidUpTo φ a T)
    (hT : isProhibited φ (pidOfAssign φ a T) = false) : ValidUpTo φ a (T + 1) := by
  intro k hk
  by_cases e : k = T
  · rw [e]; exact hT
  · exact h k (by omega)

theorem validUpTo_of_sat {φ : Cnf} {a : Assign} (h : Sat a φ) (T : Int) : ValidUpTo φ a T :=
  fun k _ => pidOfAssign_not_prohibited φ a h k

-- ============================================================
-- Ajustar una asignación al nodo del mapa que sigue
-- ============================================================

theorem nodeId_ext {x y : NodeId} (h1 : x.step = y.step) (h2 : x.index = y.index) : x = y := by
  cases x; cases y; simp_all

/-- El rango del requisito de un nodo del mapa de una fórmula acotada: un paso anterior, entre la raíz y el nodo. -/
theorem reqOf_range {φ : Cnf} (hb : Bounded φ) {d : NodeId} : ∀ r ∈ reqOf φ d, 1 ≤ r.step ∧ r.step < d.step := by
  intro r hr
  rcases step_cases φ d.step with h | ⟨v, hv, h⟩ | ⟨v, hv, h⟩ | h | ⟨j, p, c, hp, hjlt, hj, h⟩ | h
  · rw [reqOf_nonpos φ d h] at hr; exact absurd hr List.not_mem_nil
  · rw [reqOf_var φ d v hv h] at hr; exact absurd hr List.not_mem_nil
  · rw [reqOf_neg φ d v hv h] at hr
    rw [List.mem_singleton] at hr; subst hr
    simp only [h, varStep, negStep]; omega
  · rw [reqOf_mid φ d h] at hr; exact absurd hr List.not_mem_nil
  · rw [reqOf_clause φ d j p c hp hjlt hj h] at hr
    rw [List.mem_singleton] at hr; subst hr
    obtain ⟨h1, h2, h3⟩ := hb c (List.mem_of_getElem? hj)
    have hv : (litAt c p).v < φ.nVars := by unfold litAt; split <;> assumption
    obtain ⟨b0, b1⟩ := lit_step_bounds φ _ hv
    simp only [h, clauseStep, midFusion] at b1 ⊢
    omega
  · rw [reqOf_above φ d h] at hr; exact absurd hr List.not_mem_nil

/-- **Ajuste.** Una asignación cuyo nodo en `T - 1` tiene a `d` por hijo y que cumple el requisito de `d` se puede
cambiar, sin tocar lo que elige por debajo de `T`, para que elija `d` en `T`. Solo hace falta cambiar algo cuando `T`
es el paso de una variable nueva (los dos valores son hijos); en los demás pasos el nodo ya es `d`. -/
theorem adjust {φ : Cnf} (hb : Bounded φ) (a : Assign) {T : Int} (hT : 1 ≤ T) {d : NodeId}
    (hd : d ∈ sonsOfMap φ (selOfAssign φ a (T - 1))) (hdm : d ∈ mapNodes φ T)
    (hagr : ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) :
    ∃ a', (∀ j, j < T → selOfAssign φ a' j = selOfAssign φ a j) ∧ selOfAssign φ a' T = d := by
  have hds : d.step = T := mapNodes_step φ T d hdm
  have hTc : T < stepCount φ := by
    by_cases h : stepCount φ ≤ T
    · unfold mapNodes at hdm
      rw [if_neg (by omega), if_pos h] at hdm
      exact absurd hdm List.not_mem_nil
    · omega
  have single : mapNodes φ T = [⟨T, 0⟩] → selOfAssign φ a T = d := by
    intro e
    have h1 := selOfAssign_onMap φ a T (by omega) hTc
    rw [e, List.mem_singleton] at h1 hdm
    rw [h1, hdm]
  rcases step_cases φ T with h | ⟨v, hv, h⟩ | ⟨v, hv, h⟩ | h | ⟨j, p, c, hp, hjlt, hj, h⟩ | h
  · omega
  · -- una variable nueva: se elige su valor
    refine ⟨fun u => if u = v then decide (d.index = 1) else a u, fun j hj => ?_, ?_⟩
    · apply sel_eq_of_var
      intro u hu
      have hne : u ≠ v := by
        unfold stepVar at hu
        split at hu
        · cases hu
        · split at hu
          · cases hu
            simp only [h, varStep, varOfStep] at hj ⊢
            omega
          · rename_i hlt
            exfalso
            simp only [h, varStep, midFusion] at hj hlt
            omega
      simp [hne]
    · rw [h, selOfAssign_var φ _ v hv]
      apply nodeId_ext
      · rw [hds, h]
      · rcases mapNodes_index φ T d hdm with e | e <;> simp [e, bit]
  · -- la negación: el único hijo es el que la asignación ya elige
    refine ⟨a, fun _ _ => rfl, ?_⟩
    have e1 : T - 1 = varStep v := by rw [h]; simp only [varStep, negStep]; omega
    rw [e1, selOfAssign_var φ a v hv] at hd
    unfold sonsOfMap at hd
    rw [if_pos (by refine ⟨?_, ?_, ?_⟩ <;> simp only [varStep, midFusion] <;> omega)] at hd
    rw [List.mem_singleton] at hd
    rw [h, selOfAssign_neg φ a v hv, hd]
    apply nodeId_ext
    · simp only [varStep, negStep]; omega
    · simp only [bit_not]
  · exact ⟨a, fun _ _ => rfl, single (by rw [h]; exact mapNodes_fusion φ _ (Or.inr (Or.inl rfl)))⟩
  · -- la copia de un literal: el requisito fija el valor
    refine ⟨a, fun _ _ => rfl, ?_⟩
    have hreq := reqOf_clause φ d j p c hp hjlt hj (hds.trans h)
    have hr := hagr _ (by rw [hreq]; exact List.mem_singleton_self _)
    obtain ⟨h1, h2, h3⟩ := hb c (List.mem_of_getElem? hj)
    have hv : (litAt c p).v < φ.nVars := by unfold litAt; split <;> assumption
    have hl := selOfAssign_lit φ a (litAt c p) hv
    have hidx : bit (litVal a (litAt c p)) = d.index := by
      have := congrArg NodeId.index (hl.symm.trans hr)
      exact this
    rw [h, selOfAssign_clause φ a j p c hp hjlt hj]
    exact nodeId_ext (by rw [hds, h]) hidx
  · exact ⟨a, fun _ _ => rfl, single (mapNodes_fusion φ _ (Or.inr (Or.inr ⟨h, hTc⟩)))⟩

namespace MachineOn

open GPathB Driver Machine

variable {φ : Cnf}

/-- **El paso `:on`** para una rama cuya ventana nueva no está prohibida (lo único para lo que `advance_hasOn` usa
`Sat`). -/
theorem advance_hasOn' (hb : Bounded φ) (a : Assign) (t : Int) (ht0 : 0 ≤ t)
    (hnp : isProhibited φ (pidOfAssign φ a (t + 1)) = false)
    (ht : t + 1 < stepCount φ) (line : Line) (hl : LineOn (t + 1) line)
    (hh : HasOn (pidOfAssign φ a) (selOfAssign φ a t) line) :
    HasOn (pidOfAssign φ a) (selOfAssign φ a (t + 1)) (advanceM .on φ line) := by
  obtain ⟨g0, hf, hct⟩ := hh
  have hmem := List.mem_of_find?_eq_some hf
  have hok : EntOn (t + 1) (selOfAssign φ a t) g0 := hl _ hmem
  let S := pidOfAssign φ a
  let d := selOfAssign φ a (t + 1)
  have hd : d ∈ sonsOfMap φ (selOfAssign φ a t) := selOfAssign_son φ a t ht0 ht
  let g1 := g0.filterAllOn (reqOf φ d)
  have hstep1 : g1.current_step = t + 1 := (step_filterAllOn g0 _).trans hok.1.step
  have hct1 : CT g1 S := by
    refine ct_filterAllOn hct _ ?_
    intro r hr _ _
    exact reqSat_selOfAssign φ hb a (t + 1) r hr
  have htb1 : TB g1 := tb_filterAllOn hok.2.2 _
  have hnpar : S t ∈ g1.newParents := by
    obtain ⟨n, hn, _, _⟩ := hct1.1.node t ht0 (by omega)
    have hid := node?_id hn
    unfold newParents
    rw [if_pos (by omega)]
    refine List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨node?_mem hn, ?_⟩, hid⟩
    rw [hid, hstep1]; simp [S, pid_step]
  have hshift : shiftPid (S t) d = S (t + 1) := by
    have := shift_pid φ a (t + 1) (by omega)
    simpa using this
  have hct2 : CT (g1.upOn d "" (isProhibited φ)) S := by
    apply ct_upOn hct1 htb1
    · rw [hstep1]
      refine List.mem_filter.mpr ⟨?_, by simp [S, hnp]⟩
      unfold shiftRowIds
      rw [if_pos (by omega)]
      exact (mem_dedupPids _ _).mpr (List.mem_map.mpr ⟨S t, hnpar, hshift⟩)
    · intro _
      rw [hstep1, show t + 1 - 1 = t by omega]
      exact List.mem_filter.mpr ⟨hnpar, by simp [hshift]⟩
    · rw [hstep1]; exact pid_step φ a _
    · rw [hstep1]; exact fun n hn => by
        have := below_filterAllOn hok.1.below (reqOf φ d) n hn
        rw [step_filterAllOn, hok.1.step] at this; exact this
    · exact pid_root φ a
  have hup : g0.upFilteringOn (reqOf φ d) d "" (isProhibited φ) = g1.upOn d "" (isProhibited φ) := rfl
  have hvalid : (g0.upFilteringOn (reqOf φ d) d "" (isProhibited φ)).isValid = true := by
    rw [hup]; exact isValid_of_carried hct2.1
  have hok2 : EntOn (t + 1 + 1) d (g0.upFilteringOn (reqOf φ d) d "" (isProhibited φ)) :=
    entOn_upFilteringOn hok hd hvalid
  unfold advanceM
  refine foldl_establish _ (fun next => HasOn S d next) (LineOn (t + 1 + 1)) line
    (fun _ kv hkv hx => lineOn_sendAll (hl kv hkv) hx)
    (fun _ kv hkv _ hx => by
      unfold sendAllM
      exact foldl_pres _ (fun next => HasOn S d next) _ (fun y d' hd' hy => hasOn_sendTo (hl kv hkv) hd' hy) _ hx)
    (selOfAssign φ a t, g0) ?_ hmem [] (fun _ h => absurd h List.not_mem_nil)
  intro x hx
  unfold sendAllM
  refine foldl_establish _ (fun next => HasOn S d next) (LineOn (t + 1 + 1)) _
    (fun y d' hd' hy => lineOn_sendTo hok d' hd' hy)
    (fun y d' hd' _ hy => hasOn_sendTo hok hd' hy) d ?_ hd x hx
  intro y hy
  unfold sendToM
  dsimp only
  have hv' : (upFilteringM .on g0 (reqOf φ d) d "" (isProhibited φ)).isValid = true := hvalid
  rw [if_pos hv']
  exact hasOn_insert_self hy hok2 (show CT (g0.upFilteringOn (reqOf φ d) d "" (isProhibited φ)) S by rw [hup]; exact hct2)

/-- **La máquina `:on` lleva la rama de toda asignación válida hasta la línea.** -/
theorem comp_line (hb : Bounded φ) (a : Assign) : ∀ n : Nat, (n : Int) < stepCount φ → ValidUpTo φ a ((n : Int) + 1) →
    LineOn ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) ∧
      HasOn (pidOfAssign φ a) (selOfAssign φ a n) (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero =>
    intro _ _
    obtain ⟨hl, hh⟩ := initOn_inv φ a
    have e : stepsM .on φ 0 (initM .on φ) = initM .on φ := rfl
    rw [e]
    exact ⟨by simpa using hl, by simpa using hh⟩
  | succ n ih =>
    intro hn hv
    obtain ⟨hl, hh⟩ := ih (by push_cast at hn; omega) (validUpTo_mono hv (by push_cast; omega))
    rw [stepsM_succ]
    have h1 := lineOn_advance (φ := φ) hl
    have h2 := advance_hasOn' hb a n (by omega) (hv _ (by push_cast; omega)) (by push_cast at hn; omega) _ hl hh
    refine ⟨?_, ?_⟩
    · rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]; exact h1
    · rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 by push_cast; rfl]; exact h2

end MachineOn

-- ============================================================
-- El invariante semántico de parejas
-- ============================================================

/-- Las soluciones del prefijo que una entrada de la línea `T` con clave `k` debe representar. -/
def SolE (φ : Cnf) (T : Int) (k : NodeId) (a : Assign) : Prop :=
  ValidUpTo φ a T ∧ selOfAssign φ a (T - 1) = k

/-- **`MajClosed φ T`**: las soluciones del prefijo leído hasta `T` son cerradas por mayoría. -/
def MajClosed (φ : Cnf) (T : Int) : Prop :=
  ∀ a b c, ValidUpTo φ a T → ValidUpTo φ b T → ValidUpTo φ c T → ValidUpTo φ (maj3 a b c) T

theorem pid_id (φ : Cnf) (a : Assign) (k : Int) : (pidOfAssign φ a k).id = selOfAssign φ a k := rfl

namespace GPathB

open Driver Machine MachineOn

variable {φ : Cnf}

/-- **`Snd φ P g`**: toda pareja de vecinos de `g` (y todo vivo, con `x = w`) está en la rama de una asignación de
`P`. Con la completitud (toda asignación de `P` es una camarilla de `g`), el grafo es exactamente el de `P`. -/
def Snd (φ : Cnf) (P : Assign → Prop) (g : GPathB) : Prop :=
  ∀ x w, g.Adj x w → ∃ a, P a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a w.id.step = w

theorem snd_mono {P Q : Assign → Prop} {g : GPathB} (h : Snd φ P g) (hpq : ∀ a, P a → Q a) : Snd φ Q g := by
  intro x w hxw
  obtain ⟨a, ha, h1, h2⟩ := h x w hxw
  exact ⟨a, hpq a ha, h1, h2⟩

/-- El join: una arista de la unión es de un lado. -/
theorem snd_joinOn {P : Assign → Prop} {A B : GPathB} (hA : Snd φ P A) (hB : Snd φ P B) : Snd φ P (joinOn A B) := by
  intro x w hxw
  obtain ⟨T', hT⟩ := joinOn_eq A B
  have hxw' : (join A B).Adj x w := by rw [hT] at hxw; exact hxw
  rcases adj_join_cases hxw' with h | h
  · exact hA x w h
  · exact hB x w h

/-- **El filtro de un requisito, bajo mayoría.** Una pareja que sobrevive tiene un testigo común en el paso del
requisito (el estado revisado está cerrado por parejas); las tres parejas (la original y las dos con el testigo) son
de tres soluciones, y su mayoría pasa por los dos nodos y cumple el requisito. -/
theorem snd_filter {E : GPathB} {T : Int} {k : NodeId} {reqs : List NodeId} (hE : SInvB E)
    (hcs : E.current_step = T) (hvE : E.isValid = true) (hlen : reqs.length ≤ 1)
    (hrange : ∀ r ∈ reqs, 1 ≤ r.step ∧ r.step < T) (hmaj : MajClosed φ T)
    (hs : Snd φ (SolE φ T k) E) (hc : ∀ a, SolE φ T k a → CT E (pidOfAssign φ a))
    (hvY : (E.filterAllOn reqs).isValid = true) :
    Snd φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r) (E.filterAllOn reqs) := by
  intro x w hxw
  have hsh := (shrinks_filterAllOn E reqs).1
  obtain ⟨a0, hS0, hx0, hw0⟩ := hs x w (hsh.adj _ _ hxw)
  match reqs, hlen, hrange, hvY, hxw, hsh with
  | [], _, _, _, _, _ => exact ⟨a0, ⟨hS0, fun r hr => absurd hr List.not_mem_nil⟩, hx0, hw0⟩
  | [r], _, hrange, hvY, hxw, hsh =>
    obtain ⟨hr1, hr2⟩ := hrange r (List.mem_singleton_self _)
    cases hd : ([r].foldl filterRequire E).dirty
    · -- el filtro no mata a nadie: toda rama de la entrada cumple el requisito
      have hd' : (E.filterRequire r).dirty = false := hd
      have hD := hc a0 hS0
      have hal := hD.1.alive r.step (by omega) (by rw [hcs]; exact hr2)
      obtain ⟨n, hn, hnid⟩ := hE.docs _ hal
      have hline : n ∈ E.line r.step := by
        unfold line
        refine List.mem_filter.mpr ⟨hn, ?_⟩
        rw [hnid, hD.1.step r.step (by omega) (by rw [hcs]; exact hr2)]
        simp
      have := filterRequire_noVictims hvE hd' n hline
      rw [hnid] at this
      refine ⟨a0, ⟨hS0, fun r' hr' => ?_⟩, hx0, hw0⟩
      rw [List.mem_singleton] at hr'; subst hr'
      exact this
    · have e : E.filterAllOn [r] = E.pinOn [r] := by
        unfold filterAllOn pinOn
        congr 1
        generalize [r].foldl filterRequire E = F at hd
        cases F
        simp_all
      rw [e] at hvY hxw
      have hiY : SInvB (E.pinOn [r]) := sInvB_pinOn hE [r]
      have hcl : ClosedState (E.pinOn [r]) := closedState_pinOn hE hvY (by rw [hcs]; omega)
      obtain ⟨hxa, hwa⟩ := hiY.edges x w hxw
      obtain ⟨s, hss, hxs, hws⟩ := hcl.pair (y := x) (w := w) ⟨hxa, hwa, hxw⟩ r.step (by omega)
        (by rw [step_pinOn, hcs]; exact hr2)
      have hsid : s.id = r := pinned_pinOn hE.docs hvY r (List.mem_singleton_self _) s hxs.2.1 hss
      have hsub := sub_pinOn E [r]
      obtain ⟨a1, hS1, hx1, hs1⟩ := hs x s (hsub.adj _ _ hxs.2.2)
      obtain ⟨a2, hS2, hw2, hs2⟩ := hs w s (hsub.adj _ _ hws.2.2)
      refine ⟨maj3 a0 a1 a2, ⟨⟨hmaj _ _ _ hS0.1 hS1.1 hS2.1, ?_⟩, fun r' hr' => ?_⟩, ?_, ?_⟩
      · rw [sel_maj_ab (hS0.2.trans hS1.2.symm)]; exact hS0.2
      · rw [List.mem_singleton] at hr'; subst hr'
        have hm : pidOfAssign φ (maj3 a0 a1 a2) s.id.step = s := (pid_maj_bc (hs1.trans hs2.symm)).trans hs1
        have := congrArg PathNodeId.id hm
        rw [pid_id, hss] at this
        rw [this, hsid]
      · exact (pid_maj_ab (hx0.trans hx1.symm)).trans hx0
      · exact (pid_maj_ac (hw0.trans hw2.symm)).trans hw0

/-- La completitud pasa el filtro: una rama que cumple los requisitos sigue llevada. -/
theorem comp_filter {E : GPathB} {P : Assign → Prop} {reqs : List NodeId}
    (hc : ∀ a, P a → CT E (pidOfAssign φ a)) :
    ∀ a, (P a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r) → CT (E.filterAllOn reqs) (pidOfAssign φ a) :=
  fun a ha => ct_filterAllOn (hc a ha.1) reqs (fun r hr _ _ => ha.2 r hr)

section Up

variable {Y : GPathB} {T : Int} {k d : NodeId} {title : String}

/-- **Subir una rama del remitente a la llegada.** Una asignación del remitente filtrado cuya cima `q` es padre del
nodo `n` de la fila se ajusta para elegir `d` en el paso nuevo: su rama pasa por `n`, que no está prohibido, y no
cambia por debajo. -/
theorem lift_row (hb : Bounded φ) (hT : 1 ≤ T) (hdk : d ∈ sonsOfMap φ k)
    (hdm : d ∈ mapNodes φ T) {a : Assign}
    (ha : SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) {q n : PathNodeId}
    (hq : pidOfAssign φ a (T - 1) = q) (hqn : q ∈ Y.rowParents d n) (hn : n ∈ Y.newRowIds d (isProhibited φ)) :
    ∃ a', SolE φ (T + 1) d a' ∧ pidOfAssign φ a' T = n ∧ ∀ j, j < T → pidOfAssign φ a' j = pidOfAssign φ a j := by
  obtain ⟨a', hlow, htop⟩ := adjust hb a hT (by rw [ha.1.2]; exact hdk) hdm ha.2
  have hpl : ∀ j, j < T → pidOfAssign φ a' j = pidOfAssign φ a j := fun j hj =>
    pid_eq_of_sels (hlow j hj) (fun _ => hlow _ (by omega)) (fun _ => hlow _ (by omega))
  have hpT : pidOfAssign φ a' T = n := by
    have h1 := shift_pid φ a' T (by omega)
    rw [hpl (T - 1) (by omega), hq, htop] at h1
    have h2 := (List.mem_filter.mp hqn).2
    rw [← h1]; exact beq_iff_eq.mp h2
  refine ⟨a', ⟨validUpTo_succ (fun j hj => by rw [hpl j hj]; exact ha.1.1 j hj) ?_, ?_⟩, hpT, hpl⟩
  · rw [hpT]
    have := (List.mem_filter.mp hn).2
    simpa using this
  · rw [show T + 1 - 1 = T by omega]; exact htop

/-- **El UP, bajo mayoría.** Una pareja con un nodo de la fila baja a un padre suyo; una pareja de nodos viejos, si
la fila saltó alguna ventana, tiene una cima testigo (la llegada revisada está cerrada) y la mayoría de sus tres
ramas pasa por los dos y por la cima; si no saltó ninguna, su rama se alarga sin más. -/
theorem snd_upOn (hb : Bounded φ) (hiY : SInvB Y) (hcs : Y.current_step = T) (hT : 1 ≤ T)
    (hvY : Y.isValid = true) (hda : DocsAlive Y) (hdk : d ∈ sonsOfMap φ k) (hdm : d ∈ mapNodes φ T)
    (hmaj : MajClosed φ T)
    (hs : Snd φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) Y)
    (hc : ∀ a, (SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) → CT Y (pidOfAssign φ a))
    (hvA : (Y.upOn d title (isProhibited φ)).isValid = true) :
    Snd φ (SolE φ (T + 1) d) (Y.upOn d title (isProhibited φ)) := by
  have hd : d.step = Y.current_step := by rw [hcs]; exact mapNodes_step φ T d hdm
  have hsub := sub_upOn_addNode (d := d) (title := title) (forb := isProhibited φ) hvY
  have hiA : SInvB (Y.upOn d title (isProhibited φ)) := sInvB_upOn hiY hd (by rw [hd, hcs]; omega)
  have cls : ∀ {q : PathNodeId}, q ∈ (Y.upOn d title (isProhibited φ)).alive →
      (q ∈ Y.alive ∧ q.id.step < T) ∨ (q ∈ Y.newRowIds d (isProhibited φ) ∧ q.id.step = T) := by
    intro q hq
    have := alive_addNode_cases (title := title) (forb := isProhibited φ) hiY.docs hiY.below hd (hsub.alive q hq)
    rw [hcs] at this; exact this
  -- un nodo de la fila y un vecino viejo
  have newOld : ∀ {n w : PathNodeId}, n ∈ Y.newRowIds d (isProhibited φ) → w.id.step < T →
      (Y.addNode d title (isProhibited φ)).Adj n w →
      ∃ a, SolE φ (T + 1) d a ∧ pidOfAssign φ a T = n ∧ pidOfAssign φ a w.id.step = w := by
    intro n w hn hw hnw
    obtain ⟨q, hq, hqw⟩ := rowParent_of_newAdj (title := title) hiY.docs hiY.below hiY.edges hd hn
      (by rw [hcs]; exact hw) hnw
    obtain ⟨_, _, _, hqs⟩ := step_of_newParents (rowParents_sub hq)
    obtain ⟨a, ha, hq', hw'⟩ := hs q w hqw
    rw [hqs, hcs] at hq'
    obtain ⟨a', hS, hpT, hpl⟩ := lift_row hb hT hdk hdm ha hq' hq hn
    exact ⟨a', hS, hpT, by rw [hpl _ hw]; exact hw'⟩
  intro x w hxw
  obtain ⟨hxa, hwa⟩ := hiA.edges x w hxw
  have hxw' := hsub.adj _ _ hxw
  rcases cls hxa with ⟨hxY, hxs⟩ | ⟨hxn, hxs⟩ <;> rcases cls hwa with ⟨hwY, hws⟩ | ⟨hwn, hws⟩
  · -- dos nodos viejos
    have hxwY : Y.Adj x w := adj_addNode_old (title := title) (forb := isProhibited φ) hd (by rw [hcs]; exact hxs)
      (by rw [hcs]; exact hws) hxw'
    obtain ⟨a0, ha0, hx0, hw0⟩ := hs x w hxwY
    cases hsk : Y.skipsWindow d (isProhibited φ)
    · -- ninguna ventana saltada: la rama se alarga
      have hct := hc a0 ha0
      have hnpar : pidOfAssign φ a0 (T - 1) ∈ Y.newParents := by
        obtain ⟨n, hn, _, _⟩ := hct.1.node (T - 1) (by omega) (by rw [hcs]; omega)
        have hid := node?_id hn
        unfold newParents
        rw [if_pos (by rw [hcs]; omega)]
        refine List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨node?_mem hn, ?_⟩, hid⟩
        rw [hid, hcs]; simp [pid_step]
      have hrow : shiftPid (pidOfAssign φ a0 (T - 1)) d ∈ Y.shiftRowIds d := by
        unfold shiftRowIds
        rw [if_pos (by rw [hcs]; omega)]
        exact (mem_dedupPids _ _).mpr (List.mem_map.mpr ⟨_, hnpar, rfl⟩)
      have hnew : shiftPid (pidOfAssign φ a0 (T - 1)) d ∈ Y.newRowIds d (isProhibited φ) := by
        refine List.mem_filter.mpr ⟨hrow, ?_⟩
        unfold skipsWindow at hsk
        have := List.any_eq_false.mp hsk _ hrow
        simpa using this
      obtain ⟨a', hS, _, hpl⟩ := lift_row hb hT hdk hdm ha0 rfl
        (List.mem_filter.mpr ⟨hnpar, by simp⟩) hnew
      exact ⟨a', hS, by rw [hpl _ hxs]; exact hx0, by rw [hpl _ hws]; exact hw0⟩
    · -- alguna ventana saltada: la llegada revisada está cerrada y hay una cima testigo
      obtain ⟨T', hT'⟩ := upOn_eq (d := d) (title := title) (forb := isProhibited φ) hvY
      have hiN : SInvB ((Y.addNode d title (isProhibited φ)).setT T') :=
        sInvB_setT (sInvB_addNode hiY hd (by rw [hd, hcs]; omega)) T'
      have hdirty : ((Y.addNode d title (isProhibited φ)).setT T').dirty = true := by
        show (Y.dirty || Y.skipsWindow d (isProhibited φ)) = true
        rw [hsk]; simp
      have hcl : ClosedState (Y.upOn d title (isProhibited φ)) := by
        rw [hT'] at hvA ⊢
        exact closedState_reviewOn hdirty hvA hiN.docs hiN.nodup hiN.below hiN.zero
          (by show 2 ≤ Y.current_step + 1; rw [hcs]; omega)
      have hcsA : (Y.upOn d title (isProhibited φ)).current_step = T + 1 := by
        rw [hsub.step]; show Y.current_step + 1 = _; rw [hcs]
      obtain ⟨n, hns, hxn, hwn⟩ := hcl.pair (y := x) (w := w) ⟨hxa, hwa, hxw⟩ T (by omega) (by rw [hcsA]; omega)
      have hnnew : n ∈ Y.newRowIds d (isProhibited φ) := by
        rcases cls hxn.2.1 with ⟨_, h⟩ | ⟨h, _⟩
        · omega
        · exact h
      obtain ⟨a1, hS1, hn1, hx1⟩ := newOld hnnew hxs ((adj_symm _ _ _).mp (hsub.adj _ _ hxn.2.2))
      obtain ⟨a2, hS2, hn2, hw2⟩ := newOld hnnew hws ((adj_symm _ _ _).mp (hsub.adj _ _ hwn.2.2))
      have hmT : pidOfAssign φ (maj3 a0 a1 a2) T = n := (pid_maj_bc (hn1.trans hn2.symm)).trans hn1
      refine ⟨maj3 a0 a1 a2, ⟨validUpTo_succ (hmaj _ _ _ ha0.1.1 (validUpTo_mono hS1.1 (by omega))
        (validUpTo_mono hS2.1 (by omega))) ?_, ?_⟩, ?_, ?_⟩
      · rw [hmT]
        have := (List.mem_filter.mp hnnew).2
        simpa using this
      · rw [show T + 1 - 1 = T by omega, ← pid_id, hmT]; exact newRow_id' hnnew
      · exact (pid_maj_ab (hx0.trans hx1.symm)).trans hx0
      · exact (pid_maj_ac (hw0.trans hw2.symm)).trans hw0
  · -- x viejo, w de la fila
    obtain ⟨a, hS, hpT, hpx⟩ := newOld hwn hxs ((adj_symm _ _ _).mp hxw')
    exact ⟨a, hS, hpx, by rw [hws]; exact hpT⟩
  · -- x de la fila, w viejo
    obtain ⟨a, hS, hpT, hpw⟩ := newOld hxn hws hxw'
    exact ⟨a, hS, by rw [hxs]; exact hpT, hpw⟩
  · -- los dos de la fila: son el mismo
    have e : x = w := adj_addNode_new (title := title) (forb := isProhibited φ) hiY.docs hiY.below hiY.edges
      (by rw [hcs]; exact hxs) (by rw [hcs]; exact hws) hxw'
    subst e
    obtain ⟨q, hq, hqa, hqs⟩ := exists_rowParent (d := d) (forb := isProhibited φ) hda (by rw [hcs]; omega) hxn
    obtain ⟨a, ha, hq', _⟩ := hs q q (adj_refl _ _ hqa)
    rw [hqs, hcs] at hq'
    obtain ⟨a', hS, hpT, _⟩ := lift_row hb hT hdk hdm ha hq' hq hxn
    exact ⟨a', hS, by rw [hxs]; exact hpT, by rw [hxs]; exact hpT⟩

end Up

-- ============================================================
-- De la semántica a los niveles
-- ============================================================

/-- **Con la semántica de parejas, la completitud y la mayoría, los tres niveles salen a la vez**: la mayoría de las
tres ramas de las aristas de un triángulo pasa por sus tres nodos. No hay escalera. -/
theorem levels_of_snd {E : GPathB} {T : Int} {k : NodeId} (hmaj : MajClosed φ T)
    (hs : Snd φ (SolE φ T k) E) (hc : ∀ a, SolE φ T k a → CT E (pidOfAssign φ a)) : TopEdge E ∧ TopTri E := by
  refine ⟨fun t _ hts w htw => ?_, fun t _ hts u w htu htw huw _ _ _ _ => ?_⟩
  · obtain ⟨a, hS, ht, hw⟩ := hs t w htw
    exact ⟨_, hc a hS, by rw [← hts]; exact ht, hw⟩
  · obtain ⟨a0, hS0, ht0, hu0⟩ := hs t u htu
    obtain ⟨a1, hS1, ht1, hw1⟩ := hs t w htw
    obtain ⟨a2, hS2, hu2, hw2⟩ := hs u w huw
    have hS : SolE φ T k (maj3 a0 a1 a2) :=
      ⟨hmaj _ _ _ hS0.1 hS1.1 hS2.1, by rw [sel_maj_ab (hS0.2.trans hS1.2.symm)]; exact hS0.2⟩
    refine ⟨_, hc _ hS, ?_, ?_, ?_⟩
    · rw [← hts]; exact (pid_maj_ab (ht0.trans ht1.symm)).trans ht0
    · exact (pid_maj_ac (hu0.trans hu2.symm)).trans hu0
    · exact (pid_maj_bc (hw1.trans hw2.symm)).trans hw1

-- ============================================================
-- El invariante de línea
-- ============================================================

/-- **El invariante semántico de la línea `:on`** del paso `T`: la contabilidad de siempre y, en cada entrada, toda
pareja de vecinos en la rama de una solución del prefijo con la clave de la entrada. -/
structure LInvS (φ : Cnf) (T : Int) (line : Line) : Prop where
  on    : LineOn T line
  nodup : (line.map (·.1)).Nodup
  keys  : ∀ kv ∈ line, kv.1 ∈ mapNodes φ (T - 1)
  inv   : ∀ kv ∈ line, SInvB kv.2
  ndt   : ∀ kv ∈ line, NoDegT kv.2
  docs  : ∀ kv ∈ line, DocsAlive kv.2
  snd   : ∀ kv ∈ line, Snd φ (SolE φ T kv.1) kv.2

/-- La completitud de una línea: cada entrada lleva la rama de toda solución del prefijo con su clave. -/
def CompLine (φ : Cnf) (T : Int) (line : Line) : Prop :=
  ∀ kv ∈ line, ∀ a, SolE φ T kv.1 a → CT kv.2 (pidOfAssign φ a)

/-- **El paso de la máquina bajo mayoría.** -/
theorem lInvS_advance (hb : Bounded φ) {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvS φ T line)
    (hcomp : CompLine φ T line) (hmaj : MajClosed φ T) : LInvS φ (T + 1) (advanceM .on φ line) := by
  have hlen := line_cases h.nodup h.keys
  have arr : ∀ kv ∈ line, ∀ d, SendsOn φ kv d →
      EntOn (T + 1) d (arrOn φ kv d) ∧ SInvB (arrOn φ kv d) ∧ NoDegT (arrOn φ kv d) ∧ DocsAlive (arrOn φ kv d) ∧
      Snd φ (SolE φ (T + 1) d) (arrOn φ kv d) ∧ d ∈ mapNodes φ T := by
    intro kv hkv d hs
    have hent := h.on kv hkv
    have hok := hent.1
    have hd : d.step = kv.2.current_step := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key, hok.step]; omega
    have hi := h.inv kv hkv
    have hcsY : (kv.2.filterAllOn (reqOf φ d)).current_step = T := by rw [step_filterAllOn]; exact hok.step
    have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by rw [step_filterAllOn]; exact hd
    have hvY : (kv.2.filterAllOn (reqOf φ d)).isValid = true :=
      valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
    have hiY := sInvB_filterAllOn hi (reqOf φ d)
    have hdaY := docsAlive_filterAllOn (h.docs kv hkv) (reqOf φ d) hvY
    have hdm : d ∈ mapNodes φ T := by
      have hk' : kv.1 ∈ mapNodes φ kv.1.step := by rw [hok.key]; exact h.keys kv hkv
      have := sonsOfMap_subset φ kv.1 hk' d hs.1
      rw [hok.key, show T - 1 + 1 = T by omega] at this
      exact this
    have sY := snd_filter hi hok.step hok.valid (reqOf_length_le_one φ d)
      (fun r hr => by have := reqOf_range hb r hr; rw [hd, hok.step] at this; exact this) hmaj
      (h.snd kv hkv) (hcomp kv hkv) hvY
    refine ⟨entOn_upFilteringOn hent hs.1 hs.2,
      sInvB_upOn hiY hdY (by rw [hd, hok.step]; omega),
      noDegT_upOn (noSelf_filterAllOn hent.2.1 _) (noDegT_filterAllOn hent.2.1 (h.ndt kv hkv) _),
      docsAlive_upOn hdaY hvY hs.2,
      snd_upOn hb hiY hcsY hT hvY hdaY hs.1 hdm hmaj sY (comp_filter (hcomp kv hkv)) hs.2, hdm⟩
  have ent : ∀ E ∈ advanceM .on φ line, SInvB E.2 ∧ NoDegT E.2 ∧ DocsAlive E.2 ∧
      Snd φ (SolE φ (T + 1) E.1) E.2 ∧ E.1 ∈ mapNodes φ T := by
    intro E hE
    rcases entry_shapeOn hlen h.nodup hE with ⟨kv, hkv, hs, he⟩ | ⟨a, ha, b, hb', _, hsa, hsb, he⟩
    · obtain ⟨_, hi, hn, hda, hp, hm⟩ := arr kv hkv E.1 hs
      rw [he]; exact ⟨hi, hn, hda, hp, hm⟩
    · obtain ⟨ea, ia, _, da, pa, hm⟩ := arr a ha E.1 hsa
      obtain ⟨eb, ib, _, db, pb, _⟩ := arr b hb' E.1 hsb
      have hcs : (arrOn φ a E.1).current_step = (arrOn φ b E.1).current_step := ea.1.step.trans eb.1.step.symm
      have hjoin : doJoinOn (arrOn φ a E.1) (arrOn φ b E.1) = joinOn (arrOn φ a E.1) (arrOn φ b E.1) := by
        unfold doJoinOn okJoin
        rw [if_pos (by simp [ea.1.step, eb.1.step, ea.1.mp, eb.1.mp, ea.1.valid, eb.1.valid])]
      rw [he, hjoin]
      exact ⟨sInvB_joinOn ia ib hcs, noDegT_joinOn ea.2.1 eb.2.1 ia.edges ib.edges, docsAlive_joinOn da db,
        snd_joinOn pa pb, hm⟩
  exact ⟨lineOn_advance h.on, advanceOn_nodup φ line,
    fun E hE => by rw [show T + 1 - 1 = T by omega]; exact (ent E hE).2.2.2.2,
    fun E hE => (ent E hE).1, fun E hE => (ent E hE).2.1, fun E hE => (ent E hE).2.2.1,
    fun E hE => (ent E hE).2.2.2.1⟩

/-- Por debajo de la tercera posición de la primera cláusula no hay ventanas prohibidas. -/
theorem not_prohibited_low {w : PathNodeId} (h : w.id.step < midFusion φ + 3) : isProhibited φ w = false := by
  cases hp : isProhibited φ w with
  | false => rfl
  | true =>
    exfalso
    simp only [isProhibited, isL3, Bool.and_eq_true, decide_eq_true_eq] at hp
    omega

theorem validUpTo_pre (a : Assign) {T : Int} (hT : T ≤ midFusion φ + 3) : ValidUpTo φ a T :=
  fun k hk => not_prohibited_low (by rw [pid_step]; omega)

/-- **Antes de la primera ventana prohibida todo conjunto de asignaciones es cerrado por mayoría**: son todas. -/
theorem majClosed_pre {T : Int} (hT : T ≤ midFusion φ + 3) : MajClosed φ T :=
  fun _ _ _ _ _ _ => validUpTo_pre _ hT

/-- La completitud de las líneas de la máquina (`comp_line`, con las claves sin repetir). -/
theorem compLine_steps (hb : Bounded φ) {n : Nat} (h : LInvS φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ))) :
    CompLine φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
  intro kv hkv a ha
  have hn : (n : Int) < stepCount φ := by
    have hk := h.keys kv hkv
    rw [show (n : Int) + 1 - 1 = n by omega] at hk
    by_cases hc : stepCount φ ≤ (n : Int)
    · unfold mapNodes at hk
      rw [if_neg (by omega), if_pos hc] at hk
      exact absurd hk List.not_mem_nil
    · omega
  obtain ⟨_, g, hf, hct⟩ := comp_line hb a n hn ha.1
  have hkey : selOfAssign φ a n = kv.1 := by have := ha.2; rw [show (n : Int) + 1 - 1 = n by omega] at this; exact this
  have hl := lookup_of_mem h.nodup hkv
  unfold lookup at hl
  rw [hkey] at hf
  rw [hf] at hl
  simp only [Option.map_some, Option.some.injEq] at hl
  rw [← hl]; exact hct

/-- **El caso base.** -/
theorem lInvS_init (φ : Cnf) : LInvS φ 1 (initM .on φ) := by
  have h0 := lInvX_init φ
  refine ⟨h0.on, h0.nodup, h0.keys, h0.inv, h0.ndt, h0.docs, ?_⟩
  obtain ⟨hl, g, hf, hct⟩ := initOn_inv φ (fun _ => false)
  rw [initM_eq] at hf
  let d : NodeId := ⟨0, 0⟩
  have hg : g = initSeedOn d "" := by
    have := List.mem_of_find?_eq_some hf
    rw [List.mem_singleton] at this
    exact (Prod.mk.inj this).2
  subst hg
  have hmem : (d, initSeedOn d "") ∈ initM .on φ := by rw [initM_eq]; exact List.mem_singleton_self _
  have hstep : (initSeedOn d "").current_step = 1 := (hl _ hmem).1.step
  have hsub : Sub (initSeedOn d "") (GPathB.empty.addNode d "" (fun _ => false)) :=
    sub_upOn_addNode (g := GPathB.empty) (by rfl)
  have huniq : ∀ q ∈ (initSeedOn d "").alive, q = { id := ⟨0, 0⟩, parent_id := none, gparent_id := none } := by
    intro q hq
    have := hsub.alive q hq
    rw [seedRow_alive] at this
    exact List.mem_singleton.mp this
  have hea : EdgesAlive (initSeedOn d "") := (h0.inv _ hmem).edges
  have hroot : pidOfAssign φ (fun _ => false) 0 = { id := ⟨0, 0⟩, parent_id := none, gparent_id := none } :=
    huniq _ (hct.1.alive 0 (Int.le_refl 0) (by rw [hstep]; omega))
  rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
  intro x w hxw
  have hx := huniq _ (hea _ _ hxw).1
  have hw := huniq _ (hea _ _ hxw).2
  refine ⟨fun _ => false, ⟨validUpTo_pre _ (by unfold midFusion; omega), by simp [sel_zero]⟩, ?_, ?_⟩
  · rw [hx]; exact hroot
  · rw [hw]; exact hroot

/-- **La inducción**: si las soluciones de los prefijos son cerradas por mayoría hasta la línea, el invariante
semántico vale en ella. -/
theorem lInvS_steps (hb : Bounded φ) : ∀ n : Nat, (∀ T : Int, T ≤ n → MajClosed φ T) →
    LInvS φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero => intro _; exact lInvS_init φ
  | succ n ih =>
    intro hm
    have hl := ih (fun T hT => hm T (by push_cast; omega))
    rw [stepsM_succ]
    have := lInvS_advance hb (by omega) hl (compLine_steps hb hl) (hm _ (by push_cast; omega))
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

/-- **Los tres niveles en toda línea cuyos prefijos son cerrados por mayoría.** -/
theorem levels_steps (hb : Bounded φ) (n : Nat) (hm : ∀ T : Int, T ≤ (n : Int) + 1 → MajClosed φ T) :
    ∀ kv ∈ stepsM .on φ n (initM .on φ), TopCT kv.2 ∧ TopEdge kv.2 ∧ TopTri kv.2 := by
  intro kv hkv
  have hl := lInvS_steps hb n (fun T hT => hm T (by omega))
  obtain ⟨h2, h3⟩ := levels_of_snd (hm _ (Int.le_refl _)) (hl.snd kv hkv)
    (compLine_steps hb hl kv hkv)
  exact ⟨topCT_of_topEdge h2, h2, h3⟩

/-- **Sin ventanas prohibidas las copias no consumen nivel.** Hasta la línea del segundo literal de la primera
cláusula, que ya ha pasado dos filtros lejanos, toda entrada cumple los tres niveles, sin hipótesis. La prueba no usa
la escalera: usa que las ramas son todas las asignaciones, y la mayoría. -/
theorem levels_before_first_window (hb : Bounded φ) (n : Nat) (hn : (n : Int) ≤ midFusion φ + 2) :
    ∀ kv ∈ stepsM .on φ n (initM .on φ), TopCT kv.2 ∧ TopEdge kv.2 ∧ TopTri kv.2 :=
  levels_steps hb n (fun _ hT => majClosed_pre (by omega))

end GPathB

-- ============================================================
-- La ventana prohibida, leída en la asignación
-- ============================================================

section Window

variable {φ : Cnf}

/-- **Una ventana prohibida de la rama es una cláusula con sus tres literales falsos.** -/
theorem prohibited_clause {a : Assign} {k : Int} (hpr : isProhibited φ (pidOfAssign φ a k) = true) :
    ∃ j c, φ.clauses[j]? = some c ∧ k = clauseStep φ j 2 ∧
      litVal a c.l1 = false ∧ litVal a c.l2 = false ∧ litVal a c.l3 = false := by
  simp only [isProhibited, isL3, pidOfAssign, selOfAssign_step, Bool.and_eq_true, beq_iff_eq] at hpr
  obtain ⟨⟨⟨⟨⟨hlo, hhi⟩, hmod⟩, hidx⟩, hpar⟩, hgp⟩ := hpr
  have hlo := of_decide_eq_true hlo
  have hhi := of_decide_eq_true hhi
  have hmod := of_decide_eq_true hmod
  obtain ⟨c, p, hp, hc⟩ := clauseOf_isSome φ k hlo hhi
  have hjlt : ((k - midFusion φ - 1) / 3).toNat < φ.clauses.length := by
    simp only [midFusion, fusionTop] at hlo hhi ⊢; omega
  obtain ⟨j, hjdef⟩ : ∃ j, j = ((k - midFusion φ - 1) / 3).toNat := ⟨_, rfl⟩
  rw [← hjdef] at hjlt
  have hcj : φ.clauses[j]? = some c := by
    simp only [clauseOf] at hc
    split at hc
    · exact absurd hc (by simp)
    · next c' hc' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rw [hjdef, hc']; rw [hc.1]
  have e3 : k = clauseStep φ j 2 := by simp only [hjdef, clauseStep, midFusion] at hlo hmod ⊢; omega
  have e2 : k - 1 = clauseStep φ j 1 := by rw [e3]; simp only [clauseStep]; omega
  have e1 : k - 2 = clauseStep φ j 0 := by rw [e3]; simp only [clauseStep]; omega
  have hk0 : 0 < k := by simp only [midFusion] at hlo; omega
  have hk1 : 1 < k := by simp only [midFusion] at hlo; omega
  rw [if_pos hk0] at hpar
  rw [if_pos hk1] at hgp
  simp only [Option.some.injEq] at hpar hgp
  have v3 := congrArg NodeId.index (selOfAssign_clause φ a j 2 c (by omega) hjlt hcj)
  have v2 := congrArg NodeId.index (selOfAssign_clause φ a j 1 c (by omega) hjlt hcj)
  have v1 := congrArg NodeId.index (selOfAssign_clause φ a j 0 c (by omega) hjlt hcj)
  rw [← e3] at v3
  rw [← e2] at v2
  rw [← e1] at v1
  have i3 : bit (litVal a c.l3) = 0 := by rw [← hidx]; exact v3.symm
  have i2 : bit (litVal a c.l2) = 0 := by
    have := congrArg NodeId.index hpar; simp only at this; rw [← this]; exact v2.symm
  have i1 : bit (litVal a c.l1) = 0 := by
    have := congrArg NodeId.index hgp; simp only at this; rw [← this]; exact v1.symm
  have z : ∀ {b : Bool}, bit b = 0 → b = false := by intro b; cases b <;> simp [bit]
  exact ⟨j, c, hcj, e3, z i1, z i2, z i3⟩

/-- Y al revés: una cláusula con sus tres literales falsos da una ventana prohibida en su tercer paso. -/
theorem prohibited_of_false {a : Assign} {j : Nat} {c : Clause} (hj : φ.clauses[j]? = some c)
    (h1 : litVal a c.l1 = false) (h2 : litVal a c.l2 = false) (h3 : litVal a c.l3 = false) :
    isProhibited φ (pidOfAssign φ a (clauseStep φ j 2)) = true := by
  have hjlt : j < φ.clauses.length := by
    by_cases hc : j < φ.clauses.length
    · exact hc
    · rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  have s3 := selOfAssign_clause φ a j 2 c (by omega) hjlt hj
  have s2 := selOfAssign_clause φ a j 1 c (by omega) hjlt hj
  have s1 := selOfAssign_clause φ a j 0 c (by omega) hjlt hj
  have e2 : clauseStep φ j 2 - 1 = clauseStep φ j 1 := by simp only [clauseStep]; omega
  have e1 : clauseStep φ j 2 - 2 = clauseStep φ j 0 := by simp only [clauseStep]; omega
  have hk0 : 0 < clauseStep φ j 2 := by simp only [clauseStep]; omega
  have hk1 : 1 < clauseStep φ j 2 := by simp only [clauseStep]; omega
  have l3 : litVal a (litAt c 2) = false := h3
  have l2 : litVal a (litAt c 1) = false := h2
  have l1 : litVal a (litAt c 0) = false := h1
  simp only [isProhibited, isL3, pidOfAssign, if_pos hk0, if_pos hk1, e2, e1, s3, s2, s1, l3, l2, l1, bit,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [clauseStep, midFusion]; omega
  · simp only [clauseStep, fusionTop]; omega
  · simp only [clauseStep, midFusion]; omega
  · rfl
  · simp
  · simp

theorem litVal_maj (a b c : Assign) (l : Lit) :
    litVal (maj3 a b c) l = ((litVal a l && litVal b l) || (litVal a l && litVal c l) || (litVal b l && litVal c l)) := by
  unfold litVal maj3
  split <;> cases a l.v <;> cases b l.v <;> cases c l.v <;> rfl

/-- **Las fórmulas con forma 2-CNF**: en cada cláusula el segundo y el tercer literal son el mismo. -/
def TwoLike (φ : Cnf) : Prop := ∀ c ∈ φ.clauses, c.l2 = c.l3

/-- **En una fórmula con forma 2-CNF las soluciones de todo prefijo son cerradas por mayoría**: si la mayoría hace
falsos los dos literales distintos de una cláusula, una de las tres asignaciones ya los hacía falsos. -/
theorem majClosed_twoLike (h2 : TwoLike φ) (T : Int) : MajClosed φ T := by
  intro a b c ha hbv hc k hk
  cases hp : isProhibited φ (pidOfAssign φ (maj3 a b c) k) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨j, cl, hj, e, m1, m2, _⟩ := prohibited_clause hp
    have heq := h2 cl (List.mem_of_getElem? hj)
    rw [litVal_maj] at m1 m2
    have key : (litVal a cl.l1 = false ∧ litVal a cl.l2 = false) ∨ (litVal b cl.l1 = false ∧ litVal b cl.l2 = false) ∨
        (litVal c cl.l1 = false ∧ litVal c cl.l2 = false) := by
      revert m1 m2
      cases litVal a cl.l1 <;> cases litVal b cl.l1 <;> cases litVal c cl.l1 <;>
        cases litVal a cl.l2 <;> cases litVal b cl.l2 <;> cases litVal c cl.l2 <;> simp
    rcases key with ⟨x1, x2⟩ | ⟨x1, x2⟩ | ⟨x1, x2⟩
    · have := prohibited_of_false (a := a) hj x1 x2 (by rw [← heq]; exact x2)
      rw [← e, ha k hk] at this; cases this
    · have := prohibited_of_false (a := b) hj x1 x2 (by rw [← heq]; exact x2)
      rw [← e, hbv k hk] at this; cases this
    · have := prohibited_of_false (a := c) hj x1 x2 (by rw [← heq]; exact x2)
      rw [← e, hc k hk] at this; cases this

end Window

namespace MachineOn

open GPathB Driver Machine Struct

variable {φ : Cnf}

/-- El veredicto, desde `TopCT` de los estados finales. -/
theorem spineVerdictOn_iff_of_finalTopCT (hbd : Bounded φ) (H : ∀ kv ∈ runM .on φ, TopCT kv.2) :
    SpineVerdictOn φ ↔ Satisfiable φ := by
  constructor
  · rintro ⟨kv, hkv, hval⟩
    obtain ⟨hlo, hls⟩ := lineOn_run_shape hbd
    have hent := hlo kv hkv
    have hsh := hls kv hkv
    have hsc : 2 ≤ stepCount φ := by unfold stepCount; omega
    have hcs0 : kv.2.current_step = stepCount φ := hent.1.step
    have hval' : (kv.2.pinOn []).isValid = true := hval
    have hcs : (kv.2.pinOn []).current_step = stepCount φ := (step_pinOn kv.2 []).trans hcs0
    obtain ⟨t, ht, hts⟩ := exists_alive_at hval' (k := stepCount φ - 1) (by omega) (by rw [hcs]; omega)
    obtain ⟨S, hS, _⟩ := H kv hkv t ((sub_pinOn kv.2 []).alive t ht) (by rw [hts, hcs0])
    have hct : CT (kv.2.pinOn []) S := ct_pinOn hS [] (fun r hr => absurd hr List.not_mem_nil)
    have hstr : Struct φ (kv.2.pinOn []) :=
      struct_of_sub (sub_pinOn kv.2 []) ⟨hsh.2.2.1.pmp, hsh.2.2.1.gpmp, hsh.2.2.1.noforb, hsh.2.2.1.onmap,
        hsh.2.2.1.req⟩
    exact ⟨Decode.decode S, Decode.sat_of_carried hbd hstr hct.1 hcs⟩
  · rintro ⟨a, ha⟩
    obtain ⟨g, hf, hct, _⟩ := run_carriesOn hbd a ha
    refine ⟨_, List.mem_of_find?_eq_some hf, ?_⟩
    exact isValid_of_carried (ct_reviewOn (ct_dirty hct true)).1

/-- **La espina `:on` decide toda fórmula cuyas soluciones de prefijo son cerradas por mayoría**, sin más
hipótesis. La ventana prohibida es lo único que puede romper esa clausura. -/
theorem spineVerdictOn_iff_of_majClosed (hbd : Bounded φ) (hm : ∀ T : Int, MajClosed φ T) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_finalTopCT hbd
    (fun kv hkv => (levels_steps hbd (stepCount φ - 1).toNat (fun T _ => hm T) kv hkv).1)

/-- **La espina `:on` decide las fórmulas con forma 2-CNF**, sin hipótesis. -/
theorem spineVerdictOn_iff_of_twoLike (hbd : Bounded φ) (h2 : TwoLike φ) : SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_majClosed hbd (majClosed_twoLike h2)

end MachineOn

end AbsSatBingo.Model
