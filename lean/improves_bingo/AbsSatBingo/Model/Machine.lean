-- lean/improves_bingo/AbsSatBingo/Model/Machine.lean
import AbsSatBingo.Model.Grow
import AbsSatBingo.Model.Reader
import AbsSatBingo.Model.Driver
import AbsSatBin.GraphMap.CnfSelBin

/-!
# La máquina lleva la camarilla de toda solución (fase L6b, parte 2)

**`run_carries`**: si `a` satisface `φ`, la línea final de la máquina tiene, en la clave que elige `a`, un estado que
lleva la camarilla de `a` (`pidOfAssign φ a`: el id de camino que la rama de `a` tiene en cada paso). En particular
la máquina dice SAT (`machineVerdict_of_sat`).

Es una inducción sobre las líneas. En cada línea `t`:
* **`LineOk`** — todo estado está en el paso `t + 1`, en su nodo de mapa, es válido y sus documentos están por
  debajo de su paso;
* **`Has`** — el primer estado con la clave `selOfAssign φ a t` lleva la camarilla.

El paso usa `carried_filterAll` (los requisitos de la rama concuerdan con ella: `reqSat_selOfAssign`),
`carried_up` (la ventana de la rama no está prohibida: `pidOfAssign_not_prohibited`, el único sitio donde entra
`Sat`) y `carried_doJoin_*` (los joins de la línea no la pierden).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace Machine

open GPathB Driver

-- ============================================================
-- La rama de una asignación
-- ============================================================

theorem pid_step (φ : Cnf) (a : Assign) (k : Int) : (pidOfAssign φ a k).id.step = k :=
  selOfAssign_step φ a k

theorem pid_root (φ : Cnf) (a : Assign) : (pidOfAssign φ a 0).parent_id = none := by
  simp [pidOfAssign]

/-- La ventana de la rama se desplaza como la de la máquina. -/
theorem shift_pid (φ : Cnf) (a : Assign) (c : Int) (hc : 0 < c) :
    shiftPid (pidOfAssign φ a (c - 1)) (selOfAssign φ a c) = pidOfAssign φ a c := by
  simp only [shiftPid, pidOfAssign]
  congr 1
  · simp [hc]
  · by_cases h : 1 < c
    · simp [h, show c - 1 - 1 = c - 2 by omega]
    · simp [h]

theorem sonsOfMap_step (φ : Cnf) (d s : NodeId) (h : s ∈ sonsOfMap φ d) : s.step = d.step + 1 := by
  unfold sonsOfMap at h
  split at h
  · rw [List.mem_singleton] at h; subst h; rfl
  · exact mapNodes_step φ _ _ h

-- ============================================================
-- Documentos por debajo del paso
-- ============================================================

def Below (g : GPathB) : Prop := ∀ n ∈ g.nodes, n.id.id.step < g.current_step

theorem below_of_shrinks {h g : GPathB} (hs : Shrinks h g) (hb : Below g) : Below h := by
  intro n hn
  obtain ⟨m, hm, hid, _, _⟩ := hs.1.nodes n hn
  rw [hs.1.step, ← hid]
  exact hb m hm

theorem mapId_of_mem_shiftRowIds {g : GPathB} {d : NodeId} {pid : PathNodeId} (h : pid ∈ g.shiftRowIds d) :
    pid.id = d := by
  unfold shiftRowIds at h
  split at h
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp ((mem_dedupPids _ _).mp h)
    rfl
  · rw [List.mem_singleton] at h; subst h; rfl

theorem below_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (hb : Below g) (hd : d.step = g.current_step) : Below (g.addNode d title forb) := by
  intro n hn
  show n.id.id.step < g.current_step + 1
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    have := hb m hm
    show m.id.id.step < _
    omega
  · obtain ⟨pid, hpid, rfl⟩ := List.mem_map.mp hn
    show pid.id.step < _
    rw [mapId_of_mem_shiftRowIds (List.mem_filter.mp hpid).1, hd]
    omega

theorem aliveDocs_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (h : AliveDocs g) : AliveDocs (g.addNode d title forb) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨n, hn, rfl⟩ := h q hq
    exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨n, hn, rfl⟩), rfl⟩
  · exact ⟨g.rowNode d title q, List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩), rfl⟩

theorem aliveDocs_join {g₁ g₂ : GPathB} (h₁ : AliveDocs g₁) (h₂ : AliveDocs g₂) : AliveDocs (join g₁ g₂) := by
  intro q hq
  rcases (alive_join g₁ g₂ q).mp hq with hq | hq
  · obtain ⟨n, hn, rfl⟩ := h₁ q hq
    exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨n, hn, rfl⟩), by split <;> rfl⟩
  · obtain ⟨m, hm, rfl⟩ := h₂ q hq
    cases hn : g₁.node? m.id with
    | some n =>
      refine ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨n, node?_mem hn, rfl⟩), ?_⟩
      have := node?_id hn
      split <;> exact this
    | none =>
      exact ⟨m, List.mem_append_right _ (List.mem_filter.mpr ⟨hm, by simp [hn]⟩), rfl⟩

-- ============================================================
-- Lo que un `upFiltering` válido deja
-- ============================================================

/-- Un estado de la máquina en el paso `T`, en su nodo de mapa `key`. -/
structure StateOk (T : Int) (key : NodeId) (g : GPathB) : Prop where
  step  : g.current_step = T
  mp    : g.map_parent = some key
  valid : g.isValid = true
  below : Below g
  key   : key.step = T - 1
  docs  : AliveDocs g

theorem stateOk_upFiltering {φ : Cnf} {T : Int} {key d : NodeId} {g : GPathB} (hg : StateOk T key g)
    (hd : d ∈ sonsOfMap φ key) (hv : (g.upFiltering (reqOf φ d) d "" (isProhibited φ)).isValid = true) :
    StateOk (T + 1) d (g.upFiltering (reqOf φ d) d "" (isProhibited φ)) := by
  have hs := shrinks_filterAll g (reqOf φ d)
  have hdstep : d.step = T := by rw [sonsOfMap_step φ key d hd, hg.key]; omega
  unfold upFiltering up at hv ⊢
  split
  · rename_i hv1
    have hsr := shrinks_review ((g.filterAll (reqOf φ d)).addNode d "" (isProhibited φ))
    have hstep : (g.filterAll (reqOf φ d)).current_step = T := (step_of_shrinks hs).trans hg.step
    rw [if_pos hv1] at hv
    refine ⟨?_, ?_, hv, ?_, by omega, ?_⟩
    · rw [step_of_shrinks hsr]; show (g.filterAll (reqOf φ d)).current_step + 1 = _; rw [hstep]
    · rw [hsr.1.mp]; rfl
    · refine below_of_shrinks hsr (below_addNode (below_of_shrinks hs hg.below) ?_)
      rw [hdstep, hstep]
    · exact aliveDocs_review (aliveDocs_addNode (aliveDocs_filterAll hg.docs _))
  · rename_i hv1
    rw [if_neg hv1] at hv
    exact absurd hv hv1

-- ============================================================
-- La inserción
-- ============================================================

def LineOk (T : Int) (line : Line) : Prop := ∀ kv ∈ line, StateOk T kv.1 kv.2

theorem stateOk_doJoin {T : Int} {key : NodeId} {e g : GPathB} (he : StateOk T key e) (hg : StateOk T key g) :
    StateOk T key (doJoin e g) := by
  unfold doJoin
  split
  · refine ⟨he.step, he.mp, ?_, ?_, he.key, aliveDocs_join he.docs hg.docs⟩
    · unfold isValid
      have := he.valid
      unfold isValid at this
      rw [List.all_eq_true] at this ⊢
      intro k hk
      obtain ⟨q, hq, hqk⟩ := List.any_eq_true.mp (this k hk)
      exact List.any_eq_true.mpr ⟨q, (alive_join e g q).mpr (Or.inl hq), hqk⟩
    · intro n hn
      show n.id.id.step < e.current_step
      rcases List.mem_append.mp hn with hn | hn
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
        have := he.below m hm
        split <;> exact this
      · have := hg.below n (List.mem_filter.mp hn).1
        rw [he.step, ← hg.step]; exact this
  · exact he

theorem lineOk_insert {T : Int} {line : Line} {key : NodeId} {g : GPathB} (hl : LineOk T line)
    (hg : StateOk T key g) : LineOk T (Driver.insert line key g) := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    subst hkey
    have he := hl _ (List.mem_of_find?_eq_some hfind)
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact stateOk_doJoin he hg
    · exact hl kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton] at h; subst h; exact hg

/-- El primer estado con la clave `key` lleva `S`. -/
def Has (S : Int → PathNodeId) (key : NodeId) (line : Line) : Prop :=
  ∃ g, line.find? (fun kv => kv.1 == key) = some (key, g) ∧ Carried g S

theorem find?_map_ite (key key' : NodeId) (v : GPathB) (hne : key ≠ key') :
    ∀ line : Line, Option.map (fun kv => if (kv.1 == key) = true then (key, v) else kv)
      (List.find? ((fun kv => kv.1 == key') ∘ fun kv => if (kv.1 == key) = true then (key, v) else kv) line) =
      line.find? (fun kv => kv.1 == key') := by
  intro line
  induction line with
  | nil => rfl
  | cons kv rest ih =>
    simp only [List.find?_cons, Function.comp]
    by_cases hk : kv.1 = key
    · have h1 : (kv.1 == key) = true := by simp [hk]
      have h2 : (kv.1 == key') = false := by rw [hk]; exact beq_false_of_ne hne
      have h3 : (key == key') = false := beq_false_of_ne hne
      simp only [h1, if_true, h3, h2]
      exact ih
    · have h1 : (kv.1 == key) = false := beq_false_of_ne hk
      simp only [h1, Bool.false_eq_true, if_false]
      split
      · simp only [Option.map_some, h1, Bool.false_eq_true, if_false]
      · exact ih

theorem find?_insert_ne (line : Line) (key key' : NodeId) (g : GPathB) (hne : key ≠ key') :
    (Driver.insert line key g).find? (fun kv => kv.1 == key') = line.find? (fun kv => kv.1 == key') := by
  unfold Driver.insert
  split
  · rw [List.find?_map]
    exact find?_map_ite key key' _ hne line
  · rw [List.find?_append]
    cases hf : line.find? (fun kv => kv.1 == key') with
    | some _ => rfl
    | none =>
      simp only [Option.none_or, List.find?_cons, List.find?_nil]
      have : ((key, g).1 == key') = false := beq_false_of_ne hne
      rw [this]

/-- Insertar conserva `Has` (los joins no pierden la camarilla). -/
theorem has_insert {S : Int → PathNodeId} {key key' : NodeId} {line : Line} {g : GPathB}
    (h : Has S key' line) : Has S key' (Driver.insert line key g) := by
  by_cases hk : key = key'
  · subst hk
    obtain ⟨g0, hf, hc⟩ := h
    refine ⟨doJoin g0 g, ?_, carried_doJoin_left hc⟩
    unfold Driver.insert
    rw [hf]
    simp only
    rw [List.find?_map]
    have : (List.find? ((fun kv => kv.1 == key) ∘ fun kv => if kv.1 == key then (key, doJoin g0 g) else kv) line) =
        line.find? (fun kv => kv.1 == key) := by
      congr 1; funext kv; simp only [Function.comp]; split <;> simp_all
    rw [this, hf]
    simp
  · obtain ⟨g0, hf, hc⟩ := h
    exact ⟨g0, by rw [find?_insert_ne line key key' g hk, hf], hc⟩

/-- Insertar un estado que lleva `S` en su clave establece `Has`, si los estados de esa clave se pueden unir. -/
theorem has_insert_self {S : Int → PathNodeId} {T : Int} {key : NodeId} {line : Line} {g : GPathB}
    (hl : LineOk T line) (hg : StateOk T key g) (hc : Carried g S) : Has S key (Driver.insert line key g) := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    subst hkey
    have he : StateOk T key' e := hl _ (List.mem_of_find?_eq_some hfind)
    refine ⟨doJoin e g, ?_, ?_⟩
    · rw [List.find?_map]
      have : (List.find? ((fun kv => kv.1 == key') ∘ fun kv => if kv.1 == key' then (key', doJoin e g) else kv) line) =
          line.find? (fun kv => kv.1 == key') := by
        congr 1; funext kv; simp only [Function.comp]; split <;> simp_all
      rw [this, hfind]
      simp
    · apply carried_doJoin_right _ hc
      unfold okJoin
      simp [he.step, hg.step, he.mp, hg.mp, he.valid, hg.valid]
  · rename_i hnone
    refine ⟨g, ?_, hc⟩
    rw [List.find?_append, hnone]
    simp

-- ============================================================
-- Un paso de la máquina
-- ============================================================

/-- Un `foldl` en el que un elemento establece `P`, los demás lo conservan, y `Q` es un invariante de todos. -/
theorem foldl_establish {α β : Type} (f : β → α → β) (P Q : β → Prop) (l : List α)
    (hQ : ∀ x a, a ∈ l → Q x → Q (f x a)) (hpres : ∀ x a, a ∈ l → Q x → P x → P (f x a))
    (e : α) (hest : ∀ x, Q x → P (f x e)) :
    e ∈ l → ∀ init, Q init → P (l.foldl f init) := by
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons a as ih =>
    intro h init hq
    simp only [List.foldl_cons]
    have hQ' : ∀ x b, b ∈ as → Q x → Q (f x b) := fun x b hb => hQ x b (List.mem_cons_of_mem _ hb)
    have hpres' : ∀ x b, b ∈ as → Q x → P x → P (f x b) := fun x b hb => hpres x b (List.mem_cons_of_mem _ hb)
    rcases List.mem_cons.mp h with rfl | h
    · have : ∀ (l' : List α), (∀ b ∈ l', b ∈ as) → ∀ x, Q x → P x → P (l'.foldl f x) := by
        intro l'
        induction l' with
        | nil => intro _ x _ hx; exact hx
        | cons b bs ih' =>
          intro hsub x hqx hx
          exact ih' (fun c hc => hsub c (List.mem_cons_of_mem _ hc)) _
            (hQ' x b (hsub b (List.mem_cons_self ..)) hqx) (hpres' x b (hsub b (List.mem_cons_self ..)) hqx hx)
      exact this as (fun _ hb => hb) _ (hQ init e (List.mem_cons_self ..) hq) (hest init hq)
    · exact ih hQ' hpres' h _ (hQ init a (List.mem_cons_self ..) hq)

theorem foldl_pres {α β : Type} (f : β → α → β) (P : β → Prop) (l : List α)
    (hpres : ∀ x a, a ∈ l → P x → P (f x a)) : ∀ init, P init → P (l.foldl f init) := by
  induction l with
  | nil => intro x hx; exact hx
  | cons b bs ih =>
    intro x hx
    exact ih (fun y a ha hy => hpres y a (List.mem_cons_of_mem _ ha) hy) _ (hpres x b (List.mem_cons_self ..) hx)

theorem lineOk_sendTo {φ : Cnf} {T : Int} {kv : NodeId × GPathB} (hkv : StateOk T kv.1 kv.2) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) {next : Line} (hn : LineOk (T + 1) next) :
    LineOk (T + 1) (sendTo φ kv.2 next d) := by
  unfold sendTo
  dsimp only
  split
  · exact lineOk_insert hn (stateOk_upFiltering hkv hd (by assumption))
  · exact hn

theorem lineOk_sendAll {φ : Cnf} {T : Int} {kv : NodeId × GPathB} (hkv : StateOk T kv.1 kv.2) {next : Line}
    (hn : LineOk (T + 1) next) : LineOk (T + 1) (sendAll φ kv next) :=
  foldl_pres _ (LineOk (T + 1)) _ (fun _ d hd hx => lineOk_sendTo hkv d hd hx) _ hn

theorem lineOk_advance {φ : Cnf} {T : Int} {line : Line} (hl : LineOk T line) :
    LineOk (T + 1) (advance φ line) :=
  foldl_pres _ (LineOk (T + 1)) _ (fun _ kv hkv hx => lineOk_sendAll (hl kv hkv) hx) _
    (fun _ h => absurd h List.not_mem_nil)

theorem has_sendTo {φ : Cnf} {S : Int → PathNodeId} {key : NodeId} {g : GPathB} {next : Line} {d : NodeId}
    (h : Has S key next) : Has S key (sendTo φ g next d) := by
  unfold sendTo; dsimp only; split
  · exact has_insert h
  · exact h

/-- **El paso**: la rama de `a` sigue viva en la línea siguiente. -/
theorem advance_has (φ : Cnf) (hb : Bounded φ) (a : Assign) (hsat : Sat a φ) (t : Int) (ht0 : 0 ≤ t)
    (ht : t + 1 < stepCount φ) (line : Line) (hl : LineOk (t + 1) line)
    (hh : Has (pidOfAssign φ a) (selOfAssign φ a t) line) :
    Has (pidOfAssign φ a) (selOfAssign φ a (t + 1)) (advance φ line) := by
  obtain ⟨g0, hf, hc⟩ := hh
  have hmem := List.mem_of_find?_eq_some hf
  have hok : StateOk (t + 1) (selOfAssign φ a t) g0 := hl _ hmem
  let S := pidOfAssign φ a
  let d := selOfAssign φ a (t + 1)
  have hd : d ∈ sonsOfMap φ (selOfAssign φ a t) := selOfAssign_son φ a t ht0 ht
  -- el estado que llega a `d` lleva la camarilla
  let g1 := g0.filterAll (reqOf φ d)
  have hs1 := shrinks_filterAll g0 (reqOf φ d)
  have hstep1 : g1.current_step = t + 1 := (step_of_shrinks hs1).trans hok.step
  have hc1 : Carried g1 S := by
    refine carried_filterAll hc _ ?_
    intro r hr _ _
    exact reqSat_selOfAssign φ hb a (t + 1) r hr
  have hnp : S t ∈ g1.newParents := by
    obtain ⟨n, hn, _, _⟩ := hc1.node t ht0 (by omega)
    have hid := node?_id hn
    unfold newParents
    rw [if_pos (by omega)]
    refine List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨node?_mem hn, ?_⟩, hid⟩
    rw [hid, hstep1]; simp [S, pid_step]
  have hshift : shiftPid (S t) d = S (t + 1) := by
    have := shift_pid φ a (t + 1) (by omega)
    simpa using this
  have hc2 : Carried (g1.up d "" (isProhibited φ)) S := by
    apply carried_up hc1
    · rw [hstep1]
      refine List.mem_filter.mpr ⟨?_, by simp [S, pidOfAssign_not_prohibited φ a hsat]⟩
      unfold shiftRowIds
      rw [if_pos (by omega)]
      exact (mem_dedupPids _ _).mpr (List.mem_map.mpr ⟨S t, hnp, hshift⟩)
    · intro _
      rw [hstep1, show t + 1 - 1 = t by omega]
      exact List.mem_filter.mpr ⟨hnp, by simp [hshift]⟩
    · rw [hstep1]; exact pid_step φ a _
    · rw [hstep1]; exact fun n hn => hstep1 ▸ below_of_shrinks hs1 hok.below n hn
    · exact pid_root φ a
  have hup : g0.upFiltering (reqOf φ d) d "" (isProhibited φ) = g1.up d "" (isProhibited φ) := rfl
  -- el paso de la máquina
  have hvalid : (g0.upFiltering (reqOf φ d) d "" (isProhibited φ)).isValid = true := by
    rw [hup]; exact isValid_of_carried hc2
  have hok2 : StateOk (t + 1 + 1) d (g0.upFiltering (reqOf φ d) d "" (isProhibited φ)) :=
    stateOk_upFiltering hok hd hvalid
  unfold advance
  refine foldl_establish _ (fun next => Has S d next) (LineOk (t + 1 + 1)) line
    (fun _ kv hkv hx => lineOk_sendAll (hl kv hkv) hx)
    (fun _ kv _ _ hx => by
      unfold sendAll
      exact foldl_pres _ (fun next => Has S d next) _ (fun y d' _ hy => has_sendTo hy) _ hx)
    (selOfAssign φ a t, g0) ?_ hmem [] (fun _ h => absurd h List.not_mem_nil)
  intro x hx
  unfold sendAll
  refine foldl_establish _ (fun next => Has S d next) (LineOk (t + 1 + 1)) _
    (fun y d' hd' hy => lineOk_sendTo hok d' hd' hy)
    (fun y d' _ _ hy => has_sendTo hy) d ?_ hd x hx
  intro y hy
  unfold sendTo
  dsimp only
  rw [if_pos hvalid]
  exact has_insert_self hy hok2 (by rw [hup]; exact hc2)

-- ============================================================
-- La línea inicial y la inducción
-- ============================================================

theorem sel_zero (φ : Cnf) (a : Assign) : selOfAssign φ a 0 = ⟨0, 0⟩ := by simp [selOfAssign]

theorem stepCount_pos (φ : Cnf) : 0 < stepCount φ := by unfold stepCount; omega

theorem carried_empty (S : Int → PathNodeId) : Carried GPathB.empty S :=
  ⟨fun k h0 h1 => absurd h1 (by show ¬ k < 0; omega), fun k h0 h1 => absurd h1 (by show ¬ k < 0; omega),
   fun k _ h0 h1 _ _ => absurd h1 (by show ¬ k < 0; omega), fun h => absurd h (by show ¬ (0 : Int) < 0; omega),
   fun k h0 h1 => absurd h1 (by show ¬ k < 0; omega)⟩

theorem init_eq (φ : Cnf) : init φ = [(⟨0, 0⟩, initSeed ⟨0, 0⟩ "")] := by
  unfold init
  have : mapNodes φ 0 = [⟨0, 0⟩] := by
    unfold mapNodes
    have := stepCount_pos φ
    simp only [show ¬ (0 : Int) < 0 by omega, if_false, show ¬ stepCount φ ≤ 0 by omega, if_true]
  rw [this]
  rfl

theorem init_inv (φ : Cnf) (a : Assign) :
    LineOk 1 (init φ) ∧ Has (pidOfAssign φ a) (selOfAssign φ a 0) (init φ) := by
  let S := pidOfAssign φ a
  let d : NodeId := ⟨0, 0⟩
  have hc : Carried (initSeed d "") S := by
    unfold initSeed
    apply carried_up (carried_empty S)
    · show S 0 ∈ (GPathB.empty.shiftRowIds d).filter _
      refine List.mem_filter.mpr ⟨?_, rfl⟩
      unfold shiftRowIds
      rw [if_neg (by show ¬ (0 : Int) < 0; omega)]
      simp [S, pidOfAssign, sel_zero, d]
    · intro h; exact absurd h (by show ¬ (0 : Int) < 0; omega)
    · exact pid_step φ a 0
    · intro n hn; exact absurd hn List.not_mem_nil
    · exact pid_root φ a
  have hok : StateOk 1 d (initSeed d "") := by
    have hsr := shrinks_review (GPathB.empty.addNode d "" (fun _ => false))
    have hup : initSeed d "" = (GPathB.empty.addNode d "" (fun _ => false)).review := by
      unfold initSeed up
      rw [if_pos (show GPathB.empty.isValid = true by rfl)]
    refine ⟨?_, ?_, isValid_of_carried hc, ?_, rfl, ?_⟩
    · rw [hup, step_of_shrinks hsr]; rfl
    · rw [hup, hsr.1.mp]; rfl
    · rw [hup]
      exact below_of_shrinks hsr (below_addNode (fun n hn => absurd hn List.not_mem_nil) rfl)
    · rw [hup]
      exact aliveDocs_review (aliveDocs_addNode (fun q hq => absurd hq List.not_mem_nil))
  rw [init_eq]
  refine ⟨?_, initSeed d "", ?_, hc⟩
  · intro kv hkv
    rw [List.mem_singleton] at hkv; subst hkv; exact hok
  · rw [sel_zero]; simp [d]

theorem steps_inv (φ : Cnf) (hb : Bounded φ) (a : Assign) (hsat : Sat a φ) :
    ∀ (n : Nat) (t : Int) (line : Line), 0 ≤ t → t + n < stepCount φ →
      LineOk (t + 1) line → Has (pidOfAssign φ a) (selOfAssign φ a t) line →
      LineOk (t + n + 1) (steps φ n line) ∧ Has (pidOfAssign φ a) (selOfAssign φ a (t + n)) (steps φ n line) := by
  intro n
  induction n with
  | zero =>
    intro t line _ _ hl hh
    have h0 : t + ((0 : Nat) : Int) = t := by omega
    simp only [steps]
    rw [h0]
    exact ⟨hl, hh⟩
  | succ n ih =>
    intro t line h0 ht hl hh
    simp only [steps]
    have h1 := lineOk_advance (φ := φ) hl
    have h2 := advance_has φ hb a hsat t h0 (by omega) line hl hh
    have := ih (t + 1) (advance φ line) (by omega) (by omega) h1 h2
    rw [show t + 1 + (n : Int) = t + ((n + 1 : Nat) : Int) by push_cast; omega] at this
    exact this

/-- **La máquina lleva la camarilla de toda solución**: si `a` satisface `φ`, el primer estado de la línea final con
la clave de `a` lleva `pidOfAssign φ a`, y está bien formado. -/
theorem run_carries (φ : Cnf) (hb : Bounded φ) (a : Assign) (hsat : Sat a φ) :
    ∃ g, (run φ).find? (fun kv => kv.1 == selOfAssign φ a (stepCount φ - 1)) =
        some (selOfAssign φ a (stepCount φ - 1), g) ∧
      Carried g (pidOfAssign φ a) ∧ StateOk (stepCount φ) (selOfAssign φ a (stepCount φ - 1)) g := by
  have hpos := stepCount_pos φ
  obtain ⟨hl0, hh0⟩ := init_inv φ a
  have hn : (0 : Int) + ((stepCount φ - 1).toNat : Int) = stepCount φ - 1 := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  obtain ⟨hl, g, hf, hc⟩ := steps_inv φ hb a hsat (stepCount φ - 1).toNat 0 (init φ) (by omega)
    (by rw [hn]; omega) (by simpa using hl0) hh0
  rw [hn] at hf hl
  refine ⟨g, hf, hc, ?_⟩
  have := hl _ (List.mem_of_find?_eq_some hf)
  rw [show stepCount φ - 1 + 1 = stepCount φ by omega] at this
  exact this

/-- **Completitud de la máquina**: si `φ` es satisfacible, dice SAT. -/
theorem machineVerdict_of_sat (φ : Cnf) (hb : Bounded φ) (hs : Satisfiable φ) : machineVerdict φ = true := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨g, hf, _, _⟩ := run_carries φ hb a ha
  unfold machineVerdict
  cases hr : run φ with
  | nil => rw [hr] at hf; simp at hf
  | cons _ _ => rfl

/-- **El lector decide las fórmulas satisfacibles bajo `NoZombie`**: si ningún estado que visita el lector a partir
de los estados de la línea final es un zombi, el lector dice SAT. -/
theorem readerVerdict_of_sat_noZombie (φ : Cnf) (hb : Bounded φ) (hs : Satisfiable φ)
    (hnz : ∀ kv ∈ run φ, ∀ h, Visited kv.2 h → NoZombie h) : readerVerdict φ = true := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨g, hf, hc, hok⟩ := run_carries φ hb a ha
  have hmem := List.mem_of_find?_eq_some hf
  unfold readerVerdict
  refine List.any_eq_true.mpr ⟨_, hmem, ?_⟩
  exact readG_isSome_of_noZombie g (isValid_of_carried (carried_review (carried_dirty hc _))) hok.docs
    (hnz _ hmem)

end Machine

end AbsSatBingo.Model
