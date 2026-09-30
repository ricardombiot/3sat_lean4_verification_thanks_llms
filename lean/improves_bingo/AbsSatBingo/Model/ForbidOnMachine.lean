-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnMachine.lean
import AbsSatBingo.Model.ForbidOnSound
import AbsSatBingo.Model.Machine

/-!
# La máquina `:on` lleva la rama de toda solución (`docs/plans/lean_forbid_on.md`, F3)

Espejo de `run_carries` (`Machine.lean`) para `FORBID = :on`. Cada entrada de la línea cumple `EntOn`: `StateOk`,
sin aristas de un nodo a sí mismo, y los tríos y vivos por debajo del paso (`TB`). La entrada de la clave de la
solución cumple además `CT`: lleva la rama y la rama esquiva sus tríos. Así la regla no corta la rama, y la máquina
`:on` dice SAT en toda fórmula satisfacible (`machineVerdictOn_of_sat`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

variable {S : Int → PathNodeId}

-- ============================================================
-- Paso y mapa por el review `:on`
-- ============================================================

theorem revPrims_mp (c : Option NodeId) : RevPrims (fun h : GPathB => h.map_parent = c) :=
  ⟨fun _ _ h => h, fun _ _ _ h => h, fun _ _ h => h, fun _ _ h => h,
    fun g h => (shrinks_pruneLinks g).1.mp.trans h⟩

theorem mp_reviewOn (g : GPathB) : g.reviewOn.map_parent = g.map_parent :=
  revPrims_reviewOn (revPrims_mp g.map_parent) (fun _ _ h => h) g rfl

-- ============================================================
-- El filtro `:on`
-- ============================================================

theorem foldl_filterRequire_pres {P : GPathB → Prop} (hp : RevPrims P) :
    ∀ (l : List NodeId) (g : GPathB), P g → P (l.foldl filterRequire g) := by
  intro l
  induction l with
  | nil => intro g h; exact h
  | cons r rs ih => intro g h; rw [List.foldl_cons]; exact ih _ (Final.revPrims_filterRequire hp g r h)

theorem shrinks_foldl_filterRequire : ∀ (l : List NodeId) (g : GPathB), Shrinks (l.foldl filterRequire g) g := by
  intro l
  induction l with
  | nil => intro g; exact Shrinks.refl g
  | cons r rs ih => intro g; rw [List.foldl_cons]; exact (ih _).trans (shrinks_filterRequire g r)

theorem trios_foldl_filterRequire : ∀ (l : List NodeId) (g : GPathB), (l.foldl filterRequire g).trios = g.trios := by
  intro l
  induction l with
  | nil => intro g; rfl
  | cons r rs ih =>
    intro g
    rw [List.foldl_cons, ih]
    exact trios_of_comm (f := fun x => x.filterRequire r) (fun x T => filterRequire_setT T x r) g

theorem tb_filterAllOn {g : GPathB} (h : TB g) (reqs : List NodeId) : TB (g.filterAllOn reqs) := by
  unfold filterAllOn
  apply tb_reviewOn
  exact tb_of_shrink h (shrinks_foldl_filterRequire reqs g) (trios_foldl_filterRequire reqs g)
    (foldl_filterRequire_pres revPrims_aliveBelow reqs g h.2.1) (foldl_filterRequire_pres revPrims_edgesAlive reqs g h.2.2)

theorem noSelf_filterAllOn {g : GPathB} (h : NoSelf g) (reqs : List NodeId) : NoSelf (g.filterAllOn reqs) :=
  revPrims_reviewOn revPrims_noSelf trioBlind_noSelf _ (foldl_filterRequire_pres revPrims_noSelf reqs g h)

theorem step_filterAllOn (g : GPathB) (reqs : List NodeId) : (g.filterAllOn reqs).current_step = g.current_step := by
  unfold filterAllOn
  rw [step_reviewOn]; exact (shrinks_foldl_filterRequire reqs g).1.step

theorem mp_filterAllOn (g : GPathB) (reqs : List NodeId) : (g.filterAllOn reqs).map_parent = g.map_parent := by
  unfold filterAllOn
  rw [mp_reviewOn]; exact (shrinks_foldl_filterRequire reqs g).1.mp

theorem below_filterAllOn {g : GPathB} (h : Machine.Below g) (reqs : List NodeId) : Machine.Below (g.filterAllOn reqs) :=
  revPrims_reviewOn revPrims_below trioBlind_below _ (foldl_filterRequire_pres revPrims_below reqs g h)

theorem docs_filterAllOn {g : GPathB} (h : AliveDocs g) (reqs : List NodeId) : AliveDocs (g.filterAllOn reqs) :=
  aliveDocs_reviewOn (aliveDocs_foldl _ (fun _ a h => aliveDocs_filterRequire h a) _ _ h)

-- ============================================================
-- El UP `:on`
-- ============================================================

section Up

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- La fila con los tríos de antes y los de `up_forbid!`. -/
theorem upForbidRow_eq (x : GPathB) (ids : List PathNodeId) : ∃ T', x.upForbidRow ids = x.setT T' := by
  unfold upForbidRow
  exact addTrios_eq x _ _

theorem upOn_eq (hv : g.isValid = true) : ∃ T', g.upOn d title forb = ((g.addNode d title forb).setT T').reviewOn := by
  unfold upOn
  rw [if_pos hv]
  obtain ⟨T', hT⟩ := upForbidRow_eq ((g.addNode d title forb).setT g.trios) (g.newRowIds d forb)
  exact ⟨T', by rw [hT]⟩

theorem tb_upOn (h : TB g) (hdS : d.step = g.current_step) : TB (g.upOn d title forb) := by
  unfold upOn
  split
  · apply tb_reviewOn
    let a' := (g.addNode d title forb).setT g.trios
    have hcs : a'.current_step = g.current_step + 1 := rfl
    have hab : AliveBelow a' := by
      intro q hq
      rw [hcs]
      rcases List.mem_append.mp hq with hq | hq
      · have := h.2.1 q hq; omega
      · rw [newRow_id' hq, hdS]; omega
    have ha' : TB a' := by
      refine ⟨?_, hab, edgesAlive_addNode (title := title) h.2.2⟩
      intro t ht
      have := h.1 t ht
      rw [hcs]; omega
    unfold upForbidRow
    apply tb_addTrios ha'
    intro t ht
    obtain ⟨n, hn, ht⟩ := List.mem_flatMap.mp ht
    unfold upForbidTodo at ht
    obtain ⟨wr, hwr, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hw, hr⟩ := mem_pairsOf (List.mem_filter.mp hwr).1
    have hw' := ((idx_mem_nbrs a' n wr.1).mp hw).2.1
    have hr' := ((idx_mem_nbrs a' n wr.2).mp hr).2.1
    refine ⟨?_, hab _ hw', hab _ hr'⟩
    show n.id.step < a'.current_step
    rw [hcs, newRow_id' hn, hdS]; omega
  · exact h

theorem noSelf_upOn (h : NoSelf g) : NoSelf (g.upOn d title forb) := by
  unfold upOn
  split
  · apply revPrims_reviewOn revPrims_noSelf trioBlind_noSelf
    obtain ⟨T', hT⟩ := upForbidRow_eq ((g.addNode d title forb).setT g.trios) (g.newRowIds d forb)
    rw [hT]
    exact noSelf_addNode (title := title) h
  · exact h

end Up

-- ============================================================
-- El join `:on`
-- ============================================================

theorem hasEdge_of_mem {g : GPathB} {e : PathNodeId × PathNodeId} (he : e ∈ g.edges) : g.hasEdge e.1 e.2 = true :=
  List.any_eq_true.mpr ⟨e, he, by simp [joins]⟩

theorem joinOn_eq (g₁ g₂ : GPathB) : ∃ T', joinOn g₁ g₂ = (join g₁ g₂).setT T' := by
  unfold joinOn
  obtain ⟨T', hT⟩ := addTrios_eq ({ join g₁ g₂ with trios := [] } : GPathB) _ (joinForbid g₁ g₂)
  exact ⟨T', by rw [hT]⟩

theorem tb_joinOn {g₁ g₂ : GPathB} (h₁ : TB g₁) (h₂ : TB g₂) (hcs : g₁.current_step = g₂.current_step) :
    TB (joinOn g₁ g₂) := by
  let u : GPathB := { join g₁ g₂ with trios := [] }
  have hab : AliveBelow u := by
    intro q hq
    rcases (alive_join g₁ g₂ q).mp hq with hq | hq
    · exact h₁.2.1 q hq
    · show q.id.step < g₁.current_step; rw [hcs]; exact h₂.2.1 q hq
  have hea : EdgesAlive u := edgesAlive_join h₁.2.2 h₂.2.2
  have hu : TB u := ⟨fun t ht => absurd ht (List.not_mem_nil), hab, hea⟩
  unfold joinOn
  apply tb_addTrios hu
  intro t ht
  unfold joinForbid at ht
  obtain ⟨e, he, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  have hr' := (List.mem_filter.mp hr).1
  -- los extremos de la arista y `r` están vivos en algún lado
  have hbelow : ∀ x, x ∈ g₁.alive ∨ x ∈ g₂.alive → x.id.step < u.current_step := by
    intro x hx
    rcases hx with hx | hx
    · exact h₁.2.1 x hx
    · show x.id.step < g₁.current_step; rw [hcs]; exact h₂.2.1 x hx
  have hre : e.1 ∈ g₁.alive ∨ e.1 ∈ g₂.alive := by
    rcases List.mem_append.mp he with he | he
    · exact Or.inl (alive_of_hasEdge h₁.2.2 (hasEdge_of_mem he)).1
    · exact Or.inr (alive_of_hasEdge h₂.2.2 (hasEdge_of_mem he)).1
  have hre2 : e.2 ∈ g₁.alive ∨ e.2 ∈ g₂.alive := by
    rcases List.mem_append.mp he with he | he
    · exact Or.inl (alive_of_hasEdge h₁.2.2 (hasEdge_of_mem he)).2
    · exact Or.inr (alive_of_hasEdge h₂.2.2 (hasEdge_of_mem he)).2
  have hrr : r ∈ g₁.alive ∨ r ∈ g₂.alive := by
    rcases List.mem_append.mp hr' with h | h
    · exact Or.inl ((idx_mem_nbrs g₁ e.1 r).mp h).2.1
    · exact Or.inr ((idx_mem_nbrs g₂ e.1 r).mp h).2.1
  exact ⟨hbelow _ hre, hbelow _ hre2, hbelow _ hrr⟩

end GPathB

namespace MachineOn

open GPathB Driver Machine

variable {φ : Cnf}

/-- **Una entrada de la línea `:on`**: `StateOk`, sin aristas a sí mismo, tríos y vivos por debajo del paso. -/
def EntOn (T : Int) (key : NodeId) (g : GPathB) : Prop := StateOk T key g ∧ NoSelf g ∧ TB g

def LineOn (T : Int) (line : Line) : Prop := ∀ kv ∈ line, EntOn T kv.1 kv.2

/-- La primera entrada con la clave `key` lleva `S` y `S` esquiva sus tríos. -/
def HasOn (S : Int → PathNodeId) (key : NodeId) (line : Line) : Prop :=
  ∃ g, line.find? (fun kv => kv.1 == key) = some (key, g) ∧ CT g S

theorem stateOk_setT {T : Int} {key : NodeId} {g : GPathB} (h : StateOk T key g)
    (T' : List (PathNodeId × PathNodeId × PathNodeId)) : StateOk T key (g.setT T') :=
  ⟨h.step, h.mp, h.valid, h.below, h.key, h.docs⟩

-- ============================================================
-- El join y el envío `:on`
-- ============================================================

theorem entOn_doJoinOn {T : Int} {key : NodeId} {e g : GPathB} (he : EntOn T key e) (hg : EntOn T key g) :
    EntOn T key (doJoinOn e g) := by
  unfold doJoinOn
  split
  · rename_i hok
    obtain ⟨T', hT⟩ := joinOn_eq e g
    have hj : StateOk T key (join e g) := by
      have := stateOk_doJoin he.1 hg.1; unfold doJoin at this; rw [if_pos hok] at this; exact this
    rw [hT]
    exact ⟨stateOk_setT hj T', noSelf_join he.2.1 hg.2.1,
      by rw [← hT]; exact tb_joinOn he.2.2 hg.2.2 (he.1.step.trans hg.1.step.symm)⟩
  · exact he

theorem entOn_upFilteringOn {T : Int} {key d : NodeId} {g : GPathB} (hg : EntOn T key g)
    (hd : d ∈ sonsOfMap φ key) (hv : (g.upFilteringOn (reqOf φ d) d "" (isProhibited φ)).isValid = true) :
    EntOn (T + 1) d (g.upFilteringOn (reqOf φ d) d "" (isProhibited φ)) := by
  have hdstep : d.step = T := by rw [sonsOfMap_step φ key d hd, hg.1.key]; omega
  let g1 := g.filterAllOn (reqOf φ d)
  have hs1 : g1.current_step = T := (step_filterAllOn g _).trans hg.1.step
  have hns1 : NoSelf g1 := noSelf_filterAllOn hg.2.1 _
  have htb1 : TB g1 := tb_filterAllOn hg.2.2 _
  unfold upFilteringOn at hv ⊢
  refine ⟨?_, noSelf_upOn hns1, tb_upOn htb1 (by rw [hdstep, hs1])⟩
  by_cases hv1 : g1.isValid = true
  · obtain ⟨T', hT⟩ := upOn_eq (d := d) (title := "") (forb := isProhibited φ) hv1
    show StateOk (T + 1) d (g1.upOn d "" (isProhibited φ))
    rw [hT] at hv ⊢
    let a := (g1.addNode d "" (isProhibited φ)).setT T'
    refine ⟨?_, ?_, hv, ?_, by omega, ?_⟩
    · rw [step_reviewOn]; show g1.current_step + 1 = _; rw [hs1]
    · rw [mp_reviewOn]; rfl
    · apply revPrims_reviewOn revPrims_below trioBlind_below
      exact below_addNode (below_filterAllOn hg.1.below _) (by rw [hdstep, hs1])
    · exact aliveDocs_reviewOn (aliveDocs_addNode (docs_filterAllOn hg.1.docs _))
  · exfalso
    unfold upOn at hv
    rw [if_neg hv1] at hv
    exact hv1 hv

-- ============================================================
-- La inserción `:on`
-- ============================================================

theorem lineOn_insertM {T : Int} {line : Line} {key : NodeId} {g : GPathB} (hl : LineOn T line)
    (hg : EntOn T key g) : LineOn T (insertM .on line key g) := by
  unfold insertM
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    subst hkey
    have he := hl _ (List.mem_of_find?_eq_some hfind)
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact entOn_doJoinOn he hg
    · exact hl kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton] at h; subst h; exact hg

theorem find?_insertM_ne (m : Mode) (line : Line) (key key' : NodeId) (g : GPathB) (hne : key ≠ key') :
    (insertM m line key g).find? (fun kv => kv.1 == key') = line.find? (fun kv => kv.1 == key') := by
  unfold insertM
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

theorem hasOn_insert {S : Int → PathNodeId} {T : Int} {key key' : NodeId} {line : Line} {g : GPathB}
    (hg : EntOn T key g) (h : HasOn S key' line) : HasOn S key' (insertM .on line key g) := by
  by_cases hk : key = key'
  · subst hk
    obtain ⟨g0, hf, hc⟩ := h
    refine ⟨doJoinOn g0 g, ?_, ct_doJoinOn_left hc hg.2.1⟩
    unfold insertM
    rw [hf]
    simp only
    rw [List.find?_map]
    have : (List.find? ((fun kv => kv.1 == key) ∘ fun kv => if kv.1 == key then (key, doJoinM .on g0 g) else kv) line) =
        line.find? (fun kv => kv.1 == key) := by
      congr 1; funext kv; simp only [Function.comp]; split <;> simp_all
    rw [this, hf]
    simp [doJoinM]
  · obtain ⟨g0, hf, hc⟩ := h
    exact ⟨g0, by rw [find?_insertM_ne .on line key key' g hk, hf], hc⟩

theorem hasOn_insert_self {S : Int → PathNodeId} {T : Int} {key : NodeId} {line : Line} {g : GPathB}
    (hl : LineOn T line) (hg : EntOn T key g) (hc : CT g S) : HasOn S key (insertM .on line key g) := by
  unfold insertM
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    subst hkey
    have he : EntOn T key' e := hl _ (List.mem_of_find?_eq_some hfind)
    refine ⟨doJoinOn e g, ?_, ?_⟩
    · rw [List.find?_map]
      have : (List.find? ((fun kv => kv.1 == key') ∘ fun kv => if kv.1 == key' then (key', doJoinM .on e g) else kv)
          line) = line.find? (fun kv => kv.1 == key') := by
        congr 1; funext kv; simp only [Function.comp]; split <;> simp_all
      rw [this, hfind]
      simp [doJoinM]
    · apply ct_doJoinOn_right _ hc he.2.1
      unfold okJoin
      simp [he.1.step, hg.1.step, he.1.mp, hg.1.mp, he.1.valid, hg.1.valid]
  · rename_i hnone
    refine ⟨g, ?_, hc⟩
    rw [List.find?_append, hnone]
    simp

-- ============================================================
-- Un paso de la máquina `:on`
-- ============================================================

theorem lineOn_sendTo {T : Int} {kv : NodeId × GPathB} (hkv : EntOn T kv.1 kv.2) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) {next : Line} (hn : LineOn (T + 1) next) :
    LineOn (T + 1) (sendToM .on φ kv.2 next d) := by
  unfold sendToM
  dsimp only
  split
  · exact lineOn_insertM hn (entOn_upFilteringOn hkv hd (by assumption))
  · exact hn

theorem lineOn_sendAll {T : Int} {kv : NodeId × GPathB} (hkv : EntOn T kv.1 kv.2) {next : Line}
    (hn : LineOn (T + 1) next) : LineOn (T + 1) (sendAllM .on φ kv next) :=
  foldl_pres _ (LineOn (T + 1)) _ (fun _ d hd hx => lineOn_sendTo hkv d hd hx) _ hn

theorem lineOn_advance {T : Int} {line : Line} (hl : LineOn T line) : LineOn (T + 1) (advanceM .on φ line) :=
  foldl_pres _ (LineOn (T + 1)) _ (fun _ kv hkv hx => lineOn_sendAll (hl kv hkv) hx) _
    (fun _ h => absurd h List.not_mem_nil)

theorem hasOn_sendTo {S : Int → PathNodeId} {T : Int} {key : NodeId} {kv : NodeId × GPathB}
    (hkv : EntOn T kv.1 kv.2) {next : Line} {d : NodeId} (hd : d ∈ sonsOfMap φ kv.1)
    (h : HasOn S key next) : HasOn S key (sendToM .on φ kv.2 next d) := by
  unfold sendToM; dsimp only; split
  · exact hasOn_insert (entOn_upFilteringOn hkv hd (by assumption)) h
  · exact h

/-- **El paso `:on`**: la rama de `a` sigue viva, y esquivando los tríos, en la línea siguiente. -/
theorem advance_hasOn (hb : Bounded φ) (a : Assign) (hsat : Sat a φ) (t : Int) (ht0 : 0 ≤ t)
    (ht : t + 1 < stepCount φ) (line : Line) (hl : LineOn (t + 1) line)
    (hh : HasOn (pidOfAssign φ a) (selOfAssign φ a t) line) :
    HasOn (pidOfAssign φ a) (selOfAssign φ a (t + 1)) (advanceM .on φ line) := by
  obtain ⟨g0, hf, hct⟩ := hh
  have hmem := List.mem_of_find?_eq_some hf
  have hok : EntOn (t + 1) (selOfAssign φ a t) g0 := hl _ hmem
  let S := pidOfAssign φ a
  let d := selOfAssign φ a (t + 1)
  have hd : d ∈ sonsOfMap φ (selOfAssign φ a t) := selOfAssign_son φ a t ht0 ht
  -- el filtro de requisitos
  let g1 := g0.filterAllOn (reqOf φ d)
  have hstep1 : g1.current_step = t + 1 := (step_filterAllOn g0 _).trans hok.1.step
  have hct1 : CT g1 S := by
    refine ct_filterAllOn hct _ ?_
    intro r hr _ _
    exact reqSat_selOfAssign φ hb a (t + 1) r hr
  have htb1 : TB g1 := tb_filterAllOn hok.2.2 _
  have hnp : S t ∈ g1.newParents := by
    obtain ⟨n, hn, _, _⟩ := hct1.1.node t ht0 (by omega)
    have hid := node?_id hn
    unfold newParents
    rw [if_pos (by omega)]
    refine List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨node?_mem hn, ?_⟩, hid⟩
    rw [hid, hstep1]; simp [S, pid_step]
  have hshift : shiftPid (S t) d = S (t + 1) := by
    have := shift_pid φ a (t + 1) (by omega)
    simpa using this
  -- el UP
  have hct2 : CT (g1.upOn d "" (isProhibited φ)) S := by
    apply ct_upOn hct1 htb1
    · rw [hstep1]
      refine List.mem_filter.mpr ⟨?_, by simp [S, pidOfAssign_not_prohibited φ a hsat]⟩
      unfold shiftRowIds
      rw [if_pos (by omega)]
      exact (mem_dedupPids _ _).mpr (List.mem_map.mpr ⟨S t, hnp, hshift⟩)
    · intro _
      rw [hstep1, show t + 1 - 1 = t by omega]
      exact List.mem_filter.mpr ⟨hnp, by simp [hshift]⟩
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

-- ============================================================
-- La línea inicial y la inducción
-- ============================================================

theorem initM_eq (φ : Cnf) : initM .on φ = [(⟨0, 0⟩, initSeedOn ⟨0, 0⟩ "")] := by
  unfold initM
  have : mapNodes φ 0 = [⟨0, 0⟩] := by
    unfold mapNodes
    have := stepCount_pos φ
    simp only [show ¬ (0 : Int) < 0 by omega, if_false, show ¬ stepCount φ ≤ 0 by omega, if_true]
  rw [this]
  rfl

theorem empty_ct (S : Int → PathNodeId) : CT GPathB.empty S :=
  ⟨carried_empty S, fun _ _ _ _ h1 _ _ _ _ _ => absurd h1 (by show ¬ _ < (0 : Int); omega),
    fun _ he => absurd he List.not_mem_nil⟩

theorem empty_tb : TB GPathB.empty :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun y w h => by unfold Adj adjb isAlive hasEdge at h; simp [GPathB.empty] at h⟩

theorem initOn_inv (φ : Cnf) (a : Assign) :
    LineOn 1 (initM .on φ) ∧ HasOn (pidOfAssign φ a) (selOfAssign φ a 0) (initM .on φ) := by
  let S := pidOfAssign φ a
  let d : NodeId := ⟨0, 0⟩
  have hct : CT (initSeedOn d "") S := by
    unfold initSeedOn
    apply ct_upOn (empty_ct S) empty_tb
    · show S 0 ∈ (GPathB.empty.shiftRowIds d).filter _
      refine List.mem_filter.mpr ⟨?_, rfl⟩
      unfold shiftRowIds
      rw [if_neg (by show ¬ (0 : Int) < 0; omega)]
      simp [S, pidOfAssign, sel_zero, d]
    · intro h; exact absurd h (by show ¬ (0 : Int) < 0; omega)
    · exact pid_step φ a 0
    · intro n hn; exact absurd hn List.not_mem_nil
    · exact pid_root φ a
  have hvalid : (initSeedOn d "").isValid = true := isValid_of_carried hct.1
  have hent : EntOn 1 d (initSeedOn d "") := by
    obtain ⟨T', hT⟩ := upOn_eq (g := GPathB.empty) (d := d) (title := "") (forb := fun _ => false) rfl
    have heq : initSeedOn d "" = ((GPathB.empty.addNode d "" (fun _ => false)).setT T').reviewOn := hT
    refine ⟨?_, noSelf_upOn (fun _ he => absurd he List.not_mem_nil), tb_upOn empty_tb rfl⟩
    rw [heq] at hvalid ⊢
    refine ⟨?_, ?_, hvalid, ?_, rfl, ?_⟩
    · rw [step_reviewOn]; rfl
    · rw [mp_reviewOn]; rfl
    · apply revPrims_reviewOn revPrims_below trioBlind_below
      exact below_addNode (fun n hn => absurd hn List.not_mem_nil) rfl
    · exact aliveDocs_reviewOn (aliveDocs_addNode (fun q hq => absurd hq List.not_mem_nil))
  rw [initM_eq]
  refine ⟨?_, initSeedOn d "", ?_, hct⟩
  · intro kv hkv
    rw [List.mem_singleton] at hkv; subst hkv; exact hent
  · rw [sel_zero]; simp [d]

theorem stepsOn_inv (hb : Bounded φ) (a : Assign) (hsat : Sat a φ) :
    ∀ (n : Nat) (t : Int) (line : Line), 0 ≤ t → t + n < stepCount φ →
      LineOn (t + 1) line → HasOn (pidOfAssign φ a) (selOfAssign φ a t) line →
      LineOn (t + n + 1) (stepsM .on φ n line) ∧
        HasOn (pidOfAssign φ a) (selOfAssign φ a (t + n)) (stepsM .on φ n line) := by
  intro n
  induction n with
  | zero =>
    intro t line _ _ hl hh
    have h0 : t + ((0 : Nat) : Int) = t := by omega
    simp only [stepsM]
    rw [h0]
    exact ⟨hl, hh⟩
  | succ n ih =>
    intro t line h0 ht hl hh
    simp only [stepsM]
    have h1 := lineOn_advance (φ := φ) hl
    have h2 := advance_hasOn hb a hsat t h0 (by omega) line hl hh
    have := ih (t + 1) (advanceM .on φ line) (by omega) (by omega) h1 h2
    rw [show t + 1 + (n : Int) = t + ((n + 1 : Nat) : Int) by push_cast; omega] at this
    exact this

/-- **La máquina `:on` lleva la rama de toda solución**, y la rama esquiva los tríos del estado. -/
theorem run_carriesOn (hb : Bounded φ) (a : Assign) (hsat : Sat a φ) :
    ∃ g, (runM .on φ).find? (fun kv => kv.1 == selOfAssign φ a (stepCount φ - 1)) =
        some (selOfAssign φ a (stepCount φ - 1), g) ∧
      CT g (pidOfAssign φ a) ∧ EntOn (stepCount φ) (selOfAssign φ a (stepCount φ - 1)) g := by
  have hpos := stepCount_pos φ
  obtain ⟨hl0, hh0⟩ := initOn_inv φ a
  have hn : (0 : Int) + ((stepCount φ - 1).toNat : Int) = stepCount φ - 1 := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  obtain ⟨hl, g, hf, hc⟩ := stepsOn_inv hb a hsat (stepCount φ - 1).toNat 0 (initM .on φ) (by omega)
    (by rw [hn]; omega) (by simpa using hl0) hh0
  rw [hn] at hf hl
  refine ⟨g, hf, hc, ?_⟩
  have := hl _ (List.mem_of_find?_eq_some hf)
  rw [show stepCount φ - 1 + 1 = stepCount φ by omega] at this
  exact this

/-- **Completitud de la máquina `:on`**: si `φ` es satisfacible, dice SAT. -/
theorem machineVerdictOn_of_sat (hb : Bounded φ) (hs : Satisfiable φ) : machineVerdictM .on φ = true := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨g, hf, _, _⟩ := run_carriesOn hb a ha
  unfold machineVerdictM
  cases hr : runM .on φ with
  | nil => rw [hr] at hf; simp at hf
  | cons _ _ => rfl

end MachineOn

end AbsSatBingo.Model
