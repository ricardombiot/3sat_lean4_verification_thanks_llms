-- lean/improves_bingo/AbsSatBingo/Tagged/Machine.lean
import AbsSatBingo.Tagged.Keeps

/-!
# La máquina con etiquetas lleva la camarilla de toda solución (fase T2 de `docs/plans/lean_row_tags.md`)

Espejo de `Model/Machine.lean` para `DriverT`. **`run_carriesT`**: si `a` satisface `φ`, la línea final de la máquina
con etiquetas tiene, en la clave de `a`, un estado que lleva la camarilla de `a` **con sus claves en todas las filas**
(`TagCarried`). En particular, la máquina con etiquetas dice SAT (`machineVerdictT_of_sat`): **la regla de la etiqueta
no pierde soluciones**.

La contabilidad de un estado de la línea es la de siempre (`StateOk`, sobre la componente `GPathB`) más que las filas
de claves marcadas son las de los pasos por debajo de la cima (`krows = T - 1`): es lo que hace que la marca de la
llegada caiga en la fila de la cima del remitente.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace MachineT

open GPathB TGPath DriverT Machine

-- ============================================================
-- La regla y el review etiquetado solo borran
-- ============================================================

theorem shrinks_filterEdges (g : GPathB) (p : PathNodeId × PathNodeId → Bool) :
    Shrinks { g with edges := g.edges.filter p } g := by
  refine ⟨⟨rfl, rfl, fun _ h => h, ?_, fun n hn => ⟨n, hn, rfl, fun _ h => h, fun _ h => h⟩⟩, ?_⟩
  · intro x w h
    rw [adj_iff] at h ⊢
    rcases h with h | ⟨e, he, hj⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, (List.mem_filter.mp he).1, hj⟩
  · have := List.length_filter_le p g.edges
    show g.alive.length + (g.edges.filter p).length + (g.nodes.map PNodeB.weight).sum ≤
      g.alive.length + g.edges.length + (g.nodes.map PNodeB.weight).sum
    omega

theorem shrinks_tagCut (g : GPathB) (T : List TagE) (krows : Int) : Shrinks (tagCut g T krows) g := by
  unfold tagCut
  exact (shrinks_filterEdges _ _).trans (shrinks_foldl _ shrinks_killVertex _ _)

theorem aliveDocs_foldl_killVertex (l : List PathNodeId) : ∀ g : GPathB, AliveDocs g → AliveDocs (l.foldl killVertex g) := by
  induction l with
  | nil => intro g h; exact h
  | cons a as ih => intro g h; exact ih _ (aliveDocs_killVertex h a)

theorem aliveDocs_tagCut {g : GPathB} (h : AliveDocs g) (T : List TagE) (krows : Int) : AliveDocs (tagCut g T krows) :=
  aliveDocs_foldl_killVertex _ g h

/-- **El review etiquetado solo borra**, no toca las filas marcadas y conserva los documentos de los vivos. -/
theorem reviewTFuel_spec : ∀ (n : Nat) (tg : TGPath),
    Shrinks (reviewTFuel n tg).g tg.g ∧ (reviewTFuel n tg).krows = tg.krows ∧
      (AliveDocs tg.g → AliveDocs (reviewTFuel n tg).g) := by
  intro n
  induction n with
  | zero => intro tg; exact ⟨Shrinks.refl _, rfl, fun h => h⟩
  | succ n ih =>
    intro tg
    have hr := shrinks_review tg.g
    simp only [reviewTFuel]
    split
    · split
      · split
        · refine ⟨(ih _).1.trans ((shrinks_of_dirty true (shrinks_tagCut _ _ _)).trans hr), (ih _).2.1,
            fun hd => (ih _).2.2 ?_⟩
          exact aliveDocs_dirty (aliveDocs_tagCut (aliveDocs_review hd) _ _) true
        · exact ⟨hr, rfl, fun hd => aliveDocs_review hd⟩
      · exact ⟨hr, rfl, fun hd => aliveDocs_review hd⟩
    · exact ⟨Shrinks.refl _, rfl, fun h => h⟩

theorem reviewT_spec (tg : TGPath) :
    Shrinks (reviewT tg).g tg.g ∧ (reviewT tg).krows = tg.krows ∧ (AliveDocs tg.g → AliveDocs (reviewT tg).g) :=
  reviewTFuel_spec _ tg

theorem filterAllT_spec (tg : TGPath) (reqs : List NodeId) :
    Shrinks (tg.filterAllT reqs).g tg.g ∧ (tg.filterAllT reqs).krows = tg.krows ∧
      (AliveDocs tg.g → AliveDocs (tg.filterAllT reqs).g) := by
  obtain ⟨h1, h2, h3⟩ := reviewT_spec { tg with g := reqs.foldl filterRequire tg.g }
  refine ⟨h1.trans (shrinks_foldl _ shrinks_filterRequire _ _), h2, fun hd => h3 ?_⟩
  exact aliveDocs_foldl _ (fun _ a h => aliveDocs_filterRequire h a) _ _ hd

-- ============================================================
-- La contabilidad de un estado de la línea
-- ============================================================

/-- Un estado de la máquina con etiquetas en el paso `T`: el de siempre, con las filas de claves de los pasos por
debajo de la cima. -/
structure StateOkT (T : Int) (key : NodeId) (tg : TGPath) : Prop where
  base  : StateOk T key tg.g
  krows : tg.krows = T - 1

theorem upFilteringT_eq {tg : TGPath} {key : NodeId} (hmp : tg.g.map_parent = some key) (reqs : List NodeId)
    (d : NodeId) (title : String) (forb : PathNodeId → Bool) :
    tg.upFilteringT reqs d title forb = upT ((tg.stamp key).filterAllT reqs) d title forb := by
  unfold upFilteringT
  rw [hmp]

theorem stateOkT_upFilteringT {φ : Cnf} {T : Int} {key d : NodeId} {tg : TGPath} (hg : StateOkT T key tg)
    (hd : d ∈ sonsOfMap φ key) (hv : (tg.upFilteringT (reqOf φ d) d "" (isProhibited φ)).g.isValid = true) :
    StateOkT (T + 1) d (tg.upFilteringT (reqOf φ d) d "" (isProhibited φ)) := by
  rw [upFilteringT_eq hg.base.mp] at hv ⊢
  let tg2 := (tg.stamp key).filterAllT (reqOf φ d)
  obtain ⟨hs, hk2, hd2⟩ := filterAllT_spec (tg.stamp key) (reqOf φ d)
  have hdstep : d.step = T := by rw [sonsOfMap_step φ key d hd, hg.base.key]; omega
  have hstep : tg2.g.current_step = T := (step_of_shrinks hs).trans hg.base.step
  have hkr2 : tg2.krows = T := by rw [hk2]; show tg.krows + 1 = T; rw [hg.krows]; omega
  unfold upT at hv ⊢
  split
  · rename_i hv1
    rw [if_pos hv1] at hv
    obtain ⟨hsr, hkr, hdr⟩ := reviewT_spec (tg2.addNodeT d "" (isProhibited φ))
    refine ⟨⟨?_, ?_, hv, ?_, by omega, ?_⟩, ?_⟩
    · rw [step_of_shrinks hsr]; show tg2.g.current_step + 1 = _; rw [hstep]
    · rw [hsr.1.mp]; rfl
    · refine below_of_shrinks hsr (below_addNode (below_of_shrinks hs hg.base.below) ?_)
      rw [hdstep, hstep]
    · exact hdr (aliveDocs_addNode (hd2 hg.base.docs))
    · rw [hkr]; show tg2.krows = _; rw [hkr2]; omega
  · rename_i hv1
    rw [if_neg hv1] at hv
    exact absurd hv hv1

theorem doJoinT_g (a b : TGPath) : (doJoinT a b).g = doJoin a.g b.g := by
  unfold doJoinT doJoin; split <;> rfl

theorem doJoinT_krows (a b : TGPath) : (doJoinT a b).krows = a.krows := by
  unfold doJoinT; split <;> rfl

theorem stateOkT_doJoinT {T : Int} {key : NodeId} {e g : TGPath} (he : StateOkT T key e) (hg : StateOkT T key g) :
    StateOkT T key (doJoinT e g) :=
  ⟨doJoinT_g e g ▸ stateOk_doJoin he.base hg.base, (doJoinT_krows e g).trans he.krows⟩

-- ============================================================
-- La línea
-- ============================================================

def LineOkT (T : Int) (line : LineT) : Prop := ∀ kv ∈ line, StateOkT T kv.1 kv.2

theorem lineOkT_insertT {T : Int} {line : LineT} {key : NodeId} {g : TGPath} (hl : LineOkT T line)
    (hg : StateOkT T key g) : LineOkT T (insertT line key g) := by
  unfold insertT
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    subst hkey
    have he := hl _ (List.mem_of_find?_eq_some hfind)
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact stateOkT_doJoinT he hg
    · exact hl kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton] at h; subst h; exact hg

/-- El primer estado con la clave `key` lleva `S` con sus claves. -/
def HasT (S : Int → PathNodeId) (key : NodeId) (line : LineT) : Prop :=
  ∃ tg, line.find? (fun kv => kv.1 == key) = some (key, tg) ∧ TagCarried tg S

theorem find?_map_iteT (key key' : NodeId) (v : TGPath) (hne : key ≠ key') :
    ∀ line : LineT, Option.map (fun kv => if (kv.1 == key) = true then (key, v) else kv)
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

theorem find?_insertT_ne (line : LineT) (key key' : NodeId) (g : TGPath) (hne : key ≠ key') :
    (insertT line key g).find? (fun kv => kv.1 == key') = line.find? (fun kv => kv.1 == key') := by
  unfold insertT
  split
  · rw [List.find?_map]
    exact find?_map_iteT key key' _ hne line
  · rw [List.find?_append]
    cases hf : line.find? (fun kv => kv.1 == key') with
    | some _ => rfl
    | none =>
      simp only [Option.none_or, List.find?_cons, List.find?_nil]
      have : ((key, g).1 == key') = false := beq_false_of_ne hne
      rw [this]

theorem hasT_insertT {S : Int → PathNodeId} {key key' : NodeId} {line : LineT} {g : TGPath}
    (h : HasT S key' line) : HasT S key' (insertT line key g) := by
  by_cases hk : key = key'
  · subst hk
    obtain ⟨g0, hf, hc⟩ := h
    refine ⟨doJoinT g0 g, ?_, tagCarried_doJoinT_left hc⟩
    unfold insertT
    rw [hf]
    simp only
    rw [List.find?_map]
    have : (List.find? ((fun kv => kv.1 == key) ∘ fun kv => if kv.1 == key then (key, doJoinT g0 g) else kv) line) =
        line.find? (fun kv => kv.1 == key) := by
      congr 1; funext kv; simp only [Function.comp]; split <;> simp_all
    rw [this, hf]
    simp
  · obtain ⟨g0, hf, hc⟩ := h
    exact ⟨g0, by rw [find?_insertT_ne line key key' g hk, hf], hc⟩

theorem hasT_insert_self {S : Int → PathNodeId} {T : Int} {key : NodeId} {line : LineT} {g : TGPath}
    (hl : LineOkT T line) (hg : StateOkT T key g) (hc : TagCarried g S) : HasT S key (insertT line key g) := by
  unfold insertT
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    subst hkey
    have he : StateOkT T key' e := hl _ (List.mem_of_find?_eq_some hfind)
    refine ⟨doJoinT e g, ?_, ?_⟩
    · rw [List.find?_map]
      have : (List.find? ((fun kv => kv.1 == key') ∘ fun kv => if kv.1 == key' then (key', doJoinT e g) else kv) line) =
          line.find? (fun kv => kv.1 == key') := by
        congr 1; funext kv; simp only [Function.comp]; split <;> simp_all
      rw [this, hfind]
      simp
    · refine tagCarried_doJoinT_right ?_ (he.krows.trans hg.krows.symm) hc
      unfold okJoin
      simp [he.base.step, hg.base.step, he.base.mp, hg.base.mp, he.base.valid, hg.base.valid]
  · rename_i hnone
    refine ⟨g, ?_, hc⟩
    rw [List.find?_append, hnone]
    simp

-- ============================================================
-- Un paso de la máquina
-- ============================================================

theorem lineOkT_sendToT {φ : Cnf} {T : Int} {kv : NodeId × TGPath} (hkv : StateOkT T kv.1 kv.2) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) {next : LineT} (hn : LineOkT (T + 1) next) :
    LineOkT (T + 1) (sendToT φ kv.2 next d) := by
  unfold sendToT
  dsimp only
  split
  · exact lineOkT_insertT hn (stateOkT_upFilteringT hkv hd (by assumption))
  · exact hn

theorem lineOkT_sendAllT {φ : Cnf} {T : Int} {kv : NodeId × TGPath} (hkv : StateOkT T kv.1 kv.2) {next : LineT}
    (hn : LineOkT (T + 1) next) : LineOkT (T + 1) (sendAllT φ kv next) :=
  foldl_pres _ (LineOkT (T + 1)) _ (fun _ d hd hx => lineOkT_sendToT hkv d hd hx) _ hn

theorem lineOkT_advanceT {φ : Cnf} {T : Int} {line : LineT} (hl : LineOkT T line) :
    LineOkT (T + 1) (advanceT φ line) :=
  foldl_pres _ (LineOkT (T + 1)) _ (fun _ kv hkv hx => lineOkT_sendAllT (hl kv hkv) hx) _
    (fun _ h => absurd h List.not_mem_nil)

theorem hasT_sendToT {φ : Cnf} {S : Int → PathNodeId} {key : NodeId} {g : TGPath} {next : LineT} {d : NodeId}
    (h : HasT S key next) : HasT S key (sendToT φ g next d) := by
  unfold sendToT; dsimp only; split
  · exact hasT_insertT h
  · exact h

/-- **El paso**: la rama de `a` sigue viva, con sus claves, en la línea siguiente. -/
theorem advance_hasT (φ : Cnf) (hb : Bounded φ) (a : Assign) (hsat : Sat a φ) (t : Int) (ht0 : 0 ≤ t)
    (ht : t + 1 < stepCount φ) (line : LineT) (hl : LineOkT (t + 1) line)
    (hh : HasT (pidOfAssign φ a) (selOfAssign φ a t) line) :
    HasT (pidOfAssign φ a) (selOfAssign φ a (t + 1)) (advanceT φ line) := by
  obtain ⟨g0, hf, hc⟩ := hh
  have hmem := List.mem_of_find?_eq_some hf
  have hok : StateOkT (t + 1) (selOfAssign φ a t) g0 := hl _ hmem
  let S := pidOfAssign φ a
  let key := selOfAssign φ a t
  let d := selOfAssign φ a (t + 1)
  have hd : d ∈ sonsOfMap φ key := selOfAssign_son φ a t ht0 ht
  have hkstep : key.step = t := selOfAssign_step φ a t
  -- la marca de la llegada
  have hc0 : TagCarried (g0.stamp key) S := by
    refine tagCarried_stamp hc (by rw [hkstep, hok.krows]; omega) ?_
    rw [hkstep]; rfl
  -- el filtro
  let g1 := (g0.stamp key).filterAllT (reqOf φ d)
  obtain ⟨hs1, hk1, _⟩ := filterAllT_spec (g0.stamp key) (reqOf φ d)
  have hstep1 : g1.g.current_step = t + 1 := (step_of_shrinks hs1).trans hok.base.step
  have hkr1 : g1.krows = t + 1 := by rw [hk1]; show g0.krows + 1 = _; rw [hok.krows]; omega
  have hc1 : TagCarried g1 S := by
    refine tagCarried_filterAllT hc0 _ ?_
    intro r hr _ _
    exact reqSat_selOfAssign φ hb a (t + 1) r hr
  have hnp : S t ∈ g1.g.newParents := by
    obtain ⟨n, hn, _, _⟩ := hc1.carried.node t ht0 (by omega)
    have hid := node?_id hn
    unfold newParents
    rw [if_pos (by omega)]
    refine List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨node?_mem hn, ?_⟩, hid⟩
    rw [hid, hstep1]; simp [S, pid_step]
  have hshift : shiftPid (S t) d = S (t + 1) := by
    have := shift_pid φ a (t + 1) (by omega)
    simpa using this
  -- la fila nueva y su review
  have hc2 : TagCarried (upT g1 d "" (isProhibited φ)) S := by
    unfold upT
    rw [if_pos (isValid_of_carried hc1.carried)]
    apply tagCarried_reviewT
    apply tagCarried_addNodeT hc1
    · rw [hstep1]
      refine List.mem_filter.mpr ⟨?_, by simp [S, pidOfAssign_not_prohibited φ a hsat]⟩
      unfold shiftRowIds
      rw [if_pos (by omega)]
      exact (mem_dedupPids _ _).mpr (List.mem_map.mpr ⟨S t, hnp, hshift⟩)
    · intro _
      rw [hstep1, show t + 1 - 1 = t by omega]
      exact List.mem_filter.mpr ⟨hnp, by simp [hshift]⟩
    · rw [hstep1]; exact pid_step φ a _
    · rw [hstep1]; exact fun n hn => hstep1 ▸ below_of_shrinks hs1 hok.base.below n hn
    · exact pid_root φ a
    · exact Int.le_of_eq (hkr1.trans hstep1.symm)
  have hup : g0.upFilteringT (reqOf φ d) d "" (isProhibited φ) = upT g1 d "" (isProhibited φ) :=
    upFilteringT_eq hok.base.mp _ _ _ _
  have hvalid : (g0.upFilteringT (reqOf φ d) d "" (isProhibited φ)).g.isValid = true := by
    rw [hup]; exact isValid_of_carried hc2.carried
  have hok2 : StateOkT (t + 1 + 1) d (g0.upFilteringT (reqOf φ d) d "" (isProhibited φ)) :=
    stateOkT_upFilteringT hok hd hvalid
  unfold advanceT
  refine foldl_establish _ (fun next => HasT S d next) (LineOkT (t + 1 + 1)) line
    (fun _ kv hkv hx => lineOkT_sendAllT (hl kv hkv) hx)
    (fun _ kv _ _ hx => by
      unfold sendAllT
      exact foldl_pres _ (fun next => HasT S d next) _ (fun y d' _ hy => hasT_sendToT hy) _ hx)
    (selOfAssign φ a t, g0) ?_ hmem [] (fun _ h => absurd h List.not_mem_nil)
  intro x hx
  unfold sendAllT
  refine foldl_establish _ (fun next => HasT S d next) (LineOkT (t + 1 + 1)) _
    (fun y d' hd' hy => lineOkT_sendToT hok d' hd' hy)
    (fun y d' _ _ hy => hasT_sendToT hy) d ?_ hd x hx
  intro y hy
  unfold sendToT
  dsimp only
  rw [if_pos hvalid]
  exact hasT_insert_self hy hok2 (by rw [hup]; exact hc2)

-- ============================================================
-- La línea inicial y la inducción
-- ============================================================

theorem initT_eq (φ : Cnf) : initT φ = [(⟨0, 0⟩, initSeedT ⟨0, 0⟩ "")] := by
  unfold initT
  have : mapNodes φ 0 = [⟨0, 0⟩] := by
    unfold mapNodes
    have := stepCount_pos φ
    simp only [show ¬ (0 : Int) < 0 by omega, if_false, show ¬ stepCount φ ≤ 0 by omega, if_true]
  rw [this]
  rfl

theorem init_invT (φ : Cnf) (a : Assign) :
    LineOkT 1 (initT φ) ∧ HasT (pidOfAssign φ a) (selOfAssign φ a 0) (initT φ) := by
  let S := pidOfAssign φ a
  let d : NodeId := ⟨0, 0⟩
  let e : TGPath := { g := GPathB.empty, tags := [], krows := 0 }
  have he : TagCarried e S :=
    ⟨carried_empty S, fun ℓ _ h1 => absurd h1 (by show ¬ ℓ < 0; omega)⟩
  have hc : TagCarried (initSeedT d "") S := by
    unfold initSeedT upT
    rw [if_pos (show GPathB.empty.isValid = true by rfl)]
    apply tagCarried_reviewT
    apply tagCarried_addNodeT he
    · show S 0 ∈ (GPathB.empty.shiftRowIds d).filter _
      refine List.mem_filter.mpr ⟨?_, rfl⟩
      unfold shiftRowIds
      rw [if_neg (by show ¬ (0 : Int) < 0; omega)]
      simp [S, pidOfAssign, sel_zero, d]
    · intro h; exact absurd h (by show ¬ (0 : Int) < 0; omega)
    · exact pid_step φ a 0
    · intro n hn; exact absurd hn List.not_mem_nil
    · exact pid_root φ a
    · show (0 : Int) ≤ 0; omega
  have hok : StateOkT 1 d (initSeedT d "") := by
    obtain ⟨hsr, hkr, hdr⟩ := reviewT_spec (e.addNodeT d "" (fun _ => false))
    have hup : initSeedT d "" = reviewT (e.addNodeT d "" (fun _ => false)) := by
      unfold initSeedT upT
      rw [if_pos (show GPathB.empty.isValid = true by rfl)]
    refine ⟨⟨?_, ?_, isValid_of_carried hc.carried, ?_, rfl, ?_⟩, ?_⟩
    · rw [hup, step_of_shrinks hsr]; rfl
    · rw [hup, hsr.1.mp]; rfl
    · rw [hup]
      exact below_of_shrinks hsr (below_addNode (fun n hn => absurd hn List.not_mem_nil) rfl)
    · rw [hup]
      exact hdr (aliveDocs_addNode (fun q hq => absurd hq List.not_mem_nil))
    · rw [hup, hkr]; rfl
  rw [initT_eq]
  refine ⟨?_, initSeedT d "", ?_, hc⟩
  · intro kv hkv
    rw [List.mem_singleton] at hkv; subst hkv; exact hok
  · rw [sel_zero]; simp [d]

theorem steps_invT (φ : Cnf) (hb : Bounded φ) (a : Assign) (hsat : Sat a φ) :
    ∀ (n : Nat) (t : Int) (line : LineT), 0 ≤ t → t + n < stepCount φ →
      LineOkT (t + 1) line → HasT (pidOfAssign φ a) (selOfAssign φ a t) line →
      LineOkT (t + n + 1) (stepsT φ n line) ∧ HasT (pidOfAssign φ a) (selOfAssign φ a (t + n)) (stepsT φ n line) := by
  intro n
  induction n with
  | zero =>
    intro t line _ _ hl hh
    have h0 : t + ((0 : Nat) : Int) = t := by omega
    simp only [stepsT]
    rw [h0]
    exact ⟨hl, hh⟩
  | succ n ih =>
    intro t line h0 ht hl hh
    simp only [stepsT]
    have h1 := lineOkT_advanceT (φ := φ) hl
    have h2 := advance_hasT φ hb a hsat t h0 (by omega) line hl hh
    have := ih (t + 1) (advanceT φ line) (by omega) (by omega) h1 h2
    rw [show t + 1 + (n : Int) = t + ((n + 1 : Nat) : Int) by push_cast; omega] at this
    exact this

/-- **La máquina con etiquetas lleva la camarilla de toda solución, con sus claves en todas las filas.** -/
theorem run_carriesT (φ : Cnf) (hb : Bounded φ) (a : Assign) (hsat : Sat a φ) :
    ∃ tg, (runT φ).find? (fun kv => kv.1 == selOfAssign φ a (stepCount φ - 1)) =
        some (selOfAssign φ a (stepCount φ - 1), tg) ∧
      TagCarried tg (pidOfAssign φ a) ∧ StateOkT (stepCount φ) (selOfAssign φ a (stepCount φ - 1)) tg := by
  have hpos := stepCount_pos φ
  obtain ⟨hl0, hh0⟩ := init_invT φ a
  have hn : (0 : Int) + ((stepCount φ - 1).toNat : Int) = stepCount φ - 1 := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  obtain ⟨hl, g, hf, hc⟩ := steps_invT φ hb a hsat (stepCount φ - 1).toNat 0 (initT φ) (by omega)
    (by rw [hn]; omega) (by simpa using hl0) hh0
  rw [hn] at hf hl
  refine ⟨g, hf, hc, ?_⟩
  have := hl _ (List.mem_of_find?_eq_some hf)
  rw [show stepCount φ - 1 + 1 = stepCount φ by omega] at this
  exact this

/-- **La regla de la etiqueta no pierde soluciones**: con una fórmula satisfacible, la máquina con etiquetas dice SAT. -/
theorem machineVerdictT_of_sat (φ : Cnf) (hb : Bounded φ) (hs : Satisfiable φ) : machineVerdictT φ = true := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨g, hf, _, _⟩ := run_carriesT φ hb a ha
  unfold machineVerdictT
  cases hr : runT φ with
  | nil => rw [hr] at hf; simp at hf
  | cons _ _ => rfl

end MachineT

end AbsSatBingo.Model
