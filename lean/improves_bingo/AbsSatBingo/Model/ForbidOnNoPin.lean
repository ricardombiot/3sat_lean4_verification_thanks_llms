-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnNoPin.lean
import AbsSatBingo.Model.ForbidOnApart

/-!
# `TopSideAt` sin pins, demostrada

Sin pins, `TopSideAt A B []` dice: una cima viva de la unión revisada está viva en su lado revisado. Aquí se demuestra
en los joins de la máquina, **sin hipótesis nuevas**, por camarillas:

* **`TopCT g`**: toda cima viva de `g` (el estado tal cual, sin revisar) está en una camarilla que esquiva los tríos
  de `g`. Es un invariante de las entradas y de las llegadas:
  - filtro (`topCT_filterAllOn`): si el filtro mata algo, el estado filtrado es el estado fijado y sirve `TopAt`, que
    ya es invariante de la línea; si no mata nada, la camarilla de la entrada cumple el requisito sola;
  - UP (`topCT_upOn`): una cima nueva tiene un padre vivo (`exists_rowParent`, con `DocsAlive`), y la camarilla del
    padre se alarga con ella (`ct_upOn`);
  - join (`topCT_joinOn`): una camarilla de un lado lo es de la unión.
* Una camarilla que esquiva los tríos **sobrevive a cualquier review** (`ct_pinOn`), así que la cima está viva en el
  lado revisado (`topSideAt_nil`).

Con eso, de la hipótesis separada por pins solo queda la mitad con pins: `StarTriAt` para `R ≠ []`
(`spineVerdictOn_iff_of_starTriPins`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Driver Machine MachineOn

-- ============================================================
-- `DocsAlive` en las operaciones `:on`
-- ============================================================

theorem docsAlive_setT {g : GPathB} (h : DocsAlive g) (T : List (PathNodeId × PathNodeId × PathNodeId)) :
    DocsAlive (g.setT T) := h

/-- **El review `:on` válido deja todo documento vivo** si la entrada ya lo cumplía o tenía algo que revisar. -/
theorem docsAlive_reviewOn {g : GPathB} (hv : g.reviewOn.isValid = true) (h : DocsAlive g ∨ g.dirty = true) :
    DocsAlive g.reviewOn := by
  cases hd : g.dirty
  · have e : g.reviewOn = g := by
      unfold reviewOn reviewFuelOn
      simp [hd]
    rw [e]
    rcases h with h | h
    · exact h
    · rw [hd] at h; cases h
  · have hc := reviewOn_exits_clean g hv
    obtain ⟨g₁, hg₁, he, hpd, hvp, _⟩ := reviewFuelOn_exit _ g hd hv hc
    obtain ⟨T', hT⟩ := reviewPassOn_quiet hpd
    have heq : g.reviewOn = g₁.reviewPass.setT T' := he.trans hT
    have hpd' : g₁.reviewPass.dirty = false := by
      have := hpd; rw [hT, dirty_setT'] at this; exact this
    have hvp' : g₁.reviewPass.isValid = true := by
      have := hvp; rw [hT, isValid_setT] at this; exact this
    rw [heq]
    exact docsAlive_setT (docsAlive_reviewPass hg₁ hpd' hvp') T'

theorem docsAlive_filterAllOn {g : GPathB} (hda : DocsAlive g) (reqs : List NodeId)
    (hv : (g.filterAllOn reqs).isValid = true) : DocsAlive (g.filterAllOn reqs) := by
  unfold filterAllOn at hv ⊢
  apply docsAlive_reviewOn hv
  cases hd : (reqs.foldl filterRequire g).dirty
  · obtain ⟨ha, hn⟩ := filterRequires_clean reqs g hd
    exact Or.inl (fun n hnm => by rw [ha]; rw [hn] at hnm; exact hda n hnm)
  · exact Or.inr rfl

theorem docsAlive_upOn {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool} (hda : DocsAlive g)
    (hvg : g.isValid = true) (hv : (g.upOn d title forb).isValid = true) : DocsAlive (g.upOn d title forb) := by
  have e : g.upOn d title forb =
      (((g.addNode d title forb).setT g.trios).upForbidRow (g.newRowIds d forb)).reviewOn := by
    unfold upOn; rw [if_pos hvg]
  rw [e] at hv ⊢
  apply docsAlive_reviewOn hv
  left
  obtain ⟨T', hT⟩ := upForbidRow_eq ((g.addNode d title forb).setT g.trios) (g.newRowIds d forb)
  rw [hT]
  exact docsAlive_setT (docsAlive_setT (docsAlive_addNode (title := title) (forb := forb) hda) g.trios) T'

theorem docsAlive_joinOn {A B : GPathB} (hA : DocsAlive A) (hB : DocsAlive B) : DocsAlive (joinOn A B) := by
  obtain ⟨T', hT⟩ := joinOn_eq A B
  rw [hT]
  exact docsAlive_setT (docsAlive_join hA hB) T'

-- ============================================================
-- Toda cima viva del estado sin revisar está en una camarilla que esquiva sus tríos
-- ============================================================

/-- **`TopCT`**: toda cima viva de `g` está en una camarilla de `g` que esquiva sus tríos. -/
def TopCT (g : GPathB) : Prop :=
  ∀ t ∈ g.alive, t.id.step = g.current_step - 1 → ∃ D, CT g D ∧ D (g.current_step - 1) = t

/-- Un `filterRequire` que no enciende `dirty` sobre un estado válido no tiene a quién matar: todos los documentos
del paso del requisito son del requisito. -/
theorem filterRequire_noVictims {g : GPathB} {r : NodeId} (hv : g.isValid = true)
    (hd : (g.filterRequire r).dirty = false) : ∀ n ∈ g.line r.step, n.id.id = r := by
  intro n hn
  unfold filterRequire at hd
  rw [if_pos hv] at hd
  dsimp only at hd
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hd
  have := List.filter_eq_nil_iff.mp hd.2 n.id (List.mem_map.mpr ⟨n, hn, rfl⟩)
  simpa using this

/-- **El filtro conserva `TopCT`**, con `TopAt` de la entrada para el caso en que el filtro mata algo. -/
theorem topCT_filterAllOn {E : GPathB} {reqs : List NodeId} (hE : SInvB E) (hvE : E.isValid = true)
    (hlen : reqs.length ≤ 1) (hct : TopCT E) (hT : TopAt E reqs) (hvY : (E.filterAllOn reqs).isValid = true) :
    TopCT (E.filterAllOn reqs) := by
  cases hd : (reqs.foldl filterRequire E).dirty
  · -- el filtro no mata a nadie: la camarilla de la entrada cumple los requisitos
    intro t ht hts
    rw [step_filterAllOn] at hts
    obtain ⟨D, hD, hDt⟩ := hct t ((shrinks_filterAllOn E reqs).1.alive t ht) hts
    refine ⟨D, ct_filterAllOn hD reqs ?_, by rw [step_filterAllOn]; exact hDt⟩
    intro r hr h0 h1
    have hr' : reqs = [r] := by
      match reqs, hlen, hr with
      | [x], _, hr => rw [List.mem_singleton] at hr; rw [hr]
    subst hr'
    have hd' : (E.filterRequire r).dirty = false := hd
    obtain ⟨n, hn, hnid⟩ := hE.docs (D r.step) (hD.1.alive r.step h0 h1)
    have hline : n ∈ E.line r.step := by
      unfold line
      refine List.mem_filter.mpr ⟨hn, ?_⟩
      rw [hnid, hD.1.step r.step h0 h1]
      simp
    have := filterRequire_noVictims hvE hd' n hline
    rw [hnid] at this
    exact this
  · -- el filtro mata algo: el estado filtrado es el fijado
    have e : E.filterAllOn reqs = E.pinOn reqs := by
      unfold filterAllOn pinOn
      congr 1
      generalize reqs.foldl filterRequire E = F at hd
      cases F
      simp_all
    rw [e] at hvY ⊢
    intro t ht hts
    rw [step_pinOn] at hts ⊢
    exact hT hvY t ht hts

/-- **El UP conserva `TopCT`**: la camarilla de un padre vivo de la cima nueva se alarga con ella. -/
theorem topCT_upOn {Y : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool} (hiY : SInvB Y)
    (htb : TB Y) (hda : DocsAlive Y) (hd : d.step = Y.current_step) (hpos : 1 ≤ Y.current_step)
    (hvY : Y.isValid = true) (hct : TopCT Y) : TopCT (Y.upOn d title forb) := by
  intro t ht hts
  have hsub := sub_upOn_addNode (d := d) (title := title) (forb := forb) hvY
  have hcsA : (Y.upOn d title forb).current_step = Y.current_step + 1 := by rw [hsub.step]; rfl
  rw [hcsA] at hts ⊢
  have htnew : t ∈ Y.newRowIds d forb := by
    rcases alive_addNode_cases (title := title) (forb := forb) hiY.docs hiY.below hd (hsub.alive t ht) with
      ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact h
  obtain ⟨q, hq, hqa, hqs⟩ := exists_rowParent (d := d) (forb := forb) hda (by omega) htnew
  obtain ⟨D, hD, hDq⟩ := hct q hqa hqs
  have hS : CT Y (extSel D Y.current_step t) :=
    ct_congr hD (fun k _ h1 => by simp [extSel, show k ≠ Y.current_step by omega])
  have e0 : extSel D Y.current_step t Y.current_step = t := by simp [extSel]
  have e1 : extSel D Y.current_step t (Y.current_step - 1) = D (Y.current_step - 1) := by
    simp [extSel, show Y.current_step - 1 ≠ Y.current_step by omega]
  have e2 : extSel D Y.current_step t 0 = D 0 := by
    simp [extSel, show (0 : Int) ≠ Y.current_step by omega]
  refine ⟨extSel D Y.current_step t, ct_upOn hS htb (by rw [e0]; exact htnew) (fun _ => by rw [e0, e1, hDq]; exact hq)
    (by rw [e0]; exact newRow_step hd htnew) hiY.below (by rw [e2]; exact hD.1.root (by omega)), ?_⟩
  rw [show Y.current_step + 1 - 1 = Y.current_step by omega]
  exact e0

/-- **El join conserva `TopCT`**: una camarilla de un lado lo es de la unión. -/
theorem topCT_joinOn {A B : GPathB} (hA : TopCT A) (hB : TopCT B) (hnsA : NoSelf A) (hnsB : NoSelf B)
    (hcs : A.current_step = B.current_step) : TopCT (joinOn A B) := by
  intro t ht hts
  rw [step_joinOn] at hts ⊢
  obtain ⟨T', hT⟩ := joinOn_eq A B
  rw [hT] at ht
  rcases (alive_join A B t).mp ht with h | h
  · obtain ⟨D, hD, hDt⟩ := hA t h hts
    exact ⟨D, ct_joinOn_left hD hnsB, hDt⟩
  · obtain ⟨D, hD, hDt⟩ := hB t h (by rw [← hcs]; exact hts)
    exact ⟨D, ct_joinOn_right hcs hD hnsA, by rw [hcs]; exact hDt⟩

-- ============================================================
-- En la línea
-- ============================================================

/-- La contabilidad de los estados sin revisar: documentos vivos y cimas en camarillas. -/
def LineRaw (line : Line) : Prop := ∀ kv ∈ line, DocsAlive kv.2 ∧ TopCT kv.2

/-- **La llegada válida de una entrada de la línea conserva `DocsAlive` y `TopCT`.** -/
theorem arrOn_raw {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line) (hr : LineRaw line)
    {kv : NodeId × GPathB} (hkv : kv ∈ line) {d : NodeId} (hs : SendsOn φ kv d) :
    DocsAlive (arrOn φ kv d) ∧ TopCT (arrOn φ kv d) := by
  have hent := h.on kv hkv
  have hok := hent.1
  have hi := h.inv kv hkv
  have hvY : (kv.2.filterAllOn (reqOf φ d)).isValid = true :=
    valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
  have hcsY : (kv.2.filterAllOn (reqOf φ d)).current_step = T := by rw [step_filterAllOn]; exact hok.step
  have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by
    rw [hcsY, sonsOfMap_step φ kv.1 d hs.1, hok.key]; omega
  have hTop : TopAt kv.2 (reqOf φ d) := by
    have := h.top kv hkv _ (PinsFrom.cons hs.1 (PinsFrom.nil d))
    rw [List.append_nil] at this
    exact this
  have hdaY := docsAlive_filterAllOn (hr kv hkv).1 (reqOf φ d) hvY
  have hctY := topCT_filterAllOn hi hok.valid (reqOf_length_le_one φ d) (hr kv hkv).2 hTop hvY
  exact ⟨docsAlive_upOn hdaY hvY hs.2,
    topCT_upOn (sInvB_filterAllOn hi _) (tb_filterAllOn hent.2.2 _) hdaY hdY (by rw [hcsY]; exact hT) hvY hctY⟩

theorem lineRaw_advance {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (hr : LineRaw line) : LineRaw (advanceM .on φ line) := by
  intro E hE
  rcases entry_shapeOn (line_cases h.nodup h.keys) h.nodup hE with ⟨kv, hkv, hs, he⟩ |
    ⟨a, ha, b, hb, _, hsa, hsb, he⟩
  · rw [he]; exact arrOn_raw hT h hr hkv hs
  · obtain ⟨ea, _⟩ := arrTop_facts hT h ha hsa
    obtain ⟨eb, _⟩ := arrTop_facts hT h hb hsb
    have hjoin : doJoinOn (arrOn φ a E.1) (arrOn φ b E.1) = joinOn (arrOn φ a E.1) (arrOn φ b E.1) := by
      unfold doJoinOn okJoin
      rw [if_pos (by simp [ea.1.step, eb.1.step, ea.1.mp, eb.1.mp, ea.1.valid, eb.1.valid])]
    obtain ⟨da, ca⟩ := arrOn_raw hT h hr ha hsa
    obtain ⟨db, cb⟩ := arrOn_raw hT h hr hb hsb
    rw [he, hjoin]
    exact ⟨docsAlive_joinOn da db, topCT_joinOn ca cb ea.2.1 eb.2.1 (ea.1.step.trans eb.1.step.symm)⟩

theorem lineRaw_init (φ : Cnf) : LineRaw (initM .on φ) := by
  obtain ⟨hl, g, hf, hct⟩ := initOn_inv φ (fun _ => false)
  rw [initM_eq] at hf
  let d : NodeId := ⟨0, 0⟩
  have hg : g = initSeedOn d "" := by
    have := List.mem_of_find?_eq_some hf
    rw [List.mem_singleton] at this
    exact (Prod.mk.inj this).2
  subst hg
  rw [initM_eq]; intro kv hkv; rw [List.mem_singleton] at hkv; subst hkv
  have hmem : (d, initSeedOn d "") ∈ initM .on φ := by rw [initM_eq]; exact List.mem_singleton_self _
  have hstep : (initSeedOn d "").current_step = 1 := (hl _ hmem).1.step
  have hsub : Sub (initSeedOn d "") (GPathB.empty.addNode d "" (fun _ => false)) :=
    sub_upOn_addNode (g := GPathB.empty) (by rfl)
  have huniq : ∀ q ∈ (initSeedOn d "").alive, q = { id := ⟨0, 0⟩, parent_id := none, gparent_id := none } := by
    intro q hq
    have := hsub.alive q hq
    rw [seedRow_alive] at this
    exact List.mem_singleton.mp this
  constructor
  · exact docsAlive_upOn (g := GPathB.empty) (d := d) (title := "") (forb := fun _ => false)
      (fun n hn => absurd hn List.not_mem_nil) (by rfl) (hl _ hmem).1.valid
  · intro t ht _
    refine ⟨pidOfAssign φ (fun _ => false), hct, ?_⟩
    show pidOfAssign φ (fun _ => false) ((initSeedOn d "").current_step - 1) = t
    rw [hstep]
    exact (huniq _ (hct.1.alive 0 (Int.le_refl 0) (by rw [hstep]; omega))).trans (huniq t ht).symm

-- ============================================================
-- `TopSideAt` sin pins
-- ============================================================

/-- **`TopSideAt` sin pins**: una cima viva de la unión revisada es una cima viva de un lado, está en una camarilla de
ese lado que esquiva sus tríos, y esa camarilla sobrevive al review del lado. -/
theorem topSideAt_nil {A B : GPathB} (hA : TopCT A) (hB : TopCT B) (hcs : A.current_step = B.current_step)
    (hc1 : 1 ≤ A.current_step) : TopSideAt A B [] := by
  intro _ t ht hts
  have htJ := (sub_pinOn (joinOn A B) []).alive t ht
  obtain ⟨T', hT⟩ := joinOn_eq A B
  rw [hT] at htJ
  have pins : ∀ {g : GPathB} {D : Int → PathNodeId}, ∀ r ∈ ([] : List NodeId), Agrees g.current_step D r :=
    fun r hr => absurd hr List.not_mem_nil
  rcases (alive_join A B t).mp htJ with h | h
  · obtain ⟨D, hD, hDt⟩ := hA t h hts
    have hP := ct_pinOn hD [] pins
    refine Or.inl ⟨isValid_of_carried hP.1, ?_⟩
    have := hP.1.alive (A.current_step - 1) (by omega) (by rw [step_pinOn]; omega)
    rw [hDt] at this
    exact this
  · obtain ⟨D, hD, hDt⟩ := hB t h (by rw [← hcs]; exact hts)
    have hP := ct_pinOn hD [] pins
    refine Or.inr ⟨isValid_of_carried hP.1, ?_⟩
    have := hP.1.alive (B.current_step - 1) (by omega) (by rw [step_pinOn]; omega)
    rw [hDt] at this
    exact this

/-- **`TopSideAt` sin pins en los joins de la máquina**, sin hipótesis. -/
theorem topSideAt_nil_line {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (hr : LineRaw line) {a b : NodeId × GPathB} (ha : a ∈ line) (hb : b ∈ line) {d : NodeId}
    (hsa : SendsOn φ a d) (hsb : SendsOn φ b d) : TopSideAt (arrOn φ a d) (arrOn φ b d) [] := by
  obtain ⟨ea, _⟩ := arrTop_facts hT h ha hsa
  obtain ⟨eb, _⟩ := arrTop_facts hT h hb hsb
  exact topSideAt_nil (arrOn_raw hT h hr ha hsa).2 (arrOn_raw hT h hr hb hsb).2 (ea.1.step.trans eb.1.step.symm)
    (by rw [ea.1.step]; omega)

-- ============================================================
-- El veredicto con solo la mitad con pins
-- ============================================================

/-- **`StarTriAt` con pins**, en los joins de una línea: para cada lista de pins no vacía de `PinsFrom`. -/
def HStarTriPinsOn (φ : Cnf) (line : Line) : Prop :=
  ∀ a ∈ line, ∀ b ∈ line, a.1 ≠ b.1 → ∀ d, SendsOn φ a d → SendsOn φ b d → ∀ R, PinsFrom φ d R → R ≠ [] →
    StarTriAt (arrOn φ a d) (joinOn (arrOn φ a d) (arrOn φ b d)) R ∧
    StarTriAt (arrOn φ b d) (joinOn (arrOn φ a d) (arrOn φ b d)) R

theorem hStarPinOn_of_pins {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (hr : LineRaw line) (hp : HStarTriPinsOn φ line) : HStarPinOn φ line := by
  intro a ha b hb hab d hsa hsb R hR
  exact ⟨fun _ => topSideAt_nil_line hT h hr ha hb hsa hsb, fun hne => hp a ha b hb hab d hsa hsb R hR hne⟩

/-- **La hipótesis**: `StarTriAt` con pins en cada línea de la máquina `:on`. -/
def HypsStarTriPinsOn (φ : Cnf) : Prop := ∀ n : Nat, HStarTriPinsOn φ (stepsM .on φ n (initM .on φ))

/-- La inducción de línea con la contabilidad de los estados sin revisar. -/
theorem lInvRaw_steps {φ : Cnf} (H : HypsStarTriPinsOn φ) :
    ∀ n : Nat, LInvTop φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) ∧ LineBk (stepsM .on φ n (initM .on φ)) ∧
      LineRaw (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero => exact ⟨lInvTop_init φ, lineBk_init φ, lineRaw_init φ⟩
  | succ n ih =>
    obtain ⟨hl, hbk, hr⟩ := ih
    have hT : (1 : Int) ≤ (n : Int) + 1 := by omega
    have hl' := lInvTop_advance hT hl (hTopOn_of_starPin hT hl hbk (hStarPinOn_of_pins hT hl hr (H n)))
    rw [stepsM_succ]
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact ⟨hl', lineBk_advance hT hl hbk, lineRaw_advance hT hl hr⟩

theorem hypsTopOn_of_starTriPins {φ : Cnf} (H : HypsStarTriPinsOn φ) : HypsTopOn φ := fun n =>
  hTopOn_of_starPin (by omega) (lInvRaw_steps H n).1 (lInvRaw_steps H n).2.1
    (hStarPinOn_of_pins (by omega) (lInvRaw_steps H n).1 (lInvRaw_steps H n).2.2 (H n))

end GPathB

namespace MachineOn

open GPathB Driver

/-- **El veredicto con solo la mitad con pins**: la espina `:on` decide la satisfacibilidad si, en los joins de la
máquina y para cada lista de pins **no vacía**, una base viva en la unión fijada bajo una cima con sus tres caras vivas
no está en los tríos del lado fijado (`StarTriAt`). El caso sin pins está demostrado (`topSideAt_nil_line`). -/
theorem spineVerdictOn_iff_of_starTriPins {φ : Cnf} (hbd : Bounded φ) (H : HypsStarTriPinsOn φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_topOn hbd (hypsTopOn_of_starTriPins H)

end MachineOn

end AbsSatBingo.Model
