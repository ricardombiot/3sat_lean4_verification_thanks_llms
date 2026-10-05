-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnWinPin.lean
import AbsSatBingo.Model.ForbidOnWinRead

/-!
# El nodo de ventana: un filtro de varios requisitos con un solo review

`ForbidOnWinRead` modela una ventana como tres elecciones seguidas. Aquí va la operación tal cual: fijar el nodo de
ventana `q` (su id lleva los nodos de los pasos `k`, `k - 1` y `k - 2`) es `filterAllOn` con los tres requisitos a la
vez, y **un solo review**.

* `foldl_clean`: si los filtros no matan a nadie, el estado no cambia y toda rama ya cumple los requisitos.
* **`snd3_filterL`**: el filtro de una lista de requisitos conserva `Snd3`, si cada requisito, con los anteriores ya
  cumplidos **en un orden `ord` cualquiera** (no hace falta el del filtro), no deja familias fantasma. La estructura es
  **la misma** para todos los requisitos (el estado fijado y revisado): se aplica `PhantomFree` una vez por requisito,
  y cada vez la familia crece en uno.
* `read_stepL`; **`WinReading`**: cada paso fija un nodo vivo `q` del tercer paso de una cláusula con sus tres ids
  `[abuelo, padre, q]` en un solo `filterAllOn`. `win_sels`: una rama por `q` elige los tres, y están en los tres pasos
  de la cláusula. `winOk_node`: los tres, separadores primero, son una ventana de `ForbidOnWinRead`.
* **`reader_winNode_on`** (con `SepCover`, `SepPinAny`, `OneWin`), **`reader_winNode_of_chainOrd`** (sin hipótesis en
  toda cadena en orden) y `reader_winNode_chain12O`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

open Driver Machine MachineOn

variable {φ : Cnf}

theorem filterRequire_dirty {g : GPathB} (r : NodeId) (h : g.dirty = true) : (g.filterRequire r).dirty = true := by
  unfold filterRequire
  split
  · dsimp only
    cases hv : (((g.line r.step).map (·.id)).filter (fun q => q.id != r)).isEmpty
    · simp
    · rw [List.isEmpty_iff] at hv
      rw [hv]; simp [h]
  · exact h

theorem foldl_dirty {g : GPathB} : ∀ (R : List NodeId), g.dirty = true → (R.foldl filterRequire g).dirty = true := by
  intro R
  induction R generalizing g with
  | nil => intro h; exact h
  | cons r rs ih => intro h; exact ih (filterRequire_dirty r h)

theorem filterRequire_eqClean {g : GPathB} {r : NodeId} (hd : (g.filterRequire r).dirty = false) :
    g.filterRequire r = g ∧ (g.isValid = true → ∀ n ∈ g.line r.step, n.id.id = r) := by
  refine ⟨?_, fun hv => filterRequire_noVictims hv hd⟩
  unfold filterRequire at hd ⊢
  split
  · rename_i hv
    rw [if_pos hv] at hd
    dsimp only at hd ⊢
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hd
    rw [hd.2]
    simp only [List.foldl_nil, List.isEmpty_nil, Bool.not_true, Bool.or_false]
  · rfl

/-- **Si los filtros no matan a nadie**, el estado no cambia y toda línea de requisito ya es el requisito. -/
theorem foldl_clean : ∀ (R : List NodeId) {g : GPathB}, (R.foldl filterRequire g).dirty = false →
    R.foldl filterRequire g = g ∧ (g.isValid = true → ∀ r ∈ R, ∀ n ∈ g.line r.step, n.id.id = r) := by
  intro R
  induction R with
  | nil => intro g _; exact ⟨rfl, fun _ r hr => absurd hr List.not_mem_nil⟩
  | cons r rs ih =>
    intro g hd
    have hd1 : (g.filterRequire r).dirty = false := by
      cases e : (g.filterRequire r).dirty
      · rfl
      · have := foldl_dirty rs e
        simp only [List.foldl_cons] at hd
        rw [hd] at this; cases this
    obtain ⟨e, hnv⟩ := filterRequire_eqClean hd1
    simp only [List.foldl_cons] at hd ⊢
    rw [e] at hd ⊢
    obtain ⟨e', hnv'⟩ := ih hd
    refine ⟨e', fun hv r' hr' => ?_⟩
    rcases List.mem_cons.mp hr' with h | h
    · subst h; exact hnv hv
    · exact hnv' hv r' h

/-- Las ramas de `P0` que cumplen los `i` primeros requisitos. -/
def PinPre (φ : Cnf) (P0 : Assign → Prop) (reqs : List NodeId) (i : Nat) (a : Assign) : Prop :=
  P0 a ∧ ∀ r ∈ reqs.take i, selOfAssign φ a r.step = r

/-- **El filtro de una lista de requisitos conserva `Snd3`**, con un solo review, si cada requisito, con los
anteriores cumplidos, no deja familias fantasma. -/
theorem snd3_filterL {E : GPathB} {T : Int} {P0 : Assign → Prop} {reqs ord : List NodeId} (hE : SInvB E)
    (hns : NoSelf E) (hndt : NoDegT E) (hcs : E.current_step = T) (hvE : E.isValid = true)
    (hrange : ∀ r ∈ reqs, 1 ≤ r.step ∧ r.step < T) (hperm : ∀ r, r ∈ ord ↔ r ∈ reqs)
    (hH : ∀ i (hi : i < ord.length), PhantomFree φ (PinPre φ P0 ord i)
      (fun a => PinPre φ P0 ord i a ∧ selOfAssign φ a ord[i].step = ord[i]) T ord[i].step)
    (hs : Snd3 φ P0 E) (hc : ∀ a, P0 a → CT E (pidOfAssign φ a))
    (hvY : (E.filterAllOn reqs).isValid = true) :
    Snd3 φ (fun a => P0 a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r) (E.filterAllOn reqs) := by
  have hsh := (shrinks_filterAllOn E reqs).1
  cases hd : (reqs.foldl filterRequire E).dirty
  · -- los filtros no matan a nadie: toda rama de la entrada cumple los requisitos
    obtain ⟨_, hnv⟩ := foldl_clean reqs hd
    have agr : ∀ a, P0 a → ∀ r ∈ reqs, selOfAssign φ a r.step = r := by
      intro a hS r hr
      obtain ⟨hr1, hr2⟩ := hrange r hr
      have hD := hc a hS
      have hal := hD.1.alive r.step (by omega) (by rw [hcs]; exact hr2)
      obtain ⟨n, hn, hnid⟩ := hE.docs _ hal
      have hline : n ∈ E.line r.step := by
        unfold line
        refine List.mem_filter.mpr ⟨hn, ?_⟩
        rw [hnid, hD.1.step r.step (by omega) (by rw [hcs]; exact hr2)]
        simp
      have := hnv hvE r hr n hline
      rw [hnid] at this
      exact this
    refine ⟨fun x w hxw => ?_, fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
    · obtain ⟨a, hS, h1, h2⟩ := hs.1 x w (hsh.adj _ _ hxw)
      exact ⟨a, ⟨hS, agr a hS⟩, h1, h2⟩
    · have hnE : ¬ TF E x u w := fun hf => hn (tF_mono (trios_grow_filterAllOn E reqs) hxu hf)
      obtain ⟨a, hS, h1, h2, h3⟩ := hs.2 x u w (hsh.adj _ _ hxu) (hsh.adj _ _ hxw) (hsh.adj _ _ huw) nxu nxw nuw hnE
      exact ⟨a, ⟨hS, agr a hS⟩, h1, h2, h3⟩
  · cases reqs with
    | nil =>
      exact snd3_filter hE hns hndt hcs hvE (by simp) hrange (fun r hr => absurd hr List.not_mem_nil) hs hc hvY
    | cons r0 rs0 =>
    have hT2 : 2 ≤ T := by have := hrange r0 List.mem_cons_self; omega
    generalize hreqs : r0 :: rs0 = reqs at *
    have e : E.filterAllOn reqs = E.pinOn reqs := by
      unfold filterAllOn pinOn
      congr 1
      generalize reqs.foldl filterRequire E = F at hd
      cases F
      simp_all
    rw [e] at hvY ⊢
    have hsub := sub_pinOn E reqs
    have hiY : SInvB (E.pinOn reqs) := sInvB_pinOn hE reqs
    have hcl : ClosedState (E.pinOn reqs) := closedState_pinOn hE hvY (by rw [hcs]; exact hT2)
    have hf : FixClosed (E.pinOn reqs) :=
      fixClosed_reviewOn (g := { reqs.foldl filterRequire E with dirty := true }) rfl hvY
    have hg := trioGood_low hf (noDegT_pinOn hns hndt reqs) (Int.le_refl _)
    have hlt : ∀ {q : PathNodeId}, q ∈ (E.pinOn reqs).alive → q.id.step < (E.pinOn reqs).current_step :=
      fun hq => alive_below hiY.docs hiY.below hq
    have hR : ∀ {y z : PathNodeId}, (E.pinOn reqs).Adj y z →
        LowR (E.pinOn reqs) (E.pinOn reqs).current_step y z := fun h =>
      ⟨⟨(hiY.edges _ _ h).1, (hiY.edges _ _ h).2, h⟩, hlt (hiY.edges _ _ h).1, hlt (hiY.edges _ _ h).2⟩
    have pinned := pinned_pinOn hE.docs hvY
    have nE : ∀ {y z v : PathNodeId}, (E.pinOn reqs).Adj y z → ¬ TF (E.pinOn reqs) y z v → ¬ TF E y z v :=
      fun hyz hn hf => hn (tF_mono (trios_grow_pinOn E reqs) hyz hf)
    have agS : ∀ {r : NodeId}, r ∈ reqs → ∀ {a : Assign} {s : PathNodeId}, s ∈ (E.pinOn reqs).alive →
        s.id.step = r.step → pidOfAssign φ a s.id.step = s → selOfAssign φ a r.step = r := by
      intro r hr a s hsa hss hp
      have := congrArg PathNodeId.id hp
      rw [pid_id, hss] at this
      rw [this]; exact pinned r hr s hsa hss
    have b0 : ∀ {q : PathNodeId}, q ∈ (E.pinOn reqs).alive → 0 ≤ q.id.step ∧ q.id.step < T := by
      intro q hq
      obtain ⟨n, hn, rfl⟩ := hiY.docs q hq
      have h1 := hiY.below n hn
      rw [step_pinOn, hcs] at h1
      exact ⟨hiY.zero n hn, h1⟩
    have hcT : (E.pinOn reqs).current_step = T := by rw [step_pinOn, hcs]
    -- lo que da la estructura del estado fijado, para cualquier par de familias
    let L := LowR (E.pinOn reqs) (E.pinOn reqs).current_step
    let B2 : (Assign → Prop) → Prop := fun Q => ∀ y w, L y w →
      ∃ a, Q a ∧ pidOfAssign φ a y.id.step = y ∧ pidOfAssign φ a w.id.step = w
    let B3 : (Assign → Prop) → Prop := fun Q => ∀ x u w, L x u → L x w → L u w → x ≠ u → x ≠ w → u ≠ w →
      ¬ TF (E.pinOn reqs) x u w →
      ∃ a, Q a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧ pidOfAssign φ a w.id.step = w
    have use : ∀ {Pa Pb : Assign → Prop} {σ : Int}, PhantomFree φ Pa Pb T σ → B2 Pa → B3 Pa →
        (∀ a s, Pa a → L s s → s.id.step = σ → pidOfAssign φ a σ = s → Pb a) → B2 Pb ∧ B3 Pb := by
      intro Pa Pb σ hPF h2 h3 hanch
      exact hPF L (TF (E.pinOn reqs))
        (fun y w h => ⟨hR (adj_refl _ _ h.1.1), hR (adj_refl _ _ h.1.2.1)⟩)
        (fun y w h => hR ((adj_symm _ _ _).mp h.1.2.2))
        (fun a b r h1 h2 h3 hT => hg.swap23 h1 h2 h3 hT)
        (fun a b r h1 h2 h3 hT => hg.swap12 h1 h2 h3 hT)
        (fun y w h => b0 h.1.1)
        (fun y w h l l0 l1 => by
          by_cases e : y = w
          · obtain ⟨s, hss, hys, hws⟩ := hcl.pair (y := y) (w := w) h.1 l l0 (by rw [hcT]; exact l1)
            exact ⟨s, hss, hR hys.2.2, hR hws.2.2, Or.inl e⟩
          · obtain ⟨s, hss, hys, hws, hor⟩ := hg.edge h e l l0 (by rw [hcT]; exact l1)
            exact ⟨s, hss, hys, hws, Or.inr hor⟩)
        (fun x u w h1 h2 h3 n1 n2 n3 hn l l0 l1 => hg.trio h1 h2 h3 n1 n2 n3 hn l l0 (by rw [hcT]; exact l1))
        h2 h3 hanch
    -- un requisito más cada vez, sobre la misma estructura
    have key : ∀ i, i ≤ ord.length → B2 (PinPre φ P0 ord i) ∧ B3 (PinPre φ P0 ord i) := by
      intro i
      induction i with
      | zero =>
        intro _
        refine ⟨fun y w h => ?_, fun x u w h1 h2 h3 n1 n2 n3 hn => ?_⟩
        · obtain ⟨a, ha, e1, e2⟩ := hs.1 y w (hsub.adj _ _ h.1.2.2)
          exact ⟨a, ⟨ha, fun r hr => by simp at hr⟩, e1, e2⟩
        · obtain ⟨a, ha, e1, e2, e3⟩ := hs.2 x u w (hsub.adj _ _ h1.1.2.2) (hsub.adj _ _ h2.1.2.2)
            (hsub.adj _ _ h3.1.2.2) n1 n2 n3 (nE h1.1.2.2 hn)
          exact ⟨a, ⟨ha, fun r hr => by simp at hr⟩, e1, e2, e3⟩
      | succ i ih =>
        intro hi
        have hil : i < ord.length := by omega
        obtain ⟨h2, h3⟩ := ih (by omega)
        have hmem : ord[i] ∈ reqs := (hperm _).mp (List.getElem_mem hil)
        have up : ∀ a, (PinPre φ P0 ord i a ∧ selOfAssign φ a ord[i].step = ord[i]) → PinPre φ P0 ord (i + 1) a := by
          intro a ⟨⟨ha, hpre⟩, hr⟩
          refine ⟨ha, fun r hr' => ?_⟩
          rw [List.take_add_one, List.getElem?_eq_getElem hil] at hr'
          rcases List.mem_append.mp hr' with h | h
          · exact hpre r h
          · simp only [Option.toList_some, List.mem_singleton] at h
            subst h; exact hr
        obtain ⟨c2, c3⟩ := use (hH i hil) h2 h3
          (fun a s hP hss hstep hp => ⟨hP, agS hmem hss.1.1 hstep (by rw [hstep]; exact hp)⟩)
        refine ⟨fun y w h => ?_, fun x u w h1 h2' h3' n1 n2 n3 hn => ?_⟩
        · obtain ⟨a, ha, e1, e2⟩ := c2 y w h
          exact ⟨a, up a ha, e1, e2⟩
        · obtain ⟨a, ha, e1, e2, e3⟩ := c3 x u w h1 h2' h3' n1 n2 n3 hn
          exact ⟨a, up a ha, e1, e2, e3⟩
    obtain ⟨c2, c3⟩ := key ord.length (Nat.le_refl _)
    have fin : ∀ a, PinPre φ P0 ord ord.length a → P0 a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r := by
      intro a ha
      refine ⟨ha.1, fun r hr => ha.2 r ?_⟩
      rw [List.take_length]; exact (hperm r).mpr hr
    refine ⟨fun x w hxw => ?_, fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
    · obtain ⟨a, hP, h1, h2⟩ := c2 x w (hR hxw)
      exact ⟨a, fin a hP, h1, h2⟩
    · obtain ⟨a, hP, h1, h2, h3⟩ := c3 x u w (hR hxu) (hR hxw) (hR huw) nxu nxw nuw hn
      exact ⟨a, fin a hP, h1, h2, h3⟩

/-- **Un paso de lectura con una lista de requisitos** conserva el invariante, si una rama de la familia los cumple
todos y cada requisito, en el orden `ord`, no deja familias fantasma. -/
theorem read_stepL {T : Int} {P : Assign → Prop} {g : GPathB} (h : RInv φ T P g) {reqs ord : List NodeId}
    (hw : ∃ a, P a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r) (hrange : ∀ r ∈ reqs, 1 ≤ r.step ∧ r.step < T)
    (hperm : ∀ r, r ∈ ord ↔ r ∈ reqs)
    (hH : ∀ i (hi : i < ord.length), PhantomFree φ (PinPre φ P ord i)
      (fun a => PinPre φ P ord i a ∧ selOfAssign φ a ord[i].step = ord[i]) T ord[i].step) :
    RInv φ T (fun a => P a ∧ ∀ r ∈ reqs, selOfAssign φ a r.step = r) (g.filterAllOn reqs) := by
  obtain ⟨a, hPa, hra⟩ := hw
  have hvY : (g.filterAllOn reqs).isValid = true := isValid_of_carried (comp_filter h.comp a ⟨hPa, hra⟩).1
  exact ⟨sInvB_filterAllOn h.inv _, noSelf_filterAllOn h.ns _, noDegT_filterAllOn h.ns h.ndt _,
    (step_filterAllOn g _).trans h.step, hvY,
    snd3_filterL h.inv h.ns h.ndt h.step h.valid hrange hperm hH h.snd h.comp hvY, fun b hb => comp_filter h.comp b hb⟩

/-- **El lector por nodos de ventana**: cada paso fija un nodo vivo `q` del tercer paso de una cláusula con sus tres
ids (abuelo, padre, hijo) en un solo filtro. -/
inductive WinReading (φ : Cnf) : GPathB → List (List NodeId) → GPathB → Prop
  | nil (g : GPathB) : WinReading φ g [] g
  | cons {g g' : GPathB} {q : PathNodeId} {j : Nat} {p gp : NodeId} {W : List (List NodeId)} :
      q ∈ g.alive → j < φ.clauses.length → q.id.step = clauseStep φ j 2 → q.parent_id = some p →
      q.gparent_id = some gp → WinReading φ (g.filterAllOn [gp, p, q.id]) W g' →
      WinReading φ g ([gp, p, q.id] :: W) g'

/-- Una rama por un nodo de ventana elige sus tres ids, y los ids están en los tres pasos de la cláusula. -/
theorem win_sels {T : Int} {P : Assign → Prop} {g : GPathB} (h : RInv φ T P g) {q : PathNodeId} (hq : q ∈ g.alive)
    {j : Nat} (hk : q.id.step = clauseStep φ j 2) {p gp : NodeId} (hp : q.parent_id = some p)
    (hgp : q.gparent_id = some gp) :
    (∃ a, P a ∧ ∀ r ∈ [gp, p, q.id], selOfAssign φ a r.step = r) ∧ gp.step = clauseStep φ j 0 ∧
      p.step = clauseStep φ j 1 ∧ q.id.step < T := by
  obtain ⟨a, hPa, hpa, _⟩ := h.snd.1 q q (adj_refl _ _ hq)
  have hk1 : 1 < q.id.step := by rw [hk]; simp only [clauseStep]; omega
  have e1 := congrArg PathNodeId.parent_id hpa
  have e2 := congrArg PathNodeId.gparent_id hpa
  simp only [pidOfAssign] at e1 e2
  rw [if_pos (by omega), hp] at e1
  rw [if_pos hk1, hgp] at e2
  have s1 := Option.some.inj e1
  have s2 := Option.some.inj e2
  have st1 : p.step = q.id.step - 1 := by rw [← s1, selOfAssign_step]
  have st2 : gp.step = q.id.step - 2 := by rw [← s2, selOfAssign_step]
  refine ⟨⟨a, hPa, fun r hr => ?_⟩, by rw [st2, hk]; simp only [clauseStep]; omega,
    by rw [st1, hk]; simp only [clauseStep]; omega, by rw [← h.step]; exact alive_below h.inv.docs h.inv.below hq⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [st2]; exact s2
  · rw [st1]; exact s1
  · have := congrArg PathNodeId.id hpa
    rw [pid_id] at this; exact this

theorem goodAlong_get {G : List NodeId → NodeId → Prop} : ∀ (l R0 : List NodeId), GoodAlongG G R0 l →
    ∀ i (hi : i < l.length), G (R0 ++ l.take i) l[i] := by
  intro l
  induction l with
  | nil => intro _ _ i hi; simp at hi
  | cons r rs ih =>
    intro R0 h i hi
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := ih (R0 ++ [r]) h.2 i (by simp at hi; omega)
      simpa [List.append_assoc] using this

/-- Si la lectura va primero por los separadores. -/
def rdS (φ : Cnf) (S : List Nat) (r : NodeId) : Bool :=
  match pinVar φ r with
  | some z => decide (z ∈ S)
  | none => false

/-- **Los tres ids de un nodo de ventana, separadores primero, son una ventana** (`WinOk`). -/
theorem winOk_node {S : List Nat} {j : Nat} {c : Clause} (hc : φ.clauses[j]? = some c) {gp p x : NodeId}
    (h0 : gp.step = clauseStep φ j 0) (h1 : p.step = clauseStep φ j 1) (h2 : x.step = clauseStep φ j 2) :
    WinOk φ S ([gp, p, x].filter (rdS φ S) ++ [gp, p, x].filter (fun r => !rdS φ S r)) := by
  have rd : ∀ r ∈ [gp, p, x], ∃ z, pinVar φ r = some z ∧ ClVar c z := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by unfold pinVar; rw [h0]; exact stepVar_clause hc 0 (by omega), Or.inl rfl⟩
    · exact ⟨_, by unfold pinVar; rw [h1]; exact stepVar_clause hc 1 (by omega), Or.inr (Or.inl rfl)⟩
    · exact ⟨_, by unfold pinVar; rw [h2]; exact stepVar_clause hc 2 (by omega), Or.inr (Or.inr rfl)⟩
  refine ⟨c, List.mem_of_getElem? hc, _, _, rfl, fun y hy => ?_, fun y hy => rd y (List.mem_filter.mp hy).1,
    fun s hs hcs => ?_⟩
  · have hy' := (List.mem_filter.mp hy).2
    unfold rdS at hy'
    split at hy'
    · rename_i z hz; exact ⟨z, of_decide_eq_true hy', hz⟩
    · cases hy'
  · -- el separador de la cláusula lo lee uno de los tres
    have : ∃ y ∈ [gp, p, x], pinVar φ y = some s := by
      rcases hcs with e | e | e
      · exact ⟨gp, by simp, by unfold pinVar; rw [h0, e]; exact stepVar_clause hc 0 (by omega)⟩
      · exact ⟨p, by simp, by unfold pinVar; rw [h1, e]; exact stepVar_clause hc 1 (by omega)⟩
      · exact ⟨x, by simp, by unfold pinVar; rw [h2, e]; exact stepVar_clause hc 2 (by omega)⟩
    obtain ⟨y, hy, hys⟩ := this
    exact ⟨y, List.mem_filter.mpr ⟨hy, by unfold rdS; rw [hys]; exact decide_eq_true hs⟩, hys⟩

theorem mem_split {S : List Nat} (l : List NodeId) (r : NodeId) :
    r ∈ l.filter (rdS φ S) ++ l.filter (fun r => !rdS φ S r) ↔ r ∈ l := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact (List.mem_filter.mp h).1
    · exact (List.mem_filter.mp h).1
  · intro h
    cases e : rdS φ S r
    · exact List.mem_append_right _ (List.mem_filter.mpr ⟨h, by simp [e]⟩)
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨h, e⟩)

end GPathB

end AbsSatBingo.Model

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace MachineOn

open GPathB Driver Machine

variable {φ : Cnf}

/-- **El lector por nodos de ventana no se atasca**, con las líneas, una cobertura por separadores, `SepPinAny` y
`OneWin`: cada nodo de ventana se fija con sus tres ids en un solo filtro y un solo review, y toda lectura deja un
estado válido que lleva la rama de una asignación que satisface `φ` y coincide con todas las elecciones. -/
theorem reader_winNode_on {S : List Nat} {part : Nat → Nat} (hbd : Bounded φ)
    (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T) (hc : SepCover φ S part) (h2 : SepPinAny φ S (stepCount φ))
    (hone : OneWin φ S part) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ) {W : List (List NodeId)} {g' : GPathB}
    (hr : WinReading φ kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ W.flatten, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) := by
  have hpos := stepCount_pos φ
  have hn : (((stepCount φ - 1).toNat : Nat) : Int) + 1 = stepCount φ := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  have hl := lInvS3_stepsW hbd (stepCount φ - 1).toNat (fun T h1 _ => HA T h1)
  have hcomp := compLine_steps hbd (lInvS_of_s3 hl)
  rw [hn] at hl hcomp
  have hkv' : kv ∈ stepsM .on φ (stepCount φ - 1).toNat (initM .on φ) := hkv
  have hent := hl.on kv hkv'
  have h0 : RInv φ (stepCount φ) (Pinned φ (SolE φ (stepCount φ) kv.1) []) kv.2 :=
    rInv_congr (P := SolE φ (stepCount φ) kv.1)
      ⟨hl.inv kv hkv', hent.2.1, hl.ndt kv hkv', hent.1.step, hent.1.valid, hl.snd kv hkv', hcomp kv hkv'⟩
      (fun a => ⟨fun ha => ⟨ha, fun r hr => absurd hr List.not_mem_nil⟩, fun ha => ha.1⟩)
  let P := SolE φ (stepCount φ) kv.1
  have hH : ∀ R0 r, 1 ≤ r.step → r.step < stepCount φ → WinGood φ S part R0 r →
      PhantomFree φ (Pinned φ P R0) (fun a => Pinned φ P R0 a ∧ selOfAssign φ a r.step = r) (stepCount φ) r.step := by
    intro R0 r hr1 hrT hg
    cases hv : stepVar φ r.step with
    | none => exact phantomFree_none (locPair_read _ kv.1 R0 r) hv (by omega) hrT
    | some v =>
      by_cases hvS : v ∈ S
      · exact h2 kv.1 R0 r v hvS hv hr1 hrT
      · exact phantomFree_pinnedNear (locPair_read _ kv.1 R0 r) hc hv hvS
          (fun a b ha hb s hs hn => agree_of_pins (hg v hv hvS s hs hn) a b ha hb) (by omega) hrT
  -- la inducción sobre la lectura, con lo fijado antes
  have main : ∀ {g g' : GPathB} {W : List (List NodeId)}, WinReading φ g W g' → ∀ R0,
      RInv φ (stepCount φ) (Pinned φ P R0) g → RInv φ (stepCount φ) (Pinned φ P (R0 ++ W.flatten)) g' := by
    intro g g' W hw
    induction hw with
    | nil g => intro R0 h; rw [List.flatten_nil, List.append_nil]; exact h
    | @cons g g' q j p gp W hq hj hk hp hgp _ ih =>
      intro R0 h
      obtain ⟨hwit, s0, s1, hkT⟩ := win_sels h hq hk hp hgp
      have hcj : φ.clauses[j]? = some (φ.clauses[j]'hj) := List.getElem?_eq_getElem hj
      let ord := [gp, p, q.id].filter (rdS φ S) ++ [gp, p, q.id].filter (fun r => !rdS φ S r)
      have hperm : ∀ r, r ∈ ord ↔ r ∈ [gp, p, q.id] := mem_split _
      have hrange : ∀ r ∈ [gp, p, q.id], 1 ≤ r.step ∧ r.step < stepCount φ := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hk1 : 1 ≤ clauseStep φ j 0 := by simp only [clauseStep]; omega
        rcases hr with rfl | rfl | rfl
        · rw [s0]; refine ⟨hk1, ?_⟩; rw [hk] at hkT; simp only [clauseStep] at hkT ⊢; omega
        · rw [s1]; refine ⟨by simp only [clauseStep]; omega, ?_⟩; rw [hk] at hkT; simp only [clauseStep] at hkT ⊢; omega
        · refine ⟨by rw [hk]; simp only [clauseStep]; omega, hkT⟩
      have hgood := goodAlong_win hone (winOk_node (S := S) hcj s0 s1 hk) R0
      have h1 := read_stepL h hwit hrange hperm (fun i hi => by
        have e : PinPre φ (Pinned φ P R0) ord i = Pinned φ P (R0 ++ ord.take i) := by
          funext a
          apply propext
          constructor
          · intro ha
            exact ⟨ha.1.1, fun r hr => (List.mem_append.mp hr).elim (ha.1.2 r) (ha.2 r)⟩
          · intro ha
            exact ⟨⟨ha.1, fun r hr => ha.2 r (List.mem_append_left _ hr)⟩,
              fun r hr => ha.2 r (List.mem_append_right _ hr)⟩
        rw [e]
        obtain ⟨b1, b2⟩ := hrange _ ((hperm _).mp (List.getElem_mem hi))
        exact hH _ _ b1 b2 (goodAlong_get ord R0 hgood i hi))
      have h1' : RInv φ (stepCount φ) (Pinned φ P (R0 ++ [gp, p, q.id])) (g.filterAllOn [gp, p, q.id]) :=
        rInv_congr h1 (fun a => ⟨fun ha => ⟨ha.1.1, fun r hr => (List.mem_append.mp hr).elim (ha.1.2 r) (ha.2 r)⟩,
          fun ha => ⟨⟨ha.1, fun r hr => ha.2 r (List.mem_append_left _ hr)⟩,
            fun r hr => ha.2 r (List.mem_append_right _ hr)⟩⟩)
      have := ih (R0 ++ [gp, p, q.id]) h1'
      rw [List.flatten_cons, ← List.append_assoc]
      exact this
  have hfin := main hr [] h0
  rw [List.nil_append] at hfin
  refine ⟨hfin.valid, ?_⟩
  obtain ⟨q, hq, _⟩ := exists_alive_at hfin.valid (k := 0) (Int.le_refl 0) (by rw [hfin.step]; exact hpos)
  obtain ⟨a, ha, _, _⟩ := hfin.snd.1 q q (adj_refl _ _ hq)
  exact ⟨a, sat_of_validUpTo ha.1.1, ha.2, hfin.comp a ha⟩

variable {n : Nat} {zone sv : Nat → Nat}

/-- **El lector por nodos de ventana no se atasca en ninguna cadena en orden**, de cualquier longitud y en cualquier
orden de las ventanas: sin hipótesis. -/
theorem reader_winNode_of_chainOrd (hb : Bounded φ) (C : ChainOrdN φ n zone sv) {ord : List Nat}
    (hord : ∀ q ∈ ord, 1 ≤ q ∧ q < n) (hall : ∀ q, 1 ≤ q → q < n → q ∈ ord) {kv : NodeId × GPathB}
    (hkv : kv ∈ runM .on φ) {W : List (List NodeId)} {g' : GPathB} (hr : WinReading φ kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ W.flatten, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) := by
  have hS := mem_sep_iff' C.D C.hsv hord hall
  exact reader_winNode_on hb (fun T hT => phantomAtW_of_phantomAt (phantomAt_of_chainOrd hb C T hT))
    (sepCover_of_chainN C.D (fun _ hc => ordM_cl C.toM hc) hS)
    (sepPinAny_of_local C.D C.hsv (localReads_of C.hsv C.num C.lit) hS) (oneWin_of_chainOrd C hS) hkv hr

/-- **`chain12_order` con el lector por nodos de ventana.** -/
theorem reader_winNode_chain12O {kv : NodeId × GPathB} (hkv : kv ∈ runM .on chain12O) {W : List (List NodeId)}
    {g' : GPathB} (hr : WinReading chain12O kv.2 W g') :
    g'.isValid = true ∧ ∃ a, Sat a chain12O ∧ (∀ r ∈ W.flatten, selOfAssign chain12O a r.step = r) ∧
      CT g' (pidOfAssign chain12O a) :=
  reader_winNode_of_chainOrd bounded_chain12O chainOrd_chain12O (ord := List.range' 1 11)
    (fun q hq => by rw [List.mem_range'_1] at hq; omega)
    (fun q h1 h2 => by rw [List.mem_range'_1]; omega) hkv hr

end MachineOn

end AbsSatBingo.Model
