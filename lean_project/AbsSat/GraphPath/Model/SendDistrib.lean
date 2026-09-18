-- lean_project/AbsSat/GraphPath/Model/SendDistrib.lean
import AbsSat.GraphPath.Model.BranchReader

/-!
# The verdict from one global equation: the send distributes over the join

The author's reading (v138): the structure is read **whole**, not in parts — the reader pins a choice
and the review runs over the entire state again. So the property to ask of the machine is not a local
rule on owner tables (five of them are refuted, v130–v132) but a statement about **whole operations**.

The one measured here and used below is that **a send distributes over a join**:

* **`SendDistrib`** — sending `join e h` to `d` (weak filter, pins, aggressive review, up) gives a state
  inside the join of the sends of `e` and `h` that survive; if it survives, one of them does.
* **`ReviewDistrib`** — if the reader's review keeps `join e h` valid, it keeps `e` or `h` valid.

Both are one step and two states. The probe `helly distrib` compares both sides **table by table** at
every join of the run: equal in every one of ~90,000 checks, over six structured families and three
random seeds.

From them, by induction over the construction:

* **`split_branch`** — a valid branch splits at any step into single-key pieces, one of which is valid
  on its own: the run from a line sits inside the merge of the runs from its entries.
* **`noBorrow_of_distrib`** — which is `NoBorrow` (v127).
* **`sat_of_distrib`** — and the Improves verdict: a valid final state gives a model of `φ`.

The merge (`mergeL`) is the union of lines the driver itself performs (`insertPure`), so no new
operation enters the argument.
-/

namespace AbsSat.GraphPath.Model.SendDistrib

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriver (PureLine insertPure pureInit insertPure_keys_some insertPure_keys_none)
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv LineInv_insertPure LineInv_pureAdvanceW LineInv_init
  MInv_sent)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF LineOkF StateOkF_sent Fsac prunes_Fsac
  okJoin_of_stateOkF)
open AbsSat.GraphPath.Model.EmbeddedSupport
open AbsSat.GraphPath.Model.BranchRun
open AbsSat.GraphPath.Model.BranchLines
open AbsSat.GraphPath.Model.BranchCompat
open AbsSat.GraphPath.Model.BranchReader
open AbsSat.GraphPath.Model.PickInduction (choiceAt hasChoice gowner_of_isValid)

variable (φ : Cnf)

-- ============================================================
-- The two equations
-- ============================================================

/-- The reader's review of a state. -/
abbrev rev (g : GPathM) : GPathM := filterAllAgg g []

/-- **A send distributes over a join.** Sending the join of two states of a line with the same key
gives a state inside the join of the sends that survive, and one of them survives. -/
def SendDistrib : Prop :=
  ∀ (k : Int) (key : NodeId) (e h : GPathM), StateOkF φ k (key, e) → StateOkF φ k (key, h) →
    MInv φ e → MInv φ h → ∀ d ∈ mapSons φ key.step key.index,
    isValid (sent φ (join e h) d) = true →
      (isValid (sent φ e d) = true ∧ isValid (sent φ h d) = true ∧
          Embedded (sent φ (join e h) d) (join (sent φ e d) (sent φ h d))) ∨
      (isValid (sent φ e d) = true ∧ Embedded (sent φ (join e h) d) (sent φ e d)) ∨
      (isValid (sent φ h d) = true ∧ Embedded (sent φ (join e h) d) (sent φ h d))

/-- **The reader's review distributes over a join**, at the level of validity. -/
def ReviewDistrib : Prop :=
  ∀ (k : Int) (key : NodeId) (e h : GPathM), StateOkF φ k (key, e) → StateOkF φ k (key, h) →
    MInv φ e → MInv φ h → isValid (rev (join e h)) = true →
      isValid (rev e) = true ∨ isValid (rev h) = true

-- ============================================================
-- Embedding is transitive
-- ============================================================

theorem mem_of_embedded {A B : GPathM} (h : Embedded A B) {q : PathNodeId} (hq : Mem A q) : Mem B q := by
  obtain ⟨m, hm⟩ := hq
  obtain ⟨n, hn, _, _⟩ := h.node q m hm
  exact ⟨n, hn⟩

theorem embedded_trans {A B C : GPathM} (h₁ : Embedded A B) (h₂ : Embedded B C) : Embedded A C where
  step := h₁.step.trans h₂.step
  gow p hp := h₂.gow p (h₁.gow p hp)
  node p m hm := by
    obtain ⟨n, hn, ho, hpa⟩ := h₁.node p m hm
    obtain ⟨n', hn', ho', hpa'⟩ := h₂.node p n hn
    exact ⟨n', hn', fun q hq hmq => ho' q (ho q hq hmq) (mem_of_embedded h₁ hmq),
      fun q hq hmq => hpa' q (hpa q hq hmq) (mem_of_embedded h₁ hmq)⟩

theorem embedded_of_grown' {B G : GPathM} (h : Grown B G) : Embedded B G :=
  embedded_of_grown (embedded_refl B) h

-- ============================================================
-- Merging lines
-- ============================================================

/-- Insert every entry of `xs` into `acc`, as the driver does. -/
def mergeL (xs acc : PureLine) : PureLine := xs.foldl (fun a kv => insertPure a kv.1 kv.2) acc

theorem lineInv_mergeL (k : Int) : ∀ (xs acc : PureLine), LineInv φ k acc →
    (∀ kv ∈ xs, StateOkF φ k kv ∧ MInv φ kv.2) → LineInv φ k (mergeL xs acc) := by
  intro xs
  induction xs with
  | nil => intro acc h _; exact h
  | cons x rest ih =>
    intro acc h hx
    exact ih _ (LineInv_insertPure φ k acc x.1 x.2 h (hx x List.mem_cons_self).1 (hx x List.mem_cons_self).2)
      (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv))

/-- Every entry, old or merged, grows into the entry of its key. -/
theorem mergeL_grows (k : Int) : ∀ (xs acc : PureLine), LineInv φ k acc →
    (∀ kv ∈ xs, StateOkF φ k kv ∧ MInv φ kv.2) →
    (∀ kv ∈ acc, ∃ J, (kv.1, J) ∈ mergeL xs acc ∧ Grown kv.2 J) ∧
    (∀ kv ∈ xs, ∃ J, (kv.1, J) ∈ mergeL xs acc ∧ Grown kv.2 J) := by
  intro xs
  induction xs with
  | nil =>
    intro acc _ _
    exact ⟨fun kv hkv => ⟨kv.2, hkv, Grown.refl _⟩, fun kv hkv => absurd hkv List.not_mem_nil⟩
  | cons x rest ih =>
    intro acc h hx
    have hx0 := hx x List.mem_cons_self
    have h' := LineInv_insertPure φ k acc x.1 x.2 h hx0.1 hx0.2
    obtain ⟨ihA, ihX⟩ := ih (insertPure acc x.1 x.2) h' (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv))
    refine ⟨fun kv hkv => ?_, fun kv hkv => ?_⟩
    · obtain ⟨J', hJ', hg'⟩ := insert_grows acc x.1 x.2 h.1.1 kv.1 kv.2 hkv
      obtain ⟨J, hJ, hg⟩ := ihA (kv.1, J') hJ'
      exact ⟨J, hJ, Grown.trans hg' hg⟩
    · rcases List.mem_cons.mp hkv with rfl | hkv'
      · obtain ⟨J', hJ', hg'⟩ := insert_new acc kv.1 kv.2
          (fun e he => okJoin_of_stateOkF φ k kv.1 e kv.2 (h.1.2 (kv.1, e) he) hx0.1)
        obtain ⟨J, hJ, hg⟩ := ihA (kv.1, J') hJ'
        exact ⟨J, hJ, Grown.trans hg' hg⟩
      · exact ihX kv hkv'

/-- A property of entries that the join keeps holds of every merged entry. -/
theorem mergeL_inv (k : Int) (Q : NodeId → GPathM → Prop)
    (hQ : ∀ d e g, StateOkF φ k (d, e) → StateOkF φ k (d, g) → MInv φ e → MInv φ g →
      Q d e → Q d g → Q d (doJoin e g)) :
    ∀ (xs acc : PureLine), LineInv φ k acc → (∀ kv ∈ xs, StateOkF φ k kv ∧ MInv φ kv.2) →
      (∀ kv ∈ acc, Q kv.1 kv.2) → (∀ kv ∈ xs, Q kv.1 kv.2) → ∀ kv ∈ mergeL xs acc, Q kv.1 kv.2 := by
  intro xs
  induction xs with
  | nil => intro acc _ _ hacc _; exact hacc
  | cons x rest ih =>
    intro acc h hx hacc hq
    have hx0 := hx x List.mem_cons_self
    refine ih (insertPure acc x.1 x.2) (LineInv_insertPure φ k acc x.1 x.2 h hx0.1 hx0.2)
      (fun kv hkv => hx kv (List.mem_cons_of_mem _ hkv)) ?_ (fun kv hkv => hq kv (List.mem_cons_of_mem _ hkv))
    rintro ⟨d, B⟩ hB
    rcases insert_src acc x.1 x.2 d B hB with ⟨hdx, hB'⟩ | ⟨hB', _⟩
    · subst hdx
      rcases hB' with rfl | ⟨e, he, rfl⟩
      · exact hq x List.mem_cons_self
      · exact hQ x.1 e x.2 (h.1.2 (x.1, e) he) hx0.1 (h.2 (x.1, e) he) hx0.2 (hacc (x.1, e) he)
          (hq x List.mem_cons_self)
    · exact hacc (d, B) hB'

-- ============================================================
-- Merging commutes with restricting by key
-- ============================================================

theorem keys_nodup_insertPure (acc : PureLine) (key : NodeId) (g : GPathM) (hnd : (acc.map (·.1)).Nodup) :
    ((insertPure acc key g).map (·.1)).Nodup := by
  cases hf : acc.find? (fun kv => kv.1 == key) with
  | none =>
    rw [insertPure_keys_none acc key g hf]
    refine List.nodup_append.mpr ⟨hnd, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton.mp hb] at hab
    obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp ha
    have := List.find?_eq_none.mp hf kv hkv
    simp [hab] at this
  | some e =>
    rw [insertPure_keys_some acc key g e hf]
    exact hnd

theorem filter_insertPure (p : NodeId → Bool) (acc : PureLine) (key : NodeId) (g : GPathM)
    (hnd : (acc.map (·.1)).Nodup) :
    (insertPure acc key g).filter (fun kv => p kv.1) =
      if p key then insertPure (acc.filter (fun kv => p kv.1)) key g else acc.filter (fun kv => p kv.1) := by
  unfold insertPure
  cases hf : acc.find? (fun kv => kv.1 == key) with
  | none =>
    have hf' : (acc.filter (fun kv => p kv.1)).find? (fun kv => kv.1 == key) = none := by
      apply List.find?_eq_none.mpr
      intro kv hkv
      exact List.find?_eq_none.mp hf kv (List.mem_filter.mp hkv).1
    simp only [List.filter_append]
    by_cases hp : p key
    · simp [hp, hf']
    · simp [hp]
  | some e =>
    simp only
    have he : e ∈ acc := List.mem_of_find?_eq_some hf
    have hek : e.1 = key := eq_of_beq (List.find?_some (p := fun kv : NodeId × GPathM => kv.1 == key) hf)
    let F : NodeId × GPathM → NodeId × GPathM := fun kv => if kv.1 == key then (key, doJoin e.2 g) else kv
    have hF1 : ∀ kv, (F kv).1 = kv.1 := by
      intro kv
      simp only [F]
      split
      · next h => exact (eq_of_beq h).symm
      · rfl
    have hmapf : (acc.map F).filter (fun kv => p kv.1) = (acc.filter (fun kv => p kv.1)).map F := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro kv _
      simp only [Function.comp, hF1]
    by_cases hp : p key
    · simp only [hp, if_true]
      have hef : e ∈ acc.filter (fun kv => p kv.1) := List.mem_filter.mpr ⟨he, by rw [hek]; exact hp⟩
      obtain ⟨e', he'⟩ : ∃ e', (acc.filter (fun kv => p kv.1)).find? (fun kv => kv.1 == key) = some e' := by
        cases h' : (acc.filter (fun kv => p kv.1)).find? (fun kv => kv.1 == key) with
        | none => exact absurd (List.find?_eq_none.mp h' e hef) (by simp [hek])
        | some e' => exact ⟨e', rfl⟩
      rw [he']
      have he'm : e' ∈ acc := (List.mem_filter.mp (List.mem_of_find?_eq_some he')).1
      have he'k : e'.1 = key := eq_of_beq (List.find?_some (p := fun kv : NodeId × GPathM => kv.1 == key) he')
      have hee : e'.2 = e.2 := key_unique acc hnd key e'.2 e.2 (by rw [← he'k]; exact he'm)
        (by rw [← hek]; exact he)
      simp only
      rw [hmapf, hee]
    · rw [if_neg hp, hmapf]
      have hid : ∀ kv ∈ acc.filter (fun kv => p kv.1), F kv = kv := by
        intro kv hkv
        have hk : kv.1 ≠ key := by
          intro h
          have h2 : p kv.1 = true := by simpa using (List.mem_filter.mp hkv).2
          exact hp (h ▸ h2)
        simp only [F, beq_false_of_ne hk]
        rfl
      rw [List.map_congr_left hid]
      simp

theorem mergeL_filter (p : NodeId → Bool) : ∀ (xs acc : PureLine), (acc.map (·.1)).Nodup →
    mergeL (xs.filter (fun kv => p kv.1)) (acc.filter (fun kv => p kv.1)) =
      (mergeL xs acc).filter (fun kv => p kv.1) := by
  intro xs
  induction xs with
  | nil => intro acc _; rfl
  | cons x rest ih =>
    intro acc hnd
    have hnd' := keys_nodup_insertPure acc x.1 x.2 hnd
    have key := filter_insertPure p acc x.1 x.2 hnd
    by_cases hp : p x.1
    · simp only [List.filter_cons, hp, if_true, mergeL, List.foldl_cons]
      rw [if_pos hp] at key
      rw [← key]
      exact ih _ hnd'
    · simp only [List.filter_cons, hp, mergeL, List.foldl_cons]
      rw [if_neg hp] at key
      have := ih _ hnd'
      rw [key] at this
      exact this

theorem filter_flatten' (p : NodeId × GPathM → Bool) : ∀ (Ls : List PureLine),
    (Ls.map (fun L => L.filter p)).flatten = Ls.flatten.filter p := by
  intro Ls
  induction Ls with
  | nil => rfl
  | cons L rest ih => simp only [List.map_cons, List.flatten_cons, List.filter_append, ih]

-- ============================================================
-- The line step: advancing a merge sits inside the merge of the advances
-- ============================================================

/-- **The distributive step.** Under `SendDistrib`, advancing the merge of some lines gives, key by
key, states inside the merge of their advances. -/
theorem lineEmb_advance_merge (hwf : WF φ) (hS : SendDistrib φ) (k : Int) (Ls : List PureLine)
    (hL : ∀ L ∈ Ls, LineInv φ k L) :
    LineEmb (pureAdvanceW φ (mergeL Ls.flatten [])) (mergeL (Ls.map (pureAdvanceW φ)).flatten []) := by
  have hxs : ∀ kv ∈ Ls.flatten, StateOkF φ k kv ∧ MInv φ kv.2 := by
    intro kv hkv
    obtain ⟨L, hL', hkv'⟩ := List.mem_flatten.mp hkv
    exact ⟨(hL L hL').1.2 kv hkv', (hL L hL').2 kv hkv'⟩
  have hA : LineInv φ k (mergeL Ls.flatten []) := lineInv_mergeL φ k _ [] (lineInv_nil φ k) hxs
  have hys : ∀ kv ∈ (Ls.map (pureAdvanceW φ)).flatten, StateOkF φ (k + 1) kv ∧ MInv φ kv.2 := by
    intro kv hkv
    obtain ⟨L', hL', hkv'⟩ := List.mem_flatten.mp hkv
    obtain ⟨L, hL0, rfl⟩ := List.mem_map.mp hL'
    have := LineInv_pureAdvanceW φ hwf k L (hL L hL0)
    exact ⟨this.1.2 kv hkv', this.2 kv hkv'⟩
  have hM : LineInv φ (k + 1) (mergeL (Ls.map (pureAdvanceW φ)).flatten []) :=
    lineInv_mergeL φ (k + 1) _ [] (lineInv_nil φ (k + 1)) hys
  have hgrowM := (mergeL_grows φ (k + 1) _ [] (lineInv_nil φ (k + 1)) hys).2
  -- every send of a merged state lands inside the entry of its key in the merge of the advances
  let Q : NodeId → GPathM → Prop := fun key S => ∀ d ∈ mapSons φ key.step key.index,
    isValid (sent φ S d) = true →
      ∃ J, (d, J) ∈ mergeL (Ls.map (pureAdvanceW φ)).flatten [] ∧ Embedded (sent φ S d) J
  have hQ : ∀ kv ∈ mergeL Ls.flatten [], Q kv.1 kv.2 := by
    refine mergeL_inv φ k Q ?_ _ [] (lineInv_nil φ k) hxs (fun kv hkv => absurd hkv List.not_mem_nil) ?_
    · intro key e g hse hsg hme hmg hQe hQg
      unfold doJoin
      split
      · intro d hd hv
        rcases hS k key e g hse hsg hme hmg d hd hv with ⟨hve, hvg, hemb⟩ | ⟨hve, hemb⟩ | ⟨hvg, hemb⟩
        · obtain ⟨Je, hJe, hee⟩ := hQe d hd hve
          obtain ⟨Jg, hJg, heg⟩ := hQg d hd hvg
          have hJJ := key_unique _ hM.1.1 d Je Jg hJe hJg
          rw [← hJJ] at heg
          have hmse := MInv_sent φ hwf k (key, e) hse hme d hd hve
          have hmsg := MInv_sent φ hwf k (key, g) hsg hmg d hd hvg
          exact ⟨Je, hJe, embedded_trans hemb (embedded_join_same _ _ Je hee heg (own_mem φ hmse)
            (own_mem φ hmsg) hmse.rctx.shape.pn hmsg.rctx.shape.pn hmse.rctx.nodup hmsg.rctx.nodup)⟩
        · obtain ⟨Je, hJe, hee⟩ := hQe d hd hve
          exact ⟨Je, hJe, embedded_trans hemb hee⟩
        · obtain ⟨Jg, hJg, heg⟩ := hQg d hd hvg
          exact ⟨Jg, hJg, embedded_trans hemb heg⟩
      · exact hQe
    · intro kv hkv d hd hv
      obtain ⟨L, hL0, hkvL⟩ := List.mem_flatten.mp hkv
      obtain ⟨J0, hJ0, hg0⟩ := full_reach φ hwf k L (hL L hL0) kv hkvL d hd hv
      have hmem : (d, J0) ∈ (Ls.map (pureAdvanceW φ)).flatten :=
        List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨L, hL0, rfl⟩, hJ0⟩
      obtain ⟨J, hJ, hg⟩ := hgrowM (d, J0) hmem
      exact ⟨J, hJ, embedded_of_grown' (Grown.trans hg0 hg)⟩
  rintro ⟨d, B⟩ hB
  obtain ⟨kv, hkv, hd, hv⟩ := advance_origin φ _ d B hB
  obtain ⟨J, hJ, _⟩ := hQ kv hkv d hd hv
  refine ⟨(d, J), hJ, rfl, branch_union φ hwf k _ hA d J ?_ B hB⟩
  intro kv' hkv' hd' hv'
  obtain ⟨J', hJ', he'⟩ := hQ kv' hkv' d hd' hv'
  rw [key_unique _ hM.1.1 d J J' hJ hJ']
  exact he'

-- ============================================================
-- Branch lines
-- ============================================================

/-- The branch of `P` at line `j`. -/
def bline (P : List NodeId) (j : Nat) : PureLine :=
  branchSteps φ P j 0 (restrictLine P 0 (pureInit φ))

theorem branchSteps_add (P : List NodeId) : ∀ (a b : Nat) (k : Int) (L : PureLine),
    branchSteps φ P (a + b) k L = branchSteps φ P b (k + a) (branchSteps φ P a k L) := by
  intro a
  induction a with
  | zero => intro b k L; simp [branchSteps]
  | succ a ih =>
    intro b k L
    have h1 : a + 1 + b = (a + b) + 1 := by omega
    rw [h1]
    show branchSteps φ P (a + b) (k + 1) (restrictLine P (k + 1) (pureAdvanceW φ L)) =
      branchSteps φ P b (k + ((a + 1 : Nat) : Int)) (branchSteps φ P a (k + 1) (restrictLine P (k + 1) (pureAdvanceW φ L)))
    rw [ih b (k + 1)]
    have h2 : k + 1 + (a : Int) = k + ((a + 1 : Nat) : Int) := by omega
    rw [h2]

theorem branchSteps_one (P : List NodeId) (k : Int) (L : PureLine) :
    branchSteps φ P 1 k L = restrictLine P (k + 1) (pureAdvanceW φ L) := rfl

theorem bline_succ (P : List NodeId) (j : Nat) :
    bline φ P (j + 1) = restrictLine P ((j : Int) + 1) (pureAdvanceW φ (bline φ P j)) := by
  unfold bline
  rw [branchSteps_add φ P j 1, branchSteps_one]
  simp

theorem lineInv_bline (hwf : WF φ) (P : List NodeId) (j : Nat) : LineInv φ j (bline φ P j) := by
  have h0 := LineInv_init φ hwf
  have h := (branchSteps_embedded φ hwf P j 0 (restrictLine P 0 (pureInit φ)) (pureInit φ)
    (lineInv_restrict φ P 0 0 _ h0) h0
    (fun kv hkv => ⟨kv, (List.mem_filter.mp hkv).1, rfl, embedded_refl kv.2⟩)).1
  simpa [bline] using h

theorem branchRun_eq_bline (P : List NodeId) : branchRun φ P = bline φ P (stepCount φ - 1).toNat := rfl

-- restricting by one more pin

theorem restrictLine_append (P : List NodeId) (r : NodeId) (j : Int) (L : PureLine) :
    restrictLine (P ++ [r]) j L = restrictLine [r] j (restrictLine P j L) := by
  unfold restrictLine
  rw [List.filter_filter]
  apply List.filter_congr
  intro kv _
  simp [List.all_append, Bool.and_comm]

theorem restrictLine_other (r : NodeId) (j : Int) (hj : r.step ≠ j) (L : PureLine) :
    restrictLine [r] j L = L := by
  unfold restrictLine
  apply List.filter_eq_self.mpr
  intro kv _
  simp [hj]

theorem branchSteps_congr (P P' : List NodeId) : ∀ (n : Nat) (k : Int) (L : PureLine),
    (∀ j, k < j → ∀ L', restrictLine P' j L' = restrictLine P j L') →
    branchSteps φ P' n k L = branchSteps φ P n k L := by
  intro n
  induction n with
  | zero => intro k L _; rfl
  | succ n ih =>
    intro k L h
    show branchSteps φ P' n (k + 1) (restrictLine P' (k + 1) (pureAdvanceW φ L)) =
      branchSteps φ P n (k + 1) (restrictLine P (k + 1) (pureAdvanceW φ L))
    rw [h (k + 1) (by omega)]
    exact ih (k + 1) _ (fun j hj => h j (by omega))

/-- Before and at the step of the new pin, the branch of `P ++ [r]` is the branch of `P` restricted at
that step. -/
theorem bline_append (P : List NodeId) (r : NodeId) (k : Nat) (hr : r.step = k) :
    ∀ j, j ≤ k → bline φ (P ++ [r]) j = restrictLine [r] j (bline φ P j) := by
  intro j
  induction j with
  | zero =>
    intro _
    show restrictLine (P ++ [r]) 0 (pureInit φ) = restrictLine [r] 0 (restrictLine P 0 (pureInit φ))
    exact restrictLine_append P r 0 _
  | succ j ih =>
    intro hj
    rw [bline_succ, bline_succ, ih (by omega), restrictLine_other r j (by omega), restrictLine_append]
    simp

theorem bline_key_step (hwf : WF φ) (P : List NodeId) (j : Nat) (kv : NodeId × GPathM)
    (h : kv ∈ bline φ P j) : kv.1.step = j :=
  mapNodes_step φ j kv.1 ((lineInv_bline φ hwf P j).1.2 kv h).onMap

/-- **The branch of `P ++ [x.1]`, for an entry `x` of the branch of `P` at line `k`, is the branch of
`P` run from the piece of that line with `x`'s key.** -/
theorem branchRun_append (hwf : WF φ) (P : List NodeId) (k : Nat) (hk : k ≤ (stepCount φ - 1).toNat)
    (x : NodeId × GPathM) (hx : x ∈ bline φ P k) :
    branchRun φ (P ++ [x.1]) =
      branchSteps φ P ((stepCount φ - 1).toNat - k) k (restrictLine [x.1] k (bline φ P k)) := by
  have hxs := bline_key_step φ hwf P k x hx
  rw [branchRun_eq_bline]
  unfold bline
  have hsplit : (stepCount φ - 1).toNat = k + ((stepCount φ - 1).toNat - k) := by omega
  rw [hsplit, branchSteps_add]
  have hb := bline_append φ P x.1 k hxs k (Nat.le_refl _)
  unfold bline at hb
  simp only [Int.zero_add] at hb ⊢
  rw [hb]
  have hsub : k + ((stepCount φ - 1).toNat - k) - k = (stepCount φ - 1).toNat - k := by omega
  rw [hsub]
  apply branchSteps_congr
  intro j hj L'
  rw [restrictLine_append, restrictLine_other x.1 j (by omega)]

-- ============================================================
-- A valid branch splits
-- ============================================================

/-- **A valid branch splits at any step.** If the branch of `P` reaches `K` valid, some entry `x` of
its line `k` has a branch `P ++ [x.1]` that reaches `K` valid on its own. -/
theorem split_branch (hwf : WF φ) (hS : SendDistrib φ) (hR : ReviewDistrib φ) (P : List NodeId)
    (K : NodeId) (k : Nat) (hk : k ≤ (stepCount φ - 1).toNat) (hb : BranchValid φ P K) :
    ∃ x ∈ bline φ P k, BranchValid φ (P ++ [x.1]) K := by
  let L := bline φ P k
  have hL : LineInv φ k L := lineInv_bline φ hwf P k
  let piece : NodeId × GPathM → PureLine := fun x => restrictLine [x.1] k L
  let S : Nat → PureLine := fun n => branchSteps φ P n k L
  let PC : NodeId × GPathM → Nat → PureLine := fun x n => branchSteps φ P n k (piece x)
  let T : Nat → PureLine := fun n => mergeL (L.map (fun x => PC x n)).flatten []
  have hstep : ∀ (n : Nat) (M : PureLine),
      branchSteps φ P (n + 1) k M = restrictLine P (k + n + 1) (pureAdvanceW φ (branchSteps φ P n k M)) := by
    intro n M
    rw [branchSteps_add φ P n 1, branchSteps_one]
  -- the invariant, one line at a time
  have inv : ∀ n : Nat, LineInv φ (k + n) (S n) ∧ (∀ x ∈ L, LineInv φ (k + n) (PC x n)) ∧
      LineEmb (S n) (T n) := by
    intro n
    induction n with
    | zero =>
      have hp : ∀ x ∈ L, LineInv φ k (piece x) := fun x _ => lineInv_restrict φ [x.1] k k L hL
      refine ⟨by simpa [S, branchSteps] using hL, fun x hx => by simpa [PC, branchSteps] using hp x hx, ?_⟩
      have hxs : ∀ kv ∈ (L.map (fun x => PC x 0)).flatten, StateOkF φ k kv ∧ MInv φ kv.2 := by
        intro kv hkv
        obtain ⟨M, hM, hkv'⟩ := List.mem_flatten.mp hkv
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hM
        have := hp x hx
        exact ⟨this.1.2 kv hkv', this.2 kv hkv'⟩
      have hg := (mergeL_grows φ k _ [] (lineInv_nil φ k) hxs).2
      intro kv hkv
      have hin : kv ∈ (L.map (fun x => PC x 0)).flatten :=
        List.mem_flatten.mpr ⟨PC kv 0, List.mem_map.mpr ⟨kv, hkv, rfl⟩,
          List.mem_filter.mpr ⟨hkv, by simp⟩⟩
      obtain ⟨J, hJ, hgJ⟩ := hg kv hin
      exact ⟨(kv.1, J), hJ, rfl, embedded_of_grown' hgJ⟩
    | succ n ih =>
      obtain ⟨hSn, hPCn, hemb⟩ := ih
      have hcast : (k : Int) + ((n + 1 : Nat) : Int) = ((k : Int) + (n : Int)) + 1 := by omega
      have hSn' : S (n + 1) = restrictLine P ((k : Int) + (n : Int) + 1) (pureAdvanceW φ (S n)) := hstep n L
      have hPCn' : ∀ x, PC x (n + 1) =
          restrictLine P ((k : Int) + (n : Int) + 1) (pureAdvanceW φ (PC x n)) := fun x => hstep n (piece x)
      refine ⟨?_, fun x hx => ?_, ?_⟩
      · rw [hSn', hcast]
        exact lineInv_restrict φ P _ _ _ (LineInv_pureAdvanceW φ hwf _ _ hSn)
      · rw [hPCn' x, hcast]
        exact lineInv_restrict φ P _ _ _ (LineInv_pureAdvanceW φ hwf _ _ (hPCn x hx))
      · -- the merge of the pieces, as a line
        have hxs : ∀ kv ∈ (L.map (fun x => PC x n)).flatten, StateOkF φ (k + n) kv ∧ MInv φ kv.2 := by
          intro kv hkv
          obtain ⟨M, hM, hkv'⟩ := List.mem_flatten.mp hkv
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hM
          exact ⟨(hPCn x hx).1.2 kv hkv', (hPCn x hx).2 kv hkv'⟩
        have hTn : LineInv φ (k + n) (T n) := lineInv_mergeL φ _ _ [] (lineInv_nil φ _) hxs
        have e1 := lineEmb_advance φ hwf _ _ _ hSn hTn hemb
        have e2 := lineEmb_advance_merge φ hwf hS _ (L.map (fun x => PC x n))
          (fun M hM => by obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hM; exact hPCn x hx)
        -- restricting commutes with the merge
        let p : NodeId → Bool := fun d => P.all (fun r => r.step != ((k : Int) + (n : Int) + 1) || d == r)
        have hT : T (n + 1) = (mergeL ((L.map (fun x => PC x n)).map (pureAdvanceW φ)).flatten []).filter
            (fun kv => p kv.1) := by
          have hmap : (L.map (fun x => PC x (n + 1))) =
              ((L.map (fun x => PC x n)).map (pureAdvanceW φ)).map (fun M => M.filter (fun kv => p kv.1)) := by
            simp only [List.map_map]
            apply List.map_congr_left
            intro x _
            simp only [Function.comp]
            rw [hPCn' x]
            rfl
          show mergeL (L.map (fun x => PC x (n + 1))).flatten [] = _
          rw [hmap, filter_flatten']
          have := mergeL_filter p ((L.map (fun x => PC x n)).map (pureAdvanceW φ)).flatten [] List.nodup_nil
          simpa using this
        rintro ⟨d, B⟩ hB
        rw [hSn'] at hB
        have hB1 : (d, B) ∈ pureAdvanceW φ (S n) := (List.mem_filter.mp hB).1
        have hpd : p d = true := (List.mem_filter.mp hB).2
        obtain ⟨kv1, hkv1, hk1, he1⟩ := e1 (d, B) hB1
        obtain ⟨kv2, hkv2, hk2, he2⟩ := e2 kv1 hkv1
        refine ⟨kv2, ?_, hk2.trans hk1, embedded_trans he1 he2⟩
        rw [hT]
        refine List.mem_filter.mpr ⟨hkv2, ?_⟩
        have : kv2.1 = d := hk2.trans hk1
        rw [this]
        exact hpd
  -- read the invariant at the last line
  let N := (stepCount φ - 1).toNat
  obtain ⟨hSN, hPCN, hembN⟩ := inv (N - k)
  have hSrun : branchRun φ P = S (N - k) := by
    rw [branchRun_eq_bline]
    show bline φ P N = branchSteps φ P (N - k) k L
    unfold bline
    have hsplit : k + (N - k) = N := by omega
    have := branchSteps_add φ P k (N - k) 0 (restrictLine P 0 (pureInit φ))
    rw [hsplit] at this
    rw [this, Int.zero_add]
    rfl
  obtain ⟨kvb, hkvb, hkey, hvb⟩ := hb
  rw [hSrun] at hkvb
  obtain ⟨kvT, hkvT, hkeyT, heT⟩ := hembN kvb hkvb
  -- the reader's review of the merged state is valid
  have hxsN : ∀ kv ∈ (L.map (fun x => PC x (N - k))).flatten,
      StateOkF φ (k + (N - k : Nat)) kv ∧ MInv φ kv.2 := by
    intro kv hkv
    obtain ⟨M, hM, hkv'⟩ := List.mem_flatten.mp hkv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hM
    exact ⟨(hPCN x hx).1.2 kv hkv', (hPCN x hx).2 kv hkv'⟩
  have hTN : LineInv φ (k + (N - k : Nat)) (T (N - k)) := lineInv_mergeL φ _ _ [] (lineInv_nil φ _) hxsN
  have mb := hSN.2 kvb hkvb
  have mf := hTN.2 kvT hkvT
  have hRB : ReadableAgg (filterAllAgg kvb.2 []) := ⟨kvb.2, [], mb.rctx, rfl⟩
  have hsB := AnchoredSurvive.SMP_filterAllAgg kvb.2 mb.smp mb.rctx.shape.notroot []
  have hpB := AggInvariants.PMS_filterAllAgg kvb.2 [] mb.pms
  have hnB := AggInvariants.SN_filterAllAgg kvb.2 [] mb.sn
  have heBG := embedded_filterAllAgg kvb.2 kvT.2 [] heT mb.rctx.nodup hRB hvb hsB hpB hnB mf.smp
    mf.rctx.shape.notroot
  have hvT : isValid (rev kvT.2) = true := isValid_of_embedded heBG hvb
  -- the review of a merge is valid only if the review of one of its pieces is
  let Q : NodeId → GPathM → Prop := fun key G => isValid (rev G) = true →
    ∃ x ∈ L, ∃ G', (key, G') ∈ PC x (N - k) ∧ isValid (rev G') = true
  have hQ : ∀ kv ∈ T (N - k), Q kv.1 kv.2 := by
    refine mergeL_inv φ _ Q ?_ _ [] (lineInv_nil φ _) hxsN (fun kv hkv => absurd hkv List.not_mem_nil) ?_
    · intro key e g hse hsg hme hmg hQe hQg
      unfold doJoin
      split
      · intro hv
        rcases hR _ key e g hse hsg hme hmg hv with hve | hvg
        · exact hQe hve
        · exact hQg hvg
      · exact hQe
    · intro kv hkv hv
      obtain ⟨M, hM, hkv'⟩ := List.mem_flatten.mp hkv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hM
      exact ⟨x, hx, kv.2, hkv', hv⟩
  obtain ⟨x, hx, G', hG', hvG'⟩ := hQ kvT hkvT hvT
  refine ⟨x, hx, ⟨(kvT.1, G'), ?_, hkeyT.trans hkey, hvG'⟩⟩
  rw [branchRun_append φ hwf P k hk x hx]
  exact hG'

-- ============================================================
-- No borrowing, and the verdict
-- ============================================================

theorem pinOneByOne_step (g : GPathM) : ∀ P, (pinOneByOne g P).current_step = g.current_step := by
  intro P
  induction P generalizing g with
  | nil => rfl
  | cons q rest ih =>
    show (pinOneByOne (filterAllAgg g [q]) rest).current_step = g.current_step
    rw [ih, (pruned_filterAllAgg g [q]).step_eq]

/-- **`NoBorrow` from the two equations.** -/
theorem noBorrow_of_distrib (hwf : WF φ) (hS : SendDistrib φ) (hR : ReviewDistrib φ) (K : NodeId) :
    NoBorrow φ K := by
  intro P G hG hb hch
  have hGstep : G.current_step = stepCount φ := (ReaderAggRun.pureRunW_state φ hwf (K, G) hG).2.1
  have hGp : (pinOneByOne (filterAllAgg G []) P).current_step = stepCount φ := by
    rw [pinOneByOne_step, (pruned_filterAllAgg G []).step_eq, hGstep]
  obtain ⟨k, hkr, hck⟩ := List.any_eq_true.mp hch
  have hk0 := mem_intRange_lower hkr
  have hk1 := mem_intRange_upper hkr
  have hkN : k.toNat ≤ (stepCount φ - 1).toNat := by omega
  obtain ⟨x, hx, hbx⟩ := split_branch φ hwf hS hR P K k.toNat hkN hb
  have hxs : x.1.step = k := by
    have := bline_key_step φ hwf P k.toNat x hx
    omega
  -- the pinned state stays valid, so the pinned step keeps a global owner carrying `x.1`
  have hvq := valid_of_branchValid φ hwf K G hG (P ++ [x.1]) hbx
  rw [pinOneByOne_append] at hvq
  have hstep' : (filterAllAgg (pinOneByOne (filterAllAgg G []) P) [x.1]).current_step = stepCount φ := by
    rw [(pruned_filterAllAgg (pinOneByOne (filterAllAgg G []) P) [x.1]).step_eq, hGp]
  obtain ⟨q, hq, hqs⟩ := gowner_of_isValid _ hvq k hk0 (by rw [hstep']; omega)
  have hq1 : q ∈ ([x.1].foldl filterRequire (pinOneByOne (filterAllAgg G []) P)).gowners :=
    (reviewOk_reviewAgg.pruned ([x.1].foldl filterRequire (pinOneByOne (filterAllAgg G []) P))).gowners_sub q hq
  simp only [List.foldl_cons, List.foldl_nil, filterRequire, List.mem_filter] at hq1
  have hqid : q.id = x.1 := by
    have h2 := hq1.2
    have hne : (q.id.step != x.1.step) = false := by rw [hqs, hxs]; exact bne_self_eq_false k
    rw [hne, Bool.false_or] at h2
    exact eq_of_beq h2
  refine ⟨k, hk0, by rw [hGp]; omega, hck, q, List.mem_filter.mpr ⟨hq1.1, beq_iff_eq.mpr hqs⟩, ?_⟩
  rw [hqid]
  exact hbx

/-- **The Improves verdict from one global equation.** If sends and the reader's review distribute
over joins, a valid final state of the machine gives a model of `φ`. -/
theorem sat_of_distrib (hwf : WF φ) (hS : SendDistrib φ) (hR : ReviewDistrib φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ) (hv : isValid (filterAllAgg kv.2 []) = true) :
    Satisfiable φ :=
  sat_of_noBorrow φ hwf kv hkv hv (noBorrow_of_distrib φ hwf hS hR kv.1)

/-- info: 'AbsSat.GraphPath.Model.SendDistrib.split_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms split_branch

/-- info: 'AbsSat.GraphPath.Model.SendDistrib.sat_of_distrib' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_distrib


end AbsSat.GraphPath.Model.SendDistrib
