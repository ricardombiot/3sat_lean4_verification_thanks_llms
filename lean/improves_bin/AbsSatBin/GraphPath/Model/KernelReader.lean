-- lean/improves_bin/AbsSatBin/GraphPath/Model/KernelReader.lean
import AbsSatBin.GraphPath.Model.Kernel

/-!
# Every valid state of the reader is a kernel, and `NoDeadEnd` is a statement about kernels

* **`OwnAbove`**: every table entry sits at a step `≥ 0`. It holds on every state the machine builds
  (`ownAbove_reachable`) and survives every narrowing.
* **`kernel_of_review`**: a valid review of a state with the reader's context, symmetric tables and
  `OwnAbove` is a `Kernel`. Each field comes from the review's fixpoint: the cut (`CutClosed`), the
  links (`Bridge.linksInOwners_review` and symmetry), the pair rule (`PairInactive`), and the
  coherence with the parents' and sons' tables (`review_owners_coherent_parents`/`_sons`).
* **`kernel_readPins`**: so every valid state the reader visits is a kernel.
* **`KernelSplit`**: at every valid state the reader visits, some node of the first choice has a
  valid kernel below the state that agrees with it. **`NoDeadEnd ⇐ KernelSplit`**
  (`Kernel.isValid_filterAll_of_kernel`), and with it the reader decides `φ`.

So the open core is now a statement about kernels alone: **a kernel with a choice between two bits
contains a covering sub-kernel for one of them.**
-/

namespace AbsSatBin.GraphPath.Model.KernelReader

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Threaded (OwnSymmetric)
open AbsSatBin.GraphPath.Model.Reader (RCtx)
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

-- ============================================================
-- Table entries sit at steps ≥ 0
-- ============================================================

def OwnAbove (g : GPathM) : Prop := ∀ n ∈ g.nodes, ∀ q ∈ n.owners, 0 ≤ q.id.step

theorem ownAbove_of_pruned {g g' : GPathM} (hpr : Pruned g g') (h : OwnAbove g) : OwnAbove g' := by
  intro n hn q hq
  obtain ⟨m, hm, _, ho, _⟩ := hpr.nodes_derived n hn
  exact h m hm q (ho q hq)

theorem ownAbove_addNode (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
    (hd : d.step = g.current_step) (hcs : 0 ≤ g.current_step) (hgn : GownersNodes.GN g)
    (hsnn : SelfOwn.SNN g) (h : OwnAbove g) : OwnAbove (addNode g d title forb) := by
  intro n hn q hq
  rw [addNode_nodes] at hn
  rcases List.mem_append.mp hn with h1 | h1
  · obtain ⟨n0, hn0, rfl⟩ := List.mem_map.mp h1
    rw [upMap_owners] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact h n0 hn0 q hq
    · rw [mapId_of_mem_newRowIds g d forb q (List.mem_filter.mp hq).1, hd]; exact hcs
  · obtain ⟨pid, hpid, rfl⟩ := (mem_newRow_iff g d title forb _).mp h1
    rw [rowNode_owners] at hq
    unfold rowOwners at hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨m, hm, hmid⟩ := hgn q (List.contains_iff_mem.mp (List.mem_filter.mp hq).2)
      rw [← hmid]; exact hsnn m hm
    · rw [List.mem_singleton.mp hq, mapId_of_mem_newRowIds g d forb pid hpid, hd]; exact hcs

theorem ownAbove_join (g₁ g₂ : GPathM) (h₁ : OwnAbove g₁) (h₂ : OwnAbove g₂) :
    OwnAbove (join g₁ g₂) := by
  intro n hn q hq
  rw [GownersNodes.join_nodes] at hn
  rcases List.mem_append.mp hn with h1 | h1
  · obtain ⟨n1, hn1, rfl⟩ := List.mem_map.mp h1
    split at hq
    · next m hm =>
      rcases List.mem_append.mp hq with hq | hq
      · exact h₁ n1 hn1 q hq
      · exact h₂ m (List.mem_of_find?_eq_some hm) q (List.mem_filter.mp hq).1
    · exact h₁ n1 hn1 q hq
  · exact h₂ n (List.mem_filter.mp h1).1 q hq

section
variable (reqOf : NodeId → List NodeId) (forb : PathNodeId → Bool)

theorem ownAbove_reachable (g : GPathM) (h : Reachable reqOf forb g) : OwnAbove g := by
  induction h with
  | seed d title hstep _ =>
    have he : initSeed d title = addNode empty d title noForb := by
      simp only [initSeed, up, skipsWindow_noForb, Bool.false_eq_true, if_false]
      rfl
    rw [he]
    exact ownAbove_addNode empty d title noForb hstep (Int.le_refl 0) (fun _ h => by cases h)
      (fun _ h => by cases h) (fun _ h => by cases h)
  | up g d title hstep _ _ hr ih =>
    have hpr := pruned_filterAll g (reqOf d)
    have abF := ownAbove_of_pruned hpr ih
    have cF := Reader.RCtx_filterAll g
      (Reader.RCtx_reachable reqOf forb g (Reader.NodupIds_reachable reqOf forb g hr) hr) (reqOf d)
    have hmok := MachineOk_of_pruned hpr (Certifies.MachineOk_reachable reqOf forb g hr)
    have hdF : d.step = (filterAll g (reqOf d)).current_step := by rw [hpr.step_eq]; exact hstep
    have hA := ownAbove_addNode _ d title forb hdF hmok.1 cF.gn cF.snn abF
    show OwnAbove (up (filterAll g (reqOf d)) d title forb)
    simp only [up]
    split
    · split
      · exact ownAbove_of_pruned (pruned_review _) hA
      · exact hA
    · exact abF
  | join g₁ g₂ _ _ _ ih₁ ih₂ => exact ownAbove_join g₁ g₂ ih₁ ih₂

end

-- ============================================================
-- The union of the neighbours' tables
-- ============================================================

theorem mem_unionFold_inv (g : GPathM) (ids : List PathNodeId) :
    ∀ (acc : List PathNodeId) (q : PathNodeId), q ∈ ids.foldl (unionStep g) acc →
      q ∈ acc ∨ ∃ c ∈ ids, ∃ nc, g.node? c = some nc ∧ q ∈ nc.owners := by
  induction ids with
  | nil => intro acc q h; exact Or.inl h
  | cons c cs ih =>
    intro acc q h
    simp only [List.foldl_cons] at h
    rcases ih _ q h with h | ⟨c', hc', nc, hnc, hq⟩
    · unfold unionStep at h
      cases hn : g.node? c with
      | none => rw [hn] at h; exact Or.inl h
      | some p =>
        rw [hn] at h
        rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨c, List.mem_cons_self, p, hn, h⟩
    · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', nc, hnc, hq⟩

theorem mem_unionOwnersOf_inv (g : GPathM) (ids : List PathNodeId) (q : PathNodeId)
    (h : q ∈ unionOwnersOf g ids) : ∃ c ∈ ids, ∃ nc, g.node? c = some nc ∧ q ∈ nc.owners := by
  rcases mem_unionFold_inv g ids [] q h with h | h
  · cases h
  · exact h

-- ============================================================
-- A valid review is a kernel
-- ============================================================

/-- **A valid review of a symmetric state with the reader's context is a kernel.** -/
theorem kernel_of_review (X : GPathM) (c : RCtx X) (hs : OwnSymmetric X) (hab : OwnAbove X)
    (hv : isValid (review X) = true) : Kernel (review X) := by
  have cr : RCtx (review X) := Reader.RCtx_filterAll X c []
  have hsym : OwnSymmetric (review X) :=
    PairInactive.OwnSymmetric_review X (SymMachine.revOk_foldl X c hs []) hv
  have habr : OwnAbove (review X) := ownAbove_of_pruned (pruned_review X) hab
  have hcc := SymMachine.cutClosed_review X hv
  have hso := SelfOwn.SelfOwned_of_OOS X hv cr.oos cr.snn cr.below
  have hown : ∀ p n, (review X).node? p = some n → ∀ v ∈ n.owners, v ∈ (review X).gowners := by
    intro p n hn v hv'
    have hm := List.mem_of_find?_eq_some hn
    exact hcc n hm v hv' (hasStepEntry_of_isValid _ hv _ (habr n hm v hv') (cr.ownb n hm v hv'))
  have hgn : ∀ q ∈ (review X).gowners, ((review X).node? q).isSome = true := by
    intro q hq
    obtain ⟨m, hm, hmid⟩ := cr.gn q hq
    rw [← hmid, node?_of_mem cr.nodup m hm]; rfl
  have hnode : ∀ p n, (review X).node? p = some n → ∀ v ∈ n.owners,
      ∃ nv, (review X).node? v = some nv :=
    fun p n hn v hv' => Option.isSome_iff_exists.mp (hgn v (hown p n hn v hv'))
  have hvalid : ∀ p n, (review X).node? p = some n → isValidNode (review X) n = true :=
    fun p n hn => review_node_valid X hv p n hn
  have hentry : ∀ p n, (review X).node? p = some n → ∀ k, 0 ≤ k → k < (review X).current_step →
      ∃ r ∈ n.owners, r.id.step = k := by
    intro p n hn k h0 h1
    have hok := ((isValidNode_iff _ n).mp (hvalid p n hn)).1
    obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hok k (mem_intRange h0 (by omega)))
    exact ⟨r, hr, eq_of_beq hrs⟩
  have hlinks := Bridge.linksInOwners_review X hv
  -- a node's own neighbours carry every entry of its table
  have hnbr : ∀ p n, (review X).node? p = some n → ∀ (nbs : List PathNodeId), nbs ≠ [] →
      (∀ c ∈ nbs, c ∈ n.owners) →
      intersectOwners n.owners (unionOwnersOf (review X) nbs) = n.owners → ∀ v ∈ n.owners,
      ∃ c ∈ nbs, ∃ nc, (review X).node? c = some nc ∧ v ∈ nc.owners := by
    intro p n hn nbs hne hin hcoh v hv'
    have hm := List.mem_of_find?_eq_some hn
    have hkeep := List.filter_eq_self.mp hcoh v hv'
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨nc, hnc⟩ := hnode p n hn c (hin c hc)
    obtain ⟨t, ht, hts⟩ := hentry c nc hnc v.id.step (habr n hm v hv') (cr.ownb n hm v hv')
    have hse : hasStepEntry (unionOwnersOf (review X) nbs) v.id.step = true :=
      List.any_eq_true.mpr ⟨t, mem_unionOwnersOf _ _ c nc t hc hnc ht, beq_iff_eq.mpr hts⟩
    rw [hse] at hkeep
    have hcont : (unionOwnersOf (review X) nbs).contains v = true := by
      rw [Bool.not_true, Bool.false_or] at hkeep; exact hkeep
    exact mem_unionOwnersOf_inv _ _ v (List.contains_iff_mem.mp hcont)
  refine ⟨?_, hgn, hown, hvalid, hsym, ?_, ?_, ?_, ?_, ?_⟩
  · intro p n hn
    have hm := List.mem_of_find?_eq_some hn
    have hid : n.id = p := node?_id_eq _ p n hn
    have hs' : hasStepEntry (review X).gowners p.id.step = true := by
      rw [← hid]; exact hasStepEntry_of_isValid _ hv _ (cr.snn n hm) (cr.below n hm)
    exact hcc n hm p (hso p n hn) hs'
  · intro p n hn c hc
    have hco := (hlinks p n hn).1 c hc
    obtain ⟨nc, hnc⟩ := hnode p n hn c hco
    exact ⟨hco, nc, hnc, hsym p n c nc hn hnc hco⟩
  · intro p n hn c hc
    have hco := (hlinks p n hn).2 c hc
    obtain ⟨nc, hnc⟩ := hnode p n hn c hco
    exact ⟨hco, nc, hnc, hsym p n c nc hn hnc hco⟩
  · intro p n w nw hn hnw hw k h0 h1
    by_cases hwp : w = p
    · subst hwp
      rw [hn] at hnw; cases hnw
      obtain ⟨r, hr, hrs⟩ := hentry w n hn k h0 h1
      exact ⟨r, hr, hr, hrs⟩
    · have hfix := PairInactive.pairFixed_of_reviewPass_eq (review X) hv (reviewPass_review X hv)
      have hok := PairInactive.pairOk_of_fixed _ hfix p n w hn hw hwp nw hnw
      unfold pairShares at hok
      have hk : (!hasStepEntry n.owners k || !hasStepEntry nw.owners k ||
          (ownersAt n.owners k).any (fun r => nw.owners.contains r)) = true :=
        List.all_eq_true.mp hok k (mem_intRange h0 (by omega))
      obtain ⟨r1, hr1, hs1⟩ := hentry p n hn k h0 h1
      obtain ⟨r2, hr2, hs2⟩ := hentry w nw hnw k h0 h1
      have e1 : hasStepEntry n.owners k = true := List.any_eq_true.mpr ⟨r1, hr1, beq_iff_eq.mpr hs1⟩
      have e2 : hasStepEntry nw.owners k = true := List.any_eq_true.mpr ⟨r2, hr2, beq_iff_eq.mpr hs2⟩
      cases ha : (ownersAt n.owners k).any (fun r => nw.owners.contains r) with
      | false => rw [e1, e2, ha] at hk; cases hk
      | true =>
        obtain ⟨r, hr, hrw⟩ := List.any_eq_true.mp ha
        obtain ⟨hr1, hrs⟩ := List.mem_filter.mp hr
        exact ⟨r, hr1, List.contains_iff_mem.mp hrw, eq_of_beq hrs⟩
  · intro p n hn hstep
    have hm := List.mem_of_find?_eq_some hn
    have hid : n.id = p := node?_id_eq _ p n hn
    have hk : p.id.step ∈ intRange 1 ((review X).current_step - 1) :=
      mem_intRange hstep (by have := cr.below n hm; rw [hid] at this; exact Int.le_sub_one_of_lt this)
    have hline : p ∈ ((review X).line p.id.step).map (·.id) :=
      List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨hm, beq_iff_eq.mpr (by rw [hid])⟩, hid⟩
    have hcoh := review_owners_coherent_parents X hv _ hk p hline n hn
    have hnr : p.parent_id ≠ none := by
      have := cr.shape.notroot n hm (by rw [hid]; exact Int.lt_of_lt_of_le Int.zero_lt_one hstep)
      rwa [hid] at this
    have hpar : n.parents ≠ [] := by
      rcases ((isValidNode_iff _ n).mp (hvalid p n hn)).2.1 with hr | hr
      · rw [hid] at hr; exact absurd (Option.isNone_iff_eq_none.mp hr) hnr
      · exact hr
    exact hnbr p n hn n.parents hpar (hlinks p n hn).1 hcoh
  · intro p n hn hstep
    have hm := List.mem_of_find?_eq_some hn
    have hid : n.id = p := node?_id_eq _ p n hn
    have hk : p.id.step ∈ intRange 0 ((review X).current_step - 2) :=
      mem_intRange (by have := cr.snn n hm; rw [hid] at this; exact this) hstep
    have hline : p ∈ ((review X).line p.id.step).map (·.id) :=
      List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨hm, beq_iff_eq.mpr (by rw [hid])⟩, hid⟩
    have hcoh := review_owners_coherent_sons X hv _ hk p hline n hn
    have hsons : n.sons ≠ [] := by
      rcases ((isValidNode_iff _ n).mp (hvalid p n hn)).2.2 with hl | hl
      · rw [hid] at hl
        have e := eq_of_beq hl
        rw [e] at hstep
        exact absurd hstep (Int.not_le.mpr (Int.sub_lt_sub_left (by decide : (1 : Int) < 2) _))
      · exact hl
    exact hnbr p n hn n.sons hsons (hlinks p n hn).2 hcoh

-- ============================================================
-- Every valid reader state is a kernel
-- ============================================================

variable (φ : Cnf)

/-- **Every valid state the reader visits is a kernel.** -/
theorem kernel_readPins (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (ps : List NodeId) (g : GPathM) (hp : ReadPins (filterAll kv.2 []) ps g) (hv : isValid g = true) :
    Kernel g := by
  have hzero : (0 : Int) < stepCount φ := by simp only [stepCount]; omega
  have hok := Decision.stateOk_pureRun φ hzero kv hkv
  have hreach := MapReachable.reachable_of_mapReachable φ hbd kv.2 hok.reach
  obtain ⟨cm, sm⟩ := SymMachine.machine_ctx φ hbd kv hkv
  have abm := ownAbove_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  cases hp with
  | start => exact kernel_of_review kv.2 cm sm abm hv
  | pin g' k q ps' hp' hv' _ _ _ =>
    have c₀ := Reader.RCtx_filterAll kv.2 cm []
    have cg' := NoDeadEnd.rctx_readPins _ c₀ ps' g' hp'
    have sg' := SymMachine.sym_readFirst φ hbd kv hkv g'
      (NoDeadEnd.readFirst_of_readPins _ ps' g' hp') hv'
    have abg' := ownAbove_of_pruned
      (Pruned.trans (pruned_filterAll kv.2 []) (NoDeadEnd.pruned_readPins _ ps' g' hp')) abm
    have cX : RCtx ([q.id].foldl filterRequire g') :=
      ReaderAgg.RCtx_of_keeps (ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire [q.id] g') cg'
    have abX : OwnAbove ([q.id].foldl filterRequire g') := by
      intro n hn; rw [SymMachine.foldl_filterRequire_nodes] at hn; exact abg' n hn
    exact kernel_of_review _ cX (SymMachine.sym_foldl_filterRequire [q.id] g' sg') abX hv

-- ============================================================
-- `NoDeadEnd` as a statement about kernels
-- ============================================================

/-- **`KernelSplit`**: at every valid state the reader visits, some node of the first choice has a
valid kernel below the state that agrees with it. -/
def KernelSplit (g₀ : GPathM) : Prop :=
  ∀ g, ReadFirst g₀ g → isValid g = true → ∀ k, firstChoice g = some k →
    ∃ q ∈ ownersAt g.gowners k, ∃ h, Kernel h ∧ isValid h = true ∧ Below g h ∧
      ∀ x ∈ h.gowners, x.id.step = q.id.step → x.id = q.id

theorem noDeadEnd_of_kernelSplit (g₀ : GPathM) (hks : KernelSplit g₀) : NoDeadEnd.NoDeadEnd g₀ := by
  intro g hF hv k hf
  obtain ⟨q, hq, h, hk, hvh, hb, hpin⟩ := hks g hF hv k hf
  exact ⟨q, hq, isValid_filterAll_of_kernel hk hvh hb [q.id]
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hpin)⟩

/-- **The reader decides `φ` under `KernelSplit`.** -/
theorem readerVerdictW_iff_of_kernelSplit (hbd : Bounded φ)
    (hks : ∀ kv ∈ pureRun φ, KernelSplit (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  NoDeadEnd.readerVerdictW_iff_of_noDeadEnd φ hbd
    (fun kv hkv => noDeadEnd_of_kernelSplit _ (hks kv hkv))

/-- info: 'AbsSatBin.GraphPath.Model.KernelReader.kernel_readPins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kernel_readPins

/-- info: 'AbsSatBin.GraphPath.Model.KernelReader.readerVerdictW_iff_of_kernelSplit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_kernelSplit

end AbsSatBin.GraphPath.Model.KernelReader
