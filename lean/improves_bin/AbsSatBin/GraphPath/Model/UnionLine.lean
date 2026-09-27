-- lean/improves_bin/AbsSatBin/GraphPath/Model/UnionLine.lean
import AbsSatBin.GraphPath.Model.AnchorPiece

/-!
# The union of a line, as a state, and the induction of LUA

`AnchorPiece` reduces the reader to anchored locality of line unions (LUA) and growth. To prove LUA by induction on the
line, the union of the states of a line is built as a state (`lineU`, by `join`) and carries the reader's context; below
its top it sits inside the union of the previous line (every field of every node comes, through the driver, from a
state of the previous line).

* **Provenance of every field** (`SrcF`, `srcF_pureAdvance`): the owners, parents and sons of a node of a state of line
  `n+1` come from `upFiltering` of states of line `n` (the owners part is `LineSem.Src`).
-/

namespace AbsSatBin.GraphPath.Model.UnionLine

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.CliqueTri (Clique)
open AbsSatBin.GraphPath.Model.CertDescent (Wit)
open AbsSatBin.GraphPath.Model.FiltCert
open AbsSatBin.GraphPath.Model.AnchorPiece

variable (φ : Cnf)

-- ============================================================
-- Provenance of a field through the driver
-- ============================================================

/-- A field of a node joins as a union: every element comes from one side. -/
def JoinsAsUnion (sel : PNodeM → List PathNodeId) : Prop :=
  ∀ g₁ g₂ pid n, (join g₁ g₂).node? pid = some n → ∀ w ∈ sel n,
    (∃ m, g₁.node? pid = some m ∧ w ∈ sel m) ∨ (∃ m, g₂.node? pid = some m ∧ w ∈ sel m)

theorem owners_joins : JoinsAsUnion PNodeM.owners := fun g₁ g₂ pid n h w hw => join_owners_source g₁ g₂ pid n h w hw
theorem parents_joins : JoinsAsUnion PNodeM.parents := fun g₁ g₂ pid n h w hw =>
  join_parents_source g₁ g₂ pid n h w hw
theorem sons_joins : JoinsAsUnion PNodeM.sons := fun g₁ g₂ pid n h w hw => join_sons_source g₁ g₂ pid n h w hw

/-- Every element of the field `sel` of a node of `kv'` comes from `upFiltering` of a state of `line`. -/
def SrcF (sel : PNodeM → List PathNodeId) (line : PureLine) (kv' : NodeId × GPathM) : Prop :=
  ∀ r nr, kv'.2.node? r = some nr → ∀ q ∈ sel nr, ∃ kv ∈ line, kv'.1 ∈ sonsOfMap φ kv.1 ∧
    isValid (upF φ kv.2 kv'.1) = true ∧ ∃ n, (upF φ kv.2 kv'.1).node? r = some n ∧ q ∈ sel n

theorem srcF_insertPure (sel : PNodeM → List PathNodeId) (hj : JoinsAsUnion sel) (line : PureLine) (acc : PureLine)
    (hacc : ∀ kv' ∈ acc, SrcF φ sel line kv') (kv : NodeId × GPathM) (hkv : kv ∈ line) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true) :
    ∀ kv' ∈ insertPure acc d (upF φ kv.2 d), SrcF φ sel line kv' := by
  have hnew : SrcF φ sel line (d, upF φ kv.2 d) := fun r nr hr q hq => ⟨kv, hkv, hd, hv, nr, hr, hq⟩
  intro kv' hkv'
  unfold insertPure at hkv'
  cases hf : acc.find? (fun kv => kv.1 == d) with
  | none =>
    rw [hf] at hkv'
    rcases List.mem_append.mp hkv' with h | h
    · exact hacc kv' h
    · rw [List.mem_singleton.mp h]; exact hnew
  | some e =>
    rw [hf] at hkv'
    obtain ⟨kv0, hkv0, hEq⟩ := List.mem_map.mp hkv'
    have he : e ∈ acc := List.mem_of_find?_eq_some hf
    have hekey : e.1 = d := eq_of_beq (List.find?_some (p := fun kv : NodeId × GPathM => kv.1 == d) hf)
    by_cases hk0 : kv0.1 = d
    · have hEq' : kv' = (d, doJoin e.2 (upF φ kv.2 d)) := by
        rw [← hEq]; simp only [beq_iff_eq.mpr hk0, if_true]
      rw [hEq']
      have hes : SrcF φ sel line (d, e.2) := by have := hacc e he; rw [← hekey]; exact this
      unfold doJoin
      cases hok : okJoin e.2 (upF φ kv.2 d) with
      | false => exact hes
      | true =>
        intro r nr hr q hq
        rcases hj _ _ r nr hr q hq with ⟨m, hm, hqm⟩ | ⟨m, hm, hqm⟩
        · exact hes r m hm q hqm
        · exact hnew r m hm q hqm
    · have hEq' : kv' = kv0 := by
        rw [← hEq]
        have : (kv0.1 == d) = false := by
          cases h : (kv0.1 == d) with
          | false => rfl
          | true => exact absurd (eq_of_beq h) hk0
        simp only [this]; rfl
      rw [hEq']; exact hacc kv0 hkv0

theorem srcF_sendAll (sel : PNodeM → List PathNodeId) (hj : JoinsAsUnion sel) (line : PureLine)
    (kv : NodeId × GPathM) (hkv : kv ∈ line) :
    ∀ (ds : List NodeId), (∀ d ∈ ds, d ∈ sonsOfMap φ kv.1) → ∀ acc, (∀ kv' ∈ acc, SrcF φ sel line kv') →
      ∀ kv' ∈ ds.foldl (sendTo φ kv.2) acc, SrcF φ sel line kv' := by
  intro ds
  induction ds with
  | nil => intro _ acc h; exact h
  | cons d ds ih =>
    intro hds acc hacc
    simp only [List.foldl_cons]
    refine ih (fun d' h => hds d' (List.mem_cons_of_mem _ h)) _ ?_
    unfold sendTo
    split
    · rename_i hv
      exact srcF_insertPure φ sel hj line acc hacc kv hkv d (hds d List.mem_cons_self) hv
    · exact hacc

/-- **Every field of every node of the next line comes from `upFiltering` of states of this one.** -/
theorem srcF_pureAdvance (sel : PNodeM → List PathNodeId) (hj : JoinsAsUnion sel) (line : PureLine) :
    ∀ kv' ∈ pureAdvance φ line, SrcF φ sel line kv' := by
  unfold pureAdvance
  have main : ∀ (l : PureLine), (∀ kv ∈ l, kv ∈ line) → ∀ acc, (∀ kv' ∈ acc, SrcF φ sel line kv') →
      ∀ kv' ∈ l.foldl (fun next kv => sendAll φ kv next) acc, SrcF φ sel line kv' := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons kv l ih =>
      intro hl acc hacc
      simp only [List.foldl_cons]
      refine ih (fun x h => hl x (List.mem_cons_of_mem _ h)) _ ?_
      unfold sendAll
      exact srcF_sendAll φ sel hj line kv (hl kv List.mem_cons_self) _ (fun d h => h) acc hacc
  exact main line (fun _ h => h) [] (fun _ h => absurd h List.not_mem_nil)

-- ============================================================
-- The context a union of states keeps
-- ============================================================

/-- **The reader's context of a union**: what `join` keeps. -/
structure UCtx (g : GPathM) : Prop where
  rc : Reader.RCtx g
  sym : Threaded.OwnSymmetric g
  cut : SymMachine.CutClosed g
  ab : KernelReader.OwnAbove g
  sa : Sons.SAbove g
  valid : isValid g = true
  ker : Kernel.Kernel g

/-- `join` does not look at the second state's `map_parent`: realigned, the two states pass `okJoin`. -/
theorem okJoin_realign (a b : GPathM) (hcs : a.current_step = b.current_step) (ha : isValid a = true)
    (hb : isValid b = true) : okJoin a { b with map_parent := a.map_parent } = true := by
  unfold okJoin
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨hcs, trivial⟩, ha⟩, hb⟩

theorem rctx_realign (b : GPathM) (m : Option NodeId) (h : Reader.RCtx b) : Reader.RCtx { b with map_parent := m } :=
  { oos := h.oos, snn := h.snn, gn := h.gn, shape := ⟨h.shape.pn, h.shape.pbelow, h.shape.notroot⟩,
    rootz := h.rootz, pmp := h.pmp, gpmp := h.gpmp, ownb := h.ownb, below := h.below, nodup := h.nodup }

theorem kernel_realign (b : GPathM) (m : Option NodeId) (h : Kernel.Kernel b) :
    Kernel.Kernel { b with map_parent := m } :=
  ⟨h.gow, h.gn, h.own, h.valid, h.sym, h.linkP, h.linkS, h.pair, h.nbrP, h.nbrS⟩

theorem isValid_join (a b : GPathM) (ha : isValid a = true) : isValid (join a b) = true := by
  unfold isValid at *
  refine List.all_eq_true.mpr (fun k hk => ?_)
  obtain ⟨q, hq, e⟩ := List.any_eq_true.mp (List.all_eq_true.mp ha k hk)
  exact List.any_eq_true.mpr ⟨q, List.mem_append_left _ hq, e⟩

theorem below_join (a b : GPathM) (ha : Reader.RCtx a) (hb : Reader.RCtx b) (hcs : a.current_step = b.current_step) :
    ∀ n ∈ (join a b).nodes, n.id.id.step < (join a b).current_step := by
  intro n hn
  have hnd := Reader.nodup_join a b ha.nodup hb.nodup
  have hnn : (join a b).node? n.id = some n := node?_of_mem hnd n hn
  show n.id.id.step < a.current_step
  rcases join_node?_source a b n.id n hnn with h | h
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
    have := ha.below m (List.mem_of_find?_eq_some hm)
    rw [node?_id_eq _ _ m hm] at this; exact this
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
    have := hb.below m (List.mem_of_find?_eq_some hm)
    rw [node?_id_eq _ _ m hm, ← hcs] at this; exact this

/-- **`join` of two states with the reader's context and the same step keeps it.** -/
theorem UCtx_join (a b : GPathM) (ha : UCtx a) (hb : UCtx b) (hcs : a.current_step = b.current_step) :
    UCtx (join a b) := by
  have hok := okJoin_realign a b hcs ha.valid hb.valid
  have hrc : Reader.RCtx (join a b) :=
    { oos := SelfOwn.OOS_join a b ha.rc.oos hb.rc.oos
      snn := SelfOwn.SNN_join a b ha.rc.snn hb.rc.snn
      gn := GownersNodes.GN_join a b ha.rc.gn hb.rc.gn
      shape := ⟨Parents.PN_join a b ha.rc.shape.pn hb.rc.shape.pn,
        Parents.PBelow_join a b ha.rc.shape.pbelow hb.rc.shape.pbelow,
        Parents.NotRoot_join a b ha.rc.shape.notroot hb.rc.shape.notroot⟩
      rootz := Sons.RootAtZero_join a b ha.rc.rootz hb.rc.rootz
      pmp := ParentId.PMP_join a b ha.rc.pmp hb.rc.pmp
      gpmp := ParentId.GPMP_join a b ha.rc.gpmp hb.rc.gpmp
      ownb := SelfOwn.OwnBelow_join a { b with map_parent := a.map_parent } hok ha.rc.ownb hb.rc.ownb
      below := below_join a b ha.rc hb.rc hcs
      nodup := Reader.nodup_join a b ha.rc.nodup hb.rc.nodup }
  have hk := KernelUp.kernel_join (A := a) (B := { b with map_parent := a.map_parent }) ha.ker
    (kernel_realign b _ hb.ker) hok
  exact
    { rc := hrc
      sym := SymMachine.sym_join a { b with map_parent := a.map_parent } hok ha.rc (rctx_realign b _ hb.rc) ha.sym
        hb.sym ha.cut hb.cut
      cut := SymMachine.cutClosed_join a { b with map_parent := a.map_parent } hok ha.rc (rctx_realign b _ hb.rc)
        ha.cut hb.cut
      ab := KernelReader.ownAbove_join a b ha.ab hb.ab
      sa := Sons.SAbove_join a b ha.sa hb.sa
      valid := isValid_join a b ha.valid
      ker := hk }

/-- info: 'AbsSatBin.GraphPath.Model.UnionLine.UCtx_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UCtx_join

theorem grown_join_right' (a b : GPathM) (hcs : a.current_step = b.current_step) (ha : isValid a = true)
    (hb : isValid b = true) : Grown b (join a b) :=
  have h := grown_join_right a { b with map_parent := a.map_parent } (okJoin_realign a b hcs ha hb)
  ⟨h.step_eq, h.gowners_grown, h.node?_grown⟩

/-- **Folding `join` over states with the context and one step**: the union keeps the context and the step, every
state grows into it, and every node and every element of every field of it comes from one of the states. -/
theorem fold_props (k : Int) : ∀ (rest : PureLine) (acc : GPathM), UCtx acc → acc.current_step = k →
    (∀ x ∈ rest, UCtx x.2 ∧ x.2.current_step = k) →
    UCtx (rest.foldl (fun g x => join g x.2) acc) ∧ (rest.foldl (fun g x => join g x.2) acc).current_step = k ∧
    Grown acc (rest.foldl (fun g x => join g x.2) acc) ∧
    (∀ x ∈ rest, Grown x.2 (rest.foldl (fun g x => join g x.2) acc)) ∧
    (∀ p nu, (rest.foldl (fun g x => join g x.2) acc).node? p = some nu →
      (acc.node? p).isSome ∨ ∃ x ∈ rest, (x.2.node? p).isSome) ∧
    (∀ sel, JoinsAsUnion sel → ∀ p nu, (rest.foldl (fun g x => join g x.2) acc).node? p = some nu → ∀ v ∈ sel nu,
      (∃ m, acc.node? p = some m ∧ v ∈ sel m) ∨ ∃ x ∈ rest, ∃ m, x.2.node? p = some m ∧ v ∈ sel m) := by
  intro rest
  induction rest with
  | nil =>
    intro acc hacc hk _
    refine ⟨hacc, hk, Grown.refl _, fun _ h => absurd h List.not_mem_nil, fun p nu h => Or.inl (by
      simp only [List.foldl_nil] at h; rw [h]; rfl), fun sel _ p nu h v hv => Or.inl ⟨nu, h, hv⟩⟩
  | cons x xs ih =>
    intro acc hacc hk hxs
    simp only [List.foldl_cons]
    obtain ⟨hx, hxk⟩ := hxs x List.mem_cons_self
    have hcs : acc.current_step = x.2.current_step := hk.trans hxk.symm
    have hacc' := UCtx_join acc x.2 hacc hx hcs
    obtain ⟨hU, hUk, hgr, hgrs, hsrc, hsel⟩ := ih (join acc x.2) hacc' hk (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    refine ⟨hU, hUk, (grown_join_left acc x.2).trans hgr, fun y hy => ?_, fun p nu h => ?_, fun sel hj p nu h v hv => ?_⟩
    · rcases List.mem_cons.mp hy with e | hy
      · rw [e]; exact (grown_join_right' acc x.2 hcs hacc.valid hx.valid).trans hgr
      · exact hgrs y hy
    · rcases hsrc p nu h with h1 | ⟨y, hy, h2⟩
      · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h1
        rcases join_node?_source acc x.2 p m hm with h3 | h3
        · exact Or.inl h3
        · exact Or.inr ⟨x, List.mem_cons_self, h3⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h2⟩
    · rcases hsel sel hj p nu h v hv with ⟨m, hm, hvm⟩ | ⟨y, hy, m, hm, hvm⟩
      · rcases hj acc x.2 p m hm v hvm with h3 | ⟨m', hm', hv'⟩
        · exact Or.inl h3
        · exact Or.inr ⟨x, List.mem_cons_self, m', hm', hv'⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, m, hm, hvm⟩

/-- **The union of the states of line `n`**, as a state (`join` of all of them). -/
def lineU (n : Nat) : GPathM :=
  match line φ n with
  | [] => GPathM.initSeed ⟨0, 0⟩ ""
  | kv :: rest => rest.foldl (fun g x => join g x.2) kv.2

/-- **A valid filter of a state with the union context has the reader's context** (`LineSem.filt_ctx`, from the context
instead of reachability). -/
theorem actx_of_uctx (g : GPathM) (hU : UCtx g) (reqs : List NodeId) (hv : isValid (filterAll g reqs) = true) :
    AmbTriCore.ACtx (filterAll g reqs) := by
  have cX : Reader.RCtx (reqs.foldl filterRequire g) :=
    ReaderAgg.RCtx_of_keeps (ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire reqs g) hU.rc
  have abX : KernelReader.OwnAbove (reqs.foldl filterRequire g) := by
    intro n hn; rw [SymMachine.foldl_filterRequire_nodes] at hn; exact hU.ab n hn
  have hk := KernelReader.kernel_of_review _ cX (SymMachine.sym_foldl_filterRequire reqs g hU.sym) abX hv
  have rF := Reader.RCtx_filterAll g hU.rc reqs
  have sa := Sons.SAbove_filterAll g reqs hU.sa
  exact ⟨⟨hk, rF.nodup, rF.oos, rF.shape.pbelow, sa, rF.snn, rF.below⟩, rF⟩

-- ============================================================
-- An old node of a piece, in its source
-- ============================================================

variable (hbd : Bounded φ)
include hbd

/-- **A node of a piece below its top is a node of the source**, with its owners and sons below the top and all its
parents. -/
theorem piece_old (n : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true) (p : PathNodeId) (np : PNodeM)
    (hnp : (upF φ kv.2 d).node? p = some np) (hps : p.id.step ≤ n) :
    ∃ nX, kv.2.node? p = some nX ∧ (∀ v ∈ np.owners, v.id.step ≤ n → v ∈ nX.owners) ∧
      (∀ v ∈ np.parents, v ∈ nX.parents) ∧ (∀ v ∈ np.sons, v.id.step ≤ n → v ∈ nX.sons) := by
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ d) hvF
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ d)
  have hFcs : (filterAll kv.2 (reqOf φ d)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  have hdF : d.step = (filterAll kv.2 (reqOf φ d)).current_step := by rw [hFcs, ← hcs, hdst]
  have hndG := Reader.nodup_addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ) c.pc.nd c.pc.below hdF
  have hPA : Kernel.Below (addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ)) (upF φ kv.2 d) := by
    rcases (upF_shape φ kv.2 d hv).2 with e | e
    · rw [e]; exact ⟨rfl, fun q h => h, fun p n' h => ⟨n', h, fun _ x => x, fun _ x => x, fun _ x => x⟩⟩
    · rw [e]; exact KernelIff.below_filterAll_self _ hndG []
  obtain ⟨nG, hnG, hoG, hpG, hsG⟩ := hPA.node p np hnp
  obtain ⟨nF, hnF, hEq⟩ := addNode_node?_below _ d "" (isProhibited φ) hdF p nG hnG (by rw [hFcs]; omega)
  obtain ⟨nX, hnX, hoX, hpX, hsX⟩ := hb.node p nF hnF
  refine ⟨nX, hnX, fun v hv hvs => ?_, fun v hv => ?_, fun v hv hvs => ?_⟩
  · have := hoG v hv; rw [hEq, upMap_owners] at this
    rcases List.mem_append.mp this with h | h
    · exact hoX v h
    · have := KernelUp.row_step _ d (isProhibited φ) hdF v (gainedOwners_subset _ _ _ _ v h)
      rw [hFcs] at this; omega
  · have := hpG v hv; rw [hEq, upMap_parents] at this; exact hpX v this
  · have := hsG v hv; rw [hEq, upMap_sons] at this
    rcases List.mem_append.mp this with h | h
    · exact hsX v h
    · have := KernelUp.row_step _ d (isProhibited φ) hdF v ((KernelUp.mem_gainedSons _ _ _ _ v).mp h).1
      rw [hFcs] at this; omega

/-- info: 'AbsSatBin.GraphPath.Model.UnionLine.piece_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms piece_old

/-- **A node of a state of line `n+1` below the top is a node of states of line `n`, field by field** (each element of
each field, and the node itself, in some state of line `n`). -/
theorem line_old (n : Nat) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (p : PathNodeId) (np : PNodeM)
    (hnp : kv'.2.node? p = some np) (hps : p.id.step ≤ n) :
    (∃ kv ∈ line φ n, ∃ nX, kv.2.node? p = some nX) ∧
    (∀ v ∈ np.owners, v.id.step ≤ n → ∃ kv ∈ line φ n, ∃ nX, kv.2.node? p = some nX ∧ v ∈ nX.owners) ∧
    (∀ v ∈ np.parents, ∃ kv ∈ line φ n, ∃ nX, kv.2.node? p = some nX ∧ v ∈ nX.parents) ∧
    (∀ v ∈ np.sons, v.id.step ≤ n → ∃ kv ∈ line φ n, ∃ nX, kv.2.node? p = some nX ∧ v ∈ nX.sons) := by
  have hkv'' := hkv'
  rw [line_succ] at hkv''
  refine ⟨?_, fun v hv hvs => ?_, fun v hv => ?_, fun v hv hvs => ?_⟩
  · obtain ⟨kv, hkv, hd, hv, n0, hn0⟩ := (src_pureAdvance φ (line φ n) kv' hkv'').1 p np hnp
    obtain ⟨nX, hnX, _⟩ := piece_old φ hbd n kv hkv kv'.1 hd hv p n0 hn0 hps
    exact ⟨kv, hkv, nX, hnX⟩
  · obtain ⟨kv, hkv, hd, hv', n0, hn0, hvn⟩ := srcF_pureAdvance φ _ owners_joins (line φ n) kv' hkv'' p np hnp v hv
    obtain ⟨nX, hnX, ho, _, _⟩ := piece_old φ hbd n kv hkv kv'.1 hd hv' p n0 hn0 hps
    exact ⟨kv, hkv, nX, hnX, ho v hvn hvs⟩
  · obtain ⟨kv, hkv, hd, hv', n0, hn0, hvn⟩ := srcF_pureAdvance φ _ parents_joins (line φ n) kv' hkv'' p np hnp v hv
    obtain ⟨nX, hnX, _, hpa, _⟩ := piece_old φ hbd n kv hkv kv'.1 hd hv' p n0 hn0 hps
    exact ⟨kv, hkv, nX, hnX, hpa v hvn⟩
  · obtain ⟨kv, hkv, hd, hv', n0, hn0, hvn⟩ := srcF_pureAdvance φ _ sons_joins (line φ n) kv' hkv'' p np hnp v hv
    obtain ⟨nX, hnX, _, _, hso⟩ := piece_old φ hbd n kv hkv kv'.1 hd hv' p n0 hn0 hps
    exact ⟨kv, hkv, nX, hnX, hso v hvn hvs⟩

/-- info: 'AbsSatBin.GraphPath.Model.UnionLine.line_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms line_old

/-- **A state of a line has the union context.** -/
theorem uctx_line (n : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) :
    UCtx kv.2 ∧ kv.2.current_step = (n : Int) + 1 := by
  have hok : StateOk φ n kv := (lineOk φ n).2 kv hkv
  have hreach := MapReachable.reachable_of_mapReachable φ hbd _ hok.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreach
  obtain ⟨hs, hc⟩ := SymMachine.symInv_reachable (reqOf φ) (isProhibited φ) _ hreach hok.valid
  exact ⟨{ rc := Reader.RCtx_reachable (reqOf φ) (isProhibited φ) _ hnd hreach
           sym := hs
           cut := hc
           ab := KernelReader.ownAbove_reachable (reqOf φ) (isProhibited φ) _ hreach
           sa := KernelSplit.SAbove_reachable (reqOf φ) (isProhibited φ) _ hreach
           valid := hok.valid
           ker := KernelUp.kernel_reachable (reqOf φ) (isProhibited φ) _ hreach hok.valid }, hok.step⟩

/-- **The union of a non-empty line**: context, step, every state grows into it, and every node and field element of it
comes from a state. -/
theorem lineU_props (n : Nat) (kv0 : NodeId × GPathM) (hkv0 : kv0 ∈ line φ n) :
    UCtx (lineU φ n) ∧ (lineU φ n).current_step = (n : Int) + 1 ∧ (∀ kv ∈ line φ n, Grown kv.2 (lineU φ n)) ∧
    (∀ p nu, (lineU φ n).node? p = some nu → ∃ kv ∈ line φ n, (kv.2.node? p).isSome) ∧
    (∀ sel, JoinsAsUnion sel → ∀ p nu, (lineU φ n).node? p = some nu → ∀ v ∈ sel nu,
      ∃ kv ∈ line φ n, ∃ m, kv.2.node? p = some m ∧ v ∈ sel m) := by
  unfold lineU
  split
  · rename_i h; rw [h] at hkv0; exact absurd hkv0 List.not_mem_nil
  · rename_i kv rest h
    have hin : ∀ x ∈ kv :: rest, x ∈ line φ n := fun x hx => by rw [h]; exact hx
    obtain ⟨hkc, hkk⟩ := uctx_line φ hbd n kv (hin kv List.mem_cons_self)
    obtain ⟨hU, hUk, hgr, hgrs, hsrc, hsel⟩ := fold_props ((n : Int) + 1) rest kv.2 hkc hkk
      (fun x hx => uctx_line φ hbd n x (hin x (List.mem_cons_of_mem _ hx)))
    refine ⟨hU, hUk, fun y hy => ?_, fun p nu hp => ?_, fun sel hj p nu hp v hv => ?_⟩
    · rw [h] at hy
      rcases List.mem_cons.mp hy with e | hy
      · rw [e]; exact hgr
      · exact hgrs y hy
    · rcases hsrc p nu hp with h1 | ⟨y, hy, h2⟩
      · exact ⟨kv, hin kv List.mem_cons_self, h1⟩
      · exact ⟨y, hin y (List.mem_cons_of_mem _ hy), h2⟩
    · rcases hsel sel hj p nu hp v hv with ⟨m, hm, hvm⟩ | ⟨y, hy, m, hm, hvm⟩
      · exact ⟨kv, hin kv List.mem_cons_self, m, hm, hvm⟩
      · exact ⟨y, hin y (List.mem_cons_of_mem _ hy), m, hm, hvm⟩

/-- info: 'AbsSatBin.GraphPath.Model.UnionLine.lineU_props' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lineU_props

-- ============================================================
-- Below the top, inside the union of the previous line
-- ============================================================

/-- `g` below step `n+1` is inside the states of line `n`, field by field. -/
def LowIn (g : GPathM) (n : Nat) : Prop :=
  ∀ p np, g.node? p = some np → p.id.step ≤ n →
    (∃ kv ∈ line φ n, (kv.2.node? p).isSome) ∧
    (∀ v ∈ np.owners, v.id.step ≤ n → ∃ kv ∈ line φ n, ∃ nX, kv.2.node? p = some nX ∧ v ∈ nX.owners) ∧
    (∀ v ∈ np.parents, ∃ kv ∈ line φ n, ∃ nX, kv.2.node? p = some nX ∧ v ∈ nX.parents) ∧
    (∀ v ∈ np.sons, v.id.step ≤ n → ∃ kv ∈ line φ n, ∃ nX, kv.2.node? p = some nX ∧ v ∈ nX.sons)

omit hbd in
theorem lowIn_of_old (n : Nat) (g : GPathM)
    (h : ∀ p np, g.node? p = some np → p.id.step ≤ n →
      (∃ kv ∈ line φ n, ∃ nX, kv.2.node? p = some nX) ∧
      (∀ v ∈ np.owners, v.id.step ≤ n → ∃ kv ∈ line φ n, ∃ nX, kv.2.node? p = some nX ∧ v ∈ nX.owners) ∧
      (∀ v ∈ np.parents, ∃ kv ∈ line φ n, ∃ nX, kv.2.node? p = some nX ∧ v ∈ nX.parents) ∧
      (∀ v ∈ np.sons, v.id.step ≤ n → ∃ kv ∈ line φ n, ∃ nX, kv.2.node? p = some nX ∧ v ∈ nX.sons)) :
    LowIn φ g n := by
  intro p np hnp hps
  obtain ⟨⟨kv, hkv, nX, hnX⟩, h2, h3, h4⟩ := h p np hnp hps
  exact ⟨⟨kv, hkv, by rw [hnX]; rfl⟩, h2, h3, h4⟩

/-- **A state of line `n+1` is inside line `n` below its top.** -/
theorem lowIn_line (n : Nat) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) : LowIn φ kv'.2 n :=
  lowIn_of_old φ n _ (fun p np hnp hps => line_old φ hbd n kv' hkv' p np hnp hps)

/-- **The union of line `n+1` is inside line `n` below its top.** -/
theorem lowIn_lineU (n : Nat) (kv0 : NodeId × GPathM) (hkv0 : kv0 ∈ line φ (n + 1)) : LowIn φ (lineU φ (n + 1)) n := by
  obtain ⟨_, _, _, hsrc, hsel⟩ := lineU_props φ hbd (n + 1) kv0 hkv0
  intro p np hnp hps
  refine ⟨?_, fun v hv hvs => ?_, fun v hv => ?_, fun v hv hvs => ?_⟩
  · obtain ⟨kv', hkv', h⟩ := hsrc p np hnp
    obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp h
    exact (lowIn_line φ hbd n kv' hkv' p nq hnq hps).1
  · obtain ⟨kv', hkv', m, hm, hvm⟩ := hsel _ owners_joins p np hnp v hv
    exact (lowIn_line φ hbd n kv' hkv' p m hm hps).2.1 v hvm hvs
  · obtain ⟨kv', hkv', m, hm, hvm⟩ := hsel _ parents_joins p np hnp v hv
    exact (lowIn_line φ hbd n kv' hkv' p m hm hps).2.2.1 v hvm
  · obtain ⟨kv', hkv', m, hm, hvm⟩ := hsel _ sons_joins p np hnp v hv
    exact (lowIn_line φ hbd n kv' hkv' p m hm hps).2.2.2 v hvm hvs

/-- **The truncation of a filtered state inside line `n` below its top sits below the union of line `n`.** -/
theorem trunc_below (n : Nat) (g : GPathM) (hlow : LowIn φ g n) (hnd : NodupIds g)
    (hgcs : g.current_step = (n : Int) + 2) (S : List NodeId) (cF : AmbTriCore.ACtx (filterAll g S))
    (kv0 : NodeId × GPathM) (hkv0 : kv0 ∈ line φ n) :
    Kernel.Below (lineU φ n) (Trunc.trunc (filterAll g S)) := by
  obtain ⟨hU, hUcs, hgrU, _, _⟩ := lineU_props φ hbd n kv0 hkv0
  have hbF := KernelIff.below_filterAll_self g hnd S
  have hFcs : (filterAll g S).current_step = (n : Int) + 2 := by rw [← hbF.step, hgcs]
  -- a node of the truncation is a node of the union, and it is the same node for every field
  have inU : ∀ p, (∃ kv ∈ line φ n, (kv.2.node? p).isSome) → ∃ nU, (lineU φ n).node? p = some nU := by
    intro p ⟨kv, hkv, h⟩
    obtain ⟨nX, hnX⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨nU, hnU, _⟩ := (hgrU kv hkv).node?_grown p nX hnX
    exact ⟨nU, hnU⟩
  refine ⟨?_, fun q hq => ?_, fun p nk hnk => ?_⟩
  · show (lineU φ n).current_step = (filterAll g S).current_step - 1
    rw [hUcs, hFcs]; omega
  · obtain ⟨hqF, hqs⟩ := List.mem_filter.mp hq
    have hqs' : q.id.step ≠ (filterAll g S).current_step - 1 := by
      intro h; simp [h] at hqs
    obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (cF.pc.ker.gn q hqF)
    have hr := CertFix.step_range cF.pc q nq hnq
    rw [hFcs] at hr hqs'
    obtain ⟨ng, hng, _, _, _⟩ := hbF.node q nq hnq
    obtain ⟨nU, hnU⟩ := inU q (hlow q ng hng (by omega)).1
    exact hU.ker.gow q nU hnU
  · obtain ⟨nF, hnF, hps, rfl⟩ := Trunc.trunc_node?_some _ p nk hnk
    have hpr := CertFix.step_range cF.pc p nF hnF
    rw [hFcs] at hpr hps
    obtain ⟨ng, hng, hog, hpg, hsg⟩ := hbF.node p nF hnF
    obtain ⟨h1, h2, h3, h4⟩ := hlow p ng hng (by omega)
    obtain ⟨nU, hnU⟩ := inU p h1
    have land : ∀ kv ∈ line φ n, ∀ nX, kv.2.node? p = some nX → ∃ n'', (lineU φ n).node? p = some n'' ∧
        (∀ v ∈ nX.owners, v ∈ n''.owners) ∧ (∀ v ∈ nX.parents, v ∈ n''.parents) ∧ (∀ v ∈ nX.sons, v ∈ n''.sons) :=
      fun kv hkv nX hnX => (hgrU kv hkv).node?_grown p nX hnX
    refine ⟨nU, hnU, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨hvF, hvs⟩ := (Trunc.mem_cutTop_owners _ _ v).mp hv
      obtain ⟨nv, hnv⟩ := Option.isSome_iff_exists.mp (cF.pc.ker.gn v (cF.pc.ker.own p nF hnF v hvF))
      have hvr := CertFix.step_range cF.pc v nv hnv
      rw [hFcs] at hvr hvs
      obtain ⟨kv, hkv, nX, hnX, hvX⟩ := h2 v (hog v hvF) (by omega)
      obtain ⟨n'', hn'', ho'', _, _⟩ := land kv hkv nX hnX
      rw [hnU] at hn''; cases hn''; exact ho'' v hvX
    · obtain ⟨kv, hkv, nX, hnX, hvX⟩ := h3 v (hpg v hv)
      obtain ⟨n'', hn'', _, hp'', _⟩ := land kv hkv nX hnX
      rw [hnU] at hn''; cases hn''; exact hp'' v hvX
    · obtain ⟨hvF, hvs⟩ := (Trunc.mem_cutTop_sons _ _ v).mp hv
      have hvst := cF.pc.sa nF (List.mem_of_find?_eq_some hnF) v hvF
      rw [node?_id_eq _ _ nF hnF] at hvst
      rw [hFcs] at hvs
      obtain ⟨kv, hkv, nX, hnX, hvX⟩ := h4 v (hsg v hvF) (by omega)
      obtain ⟨n'', hn'', _, _, hs''⟩ := land kv hkv nX hnX
      rw [hnU] at hn''; cases hn''; exact hs'' v hvX

/-- info: 'AbsSatBin.GraphPath.Model.UnionLine.trunc_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms trunc_below

end AbsSatBin.GraphPath.Model.UnionLine
