-- lean/improves_bin/AbsSatBin/GraphPath/Model/UnionLine.lean
import AbsSatBin.GraphPath.Model.AnchorPiece

/-!
# The union of a line, as a state, and the induction of LUA

`AnchorPiece` reduces the reader to anchored locality of line unions (LUA) and growth. To prove LUA by induction on the
line, the union of the states of a line is built as a state (`lineU`, by `join`) and carries the reader's context; below
its top it sits inside the union of the previous line (every field of every node comes, through the driver, from a
state of the previous line).

* **Provenance of every field** (`SrcF`, `srcF_pureAdvance`): the owners, parents and sons of a node of a state of line
  `n+1` come from `upFiltering` of states of line `n` (the owners part is `LineSem.Src`); below the top, from the states
  of line `n` themselves (`piece_old`, `line_old`).
* **The union as a state** (`UCtx`, `UCtx_join`, `lineU`, `lineU_props`): `join` ignores the second state's
  `map_parent`, so the `_join` lemmas give the reader's context of the union; every state grows into it and every field
  element of it comes from a state.
* **Below the top, inside the previous line** (`LowIn`, `trunc_below`): the truncation of a filtered state (a joined
  state, or the union of line `n+1`) sits below the union of line `n`.
* **LUAU by induction** (`luau_zero`, `luau_succ`): an anchored clique with witnesses of the filtered union of a line is
  one of the state of its anchor's key. The step pins the anchor's requirement (**AFU**, the anchored filter in the
  union), gives the anchor's place to a parent (`single_parent`, or **`TopMergeU`** at a merge), goes below to the union
  of the previous line, applies LUAU there, and climbs back with the certificate of `FCert` (`climbE`: the anchor is the
  shift of its parent, a node of the piece).
* **LUAJ from LUAU** (`luaJ_of_luau`), **A1 from A1K and LUAJ** (`anchorF_of_a1k`: the anchor's son in its piece is its
  shift).
* **`readerVerdictW_iff_of_luau`**: with `FCert` and LUAU carried together along the run (`fCert_luau_line`), the reader
  decides under A1K (growth at the top of the truncation), AFU, `TopMergeU`, `TopMergeJ` and AF in the pieces. LUA is no
  longer a hypothesis.
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

-- ============================================================
-- LUA on the union of a line, by induction
-- ============================================================

omit hbd in
/-- A clique with witnesses of a kernel climbs to a state it sits below, which is then valid. -/
theorem good_up {X h : GPathM} (hb : Kernel.Below X h) (hker : Kernel.Kernel h) {Q : List PathNodeId}
    (hQ : Clique h Q) (hW : Wit h Q) : isValid X = true ∧ Clique X Q ∧ Wit X Q := by
  refine ⟨?_, fun p hp => ?_, fun l h0 h1 => ?_⟩
  · unfold isValid
    rw [hb.step]
    refine List.all_eq_true.mpr (fun l hl => ?_)
    have h0 := mem_intRange_lower hl
    have h1 := mem_intRange_upper hl
    obtain ⟨r, nr, hnr, hrs, _⟩ := hW l h0 (by omega)
    exact List.any_eq_true.mpr ⟨r, hb.gow r (hker.gow r nr hnr), beq_iff_eq.mpr hrs⟩
  · obtain ⟨np, hnp, ho⟩ := hQ p hp
    obtain ⟨nx, hnx, hox, _, _⟩ := hb.node p np hnp
    exact ⟨nx, hnx, fun s hs => hox s (ho s hs)⟩
  · obtain ⟨r, nr, hnr, hrs, ho⟩ := hW l h0 (by rw [← hb.step]; exact h1)
    obtain ⟨nx, hnx, hox, _, _⟩ := hb.node r nr hnr
    exact ⟨r, nx, hnx, hrs, fun s hs => hox s (ho s hs)⟩

omit hbd in
/-- **LUAU n**: a clique with witnesses `c :: Q0` of the union of line `n` filtered by `S`, with `c` at the top, is one
of the state of `c`'s key filtered by `S`. -/
def LUAU (n : Nat) : Prop :=
  ∀ S : List NodeId, (∀ p ∈ S, 0 ≤ p.step ∧ p.step ≤ n) → isValid (filterAll (lineU φ n) S) = true →
    ∀ c Q0, Clique (filterAll (lineU φ n) S) (c :: Q0) → Wit (filterAll (lineU φ n) S) (c :: Q0) →
    c.id.step = n → ∀ kv ∈ line φ n, kv.1 = c.id →
      isValid (filterAll kv.2 S) = true ∧ Clique (filterAll kv.2 S) (c :: Q0) ∧ Wit (filterAll kv.2 S) (c :: Q0)

omit hbd in
/-- **AFU n**: in the union of line `n` filtered by `S`, a clique with witnesses with a top member `c` survives the pin
of `c`'s requirement (the anchored filter, AF, in the union: `c` fixes it). -/
def AFU (n : Nat) : Prop :=
  ∀ S : List NodeId, (∀ p ∈ S, 0 ≤ p.step ∧ p.step ≤ n) → isValid (filterAll (lineU φ n) S) = true →
    ∀ c Q0, Clique (filterAll (lineU φ n) S) (c :: Q0) → Wit (filterAll (lineU φ n) S) (c :: Q0) →
    c.id.step = n → ∀ r ∈ reqOf φ c.id,
      isValid (filterAll (lineU φ n) (S ++ [r])) = true ∧ Clique (filterAll (lineU φ n) (S ++ [r])) (c :: Q0) ∧
      Wit (filterAll (lineU φ n) (S ++ [r])) (c :: Q0)

omit hbd in
/-- **TopMergeU n**: in the filtered union of line `n`, a clique with witnesses whose top member comes from a merge hands
itself to one of its parents. -/
def TopMergeU (n : Nat) : Prop :=
  ∀ S : List NodeId, (∀ p ∈ S, 0 ≤ p.step ∧ p.step ≤ n) → isValid (filterAll (lineU φ n) S) = true →
    ∀ c Q0, Clique (filterAll (lineU φ n) S) (c :: Q0) → Wit (filterAll (lineU φ n) S) (c :: Q0) →
    c.id.step = n → (∀ q ∈ Q0, q.id.step < n) →
    ∀ nc, (filterAll (lineU φ n) S).node? c = some nc → (∃ c₁ ∈ nc.parents, ∃ c₂ ∈ nc.parents, c₁ ≠ c₂) →
    ∃ cp ∈ nc.parents, Clique (filterAll (lineU φ n) S) (cp :: Q0) ∧ Wit (filterAll (lineU φ n) S) (cp :: Q0)

omit hbd in
/-- **LUAU at line 0**: the union of line 0 is the seed, the only state. -/
theorem luau_zero : LUAU φ 0 := by
  intro S _ hv c Q0 hQ hW _ kv hkv _
  have hm : mapNodes φ 0 = [⟨0, 0⟩] := mapNodes_fusion φ 0 (Or.inl rfl)
  have h0 : line φ 0 = [(⟨0, 0⟩, GPathM.initSeed ⟨0, 0⟩ "")] := by
    show pureInit φ = _
    unfold pureInit; rw [hm]; rfl
  have hU : lineU φ 0 = GPathM.initSeed ⟨0, 0⟩ "" := by
    unfold lineU; simp only [h0, List.foldl_nil]
  rw [hU] at hv hQ hW
  rw [line_zero φ kv hkv]
  exact ⟨hv, hQ, hW⟩

/-- **A certificate of a source pinned by the requirements and the pins below the top climbs to the filtered piece**,
when the shift of its node at step `n` is a node of the piece (so its window is allowed) and every pin at the top is the
destination. -/
theorem climbE (n : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true)
    (ps : List NodeId) (htop : ∀ r ∈ ps, r.step = (n : Int) + 1 → r = d) (sel : Int → PathNodeId)
    (hsG : ChainSound (filterAll kv.2 (reqOf φ d ++ ps.filter (fun m => decide (m.step ≤ (n : Int))))) sel)
    (hz : ∃ nz, (upF φ kv.2 d).node? (shiftPid (sel n) d) = some nz) :
    ChainSound (filterAll (upF φ kv.2 d) ps) (extend (filterAll kv.2 (reqOf φ d)) d sel) ∧
      (∀ l, l ≤ (n : Int) → extend (filterAll kv.2 (reqOf φ d)) d sel l = sel l) ∧
      extend (filterAll kv.2 (reqOf φ d)) d sel ((n : Int) + 1) = shiftPid (sel n) d := by
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ d)
  have hFcs : (filterAll kv.2 (reqOf φ d)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  have hdF : d.step = (filterAll kv.2 (reqOf φ d)).current_step := by rw [hFcs, ← hcs, hdst]
  have c := filt_ctx φ hbd n kv hok (reqOf φ d) hvF
  have hP : StateOk φ ((n : Int) + 1) (d, upF φ kv.2 d) := StateOk_sent φ n kv hok d hd hv
  have hPcs : (upF φ kv.2 d).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  have hsX : ChainSound kv.2 sel :=
    ChainSound_of_grown (PieceFilter.grown_of_below (KernelIff.below_filterAll_self kv.2 hnd _)) sel hsG
  have hpS := chain_pins kv.2 _ sel hsG
  have hreqs : ∀ req ∈ reqOf φ d, 0 ≤ req.step → req.step < kv.2.current_step → (sel req.step).id = req :=
    fun req hr h0 h1 => hpS req (List.mem_append_left _ hr) h0 h1
  have hmokX : MachineOk kv.2 := ⟨by rw [hok.step]; omega, fun h => by rw [hok.step] at h; omega,
    fun _ => by rw [hok.par]; simp⟩
  have hmok : MachineOk (filterAll kv.2 (reqOf φ d)) := MachineOk_of_pruned (pruned_filterAll _ _) hmokX
  have hpos : 0 < (filterAll kv.2 (reqOf φ d)).current_step := by omega
  have hext : extendPid (filterAll kv.2 (reqOf φ d)) d sel = shiftPid (sel n) d := by
    unfold extendPid; rw [if_pos hpos, hFcs, show (n : Int) + 1 - 1 = n by omega]
  obtain ⟨nz, hnz⟩ := hz
  have hznew := (upF_new φ kv.2 d hdst c hv _ nz hnz (show d.step = kv.2.current_step from hdst)).1
  have hf : isProhibited φ (extendPid (filterAll kv.2 (reqOf φ d)) d sel) = false := by
    rw [hext]; exact not_forb_of_mem_newRowIds _ _ _ _ hznew
  have hsP : ChainSound (upF φ kv.2 d) (extend (filterAll kv.2 (reqOf φ d)) d sel) :=
    ChainSound_upFiltering kv.2 (reqOf φ d) d "" (isProhibited φ) hvF hdF c.pc.below hmok sel hsX hreqs hf
  have hlow : ∀ l, l ≤ (n : Int) → extend (filterAll kv.2 (reqOf φ d)) d sel l = sel l := by
    intro l hl; unfold extend; rw [if_neg (by rw [hFcs]; omega)]
  have htopE : extend (filterAll kv.2 (reqOf φ d)) d sel ((n : Int) + 1) = shiftPid (sel n) d := by
    rw [show (n : Int) + 1 = (filterAll kv.2 (reqOf φ d)).current_step by rw [hFcs], extend_top, hext]
  refine ⟨ChainSound_filterAll _ ps _ hsP (fun r hr h0 h1 => ?_), hlow, htopE⟩
  rw [hPcs] at h1
  by_cases hrt : r.step = (n : Int) + 1
  · rw [hrt, htopE, htop r hr hrt]; rfl
  · rw [hlow r.step (by omega)]
    exact hpS r (List.mem_append_right _ (List.mem_filter.mpr ⟨hr, decide_eq_true (by omega)⟩)) h0
      (by rw [hcs]; omega)

/-- info: 'AbsSatBin.GraphPath.Model.UnionLine.climbE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms climbE

/-- **The step of LUAU.** A clique with witnesses `c :: Q` of the filtered union of line `n+1`, anchored at `c` on the
top, is pinned at `c`'s requirement (AFU); `c` gives its place to a parent `cp` (`parent_or_merge`, `TopMergeU`); the
truncation sits below the union of line `n`, pinned (`trunc_below`); LUAU at `n` puts `cp :: Q₀` in the state of `cp`'s
key, `FCert` gives a certificate there, and it climbs through `up` with `c` (the shift of `cp`, a node of the piece) into
the state of `c`'s key. -/
theorem luau_succ (n : Nat) (hL : LUAU φ n) (hA : AFU φ (n + 1)) (hTM : TopMergeU φ (n + 1))
    (hX : ∀ kv ∈ line φ n, FCert kv.2) : LUAU φ (n + 1) := by
  intro S hS hv c Q hQ hW hcs kv hkv hkey
  have hcs' : c.id.step = (n : Int) + 1 := by rw [hcs]; push_cast; rfl
  obtain ⟨hU, hUcs, hgrU, hsrcU, _⟩ := lineU_props φ hbd (n + 1) kv hkv
  have hUcs' : (lineU φ (n + 1)).current_step = (n : Int) + 2 := by rw [hUcs]; push_cast; omega
  have hbU := KernelIff.below_filterAll_self (lineU φ (n + 1)) hU.rc.nodup S
  have hFcs : (filterAll (lineU φ (n + 1)) S).current_step = (n : Int) + 2 := by rw [← hbU.step, hUcs']
  have cF := actx_of_uctx _ hU S hv
  -- the members below the top
  have hsub0 : ∀ q ∈ c :: Q.filter (fun q => decide (q.id.step ≤ (n : Int))), q ∈ c :: Q := by
    intro q hq
    rcases List.mem_cons.mp hq with e | hq
    · rw [e]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mp hq).1
  obtain ⟨hQ0, hW0⟩ := good_sub hsub0 hQ hW
  have hlow0 : ∀ q ∈ Q.filter (fun q => decide (q.id.step ≤ (n : Int))), q.id.step ≤ n :=
    fun q hq => of_decide_eq_true (List.mem_filter.mp hq).2
  -- pin `c`'s requirement
  have hreqr : ∀ r ∈ reqOf φ c.id, 0 ≤ r.step ∧ r.step ≤ n := fun r hr =>
    ⟨reqOf_nonneg φ hbd c.id r hr, by have := reqOf_backward φ hbd c.id r hr; rw [hcs'] at this; omega⟩
  obtain ⟨hvF', hQ', hW'⟩ : isValid (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id)) = true ∧
      Clique (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id)) (c :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) ∧
      Wit (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id)) (c :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) := by
    have hl := reqOf_length_le_one φ c.id
    cases hr : reqOf φ c.id with
    | nil => rw [List.append_nil]; exact ⟨hv, hQ0, hW0⟩
    | cons r rest =>
      cases rest with
      | cons _ _ => rw [hr] at hl; simp at hl
      | nil => exact hA S hS hv c _ hQ0 hW0 hcs r (by rw [hr]; exact List.mem_cons_self)
  have hS' : ∀ p ∈ S ++ reqOf φ c.id, 0 ≤ p.step ∧ p.step ≤ ((n + 1 : Nat) : Int) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hS p hp
    · exact ⟨(hreqr p hp).1, by have := (hreqr p hp).2; push_cast; omega⟩
  have cF' := actx_of_uctx _ hU _ hvF'
  have hbU' := KernelIff.below_filterAll_self (lineU φ (n + 1)) hU.rc.nodup (S ++ reqOf φ c.id)
  have hF'cs : (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id)).current_step = (n : Int) + 2 := by
    rw [← hbU'.step, hUcs']
  obtain ⟨nc, hnc, _⟩ := hQ' c List.mem_cons_self
  have hcmem := List.mem_of_find?_eq_some hnc
  have hcid : nc.id = c := node?_id_eq _ c nc hnc
  -- a parent `cp` takes `c`'s place
  obtain ⟨cp, hcp, hQc, hWc⟩ : ∃ cp ∈ nc.parents,
      Clique (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id)) (cp :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) ∧
      Wit (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id)) (cp :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) := by
    rcases parent_or_merge cF' c nc hnc (by rw [hcs']; omega) _ hQ' hW' with hm | h
    · exact hTM _ hS' hvF' c _ hQ' hW' hcs (fun q hq => by have := hlow0 q hq; push_cast; omega) nc hnc hm
    · exact h
  have hcps : cp.id.step = (n : Int) := by
    have := cF'.pc.pb nc hcmem cp hcp; rw [hcid, hcs'] at this; omega
  have hparc : some cp.id = c.parent_id := by
    have := cF'.rc.pmp nc hcmem cp hcp; rw [hcid] at this; exact this
  have hgpar : c.gparent_id = cp.parent_id := by
    have := cF'.rc.gpmp.1 nc hcmem cp hcp; rw [hcid] at this; exact this
  -- a state of line `n`
  obtain ⟨ncp, hncp, _⟩ := hQc cp List.mem_cons_self
  obtain ⟨ncpU, hncpU, _, _, _⟩ := hbU'.node cp ncp hncp
  obtain ⟨kv1, hkv1, h1⟩ := hsrcU cp ncpU hncpU
  obtain ⟨n1, hn1⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨⟨kv0, hkv0, _⟩, _⟩ := lowIn_line φ hbd n kv1 hkv1 cp n1 hn1 (by omega)
  -- the truncation, below the union of line `n`, pinned
  have hBK := trunc_below φ hbd n (lineU φ (n + 1)) (lowIn_lineU φ hbd n kv hkv) hU.rc.nodup hUcs' _ cF' kv0 hkv0
  have hkT := Trunc.kernel_trunc cF'.pc.ker cF'.pc.pb cF'.pc.sa cF'.pc.below
  have hBL := Kernel.below_filterAll hkT hBK ((S ++ reqOf φ c.id).filter (fun m => decide (m.step ≤ (n : Int))))
    (fun r hr q hq hqs => LineUnion.gowner_pinned _ _ q (List.mem_filter.mp hq).1 r (List.mem_filter.mp hr).1 hqs)
  have toK : ∀ p np, (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id)).node? p = some np → p.id.step ≤ n →
      (Trunc.trunc (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id))).node? p =
        some (Trunc.cutTop ((filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id)).current_step - 1) np) :=
    fun p np hnp hps' => Trunc.trunc_node?_of _ p np hnp (by rw [hF'cs]; omega)
  have hlowc : ∀ q ∈ cp :: Q.filter (fun q => decide (q.id.step ≤ (n : Int))), q.id.step ≤ n := by
    intro q hq
    rcases List.mem_cons.mp hq with e | hq
    · rw [e, hcps]; exact Int.le_refl _
    · exact hlow0 q hq
  have hKcs : (Trunc.trunc (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id))).current_step = (n : Int) + 1 := by
    show (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id)).current_step - 1 = _; rw [hF'cs]; omega
  have hQK : Clique (Trunc.trunc (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id)))
      (cp :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) := fun p hp => by
    obtain ⟨np, hnp, ho⟩ := hQc p hp
    exact ⟨_, toK p np hnp (hlowc p hp), fun s hs =>
      (Trunc.mem_cutTop_owners _ _ s).mpr ⟨ho s hs, by rw [hF'cs]; have := hlowc s hs; omega⟩⟩
  have hWK : Wit (Trunc.trunc (filterAll (lineU φ (n + 1)) (S ++ reqOf φ c.id)))
      (cp :: Q.filter (fun q => decide (q.id.step ≤ (n : Int)))) := by
    intro l h0 h1
    rw [hKcs] at h1
    obtain ⟨r, nr, hnr, hrs, ho⟩ := hWc l h0 (by rw [hF'cs]; omega)
    exact ⟨r, _, toK r nr hnr (by omega), hrs, fun s hs =>
      (Trunc.mem_cutTop_owners _ _ s).mpr ⟨ho s hs, by rw [hF'cs]; have := hlowc s hs; omega⟩⟩
  obtain ⟨hvL, hQL, hWL⟩ := good_up hBL hkT hQK hWK
  have hS2 : ∀ p ∈ (S ++ reqOf φ c.id).filter (fun m => decide (m.step ≤ (n : Int))), 0 ≤ p.step ∧ p.step ≤ n := by
    intro p hp
    obtain ⟨hp, hle⟩ := List.mem_filter.mp hp
    exact ⟨(hS' p hp).1, of_decide_eq_true hle⟩
  -- the state `Y` of `cp`'s key
  obtain ⟨hUn, _, _, hsrcUn, _⟩ := lineU_props φ hbd n kv0 hkv0
  obtain ⟨nL, hnL, _⟩ := hQL cp List.mem_cons_self
  obtain ⟨nL', hnL', _, _, _⟩ := (KernelIff.below_filterAll_self (lineU φ n) hUn.rc.nodup _).node cp nL hnL
  obtain ⟨Y, hY, hYs⟩ := hsrcUn cp nL' hnL'
  obtain ⟨nY, hnY⟩ := Option.isSome_iff_exists.mp hYs
  have cY := KernelUp.aCtx_line φ hbd n Y hY
  have hYkey : Y.1 = cp.id :=
    (top_entry_key φ hbd n Y hY cp nY hnY cp (TriPinCut.self_own_pc cY.pc cp nY hnY) hcps).symm
  obtain ⟨hvG, hQG, hWG⟩ := hL _ hS2 hvL cp _ hQL hWL hcps Y hY hYkey
  have hYcs : Y.2.current_step = (n : Int) + 1 := ((lineOk φ n).2 Y hY).step
  obtain ⟨sel, hsG, hon⟩ := hX Y hY _ (fun p hp => ⟨(hS2 p hp).1, by rw [hYcs]; have := (hS2 p hp).2; omega⟩)
    hvG _ hQG hWG
  -- `c` lives in the state of its key, and comes from the piece of `Y`
  obtain ⟨ncF, hncF, hcownF⟩ := hQ c List.mem_cons_self
  obtain ⟨ncU, hncU, hoU, _, _⟩ := hbU.node c ncF hncF
  obtain ⟨kv2, hkv2, h2⟩ := hsrcU c ncU hncU
  obtain ⟨n2, hn2⟩ := Option.isSome_iff_exists.mp h2
  have c2 := KernelUp.aCtx_line φ hbd (n + 1) kv2 hkv2
  have hk2 := top_entry_key φ hbd (n + 1) kv2 hkv2 c n2 hn2 c (TriPinCut.self_own_pc c2.pc c n2 hn2) hcs
  have he2 : kv2 = kv := key_inj _ (lineOk φ (n + 1)).1 kv2 hkv2 kv hkv (hk2.symm.trans hkey.symm)
  subst he2
  obtain ⟨Y', hY', hd, hvp, hpY, hent⟩ := StateGrow.top_one_source φ hbd n kv2 hkv2 c n2 hn2 hcs'
  have hY'Y : Y' = Y := key_inj _ (lineOk φ n).1 Y' hY' Y hY
    (by rw [hYkey]; exact Option.some.inj (hpY.symm.trans hparc.symm))
  subst hY'Y
  obtain ⟨nz, hnz, _⟩ := hent c (TriPinCut.self_own_pc c2.pc c n2 hn2)
  have hshift : shiftPid cp kv2.1 = c := by
    unfold shiftPid
    have hwd : c.id = kv2.1 := hk2
    revert hwd hparc hgpar
    cases c with
    | mk ci cpar cg =>
      intro hwd hparc hgpar
      simp only at hwd hparc hgpar
      rw [hwd, hparc, hgpar]
  have hselc : sel n = cp := by rw [← hcps]; exact hon cp List.mem_cons_self
  -- the certificate, pinned as the climb wants it
  have hndY := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ ((lineOk φ n).2 Y' hY').reach)
  have hsY : ChainSound Y'.2 sel :=
    ChainSound_of_grown (PieceFilter.grown_of_below (KernelIff.below_filterAll_self Y'.2 hndY _)) sel hsG
  have hkeyc : reqOf φ kv2.1 = reqOf φ c.id := by rw [hk2]
  have hsG' : ChainSound (filterAll Y'.2 (reqOf φ kv2.1 ++ S.filter (fun m => decide (m.step ≤ (n : Int))))) sel := by
    refine ChainSound_filterAll Y'.2 _ sel hsY (fun r hr h0 h1 => chain_pins Y'.2 _ sel hsG r ?_ h0 h1)
    rcases List.mem_append.mp hr with hr | hr
    · rw [hkeyc] at hr
      exact List.mem_filter.mpr ⟨List.mem_append_right _ hr, decide_eq_true (hreqr r hr).2⟩
    · obtain ⟨hr, hle⟩ := List.mem_filter.mp hr
      exact List.mem_filter.mpr ⟨List.mem_append_left _ hr, hle⟩
  have htopS : ∀ r ∈ S, r.step = (n : Int) + 1 → r = kv2.1 := by
    intro r hr hrs
    have := LineUnion.gowner_pinned _ S c (cF.pc.ker.gow c ncF hncF) r hr (by rw [hcs', hrs])
    rw [← this, hk2]
  obtain ⟨hsP, hlowsel, htopE⟩ := climbE φ hbd n Y' hY' kv2.1 hd hvp S htopS sel hsG'
    ⟨nz, by rw [hselc, hshift]; exact hnz⟩
  -- into the state of `c`'s key
  obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n Y' hY' kv2.1 hd hvp
  have he : (kv2.1, h) = kv2 := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv2 hkv2 rfl
  have hP : StateOk φ ((n : Int) + 1) (kv2.1, upF φ Y'.2 kv2.1) := StateOk_sent φ n Y' ((lineOk φ n).2 Y' hY') kv2.1 hd hvp
  have hndP := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ hP.reach)
  have hsJ : ChainSound (filterAll h S) (extend (filterAll Y'.2 (reqOf φ kv2.1)) kv2.1 sel) := by
    have hsU : ChainSound (upF φ Y'.2 kv2.1) (extend (filterAll Y'.2 (reqOf φ kv2.1)) kv2.1 sel) :=
      ChainSound_of_grown (PieceFilter.grown_of_below (KernelIff.below_filterAll_self _ hndP S)) _ hsP
    exact ChainSound_filterAll h S _ (ChainSound_of_grown hgr _ hsU) (fun r hr h0 h1 =>
      chain_pins (upF φ Y'.2 kv2.1) S _ hsP r hr h0 (by rw [← hgr.step_eq]; exact h1))
  rw [← he]
  have hJcs : (filterAll h S).current_step = (n : Int) + 2 := by
    have := ((lineOk φ (n + 1)).2 _ hmem).step
    rw [(pruned_filterAll _ S).step_eq, this]; push_cast; omega
  exact good_of_chain _ hsJ (c :: Q) (fun q hq => by
    rw [hJcs]
    rcases List.mem_cons.mp hq with e | hq
    · rw [e, hcs', htopE, hselc, hshift]; exact ⟨by omega, by omega, rfl⟩
    · obtain ⟨nq, hnq, _⟩ := hQ q (List.mem_cons_of_mem _ hq)
      have hqr := CertFix.step_range cF.pc q nq hnq
      rw [hFcs] at hqr
      by_cases hqs : q.id.step ≤ (n : Int)
      · refine ⟨hqr.1, by omega, ?_⟩
        rw [hlowsel _ hqs]
        exact hon q (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hq, decide_eq_true hqs⟩))
      · have hqs' : q.id.step = (n : Int) + 1 := by omega
        have hncFm := List.mem_of_find?_eq_some hncF
        have hncFid : ncF.id = c := node?_id_eq _ c ncF hncF
        have hqc : q = c := by
          have := cF.pc.oos ncF hncFm q (hcownF q (List.mem_cons_of_mem _ hq)) (by rw [hncFid, hqs', hcs'])
          rw [hncFid] at this; exact this
        rw [hqc, hcs', htopE, hselc, hshift]; exact ⟨by omega, by omega, rfl⟩)

/-- info: 'AbsSatBin.GraphPath.Model.UnionLine.luau_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms luau_succ

/-- **LUAU gives LUAJ**: the truncated filtered joined state sits below the union of its line, pinned by the
destination's requirements and by `R` below the top (`trunc_below`). -/
theorem luaJ_of_luau (n : Nat) (hL : LUAU φ n) : LUAJ φ n := by
  intro kv' hkv' R hR hv cp Q0 hQK hWK hcps _ kv hkv _ _ hkey
  have hok' : StateOk φ ((n + 1 : Nat) : Int) kv' := (lineOk φ (n + 1)).2 kv' hkv'
  have hreach' := MapReachable.reachable_of_mapReachable φ hbd _ hok'.reach
  have hnd' := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreach'
  have cF := filt_ctx φ hbd _ kv' hok' R hv
  have hbJ := KernelIff.below_filterAll_self kv'.2 hnd' R
  have hcsJ : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hFcs : (filterAll kv'.2 R).current_step = (n : Int) + 2 := by rw [← hbJ.step, hcsJ]
  have hkT := Trunc.kernel_trunc cF.pc.ker cF.pc.pb cF.pc.sa cF.pc.below
  have hKcs : (Trunc.trunc (filterAll kv'.2 R)).current_step = (n : Int) + 1 := by
    show (filterAll kv'.2 R).current_step - 1 = _; rw [hFcs]; omega
  obtain ⟨kvd, hkvd, hdd, hvd, _⟩ : ∃ kv0 ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv0.1 ∧
      isValid (upF φ kv0.2 kv'.1) = true ∧ True := by
    obtain ⟨nc, hnc, _⟩ := hQK cp List.mem_cons_self
    obtain ⟨nF, hnF, _, _⟩ := Trunc.trunc_node?_some _ cp nc hnc
    obtain ⟨nJ, hnJ, _, _, _⟩ := hbJ.node cp nF hnF
    obtain ⟨kv0, hkv0, hd0, hv0, _⟩ := (PieceJoin.join_no_new φ n kv' hkv').1 cp nJ hnJ
    exact ⟨kv0, hkv0, hd0, hv0, trivial⟩
  obtain ⟨_, hdst, hcs, _, _, _⟩ := src_ctx φ hbd n kvd hkvd kv'.1 hdd hvd
  -- a node of the joined state below the top lives in a source, with its entries below the top
  have toSrc : ∀ p nJ, kv'.2.node? p = some nJ → p.id.step ≤ n → ∀ v ∈ nJ.owners, v.id.step ≤ n →
      ∃ kv0 ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv0.1 ∧ isValid (upF φ kv0.2 kv'.1) = true ∧
        ∃ nF0, (filterAll kv0.2 (reqOf φ kv'.1)).node? p = some nF0 ∧ v ∈ nF0.owners := by
    intro p nJ hnJ hps v hv hvs
    obtain ⟨kv0, hkv0, hd0, hv0, n', hn', hvn'⟩ := (PieceJoin.join_no_new φ n kv' hkv').2 p nJ hnJ v hv
    obtain ⟨hok0, hdst0, hcs0, _, hvF0, _⟩ := src_ctx φ hbd n kv0 hkv0 kv'.1 hd0 hv0
    have c0 := filt_ctx φ hbd n kv0 hok0 (reqOf φ kv'.1) hvF0
    obtain ⟨nF0, hnF0, ho0⟩ := upF_old φ kv0.2 kv'.1 hdst0 c0 hv0 p n' hn' (by rw [hcs0]; omega)
    exact ⟨kv0, hkv0, hd0, hv0, nF0, hnF0, ho0 v hvn' (by rw [hcs0]; omega)⟩
  have hreqr : ∀ r ∈ reqOf φ kv'.1, 0 ≤ r.step ∧ r.step ≤ n := fun r hr =>
    ⟨reqOf_nonneg φ hbd kv'.1 r hr, by have := reqOf_backward φ hbd kv'.1 r hr; rw [hdst, hcs] at this; omega⟩
  have hSr : ∀ p ∈ reqOf φ kv'.1 ++ R.filter (fun m => decide (m.step ≤ (n : Int))), 0 ≤ p.step ∧ p.step ≤ n := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hreqr p hp
    · obtain ⟨hp, hle⟩ := List.mem_filter.mp hp
      exact ⟨(hR p hp).1, of_decide_eq_true hle⟩
  have hpinK : ∀ r ∈ reqOf φ kv'.1 ++ R.filter (fun m => decide (m.step ≤ (n : Int))),
      ∀ q ∈ (Trunc.trunc (filterAll kv'.2 R)).gowners, q.id.step = r.step → q.id = r := by
    intro r hr q hq hqs
    have hqF : q ∈ (filterAll kv'.2 R).gowners := (List.mem_filter.mp hq).1
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (cF.pc.ker.gn q hqF)
      obtain ⟨nJ, hnJ, _, _, _⟩ := hbJ.node q nq hnq
      have hqs' : q.id.step ≤ n := by rw [hqs]; exact (hreqr r hr).2
      obtain ⟨kv0, hkv0, hd0, hv0, nF0, hnF0, _⟩ := toSrc q nJ hnJ hqs' q
        (by obtain ⟨nJ', hnJ', hoJ, _, _⟩ := hbJ.node q nq hnq
            rw [hnJ] at hnJ'; cases hnJ'
            exact hoJ q (TriPinCut.self_own_pc cF.pc q nq hnq)) hqs'
      obtain ⟨hok0, _, _, _, hvF0, _⟩ := src_ctx φ hbd n kv0 hkv0 kv'.1 hd0 hv0
      have c0 := filt_ctx φ hbd n kv0 hok0 (reqOf φ kv'.1) hvF0
      exact LineUnion.pinned_entry φ kv0.2 kv'.1 q (c0.pc.ker.gow q nF0 hnF0) r hr hqs
    · exact LineUnion.gowner_pinned kv'.2 R q hqF r (List.mem_filter.mp hr).1 hqs
  have hBK := trunc_below φ hbd n kv'.2 (lowIn_line φ hbd n kv' hkv') hnd' hcsJ R cF kv hkv
  have hBL := Kernel.below_filterAll hkT hBK _ hpinK
  obtain ⟨hvL, hQL, hWL⟩ := good_up hBL hkT hQK hWK
  exact hL _ hSr hvL cp _ hQL hWL hcps kv hkv hkey

/-- info: 'AbsSatBin.GraphPath.Model.UnionLine.luaJ_of_luau' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms luaJ_of_luau

/-- **A state of line `n+1` is pinned at the requirement of its key**: its global owners at a requirement's step name
the requirement (its pieces were filtered by it). -/
theorem line_pinned_req (n : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ line φ (n + 1)) (r : NodeId)
    (hr : r ∈ reqOf φ kv.1) : ∀ q ∈ kv.2.gowners, q.id.step = r.step → q.id = r := by
  intro q hq hqs
  have ck := KernelUp.aCtx_line φ hbd (n + 1) kv hkv
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (ck.pc.ker.gn q hq)
  obtain ⟨kv0, hkv0, hd0, hv0, n0, hn0⟩ := (PieceJoin.join_no_new φ n kv hkv).1 q nq hnq
  obtain ⟨hok0, hdst0, hcs0, _, hvF0, _⟩ := src_ctx φ hbd n kv0 hkv0 kv.1 hd0 hv0
  have c0 := filt_ctx φ hbd n kv0 hok0 (reqOf φ kv.1) hvF0
  have hrs : r.step < kv0.2.current_step := by have := reqOf_backward φ hbd kv.1 r hr; rw [← hdst0]; exact this
  obtain ⟨nF0, hnF0, _⟩ := upF_old φ kv0.2 kv.1 hdst0 c0 hv0 q n0 hn0 (by rw [hqs]; exact hrs)
  exact LineUnion.pinned_entry φ kv0.2 kv.1 q (c0.pc.ker.gow q nF0 hnF0) r hr hqs

/-- **AFU follows from LUAU at the same line**: the state of the anchor's key, filtered by `S`, holds the clique; it is
pinned at the anchor's requirement, so it sits inside the union filtered by `S` and the requirement. So AFU is exactly
what LUAU adds at each line: the rest of the step (`luau_succ`) is proved. -/
theorem afu_of_luau (n : Nat) (hL : LUAU φ (n + 1)) : AFU φ (n + 1) := by
  intro S hS hv c Q0 hQ hW hcs r hr
  -- the state of `c`'s key
  obtain ⟨ncF, hncF, _⟩ := hQ c List.mem_cons_self
  have hnonempty : ∃ kv, kv ∈ line φ (n + 1) := by
    cases hl : line φ (n + 1) with
    | nil =>
      exfalso
      have hU : lineU φ (n + 1) = GPathM.initSeed ⟨0, 0⟩ "" := by unfold lineU; rw [hl]
      rw [hU] at hncF
      obtain ⟨n0, hn0, hid, _, _⟩ :=
        (pruned_filterAll (GPathM.initSeed ⟨0, 0⟩ "") S).nodes_derived ncF (List.mem_of_find?_eq_some hncF)
      rw [initSeed_nodes, List.mem_singleton] at hn0
      rw [node?_id_eq _ _ ncF hncF, hn0] at hid
      have : c.id.step = 0 := by rw [hid]
      omega
    | cons kv1 _ => exact ⟨kv1, List.mem_cons_self⟩
  obtain ⟨kv1, hkv1⟩ := hnonempty
  obtain ⟨hU, _, hgrU, hsrcU, _⟩ := lineU_props φ hbd (n + 1) kv1 hkv1
  have hbU := KernelIff.below_filterAll_self (lineU φ (n + 1)) hU.rc.nodup S
  obtain ⟨ncU, hncU, _, _, _⟩ := hbU.node c ncF hncF
  obtain ⟨kv, hkv, h2⟩ := hsrcU c ncU hncU
  obtain ⟨n2, hn2⟩ := Option.isSome_iff_exists.mp h2
  have c2 := KernelUp.aCtx_line φ hbd (n + 1) kv hkv
  have hk2 := top_entry_key φ hbd (n + 1) kv hkv c n2 hn2 c (TriPinCut.self_own_pc c2.pc c n2 hn2) hcs
  obtain ⟨hvG, hQG, hWG⟩ := hL S hS hv c Q0 hQ hW hcs kv hkv hk2.symm
  -- it sits inside the union pinned at the requirement
  have hok : StateOk φ ((n + 1 : Nat) : Int) kv := (lineOk φ (n + 1)).2 kv hkv
  have cG := filt_ctx φ hbd _ kv hok S hvG
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ hok.reach)
  have hBG : Kernel.Below (lineU φ (n + 1)) (filterAll kv.2 S) :=
    PieceFilter.below_trans (PieceFilter.below_of_grown (hgrU kv hkv)) (KernelIff.below_filterAll_self kv.2 hnd S)
  have hrk : r ∈ reqOf φ kv.1 := by rw [← hk2]; exact hr
  have hB := Kernel.below_filterAll cG.pc.ker hBG (S ++ [r]) (fun r' hr' q hq hqs => by
    rcases List.mem_append.mp hr' with hr' | hr'
    · exact LineUnion.gowner_pinned kv.2 S q hq r' hr' hqs
    · rw [List.mem_singleton.mp hr'] at hqs ⊢
      exact line_pinned_req φ hbd n kv hkv r hrk q ((pruned_filterAll kv.2 S).gowners_sub q hq) hqs)
  exact good_up hB cG.pc.ker hQG hWG

/-- info: 'AbsSatBin.GraphPath.Model.UnionLine.afu_of_luau' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms afu_of_luau

-- ============================================================
-- A1 from growth at the top of the truncation (A1K) and LUAJ
-- ============================================================

omit hbd in
/-- **A1K n**: a clique with witnesses of a filtered joined state of line `n+1` without its top row (members below
step `n+1`) gains a node at step `n`, keeping its witnesses. -/
def A1K (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ R : List NodeId, (∀ p ∈ R, 0 ≤ p.step ∧ p.step < kv'.2.current_step) →
    isValid (filterAll kv'.2 R) = true → ∀ Q, Clique (Trunc.trunc (filterAll kv'.2 R)) Q →
      Wit (Trunc.trunc (filterAll kv'.2 R)) Q → (∀ q ∈ Q, q.id.step ≤ n) →
      ∃ c, c.id.step = (n : Int) ∧ Clique (Trunc.trunc (filterAll kv'.2 R)) (c :: Q) ∧
        Wit (Trunc.trunc (filterAll kv'.2 R)) (c :: Q)

/-- **A1 from A1K and LUAJ.** The anchor `c` at step `n` puts the clique in its source (LUAJ); `FCert` gives a
certificate; `c` has a son in its piece, which is the shift of `c`, so the certificate climbs (`climbE`) to the piece
and to the joined state, and its top node anchors the clique. -/
theorem anchorF_of_a1k (n : Nat) (hA : A1K φ n) (hLJ : LUAJ φ n) (hX : ∀ kv ∈ line φ n, FCert kv.2) :
    AnchorF φ n := by
  intro kv' hkv' R hR hv Q hQ hW hlow
  have hok' : StateOk φ ((n + 1 : Nat) : Int) kv' := (lineOk φ (n + 1)).2 kv' hkv'
  have hreach' := MapReachable.reachable_of_mapReachable φ hbd _ hok'.reach
  have hnd' := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreach'
  have cF := filt_ctx φ hbd _ kv' hok' R hv
  have hbJ := KernelIff.below_filterAll_self kv'.2 hnd' R
  have hcsJ : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hFcs : (filterAll kv'.2 R).current_step = (n : Int) + 2 := by rw [← hbJ.step, hcsJ]
  have hKcs : (Trunc.trunc (filterAll kv'.2 R)).current_step = (n : Int) + 1 := by
    show (filterAll kv'.2 R).current_step - 1 = _; rw [hFcs]; omega
  have toK : ∀ p np, (filterAll kv'.2 R).node? p = some np → p.id.step ≤ n →
      (Trunc.trunc (filterAll kv'.2 R)).node? p =
        some (Trunc.cutTop ((filterAll kv'.2 R).current_step - 1) np) :=
    fun p np hnp hps' => Trunc.trunc_node?_of _ p np hnp (by rw [hFcs]; omega)
  have hQK : Clique (Trunc.trunc (filterAll kv'.2 R)) Q := fun p hp => by
    obtain ⟨np, hnp, ho⟩ := hQ p hp
    exact ⟨_, toK p np hnp (hlow p hp), fun s hs =>
      (Trunc.mem_cutTop_owners _ _ s).mpr ⟨ho s hs, by rw [hFcs]; have := hlow s hs; omega⟩⟩
  have hWK : Wit (Trunc.trunc (filterAll kv'.2 R)) Q := by
    intro l h0 h1
    rw [hKcs] at h1
    obtain ⟨r, nr, hnr, hrs, ho⟩ := hW l h0 (by rw [hFcs]; omega)
    exact ⟨r, _, toK r nr hnr (by omega), hrs, fun s hs =>
      (Trunc.mem_cutTop_owners _ _ s).mpr ⟨ho s hs, by rw [hFcs]; have := hlow s hs; omega⟩⟩
  -- the anchor at step `n` and its source
  obtain ⟨c, hcs, hQc, hWc⟩ := hA kv' hkv' R hR hv Q hQK hWK hlow
  obtain ⟨nck, hnck, _⟩ := hQc c List.mem_cons_self
  obtain ⟨ncF, hncF, _, _⟩ := Trunc.trunc_node?_some _ c nck hnck
  obtain ⟨ncJ, hncJ, _, _, _⟩ := hbJ.node c ncF hncF
  obtain ⟨kv, hkv, hd, hvp, hkey, hent⟩ := PieceJoin.mid_one_source φ hbd n kv' hkv' c ncJ hncJ hcs
  obtain ⟨hvG, hQG, hWG⟩ := hLJ kv' hkv' R hR hv c Q hQc hWc hcs hlow kv hkv hd hvp hkey.symm
  obtain ⟨hok, _, hcs0, _, _, _⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hvp
  obtain ⟨sel, hsG, hon⟩ := hX kv hkv _ (fun p hp => by
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨reqOf_nonneg φ hbd kv'.1 p hp, by
        have := reqOf_backward φ hbd kv'.1 p hp
        have hdst : kv'.1.step = kv.2.current_step := (src_ctx φ hbd n kv hkv kv'.1 hd hvp).2.1
        rw [hdst] at this; exact this⟩
    · obtain ⟨hp, hle⟩ := List.mem_filter.mp hp
      exact ⟨(hR p hp).1, by rw [hcs0]; have := of_decide_eq_true hle; omega⟩) hvG _ hQG hWG
  have hselc : sel n = c := by rw [← hcs]; exact hon c List.mem_cons_self
  -- `c` has a son in its piece, the shift of `c`
  have hP : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) := StateOk_sent φ n kv hok kv'.1 hd hvp
  have hreachP := MapReachable.reachable_of_mapReachable φ hbd _ hP.reach
  have hndP := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreachP
  have cP := KernelUp.aCtx_reachable (reqOf φ) (isProhibited φ) _ hreachP hP.valid
  have hPcs : (upF φ kv.2 kv'.1).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  obtain ⟨ncP, hncP, _⟩ := hent c (TriPinCut.self_own_pc (KernelUp.aCtx_line φ hbd (n + 1) kv' hkv').pc c ncJ hncJ)
  have hncPm := List.mem_of_find?_eq_some hncP
  have hncPid : ncP.id = c := node?_id_eq _ c ncP hncP
  obtain ⟨z, hz⟩ : ∃ z, z ∈ ncP.sons := by
    rcases ((Kernel.isValidNode_iff _ ncP).mp (cP.pc.ker.valid c ncP hncP)).2.2 with h' | h'
    · exfalso
      have := eq_of_beq h'; rw [hncPid, hcs, hPcs] at this; omega
    · exact List.exists_mem_of_ne_nil _ h'
  obtain ⟨_, nzz, hnzz, _⟩ := cP.pc.ker.linkS c ncP hncP z hz
  have hnzzm := List.mem_of_find?_eq_some hnzz
  have hnzzid : nzz.id = z := node?_id_eq _ z nzz hnzz
  have hcz : c ∈ nzz.parents := by
    have := Sons.PMS_reachable (reqOf φ) (isProhibited φ) _ hreachP ncP hncPm z hz nzz hnzzm hnzzid
    rw [hncPid] at this; exact this
  have hzs : z.id.step = (n : Int) + 1 := by
    have := cP.pc.pb nzz hnzzm c hcz; rw [hnzzid, hcs] at this; omega
  have hzp : some c.id = z.parent_id := by have := cP.rc.pmp nzz hnzzm c hcz; rw [hnzzid] at this; exact this
  have hzg : z.gparent_id = c.parent_id := by have := cP.rc.gpmp.1 nzz hnzzm c hcz; rw [hnzzid] at this; exact this
  obtain ⟨_, hdst, _, _, hvF, _⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hvp
  have c0 := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  have hzd := mapId_of_mem_newRowIds _ _ _ z (upF_new φ kv.2 kv'.1 hdst c0 hvp z nzz hnzz (by rw [hzs, hcs0])).1
  have hshift : shiftPid c kv'.1 = z := by
    unfold shiftPid
    revert hzd hzp hzg
    cases z with
    | mk zi zp zg =>
      intro hzd hzp hzg
      simp only at hzd hzp hzg
      rw [← hzd, hzp, ← hzg]
  -- every pin at the top is the destination
  have htop : ∀ r ∈ R, r.step = (n : Int) + 1 → r = kv'.1 := by
    intro r hr hrs
    obtain ⟨w0, nw0, hnw0, hw0s, _⟩ := hW ((n : Int) + 1) (by omega) (by rw [hFcs]; omega)
    have hwr := LineUnion.gowner_pinned _ R w0 (cF.pc.ker.gow w0 nw0 hnw0) r hr (by rw [hw0s, hrs])
    obtain ⟨nJ, hnJ, _, _, _⟩ := hbJ.node w0 nw0 hnw0
    obtain ⟨kv0, hkv0, hd0, hv0, nP0, hnP0⟩ := (PieceJoin.join_no_new φ n kv' hkv').1 w0 nJ hnJ
    obtain ⟨hok0, hdst0, hcs0', _, hvF0, _⟩ := src_ctx φ hbd n kv0 hkv0 kv'.1 hd0 hv0
    have c0' := filt_ctx φ hbd n kv0 hok0 (reqOf φ kv'.1) hvF0
    have hwd := mapId_of_mem_newRowIds _ _ _ w0 (upF_new φ kv0.2 kv'.1 hdst0 c0' hv0 w0 nP0 hnP0 (by rw [hw0s, hcs0'])).1
    rw [← hwr, hwd]
  obtain ⟨hsP, hlowsel, htopE⟩ := climbE φ hbd n kv hkv kv'.1 hd hvp R htop sel hsG
    ⟨nzz, by rw [hselc, hshift]; exact hnzz⟩
  -- to the joined state
  obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hd hvp
  have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
  have hsJ : ChainSound (filterAll h R) (extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel) := by
    have hsU : ChainSound (upF φ kv.2 kv'.1) (extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel) :=
      ChainSound_of_grown (PieceFilter.grown_of_below (KernelIff.below_filterAll_self _ hndP R)) _ hsP
    exact ChainSound_filterAll h R _ (ChainSound_of_grown hgr _ hsU) (fun r hr h0 h1 =>
      chain_pins (upF φ kv.2 kv'.1) R _ hsP r hr h0 (by rw [← hgr.step_eq]; exact h1))
  rw [← he] at hFcs ⊢
  obtain ⟨_, h1, h2⟩ := good_of_chain _ hsJ (z :: Q) (fun q hq => by
    rw [hFcs]
    rcases List.mem_cons.mp hq with e | hq
    · rw [e, hzs, htopE, hselc, hshift]; exact ⟨by omega, by omega, rfl⟩
    · obtain ⟨nq, hnq, _⟩ := hQ q hq
      have := CertFix.step_range cF.pc q nq hnq
      rw [← he] at this; rw [hFcs] at this
      exact ⟨this.1, by have := hlow q hq; omega, by rw [hlowsel _ (hlow q hq)]; exact hon q (List.mem_cons_of_mem _ hq)⟩)
  exact ⟨z, hzs, h1, h2⟩

/-- info: 'AbsSatBin.GraphPath.Model.UnionLine.anchorF_of_a1k' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms anchorF_of_a1k

-- ============================================================
-- The whole run, and the reader
-- ============================================================

/-- **`FCert` and LUAU along the run, together.** LUAU at `n+1` comes from LUAU and `FCert` at `n` (`luau_succ`);
`FCert` at `n+1` from the join (`PieceLocalF`: A1 from A1K and LUAJ, S2 from LUAJ) and the pieces (AF). -/
theorem fCert_luau_line (hA1K : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → A1K φ n)
    (hAFU : ∀ n : Nat, 1 ≤ n → (n : Int) < stepCount φ → AFU φ n)
    (hTMU : ∀ n : Nat, 1 ≤ n → (n : Int) < stepCount φ → TopMergeU φ n)
    (hTMJ : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → TopMergeJ φ n)
    (hAF : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → AFP φ n) :
    ∀ n : Nat, (n : Int) < stepCount φ → (∀ kv ∈ line φ n, FCert kv.2) ∧ LUAU φ n := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun kv hkv => ?_, luau_zero φ⟩
    have hok : StateOk φ ((0 : Nat) : Int) kv := (lineOk φ 0).2 kv hkv
    refine fCert_of_mapCert φ hbd _ kv hok ?_
    rw [line_zero φ kv hkv]; exact StateLine.mapCert_seed
  | succ m ih =>
    intro hm0
    have hm : (m : Int) + 1 < stepCount φ := by push_cast at hm0; exact hm0
    obtain ⟨hF, hL⟩ := ih (by omega)
    have hLJ := luaJ_of_luau φ hbd m hL
    refine ⟨?_, luau_succ φ hbd m hL (hAFU (m + 1) (by omega) hm0) (hTMU (m + 1) (by omega) hm0) hF⟩
    have hAnch : AnchorF φ m := by
      by_cases h0 : m = 0
      · subst h0; exact anchorF_zero φ hbd
      · exact anchorF_of_a1k φ hbd m (hA1K m (by omega) hm) hLJ hF
    have hS : TopPieceF φ m := by
      by_cases h0 : m = 0
      · subst h0; exact topPieceF_zero φ
      · exact topPieceF_of_luaJ φ m hbd (by omega) hLJ (hTMJ m (by omega) hm) hF
    refine fCert_join φ hbd m (pieceLocalF_of_anchor φ m hbd hAnch hS) (fun kv hkv d hd hv => ?_)
    by_cases h0 : m = 0
    · subst h0
      exact fCert_of_mapCert φ hbd _ _ (StateOk_sent φ 0 kv ((lineOk φ 0).2 kv hkv) d hd hv)
        (StateLine.mapCert_piece0 φ kv hkv d hd hv)
    · exact pieceF_of_topParent φ hbd m (by omega) (topParent_of_afp φ m hbd (by omega) (hAF m (by omega) hm))
        kv hkv (hF kv hkv) d hd hv

/-- **The reader decides `φ` under A1K, AFU, `TopMergeU`, `TopMergeJ` and AF in the pieces** — LUA is no longer a
hypothesis: it is proved by induction on the line (`luau_succ`), and A1 from A1K and LUA (`anchorF_of_a1k`). -/
theorem readerVerdictW_iff_of_luau (hA1K : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → A1K φ n)
    (hAFU : ∀ n : Nat, 1 ≤ n → (n : Int) < stepCount φ → AFU φ n)
    (hTMU : ∀ n : Nat, 1 ≤ n → (n : Int) < stepCount φ → TopMergeU φ n)
    (hTMJ : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → TopMergeJ φ n)
    (hAF : ∀ n : Nat, 1 ≤ n → (n : Int) + 1 < stepCount φ → AFP φ n) :
    ReaderExec.readerVerdictW φ = true ↔ Satisfiable φ := by
  refine readerVerdictW_iff_of_fCert φ hbd (fun kv hkv => ?_)
  have hN : (((stepCount φ - 1).toNat : Nat) : Int) < stepCount φ := by simp only [stepCount]; omega
  exact (fCert_luau_line φ hbd hA1K hAFU hTMU hTMJ hAF _ hN).1 kv hkv

/-- info: 'AbsSatBin.GraphPath.Model.UnionLine.readerVerdictW_iff_of_luau' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_luau

end AbsSatBin.GraphPath.Model.UnionLine
