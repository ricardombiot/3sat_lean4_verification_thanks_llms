-- lean/improves_bin/AbsSatBin/GraphPath/Model/Kernel.lean
import AbsSatBin.GraphPath.Model.NoDeadEnd

/-!
# Kernels: when a pin survives

A **kernel** is a state with the static properties of a valid review fixpoint: every node is valid,
every table entry is a global owner, the tables are symmetric, every link is owned both ways, two
nodes that own each other share an entry at every step (the pair rule), and every entry of a table
is in the table of some parent (and of some son). `Below X h` says `h` sits inside `X`: same step,
fewer global owners, and every node of `h` is a node of `X` with smaller tables and fewer links.

**`below_review`**: the review never goes below a kernel. Each operation of the review — the purge,
the cut, the pair rule, the reviews against parents and sons with their mirror and unlink — keeps
`Below X h`, because every test it runs on a node of `h` passes on the larger tables of `X`.

So **a pin survives when a kernel below the pinned state covers every step**
(`isValid_filterAll_of_kernel`). This is the "survives" half of the characterization of a pin's
death: a pin dies only if no kernel is compatible with it.
-/

namespace AbsSatBin.GraphPath.Model.Kernel

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Threaded (OwnSymmetric)

/-- The static properties of a valid review fixpoint. -/
structure Kernel (h : GPathM) : Prop where
  gow   : ∀ p n, h.node? p = some n → p ∈ h.gowners
  gn    : ∀ q ∈ h.gowners, (h.node? q).isSome = true
  own   : ∀ p n, h.node? p = some n → ∀ v ∈ n.owners, v ∈ h.gowners
  valid : ∀ p n, h.node? p = some n → isValidNode h n = true
  sym   : OwnSymmetric h
  linkP : ∀ p n, h.node? p = some n → ∀ c ∈ n.parents,
    c ∈ n.owners ∧ ∃ nc, h.node? c = some nc ∧ p ∈ nc.owners
  linkS : ∀ p n, h.node? p = some n → ∀ c ∈ n.sons,
    c ∈ n.owners ∧ ∃ nc, h.node? c = some nc ∧ p ∈ nc.owners
  pair  : ∀ p n w nw, h.node? p = some n → h.node? w = some nw → w ∈ n.owners →
    ∀ k, 0 ≤ k → k < h.current_step → ∃ r ∈ n.owners, r ∈ nw.owners ∧ r.id.step = k
  nbrP  : ∀ p n, h.node? p = some n → 1 ≤ p.id.step → ∀ v ∈ n.owners,
    ∃ c ∈ n.parents, ∃ nc, h.node? c = some nc ∧ v ∈ nc.owners
  nbrS  : ∀ p n, h.node? p = some n → p.id.step ≤ h.current_step - 2 → ∀ v ∈ n.owners,
    ∃ c ∈ n.sons, ∃ nc, h.node? c = some nc ∧ v ∈ nc.owners

/-- `h` sits inside `X`. -/
structure Below (X h : GPathM) : Prop where
  step : X.current_step = h.current_step
  gow  : ∀ q ∈ h.gowners, q ∈ X.gowners
  node : ∀ p nh, h.node? p = some nh → ∃ nx, X.node? p = some nx ∧
    (∀ q ∈ nh.owners, q ∈ nx.owners) ∧ (∀ q ∈ nh.parents, q ∈ nx.parents) ∧
      (∀ q ∈ nh.sons, q ∈ nx.sons)

variable {h : GPathM}

-- ============================================================
-- Node validity is monotone
-- ============================================================

theorem isValidNode_iff (g : GPathM) (n : PNodeM) :
    isValidNode g n = true ↔
      (intRange 0 (g.current_step - 1)).all (fun k => hasStepEntry n.owners k) = true ∧
      (n.id.parent_id.isNone = true ∨ n.parents ≠ []) ∧
      ((n.id.id.step == g.current_step - 1) = true ∨ n.sons ≠ []) := by
  unfold isValidNode
  cases hr : n.id.parent_id.isNone <;> cases hl : (n.id.id.step == g.current_step - 1) <;>
    cases hp : n.parents <;> cases hs : n.sons <;> simp

theorem ne_nil_mono {a b : List PathNodeId} (hab : ∀ q ∈ a, q ∈ b) (h : a ≠ []) : b ≠ [] := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil a h
  intro hb; rw [hb] at hab; exact absurd (hab x hx) List.not_mem_nil

theorem isValidNode_mono (X : GPathM) (nh nx : PNodeM) (hid : nx.id = nh.id)
    (hcs : X.current_step = h.current_step)
    (ho : ∀ q ∈ nh.owners, q ∈ nx.owners) (hp : ∀ q ∈ nh.parents, q ∈ nx.parents)
    (hs : ∀ q ∈ nh.sons, q ∈ nx.sons) (hv : isValidNode h nh = true) : isValidNode X nx = true := by
  obtain ⟨hok, hr, hl⟩ := (isValidNode_iff h nh).mp hv
  refine (isValidNode_iff X nx).mpr ⟨?_, ?_, ?_⟩
  · rw [hcs]
    refine List.all_eq_true.mpr (fun k hk => ?_)
    obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hok k hk)
    exact List.any_eq_true.mpr ⟨q, ho q hq, hqs⟩
  · rw [hid]; rcases hr with hr | hr
    · exact Or.inl hr
    · exact Or.inr (ne_nil_mono hp hr)
  · rw [hid, hcs]; rcases hl with hl | hl
    · exact Or.inl hl
    · exact Or.inr (ne_nil_mono hs hl)

-- ============================================================
-- The kernel's links and entries point to its nodes
-- ============================================================

theorem Kernel.isNode_owner (hk : Kernel h) (p : PathNodeId) (n : PNodeM) (hn : h.node? p = some n)
    (v : PathNodeId) (hv : v ∈ n.owners) : ∃ nv, h.node? v = some nv :=
  Option.isSome_iff_exists.mp (hk.gn v (hk.own p n hn v hv))

theorem Kernel.ne_of_absent (_hk : Kernel h) (id : PathNodeId) (hno : h.node? id = none)
    (p : PathNodeId) (n : PNodeM) (hn : h.node? p = some n) : p ≠ id := by
  intro e; rw [e, hno] at hn; cases hn

-- ============================================================
-- The filter, the removal of a node outside the kernel
-- ============================================================

theorem below_filterRequire {X : GPathM} (hb : Below X h) (d : NodeId)
    (hpin : ∀ q ∈ h.gowners, q.id.step = d.step → q.id = d) : Below (filterRequire X d) h where
  step := hb.step
  gow q hq := by
    refine List.mem_filter.mpr ⟨hb.gow q hq, ?_⟩
    by_cases hs : q.id.step = d.step
    · simp [hpin q hq hs]
    · simp [hs]
  node := hb.node

theorem below_foldl_filterRequire (reqs : List NodeId) :
    ∀ X : GPathM, Below X h → (∀ r ∈ reqs, ∀ q ∈ h.gowners, q.id.step = r.step → q.id = r) →
      Below (reqs.foldl filterRequire X) h := by
  induction reqs with
  | nil => intro X hb _; exact hb
  | cons r rs ih =>
    intro X hb hr
    exact ih _ (below_filterRequire hb r (hr r List.mem_cons_self))
      (fun r' h' => hr r' (List.mem_cons_of_mem _ h'))

theorem below_removeNode (hk : Kernel h) {X : GPathM} (hb : Below X h) (id : PathNodeId)
    (hno : h.node? id = none) : Below (removeNode X id) h where
  step := hb.step
  gow q hq := by
    obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (hk.gn q hq)
    refine List.mem_filter.mpr ⟨hb.gow q hq, ?_⟩
    simp [hk.ne_of_absent id hno q nq hnq]
  node p nh hnh := by
    obtain ⟨nx, hnx, ho, hp, hs⟩ := hb.node p nh hnh
    refine ⟨unlink id nx, removeNode_node? X id p nx hnx (hk.ne_of_absent id hno p nh hnh), ho, ?_, ?_⟩
    · intro c hc
      obtain ⟨_, nc, hnc, _⟩ := hk.linkP p nh hnh c hc
      exact List.mem_filter.mpr ⟨hp c hc, by simp [hk.ne_of_absent id hno c nc hnc]⟩
    · intro c hc
      obtain ⟨_, nc, hnc, _⟩ := hk.linkS p nh hnh c hc
      exact List.mem_filter.mpr ⟨hs c hc, by simp [hk.ne_of_absent id hno c nc hnc]⟩

-- ============================================================
-- The cut and the purge
-- ============================================================

/-- **A kernel node, cut in `X`, keeps everything it has in the kernel.** -/
theorem cutNode_ge (hk : Kernel h) {X : GPathM} (hb : Below X h) (p : PathNodeId) (nh : PNodeM)
    (hnh : h.node? p = some nh) (nx : PNodeM) (hnx : X.node? p = some nx) :
    (∀ q ∈ nh.owners, q ∈ (cutNode X.gowners X nx).owners) ∧
    (∀ q ∈ nh.parents, q ∈ (cutNode X.gowners X nx).parents) ∧
    (∀ q ∈ nh.sons, q ∈ (cutNode X.gowners X nx).sons) := by
  obtain ⟨nx', hnx', ho, hp, hs⟩ := hb.node p nh hnh
  rw [hnx] at hnx'; cases hnx'
  have hxid : nx.id = p := node?_id_eq X p nx hnx
  have hown : ∀ q ∈ nh.owners, q ∈ intersectOwners nx.owners X.gowners := fun q hq =>
    mem_intersectOwners_of_mem _ _ q (ho q hq) (hb.gow q (hk.own p nh hnh q hq))
  -- both ends of a kernel link admit each other in `X`
  have hadm : ∀ c, c ∈ nh.owners → (∃ nc, h.node? c = some nc ∧ p ∈ nc.owners) →
      admits X.gowners X nx.id c = true ∧ admits X.gowners X c nx.id = true := by
    intro c hc ⟨nc, hnc, hpc⟩
    obtain ⟨ncx, hncx, hco, _, _⟩ := hb.node c nc hnc
    refine ⟨?_, ?_⟩
    · rw [hxid]
      exact admits_of_node X.gowners X p nx hnx c (ho c hc) (hb.gow c (hk.own p nh hnh c hc))
    · rw [hxid]
      exact admits_of_node X.gowners X c ncx hncx p (hco p hpc) (hb.gow p (hk.gow p nh hnh))
  refine ⟨hown, fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨hco, hex⟩ := hk.linkP p nh hnh c hc
    obtain ⟨h1, h2⟩ := hadm c hco hex
    exact List.mem_filter.mpr ⟨hp c hc, by simp [h1, h2]⟩
  · obtain ⟨hco, hex⟩ := hk.linkS p nh hnh c hc
    obtain ⟨h1, h2⟩ := hadm c hco hex
    exact List.mem_filter.mpr ⟨hs c hc, by simp [h1, h2]⟩

theorem below_cutAll (hk : Kernel h) {X : GPathM} (hb : Below X h) : Below (cutAll X) h where
  step := hb.step
  gow := hb.gow
  node p nh hnh := by
    obtain ⟨nx, hnx, _⟩ := hb.node p nh hnh
    refine ⟨cutNode X.gowners X nx, by rw [node?_cutAll, hnx]; rfl, cutNode_ge hk hb p nh hnh nx hnx⟩

theorem below_purgeStep (hk : Kernel h) {X : GPathM} (hb : Below X h) (id : PathNodeId) :
    Below (purgeStep X id) h := by
  unfold purgeStep
  cases hd : X.node? id with
  | none => exact hb
  | some n =>
    simp only
    cases hh : h.node? id with
    | none => split
              · exact hb
              · exact below_removeNode hk hb id hh
    | some nh =>
      have hv : isValidNode X (cutNode X.gowners X n) = true := by
        obtain ⟨ho, hp, hs⟩ := cutNode_ge hk hb id nh hh n hd
        refine isValidNode_mono X nh _ ?_ hb.step ho hp hs (hk.valid id nh hh)
        show n.id = nh.id
        rw [node?_id_eq X id n hd, node?_id_eq h id nh hh]
      rw [if_pos hv]
      exact hb

theorem below_purgeRound (hk : Kernel h) {X : GPathM} (hb : Below X h) : Below (purgeRound X) h := by
  unfold purgeRound
  have main : ∀ (l : List PathNodeId) (Y : GPathM), Below Y h → Below (l.foldl purgeStep Y) h := by
    intro l
    induction l with
    | nil => intro Y hY; exact hY
    | cons x xs ih => intro Y hY; exact ih _ (below_purgeStep hk hY x)
  exact main _ X hb

theorem below_purgeFuel (hk : Kernel h) : ∀ (fuel : Nat) (X : GPathM), Below X h →
    Below (purgeFuel fuel X) h := by
  intro fuel
  induction fuel with
  | zero => intro X hb; exact hb
  | succ n ih =>
    intro X hb
    simp only [purgeFuel]
    split
    · split
      · exact ih _ (below_purgeRound hk hb)
      · exact below_purgeRound hk hb
    · exact hb

theorem below_cleanInvalid₂ (hk : Kernel h) {X : GPathM} (hb : Below X h) :
    Below (cleanInvalid₂ X) h :=
  below_cutAll hk (below_purgeFuel hk _ X hb)

-- ============================================================
-- The pair rule
-- ============================================================

theorem below_pairSweep (hk : Kernel h) {X : GPathM} (hb : Below X h) : Below (pairSweep X) h where
  step := hb.step
  gow := hb.gow
  node p nh hnh := by
    obtain ⟨nx, hnx, ho, hp, hs⟩ := hb.node p nh hnh
    refine ⟨pairMap X nx, pairSweep_node? X p nx hnx, fun v hv => ?_, hp, hs⟩
    refine List.mem_filter.mpr ⟨ho v hv, ?_⟩
    have hxid : nx.id = p := node?_id_eq X p nx hnx
    unfold pairBad
    by_cases hvp : v = nx.id
    · simp [hvp]
    · obtain ⟨nv, hnv⟩ := hk.isNode_owner p nh hnh v hv
      obtain ⟨nvx, hnvx, hvo, _, _⟩ := hb.node v nv hnv
      have hsh : pairShares X.current_step nx.owners nvx.owners = true := by
        unfold pairShares
        refine List.all_eq_true.mpr (fun k hkr => ?_)
        have hk0 := mem_intRange_lower hkr
        have hk1 := mem_intRange_upper hkr
        obtain ⟨r, hr, hrv, hrs⟩ := hk.pair p nh v nv hnh hnv hv k hk0 (by rw [← hb.step]; omega)
        have : (ownersAt nx.owners k).any (fun r => nvx.owners.contains r) = true :=
          List.any_eq_true.mpr ⟨r, List.mem_filter.mpr ⟨ho r hr, beq_iff_eq.mpr hrs⟩,
            List.elem_eq_true_of_mem (hvo r hrv)⟩
        rw [this]; simp
      simp [hnvx, hsh]

theorem below_pairFuel (hk : Kernel h) : ∀ (fuel : Nat) (X : GPathM), Below X h →
    Below (pairFuel fuel X) h := by
  intro fuel
  induction fuel with
  | zero => intro X hb; exact hb
  | succ n ih =>
    intro X hb
    simp only [pairFuel]
    split
    · split
      · exact ih _ (below_cleanInvalid₂ hk (below_pairSweep hk hb))
      · exact hb
    · exact hb

theorem below_cleanPair (hk : Kernel h) {X : GPathM} (hb : Below X h) : Below (cleanPair X) h :=
  below_pairFuel hk _ _ (below_cleanInvalid₂ hk hb)

-- ============================================================
-- The review against the neighbours: cut, mirror, unlink
-- ============================================================

theorem not_mem_cutRemoved_of_mem_intersect (d : PNodeM) (uni : List PathNodeId) (v : PathNodeId)
    (hv : v ∈ intersectOwners d.owners uni) : (cutRemoved d uni).contains v = false := by
  have hc := (List.mem_filter.mp hv).2
  cases hr : (cutRemoved d uni).contains v with
  | false => rfl
  | true =>
    have hm := (List.mem_filter.mp (List.contains_iff_mem.mp hr)).2
    cases h1 : hasStepEntry uni v.id.step <;> cases h2 : uni.contains v <;> simp_all

theorem mem_mirrorMap (x : PathNodeId) (rem : List PathNodeId) (m : PNodeM) (v : PathNodeId)
    (hv : v ∈ m.owners) (hx : v = x → rem.contains m.id = false) :
    v ∈ (mirrorMap x rem m).owners := by
  unfold mirrorMap
  split
  · next hc =>
    refine List.mem_filter.mpr ⟨hv, ?_⟩
    by_cases e : v = x
    · rw [hx e] at hc; cases hc
    · simp [e]
  · exact hv

theorem mem_unlinkMap_parents (n : PNodeM) (id : PathNodeId) (m : PNodeM) (hne : m.id ≠ id)
    (c : PathNodeId) (hc : c ∈ m.parents) (hcond : c = id → n.owners.contains m.id = true) :
    c ∈ (unlinkMap n id m).parents := by
  unfold unlinkMap
  have hb : (m.id == id) = false := by simp [hne]
  rw [if_neg (by simp [hb])]
  split
  · exact hc
  · next hno =>
    refine List.mem_filter.mpr ⟨hc, ?_⟩
    by_cases e : c = id
    · exact absurd (hcond e) (by simpa using hno)
    · simp [e]

theorem mem_unlinkMap_sons (n : PNodeM) (id : PathNodeId) (m : PNodeM) (hne : m.id ≠ id)
    (c : PathNodeId) (hc : c ∈ m.sons) (hcond : c = id → n.owners.contains m.id = true) :
    c ∈ (unlinkMap n id m).sons := by
  unfold unlinkMap
  have hb : (m.id == id) = false := by simp [hne]
  rw [if_neg (by simp [hb])]
  split
  · exact hc
  · next hno =>
    refine List.mem_filter.mpr ⟨hc, ?_⟩
    by_cases e : c = id
    · exact absurd (hcond e) (by simpa using hno)
    · simp [e]

theorem unlinkMap_self (n : PNodeM) (id : PathNodeId) (m : PNodeM) (he : m.id = id) :
    (unlinkMap n id m).parents = m.parents.filter (fun p => n.owners.contains p) ∧
    (unlinkMap n id m).sons = m.sons.filter (fun s => n.owners.contains s) := by
  unfold unlinkMap
  rw [if_pos (by simp [he])]
  exact ⟨rfl, rfl⟩

theorem unlinkIncompatible_gowners (g : GPathM) (id : PathNodeId) :
    (unlinkIncompatible g id).gowners = g.gowners := by
  unfold unlinkIncompatible; split <;> rfl

theorem unlinkIncompatible_step (g : GPathM) (id : PathNodeId) :
    (unlinkIncompatible g id).current_step = g.current_step := by
  unfold unlinkIncompatible; split <;> rfl

/-- **`reviewNode` never goes below a kernel**, when every entry of the reviewed kernel node is in
the table of one of its neighbours. -/
theorem below_reviewNode (hk : Kernel h) {X : GPathM} (hb : Below X h)
    (nb : PNodeM → List PathNodeId)
    (hnbsub : ∀ nh nx : PNodeM, (∀ q ∈ nh.parents, q ∈ nx.parents) → (∀ q ∈ nh.sons, q ∈ nx.sons) →
      ∀ c ∈ nb nh, c ∈ nb nx)
    (id : PathNodeId)
    (hnb : ∀ nh, h.node? id = some nh → ∀ v ∈ nh.owners,
      ∃ c ∈ nb nh, ∃ nc, h.node? c = some nc ∧ v ∈ nc.owners) :
    Below (reviewNode X nb id) h := by
  unfold reviewNode
  cases hd : X.node? id with
  | none => exact hb
  | some d =>
    simp only
    have hdid : d.id = id := node?_id_eq X id d hd
    -- the three stages, named
    let uni := unionOwnersOf X (nb d)
    let rem := cutRemoved d uni
    let f : PNodeM → PNodeM := fun n => { n with owners := intersectOwners n.owners uni }
    let g1 := updateAt X id f
    let g2 := mirrorDrop g1 id rem
    let g3 := unlinkIncompatible g2 id
    have hf : ∀ n, (f n).id = n.id := fun _ => rfl
    have hg1d : g1.node? id = some (f d) := by
      have := updateAt_node? X id f hf id d hd
      rw [this]; simp [hdid]
    have hg1o : ∀ p nx, X.node? p = some nx → p ≠ id → g1.node? p = some nx := by
      intro p nx hnx hne
      have := updateAt_node? X id f hf p nx hnx
      rw [this]
      have : (nx.id == id) = false := by rw [node?_id_eq X p nx hnx]; simp [hne]
      simp [this]
    let n2 := mirrorMap id rem (f d)
    have hg2d : g2.node? id = some n2 := mirrorDrop_node? g1 id rem id (f d) hg1d
    have hg3 : ∀ p m, g2.node? p = some m → g3.node? p = some (unlinkMap n2 id m) :=
      fun p m hm => unlinkIncompatible_node? g2 id n2 hg2d p m hm
    have hstep3 : g3.current_step = X.current_step := unlinkIncompatible_step g2 id
    have hgow3 : g3.gowners = X.gowners := unlinkIncompatible_gowners g2 id
    cases hh : h.node? id with
    | none =>
      -- the reviewed node is not in the kernel: nothing of the kernel mentions it
      have hb3 : Below g3 h := by
        refine ⟨by rw [hstep3]; exact hb.step, by rw [hgow3]; exact hb.gow, ?_⟩
        intro p nh hnh
        have hne := hk.ne_of_absent id hh p nh hnh
        obtain ⟨nx, hnx, ho, hp, hs⟩ := hb.node p nh hnh
        have hm2 := mirrorDrop_node? g1 id rem p nx (hg1o p nx hnx hne)
        have hxid : nx.id = p := node?_id_eq X p nx hnx
        refine ⟨_, hg3 p _ hm2, ?_, ?_, ?_⟩
        · intro v hv
          rw [unlinkMap_owners]
          refine mem_mirrorMap id rem nx v (ho v hv) (fun e => ?_)
          obtain ⟨nv, hnv⟩ := hk.isNode_owner p nh hnh v hv
          exact absurd e (hk.ne_of_absent id hh v nv hnv)
        · intro c hc
          have hmid : (mirrorMap id rem nx).id = p := by rw [mirrorMap_id, hxid]
          refine mem_unlinkMap_parents n2 id _ (by rw [hmid]; exact hne) c
            (by unfold mirrorMap; split <;> exact hp c hc) (fun e => ?_)
          obtain ⟨_, nc, hnc, _⟩ := hk.linkP p nh hnh c hc
          exact absurd e (hk.ne_of_absent id hh c nc hnc)
        · intro c hc
          have hmid : (mirrorMap id rem nx).id = p := by rw [mirrorMap_id, hxid]
          refine mem_unlinkMap_sons n2 id _ (by rw [hmid]; exact hne) c
            (by unfold mirrorMap; split <;> exact hs c hc) (fun e => ?_)
          obtain ⟨_, nc, hnc, _⟩ := hk.linkS p nh hnh c hc
          exact absurd e (hk.ne_of_absent id hh c nc hnc)
      split
      · split
        · exact hb3
        · exact below_removeNode hk hb3 id hh
      · exact below_removeNode hk hb id hh
    | some nh =>
      obtain ⟨nx, hnx, ho, hp, hs⟩ := hb.node id nh hh
      rw [hd] at hnx; cases hnx
      have hnhid : nh.id = id := node?_id_eq h id nh hh
      -- the cut keeps the kernel's table
      have hcut : ∀ v ∈ nh.owners, v ∈ intersectOwners d.owners uni := by
        intro v hv
        obtain ⟨c, hc, nc, hnc, hvc⟩ := hnb nh hh v hv
        obtain ⟨ncx, hncx, hco, _, _⟩ := hb.node c nc hnc
        exact mem_intersectOwners_of_mem _ _ v (ho v hv)
          (mem_unionOwnersOf X (nb d) c ncx v (hnbsub nh d hp hs c hc) hncx (hco v hvc))
      have hn2 : ∀ v ∈ nh.owners, v ∈ n2.owners := by
        intro v hv
        refine mem_mirrorMap id rem (f d) v (hcut v hv) (fun e => ?_)
        show (cutRemoved d uni).contains (f d).id = false
        rw [hf, hdid, ← e]
        exact not_mem_cutRemoved_of_mem_intersect d uni v (hcut v hv)
      have hb3 : Below g3 h := by
        refine ⟨by rw [hstep3]; exact hb.step, by rw [hgow3]; exact hb.gow, ?_⟩
        intro p np hnp
        by_cases hpe : p = id
        · subst hpe
          rw [hh] at hnp; cases hnp
          refine ⟨_, hg3 p n2 hg2d, by rw [unlinkMap_owners]; exact hn2, ?_, ?_⟩
          · have he : n2.id = p := by
              show (mirrorMap p rem (f d)).id = p
              rw [mirrorMap_id, hf, hdid]
            rw [(unlinkMap_self n2 p n2 he).1]
            intro c hc
            refine List.mem_filter.mpr ⟨?_, List.elem_eq_true_of_mem (hn2 c (hk.linkP p nh hh c hc).1)⟩
            show c ∈ (mirrorMap p rem (f d)).parents
            unfold mirrorMap; split <;> exact hp c hc
          · have he : n2.id = p := by
              show (mirrorMap p rem (f d)).id = p
              rw [mirrorMap_id, hf, hdid]
            rw [(unlinkMap_self n2 p n2 he).2]
            intro c hc
            refine List.mem_filter.mpr ⟨?_, List.elem_eq_true_of_mem (hn2 c (hk.linkS p nh hh c hc).1)⟩
            show c ∈ (mirrorMap p rem (f d)).sons
            unfold mirrorMap; split <;> exact hs c hc
        · obtain ⟨mx, hmx, hmo, hmp, hms⟩ := hb.node p np hnp
          have hm2 := mirrorDrop_node? g1 id rem p mx (hg1o p mx hmx hpe)
          have hxid : mx.id = p := node?_id_eq X p mx hmx
          have hmid : (mirrorMap id rem mx).id = p := by rw [mirrorMap_id, hxid]
          -- a kernel node owned by the reviewed one is in its cut
          have hin : id ∈ np.owners → n2.owners.contains p = true := by
            intro hid
            exact List.elem_eq_true_of_mem (hn2 p (hk.sym p np id nh hnp hh hid))
          refine ⟨_, hg3 p _ hm2, ?_, ?_, ?_⟩
          · intro v hv
            rw [unlinkMap_owners]
            refine mem_mirrorMap id rem mx v (hmo v hv) (fun e => ?_)
            rw [hxid]
            subst e
            exact not_mem_cutRemoved_of_mem_intersect d uni p
              (hcut p (hk.sym p np v nh hnp hh hv))
          · intro c hc
            refine mem_unlinkMap_parents n2 id _ (by rw [hmid]; exact hpe) c
              (by unfold mirrorMap; split <;> exact hmp c hc) (fun e => ?_)
            rw [hmid]
            subst e
            obtain ⟨_, nc, hnc, hpc⟩ := hk.linkP p np hnp c hc
            rw [hh] at hnc; cases hnc
            exact List.elem_eq_true_of_mem (hn2 p hpc)
          · intro c hc
            refine mem_unlinkMap_sons n2 id _ (by rw [hmid]; exact hpe) c
              (by unfold mirrorMap; split <;> exact hms c hc) (fun e => ?_)
            rw [hmid]
            subst e
            obtain ⟨_, nc, hnc, hpc⟩ := hk.linkS p np hnp c hc
            rw [hh] at hnc; cases hnc
            exact List.elem_eq_true_of_mem (hn2 p hpc)
      -- the reviewed node is valid before and after its cut
      have hv0 : isValidNode X d = true :=
        isValidNode_mono X nh d (by rw [hdid, hnhid]) hb.step ho hp hs (hk.valid id nh hh)
      have hv1 : isValidNode g3 (relink (intersectOwners d.owners uni) d) = true := by
        refine isValidNode_mono g3 nh _ (by show d.id = nh.id; rw [hdid, hnhid])
          (by rw [hstep3]; exact hb.step) hcut ?_ ?_ (hk.valid id nh hh)
        · intro c hc
          exact List.mem_filter.mpr ⟨hp c hc, List.elem_eq_true_of_mem (hcut c (hk.linkP id nh hh c hc).1)⟩
        · intro c hc
          exact List.mem_filter.mpr ⟨hs c hc, List.elem_eq_true_of_mem (hcut c (hk.linkS id nh hh c hc).1)⟩
      rw [if_pos hv0]
      rw [if_pos hv1]
      exact hb3

-- ============================================================
-- The passes and the loop
-- ============================================================

/-- The neighbour condition at one step. -/
def NbStep (h : GPathM) (nb : PNodeM → List PathNodeId) (k : Int) : Prop :=
  ∀ p nh, h.node? p = some nh → p.id.step = k → ∀ v ∈ nh.owners,
    ∃ c ∈ nb nh, ∃ nc, h.node? c = some nc ∧ v ∈ nc.owners

theorem below_reviewLine (hk : Kernel h) (nb : PNodeM → List PathNodeId)
    (hnbsub : ∀ nh nx : PNodeM, (∀ q ∈ nh.parents, q ∈ nx.parents) → (∀ q ∈ nh.sons, q ∈ nx.sons) →
      ∀ c ∈ nb nh, c ∈ nb nx)
    (k : Int) (hnb : NbStep h nb k) {X : GPathM} (hb : Below X h) : Below (reviewLine X nb k) h := by
  unfold reviewLine
  have main : ∀ (l : List PathNodeId), (∀ id ∈ l, id.id.step = k) → ∀ Y : GPathM, Below Y h →
      Below (l.foldl (fun g id => reviewNode g nb id) Y) h := by
    intro l
    induction l with
    | nil => intro _ Y hY; exact hY
    | cons x xs ih =>
      intro hl Y hY
      exact ih (fun id hid => hl id (List.mem_cons_of_mem _ hid)) _
        (below_reviewNode hk hY nb hnbsub x
          (fun nh hnh => hnb x nh hnh (hl x List.mem_cons_self)))
  exact main _ (fun id hid => Survive.step_of_mem_line X k id hid) X hb

theorem below_reviewSteps (hk : Kernel h) (nb : PNodeM → List PathNodeId)
    (hnbsub : ∀ nh nx : PNodeM, (∀ q ∈ nh.parents, q ∈ nx.parents) → (∀ q ∈ nh.sons, q ∈ nx.sons) →
      ∀ c ∈ nb nh, c ∈ nb nx) :
    ∀ (ks : List Int), (∀ k ∈ ks, NbStep h nb k) → ∀ X : GPathM, Below X h →
      Below (reviewSteps X nb ks) h := by
  intro ks
  induction ks with
  | nil => intro _ X hb; exact hb
  | cons k ks ih =>
    intro hks X hb
    unfold reviewSteps
    split
    · exact ih (fun k' h' => hks k' (List.mem_cons_of_mem _ h')) _
        (below_reviewLine hk nb hnbsub k (hks k List.mem_cons_self) hb)
    · exact hb

theorem below_reviewParents (hk : Kernel h) {X : GPathM} (hb : Below X h) :
    Below (reviewParents X) h := by
  unfold reviewParents
  refine below_reviewSteps hk (·.parents) (fun _ _ hp _ c hc => hp c hc) _ ?_ X hb
  intro k hkr p nh hnh hps
  exact hk.nbrP p nh hnh (by rw [hps]; exact mem_intRange_lower hkr)

theorem below_reviewSons (hk : Kernel h) {X : GPathM} (hb : Below X h) :
    Below (reviewSons X) h := by
  unfold reviewSons
  refine below_reviewSteps hk (·.sons) (fun _ _ _ hs c hc => hs c hc) _ ?_ X hb
  intro k hkr p nh hnh hps
  have := mem_intRange_upper (List.mem_reverse.mp hkr)
  exact hk.nbrS p nh hnh (by rw [hps, ← hb.step]; exact this)

theorem below_reviewPass (hk : Kernel h) {X : GPathM} (hb : Below X h) : Below (reviewPass X) h := by
  have h1 := below_cleanPair hk hb
  exact below_reviewSons hk (below_reviewParents hk h1)

theorem below_reviewFuel (hk : Kernel h) : ∀ (fuel : Nat) (X : GPathM), Below X h →
    Below (reviewFuel fuel X) h := by
  intro fuel
  induction fuel with
  | zero => intro X hb; exact hb
  | succ n ih =>
    intro X hb
    simp only [reviewFuel]
    split
    · split
      · exact ih _ (below_reviewPass hk hb)
      · exact below_reviewPass hk hb
    · exact hb

/-- **The review never goes below a kernel.** -/
theorem below_review (hk : Kernel h) {X : GPathM} (hb : Below X h) : Below (review X) h :=
  below_reviewFuel hk _ X hb

theorem below_filterAll (hk : Kernel h) {X : GPathM} (hb : Below X h) (reqs : List NodeId)
    (hpin : ∀ r ∈ reqs, ∀ q ∈ h.gowners, q.id.step = r.step → q.id = r) :
    Below (filterAll X reqs) h :=
  below_review hk (below_foldl_filterRequire reqs X hb hpin)

/-- **A pin survives when a valid kernel below the state agrees with it.** -/
theorem isValid_filterAll_of_kernel (hk : Kernel h) (hvh : isValid h = true) {X : GPathM}
    (hb : Below X h) (reqs : List NodeId)
    (hpin : ∀ r ∈ reqs, ∀ q ∈ h.gowners, q.id.step = r.step → q.id = r) :
    isValid (filterAll X reqs) = true := by
  have hb' := below_filterAll hk hb reqs hpin
  unfold isValid at hvh ⊢
  rw [hb'.step]
  refine List.all_eq_true.mpr (fun k hkr => ?_)
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hvh k hkr)
  exact List.any_eq_true.mpr ⟨q, hb'.gow q hq, hqs⟩

/-- info: 'AbsSatBin.GraphPath.Model.Kernel.isValid_filterAll_of_kernel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isValid_filterAll_of_kernel

end AbsSatBin.GraphPath.Model.Kernel
