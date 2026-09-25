-- lean/improves_bin/AbsSatBin/GraphPath/Model/AmbTriCore.lean
import AbsSatBin.GraphPath.Model.TriPinCore

/-!
# What is under `AmbTri`: the prefix and the window

Let `k` be the reader's first choice and `x` a global owner of step `k`. `AmbTri g x` asks, for two
ambiguous nodes `y`, `w`, a common entry at every step `l` that `x`'s table also holds. Two parts of
that are free:

* **Below the choice the path is fixed** (`gowner_eq`): below `k` every step has one map node, and a
  path node's window (parent and grandparent) is read off its parents (`PMP`, `GPMP`), so every step
  `≤ k` has a single path node per map node. At `l < k` the three tables share that node
  (`share_below`); at `l = k` they share `x` itself.
* **The window fixes the bit** (`excl_near`): a node at step `k + 1` or `k + 2` reads the bit of step `k`
  off its own id, so it is exclusive. At step `k` a node owning `x` is `x`. So ambiguous nodes live
  below `k` or from `k + 3` on.

What is left is **`AmbFar g k x`**: ambiguous pairs outside the window, at steps above the choice
(`ambTri_of_ambFar`, `readerVerdictW_iff_of_ambFar`).
-/

namespace AbsSatBin.GraphPath.Model.AmbTriCore

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.TriPinCore
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.PickInduction (choiceAt)
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

/-- The kernel context and the window invariants of the reader's states. -/
structure ACtx (g : GPathM) : Prop where
  pc : PinCtx g
  rc : Reader.RCtx g

variable {g : GPathM}

-- ============================================================
-- Small facts
-- ============================================================

theorem pid_ext {a b : PathNodeId} (h1 : a.id = b.id) (h2 : a.parent_id = b.parent_id)
    (h3 : a.gparent_id = b.gparent_id) : a = b := by
  cases a; cases b; dsimp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem ids_eq_of_choiceAt (g : GPathM) (i : Int) (h : choiceAt g i = false) (a b : PathNodeId)
    (ha : a ∈ ownersAt g.gowners i) (hb : b ∈ ownersAt g.gowners i) : a.id = b.id := by
  cases e : (a.id == b.id) with
  | true => exact eq_of_beq e
  | false =>
    have hne : (a.id != b.id) = true := by unfold bne; rw [e]; rfl
    have : choiceAt g i = true := List.any_eq_true.mpr ⟨a, ha, List.any_eq_true.mpr ⟨b, hb, hne⟩⟩
    rw [h] at this; cases this

theorem mem_ownersAt {l : List PathNodeId} {q : PathNodeId} {i : Int} (hq : q ∈ l) (hs : q.id.step = i) :
    q ∈ ownersAt l i :=
  List.mem_filter.mpr ⟨hq, beq_iff_eq.mpr hs⟩

theorem prefix_mono {k k' : Int} (h : PrefixUpTo g k) (hk : k' ≤ k) : PrefixUpTo g k' :=
  fun i h0 hi => h i h0 (Int.lt_of_lt_of_le hi hk)

/-- Every node has an entry at every step. -/
theorem entry_at (c : ACtx g) (y : PathNodeId) (ny : PNodeM) (hy : g.node? y = some ny) (l : Int)
    (h0 : 0 ≤ l) (h1 : l < g.current_step) : ∃ r ∈ ny.owners, r.id.step = l := by
  have hv := ((isValidNode_iff g ny).mp (c.pc.ker.valid y ny hy)).1
  have hl : l ∈ intRange 0 (g.current_step - 1) := mem_intRange h0 (by omega)
  obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv l hl)
  exact ⟨r, hr, eq_of_beq hrs⟩

/-- A node owns itself. -/
theorem self_own (c : ACtx g) (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx) :
    x ∈ nx.owners := by
  have hm := List.mem_of_find?_eq_some hx
  have hxid : nx.id = x := node?_id_eq g x nx hx
  have h0 : 0 ≤ x.id.step := by have := c.pc.snn nx hm; rw [hxid] at this; exact this
  have h1 : x.id.step < g.current_step := by have := c.pc.below nx hm; rw [hxid] at this; exact this
  obtain ⟨r, hr, hrs⟩ := entry_at c x nx hx x.id.step h0 h1
  have := c.pc.oos nx hm r hr (by rw [hxid, hrs])
  rw [hxid] at this; rw [← this]; exact hr

-- ============================================================
-- The window read off the parents
-- ============================================================

/-- An entry one step below is named by the node's parent id. -/
theorem parentId_of_owner (c : ACtx g) (y : PathNodeId) (ny : PNodeM) (hy : g.node? y = some ny)
    (h1 : 1 ≤ y.id.step) (q : PathNodeId) (hq : q ∈ ny.owners)
    -- idx: adjacent gpath rows (one row per map step, bin map too)
    (hqs : q.id.step = y.id.step - 1) : some q.id = y.parent_id := by
  obtain ⟨hp, _⟩ := parent_of_owner c.pc y ny hy h1 q hq hqs
  have := c.rc.pmp ny (List.mem_of_find?_eq_some hy) q hp
  rw [node?_id_eq g y ny hy] at this; exact this

/-- An entry two steps below is named by the node's grandparent id. -/
theorem gparentId_of_owner (c : ACtx g) (y : PathNodeId) (ny : PNodeM) (hy : g.node? y = some ny)
    (h2 : 2 ≤ y.id.step) (q : PathNodeId) (hq : q ∈ ny.owners)
    -- idx: gpath rows two apart (one row per map step, bin map too)
    (hqs : q.id.step = y.id.step - 2) : some q.id = y.gparent_id := by
  obtain ⟨cc, hcc, nc, hnc, hqc⟩ := c.pc.ker.nbrP y ny hy (by omega) q hq
  have hym := List.mem_of_find?_eq_some hy
  have hyid : ny.id = y := node?_id_eq g y ny hy
  have hncid : nc.id = cc := node?_id_eq g cc nc hnc
  -- idx: adjacent gpath rows (one row per map step, bin map too)
  have hcs : cc.id.step = y.id.step - 1 := by
    have := c.pc.pb ny hym cc hcc; rw [hyid] at this; exact this
  -- idx: adjacent gpath rows (one row per map step, bin map too)
  have hq1 := parentId_of_owner c cc nc hnc (by omega) q hqc (by omega)
  have hg := c.rc.gpmp.1 ny hym cc hcc
  rw [hyid] at hg; rw [hg]; exact hq1

-- ============================================================
-- Below the choice the path is fixed
-- ============================================================

theorem gowner_eq_nat (c : ACtx g) : ∀ (n : Nat) (a b : PathNodeId), a ∈ g.gowners → b ∈ g.gowners →
    a.id.step = (n : Int) → a.id = b.id → PrefixUpTo g n → a = b := by
  intro n
  induction n with
  | zero =>
    intro a b ha hb hs hab _
    obtain ⟨na, hna⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn a ha)
    obtain ⟨nb, hnb⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn b hb)
    have hma := List.mem_of_find?_eq_some hna
    have hmb := List.mem_of_find?_eq_some hnb
    have haid : na.id = a := node?_id_eq g a na hna
    have hbid : nb.id = b := node?_id_eq g b nb hnb
    have hbs : b.id.step = 0 := by rw [← hab, hs]; rfl
    have hpa : a.parent_id = none := by
      have := c.rc.rootz na hma (by rw [haid, hs]; rfl); rw [haid] at this; exact this
    have hpb : b.parent_id = none := by
      have := c.rc.rootz nb hmb (by rw [hbid, hbs]); rw [hbid] at this; exact this
    have hga : a.gparent_id = none := by
      have := c.rc.gpmp.2 na hma (by rw [haid]; exact hpa); rw [haid] at this; exact this
    have hgb : b.gparent_id = none := by
      have := c.rc.gpmp.2 nb hmb (by rw [hbid]; exact hpb); rw [hbid] at this; exact this
    exact pid_ext hab (by rw [hpa, hpb]) (by rw [hga, hgb])
  | succ n ih =>
    intro a b ha hb hs hab hp
    -- the parent of a node at a positive step
    have par : ∀ z, z ∈ g.gowners → z.id.step = ((n + 1 : Nat) : Int) → ∃ cz nz,
        g.node? z = some nz ∧ cz ∈ nz.parents ∧ cz ∈ g.gowners ∧ cz.id.step = (n : Int) ∧
        some cz.id = z.parent_id ∧ z.gparent_id = cz.parent_id := by
      intro z hz hzs
      obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn z hz)
      have hm := List.mem_of_find?_eq_some hnz
      have hzid : nz.id = z := node?_id_eq g z nz hnz
      have hnr : nz.id.parent_id ≠ none := c.rc.shape.notroot nz hm (by rw [hzid, hzs]; omega)
      have hne : nz.parents ≠ [] := by
        rcases ((isValidNode_iff g nz).mp (c.pc.ker.valid z nz hnz)).2.1 with h | h
        · exact absurd (Option.isNone_iff_eq_none.mp h) hnr
        · exact h
      obtain ⟨cz, hcz⟩ := List.exists_mem_of_ne_nil _ hne
      have hlink := (c.pc.ker.linkP z nz hnz cz hcz).1
      refine ⟨cz, nz, hnz, hcz, c.pc.ker.own z nz hnz cz hlink, ?_, ?_, ?_⟩
      · have := c.pc.pb nz hm cz hcz; rw [hzid, hzs] at this; rw [this]; omega
      · have := c.rc.pmp nz hm cz hcz; rw [hzid] at this; exact this
      · have := c.rc.gpmp.1 nz hm cz hcz; rw [hzid] at this; exact this
    obtain ⟨ca, _, _, _, hcag, hcas, hpa, hga⟩ := par a ha hs
    obtain ⟨cb, _, _, _, hcbg, hcbs, hpb, hgb⟩ := par b hb (by rw [← hab]; exact hs)
    have hcid : ca.id = cb.id :=
      ids_eq_of_choiceAt g n (hp n (by omega) (by omega)) ca cb (mem_ownersAt hcag hcas)
        (mem_ownersAt hcbg hcbs)
    have hc : ca = cb := ih ca cb hcag hcbg hcas hcid (prefix_mono hp (by omega))
    subst hc
    exact pid_ext hab (by rw [← hpa, ← hpb]) (by rw [hga, hgb])

/-- **Below the choice the path is fixed**: two global owners of the same map node at a step `≤ k` are
the same path node. -/
theorem gowner_eq (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (a b : PathNodeId) (ha : a ∈ g.gowners)
    (hb : b ∈ g.gowners) (h0 : 0 ≤ a.id.step) (hk : a.id.step ≤ k) (hab : a.id = b.id) : a = b := by
  have e : ((a.id.step.toNat : Nat) : Int) = a.id.step := Int.toNat_of_nonneg h0
  exact gowner_eq_nat c a.id.step.toNat a b ha hb e.symm hab (by rw [e]; exact prefix_mono hp hk)

/-- Below the choice, any three tables share the step's node. -/
theorem share_below (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (y : PathNodeId) (ny : PNodeM)
    (hy : g.node? y = some ny) (w : PathNodeId) (nw : PNodeM) (hw : g.node? w = some nw)
    (x : PathNodeId) (nx : PNodeM) (hx : g.node? x = some nx) (l : Int) (h0 : 0 ≤ l) (hl : l < k)
    (h1 : l < g.current_step) :
    ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r ∈ nx.owners ∧ r.id.step = l := by
  obtain ⟨ry, hry, hrys⟩ := entry_at c y ny hy l h0 h1
  obtain ⟨rw', hrw, hrws⟩ := entry_at c w nw hw l h0 h1
  obtain ⟨rx, hrx, hrxs⟩ := entry_at c x nx hx l h0 h1
  have gy := c.pc.ker.own y ny hy ry hry
  have gw := c.pc.ker.own w nw hw rw' hrw
  have gx := c.pc.ker.own x nx hx rx hrx
  have hch := hp l h0 hl
  have e1 : ry = rw' := gowner_eq c hp ry rw' gy gw (by rw [hrys]; exact h0) (by rw [hrys]; omega)
    (ids_eq_of_choiceAt g l hch ry rw' (mem_ownersAt gy hrys) (mem_ownersAt gw hrws))
  have e2 : ry = rx := gowner_eq c hp ry rx gy gx (by rw [hrys]; exact h0) (by rw [hrys]; omega)
    (ids_eq_of_choiceAt g l hch ry rx (mem_ownersAt gy hrys) (mem_ownersAt gx hrxs))
  refine ⟨ry, hry, ?_, ?_, hrys⟩
  · rw [e1]; exact hrw
  · rw [e2]; exact hrx

-- ============================================================
-- The window fixes the bit
-- ============================================================

theorem excl_of_exclusive (x : PathNodeId) (ny : PNodeM) (h : Exclusive x ny) : excl x ny = true := by
  refine List.all_eq_true.mpr (fun q hq => ?_)
  cases hs : (q.id.step == x.id.step) with
  | false => rfl
  | true =>
    rw [h q hq (eq_of_beq hs)]
    simp only [Bool.not_true, Bool.false_or]
    exact beq_iff_eq.mpr rfl

/-- **A node at steps `k … k+2` that owns `x` is exclusive to it.** -/
theorem excl_near (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (x : PathNodeId) (hx : x ∈ g.gowners)
    (hxs : x.id.step = k) (hk0 : 0 ≤ k) (y : PathNodeId) (ny : PNodeM) (hy : g.node? y = some ny)
    (hxy : x ∈ ny.owners) (hlo : k ≤ y.id.step)
    -- idx: the three-step window (one gpath row per map step, bin map too)
    (hhi : y.id.step ≤ k + 2) : excl x ny = true := by
  refine excl_of_exclusive x ny (fun q hq hqs => ?_)
  have hym := List.mem_of_find?_eq_some hy
  have hyid : ny.id = y := node?_id_eq g y ny hy
  have hqg := c.pc.ker.own y ny hy q hq
  -- same map node as `x` at step `k` is the same path node
  have fin : q.id = x.id → q = x := fun hid =>
    gowner_eq c hp q x hqg hx (by rw [hqs, hxs]; exact hk0) (by rw [hqs, hxs]; exact Int.le_refl k) hid
  rcases Int.lt_or_le k y.id.step with hlt | hle
  · rcases Int.lt_or_le (k + 1) y.id.step with hlt2 | hle2
    · -- step `k + 2`: the grandparent id names the bit
      -- idx: gpath rows two apart (one row per map step, bin map too)
      have e := gparentId_of_owner c y ny hy (by omega) q hq (by omega)
      -- idx: gpath rows two apart (one row per map step, bin map too)
      have e' := gparentId_of_owner c y ny hy (by omega) x hxy (by omega)
      rw [← e'] at e
      exact fin (Option.some.inj e)
    · -- step `k + 1`: the parent id names the bit
      -- idx: adjacent gpath rows (one row per map step, bin map too)
      have e := parentId_of_owner c y ny hy (by omega) q hq (by omega)
      -- idx: adjacent gpath rows (one row per map step, bin map too)
      have e' := parentId_of_owner c y ny hy (by omega) x hxy (by omega)
      rw [← e'] at e
      exact fin (Option.some.inj e)
  · -- step `k`: a table holds only the node itself at its own step
    have hys : y.id.step = k := Int.le_antisymm hle hlo
    have e := c.pc.oos ny hym q hq (by rw [hyid, hqs, hxs, hys])
    have e' := c.pc.oos ny hym x hxy (by rw [hyid, hxs, hys])
    rw [e, e']

-- ============================================================
-- What is left
-- ============================================================

/-- **`AmbFar`**: ambiguous pairs outside the window, at steps above the choice. -/
def AmbFar (g : GPathM) (k : Int) (x : PathNodeId) : Prop :=
  ∀ y ny w nw nx, g.node? y = some ny → g.node? w = some nw → g.node? x = some nx →
    x ∈ ny.owners → x ∈ nw.owners → w ∈ ny.owners → excl x ny = false → excl x nw = false →
    -- idx: outside the three-step window (one gpath row per map step, bin map too)
    (y.id.step < k ∨ k + 3 ≤ y.id.step) → (w.id.step < k ∨ k + 3 ≤ w.id.step) →
    ∀ l, k < l → l < g.current_step → ∃ r ∈ ny.owners, r ∈ nw.owners ∧ r ∈ nx.owners ∧ r.id.step = l

theorem far_of_ambiguous (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (x : PathNodeId)
    (hx : x ∈ g.gowners) (hxs : x.id.step = k) (hk0 : 0 ≤ k) (y : PathNodeId) (ny : PNodeM)
    (hy : g.node? y = some ny) (hxy : x ∈ ny.owners) (e : excl x ny = false) :
    -- idx: outside the three-step window (one gpath row per map step, bin map too)
    y.id.step < k ∨ k + 3 ≤ y.id.step := by
  rcases Int.lt_or_le y.id.step k with h | h
  · exact Or.inl h
  · rcases Int.lt_or_le (k + 2) y.id.step with h2 | h2
    · exact Or.inr (by omega)
    · rw [excl_near c hp x hx hxs hk0 y ny hy hxy h h2] at e; cases e

/-- **`AmbTri ⇐ AmbFar`**. -/
theorem ambTri_of_ambFar (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (hk0 : 0 ≤ k) (x : PathNodeId)
    (hx : x ∈ ownersAt g.gowners k) (h : AmbFar g k x) : AmbTri g x := by
  obtain ⟨hxg, hxs'⟩ := List.mem_filter.mp hx
  have hxs : x.id.step = k := eq_of_beq hxs'
  intro y ny w nw nx hy hw hxn hxy hxw hwy ey ew l h0 h1
  rcases Int.lt_or_le l k with hl | hl
  · exact share_below c hp y ny hy w nw hw x nx hxn l h0 hl h1
  · rcases Int.lt_or_le k l with hl2 | hl2
    · exact h y ny w nw nx hy hw hxn hxy hxw hwy ey ew (far_of_ambiguous c hp x hxg hxs hk0 y ny hy hxy ey)
        (far_of_ambiguous c hp x hxg hxs hk0 w nw hw hxw ew) l hl2 h1
    · exact ⟨x, hxy, hxw, self_own c x nx hxn, by rw [hxs]; exact Int.le_antisymm hl hl2⟩

-- ============================================================
-- With the reader
-- ============================================================

variable (φ : Cnf)

theorem aCtx_readPins (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (ps : List NodeId) (g : GPathM) (hp : ReadPins (filterAll kv.2 []) ps g) (hv : isValid g = true) :
    ACtx g := by
  obtain ⟨cm, _⟩ := SymMachine.machine_ctx φ hbd kv hkv
  have c₀ := Reader.RCtx_filterAll kv.2 cm []
  exact ⟨pinCtx_readPins φ hbd kv hkv ps g hp hv, NoDeadEnd.rctx_readPins _ c₀ ps g hp⟩

/-- `AmbFar` at the first choice, along the reader. -/
def AmbFarReader (g₀ : GPathM) : Prop :=
  ∀ g, ReadFirst g₀ g → isValid g = true → ∀ k, firstChoice g = some k →
    ∃ q ∈ ownersAt g.gowners k, AmbFar g k q

theorem triPinReader_of_ambFar (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (ha : AmbFarReader (filterAll kv.2 [])) : TriPinReader (filterAll kv.2 []) := by
  intro g hF hv k hf
  obtain ⟨q, hq, hqa⟩ := ha g hF hv k hf
  obtain ⟨ps, hp⟩ := OtherBitSem.readPins_of_readFirst _ g hF
  have c := aCtx_readPins φ hbd kv hkv ps g hp hv
  have hk0 : 0 ≤ k := by
    unfold firstChoice at hf
    exact mem_intRange_lower (List.mem_of_find?_eq_some hf)
  exact ⟨q, hq, triPin_of_ambTri c.pc q
    (ambTri_of_ambFar c (prefixUpTo_firstChoice g k hf) hk0 q hq hqa)⟩

/-- **The reader decides `φ` when, at every valid state it visits, some node of the first choice
satisfies the triple rule on the ambiguous pairs outside its window.** -/
theorem readerVerdictW_iff_of_ambFar (hbd : Bounded φ)
    (ha : ∀ kv ∈ pureRun φ, AmbFarReader (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ :=
  readerVerdictW_iff_of_triPin φ hbd (fun kv hkv => triPinReader_of_ambFar φ hbd kv hkv (ha kv hkv))

/-- info: 'AbsSatBin.GraphPath.Model.AmbTriCore.ambTri_of_ambFar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ambTri_of_ambFar

/-- info: 'AbsSatBin.GraphPath.Model.AmbTriCore.readerVerdictW_iff_of_ambFar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_ambFar

end AbsSatBin.GraphPath.Model.AmbTriCore
