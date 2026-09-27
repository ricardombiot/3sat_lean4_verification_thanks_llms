-- lean/improves_bin/AbsSatBin/GraphPath/Model/KeyRules.lean
import AbsSatBin.GraphPath.Model.M1bOwn

/-!
# The two rules of the key row (`docs/bitacora/verificacion_inseguridad_autor_v196.md` §3, §3.5)

A joined state `J` of line `n+1` is the union of its pieces `P_k = upF X_k d`, one per key `k` (the map node of step `n`
of the source `X_k`). Its key row is step `n = current_step - 2`. The Julia implementation lives on branch
`julia_key_rules` (`graph_path_key.jl`); here are the same two rules on the list model, as operations on top of the
existing ones (nothing of the machine or of the old review changes).

* **Key tag** (`KEY_MODE`). Pinning a key `k` keeps, in every table, only the entries of the piece of `k`
  (`restrictTo g P`, `P` the piece). The tags of the Julia code are exact (measured, `keytags_probe.jl`), so here the
  tag of an entry is its membership in the piece's table: the key tag is given by a map `pc` from keys to pieces.
  Rows at and above the key row are pure, so restricting them too changes nothing that survives the review.
* **Key check** (`KEYCHECK_MODE`). At a fixpoint of the review, every live key `k` is pinned (with its tag) in a copy;
  the keys whose copy is invalid are dropped from the global owners (`deadKeys`, `dropKeys`), all at once, and the
  review goes on (`reviewKC`). Unlike the Julia draft, the model checks a single live key too: with mixed tables one key
  can still die when its tag is applied.

What is proved (all with `[propext, Quot.sound]` only):
* **`m1_keyRules`**: in a joined state of line `n+1`, if the filter with both rules (`filterKC`) leaves a pin set valid,
  some piece is valid under the ordinary filter with the same pins. It is M1 for the joins where the rules act. The key
  check gives a live key whose tagged pin survives (`kc_spec`); the tag puts that state below the key's piece
  (`below_piece`); and a valid kernel below the piece that agrees with the pins makes the piece's filter valid.
* **`below_reviewKC`**: the review with the key check never goes below a **key-closed** kernel (`KeyClosed`: every
  live key of its key row survives its tagged pin with a valid kernel below). A live key of the kernel survives its
  tagged pin in every larger state (`survives_of_keyClosed`), so it is never dropped; and every round that drops keys
  lowers the measure (`measure_dropKeys_lt`), so the fuel does not run out.
* **`isValid_filterKC_of_kernel`**: `Kernel.isValid_filterAll_of_kernel` for the new filter. A pin set survives when a
  valid key-closed kernel below the state agrees with the pins and carries the tag of every pin of the key row
  (`TagBelow`).

**What it does not give.** The reader's induction (`FExtInd.lExt_succ`) needs M1 at **every** line for the filter it
uses on the sources `X` of the pieces, which are joined states too. Going down from a piece to its source (M2w) with
the new filter on `X` needs the kernel that comes from the piece to be key-closed and to carry the tags of `X`'s key row
(the hypotheses of `isValid_filterKC_of_kernel` at line `n`). Tags that live one line do not give that: the piece keeps
the mixed tables of `X` below its own key row. So these rules close M1 where they act, not the whole induction; see
v196 §6.
-/

namespace AbsSatBin.GraphPath.Model.KeyRules

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.Threaded (OwnSymmetric)

-- ============================================================
-- The key tag: restricting the tables to a piece
-- ============================================================

/-- A node with its table restricted to the table the piece `P` has for it (empty if `P` does not have it). -/
def rkNode (P : GPathM) (n : PNodeM) : PNodeM :=
  { n with owners := match P.node? n.id with
      | some m => n.owners.filter (fun v => m.owners.contains v)
      | none => [] }

/-- **The key tag**: every table restricted to the piece `P`. -/
def restrictTo (g P : GPathM) : GPathM := { g with nodes := g.nodes.map (rkNode P) }

theorem rkNode_id (P : GPathM) (n : PNodeM) : (rkNode P n).id = n.id := rfl

theorem restrictTo_node? (g P : GPathM) (p : PathNodeId) :
    (restrictTo g P).node? p = (g.node? p).map (rkNode P) := by
  unfold restrictTo node?
  rw [List.find?_map]
  rfl

theorem mem_rk_owners {P : GPathM} {n : PNodeM} {v : PathNodeId} (h : v ∈ (rkNode P n).owners) :
    v ∈ n.owners ∧ ∃ m, P.node? n.id = some m ∧ v ∈ m.owners := by
  unfold rkNode at h
  cases hm : P.node? n.id with
  | none => rw [hm] at h; exact absurd h List.not_mem_nil
  | some m =>
    rw [hm] at h
    obtain ⟨hv, hc⟩ := List.mem_filter.mp h
    exact ⟨hv, m, rfl, List.mem_of_elem_eq_true hc⟩

theorem mem_rk_owners_of {P : GPathM} {n m : PNodeM} {v : PathNodeId} (hm : P.node? n.id = some m)
    (hv : v ∈ n.owners) (hvm : v ∈ m.owners) : v ∈ (rkNode P n).owners := by
  unfold rkNode; rw [hm]; exact List.mem_filter.mpr ⟨hv, List.elem_eq_true_of_mem hvm⟩

theorem pruned_restrictTo (g P : GPathM) : Pruned g (restrictTo g P) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := hq
  nodes_derived n' hn' := by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hn'
    exact ⟨n, hn, rfl, fun q hq => (mem_rk_owners hq).1, fun _ hp => hp⟩

theorem keeps_restrictTo (g P : GPathM) : ReaderAgg.Keeps g (restrictTo g P) := by
  refine ⟨pruned_restrictTo g P, fun h q hq => ?_, fun h n hn p hp => ?_, ?_⟩
  · obtain ⟨n, hn, hid⟩ := h q hq
    exact ⟨rkNode P n, List.mem_map_of_mem hn, hid⟩
  · obtain ⟨n0, hn0, rfl⟩ := List.mem_map.mp hn
    obtain ⟨m, hm, hid⟩ := h n0 hn0 p hp
    exact ⟨rkNode P m, List.mem_map_of_mem hm, hid⟩
  · have : NodeIds.Ids (restrictTo g P) = NodeIds.Ids g := NodeIds.ids_map g (rkNode P) (rkNode_id P)
    rw [this]; exact List.Sublist.refl _

/-- What the key tag needs from a piece: its tables are symmetric and name nodes of it. -/
def TagOk (P : GPathM) : Prop :=
  OwnSymmetric P ∧ ∀ p m, P.node? p = some m → ∀ v ∈ m.owners, ∃ mv, P.node? v = some mv

theorem tagOk_empty : TagOk GPathM.empty := by
  refine ⟨fun p n _ _ hp => ?_, fun p m hp => ?_⟩ <;> simp [node?, GPathM.empty] at hp

theorem sym_restrictTo {g P : GPathM} (hg : OwnSymmetric g) (hP : TagOk P) : OwnSymmetric (restrictTo g P) := by
  intro p n q m hn hm hq
  rw [restrictTo_node?] at hn hm
  obtain ⟨n0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨m0, hm0, rfl⟩ := Option.map_eq_some_iff.mp hm
  obtain ⟨hq0, a, ha, hqa⟩ := mem_rk_owners hq
  have hn0id : n0.id = p := node?_id_eq g p n0 hn0
  have hm0id : m0.id = q := node?_id_eq g q m0 hm0
  rw [hn0id] at ha
  obtain ⟨b, hb⟩ := hP.2 p a ha q hqa
  exact mem_rk_owners_of (by rw [hm0id]; exact hb) (hg p n0 q m0 hn0 hm0 hq0) (hP.1 p a q b ha hb hqa)

theorem ownAbove_restrictTo {g P : GPathM} (h : KernelReader.OwnAbove g) : KernelReader.OwnAbove (restrictTo g P) :=
  KernelReader.ownAbove_of_pruned (pruned_restrictTo g P) h

theorem sAbove_restrictTo {g P : GPathM} (h : Sons.SAbove g) : Sons.SAbove (restrictTo g P) := by
  intro n hn s hs
  obtain ⟨n0, hn0, rfl⟩ := List.mem_map.mp hn
  exact h n0 hn0 s hs

-- ============================================================
-- The key check
-- ============================================================

/-- The key row: the step below the top. -/
def keyRow (g : GPathM) : Int := g.current_step - 2

/-- Pinning the key `k`, with its tag, leaves the state valid. -/
def survives (pc : NodeId → GPathM) (g : GPathM) (k : NodeId) : Bool :=
  isValid (review (restrictTo (filterRequire g k) (pc k)))

/-- The live keys whose tagged pin kills the state. -/
def deadKeys (pc : NodeId → GPathM) (g : GPathM) : List NodeId :=
  ((ownersAt g.gowners (keyRow g)).map (·.id)).filter (fun k => !survives pc g k)

/-- Drop the dead keys from the global owners. -/
def dropKeys (g : GPathM) (dead : List NodeId) : GPathM :=
  { g with gowners := g.gowners.filter (fun q => !dead.contains q.id) }

/-- **The review with the key check**: the review to its fixpoint; then the keys whose tagged pin dies are dropped,
and again. Running out of fuel gives an invalid state. -/
def reviewKC (pc : NodeId → GPathM) : Nat → GPathM → GPathM
  | 0, g => { g with gowners := [] }
  | f + 1, g =>
    if isValid (review g) then
      if (deadKeys pc (review g)).isEmpty then review g
      else reviewKC pc f (dropKeys (review g) (deadKeys pc (review g)))
    else review g

/-- The tags of the pins at the key row `s`. -/
def tagPins (pc : NodeId → GPathM) (s : Int) (ps : List NodeId) (g : GPathM) : GPathM :=
  ps.foldl (fun h r => if r.step = s then restrictTo h (pc r) else h) g

/-- **The filter with both rules.** -/
def filterKC (pc : NodeId → GPathM) (g : GPathM) (ps : List NodeId) : GPathM :=
  let X₀ := tagPins pc (keyRow g) ps (ps.foldl filterRequire g)
  reviewKC pc (measure X₀ + 1) X₀

theorem pruned_dropKeys (g : GPathM) (dead : List NodeId) : Pruned g (dropKeys g dead) where
  step_eq := rfl
  map_parent_eq := rfl
  gowners_sub _ hq := (List.mem_filter.mp hq).1
  nodes_derived n hn := ⟨n, hn, rfl, fun _ h => h, fun _ h => h⟩

theorem keeps_dropKeys (g : GPathM) (dead : List NodeId) : ReaderAgg.Keeps g (dropKeys g dead) :=
  ⟨pruned_dropKeys g dead, fun h q hq => h q (List.mem_filter.mp hq).1, fun h => h, List.Sublist.refl _⟩

theorem pruned_tagPins (pc : NodeId → GPathM) (s : Int) :
    ∀ (ps : List NodeId) (g : GPathM), Pruned g (tagPins pc s ps g) ∧ (tagPins pc s ps g).gowners = g.gowners := by
  intro ps
  induction ps with
  | nil => intro g; exact ⟨Pruned.refl g, rfl⟩
  | cons r rs ih =>
    intro g
    unfold tagPins
    simp only [List.foldl_cons]
    by_cases hr : r.step = s
    · simp only [hr, if_true]
      obtain ⟨h1, h2⟩ := ih (restrictTo g (pc r))
      exact ⟨Pruned.trans (pruned_restrictTo g (pc r)) h1, h2⟩
    · simp only [hr, if_false]
      exact ih g


-- ============================================================
-- What the rules keep
-- ============================================================

/-- The invariant carried by the review with the key check: the reader context, symmetric tables, owners and sons in
place, and pruned from the start. -/
structure Inv (X₀ g : GPathM) : Prop where
  rc  : Reader.RCtx g
  sym : OwnSymmetric g
  ab  : KernelReader.OwnAbove g
  sa  : Sons.SAbove g
  pr  : Pruned X₀ g

theorem inv_review {X₀ g : GPathM} (hI : Inv X₀ g) (hv : isValid (review g) = true) : Inv X₀ (review g) where
  rc := Reader.RCtx_filterAll g hI.rc []
  sym := PairInactive.OwnSymmetric_review g (SymMachine.revOk_foldl g hI.rc hI.sym []) hv
  ab := KernelReader.ownAbove_of_pruned (pruned_review g) hI.ab
  sa := Sons.SAbove_review g hI.sa
  pr := Pruned.trans hI.pr (pruned_review g)

theorem inv_dropKeys {X₀ g : GPathM} (hI : Inv X₀ g) (dead : List NodeId) : Inv X₀ (dropKeys g dead) where
  rc := ReaderAgg.RCtx_of_keeps (keeps_dropKeys g dead) hI.rc
  sym := fun p n q m hn hm hq => hI.sym p n q m hn hm hq
  ab := KernelReader.ownAbove_of_pruned (pruned_dropKeys g dead) hI.ab
  sa := hI.sa
  pr := Pruned.trans hI.pr (pruned_dropKeys g dead)

theorem invalid_of_no_gowners (g : GPathM) (hcs : 1 ≤ g.current_step) :
    isValid { g with gowners := [] } = false := by
  cases h : isValid { g with gowners := [] } with
  | false => rfl
  | true =>
    have hmem : (0 : Int) ∈ intRange 0 (g.current_step - 1) := mem_intRange_zero 0 _ (by omega) (by omega)
    have := List.all_eq_true.mp h 0 hmem
    simp [hasStepEntry] at this

/-- **A valid output of the review with the key check** is the review of a state that keeps the invariant, and no live
key dies at it. -/
theorem kc_spec (pc : NodeId → GPathM) (X₀ : GPathM) (hcs : 1 ≤ X₀.current_step) :
    ∀ (f : Nat) (g : GPathM), Inv X₀ g → isValid (reviewKC pc f g) = true →
      ∃ h, Inv X₀ h ∧ reviewKC pc f g = review h ∧ isValid (review h) = true ∧ deadKeys pc (review h) = [] := by
  intro f
  induction f with
  | zero =>
    intro g hI hv
    have hg : 1 ≤ g.current_step := by rw [hI.pr.step_eq]; exact hcs
    simp only [reviewKC] at hv
    rw [invalid_of_no_gowners g hg] at hv; cases hv
  | succ f ih =>
    intro g hI hv
    simp only [reviewKC] at hv ⊢
    by_cases h1 : isValid (review g) = true
    · rw [if_pos h1] at hv ⊢
      by_cases h2 : (deadKeys pc (review g)).isEmpty = true
      · rw [if_pos h2]
        exact ⟨g, hI, rfl, h1, List.isEmpty_iff.mp h2⟩
      · rw [if_neg h2] at hv ⊢
        exact ih _ (inv_dropKeys (inv_review hI h1) _) hv
    · rw [if_neg h1] at hv; exact absurd hv h1

-- ============================================================
-- The pieces as tags
-- ============================================================

section
variable (φ : Cnf) (hbd : Bounded φ)

/-- The piece of the key `k` for the destination `d`: the state of line `n` at `k`, sent to `d` (empty if there is no
valid one). This is the tag map of a joined state of line `n+1` at `d`. -/
def pieceOf (n : Nat) (d : NodeId) (k : NodeId) : GPathM :=
  match (line φ n).find? (fun kv => kv.1 == k) with
  | some kv => if d ∈ sonsOfMap φ kv.1 ∧ isValid (upF φ kv.2 d) = true then upF φ kv.2 d else GPathM.empty
  | none => GPathM.empty

theorem pieceOf_eq (n : Nat) (d : NodeId) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (hd : d ∈ sonsOfMap φ kv.1)
    (hv : isValid (upF φ kv.2 d) = true) : pieceOf φ n d kv.1 = upF φ kv.2 d := by
  unfold pieceOf
  cases hf : (line φ n).find? (fun kv' => kv'.1 == kv.1) with
  | none =>
    have := List.find?_eq_none.mp hf kv hkv
    simp at this
  | some kv0 =>
    have hp := List.find?_some hf
    have hk0 : kv0.1 = kv.1 := eq_of_beq hp
    have e := key_inj (line φ n) (lineOk φ n).1 kv0 (List.mem_of_find?_eq_some hf) kv hkv hk0
    subst e
    simp only
    rw [if_pos ⟨hd, hv⟩]

include hbd in
theorem pieceOf_tagOk (n : Nat) (d k : NodeId) : TagOk (pieceOf φ n d k) := by
  unfold pieceOf
  cases hf : (line φ n).find? (fun kv' => kv'.1 == k) with
  | none => exact tagOk_empty
  | some kv =>
    simp only
    by_cases hc : d ∈ sonsOfMap φ kv.1 ∧ isValid (upF φ kv.2 d) = true
    · rw [if_pos hc]
      have hkv := List.mem_of_find?_eq_some hf
      have hP := StateOk_sent φ n kv ((lineOk φ n).2 kv hkv) d hc.1 hc.2
      have hreach := MapReachable.reachable_of_mapReachable φ hbd _ hP.reach
      have hk := KernelUp.kernel_reachable (reqOf φ) (isProhibited φ) _ hreach hc.2
      exact ⟨(SymMachine.symInv_reachable (reqOf φ) (isProhibited φ) _ hreach hc.2).1,
        fun p m hp v hv => hk.isNode_owner p m hp v hv⟩
    · rw [if_neg hc]; exact tagOk_empty

end

theorem inv_tagPins (pc : NodeId → GPathM) (hpc : ∀ k, TagOk (pc k)) (s : Int) (X₀ : GPathM) :
    ∀ (ps : List NodeId) (g : GPathM), Inv X₀ g → Inv X₀ (tagPins pc s ps g) := by
  intro ps
  induction ps with
  | nil => intro g hI; exact hI
  | cons r rs ih =>
    intro g hI
    unfold tagPins
    simp only [List.foldl_cons]
    by_cases hr : r.step = s
    · simp only [hr, if_true]
      refine ih _ ⟨ReaderAgg.RCtx_of_keeps (keeps_restrictTo g (pc r)) hI.rc, sym_restrictTo hI.sym (hpc r),
        ownAbove_restrictTo hI.ab, sAbove_restrictTo hI.sa, Pruned.trans hI.pr (pruned_restrictTo g (pc r))⟩
    · simp only [hr, if_false]
      exact ih g hI

/-- A global owner of successive pins names the pin of its step. -/
theorem foldl_pinned : ∀ (l : List NodeId) (Y : GPathM) (q : PathNodeId), q ∈ (l.foldl filterRequire Y).gowners →
    ∀ r ∈ l, q.id.step = r.step → q.id = r := by
  intro l
  induction l with
  | nil => intro _ _ _ r hr; exact absurd hr List.not_mem_nil
  | cons r rs ih =>
    intro Y q hq r' hr' hs
    simp only [List.foldl_cons] at hq
    rcases List.mem_cons.mp hr' with rfl | hr'
    · have hq1 : q ∈ (filterRequire Y r').gowners :=
        (ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire rs _).1.gowners_sub q hq
      have := (List.mem_filter.mp hq1).2
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
      rcases this with h | h
      · exact absurd hs h
      · exact h
    · exact ih _ q hq r' hr' hs


-- ============================================================
-- The key tag puts the pinned state below the piece
-- ============================================================

section
variable (φ : Cnf) (hbd : Bounded φ)
include hbd

/-- **The key tag, by construction** (`M1bLowOwn` without proof obligation): pinning the key `k` of a state `G` of a
joined state of line `n+1` with its tag, and reviewing, gives a valid kernel below the piece of `k`. -/
theorem below_piece (n : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId) (hd : d ∈ sonsOfMap φ kv.1)
    (hvP : isValid (upF φ kv.2 d) = true) (G : GPathM) (rcG : Reader.RCtx G) (symG : OwnSymmetric G)
    (abG : KernelReader.OwnAbove G) (saG : Sons.SAbove G) (hGcs : G.current_step = (n : Int) + 2)
    (hvH : isValid (review (restrictTo (filterRequire G kv.1) (upF φ kv.2 d))) = true) :
    Kernel (review (restrictTo (filterRequire G kv.1) (upF φ kv.2 d))) ∧
      Below (upF φ kv.2 d) (review (restrictTo (filterRequire G kv.1) (upF φ kv.2 d))) ∧
      Pruned G (review (restrictTo (filterRequire G kv.1) (upF φ kv.2 d))) := by
  let P := upF φ kv.2 d
  have hPdef : P = upF φ kv.2 d := rfl
  let Y := restrictTo (filterRequire G kv.1) P
  have hYdef : Y = restrictTo (filterRequire G kv.1) P := rfl
  have hPok := StateOk_sent φ n kv ((lineOk φ n).2 kv hkv) d hd hvP
  have hPcs : P.current_step = (n : Int) + 2 := by rw [hPok.step]; omega
  have pcP := M1Parts.piece_pinCtx φ hbd n kv hkv d hd hvP
  have tP := pieceOf_tagOk φ hbd n d kv.1
  rw [pieceOf_eq φ n d kv hkv hd hvP] at tP
  -- the context of the tagged pin
  have kY : ReaderAgg.Keeps G Y :=
    ReaderAgg.Keeps.trans (ReaderAgg.keeps_filterRequire G kv.1) (keeps_restrictTo _ P)
  have rcY := ReaderAgg.RCtx_of_keeps kY rcG
  have symY : OwnSymmetric Y := sym_restrictTo (SymMachine.sym_foldl_filterRequire [kv.1] G symG) tP
  have abY : KernelReader.OwnAbove Y := KernelReader.ownAbove_of_pruned kY.1 abG
  have saY : Sons.SAbove Y := sAbove_restrictTo (fun n hn s hs => saG n hn s hs)
  have kerH := KernelReader.kernel_of_review Y rcY symY abY hvH
  have rcH : Reader.RCtx (review Y) := Reader.RCtx_filterAll Y rcY []
  have saH : Sons.SAbove (review Y) := Sons.SAbove_review Y saY
  have pcH : KernelSplit.PinCtx (review Y) :=
    ⟨kerH, rcH.nodup, rcH.oos, rcH.shape.pbelow, saH, rcH.snn, rcH.below⟩
  have hbY : Below Y (review Y) := KernelIff.below_filterAll_self Y rcY.nodup []
  have hHcs : (review Y).current_step = (n : Int) + 2 := by rw [← hbY.step]; exact hGcs
  -- every node of the reviewed tagged pin is a node of the piece, with a smaller table
  have toP : ∀ p nh, (review Y).node? p = some nh →
      ∃ m, P.node? p = some m ∧ ∀ v ∈ nh.owners, v ∈ m.owners := by
    intro p nh hnh
    obtain ⟨ny, hny, ho, _, _⟩ := hbY.node p nh hnh
    rw [hYdef, restrictTo_node?] at hny
    obtain ⟨n0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hny
    have hn0id : n0.id = p := node?_id_eq _ p n0 hn0
    obtain ⟨_, m, hm, _⟩ := mem_rk_owners (ho p (TriPinCut.self_own_pc pcH p nh hnh))
    rw [hn0id] at hm
    refine ⟨m, hm, fun v hv => ?_⟩
    obtain ⟨_, m', hm', hvm'⟩ := mem_rk_owners (ho v hv)
    rw [hn0id, hm] at hm'; cases hm'; exact hvm'
  refine ⟨kerH, ⟨by rw [hPcs, hHcs], fun z hz => ?_, fun p nh hnh => ?_⟩, Pruned.trans kY.1 (pruned_review Y)⟩
  · obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp (kerH.gn z hz)
    obtain ⟨m, hm, _⟩ := toP z nz hnz
    exact pcP.ker.gow z m hm
  · obtain ⟨m, hm, ho⟩ := toP p nh hnh
    have hnhid : nh.id = p := node?_id_eq _ p nh hnh
    refine ⟨m, hm, ho, fun c hc => ?_, fun c hc => ?_⟩
    · obtain ⟨hco, nc, hnc, _⟩ := kerH.linkP p nh hnh c hc
      have hcs : c.id.step = p.id.step - 1 := by
        have := pcH.pb nh (List.mem_of_find?_eq_some hnh) c hc; rw [hnhid] at this; exact this
      have hc0 : 0 ≤ c.id.step := by
        have := pcH.snn nc (List.mem_of_find?_eq_some hnc); rw [node?_id_eq _ c nc hnc] at this; exact this
      exact (KernelSplit.parent_of_owner pcP p m hm (by omega) c (ho c hco) hcs).1
    · obtain ⟨hco, nc, hnc, _⟩ := kerH.linkS p nh hnh c hc
      have hcs : c.id.step = p.id.step + 1 := by
        have := pcH.sa nh (List.mem_of_find?_eq_some hnh) c hc; rw [hnhid] at this; exact this
      have hcb : c.id.step < (n : Int) + 2 := by
        have := pcH.below nc (List.mem_of_find?_eq_some hnc); rw [node?_id_eq _ c nc hnc, hHcs] at this
        exact this
      exact (KernelSplit.son_of_owner pcP p m hm (by rw [hPcs]; omega) c (ho c hco) hcs).1

-- ============================================================
-- M1 where the rules act
-- ============================================================

/-- **M1 with the two rules.** In a joined state of line `n+1`, if the filter with the key tag and the key check leaves
the pins `ps` valid, some piece is valid under the ordinary filter with the same pins. -/
theorem m1_keyRules (n : Nat) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (ps : List NodeId)
    (hv : isValid (filterKC (pieceOf φ n kv'.1) kv'.2 ps) = true) :
    ∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧ isValid (upF φ kv.2 kv'.1) = true ∧
      isValid (filterAll (upF φ kv.2 kv'.1) ps) = true := by
  let pc := pieceOf φ n kv'.1
  have hpc : pc = pieceOf φ n kv'.1 := rfl
  let J := kv'.2
  have hJ : J = kv'.2 := rfl
  have hok' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : J.current_step = (n : Int) + 2 := by rw [hJ, hok'.step]; push_cast; omega
  have hreach := MapReachable.reachable_of_mapReachable φ hbd J hok'.reach
  have hndJ := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) J hreach
  have cm := Reader.RCtx_reachable (reqOf φ) (isProhibited φ) J hndJ hreach
  have sm := (SymMachine.symInv_reachable (reqOf φ) (isProhibited φ) J hreach hok'.valid).1
  have abm := KernelReader.ownAbove_reachable (reqOf φ) (isProhibited φ) J hreach
  have sam := KernelSplit.SAbove_reachable (reqOf φ) (isProhibited φ) J hreach
  -- the start of the review: pins, then tags
  let X₁ := ps.foldl filterRequire J
  have hX₁ : X₁ = ps.foldl filterRequire J := rfl
  let X₀ := tagPins pc (keyRow J) ps X₁
  have hX₀ : X₀ = tagPins pc (keyRow J) ps X₁ := rfl
  have kX₁ := ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire ps J
  have iX₁ : Inv X₁ X₁ :=
    ⟨ReaderAgg.RCtx_of_keeps kX₁ cm, SymMachine.sym_foldl_filterRequire ps J sm,
      KernelReader.ownAbove_of_pruned kX₁.1 abm,
      fun n hn s hs => sam n (by rw [SymMachine.foldl_filterRequire_nodes] at hn; exact hn) s hs, Pruned.refl _⟩
  have iX₀' := inv_tagPins pc (fun k => pieceOf_tagOk φ hbd n kv'.1 k) (keyRow J) X₁ ps X₁ iX₁
  have hX₀X₁ := pruned_tagPins pc (keyRow J) ps X₁
  have iX₀ : Inv X₀ X₀ := ⟨iX₀'.rc, iX₀'.sym, iX₀'.ab, iX₀'.sa, Pruned.refl _⟩
  have hX₀cs : X₀.current_step = (n : Int) + 2 := by rw [hX₀X₁.1.step_eq, kX₁.1.step_eq, hcs']
  -- the review with the key check ends at a state where no live key dies
  obtain ⟨h, iH, hout, hvG, hdead⟩ := kc_spec pc X₀ (by rw [hX₀cs]; omega) _ X₀ iX₀ hv
  let G := review h
  have hG : G = review h := rfl
  have iG := inv_review iH hvG
  have hGcs : G.current_step = (n : Int) + 2 := by rw [iG.pr.step_eq, hX₀cs]
  -- a live key
  have hnmem : (n : Int) ∈ intRange 0 (G.current_step - 1) := mem_intRange_zero _ _ (by omega) (by rw [hGcs]; omega)
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hvG _ hnmem)
  have hqn : q.id.step = (n : Int) := eq_of_beq hqs
  have hsurv : survives pc G q.id = true := by
    cases hs : survives pc G q.id with
    | true => rfl
    | false =>
      have hmem : q.id ∈ deadKeys pc G := by
        refine List.mem_filter.mpr ⟨List.mem_map_of_mem (List.mem_filter.mpr ⟨hq, ?_⟩), ?_⟩
        · exact beq_iff_eq.mpr (by unfold keyRow; rw [hGcs, hqn]; omega)
        · show (!survives pc G q.id) = true
          rw [hs]; rfl
      rw [hdead] at hmem; exact absurd hmem List.not_mem_nil
  -- the key names a source
  obtain ⟨nG, hnG, hidG⟩ := iG.rc.gn q hq
  have hpJ : Pruned J G := Pruned.trans (Pruned.trans kX₁.1 hX₀X₁.1) iG.pr
  obtain ⟨nJ0, hnJ0, hidJ, _, _⟩ := hpJ.nodes_derived nG hnG
  have hnJ : J.node? q = some nJ0 := by rw [← hidG, hidJ]; exact node?_of_mem hndJ nJ0 hnJ0
  obtain ⟨kv, hkv, hd, hvP, hk, _⟩ := PieceJoin.mid_one_source φ hbd n kv' hkv' q nJ0 hnJ hqn
  have hpcq : pc q.id = upF φ kv.2 kv'.1 := by rw [hpc, hk]; exact pieceOf_eq φ n kv'.1 kv hkv hd hvP
  -- its tagged pin is a valid kernel below the piece, and it keeps the pins
  have hvH : isValid (review (restrictTo (filterRequire G kv.1) (upF φ kv.2 kv'.1))) = true := by
    have := hsurv; unfold survives at this; rw [hpcq, hk] at this; exact this
  obtain ⟨kerH, hbH, hprH⟩ := below_piece φ hbd n kv hkv kv'.1 hd hvP G iG.rc iG.sym iG.ab iG.sa hGcs hvH
  refine ⟨kv, hkv, hd, hvP, isValid_filterAll_of_kernel kerH hvH hbH ps (fun r hr z hz hzs => ?_)⟩
  have hzX₁ : z ∈ X₁.gowners := by
    have := (Pruned.trans iG.pr hprH).gowners_sub z hz
    rw [hX₀X₁.2] at this; exact this
  exact foldl_pinned ps J z hzX₁ r hr hzs

end


-- ============================================================
-- The review with the key check never goes below a key-closed kernel
-- ============================================================

/-- `h`'s tables are tables of `P` (all of `h` carries the tag of `P`). -/
def TagBelow (P h : GPathM) : Prop :=
  ∀ p nh, h.node? p = some nh → ∃ m, P.node? p = some m ∧ ∀ v ∈ nh.owners, v ∈ m.owners

/-- **Key-closed kernel**: pinning any live key of its key row, with its tag, leaves a valid kernel below it. -/
def KeyClosed (pc : NodeId → GPathM) (h : GPathM) : Prop :=
  ∀ q ∈ h.gowners, q.id.step = keyRow h → ∃ K, Kernel K ∧ isValid K = true ∧ Below (restrictTo h (pc q.id)) K ∧
    ∀ z ∈ K.gowners, z.id.step = q.id.step → z.id = q.id

/-- The key tag is monotone. -/
theorem below_restrictTo {X h : GPathM} (hb : Below X h) (P : GPathM) : Below (restrictTo X P) (restrictTo h P) where
  step := hb.step
  gow := hb.gow
  node p nh hnh := by
    rw [restrictTo_node?] at hnh ⊢
    obtain ⟨n0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hnh
    obtain ⟨nx, hnx, ho, hp, hs⟩ := hb.node p n0 hn0
    refine ⟨rkNode P nx, by rw [hnx]; rfl, fun v hv => ?_, hp, hs⟩
    obtain ⟨hv0, m, hm, hvm⟩ := mem_rk_owners hv
    have e : nx.id = n0.id := by rw [node?_id_eq _ p nx hnx, node?_id_eq _ p n0 hn0]
    exact mem_rk_owners_of (by rw [e]; exact hm) (ho v hv0) hvm

/-- A kernel that carries the tag stays below the tagged state. -/
theorem below_restrictTo_of_tag {X h : GPathM} (hb : Below X h) (P : GPathM) (ht : TagBelow P h) :
    Below (restrictTo X P) h where
  step := hb.step
  gow := hb.gow
  node p nh hnh := by
    obtain ⟨nx, hnx, ho, hp, hs⟩ := hb.node p nh hnh
    obtain ⟨m, hm, hvm⟩ := ht p nh hnh
    have e : nx.id = p := node?_id_eq _ p nx hnx
    refine ⟨rkNode P nx, by rw [restrictTo_node?, hnx]; rfl, fun v hv => ?_, hp, hs⟩
    exact mem_rk_owners_of (by rw [e]; exact hm) (ho v hv) (hvm v hv)

theorem survives_of_keyClosed (pc : NodeId → GPathM) {g h : GPathM} (hb : Below g h) (hkc : KeyClosed pc h)
    (q : PathNodeId) (hq : q ∈ h.gowners) (hqs : q.id.step = keyRow h) : survives pc g q.id = true := by
  obtain ⟨K, hK, hvK, hbK, hpK⟩ := hkc q hq hqs
  have hb1 : Below (restrictTo g (pc q.id)) K := PieceFilter.below_trans (below_restrictTo hb _) hbK
  have hb2 : Below (restrictTo (filterRequire g q.id) (pc q.id)) K := below_filterRequire hb1 q.id hpK
  exact isValid_filterAll_of_kernel hK hvK hb2 [] (fun r hr => absurd hr List.not_mem_nil)

theorem measure_dropKeys_lt (g : GPathM) (dead : List NodeId) (q : PathNodeId) (hq : q ∈ g.gowners)
    (hd : q.id ∈ dead) : measure (dropKeys g dead) < measure g := by
  have hlt : (g.gowners.filter (fun q => !dead.contains q.id)).length < g.gowners.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨q, hq, by simp; exact hd⟩
  unfold GPathM.measure dropKeys
  simp only
  omega

/-- **The review with the key check never goes below a key-closed kernel** (the argument of the review of v196,
§5.2): a live key of the kernel survives its tagged pin in any larger state, so it is never dropped. -/
theorem below_reviewKC (pc : NodeId → GPathM) {h : GPathM} (hk : Kernel h) (hkc : KeyClosed pc h) :
    ∀ (f : Nat) (g : GPathM), measure g < f → Below g h → Below (reviewKC pc f g) h := by
  intro f
  induction f with
  | zero => intro g hf; exact absurd hf (Nat.not_lt_zero _)
  | succ f ih =>
    intro g hf hb
    have hb1 : Below (review g) h := below_review hk hb
    simp only [reviewKC]
    by_cases h1 : isValid (review g) = true
    · rw [if_pos h1]
      by_cases h2 : (deadKeys pc (review g)).isEmpty = true
      · rw [if_pos h2]; exact hb1
      · rw [if_neg h2]
        obtain ⟨k, hkd⟩ := List.exists_mem_of_ne_nil _ (fun e => h2 (List.isEmpty_iff.mpr e))
        obtain ⟨hkm, _⟩ := List.mem_filter.mp hkd
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hkm
        have hqg : q ∈ (review g).gowners := (List.mem_filter.mp hq).1
        have hm := measure_dropKeys_lt (review g) _ q hqg hkd
        have hmr := PickInduction.measure_review_le g
        refine ih _ (Nat.lt_of_lt_of_le hm (Nat.le_trans hmr (Nat.le_of_lt_succ hf))) ⟨hb1.step, fun z hz => ?_, hb1.node⟩
        refine List.mem_filter.mpr ⟨hb1.gow z hz, ?_⟩
        cases hc : (deadKeys pc (review g)).contains z.id with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨hzm, hzs⟩ := List.mem_filter.mp (List.mem_of_elem_eq_true hc)
          obtain ⟨z', hz', hz'id⟩ := List.mem_map.mp hzm
          have hstep : z.id.step = keyRow h := by
            have := (List.mem_filter.mp hz').2
            unfold keyRow at this ⊢
            rw [← hz'id, eq_of_beq this, hb1.step]
          have := survives_of_keyClosed pc hb1 hkc z hz hstep
          rw [this] at hzs; cases hzs
    · rw [if_neg h1]; exact hb1

/-- **A pin set survives the filter with both rules when a valid key-closed kernel below the state agrees with the pins
and carries the tag of every pin of the key row.** It is `Kernel.isValid_filterAll_of_kernel` for `filterKC`. -/
theorem isValid_filterKC_of_kernel (pc : NodeId → GPathM) {h g : GPathM} (hk : Kernel h) (hvh : isValid h = true)
    (hkc : KeyClosed pc h) (hb : Below g h) (ps : List NodeId)
    (hpin : ∀ r ∈ ps, ∀ q ∈ h.gowners, q.id.step = r.step → q.id = r)
    (htag : ∀ r ∈ ps, r.step = keyRow g → TagBelow (pc r) h) :
    isValid (filterKC pc g ps) = true := by
  have hb1 : Below (ps.foldl filterRequire g) h := below_foldl_filterRequire ps g hb hpin
  have tag : ∀ (l : List NodeId) (X : GPathM), (∀ r ∈ l, r.step = keyRow g → TagBelow (pc r) h) → Below X h →
      Below (tagPins pc (keyRow g) l X) h := by
    intro l
    induction l with
    | nil => intro X _ hX; exact hX
    | cons r rs ih =>
      intro X ht hX
      unfold tagPins
      simp only [List.foldl_cons]
      by_cases hr : r.step = keyRow g
      · simp only [hr, if_true]
        exact ih _ (fun r' h' => ht r' (List.mem_cons_of_mem _ h'))
          (below_restrictTo_of_tag hX _ (ht r List.mem_cons_self hr))
      · simp only [hr, if_false]
        exact ih X (fun r' h' => ht r' (List.mem_cons_of_mem _ h')) hX
  have hb2 := tag ps _ htag hb1
  have hb3 : Below (filterKC pc g ps) h := below_reviewKC pc hk hkc _ _ (Nat.lt_succ_self _) hb2
  unfold isValid at hvh ⊢
  rw [hb3.step]
  refine List.all_eq_true.mpr (fun k hk' => ?_)
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hvh k hk')
  exact List.any_eq_true.mpr ⟨q, hb3.gow q hq, hqs⟩

end AbsSatBin.GraphPath.Model.KeyRules

/-- info: 'AbsSatBin.GraphPath.Model.KeyRules.m1_keyRules' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.KeyRules.m1_keyRules

/-- info: 'AbsSatBin.GraphPath.Model.KeyRules.isValid_filterKC_of_kernel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.KeyRules.isValid_filterKC_of_kernel
