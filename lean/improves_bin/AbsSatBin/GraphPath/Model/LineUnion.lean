-- lean/improves_bin/AbsSatBin/GraphPath/Model/LineUnion.lean
import AbsSatBin.GraphPath.Model.KernelUp

/-!
# The union of a line, and the join through the filter

Measured (`julia/improves_bin/test_3sat/probes/global_local_probe.jl`, `docs/context/ambfar.md` §4.2κ): the union
of the states of a line (at most two in the bin map, with different keys, which the machine never joins) creates
no clique with witnesses — each lives in one state (GL, 1.78 M cliques). This module takes that as the hypothesis
of the join step.

* **`GL φ n`**: a clique with witnesses in the union of the states of line `n` (every entry and every witness
  entry taken from some state) is a clique with witnesses of one state.
* **Through the filter** (`owns_of_join`, `req_of_join`): an entry below the top of a state of line `n+1` is an
  entry of a state of line `n`; and every node of it owns, at the step of a requirement of its key, the required
  node — both pieces of one destination share its requirements, and a filtered kernel owns at a pinned step only
  the pinned node.
* **`certR_low_of_GL`**: under `GL` and `MapCert` on line `n`, a clique with witnesses of a state of line `n+1`
  whose members lie below the top has a certificate, when no window of its key is prohibited. The clique, with the
  requirements of the key added to the constraints, has witnesses in the union of the sources; `GL` puts it in one
  source, whose certificate passes the requirements, survives the filter, and climbs to the key.
* **`certR_top_of_GL`**: the same for a clique with a member `w` at the top, with no window hypothesis. The
  witnesses own the keys of `w`'s window (`wit_owns_window`: the pair rule in `w`'s piece gives a parent of `w`,
  and the kernel's support of that parent gives its own parent, named by `PMP`), so the certificate ends right
  under `w` and climbs to `w` itself, which exists.
* **`mapCert_next_of_GL`**: both together — `GL` and `MapCert` on line `n` give `MapCert` on every state of line
  `n+1` whose key has no prohibited window.
-/

namespace AbsSatBin.GraphPath.Model.LineUnion

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.CliqueTri (Clique)
open AbsSatBin.GraphPath.Model.MapCert (MapCert WitR CertR)

variable (φ : Cnf) (n : Nat)

-- ============================================================
-- The union of a line
-- ============================================================

/-- `r` owns `q` in some state of line `n`. -/
def OwnsL (r q : PathNodeId) : Prop := ∃ kv ∈ line φ n, ∃ nr, kv.2.node? r = some nr ∧ q ∈ nr.owners

/-- A clique of the union of line `n`. -/
def CliqueL (Q : List PathNodeId) : Prop := ∀ p ∈ Q, ∀ s ∈ Q, OwnsL φ n p s

/-- Witnesses in the union of line `n`: at every step, a node owning `Q` and the map nodes `R`, each entry taken
from some state. -/
def WitL (Q : List PathNodeId) (R : List NodeId) : Prop :=
  ∀ l, 0 ≤ l → l < (n : Int) + 1 → ∃ r, r.id.step = l ∧ (∃ kv ∈ line φ n, (kv.2.node? r).isSome) ∧
    (∀ q ∈ Q, OwnsL φ n r q) ∧ ∀ m ∈ R, ∃ p, OwnsL φ n r p ∧ p.id = m

/-- **GL**: the union of line `n` creates no clique with witnesses. -/
def GL : Prop :=
  ∀ Q R, CliqueL φ n Q → WitL φ n Q R → ∃ kv ∈ line φ n, Clique kv.2 Q ∧ WitR kv.2 Q R

-- ============================================================
-- The map: a chain through the requirement of `d` ends at a parent of `d`
-- ============================================================

theorem son_of_req (k d : NodeId) (hk : k ∈ mapNodes φ n) (hd : d ∈ mapNodes φ ((n : Int) + 1))
    (hreq : ∀ r ∈ reqOf φ d, r.step = k.step → r = k) : d ∈ sonsOfMap φ k := by
  have hks := mapNodes_step φ n k hk
  have hds := mapNodes_step φ _ d hd
  unfold sonsOfMap
  split
  · next h =>
    obtain ⟨h0, h1, h2⟩ := h
    have hmid : midFusion φ = 2 * (φ.nVars : Int) + 1 := rfl  -- idx: the variable block has 2·nVars steps
    have hr : reqOf φ d = [{ step := d.step - 1, index := 1 - d.index }] := by  -- idx: a negation node requires the positive node one step below
      unfold reqOf
      rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    have e := hreq _ (by rw [hr]; exact List.mem_singleton_self _) (by show d.step - 1 = k.step; omega)  -- idx: adjacent map steps
    rw [List.mem_singleton, ← e]
    cases d
    simp only [NodeId.mk.injEq] at hds ⊢
    constructor <;> omega
  · rw [hks]; exact hd

-- ============================================================
-- Through the filter
-- ============================================================

variable (hbd : Bounded φ)
include hbd

/-- A node of a state of line `n+1` below the top is a node of a state of line `n`, and its entries below the
top are entries there. -/
theorem owns_of_join (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (r : PathNodeId) (nr : PNodeM)
    (hr : kv'.2.node? r = some nr) (hrs : r.id.step ≤ n) :
    (∃ kv ∈ line φ n, (kv.2.node? r).isSome) ∧ ∀ v ∈ nr.owners, v.id.step ≤ n → OwnsL φ n r v := by
  have tr : ∀ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 → isValid (upF φ kv.2 kv'.1) = true →
      ∀ n', (upF φ kv.2 kv'.1).node? r = some n' →
        ∃ nX, kv.2.node? r = some nX ∧ ∀ v ∈ n'.owners, v.id.step ≤ n → v ∈ nX.owners := by
    intro kv hkv hd hv n' hn'
    obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hv
    have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
    obtain ⟨nF, hnF, ho⟩ := upF_old φ kv.2 kv'.1 hdst c hv r n' hn' (by rw [hcs]; omega)
    obtain ⟨nX, hnX, hoX, _, _⟩ := (KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)).node r nF hnF
    exact ⟨nX, hnX, fun v hv hvs => hoX v (ho v hv (by rw [hcs]; omega))⟩
  refine ⟨?_, fun v hv hvs => ?_⟩
  · obtain ⟨kv, hkv, hd, hvp, n', hn'⟩ := (PieceJoin.join_no_new φ n kv' hkv').1 r nr hr
    obtain ⟨nX, hnX, _⟩ := tr kv hkv hd hvp n' hn'
    exact ⟨kv, hkv, by rw [hnX]; rfl⟩
  · obtain ⟨kv, hkv, hd, hvp, n', hn', hvn⟩ := (PieceJoin.join_no_new φ n kv' hkv').2 r nr hr v hv
    obtain ⟨nX, hnX, ho⟩ := tr kv hkv hd hvp n' hn'
    exact ⟨kv, hkv, nX, hnX, ho v hvn hvs⟩

omit hbd in
/-- In a filtered state, an entry at the step of a requirement names the required node. -/
theorem pinned_entry (X : GPathM) (d : NodeId) (p : PathNodeId)
    (hp : p ∈ (filterAll X (reqOf φ d)).gowners) (req : NodeId) (hreq : req ∈ reqOf φ d)
    (hps : p.id.step = req.step) : p.id = req := by
  have hg := (pruned_review _).gowners_sub p hp
  have hl := reqOf_length_le_one φ d
  match e : reqOf φ d with
  | [] => rw [e] at hreq; exact absurd hreq List.not_mem_nil
  | [x] =>
    rw [e] at hreq hg
    rw [List.mem_singleton.mp hreq]
    have := (List.mem_filter.mp hg).2
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
    rcases this with h | h
    · rw [List.mem_singleton.mp hreq] at hps; exact absurd hps h
    · exact h
  | _ :: _ :: _ => rw [e] at hl; simp at hl

/-- **Every node of a state of line `n+1` below the top owns, at the step of each requirement of the key, the
required node** — in the state of line `n` it comes from. -/
theorem req_of_join (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (r : PathNodeId) (nr : PNodeM)
    (hr : kv'.2.node? r = some nr) (hrs : r.id.step ≤ n) :
    ∀ req ∈ reqOf φ kv'.1, ∃ p, OwnsL φ n r p ∧ p.id = req := by
  intro req hreq
  obtain ⟨kv, hkv, hd, hvp, n', hn'⟩ := (PieceJoin.join_no_new φ n kv' hkv').1 r nr hr
  obtain ⟨hok, hdst, hcs, hdm, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hvp
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  obtain ⟨nF, hnF, _⟩ := upF_old φ kv.2 kv'.1 hdst c hvp r n' hn' (by rw [hcs]; omega)
  have hFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by
    rw [(pruned_filterAll kv.2 (reqOf φ kv'.1)).step_eq, hcs]
  have h0 := reqOf_nonneg (φ := φ) hbd kv'.1 req hreq
  have h1 := reqOf_backward φ hbd kv'.1 req hreq
  rw [mapNodes_step φ _ kv'.1 hdm] at h1
  obtain ⟨hall, _, _⟩ := (Kernel.isValidNode_iff _ nF).mp (c.pc.ker.valid r nF hnF)
  obtain ⟨p, hp, hps⟩ := List.any_eq_true.mp
    (List.all_eq_true.mp hall req.step (mem_intRange_zero _ _ h0 (by rw [hFcs]; omega)))
  have hid := pinned_entry φ kv.2 kv'.1 p (c.pc.ker.own r nF hnF p hp) req hreq (eq_of_beq hps)
  obtain ⟨nX, hnX, hoX, _, _⟩ := (KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)).node r nF hnF
  exact ⟨p, ⟨kv, hkv, nX, hnX, hoX p hp⟩, hid⟩

-- ============================================================
-- The join step, on one destination
-- ============================================================

omit hbd in
/-- Every candidate of a new row is named `d`. -/
theorem shift_id (g : GPathM) (d : NodeId) : ∀ pid ∈ shiftRowIds g d, pid.id = d := by
  intro pid hpid
  unfold shiftRowIds at hpid
  split at hpid
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp ((mem_dedupPids _ _).mp hpid); rfl
  · rw [List.mem_singleton.mp hpid]

/-- **The join step, below the top, from `GL`**: under `GL` and `MapCert` on line `n`, a clique with witnesses of
a state of line `n+1`, all of whose members lie below the top, has a certificate — when no window of the key is
prohibited. -/
theorem certR_low_of_GL (hGL : GL φ n)
    (hM : ∀ kv ∈ line φ n, MapCert kv.2) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1))
    (hsafe : ∀ pid : PathNodeId, pid.id = kv'.1 → isProhibited φ pid = false)
    (Q : List PathNodeId) (R : List NodeId) (hQ : Clique kv'.2 Q) (hW : WitR kv'.2 Q R)
    (hlow : ∀ q ∈ Q, q.id.step ≤ n) : CertR kv'.2 Q R := by
  have hok' : StateOk φ ((n + 1 : Nat) : Int) kv' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hdm : kv'.1 ∈ mapNodes φ ((n : Int) + 1) := by have := hok'.onMap; push_cast at this; exact this
  let Rl := R.filter (fun m : NodeId => decide (m.step ≤ (n : Int)))
  -- the clique, with the requirements of the key, has witnesses in the union of line `n`
  have hQL : CliqueL φ n Q := by
    intro p hp s hs
    obtain ⟨np, hnp, hpQ⟩ := hQ p hp
    exact (owns_of_join φ n hbd kv' hkv' p np hnp (hlow p hp)).2 s (hpQ s hs) (hlow s hs)
  have hWL : WitL φ n Q (Rl ++ reqOf φ kv'.1) := by
    intro l h0 h1
    obtain ⟨r, nr, hnr, hrs, hrQ, hrR⟩ := hW l h0 (by rw [hcs']; omega)
    have hrl : r.id.step ≤ n := by omega
    obtain ⟨hnode, hown⟩ := owns_of_join φ n hbd kv' hkv' r nr hnr hrl
    refine ⟨r, hrs, hnode, fun q hq => hown q (hrQ q hq) (hlow q hq), fun m hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨hmR, hms⟩ := List.mem_filter.mp hm
      obtain ⟨p, hp, hpm⟩ := hrR m hmR
      exact ⟨p, hown p hp (by rw [hpm]; exact of_decide_eq_true hms), hpm⟩
    · exact req_of_join φ n hbd kv' hkv' r nr hnr hrl m hm
  -- one source carries it, and its certificate passes the requirements
  obtain ⟨kv, hkv, hQX, hWX⟩ := hGL Q _ hQL hWL
  obtain ⟨sel, hs, hon, hR⟩ := hM kv hkv Q _ hQX hWX
  have hok : StateOk φ n kv := (lineOk φ n).2 kv hkv
  have hcs : kv.2.current_step = (n : Int) + 1 := hok.step
  have hkey : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 hok.onMap
  have hsn : (sel n).id = kv.1 := by
    obtain ⟨hsome, hstep⟩ := hs.chain.1.1 n (by omega) (by rw [hcs]; omega)
    obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp hsome
    have hself := hs.self_owned n (by omega) (by rw [hcs]; omega)
    simp only [ownersOf, hnr] at hself
    exact top_entry_key φ hbd n kv hkv _ nr hnr _ hself hstep
  have hreqs : ∀ req ∈ reqOf φ kv'.1, 0 ≤ req.step → req.step < kv.2.current_step →
      (sel req.step).id = req := fun req hreq h0 h1 => hR req (List.mem_append_right _ hreq) h0 h1
  have hson : kv'.1 ∈ sonsOfMap φ kv.1 := by
    refine son_of_req φ n kv.1 kv'.1 hok.onMap hdm (fun req hreq hst => ?_)
    have h0 := reqOf_nonneg (φ := φ) hbd kv'.1 req hreq
    rw [← hreqs req hreq h0 (by rw [hcs, hst, hkey]; omega), hst, hkey, hsn]
  -- it survives the filter and climbs to the key
  have hsF := ChainSound_filterAll kv.2 (reqOf φ kv'.1) sel hs hreqs
  have hvF : isValid (filterAll kv.2 (reqOf φ kv'.1)) = true := PickInduction.isValid_of_ChainG _ sel hsF.chain
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  have hFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by
    rw [(pruned_filterAll kv.2 (reqOf φ kv'.1)).step_eq, hcs]
  have hdF : kv'.1.step = (filterAll kv.2 (reqOf φ kv'.1)).current_step := by
    rw [hFcs, mapNodes_step φ _ kv'.1 hdm]
  have hmok : MachineOk (filterAll kv.2 (reqOf φ kv'.1)) :=
    MachineOk_of_pruned (pruned_filterAll _ _) (Certifies.MachineOk_reachable (reqOf φ) (isProhibited φ) _
      (MapReachable.reachable_of_mapReachable φ hbd kv.2 hok.reach))
  have hsA := ChainSound_addNode _ kv'.1 "" (isProhibited φ) hdF c.pc.below hmok sel hsF
    (hsafe _ (extendPid_mapId _ _ _))
  have hsk : skipsWindow (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 (isProhibited φ) = false := by
    cases e : skipsWindow (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 (isProhibited φ) with
    | false => rfl
    | true =>
      obtain ⟨pid, hpid, hf⟩ := List.any_eq_true.mp e
      rw [hsafe pid (shift_id _ _ pid hpid)] at hf; exact absurd hf (by decide)
  have hup : upF φ kv.2 kv'.1 = addNode (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 "" (isProhibited φ) := by
    show up (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 "" (isProhibited φ) = _
    unfold up; rw [if_pos hvF, hsk]; rfl
  have hvP : isValid (upF φ kv.2 kv'.1) = true := by
    rw [hup]; exact PickInduction.isValid_of_ChainG _ _ hsA.chain
  -- the certificate in the piece, then in the joined state
  obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hson hvP
  have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
  rw [← he]
  have hsP : ChainSound (upF φ kv.2 kv'.1) (extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel) := by
    rw [hup]; exact hsA
  refine ⟨_, ChainSound_of_grown hgr _ hsP, fun q hq => ?_, fun m hm h0 h1 => ?_⟩
  · rw [extend_below _ _ _ _ (by rw [hFcs]; have := hlow q hq; omega)]; exact hon q hq
  · have hcsh : h.current_step = (n : Int) + 2 := by
      have := congrArg (fun x => x.2.current_step) he; simp only at this; rw [this, hcs']
    rw [hcsh] at h1
    rcases Int.lt_or_le m.step ((n : Int) + 1) with hlt | hge
    · rw [extend_below _ _ _ _ (by rw [hFcs]; exact hlt)]
      exact hR m (List.mem_append_left _ (List.mem_filter.mpr ⟨hm, decide_eq_true (by omega)⟩)) h0
        (by rw [hcs]; exact hlt)
    · -- the constraint at the top names the key
      have hmt : m.step = (n : Int) + 1 := by omega
      rw [hmt, ← hFcs, extend_top, extendPid_mapId]
      obtain ⟨r, nr, hnr, _, _, hrR⟩ := hW m.step h0 (by rw [hcs']; omega)
      obtain ⟨p, hp, hpm⟩ := hrR m hm
      rw [← hpm]
      exact (top_entry_key φ hbd (n + 1) kv' hkv' r nr hnr p hp (by rw [hpm, hmt]; push_cast; rfl)).symm

/-- info: 'AbsSatBin.GraphPath.Model.LineUnion.certR_low_of_GL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certR_low_of_GL

-- ============================================================
-- Cliques with a member at the top
-- ============================================================

/-- **A witness of a node `w` of the top owns the keys of `w`'s window.** In the piece where it owns `w`, the pair
rule gives an entry at step `n` shared with `w`, which is a parent `x` of `w` (at its own step a node owns only
itself); and the kernel's support of `x` by its parents gives a parent of `x` that owns the witness, named, by
`PMP`, as `x`'s parent. -/
theorem wit_owns_window (hn1 : 1 ≤ n) (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1))
    (w : PathNodeId) (hws : w.id.step = (n : Int) + 1) (r : PathNodeId) (nr : PNodeM)
    (hr : kv'.2.node? r = some nr) (hrs : r.id.step ≤ n) (hwr : w ∈ nr.owners) :
    ∃ x y, OwnsL φ n r x ∧ OwnsL φ n r y ∧ w.parent_id = some x.id ∧ w.gparent_id = some y.id ∧
      x.id.step = (n : Int) ∧ y.id.step = (n : Int) - 1 := by
  obtain ⟨kv, hkv, hd, hvp, n', hn', hwn'⟩ := (PieceJoin.join_no_new φ n kv' hkv').2 r nr hr w hwr
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv kv'.1 hd hvp
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  have hP : StateOk φ ((n : Int) + 1) (kv'.1, upF φ kv.2 kv'.1) := StateOk_sent φ n kv hok kv'.1 hd hvp
  have cP := KernelUp.aCtx_reachable (reqOf φ) (isProhibited φ) _
    (MapReachable.reachable_of_mapReachable φ hbd _ hP.reach) hvp
  have hPcs : (upF φ kv.2 kv'.1).current_step = (n : Int) + 2 := by rw [hP.step]; omega
  have hFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by
    rw [(pruned_filterAll kv.2 (reqOf φ kv'.1)).step_eq, hcs]
  obtain ⟨nwP, hnwP⟩ := cP.pc.ker.isNode_owner r n' hn' w hwn'
  obtain ⟨x, hxr, hxw, hxs⟩ := cP.pc.ker.pair r n' w nwP hn' hnwP hwn' n (by omega) (by rw [hPcs]; omega)
  obtain ⟨_, hsub⟩ := upF_new φ kv.2 kv'.1 hdst c hvp w nwP hnwP (by rw [hcs]; exact hws)
  have hne : x ≠ w := by intro e; rw [e, hws] at hxs; omega
  obtain ⟨q, hq, nq, hnq, hxq⟩ := KernelUp.inherit_inv kv'.1 w x (hsub x hxw) hne
  have hqs := (rowParent_node _ kv'.1 (by rw [hFcs]; omega) hq).2
  have hqid : nq.id = q := node?_id_eq _ q nq hnq
  have hxq' : x = q := by
    have := c.pc.oos nq (List.mem_of_find?_eq_some hnq) x hxq (by rw [hqid, hqs, hxs, hFcs]; omega)
    rw [hqid] at this; exact this
  subst hxq'
  have hsh := shiftPid_of_mem_rowParents _ kv'.1 w x hq
  -- the witness, in the filtered source
  obtain ⟨nF, hnF, hoF⟩ := upF_old φ kv.2 kv'.1 hdst c hvp r n' hn' (by rw [hcs]; omega)
  have hxF : x ∈ nF.owners := hoF x hxr (by rw [hxs, hcs]; omega)
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ kv'.1)
  have lift : ∀ v ∈ nF.owners, OwnsL φ n r v := by
    intro v hv
    obtain ⟨nX, hnX, hoX, _, _⟩ := hb.node r nF hnF
    exact ⟨kv, hkv, nX, hnX, hoX v hv⟩
  -- a parent of `x` owning the witness
  have hrx : r ∈ nq.owners := c.pc.ker.sym r nF x nq hnF hnq hxF
  obtain ⟨cp, hcp, ncp, hncp, hrcp⟩ := c.pc.ker.nbrP x nq hnq (by rw [hxs]; omega) r hrx
  have hcpr : cp ∈ nF.owners := c.pc.ker.sym cp ncp r nF hncp hnF hrcp
  have hpmp := c.rc.pmp nq (List.mem_of_find?_eq_some hnq) cp hcp
  rw [hqid] at hpmp
  have hcps := c.pc.pb nq (List.mem_of_find?_eq_some hnq) cp hcp
  rw [hqid, hxs] at hcps
  refine ⟨x, cp, lift x hxF, lift cp hcpr, ?_, ?_, hxs, hcps⟩
  · rw [← hsh]; rfl
  · rw [← hsh]; exact hpmp.symm

/-- **The join step for a clique with a member `w` at the top, from `GL`.** The witnesses own the keys of `w`'s
window, so the clique below the top, with the requirements and the window added to the constraints, has
witnesses in the union of the sources; `GL` puts it in one source, whose certificate ends right under `w` and
climbs to `w` itself — which exists, so its window is not prohibited. -/
theorem certR_top_of_GL (hn1 : 1 ≤ n) (hGL : GL φ n) (hM : ∀ kv ∈ line φ n, MapCert kv.2)
    (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1)) (Q : List PathNodeId) (R : List NodeId)
    (hQ : Clique kv'.2 Q) (hW : WitR kv'.2 Q R) (w : PathNodeId) (hwQ : w ∈ Q)
    (hws : w.id.step = (n : Int) + 1) : CertR kv'.2 Q R := by
  have hok' : StateOk φ ((n + 1 : Nat) : Int) kv' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have hdm : kv'.1 ∈ mapNodes φ ((n : Int) + 1) := by have := hok'.onMap; push_cast at this; exact this
  have cJ := KernelUp.aCtx_line φ hbd (n + 1) kv' hkv'
  -- `w`, and every member of `Q` at the top is `w`
  obtain ⟨nw, hnw, hwQ'⟩ := hQ w hwQ
  have hwid : w.id = kv'.1 :=
    top_entry_key φ hbd (n + 1) kv' hkv' w nw hnw w (hwQ' w hwQ) (by rw [hws]; push_cast; rfl)
  have htop : ∀ q ∈ Q, n < q.id.step → q = w := by
    intro q hq hqs
    obtain ⟨nq, hnq, _⟩ := hQ q hq
    have hr := CertFix.step_range cJ.pc q nq hnq
    have := cJ.pc.oos nw (List.mem_of_find?_eq_some hnw) q (hwQ' q hq)
      (by rw [node?_id_eq _ w nw hnw, hws]; rw [hcs'] at hr; omega)
    rwa [node?_id_eq _ w nw hnw] at this
  have hQs : ∀ q ∈ Q, q.id.step ≤ (n : Int) + 1 := by
    intro q hq
    obtain ⟨nq, hnq, _⟩ := hQ q hq
    have := (CertFix.step_range cJ.pc q nq hnq).2; rw [hcs'] at this; omega
  -- the keys of `w`'s window
  obtain ⟨r0, nr0, hnr0, hr0s, hr0Q, _⟩ := hW 0 (by omega) (by rw [hcs']; omega)
  obtain ⟨x0, y0, _, _, hwx, hwy, hx0s, hy0s⟩ :=
    wit_owns_window φ n hbd hn1 kv' hkv' w hws r0 nr0 hnr0 (by omega) (hr0Q w hwQ)
  let Ql := Q.filter (fun q : PathNodeId => decide (q.id.step ≤ (n : Int)))
  let Rl := R.filter (fun m : NodeId => decide (m.step ≤ (n : Int)))
  have hQl : ∀ q ∈ Ql, q ∈ Q ∧ q.id.step ≤ n := fun q hq =>
    ⟨(List.mem_filter.mp hq).1, of_decide_eq_true (List.mem_filter.mp hq).2⟩
  have hQL : CliqueL φ n Ql := by
    intro p hp s hs
    obtain ⟨np, hnp, hpQ⟩ := hQ p (hQl p hp).1
    exact (owns_of_join φ n hbd kv' hkv' p np hnp (hQl p hp).2).2 s (hpQ s (hQl s hs).1) (hQl s hs).2
  have hWL : WitL φ n Ql (Rl ++ reqOf φ kv'.1 ++ [x0.id, y0.id]) := by
    intro l h0 h1
    obtain ⟨r, nr, hnr, hrs, hrQ, hrR⟩ := hW l h0 (by rw [hcs']; omega)
    have hrl : r.id.step ≤ n := by omega
    obtain ⟨hnode, hown⟩ := owns_of_join φ n hbd kv' hkv' r nr hnr hrl
    obtain ⟨x, y, hx, hy, hwx', hwy', _, _⟩ := wit_owns_window φ n hbd hn1 kv' hkv' w hws r nr hnr hrl (hrQ w hwQ)
    refine ⟨r, hrs, hnode, fun q hq => hown q (hrQ q (hQl q hq).1) (hQl q hq).2, fun m hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨hmR, hms⟩ := List.mem_filter.mp hm
        obtain ⟨p, hp, hpm⟩ := hrR m hmR
        exact ⟨p, hown p hp (by rw [hpm]; exact of_decide_eq_true hms), hpm⟩
      · exact req_of_join φ n hbd kv' hkv' r nr hnr hrl m hm
    · rcases List.mem_cons.mp hm with rfl | hm
      · refine ⟨x, hx, ?_⟩; rw [hwx] at hwx'; exact (Option.some.inj hwx').symm
      · rw [List.mem_singleton.mp hm]
        refine ⟨y, hy, ?_⟩; rw [hwy] at hwy'; exact (Option.some.inj hwy').symm
  -- one source, and its certificate
  obtain ⟨kv, hkv, hQX, hWX⟩ := hGL Ql _ hQL hWL
  obtain ⟨sel, hs, hon, hR⟩ := hM kv hkv Ql _ hQX hWX
  have hok : StateOk φ n kv := (lineOk φ n).2 kv hkv
  have hcs : kv.2.current_step = (n : Int) + 1 := hok.step
  have hkey : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 hok.onMap
  have hsn : (sel n).id = kv.1 := by
    obtain ⟨hsome, hstep⟩ := hs.chain.1.1 n (by omega) (by rw [hcs]; omega)
    obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp hsome
    have hself := hs.self_owned n (by omega) (by rw [hcs]; omega)
    simp only [ownersOf, hnr] at hself
    exact top_entry_key φ hbd n kv hkv _ nr hnr _ hself hstep
  have hreqs : ∀ req ∈ reqOf φ kv'.1, 0 ≤ req.step → req.step < kv.2.current_step →
      (sel req.step).id = req :=
    fun req hreq h0 h1 => hR req (List.mem_append_left _ (List.mem_append_right _ hreq)) h0 h1
  have hmem2 : ∀ m ∈ [x0.id, y0.id], m ∈ Rl ++ reqOf φ kv'.1 ++ [x0.id, y0.id] :=
    fun m hm => List.mem_append_right _ hm
  have hsx : (sel n).id = x0.id := by
    have := hR x0.id (hmem2 _ List.mem_cons_self) (by rw [hx0s]; omega) (by rw [hx0s, hcs]; omega)
    rwa [hx0s] at this
  have hsy : (sel ((n : Int) - 1)).id = y0.id := by
    have := hR y0.id (hmem2 _ (List.mem_cons_of_mem _ List.mem_cons_self)) (by rw [hy0s]; omega)
      (by rw [hy0s, hcs]; omega)
    rwa [hy0s] at this
  have hson : kv'.1 ∈ sonsOfMap φ kv.1 := by
    refine son_of_req φ n kv.1 kv'.1 hok.onMap hdm (fun req hreq hst => ?_)
    have h0 := reqOf_nonneg (φ := φ) hbd kv'.1 req hreq
    rw [← hreqs req hreq h0 (by rw [hcs, hst, hkey]; omega), hst, hkey, hsn]
  -- it survives the filter and climbs to `w`
  have hsF := ChainSound_filterAll kv.2 (reqOf φ kv'.1) sel hs hreqs
  have hvF : isValid (filterAll kv.2 (reqOf φ kv'.1)) = true := PickInduction.isValid_of_ChainG _ sel hsF.chain
  have c := filt_ctx φ hbd n kv hok (reqOf φ kv'.1) hvF
  have hFcs : (filterAll kv.2 (reqOf φ kv'.1)).current_step = (n : Int) + 1 := by
    rw [(pruned_filterAll kv.2 (reqOf φ kv'.1)).step_eq, hcs]
  have hdF : kv'.1.step = (filterAll kv.2 (reqOf φ kv'.1)).current_step := by
    rw [hFcs, mapNodes_step φ _ kv'.1 hdm]
  have hmok : MachineOk (filterAll kv.2 (reqOf φ kv'.1)) :=
    MachineOk_of_pruned (pruned_filterAll _ _) (Certifies.MachineOk_reachable (reqOf φ) (isProhibited φ) _
      (MapReachable.reachable_of_mapReachable φ hbd kv.2 hok.reach))
  have hpar : (sel n).parent_id = some y0.id := by
    have hl := hsF.chain.1.2 ((n : Int) - 1) (by omega) (by rw [hFcs]; omega)
    rw [show (n : Int) - 1 + 1 = n by omega] at hl
    obtain ⟨nsn, hnsn⟩ := Option.isSome_iff_exists.mp (hsF.chain.1.1 n (by omega) (by rw [hFcs]; omega)).1
    rw [hnsn] at hl
    have hpmp := c.rc.pmp nsn (List.mem_of_find?_eq_some hnsn) _ hl
    rw [node?_id_eq _ _ nsn hnsn, hsy] at hpmp
    exact hpmp.symm
  have hext : extendPid (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel = w := by
    unfold extendPid
    rw [if_pos (by rw [hFcs]; omega), show (filterAll kv.2 (reqOf φ kv'.1)).current_step - 1 = (n : Int) by
      rw [hFcs]; omega]
    exact ParentId.pathNodeId_ext (by rw [hwid]; rfl) (by rw [hwx, ← hsx]; rfl) (by rw [hwy, ← hpar]; rfl)
  have hf : isProhibited φ w = false := by
    obtain ⟨kv2, hkv2, hd2, hv2, n2, hn2⟩ := (PieceJoin.join_no_new φ n kv' hkv').1 w nw hnw
    obtain ⟨hok2, hdst2, hcs2, _, hvF2, _⟩ := src_ctx φ hbd n kv2 hkv2 kv'.1 hd2 hv2
    have c2 := filt_ctx φ hbd n kv2 hok2 (reqOf φ kv'.1) hvF2
    obtain ⟨hrow, _⟩ := upF_new φ kv2.2 kv'.1 hdst2 c2 hv2 w n2 hn2 (by rw [hcs2]; exact hws)
    exact not_forb_of_mem_newRowIds _ _ _ w hrow
  have hsA := ChainSound_addNode _ kv'.1 "" (isProhibited φ) hdF c.pc.below hmok sel hsF (by rw [hext]; exact hf)
  have hsP : ChainSound (upF φ kv.2 kv'.1) (extend (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 sel) := by
    show ChainSound (up (filterAll kv.2 (reqOf φ kv'.1)) kv'.1 "" (isProhibited φ)) _
    unfold up; rw [if_pos hvF]
    split
    · exact ChainSound_review _ _ hsA
    · exact hsA
  have hvP : isValid (upF φ kv.2 kv'.1) = true := PickInduction.isValid_of_ChainG _ _ hsP.chain
  -- the certificate in the piece, then in the joined state
  obtain ⟨h, hmem, hgr⟩ := PieceJoin.piece_grown φ n kv hkv kv'.1 hson hvP
  have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
  rw [← he]
  refine ⟨_, ChainSound_of_grown hgr _ hsP, fun q hq => ?_, fun m hm h0 h1 => ?_⟩
  · by_cases hqs : q.id.step ≤ (n : Int)
    · rw [extend_below _ _ _ _ (by rw [hFcs]; omega)]
      exact hon q (List.mem_filter.mpr ⟨hq, decide_eq_true hqs⟩)
    · have hqw := htop q hq (by omega)
      subst hqw
      rw [show q.id.step = (filterAll kv.2 (reqOf φ kv'.1)).current_step by rw [hFcs, hws], extend_top, hext]
  · have hcsh : h.current_step = (n : Int) + 2 := by
      have := congrArg (fun x => x.2.current_step) he; simp only at this; rw [this, hcs']
    rw [hcsh] at h1
    rcases Int.lt_or_le m.step ((n : Int) + 1) with hlt | hge
    · rw [extend_below _ _ _ _ (by rw [hFcs]; exact hlt)]
      exact hR m (List.mem_append_left _ (List.mem_append_left _
        (List.mem_filter.mpr ⟨hm, decide_eq_true (by omega)⟩))) h0 (by rw [hcs]; exact hlt)
    · have hmt : m.step = (n : Int) + 1 := by omega
      rw [hmt, ← hFcs, extend_top, hext, hwid]
      obtain ⟨r, nr, hnr, _, _, hrR⟩ := hW m.step h0 (by rw [hcs']; omega)
      obtain ⟨p, hp, hpm⟩ := hrR m hm
      rw [← hpm]
      exact (top_entry_key φ hbd (n + 1) kv' hkv' r nr hnr p hp (by rw [hpm, hmt]; push_cast; rfl)).symm

/-- info: 'AbsSatBin.GraphPath.Model.LineUnion.certR_top_of_GL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certR_top_of_GL

/-- **`MapCert` of the next line from `GL`**: under `GL` and `MapCert` on line `n`, every state of line `n+1` whose
key has no prohibited window has `MapCert` — with a member at the top by `certR_top_of_GL`, without one by
`certR_low_of_GL`. -/
theorem mapCert_next_of_GL (hn1 : 1 ≤ n) (hGL : GL φ n) (hM : ∀ kv ∈ line φ n, MapCert kv.2)
    (kv' : NodeId × GPathM) (hkv' : kv' ∈ line φ (n + 1))
    (hsafe : ∀ pid : PathNodeId, pid.id = kv'.1 → isProhibited φ pid = false) : MapCert kv'.2 := by
  intro Q R hQ hW
  have hok' : StateOk φ ((n + 1 : Nat) : Int) kv' := (lineOk φ (n + 1)).2 kv' hkv'
  have hcs' : kv'.2.current_step = (n : Int) + 2 := by rw [hok'.step]; push_cast; omega
  have cJ := KernelUp.aCtx_line φ hbd (n + 1) kv' hkv'
  cases e : Q.find? (fun q => decide ((n : Int) < q.id.step)) with
  | some w =>
    have hwQ := List.mem_of_find?_eq_some e
    have hwn := of_decide_eq_true (List.find?_some (p := fun q : PathNodeId => decide ((n : Int) < q.id.step)) e)
    obtain ⟨nw, hnw, _⟩ := hQ w hwQ
    have := (CertFix.step_range cJ.pc w nw hnw).2
    rw [hcs'] at this
    exact certR_top_of_GL φ n hbd hn1 hGL hM kv' hkv' Q R hQ hW w hwQ (by omega)
  | none =>
    refine certR_low_of_GL φ n hbd hGL hM kv' hkv' hsafe Q R hQ hW (fun q hq => ?_)
    have := List.find?_eq_none.mp e q hq
    simp only [decide_eq_true_eq] at this
    omega

/-- info: 'AbsSatBin.GraphPath.Model.LineUnion.mapCert_next_of_GL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapCert_next_of_GL

end AbsSatBin.GraphPath.Model.LineUnion
