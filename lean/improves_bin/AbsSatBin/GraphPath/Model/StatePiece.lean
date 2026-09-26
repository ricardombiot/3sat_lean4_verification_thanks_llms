-- lean/improves_bin/AbsSatBin/GraphPath/Model/StatePiece.lean
import AbsSatBin.GraphPath.Model.PieceJoin

/-!
# One piece keeps `MapCert`, the skipped window included

A piece is `upF X d = up (filterAll X (reqOf d)) d`. Inside one piece every step is already proved except
the skipped window, and that one is the clause **inside a single piece**, where the literal is uniform:

* the requirement filter keeps `MapCert` (`MapCert.mapCert_filter`, `mapCert_filterAll_nil`);
* `addNode` without a skipped window keeps it (`MapCert.mapCert_addNode`);
* **with a skipped window** (`mapCert_skip`): the window `000` is skipped only at key `L3 = 0` from the state
  with `L2 = 0`. Every node of the reviewed piece owns a node of the new step, whose window is allowed, so
  (with `L2 = 0` fixed by the source) it goes through `L1 = 1`: **every node of the piece owns `L1 = 1`**.
  A certificate through `L1 = 1` extends by an allowed window (`MapCert.certR_addNode_sub`), and the review
  keeps it.

`mapCert_piece`: from `MapCert` of a state of line `n ≥ 1`, `MapCert` of each of its pieces.
-/

namespace AbsSatBin.GraphPath.Model.StatePiece

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.MapReachable
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.MapCert (MapCert WitR CertR)

variable (φ : Cnf) (hbd : Bounded φ) (n : Nat)
include hbd

/-- **A piece with a skipped window keeps `MapCert`.** -/
theorem mapCert_skip (hn1 : 1 ≤ n) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true)
    (hF : MapCert (filterAll kv.2 (reqOf φ d)))
    (hsk : skipsWindow (filterAll kv.2 (reqOf φ d)) d (isProhibited φ) = true) :
    MapCert (upF φ kv.2 d) := by
  obtain ⟨hok, hdst, hcs, hdm, hvF, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ d) hvF
  have hk := c.pc.ker
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ d)
  have hFcs : (filterAll kv.2 (reqOf φ d)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  have hdF : d.step = (filterAll kv.2 (reqOf φ d)).current_step := by rw [hFcs, ← hcs, hdst]
  have hmokX : MachineOk kv.2 := ⟨by rw [hok.step]; omega, fun h => by rw [hok.step] at h; omega,
    fun _ => by rw [hok.par]; simp⟩
  have hmok : MachineOk (filterAll kv.2 (reqOf φ d)) := MachineOk_of_pruned (pruned_filterAll _ _) hmokX
  have hmapF : NodesOnMap φ (filterAll kv.2 (reqOf φ d)) :=
    NodesOnMap_of_pruned φ (pruned_filterAll _ _) (nodesOnMap_of_mapReachable φ kv.2 hok.reach)
  -- a node of the filtered source at step `n` names the key
  have keyOf : ∀ p np, (filterAll kv.2 (reqOf φ d)).node? p = some np → p.id.step = (n : Int) → p.id = kv.1 := by
    intro p np hnp hps
    obtain ⟨nJ, hnJ, hoJ, _, _⟩ := hb.node p np hnp
    exact top_entry_key φ hbd n kv hkv p nJ hnJ p (hoJ p (TriPinCut.self_own_pc c.pc p np hnp)) hps
  -- what the skip says: key `L3 = 0` at a third literal, from the state with `L2 = 0`
  obtain ⟨pid, hpid, hforb⟩ := List.any_eq_true.mp hsk
  have hpos : 0 < (filterAll kv.2 (reqOf φ d)).current_step := by omega
  obtain ⟨p, hp, hpp⟩ : ∃ p ∈ newParents (filterAll kv.2 (reqOf φ d)), shiftPid p d = pid := by
    unfold shiftRowIds at hpid; rw [if_pos hpos] at hpid
    exact List.mem_map.mp ((mem_dedupPids _ _).mp hpid)
  have hpl : p ∈ ((filterAll kv.2 (reqOf φ d)).line ((filterAll kv.2 (reqOf φ d)).current_step - 1)).map (·.id) := by
    unfold newParents at hp; rw [if_pos hpos] at hp; exact hp
  have hps : p.id.step = (n : Int) := by rw [Parents.mem_line_step _ _ p hpl, hFcs]; omega
  obtain ⟨np0, hnp0m, hnp0id⟩ := Parents.mem_nodes_of_mem_line _ _ p hpl
  have hnp0 : (filterAll kv.2 (reqOf φ d)).node? p = some np0 := by
    rw [← hnp0id]; exact node?_of_mem c.pc.nd np0 hnp0m
  have hpkey := keyOf p np0 hnp0 hps
  rw [← hpp] at hforb
  have hds : d.step = (n : Int) + 1 := by rw [hdF, hFcs]
  have hforb' := hforb
  unfold isProhibited shiftPid at hforb'
  simp only [Bool.and_eq_true, beq_iff_eq] at hforb'
  obtain ⟨⟨⟨hL3, hd0⟩, hpar0⟩, _⟩ := hforb'
  rw [hds] at hL3
  have hkey0 : kv.1 = ⟨(n : Int), 0⟩ := by
    rw [← hpkey, Option.some.inj hpar0, hds]; congr 1; omega
  have hdid : d = ⟨(n : Int) + 1, 0⟩ := by
    have e : d = ⟨d.step, d.index⟩ := rfl
    rw [e, hds, hd0]
  obtain ⟨_, hmid, htop⟩ := ClauseKey.l3_facts φ n hL3
  have hm0 : (0 : Int) < midFusion φ := by simp only [midFusion]; omega
  -- the reviewed piece
  have hG : upF φ kv.2 d = filterAll (addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ)) [] := by
    show up (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ) = _
    unfold up; rw [if_pos hvF, if_pos hsk]; rfl
  have hndG := Reader.nodup_addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ) c.pc.nd c.pc.below hdF
  have hbG := KernelIff.below_filterAll_self (addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ)) hndG []
  have hvP : isValid (review (addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ))) = true := by
    have := hv; rw [hG] at this; exact this
  have hcsP : (filterAll (addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ)) []).current_step =
      (n : Int) + 2 := by
    rw [← hbG.step, addNode_current, hFcs]; omega
  -- every node of the piece owns `L1 = 1` in the source
  have hEown : ∀ r ns, (filterAll (addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ)) []).node? r = some ns →
      r.id.step < (filterAll kv.2 (reqOf φ d)).current_step → ∀ nF, (filterAll kv.2 (reqOf φ d)).node? r = some nF →
      ∀ m ∈ [(⟨(n : Int) - 1, 1⟩ : NodeId)], ∃ e ∈ nF.owners, e.id = m := by
    intro r ns hns hrs nF hnF m hm
    rw [List.mem_singleton.mp hm]
    -- an entry at the new step
    have hval := ((isValidNode_iff _ ns).mp (review_node_valid _ hvP r ns hns)).1
    have hcsP' : (review (addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ))).current_step = (n : Int) + 2 :=
      hcsP
    rw [hcsP'] at hval
    obtain ⟨z, hz, hzs'⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp hval ((n : Int) + 1) (mem_intRange (by omega) (by omega)))
    have hzs : z.id.step = (n : Int) + 1 := eq_of_beq hzs'
    obtain ⟨nG, hnG, hoG, _, _⟩ := hbG.node r ns hns
    obtain ⟨nF', hnF', hEq⟩ := addNode_node?_below _ d "" (isProhibited φ) hdF r nG hnG hrs
    rw [hnF] at hnF'; cases hnF'
    have hzG := hoG z hz
    rw [hEq, upMap_owners] at hzG
    rcases List.mem_append.mp hzG with hzF | hzn
    · exfalso; have := c.rc.ownb nF (List.mem_of_find?_eq_some hnF) z hzF
      omega
    · obtain ⟨hznew, hzc⟩ := List.mem_filter.mp hzn
      have hrz : r ∈ rowOwners (filterAll kv.2 (reqOf φ d)) d z := by
        have := List.mem_of_elem_eq_true hzc; rw [node?_id_eq _ r nF hnF] at this; exact this
      obtain ⟨⟨pz, _, hpz⟩, ⟨e, he, hez⟩⟩ :=
        row_owner_window φ c d hdF (by omega) z hznew r nF hnF hrs hrz
      -- the window of `z`: `(d, L2 = 0, e)`
      obtain ⟨p1, hp1⟩ := exists_rowParent _ d _ hpos hznew
      obtain ⟨hp1s1, hp1s⟩ := rowParent_node _ d hpos hp1
      obtain ⟨np1, hnp1⟩ := Option.isSome_iff_exists.mp hp1s1
      have hzp1 : shiftPid p1 d = z := eq_of_beq (List.mem_filter.mp hp1).2
      have hp1key := keyOf p1 np1 hnp1 (by rw [hp1s, hFcs]; omega)
      have hzid : z.id = d := by rw [← hzp1]; rfl
      have hzpar : z.parent_id = some ⟨(n : Int), 0⟩ := by rw [← hzp1, ← hkey0, ← hp1key]; rfl
      -- `e` is a node of the source at step `n - 1`
      obtain ⟨ne, hne⟩ := hk.isNode_owner r nF hnF e he
      have hzgp : z.gparent_id = p1.parent_id := by rw [← hzp1]; rfl
      obtain ⟨pp, hpp⟩ : ∃ pp, pp ∈ np1.parents := by
        have hnp1m := List.mem_of_find?_eq_some hnp1
        have hnp1id : np1.id = p1 := node?_id_eq _ p1 np1 hnp1
        have hnr : np1.id.parent_id ≠ none :=
          c.rc.shape.notroot np1 hnp1m (by rw [hnp1id, hp1s, hFcs]; omega)
        rcases ((isValidNode_iff _ np1).mp (hk.valid p1 np1 hnp1)).2.1 with h' | h'
        · exact absurd (Option.isNone_iff_eq_none.mp h') hnr
        · exact List.exists_mem_of_ne_nil _ h'
      have hppid : some pp.id = p1.parent_id := by
        have := c.rc.pmp np1 (List.mem_of_find?_eq_some hnp1) pp hpp
        rw [node?_id_eq _ p1 np1 hnp1] at this; exact this
      have hpps : pp.id.step = (n : Int) - 1 := by
        have := c.pc.pb np1 (List.mem_of_find?_eq_some hnp1) pp hpp
        rw [node?_id_eq _ p1 np1 hnp1, hp1s, hFcs] at this; rw [this]; omega
      have heid : e.id = pp.id := by
        rw [hzgp, ← hppid] at hez; exact Option.some.inj hez
      have hemap := hmapF ne (List.mem_of_find?_eq_some hne)
      rw [node?_id_eq _ e ne hne, heid, hpps, mapNodes_two φ _ (by omega) (by omega) (by omega)] at hemap
      refine ⟨e, he, ?_⟩
      rw [heid]
      rcases List.mem_cons.mp hemap with e0 | e1
      · -- `z` would be the window `000`
        exfalso
        have hnf := not_forb_of_mem_newRowIds _ _ _ z hznew
        have hzf : isProhibited φ z = true := by
          unfold isProhibited
          rw [hzid, hzpar, hzgp, ← hppid, e0, hdid, show (n : Int) + 1 - 1 = n by omega,
            show (n : Int) + 1 - 2 = n - 1 by omega]
          simp only [Bool.and_eq_true]
          exact ⟨⟨⟨hL3, beq_iff_eq.mpr rfl⟩, beq_iff_eq.mpr rfl⟩, beq_iff_eq.mpr rfl⟩
        rw [hnf] at hzf; cases hzf
      · exact List.mem_singleton.mp e1
  -- a certificate through `L1 = 1` extends by an allowed window
  have hnf' : ∀ sel, ChainSound (filterAll kv.2 (reqOf φ d)) sel →
      (∀ m ∈ [(⟨(n : Int) - 1, 1⟩ : NodeId)], 0 ≤ m.step → (sel m.step).id = m) →
      isProhibited φ (extendPid (filterAll kv.2 (reqOf φ d)) d sel) = false := by
    intro sel hs hsel
    have h1 := hsel _ List.mem_cons_self (by simp only; omega)
    simp only at h1
    have hlink := hs.chain.1.2 ((n : Int) - 1) (by omega) (by rw [hFcs]; omega)
    rw [show (n : Int) - 1 + 1 = n by omega] at hlink
    obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp (hs.chain.1.1 n (by omega) (by rw [hFcs]; omega)).1
    rw [hnl] at hlink
    have hpm := c.rc.pmp nl (List.mem_of_find?_eq_some hnl) _ hlink
    rw [node?_id_eq _ _ nl hnl, h1] at hpm
    unfold extendPid; rw [if_pos hpos, hFcs, show (n : Int) + 1 - 1 = n by omega]
    unfold isProhibited shiftPid
    rw [← hpm, hdid]
    simp only [Bool.and_eq_false_iff]
    right
    show (some (⟨(n : Int) - 1, 1⟩ : NodeId) == some ⟨(n : Int) + 1 - 2, 0⟩) = false
    rw [show (n : Int) + 1 - 2 = n - 1 by omega]
    exact beq_eq_false_iff_ne.mpr (by intro h; cases h)
  -- conclusion
  rw [hG]
  intro Q R hQ hW
  obtain ⟨sel, hs, hon, hR⟩ := MapCert.certR_addNode_sub (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ) c hdF
    (by omega) hmok hF (filterAll (addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ)) [])
    (fun p ns hns => by obtain ⟨nx, hnx, ho, _, _⟩ := hbG.node p ns hns; exact ⟨nx, hnx, ho⟩)
    hbG.step.symm [⟨(n : Int) - 1, 1⟩] (fun m hm => by rw [List.mem_singleton.mp hm, hFcs]; simp only; omega)
    hEown hnf' Q R hQ hW
  refine ⟨sel, ChainSound_filterAll _ [] sel hs (fun _ h => absurd h List.not_mem_nil), hon,
    fun m hm h0 h1 => hR m hm h0 (by rw [hbG.step]; exact h1)⟩

/-- **One piece keeps `MapCert`** (line `n ≥ 1`). -/
theorem mapCert_piece (hn1 : 1 ≤ n) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true) (hX : MapCert kv.2) :
    MapCert (upF φ kv.2 d) := by
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd n kv hkv d hd hv
  have c := filt_ctx φ hbd n kv hok (reqOf φ d) hvF
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ d)
  have hFcs : (filterAll kv.2 (reqOf φ d)).current_step = (n : Int) + 1 := by rw [← hb.step, hcs]
  have hdF : d.step = (filterAll kv.2 (reqOf φ d)).current_step := by rw [hFcs, ← hcs, hdst]
  -- the requirement filter
  have hF : MapCert (filterAll kv.2 (reqOf φ d)) := by
    have hlen := reqOf_length_le_one φ d
    have hk := c.pc.ker
    cases hr : reqOf φ d with
    | nil => exact MapCert.mapCert_filterAll_nil kv.2 hnd hX
    | cons req rest =>
      cases rest with
      | cons _ _ => rw [hr] at hlen; simp at hlen
      | nil =>
        rw [hr] at hk
        have hreq : req ∈ reqOf φ d := by rw [hr]; exact List.mem_cons_self
        exact MapCert.mapCert_filter kv.2 req hnd hk (reqOf_nonneg φ hbd d req hreq)
          (by have := reqOf_backward φ hbd d req hreq; rw [hcs]; omega) hX
  by_cases hsk : skipsWindow (filterAll kv.2 (reqOf φ d)) d (isProhibited φ) = true
  · exact mapCert_skip φ hbd n hn1 kv hkv d hd hv hF hsk
  · have hup : upF φ kv.2 d = addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ) := by
      show up (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ) = _
      unfold up; rw [if_pos hvF, if_neg hsk]
    have hmokX : MachineOk kv.2 := ⟨by rw [hok.step]; omega, fun h => by rw [hok.step] at h; omega,
      fun _ => by rw [hok.par]; simp⟩
    rw [hup]
    refine MapCert.mapCert_addNode _ d "" (isProhibited φ) c hdF
      (MachineOk_of_pruned (pruned_filterAll _ _) hmokX) hF (by omega) (fun pid hpid => ?_)
    cases hf : isProhibited φ pid with
    | false => rfl
    | true => exact absurd (List.any_eq_true.mpr ⟨pid, hpid, hf⟩) hsk

/-- info: 'AbsSatBin.GraphPath.Model.StatePiece.mapCert_piece' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapCert_piece

end AbsSatBin.GraphPath.Model.StatePiece
