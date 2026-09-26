-- lean/improves_bin/AbsSatBin/GraphPath/Model/MapCert.lean
import AbsSatBin.GraphPath.Model.CertRoute

/-!
# `MapCert`: certificates with map-level constraints — the certificate chooses the window

Three of the four unions of the machine are disjunctions over **path nodes of the same map nodes**: a
requirement names a map node that has one path node per value of the previous variable; a merge node's
parents share their map nodes and differ in the forgotten step. A clique of path nodes cannot express
"one of these"; a **map node** can.

* **`MapCert g`**: if `Q` is a clique and at every step some live node owns all of `Q` and, for each map
  node `m` of `R`, **some** path node of `m`, then a certificate goes through `Q` and through the map nodes
  of `R`. With `R = []` it is `CertClique` (`certClique_of_mapCert`).

Along the machine (demonstrated):
* **the review keeps it** (`mapCert_filterAll_nil`);
* **every requirement filter keeps it** (`mapCert_filter`), with any number of path nodes for the
  required map node: after the filter every node owns some path node of it, so the requirement is one
  more map-level constraint, and the certificate that honours it survives;
* **`addNode` keeps it, merges included** (`mapCert_addNode`): a clique with a new node `z = (d, a, b)`
  becomes the old clique with the map-level constraints `a` (one step below) and `b` (two below). A
  witness that owns `z` owns a parent `(a, b, ·)` and, by the pair rule, a path node of `b`. The
  certificate through `a` and `b` ends at **some** parent of `z` — whichever its own window gives — and
  extends through `z`.

So the requirement with two windows and the merge are no longer obligations. What is left is the
machine's join of states (not a union of pins of one state) and the skipped window (the clause).
-/

namespace AbsSatBin.GraphPath.Model.MapCert

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.CliqueTri
open AbsSatBin.GraphPath.Model.CertFix
open AbsSatBin.GraphPath.Model.CertDescent
open AbsSatBin.GraphPath.Model.CertInvariant
open AbsSatBin.GraphPath.Model.AmbTriCore (ACtx)
open AbsSatBin.GraphPath.Model.BranchRel (sh)

/-- At every step, a live node owns `Q` and some path node of each map node of `R`. -/
def WitR (g : GPathM) (Q : List PathNodeId) (R : List NodeId) : Prop :=
  ∀ l, 0 ≤ l → l < g.current_step → ∃ r nr, g.node? r = some nr ∧ r.id.step = l ∧ OwnsAll Q nr ∧
    ∀ m ∈ R, ∃ p ∈ nr.owners, p.id = m

/-- A certificate through `Q` and through the map nodes of `R`. -/
def CertR (g : GPathM) (Q : List PathNodeId) (R : List NodeId) : Prop :=
  ∃ sel, ChainSound g sel ∧ (∀ q ∈ Q, sel q.id.step = q) ∧
    ∀ m ∈ R, 0 ≤ m.step → m.step < g.current_step → (sel m.step).id = m

/-- **Certificates with map-level constraints.** -/
def MapCert (g : GPathM) : Prop := ∀ Q R, Clique g Q → WitR g Q R → CertR g Q R

theorem certClique_of_mapCert {g : GPathM} (h : MapCert g) : CertClique g := by
  intro Q hQ hW
  obtain ⟨sel, hs, hon, _⟩ := h Q [] hQ (fun l h0 h1 => by
    obtain ⟨r, nr, hnr, hrs, hrQ⟩ := hW l h0 h1
    exact ⟨r, nr, hnr, hrs, hrQ, fun _ h => absurd h List.not_mem_nil⟩)
  exact ⟨sel, hs, hon⟩

-- ============================================================
-- The review and the requirement filter
-- ============================================================

/-- **The review keeps `MapCert`.** -/
theorem mapCert_filterAll_nil (X : GPathM) (hnd : NodupIds X) (h : MapCert X) :
    MapCert (filterAll X []) := by
  have hb := KernelIff.below_filterAll_self X hnd []
  intro Q R hQ hW
  have hQX : Clique X Q := fun p hp => by
    obtain ⟨np, hnp, hpQ⟩ := hQ p hp
    obtain ⟨nx, hnx, ho, _, _⟩ := hb.node p np hnp
    exact ⟨nx, hnx, fun s hs => ho s (hpQ s hs)⟩
  have hWX : WitR X Q R := fun l h0 h1 => by
    obtain ⟨r, nr, hnr, hrs, hrQ, hrR⟩ := hW l h0 (by rw [← hb.step]; exact h1)
    obtain ⟨nx, hnx, ho, _, _⟩ := hb.node r nr hnr
    refine ⟨r, nx, hnx, hrs, fun s hs => ho s (hrQ s hs), fun m hm => ?_⟩
    obtain ⟨p, hp, hpm⟩ := hrR m hm
    exact ⟨p, ho p hp, hpm⟩
  obtain ⟨sel, hs, hon, hR⟩ := h Q R hQX hWX
  refine ⟨sel, ChainSound_filterAll X [] sel hs (fun _ h => absurd h List.not_mem_nil), hon,
    fun m hm h0 h1 => hR m hm h0 (by rw [hb.step]; exact h1)⟩

/-- **Every requirement filter keeps `MapCert`**, whatever the number of path nodes of the required map
node: the requirement becomes one more map-level constraint. -/
theorem mapCert_filter (g : GPathM) (req : NodeId) (hnd : NodupIds g) (hk : Kernel (filterAll g [req]))
    (h0 : 0 ≤ req.step) (h1 : req.step < g.current_step) (h : MapCert g) :
    MapCert (filterAll g [req]) := by
  have hb := KernelIff.below_filterAll_self g hnd [req]
  -- every node of the filtered state owns a path node of `req`
  have ownReq : ∀ q nq, (filterAll g [req]).node? q = some nq → ∃ p ∈ nq.owners, p.id = req := by
    intro q nq hq
    have hv := ((isValidNode_iff _ nq).mp (hk.valid q nq hq)).1
    rw [← hb.step] at hv
    obtain ⟨e, he, hes⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv req.step (mem_intRange h0 (by omega)))
    exact ⟨e, he, ReqFilter.req_id g req e (hk.own q nq hq e he) (eq_of_beq hes)⟩
  intro Q R hQ hW
  have hQg : Clique g Q := fun p hp => by
    obtain ⟨np, hnp, hpQ⟩ := hQ p hp
    obtain ⟨nx, hnx, ho, _, _⟩ := hb.node p np hnp
    exact ⟨nx, hnx, fun s hs => ho s (hpQ s hs)⟩
  have hWg : WitR g Q (req :: R) := fun l hl0 hl1 => by
    obtain ⟨r, nr, hnr, hrs, hrQ, hrR⟩ := hW l hl0 (by rw [← hb.step]; exact hl1)
    obtain ⟨nx, hnx, ho, _, _⟩ := hb.node r nr hnr
    refine ⟨r, nx, hnx, hrs, fun s hs => ho s (hrQ s hs), fun m hm => ?_⟩
    rcases List.mem_cons.mp hm with e | hm
    · obtain ⟨p, hp, hpm⟩ := ownReq r nr hnr
      exact ⟨p, ho p hp, by rw [e]; exact hpm⟩
    · obtain ⟨p, hp, hpm⟩ := hrR m hm
      exact ⟨p, ho p hp, hpm⟩
  obtain ⟨sel, hs, hon, hR⟩ := h Q (req :: R) hQg hWg
  refine ⟨sel, ChainSound_filterAll g [req] sel hs (fun r hr _ _ => ?_), hon,
    fun m hm hm0 hm1 => hR m (List.mem_cons_of_mem _ hm) hm0 (by rw [hb.step]; exact hm1)⟩
  rw [List.mem_singleton.mp hr]
  exact hR req List.mem_cons_self h0 h1

/-- **A union of complementary pins of a state with `MapCert` has `MapCert`**: the certificate chooses
its side at the pinned step. -/
theorem mapCert_join_pins (J : GPathM) (hnd : NodupIds J) (r₁ r₂ : NodeId) (t : Int)
    (hr₁ : r₁.step = t) (hr₂ : r₂.step = t)
    (htwo : ∀ q ∈ J.gowners, q.id.step = t → q.id = r₁ ∨ q.id = r₂)
    (hok : okJoin (filterAll J [r₁]) (filterAll J [r₂]) = true) (h : MapCert J) :
    MapCert (join (filterAll J [r₁]) (filterAll J [r₂])) := by
  have hcs : (join (filterAll J [r₁]) (filterAll J [r₂])).current_step = J.current_step := by
    show (filterAll J [r₁]).current_step = J.current_step
    exact (KernelIff.below_filterAll_self J hnd [r₁]).step.symm
  intro Q R hQ hW
  have hQJ : Clique J Q := by
    intro q hq
    obtain ⟨nq, hnq, hqQ⟩ := hQ q hq
    obtain ⟨nJ, hnJ, ho⟩ := CertRoute.join_sub J hnd r₁ r₂ q nq hnq
    exact ⟨nJ, hnJ, fun s hs => ho s (hqQ s hs)⟩
  have hWJ : WitR J Q R := by
    intro l h0 h1
    obtain ⟨r, nr, hnr, hrs, hrQ, hrR⟩ := hW l h0 (by rw [hcs]; exact h1)
    obtain ⟨nJ, hnJ, ho⟩ := CertRoute.join_sub J hnd r₁ r₂ r nr hnr
    refine ⟨r, nJ, hnJ, hrs, fun s hs => ho s (hrQ s hs), fun m hm => ?_⟩
    obtain ⟨p, hp, hpm⟩ := hrR m hm
    exact ⟨p, ho p hp, hpm⟩
  obtain ⟨sel, hs, hon, hR⟩ := h Q R hQJ hWJ
  have hR' : ∀ m ∈ R, 0 ≤ m.step → m.step < (join (filterAll J [r₁]) (filterAll J [r₂])).current_step →
      (sel m.step).id = m := fun m hm h0 h1 => hR m hm h0 (by rw [← hcs]; exact h1)
  by_cases ht : 0 ≤ t ∧ t < J.current_step
  · rcases htwo (sel t) (hs.chain.2.2 t ht.1 ht.2) (hs.chain.1.1 t ht.1 ht.2).2 with e | e
    · refine ⟨sel, ChainSound_join_left _ _ sel (ChainSound_filterAll J [r₁] sel hs (fun r hr _ _ => ?_)), hon, hR'⟩
      rw [List.mem_singleton.mp hr, hr₁, e]
    · refine ⟨sel, ChainSound_join_right _ _ hok sel (ChainSound_filterAll J [r₂] sel hs (fun r hr _ _ => ?_)), hon, hR'⟩
      rw [List.mem_singleton.mp hr, hr₂, e]
  · refine ⟨sel, ChainSound_join_left _ _ sel (ChainSound_filterAll J [r₁] sel hs (fun r hr h0 h1 => ?_)), hon, hR'⟩
    rw [List.mem_singleton.mp hr] at h0 h1
    exact absurd ⟨hr₁ ▸ h0, hr₁ ▸ h1⟩ ht

-- ============================================================
-- `addNode`, merges included
-- ============================================================

section
variable (g : GPathM) (d : NodeId) (title : String) (forb : PathNodeId → Bool)
  (c : ACtx g) (hd : d.step = g.current_step) (hs2 : 2 ≤ g.current_step)
  (hmok : MachineOk g) (hnf : ∀ pid ∈ shiftRowIds g d, forb pid = false) (h : MapCert g)
include c hd hs2 hmok hnf h

/-- **`addNode` keeps `MapCert`, merges included** (no window skipped). -/
theorem mapCert_addNode : MapCert (addNode g d title forb) := by
  have hk := c.pc.ker
  have hpos : 0 < g.current_step := by omega
  have hbelow := c.pc.below
  have hnd := c.pc.nd
  have hownb : SelfOwn.OwnBelow g := c.rc.ownb
  have hcs' : (addNode g d title forb).current_step = g.current_step + 1 := addNode_current g d title forb
  have back : ∀ q n, g.node? q = some n → ∀ v, v ∈ (upMap g d forb n).owners → v.id.step < g.current_step →
      v ∈ n.owners := by
    intro q n hn v hv hvs
    rw [upMap_owners] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hv
    · exfalso
      have := mapId_of_mem_newRowIds g d forb v (List.mem_filter.mp hv).1
      have : v.id.step = g.current_step := by rw [this]; exact hd
      omega
  -- an entry at the new step names `d`
  have topEntry : ∀ q nq, (addNode g d title forb).node? q = some nq → ∀ p ∈ nq.owners,
      p.id.step = g.current_step → p.id = d := by
    intro q nq hq p hp hps
    rcases BranchRel.node_cases g d title forb hd hbelow hnd q nq hq with ⟨n, hn, hEq, _⟩ | ⟨hqn, hEq, hqs⟩
    · rw [hEq, upMap_owners] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exfalso; have := hownb n (List.mem_of_find?_eq_some hn) p hp; omega
      · exact mapId_of_mem_newRowIds g d forb p (List.mem_filter.mp hp).1
    · rw [hEq, rowNode_owners] at hp
      rcases (mem_rowOwners_iff g d q p).mp hp with ⟨hu, _⟩ | he
      · exfalso
        obtain ⟨_, _, np', hnp', hpp'⟩ := KernelReader.mem_unionOwnersOf_inv g _ p hu
        have := hownb np' (List.mem_of_find?_eq_some hnp') p hpp'; omega
      · rw [he]; exact mapId_of_mem_newRowIds g d forb q hqn
  intro Q R hQ hW
  have topR : ∀ m ∈ R, m.step = g.current_step → m = d := by
    intro m hm hms
    obtain ⟨r, nr, hnr, _, _, hrR⟩ := hW 0 (Int.le_refl 0) (by rw [hcs']; omega)
    obtain ⟨p, hp, hpm⟩ := hrR m hm
    rw [← hpm]; exact topEntry r nr hnr p hp (by rw [hpm]; exact hms)
  -- the old part of the constraints and of the clique
  let Ro := R.filter (fun m => decide (m.step < g.current_step))
  let Qo := Q.filter (fun q => decide (q.id.step < g.current_step))
  have memRo : ∀ m, m ∈ Ro ↔ m ∈ R ∧ m.step < g.current_step := by
    intro m; rw [List.mem_filter]; exact ⟨fun ⟨a, b⟩ => ⟨a, of_decide_eq_true b⟩, fun ⟨a, b⟩ => ⟨a, decide_eq_true b⟩⟩
  have memQo : ∀ q, q ∈ Qo ↔ q ∈ Q ∧ q.id.step < g.current_step := by
    intro q; rw [List.mem_filter]; exact ⟨fun ⟨a, b⟩ => ⟨a, of_decide_eq_true b⟩, fun ⟨a, b⟩ => ⟨a, decide_eq_true b⟩⟩
  have hQo : Clique g Qo := by
    intro q hq
    obtain ⟨hqQ, hqs⟩ := (memQo q).mp hq
    obtain ⟨nq, hnq, hqQo⟩ := hQ q hqQ
    obtain ⟨n, hn, hEq⟩ := addNode_node?_below g d title forb hd q nq hnq hqs
    rw [hEq] at hqQo
    refine ⟨n, hn, fun s hs => ?_⟩
    obtain ⟨hsQ, hss⟩ := (memQo s).mp hs
    exact back q n hn s (hqQo s hsQ) hss
  -- witnesses below the new step, seen in `g`
  have witOld : ∀ l, 0 ≤ l → l < g.current_step → ∃ r nr n, (addNode g d title forb).node? r = some nr ∧
      g.node? r = some n ∧ nr = upMap g d forb n ∧ r.id.step = l ∧ OwnsAll Qo n ∧
      (∀ m ∈ Ro, ∃ p ∈ n.owners, p.id = m) ∧ OwnsAll Q nr := by
    intro l hl0 hl1
    obtain ⟨r, nr, hnr, hrs, hrQ, hrR⟩ := hW l hl0 (by rw [hcs']; omega)
    obtain ⟨n, hn, hEq⟩ := addNode_node?_below g d title forb hd r nr hnr (by rw [hrs]; exact hl1)
    refine ⟨r, nr, n, hnr, hn, hEq, hrs, fun s hs => ?_, fun m hm => ?_, hrQ⟩
    · obtain ⟨hsQ, hss⟩ := (memQo s).mp hs
      rw [hEq] at hrQ; exact back r n hn s (hrQ s hsQ) hss
    · obtain ⟨hmR, hms⟩ := (memRo m).mp hm
      obtain ⟨p, hp, hpm⟩ := hrR m hmR
      rw [hEq] at hp
      exact ⟨p, back r n hn p hp (by rw [hpm]; exact hms), hpm⟩
  -- finishing: the extension of a certificate through `Qo` and `Ro` covers `Q` and `R`
  have finish : ∀ sel, ChainSound g sel → (∀ q ∈ Qo, sel q.id.step = q) →
      (∀ m ∈ Ro, 0 ≤ m.step → m.step < g.current_step → (sel m.step).id = m) →
      forb (extendPid g d sel) = false → (∀ q ∈ Q, q.id.step = g.current_step → q = extendPid g d sel) →
      CertR (addNode g d title forb) Q R := by
    intro sel hs hon hR hf htop
    refine ⟨extend g d sel, ChainSound_addNode g d title forb hd hbelow hmok sel hs hf, fun q hq => ?_,
      fun m hm hm0 hm1 => ?_⟩
    · rcases Int.lt_or_le q.id.step g.current_step with hqs | hqs
      · rw [extend_below g d sel q.id.step hqs]; exact hon q ((memQo q).mpr ⟨hq, hqs⟩)
      · have hqs' : q.id.step = g.current_step := by
          obtain ⟨nq, hnq, _⟩ := hQ q hq
          rcases BranchRel.node_cases g d title forb hd hbelow hnd q nq hnq with ⟨_, _, _, hs'⟩ | ⟨_, _, hs'⟩
          · omega
          · exact hs'
        rw [hqs', extend_top]; exact (htop q hq hqs').symm
    · rw [hcs'] at hm1
      rcases Int.lt_or_le m.step g.current_step with hms | hms
      · rw [extend_below g d sel m.step hms]; exact hR m ((memRo m).mpr ⟨hm, hms⟩) hm0 hms
      · have hms' : m.step = g.current_step := by omega
        rw [hms', extend_top, extendPid_mapId, topR m hm hms']
  cases hz : Q.any (fun q => q.id.step == g.current_step) with
  | false =>
    -- only old nodes: the certificate extends by its own last node
    have hWo : WitR g Qo Ro := by
      intro l hl0 hl1
      obtain ⟨r, _, n, _, hn, _, hrs, hrQ, hrR, _⟩ := witOld l hl0 hl1
      exact ⟨r, n, hn, hrs, hrQ, hrR⟩
    obtain ⟨sel, hs, hon, hR⟩ := h Qo Ro hQo hWo
    refine finish sel hs hon hR (hnf _ (extendPid_mem_shiftRowIds g d sel hs.chain.1)) (fun q hq hqs => ?_)
    exfalso
    exact (List.any_eq_false.mp hz q hq) (beq_iff_eq.mpr hqs)
  | true =>
    obtain ⟨z, hzQ, hzs'⟩ := List.any_eq_true.mp hz
    have hzs : z.id.step = g.current_step := eq_of_beq hzs'
    obtain ⟨nz, hnz, hzQo⟩ := hQ z hzQ
    have hznew : z ∈ newRowIds g d forb ∧ nz = rowNode g d title z := by
      rcases BranchRel.node_cases g d title forb hd hbelow hnd z nz hnz with ⟨_, _, _, hs'⟩ | ⟨hn, hEq, _⟩
      · omega
      · exact ⟨hn, hEq⟩
    -- the window of `z`: its parents share `(a, b)`
    have hp0 := BranchRel.sh_new g d forb hpos z hznew.1 hzs
    let p0 := sh g d z
    obtain ⟨np0, hnp0⟩ := Option.isSome_iff_exists.mp (rowParent_node g d hpos hp0).1
    have hp0s : p0.id.step = g.current_step - 1 := (rowParent_node g d hpos hp0).2
    have hz0 : shiftPid p0 d = z := eq_of_beq (List.mem_filter.mp hp0).2
    have hnp0m := List.mem_of_find?_eq_some hnp0
    have hnp0id : np0.id = p0 := node?_id_eq g p0 np0 hnp0
    -- a parent of `p0`, whose map node is `b`
    obtain ⟨pp, hpp⟩ : ∃ pp, pp ∈ np0.parents := by
      have hnr : np0.id.parent_id ≠ none := c.rc.shape.notroot np0 hnp0m (by rw [hnp0id, hp0s]; omega)
      rcases ((isValidNode_iff g np0).mp (hk.valid p0 np0 hnp0)).2.1 with h' | h'
      · exact absurd (Option.isNone_iff_eq_none.mp h') hnr
      · exact List.exists_mem_of_ne_nil _ h'
    have hppid : some pp.id = p0.parent_id := by
      have := c.rc.pmp np0 hnp0m pp hpp; rw [hnp0id] at this; exact this
    have hpps : pp.id.step = g.current_step - 2 := by
      have := c.pc.pb np0 hnp0m pp hpp; rw [hnp0id, hp0s] at this; rw [this]; omega
    let a := p0.id
    let b := pp.id
    -- every parent of `z` has map node `a` and parent map node `b`
    have parWin : ∀ p ∈ rowParents g d z, p.id = a ∧ p.parent_id = some b := by
      intro p hp
      have hzp : shiftPid p d = z := eq_of_beq (List.mem_filter.mp hp).2
      rw [← hz0] at hzp
      have e1 := congrArg PathNodeId.parent_id hzp
      have e2 := congrArg PathNodeId.gparent_id hzp
      simp only [shiftPid, Option.some.injEq] at e1 e2
      exact ⟨e1, by rw [e2, ← hppid]⟩
    -- a node that owns `z` owns a path node of `a` and one of `b`
    have ownsAB : ∀ r n, g.node? r = some n → z ∈ (upMap g d forb n).owners →
        (∃ p ∈ n.owners, p.id = a) ∧ (∃ e ∈ n.owners, e.id = b) := by
      intro r n hn hzr
      rw [upMap_owners] at hzr
      rcases List.mem_append.mp hzr with hzr | hzr
      · exfalso; have := hownb n (List.mem_of_find?_eq_some hn) z hzr; omega
      · have hc := List.mem_of_elem_eq_true (List.mem_filter.mp hzr).2
        rw [node?_id_eq g r n hn] at hc
        rcases (mem_rowOwners_iff g d z r).mp hc with ⟨hu, _⟩ | he
        · obtain ⟨p, hp, np, hnp, hrp⟩ := KernelReader.mem_unionOwnersOf_inv g _ r hu
          obtain ⟨hpa, hpb⟩ := parWin p hp
          have hpr : p ∈ n.owners := hk.sym p np r n hnp hn hrp
          refine ⟨⟨p, hpr, hpa⟩, ?_⟩
          have hps : p.id.step = g.current_step - 1 := (rowParent_node g d hpos hp).2
          obtain ⟨e, he, hep, hes⟩ := hk.pair r n p np hn hnp hpr (g.current_step - 2) (by omega) (by omega)
          obtain ⟨hepar, _⟩ := parent_of_owner c.pc p np hnp (by omega) e hep (by rw [hes, hps]; omega)
          have hpm := c.rc.pmp np (List.mem_of_find?_eq_some hnp) e hepar
          rw [node?_id_eq g p np hnp, hpb] at hpm
          exact ⟨e, he, Option.some.inj hpm⟩
        · exfalso
          have : r.id.step < g.current_step := by
            have := hbelow n (List.mem_of_find?_eq_some hn); rw [node?_id_eq g r n hn] at this; exact this
          rw [he] at this; omega
    have hWo : WitR g Qo (Ro ++ [a, b]) := by
      intro l hl0 hl1
      obtain ⟨r, nr, n, _, hn, hEq, hrs, hrQ, hrR, hrQ'⟩ := witOld l hl0 hl1
      have hzr : z ∈ (upMap g d forb n).owners := by rw [← hEq]; exact hrQ' z hzQ
      obtain ⟨⟨pa, hpa, hpaid⟩, ⟨eb, heb, hebid⟩⟩ := ownsAB r n hn hzr
      refine ⟨r, n, hn, hrs, hrQ, fun m hm => ?_⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact hrR m hm
      · rcases List.mem_cons.mp hm with e | hm
        · exact ⟨pa, hpa, by rw [e]; exact hpaid⟩
        · rw [List.mem_singleton.mp hm]; exact ⟨eb, heb, hebid⟩
    obtain ⟨sel, hs, hon, hR⟩ := h Qo (Ro ++ [a, b]) hQo hWo
    -- the certificate ends at a parent of `z`
    have hsa : (sel (g.current_step - 1)).id = a := by
      have := hR a (List.mem_append_right _ List.mem_cons_self) (by show 0 ≤ p0.id.step; omega)
        (by show p0.id.step < g.current_step; omega)
      rw [show a.step = g.current_step - 1 from hp0s] at this; exact this
    have hsb : (sel (g.current_step - 2)).id = b := by
      have := hR b (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (by show 0 ≤ pp.id.step; omega) (by show pp.id.step < g.current_step; omega)
      rw [show b.step = g.current_step - 2 from hpps] at this; exact this
    have hsp : (sel (g.current_step - 1)).parent_id = some b := by
      have hlink := hs.chain.1.2 (g.current_step - 2) (by omega) (by omega)
      rw [show g.current_step - 2 + 1 = g.current_step - 1 from by omega] at hlink
      obtain ⟨nl, hnl⟩ := Option.isSome_iff_exists.mp (hs.chain.1.1 (g.current_step - 1) (by omega) (by omega)).1
      rw [hnl] at hlink
      have := c.rc.pmp nl (List.mem_of_find?_eq_some hnl) _ hlink
      rw [node?_id_eq g _ nl hnl, hsb] at this; exact this.symm
    have hext : extendPid g d sel = z := by
      unfold extendPid; rw [if_pos hpos, ← hz0]
      unfold shiftPid
      rw [hsa, hsp, ← hppid]
    refine finish sel hs (fun q hq => hon q hq) (fun m hm => hR m (List.mem_append_left _ hm))
      (by rw [hext]; exact not_forb_of_mem_newRowIds g d forb z hznew.1) (fun q hq hqs => ?_)
    rw [hext]
    -- a member at the new step is `z`
    have hqz := hzQo q hq
    rw [hznew.2, rowNode_owners] at hqz
    rcases (mem_rowOwners_iff g d z q).mp hqz with ⟨hu, _⟩ | he
    · exfalso
      obtain ⟨_, _, np', hnp', hqp'⟩ := KernelReader.mem_unionOwnersOf_inv g _ q hu
      have := hownb np' (List.mem_of_find?_eq_some hnp') q hqp'; omega
    · exact he
end

/-- info: 'AbsSatBin.GraphPath.Model.MapCert.mapCert_filter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapCert_filter

/-- info: 'AbsSatBin.GraphPath.Model.MapCert.mapCert_addNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapCert_addNode

end AbsSatBin.GraphPath.Model.MapCert
