-- lean_project/AbsSat/GraphPath/Model/DescentRun.lean
import AbsSat.GraphPath.Model.DescentUp
import AbsSat.GraphPath.Model.DescentJoin
import AbsSat.GraphPath.Model.DescentFilter
import AbsSat.GraphPath.Model.BranchLines
import AbsSat.GraphPath.Model.NoDeadEndVerdict
import AbsSat.GraphPath.Model.PinHistory
import AbsSat.GraphPath.Model.SubsetSemantics
import AbsSat.GraphPath.Model.PairChain

/-!
# The descent, assembled over the run

`DescentUp`, `DescentJoin` and `DescentFilter` each do one case of the induction over how the
machine builds a state, and every one of them is proved. **Nobody composed them.** This module
does, and the result is the verdict with exactly two named hypotheses.

The composition follows the send, `upFilteringWeak g ws reqs d = up (filterAllAgg (filterWeakAll g ws) reqs) d`,
in the order the driver applies it:

* `filterWeakAll` touches **only `gowners`**, and it is absorbed: the filter case is stated for
  `filterAllAgg g reqs` for *any* `g`, so it is applied to the weakly filtered state directly.
* `filterAllAgg` — `DescentFilter.noDeadEnd_filterAllAgg_of_completion`, under `ReqCompletion`.
* `up` — `DescentUp.noDeadEnd_addNode`, with no hypothesis beyond the reader's invariants, which
  `MInv` supplies.
* `insertPure` — a send either lands on a free key, or joins what is already there, and that is
  `DescentJoin.noDeadEnd_join` under `JoinCoveredF`.

So `noDeadEnd_line` carries the descent across one advance, `noDeadEnd_run` across the whole run,
and `sat_of_descentRun` reads the verdict off it.

**What the two hypotheses are.** `ReqCompletion g reqs` — every partial chain of the filtered state
completes, inside `g`, to a full chain meeting the pins. `JoinCoveredF g₁ g₂` — a partial chain of a
join is a partial chain of one side, or extends outright. Both are measured; neither is proved.

## Two things the assembly made visible

**The descent does not propagate along the run.** `noDeadEnd_advance` never reads the previous
line: `advance_inv` starts the new line from `[]`, and each sent state gets its descent from its
**own** filter, not from the state it came from. So the induction over the run is an induction in
name only — the real content is per-send.

**And the verdict needs only the completion.** A reader's state is read after one more
`filterAllAgg`, so `DescentFilter.noDeadEnd_filterAllAgg_of_completion` applies to it directly:
`sat_of_reqCompletion` takes `ReqAll` and **not** `JoinAll`. The join and the `up` are what one
would need to *prove* the completion by induction, not to use it. That is the sharpest statement
of where the whole route now stands.
-/

namespace AbsSat.GraphPath.Model.DescentRun

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfSel (mapSons)
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.PureDriverImproves
open AbsSat.GraphPath.Model.PureDriver (PureLine pureInit insertPure)
open AbsSat.GraphPath.Model.BranchLines (insert_src sendToW_eq advance_inv sent)
open AbsSat.GraphPath.Model.NoDeadEnd (NoDeadEnd SoundFrom upd)
open AbsSat.GraphPath.Model.ReaderAggRun (MInv LineInv LineInv_init LineInv_steps)
open AbsSat.GraphPath.Model.ConservationFilter (StateOkF)

variable (φ : Cnf)

/-- **The two obligations, named once.**

`ReqAll` is `DescentFilter.ReqCompletion` at every state the driver filters, and `JoinAll` is
`DescentJoin.JoinCoveredF` at every pair it joins. Stating them over all arguments keeps the
assembly free of bookkeeping; sharpening them to the states the run actually reaches is a
separate (and easier) exercise. -/
def ReqAll : Prop :=
  ∀ (g : GPathM) (reqs : List NodeId), DescentFilter.ReqCompletion g reqs

def JoinAll : Prop :=
  ∀ g₁ g₂ : GPathM, DescentJoin.JoinCoveredF g₁ g₂

-- ============================================================
-- `ReqCompletion` is the goal restated
-- ============================================================

/-- **The converse of `DescentFilter.noDeadEnd_filterAllAgg_of_completion`.**

Descend *inside* the filtered state instead of inside `g`: the chain that comes out is a chain of
`g` (`ChainSound_of_pruned`), and it meets every pin **for free**, because in the filtered state
every node of a pinned step already carries the pinned map node (`PairChain.node_id_of_pin`).

Together with the forward direction this says `ReqCompletion g reqs` and
`NoDeadEnd (filterAllAgg g reqs)` are **the same statement**. So the filter case of the descent
induction is not a reduction: it is the goal, rewritten as a completion inside the unfiltered
state. That is worth knowing before spending effort on it. -/
theorem reqCompletion_of_noDeadEnd (g : GPathM) (reqs : List NodeId)
    (hnd : NodupIds g) (hsmp : Sons.SMP g) (hpos : 0 < g.current_step)
    (ctx : Pinned.Ctx (filterAllAgg g reqs))
    (hbelow : ∀ n ∈ (filterAllAgg g reqs).nodes,
      n.id.id.step < (filterAllAgg g reqs).current_step)
    (hndF : NodupIds (filterAllAgg g reqs))
    (h : NoDeadEnd (filterAllAgg g reqs)) : DescentFilter.ReqCompletion g reqs := by
  intro sel lo hlo0 hlo hs
  have hstep : (filterAllAgg g reqs).current_step = g.current_step :=
    (pruned_filterAllAgg g reqs).step_eq
  obtain ⟨sel', hagree, hs'⟩ :=
    NoDeadEnd.descend _ h lo.toNat sel lo (Nat.le_refl _) (by omega) hlo hs
  have hcsF : ChainSound (filterAllAgg g reqs) sel' :=
    (NoDeadEnd.chainSound_iff_soundFrom_zero _ sel' (by rw [hstep]; exact hpos)).mpr hs'
  refine ⟨sel', SubsetSemantics.ChainSound_of_pruned (pruned_filterAllAgg g reqs) hnd hsmp sel' hcsF,
    fun k hk _ => hagree k hk, ?_⟩
  intro req hreq h0 h1
  obtain ⟨hsome, hstepk⟩ := hs'.node req.step h0 (by rw [hstep]; exact h1)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hnid : n.id = sel' req.step := node?_id_eq _ _ n hn
  have hpin := PairChain.node_id_of_pin g reqs ctx hbelow hndF req hreq h0 n
    (List.mem_of_find?_eq_some hn) (by rw [hnid]; exact hstepk)
  rw [hnid] at hpin
  exact hpin

-- ============================================================
-- The pins immediately below a chain are free
-- ============================================================

/-- **The pin one step below a node is written in the node's identifier.** A node of the filtered
state above step 0 has a parent there; that parent sits on the step below, so `node_id_of_pin`
forces its map node to be the pin, and `PMP` copies it into the node's `parent_id`. -/
theorem parent_id_of_pin (g : GPathM) (reqs : List NodeId)
    (ctx : Pinned.Ctx (filterAllAgg g reqs)) (rc : Reader.RCtx (filterAllAgg g reqs))
    (x : PathNodeId) (n : PNodeM) (hn : (filterAllAgg g reqs).node? x = some n)
    (hx0 : 0 < x.id.step) (req : NodeId) (hreq : req ∈ reqs) (hs : req.step = x.id.step - 1) :
    x.parent_id = some req := by
  have hmem : n ∈ (filterAllAgg g reqs).nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = x := node?_id_eq _ x n hn
  -- above step 0 the node is not a root, so it has a parent in the filtered state
  have hroot : n.id.parent_id.isNone = false := by
    have hne : n.id.parent_id ≠ none := rc.shape.notroot n hmem (by rw [hid]; exact hx0)
    cases hp : n.id.parent_id with
    | none => exact absurd hp hne
    | some _ => rfl
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _
    (SelfOwn.have_parents_of_isValidNode _ n (ctx.nodeval x n hn) hroot)
  obtain ⟨mc, hmc, hmcid⟩ := rc.shape.pn n hmem c hc
  have hcstep : c.id.step = req.step := by
    have := rc.shape.pbelow n hmem c hc
    rw [hid] at this; omega
  -- its map node is the pin
  have hcid : c.id = req := by
    rw [← hmcid]
    exact PairChain.node_id_of_pin g reqs ctx rc.below rc.nodup req hreq
      (by rw [← hcstep]; have := rc.snn mc hmc; rw [hmcid] at this; exact this) mc hmc
      (by rw [hmcid]; exact hcstep)
  -- and `PMP` copies it into the identifier
  have hpmp := rc.pmp n hmem c hc
  rw [hid, hcid] at hpmp
  exact hpmp.symm

/-- **The pin two steps below is written in the identifier too** — that is the third component, and
the reason the window was widened. `GPMP` reads it off the parent's own `parent_id`, which
`parent_id_of_pin` has just identified with the pin. -/
theorem gparent_id_of_pin (g : GPathM) (reqs : List NodeId)
    (ctx : Pinned.Ctx (filterAllAgg g reqs)) (rc : Reader.RCtx (filterAllAgg g reqs))
    (x : PathNodeId) (n : PNodeM) (hn : (filterAllAgg g reqs).node? x = some n)
    (hx0 : 1 < x.id.step) (req : NodeId) (hreq : req ∈ reqs) (hs : req.step = x.id.step - 2) :
    x.gparent_id = some req := by
  have hmem : n ∈ (filterAllAgg g reqs).nodes := List.mem_of_find?_eq_some hn
  have hid : n.id = x := node?_id_eq _ x n hn
  have hroot : n.id.parent_id.isNone = false := by
    have hne : n.id.parent_id ≠ none := rc.shape.notroot n hmem (by rw [hid]; omega)
    cases hp : n.id.parent_id with
    | none => exact absurd hp hne
    | some _ => rfl
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _
    (SelfOwn.have_parents_of_isValidNode _ n (ctx.nodeval x n hn) hroot)
  obtain ⟨mc, hmc, hmcid⟩ := rc.shape.pn n hmem c hc
  have hcstep : c.id.step = x.id.step - 1 := by
    have := rc.shape.pbelow n hmem c hc
    rw [hid] at this; exact this
  -- the parent's own `parent_id` is the pin, by the previous lemma one step down
  have hcpar : c.parent_id = some req :=
    parent_id_of_pin g reqs ctx rc c mc (by rw [← hmcid]; exact node?_of_mem rc.nodup mc hmc)
      (by rw [hcstep]; omega) req hreq (by rw [hcstep]; omega)
  -- and `GPMP` copies it into the identifier's third component
  have hgpmp := rc.gpmp.1 n hmem c hc
  rw [hid, hcpar] at hgpmp
  exact hgpmp

/-- **So the two picks the descent makes just below a chain cannot miss their pins.**

The identifier of the chain's lowest pick carries the pinned map nodes of the two steps below it
(`parent_id_of_pin`, `gparent_id_of_pin`), and in `g` the picks are parent-linked, so `PMP` and
`GPMP` force their map nodes to be exactly those. With a window of two only the first of the two
would be free; the third component buys the second.

This is the residue of `(★)` cut by `w - 1 = 2` steps: what is left to steer are the pins **three
or more** steps below the chain's lowest pick. -/
theorem pins_below_free (g : GPathM) (reqs : List NodeId)
    (rcg : Reader.RCtx g) (ctx : Pinned.Ctx (filterAllAgg g reqs))
    (rc : Reader.RCtx (filterAllAgg g reqs))
    (sel : Int → PathNodeId) (lo : Int) (hlo : 0 < lo)
    (hs : SoundFrom (filterAllAgg g reqs) sel lo)
    (hlohi : lo ≤ (filterAllAgg g reqs).current_step - 1)
    (sel' : Int → PathNodeId) (hagree : ∀ i, lo ≤ i → sel' i = sel i)
    (hs' : SoundFrom g sel' 0) :
    (∀ req ∈ reqs, 0 ≤ req.step → req.step = lo - 1 → (sel' req.step).id = req) ∧
      (∀ req ∈ reqs, 0 ≤ req.step → req.step = lo - 2 → (sel' req.step).id = req) := by
  have hcsF : (filterAllAgg g reqs).current_step = g.current_step :=
    (pruned_filterAllAgg g reqs).step_eq
  -- the lowest pick of the chain, as a node of the filtered state
  obtain ⟨hsome, hstep⟩ := hs.node lo (Int.le_refl _) (by omega)
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp hsome
  have hxlo : sel' lo = sel lo := hagree lo (Int.le_refl _)
  -- the pick at `lo - 1` is a parent of `sel lo` in `g`, so `PMP` fixes its map node
  have hpar : sel' (lo - 1) ∈ ((g.node? (sel' (lo - 1 + 1))).map PNodeM.parents).getD [] :=
    hs'.parent_link (lo - 1) (by omega) (by rw [← hcsF]; omega)
  rw [show lo - 1 + 1 = lo from by omega] at hpar
  obtain ⟨mx, hmx⟩ := Option.isSome_iff_exists.mp (hs'.node lo (by omega) (by rw [← hcsF]; omega)).1
  rw [hmx] at hpar
  simp only [Option.map_some, Option.getD_some] at hpar
  have hmxid : mx.id = sel' lo := node?_id_eq g _ mx hmx
  have hpmp := rcg.pmp mx (List.mem_of_find?_eq_some hmx) _ hpar
  rw [hmxid, hxlo] at hpmp
  refine ⟨fun req hreq hr0 hrs => ?_, fun req hreq hr0 hrs => ?_⟩
  · -- one step below: `parent_id_of_pin` plus `PMP` in `g`
    have := parent_id_of_pin g reqs ctx rc (sel lo) nx hnx (by rw [hstep]; omega) req hreq
      (by rw [hstep]; omega)
    rw [this] at hpmp
    rw [hrs]
    exact Option.some.inj hpmp
  · -- two steps below: the same, one level deeper, through `GPMP`
    have hgp := gparent_id_of_pin g reqs ctx rc (sel lo) nx hnx (by rw [hstep]; omega) req hreq
      (by rw [hstep]; omega)
    -- the pick at `lo - 2` is a parent of the pick at `lo - 1`
    have hpar2 : sel' (lo - 2) ∈ ((g.node? (sel' (lo - 2 + 1))).map PNodeM.parents).getD [] :=
      hs'.parent_link (lo - 2) (by omega) (by rw [← hcsF]; omega)
    rw [show lo - 2 + 1 = lo - 1 from by omega] at hpar2
    obtain ⟨mc, hmc⟩ :=
      Option.isSome_iff_exists.mp (hs'.node (lo - 1) (by omega) (by rw [← hcsF]; omega)).1
    rw [hmc] at hpar2
    simp only [Option.map_some, Option.getD_some] at hpar2
    have hmcid : mc.id = sel' (lo - 1) := node?_id_eq g _ mc hmc
    have hpmp2 := rcg.pmp mc (List.mem_of_find?_eq_some hmc) _ hpar2
    -- `GPMP` in `g`: the grandparent the lowest pick declares is the parent of its parent
    have hgpg := rcg.gpmp.1 mx (List.mem_of_find?_eq_some hmx) _ hpar
    rw [hmxid, hxlo, hgp] at hgpg
    rw [hmcid, ← hgpg] at hpmp2
    rw [hrs]
    exact Option.some.inj hpmp2

-- ============================================================
-- One send
-- ============================================================

/-- **A send keeps the descent.** The weakly filtered state is filtered and reviewed
(`ReqCompletion`), then grown by the row (`noDeadEnd_addNode`); the reader's invariants the `up`
case asks for all come from `MInv`. -/
theorem noDeadEnd_sent (hR : ReqAll) (k : Int) (hk : 0 ≤ k) (kv : NodeId × GPathM)
    (hsok : StateOkF φ k kv) (hm : MInv φ kv.2) (d : NodeId)
    (hd : d ∈ mapSons φ kv.1.step kv.1.index)
    (hv : isValid (sent φ kv.2 d) = true) :
    NoDeadEnd (sent φ kv.2 d) := by
  -- the state under the new row, and the fact that the send makes it valid
  have hprF : Pruned kv.2 (ClauseReview.pinnedAt φ kv.2 d) :=
    Pruned.trans (ConservationCore.pruned_filterWeakAll _ _) (pruned_filterAllAgg _ _)
  have hcsF : (ClauseReview.pinnedAt φ kv.2 d).current_step = k + 1 := by
    rw [hprF.step_eq, hsok.step]
  have hcsW : (filterWeakAll kv.2 (weakReqOfCnf φ d)).current_step = k + 1 := by
    rw [(ConservationCore.pruned_filterWeakAll kv.2 (weakReqOfCnf φ d)).step_eq, hsok.step]
  have hdstep : d.step = k + 1 := PinHistory.dstep_of φ k kv hsok d hd
  have hvF : isValid (ClauseReview.pinnedAt φ kv.2 d) = true := ClauseReview.valid_pinned φ kv.2 d hv
  have heq : sent φ kv.2 d = addNode (ClauseReview.pinnedAt φ kv.2 d) d "" := by
    rw [ClauseReview.sent_eq]; unfold GPathM.up; rw [hvF]; rfl
  -- the reader's invariants the `up` case asks for, all from `MInv`
  have hrcW : Reader.RCtx (filterWeakAll kv.2 (weakReqOfCnf φ d)) :=
    RCtx_of_keeps (ReaderAggRun.keeps_filterWeakAll _ _) hm.rctx
  have hRF : ReadableAgg (ClauseReview.pinnedAt φ kv.2 d) := ⟨_, _, hrcW, rfl⟩
  have rcF := RCtx_of_readableAgg _ hRF
  have ctxF : Pinned.Ctx (ClauseReview.pinnedAt φ kv.2 d) :=
    Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRF) hvF
  -- the filter case, then the `up` case
  have hndF : NoDeadEnd (ClauseReview.pinnedAt φ kv.2 d) :=
    DescentFilter.noDeadEnd_filterAllAgg_of_completion _ (reqOfCnf φ d) (by rw [hcsW]; omega)
      (hR _ (reqOfCnf φ d))
  rw [heq]
  exact DescentUp.noDeadEnd_addNode _ d "" ctxF rcF.nodup (MachineOk_of_pruned hprF hm.mok)
    (by rw [hdstep, hcsF]) (by rw [hcsF]; omega) hvF rcF.below hndF

-- ============================================================
-- One advance
-- ============================================================

/-- **A send lands on a free key or joins what is there.** -/
theorem noDeadEnd_insertPure (hJ : JoinAll) (acc : PureLine) (key : NodeId) (g : GPathM)
    (hacc : ∀ kv ∈ acc, NoDeadEnd kv.2) (hg : NoDeadEnd g) :
    ∀ kv ∈ insertPure acc key g, NoDeadEnd kv.2 := by
  rintro ⟨d, B⟩ hB
  rcases insert_src acc key g d B hB with ⟨_, hcase⟩ | ⟨hmem, _⟩
  · rcases hcase with rfl | ⟨e, he, rfl⟩
    · exact hg
    · show NoDeadEnd (doJoin e g)
      unfold doJoin
      split
      · next hok => exact DescentJoin.noDeadEnd_join e g hok (hacc (key, e) he) hg (hJ e g)
      · exact hacc (key, e) he
  · exact hacc (d, B) hmem

/-- **One advance keeps the descent.** -/
theorem noDeadEnd_advance (hR : ReqAll) (hJ : JoinAll) (k : Int) (hk : 0 ≤ k) (L : PureLine)
    (hLI : LineInv φ k L) :
    ∀ kv ∈ pureAdvanceW φ L, NoDeadEnd kv.2 := by
  refine advance_inv φ (fun acc => ∀ kv ∈ acc, NoDeadEnd kv.2) L ?_
    (by intro kv hkv; cases hkv)
  intro kv hkv d hd acc hacc
  rw [sendToW_eq]
  split
  · next hv =>
    exact noDeadEnd_insertPure hJ acc d _ hacc
      (noDeadEnd_sent φ hR k hk kv (hLI.1.2 kv hkv) (hLI.2 kv hkv) d hd hv)
  · exact hacc

-- ============================================================
-- The whole run
-- ============================================================

/-- The seed line: every state is an `initSeed`, and those have no dead ends outright. -/
theorem noDeadEnd_init (hJ : JoinAll) : ∀ kv ∈ pureInit φ, NoDeadEnd kv.2 := by
  suffices h : ∀ d B, (d, B) ∈ pureInit φ → NoDeadEnd B by
    rintro ⟨d, B⟩ hB; exact h d B hB
  simp only [pureInit]
  have main : ∀ (l : List NodeId) (acc : PureLine), (∀ d B, (d, B) ∈ acc → NoDeadEnd B) →
      ∀ d B, (d, B) ∈ l.foldl (fun line id => insertPure line id (GPathM.initSeed id "")) acc →
        NoDeadEnd B := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons x xs ih =>
      intro acc h
      simp only [List.foldl_cons]
      refine ih _ ?_
      intro d B hB
      rcases insert_src acc x _ d B hB with ⟨hdd, hB'⟩ | ⟨hB', _⟩
      · subst hdd
        rcases hB' with rfl | ⟨e, he, rfl⟩
        · exact DescentUp.noDeadEnd_initSeed d ""
        · show NoDeadEnd (doJoin e _)
          unfold doJoin
          split
          · next hok =>
            exact DescentJoin.noDeadEnd_join e _ hok (h d e he)
              (DescentUp.noDeadEnd_initSeed d "") (hJ e _)
          · exact h d e he
      · exact h d B hB'
  exact main _ [] (fun d B h => absurd h List.not_mem_nil)

/-- **The descent, across the whole run.** -/
theorem noDeadEnd_steps (hwf : WF φ) (hR : ReqAll) (hJ : JoinAll) :
    ∀ (n : Nat), ∀ kv ∈ pureStepsW φ n (pureInit φ), NoDeadEnd kv.2 := by
  intro n
  cases n with
  | zero => exact noDeadEnd_init φ hJ
  | succ n =>
    rw [RunHistory.pureStepsW_succ]
    have hLI := LineInv_steps φ hwf n 0 (pureInit φ) (LineInv_init φ hwf)
    rw [show (0 : Int) + (n : Int) = (n : Int) by omega] at hLI
    exact noDeadEnd_advance φ hR hJ (n : Int) (by omega) _ hLI

theorem noDeadEnd_run (hwf : WF φ) (hR : ReqAll) (hJ : JoinAll) :
    ∀ kv ∈ pureRunW φ, NoDeadEnd kv.2 :=
  noDeadEnd_steps φ hwf hR hJ _

/-- **The verdict, from the completion alone.** A reader's state is read after one more
`filterAllAgg`, so the filter case applies to it directly and **the join and the `up` are not
needed at all**: the descent the verdict consumes is the one the final review itself provides.
The induction over the run (`noDeadEnd_run`) is what one would need to *prove* the completion,
not to use it. -/
theorem sat_of_reqCompletion (hwf : WF φ) (hR : ReqAll)
    (kv : NodeId × GPathM) (hkv : kv ∈ pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ := by
  obtain ⟨hm, hstep, _⟩ := ReaderAggRun.pureRunW_state φ hwf kv hkv
  refine NoDeadEndVerdict.sat_of_noDeadEnd φ hwf kv hkv hv ?_
  exact DescentFilter.noDeadEnd_filterAllAgg_of_completion kv.2 [] (by
    rw [hstep]; exact ConservationCore.stepCount_pos φ) (hR kv.2 [])

/-- info: 'AbsSat.GraphPath.Model.DescentRun.parent_id_of_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parent_id_of_pin

/-- info: 'AbsSat.GraphPath.Model.DescentRun.gparent_id_of_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gparent_id_of_pin

/-- info: 'AbsSat.GraphPath.Model.DescentRun.pins_below_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pins_below_free

/-- info: 'AbsSat.GraphPath.Model.DescentRun.reqCompletion_of_noDeadEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reqCompletion_of_noDeadEnd

/-- info: 'AbsSat.GraphPath.Model.DescentRun.noDeadEnd_sent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_sent

/-- info: 'AbsSat.GraphPath.Model.DescentRun.noDeadEnd_advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_advance

/-- info: 'AbsSat.GraphPath.Model.DescentRun.noDeadEnd_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noDeadEnd_run

/-- info: 'AbsSat.GraphPath.Model.DescentRun.sat_of_reqCompletion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_reqCompletion

end AbsSat.GraphPath.Model.DescentRun
