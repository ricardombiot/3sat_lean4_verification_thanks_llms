-- lean/improves_bin/AbsSatBin/GraphPath/Model/NoInvent.lean
import AbsSatBin.GraphPath.Model.ClauseKey

/-!
# No invented entries: every entry of a table is co-occurrence on a real path

The machine removes whole partial sets that become invalid before they reach a destination, joins at a
destination only valid sets, and its `UP` creates one node per leaf except the window it knows is wrong.
The claim that follows: **an entry of a table is never invented** — if `r` owns `q`, some partial solution
of `φ` up to that step goes through both.

* **`NoInvent g n`**: every entry of the state `g` (at line `n`) lies on a partial solution (`PreSat` up
  to `n+1`) through both of its ends.
* **`noInvent_of_semCert`**: at a reviewed state of the line, `SemCert` gives it. The pair `{r, q}` is a
  clique, and the pair rule of the kernel gives its witnesses: at every step a node that both own, and
  that owns both back.
* **Why the pair alone is not inductive** (`filter_entry_req`): after the requirement filter of a step, an
  entry `r → q` comes with a third node — a path node of the requirement in both tables. To carry the
  entry to the next step one needs a partial solution through the three of them. So the statement that
  closes under the machine's steps is the one for cliques with witnesses (`SemCert`), and the pair is
  its first instance.
-/

namespace AbsSatBin.GraphPath.Model.NoInvent

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.PrefixCarry
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.MapReachable
open AbsSatBin.GraphPath.Model.CliqueTri (Clique OwnsAll)

variable (φ : Cnf)

/-- **No invented entries** at the state `g` of line `n`: every entry lies on a partial solution through
both of its ends. -/
def NoInvent (g : GPathM) (n : Nat) : Prop :=
  ∀ r nr q, g.node? r = some nr → q ∈ nr.owners →
    ∃ a, PreSat φ a ((n : Int) + 1) ∧ pidOfAssign φ a r.id.step = r ∧ pidOfAssign φ a q.id.step = q

/-- **`SemCert` gives no invented entries** at every reviewed state of the line. -/
theorem noInvent_of_semCert (hbd : Bounded φ) (n : Nat) (hn : (n : Int) < stepCount φ) (hsem : SemCert φ n)
    (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (hv : isValid (filterAll kv.2 []) = true) :
    NoInvent φ (filterAll kv.2 []) n := by
  have hok : StateOk φ n kv := (lineOk φ n).2 kv hkv
  have hmap := mapCert_start φ hbd n hn hsem kv hkv hv
  have c := filt_ctx φ hbd n kv hok [] hv
  have hk := c.pc.ker
  have hreach := reachable_of_mapReachable φ hbd kv.2 hok.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) kv.2 hreach
  have hb := KernelIff.below_filterAll_self kv.2 hnd []
  intro r nr q hr hq
  obtain ⟨nq, hnq⟩ := hk.isNode_owner r nr hr q hq
  have hrq : r ∈ nq.owners := hk.sym r nr q nq hr hnq hq
  have hQ : Clique (filterAll kv.2 []) [r, q] := by
    intro p hp
    rcases List.mem_cons.mp hp with e | hp
    · rw [e]
      refine ⟨nr, hr, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact TriPinCut.self_own_pc c.pc r nr hr
      · rw [List.mem_singleton.mp hs]; exact hq
    · rw [List.mem_singleton.mp hp]
      refine ⟨nq, hnq, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with e' | hs
      · rw [e']; exact hrq
      · rw [List.mem_singleton.mp hs]; exact TriPinCut.self_own_pc c.pc q nq hnq
  have hW : MapCert.WitR (filterAll kv.2 []) [r, q] [] := by
    intro l h0 h1
    obtain ⟨e, her, heq, hes⟩ := hk.pair r nr q nq hr hnq hq l h0 h1
    obtain ⟨ne, hne⟩ := hk.isNode_owner r nr hr e her
    refine ⟨e, ne, hne, hes, fun s hs => ?_, fun _ h => absurd h List.not_mem_nil⟩
    rcases List.mem_cons.mp hs with e' | hs
    · rw [e']; exact hk.sym r nr e ne hr hne her
    · rw [List.mem_singleton.mp hs]; exact hk.sym q nq e ne hnq hne heq
  obtain ⟨sel, hs, hon, _⟩ := hmap [r, q] [] hQ hW
  -- the certificate of the reviewed state is one of the state itself
  have hgr : Grown (filterAll kv.2 []) kv.2 := ⟨hb.step, hb.gow, hb.node⟩
  have hs' : ChainSound kv.2 sel := ChainSound_of_grown hgr sel hs
  have hcsle : kv.2.current_step ≤ stepCount φ := by rw [hok.step]; omega
  obtain ⟨hpre, hpid⟩ := PrefixDecode.decode_prefix φ kv.2 sel hbd hcsle hok.reach hs'
  rw [hok.step] at hpre
  have hsr : r.id.step < kv.2.current_step := by
    have := c.pc.below nr (List.mem_of_find?_eq_some hr)
    rw [node?_id_eq _ r nr hr, ← hb.step] at this; exact this
  have hsq : q.id.step < kv.2.current_step := by
    have := c.pc.below nq (List.mem_of_find?_eq_some hnq)
    rw [node?_id_eq _ q nq hnq, ← hb.step] at this; exact this
  have h0r : 0 ≤ r.id.step := by
    have := c.pc.snn nr (List.mem_of_find?_eq_some hr); rw [node?_id_eq _ r nr hr] at this; exact this
  have h0q : 0 ≤ q.id.step := by
    have := c.pc.snn nq (List.mem_of_find?_eq_some hnq); rw [node?_id_eq _ q nq hnq] at this; exact this
  refine ⟨CnfChain.decode sel, hpre, ?_, ?_⟩
  · rw [hpid r.id.step h0r hsr]; exact hon r List.mem_cons_self
  · rw [hpid q.id.step h0q hsq]; exact hon q (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **After the requirement filter, every entry comes with a third node**: a path node of the
requirement that both ends own. Carrying the entry needs a partial solution through the three. -/
theorem filter_entry_req (J : GPathM) (req : NodeId) (hk : Kernel (filterAll J [req])) (h0 : 0 ≤ req.step)
    (h1 : req.step < (filterAll J [req]).current_step) (r : PathNodeId) (nr : PNodeM)
    (hr : (filterAll J [req]).node? r = some nr) (q : PathNodeId) (hq : q ∈ nr.owners) :
    ∃ e nq, (filterAll J [req]).node? q = some nq ∧ e ∈ nr.owners ∧ e ∈ nq.owners ∧ e.id = req := by
  obtain ⟨nq, hnq⟩ := hk.isNode_owner r nr hr q hq
  obtain ⟨e, her, heq, hes⟩ := hk.pair r nr q nq hr hnq hq req.step h0 h1
  exact ⟨e, nq, hnq, her, heq, ReqFilter.req_id J req e (hk.own r nr hr e her) hes⟩

/-- info: 'AbsSatBin.GraphPath.Model.NoInvent.noInvent_of_semCert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noInvent_of_semCert

/-- info: 'AbsSatBin.GraphPath.Model.NoInvent.filter_entry_req' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms filter_entry_req

end AbsSatBin.GraphPath.Model.NoInvent
