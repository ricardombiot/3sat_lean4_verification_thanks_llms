-- lean/improves_bin/AbsSatBin/GraphPath/Model/NodeHistory.lean
import AbsSatBin.GraphPath.Model.M1bSrc

/-!
# Where a node comes from (`docs/context/escalera_reader.md` §4.2ο.2, the chain form of M1b)

A node is created once, in the top row of the state of line `m` at its map node, and afterwards it is only copied (by
the UP, into the pieces) and merged (by the join). Its parents are fixed when it is created; later they only shrink.

* **`piece_node_src`**: an old node of a piece `upF X d` is a node of its source `X`, with fewer parents.
* **`node_history`**: a node `y` of a state of line `N`, at a row `m ≤ N`, is a node of the state of line `m` at `y.id`,
  and every parent it has now it had there.

This replaces the purity of the key row, which only holds for the top two rows of a joined state, in the chain form of
M1b: a node pinned at any row has a source state, found through its own history.
-/

namespace AbsSatBin.GraphPath.Model.NodeHistory

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel

variable (φ : Cnf) (hbd : Bounded φ)

include hbd

/-- **An old node of a piece is a node of its source, with fewer parents.** -/
theorem piece_node_src (N : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ line φ N) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true) (y : PathNodeId) (n1 : PNodeM)
    (hn1 : (upF φ kv.2 d).node? y = some n1) (hy : y.id.step < (N : Int) + 1) :
    ∃ nX, kv.2.node? y = some nX ∧ ∀ c ∈ n1.parents, c ∈ nX.parents := by
  obtain ⟨hok, hdst, hcs, _, hvF, hnd⟩ := src_ctx φ hbd N kv hkv d hd hv
  have c := filt_ctx φ hbd N kv hok (reqOf φ d) hvF
  have hb := KernelIff.below_filterAll_self kv.2 hnd (reqOf φ d)
  have hFcs : (filterAll kv.2 (reqOf φ d)).current_step = (N : Int) + 1 := by rw [← hb.step, hcs]
  have hdF : d.step = (filterAll kv.2 (reqOf φ d)).current_step := by rw [hFcs, ← hcs, hdst]
  have hndG := Reader.nodup_addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ) c.pc.nd c.pc.below hdF
  have hPA : Below (addNode (filterAll kv.2 (reqOf φ d)) d "" (isProhibited φ)) (upF φ kv.2 d) := by
    rcases (upF_shape φ kv.2 d hv).2 with e | e
    · rw [e]; exact ⟨rfl, fun q h => h, fun p n' h => ⟨n', h, fun _ x => x, fun _ x => x, fun _ x => x⟩⟩
    · rw [e]; exact KernelIff.below_filterAll_self _ hndG []
  obtain ⟨nG, hnG, _, hpG, _⟩ := hPA.node y n1 hn1
  obtain ⟨nF, hnF, hEq⟩ := addNode_node?_below _ d "" (isProhibited φ) hdF y nG hnG (by rw [hFcs]; exact hy)
  obtain ⟨nX, hnX, _, hpX, _⟩ := hb.node y nF hnF
  refine ⟨nX, hnX, fun c hc => hpX c ?_⟩
  have := hpG c hc
  rw [hEq, upMap_parents] at this
  exact this

/-- **Where a node comes from.** -/
theorem node_history : ∀ (N : Nat) (kv' : NodeId × GPathM), kv' ∈ line φ N → ∀ y ny, kv'.2.node? y = some ny →
    ∀ m : Nat, y.id.step = (m : Int) → m ≤ N →
      ∃ kv ∈ line φ m, kv.1 = y.id ∧ ∃ ns, kv.2.node? y = some ns ∧ ∀ c ∈ ny.parents, c ∈ ns.parents := by
  -- the top row: the node names the key of its own state
  have top : ∀ (N : Nat) (kv' : NodeId × GPathM), kv' ∈ line φ N → ∀ y ny, kv'.2.node? y = some ny →
      y.id.step = (N : Int) → ∃ kv ∈ line φ N, kv.1 = y.id ∧ ∃ ns, kv.2.node? y = some ns ∧
        ∀ c ∈ ny.parents, c ∈ ns.parents := by
    intro N kv' hkv' y ny hny hys
    have pc := M1bSrc.line_pinCtx φ hbd N kv' hkv'
    have hk := top_entry_key φ hbd N kv' hkv' y ny hny y (TriPinCut.self_own_pc pc y ny hny) hys
    exact ⟨kv', hkv', hk.symm, ny, hny, fun c h => h⟩
  intro N
  induction N with
  | zero =>
    intro kv' hkv' y ny hny m hm hmN
    have : m = 0 := by omega
    subst this
    exact top 0 kv' hkv' y ny hny hm
  | succ N ih =>
    intro kv' hkv' y ny hny m hm hmN
    by_cases hmt : m = N + 1
    · subst hmt; exact top (N + 1) kv' hkv' y ny hny (by rw [hm])
    · have hmN' : m ≤ N := by omega
      have hkv'' := hkv'
      rw [line_succ] at hkv''
      -- a piece that has the node, and its source
      obtain ⟨kv, hkv, hd, hv, n1, hn1⟩ := (src_pureAdvance φ (line φ N) kv' hkv'').1 y ny hny
      obtain ⟨nX, hnX, _⟩ := piece_node_src φ hbd N kv hkv kv'.1 hd hv y n1 hn1 (by rw [hm]; omega)
      obtain ⟨kvm, hkvm, hkey, ns, hns, _⟩ := ih kv hkv y nX hnX m hm hmN'
      refine ⟨kvm, hkvm, hkey, ns, hns, fun c hc => ?_⟩
      -- each parent comes from some piece, whose source has it; that source's history is the same state
      obtain ⟨kv2, hkv2, hd2, hv2, n2, hn2, hc2⟩ :=
        UnionLine.srcF_pureAdvance φ PNodeM.parents UnionLine.parents_joins (line φ N) kv' hkv'' y ny hny c hc
      obtain ⟨nX2, hnX2, hpX2⟩ := piece_node_src φ hbd N kv2 hkv2 kv'.1 hd2 hv2 y n2 hn2 (by rw [hm]; omega)
      obtain ⟨kvm2, hkvm2, hkey2, ns2, hns2, hp2⟩ := ih kv2 hkv2 y nX2 hnX2 m hm hmN'
      have e : kvm2 = kvm := key_inj _ (lineOk φ m).1 kvm2 hkvm2 kvm hkvm (by rw [hkey2, hkey])
      subst e
      rw [hns] at hns2; cases hns2
      exact hp2 c (hpX2 c hc2)

end AbsSatBin.GraphPath.Model.NodeHistory

/-- info: 'AbsSatBin.GraphPath.Model.NodeHistory.node_history' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsSatBin.GraphPath.Model.NodeHistory.node_history
