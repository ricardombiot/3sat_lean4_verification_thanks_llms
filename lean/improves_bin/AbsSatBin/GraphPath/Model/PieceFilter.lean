-- lean/improves_bin/AbsSatBin/GraphPath/Model/PieceFilter.lean
import AbsSatBin.GraphPath.Model.ChainRoute

/-!
# The join is decompressed by filtering by the key of the source

Measured (`julia/improves_bin/test_3sat/probes/decompress_probe.jl`, D1): filtering a joined state `J` of
line `n+1` by the key `k` of the source of one of its pieces `A` gives back exactly `A`, table by table
(4 094 pieces of 4 094). The union loses nothing and can be undone.

* **`piece_survives_filter`** (the half `A ⊆ filter(J, {k})`, proved): the reviewed piece is a kernel
  (`KernelReader.kernel_of_review`), it sits below `J` (the join only adds, `PieceJoin.piece_grown`), and at
  step `n` it names only `k` (`PieceJoin.mid_key`). The review never goes below a kernel
  (`Kernel.below_filterAll`), so the whole reviewed piece survives the filter by its own key.
* **`filter_in_piece`** (the half `filter(J, {k}) ⊆ A`, reduced): if every entry the filter leaves lies on a
  chain (`EntryOnChain`), no entry of the other piece survives. The chain climbs to `J`, goes down into the
  piece of its own key at step `n` (`PieceJoin.chain_in_piece`), and that key is the pinned one.
  `EntryOnChain` of the filtered state is the open part: the review computes the greatest kernel
  (`Kernel.below_review`), and a kernel only has local support; that every entry of it lies on a chain is
  the entry form of `NoDeadEnd`. Measured: every entry of every line and reader state lies on a chain
  (`supported_probe.jl`, 74 k states, 0 failures).
* **`entryOnChain_of_mapCert`**: in a kernel every entry is a clique of two with witnesses (pair rule plus
  symmetry), so `EntryOnChain` is `MapCert` on cliques of two. **`mapCert_filter_pin`**: a pin keeps
  `MapCert` (the witnesses of the pinned kernel own only the pinned node at its step). Together:
  **`filter_in_piece_of_mapCert`**, under `MapCert` of the joined state the filter by a key leaves only its
  piece — with `ChainRoute.combined_invariant`, under `PieceLocal` the join is decompressed exactly.
-/

namespace AbsSatBin.GraphPath.Model.PieceFilter

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.Kernel

/-- `Below` is transitive. -/
theorem below_trans {X Y Z : GPathM} (h₁ : Below X Y) (h₂ : Below Y Z) : Below X Z where
  step := h₁.step.trans h₂.step
  gow := fun q hq => h₁.gow q (h₂.gow q hq)
  node := fun p nz hz => by
    obtain ⟨ny, hny, hoy, hpy, hsy⟩ := h₂.node p nz hz
    obtain ⟨nx, hnx, hox, hpx, hsx⟩ := h₁.node p ny hny
    exact ⟨nx, hnx, fun q hq => hox q (hoy q hq), fun q hq => hpx q (hpy q hq), fun q hq => hsx q (hsy q hq)⟩

/-- A state sits below what it grows into. -/
theorem below_of_grown {g g' : GPathM} (h : Grown g g') : Below g' g where
  step := h.step_eq
  gow := h.gowners_grown
  node := h.node?_grown

/-- A state grows into what it sits below. -/
theorem grown_of_below {X h : GPathM} (hb : Below X h) : Grown h X where
  step_eq := hb.step
  gowners_grown := hb.gow
  node?_grown := hb.node

/-- Every entry of a table lies on a chain through its node. -/
def EntryOnChain (g : GPathM) : Prop :=
  ∀ q nq, g.node? q = some nq → ∀ v ∈ nq.owners, ∃ sel, ChainSound g sel ∧
    0 ≤ q.id.step ∧ q.id.step < g.current_step ∧ 0 ≤ v.id.step ∧ v.id.step < g.current_step ∧
    sel q.id.step = q ∧ sel v.id.step = v

-- ============================================================
-- `EntryOnChain` is `MapCert` on cliques of two
-- ============================================================

/-- **In a kernel, every entry is a clique of two with witnesses**: the pair rule gives, at every step, a
node in both tables, and symmetry makes it own both ends. So `MapCert` gives every entry a chain. -/
theorem entryOnChain_of_mapCert {g : GPathM} (hk : Kernel g) (hso : Ownership.SelfOwned g)
    (hbelow : ∀ n ∈ g.nodes, n.id.id.step < g.current_step) (hab : KernelReader.OwnAbove g)
    (hm : MapCert.MapCert g) : EntryOnChain g := by
  intro q nq hq v hv
  obtain ⟨nv, hnv⟩ := hk.isNode_owner q nq hq v hv
  have hqq := hso q nq hq
  have hvv := hso v nv hnv
  have hqv := hk.sym q nq v nv hq hnv hv
  have hQ : CliqueTri.Clique g [q, v] := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨nq, hq, fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hqq
        · rw [List.mem_singleton.mp hx]; exact hv⟩
    · rw [List.mem_singleton.mp hp]
      exact ⟨nv, hnv, fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hqv
        · rw [List.mem_singleton.mp hx]; exact hvv⟩
  have hW : MapCert.WitR g [q, v] [] := by
    intro l h0 h1
    obtain ⟨r, hrq, hrv, hrs⟩ := hk.pair q nq v nv hq hnv hv l h0 h1
    obtain ⟨nr, hnr⟩ := hk.isNode_owner q nq hq r hrq
    refine ⟨r, nr, hnr, hrs, fun x hx => ?_, fun _ h => absurd h List.not_mem_nil⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hk.sym x nq r nr hq hnr hrq
    · rw [List.mem_singleton.mp hx]; exact hk.sym v nv r nr hnv hnr hrv
  obtain ⟨sel, hs, hon, _⟩ := hm [q, v] [] hQ hW
  have hmq := List.mem_of_find?_eq_some hq
  have hmv := List.mem_of_find?_eq_some hnv
  have hiq := node?_id_eq _ q nq hq
  have hiv := node?_id_eq _ v nv hnv
  refine ⟨sel, hs, hab nq hmq q hqq, ?_, hab nv hmv v hvv, ?_, hon q List.mem_cons_self,
    hon v (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · have := hbelow nq hmq; rw [hiq] at this; exact this
  · have := hbelow nv hmv; rw [hiv] at this; exact this

/-- **A pin keeps `MapCert`** when the pinned state is a kernel: its witnesses own, at the pinned step, only
the pinned map node, so a clique with witnesses of the pinned state has, in the state, witnesses that also
own the pin; its certificate goes through the pin and survives the filter. -/
theorem mapCert_filter_pin (X : GPathM) (hnd : NodupIds X) (k : NodeId) (hkF : Kernel (filterAll X [k]))
    (h0 : 0 ≤ k.step) (h1 : k.step < X.current_step) (hm : MapCert.MapCert X) :
    MapCert.MapCert (filterAll X [k]) := by
  have hb := KernelIff.below_filterAll_self X hnd [k]
  intro Q R hQ hW
  have hQX : CliqueTri.Clique X Q := fun p hp => by
    obtain ⟨np, hnp, hpQ⟩ := hQ p hp
    obtain ⟨nx, hnx, ho, _, _⟩ := hb.node p np hnp
    exact ⟨nx, hnx, fun s hs => ho s (hpQ s hs)⟩
  have hWX : MapCert.WitR X Q (k :: R) := by
    intro l hl0 hl1
    obtain ⟨r, nr, hnr, hrs, hrQ, hrR⟩ := hW l hl0 (by rw [← hb.step]; exact hl1)
    obtain ⟨nx, hnx, hox, _, _⟩ := hb.node r nr hnr
    refine ⟨r, nx, hnx, hrs, fun p hp => hox p (hrQ p hp), fun m hm => ?_⟩
    rcases List.mem_cons.mp hm with rfl | hm'
    · obtain ⟨hall, _, _⟩ := (isValidNode_iff _ nr).mp (hkF.valid r nr hnr)
      have he := List.all_eq_true.mp hall m.step
        (mem_intRange_zero m.step _ h0 (by rw [← hb.step]; exact h1))
      obtain ⟨p, hp, hps⟩ := List.any_eq_true.mp he
      have hg : p ∈ (filterRequire X m).gowners :=
        (pruned_review (filterRequire X m)).gowners_sub _ (hkF.own r nr hnr p hp)
      have := (List.mem_filter.mp hg).2
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this hps
      rcases this with h | h
      · exact absurd hps h
      · exact ⟨p, hox p hp, h⟩
    · obtain ⟨p, hp, hpm⟩ := hrR m hm'
      exact ⟨p, hox p hp, hpm⟩
  obtain ⟨sel, hs, hon, hR⟩ := hm Q (k :: R) hQX hWX
  refine ⟨sel, ChainSound_filterAll X [k] sel hs (fun r hr hr0 hr1 => ?_), hon,
    fun m hm hm0 hm1 => hR m (List.mem_cons_of_mem _ hm) hm0 (by rw [hb.step]; exact hm1)⟩
  rw [List.mem_singleton.mp hr] at hr0 hr1 ⊢
  exact hR k List.mem_cons_self hr0 hr1

variable (φ : Cnf) (hbd : Bounded φ) (n : Nat)
include hbd

/-- **The reviewed piece survives the filter of the joined state by the key of its source.** -/
theorem piece_survives_filter (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true)
    (hvr : isValid (review (upF φ kv.2 d)) = true) :
    ∃ J, (d, J) ∈ line φ (n + 1) ∧ Below (filterAll J [kv.1]) (review (upF φ kv.2 d)) := by
  have hok : StateOk φ n kv := (lineOk φ n).2 kv hkv
  have hA : StateOk φ ((n : Int) + 1) (d, upF φ kv.2 d) := StateOk_sent φ n kv hok d hd hv
  have hreach := MapReachable.reachable_of_mapReachable φ hbd _ hA.reach
  have hnd := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreach
  have c := Reader.RCtx_reachable (reqOf φ) (isProhibited φ) _ hnd hreach
  have hs := (SymMachine.symInv_reachable (reqOf φ) (isProhibited φ) _ hreach hv).1
  have hab := KernelReader.ownAbove_reachable (reqOf φ) (isProhibited φ) _ hreach
  have hk : Kernel (review (upF φ kv.2 d)) := KernelReader.kernel_of_review _ c hs hab hvr
  have hbA : Below (upF φ kv.2 d) (review (upF φ kv.2 d)) :=
    KernelIff.below_filterAll_self (upF φ kv.2 d) hnd []
  obtain ⟨J, hJ, hgr⟩ := PieceJoin.piece_grown φ n kv hkv d hd hv
  refine ⟨J, hJ, below_filterAll hk (below_trans (below_of_grown hgr) hbA) [kv.1] ?_⟩
  -- at step `n` the reviewed piece names only the key of its source
  intro r hr q hq hqs
  rw [List.mem_singleton.mp hr] at hqs ⊢
  have hkey : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 hok.onMap
  obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp
    ((GownersNodes.hasNode_iff _ q).mp (c.gn q (hbA.gow q hq)))
  exact PieceJoin.mid_key φ hbd n kv hkv d hd hv q nq hnq (by rw [hqs, hkey])

/-- info: 'AbsSatBin.GraphPath.Model.PieceFilter.piece_survives_filter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms piece_survives_filter

-- ============================================================
-- The other half: the filter leaves nothing of the other piece, if its entries lie on chains
-- ============================================================

/-- **The filter of the joined state by the key of a source leaves only that piece**, when every entry the
filter leaves lies on a chain: the chain climbs to the joined state, goes down into the piece of its own
key at step `n` (`PieceJoin.chain_in_piece`), and the key it names at step `n` is the pinned one. -/
theorem filter_in_piece (hn : (n : Int) + 1 < stepCount φ) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n)
    (d : NodeId) (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true) (J : GPathM)
    (hJ : (d, J) ∈ line φ (n + 1)) (hvF : isValid (filterAll J [kv.1]) = true)
    (hsup : EntryOnChain (filterAll J [kv.1])) :
    ∀ q nq, (filterAll J [kv.1]).node? q = some nq →
      ∃ nA, (upF φ kv.2 d).node? q = some nA ∧ ∀ v ∈ nq.owners, v ∈ nA.owners := by
  have hok : StateOk φ n kv := (lineOk φ n).2 kv hkv
  have hkey : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 hok.onMap
  have hA : StateOk φ ((n : Int) + 1) (d, upF φ kv.2 d) := StateOk_sent φ n kv hok d hd hv
  have hcsA : (upF φ kv.2 d).current_step = (n : Int) + 2 := by rw [hA.step]; omega
  have hokJ : StateOk φ ((n + 1 : Nat) : Int) (d, J) := (lineOk φ (n + 1)).2 _ hJ
  have hcsJ : J.current_step = (n : Int) + 2 := by rw [hokJ.step]; push_cast; omega
  have hreachJ := MapReachable.reachable_of_mapReachable φ hbd _ hokJ.reach
  have hndJ := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreachJ
  have cJ := Reader.RCtx_reachable (reqOf φ) (isProhibited φ) _ hndJ hreachJ
  have hbJ : Below J (filterAll J [kv.1]) := KernelIff.below_filterAll_self J hndJ [kv.1]
  have hcsF : (filterAll J [kv.1]).current_step = (n : Int) + 2 := by rw [← hbJ.step, hcsJ]
  -- a chain of the filter is, below `n+2`, a chain of the piece
  have aux : ∀ sel, ChainSound (filterAll J [kv.1]) sel →
      ∃ sel', ChainSound (upF φ kv.2 d) sel' ∧ ∀ k, 0 ≤ k → k < (n : Int) + 2 → sel' k = sel k := by
    intro sel hs
    have hsJ : ChainSound (d, J).2 sel := ChainSound_of_grown (grown_of_below hbJ) sel hs
    obtain ⟨kv2, hkv2, hd2, hv2, sel', hs', heq⟩ := PieceJoin.chain_in_piece φ hbd n hn (d, J) hJ sel hsJ
    -- the chain names the pinned key at step `n`
    have hg : sel n ∈ (filterAll J [kv.1]).gowners := hs.chain.2.2 n (by omega) (by rw [hcsF]; omega)
    have hg' : sel n ∈ (filterRequire J kv.1).gowners :=
      (pruned_review (filterRequire J kv.1)).gowners_sub _ hg
    have hsn : (sel n).id.step = (n : Int) := (hs.chain.1.1 n (by omega) (by rw [hcsF]; omega)).2
    have hid : (sel n).id = kv.1 := by
      have := (List.mem_filter.mp hg').2
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
      rcases this with h | h
      · exact absurd (hsn.trans hkey.symm) h
      · exact h
    obtain ⟨hsome, hstep⟩ := hs'.chain.1.1 n (by omega) (by
      have := (StateOk_sent φ n kv2 ((lineOk φ n).2 kv2 hkv2) d hd2 hv2).step
      rw [this]; omega)
    obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp hsome
    have hk2 := PieceJoin.mid_key φ hbd n kv2 hkv2 d hd2 hv2 (sel' n) nr hnr hstep
    have he : kv2 = kv := key_inj (line φ n) (lineOk φ n).1 kv2 hkv2 kv hkv (by
      rw [← hk2, heq n (by omega) (by omega), hid])
    subst he
    exact ⟨sel', hs', heq⟩
  have cF := Reader.RCtx_filterAll J cJ [kv.1]
  have hso : Ownership.SelfOwned (filterAll J [kv.1]) :=
    SelfOwn.SelfOwned_of_OOS (filterRequire J kv.1) hvF cF.oos cF.snn cF.below
  intro q nq hq
  obtain ⟨sel, hs, hq0, hq1, _, _, hselq, _⟩ := hsup q nq hq q (hso q nq hq)
  obtain ⟨sel', hs', heq⟩ := aux sel hs
  rw [hcsF] at hq1
  have hq' : sel' q.id.step = q := by rw [heq _ hq0 hq1, hselq]
  obtain ⟨nA, hnA⟩ := Option.isSome_iff_exists.mp
    (by have := (hs'.chain.1.1 q.id.step hq0 (by rw [hcsA]; exact hq1)).1; rw [hq'] at this; exact this)
  refine ⟨nA, hnA, fun v hv => ?_⟩
  obtain ⟨sel2, hs2, hq0', hq1', hv0, hv1, hq2, hv2⟩ := hsup q nq hq v hv
  obtain ⟨sel2', hs2', heq2⟩ := aux sel2 hs2
  rw [hcsF] at hq1' hv1
  have hq2' : sel2' q.id.step = q := by rw [heq2 _ hq0' hq1', hq2]
  have hv2' : sel2' v.id.step = v := by rw [heq2 _ hv0 hv1, hv2]
  by_cases hqv : v.id.step = q.id.step
  · have hvq : v = q := by rw [← hv2', ← hq2', hqv]
    have := hs2'.self_owned q.id.step hq0' (by rw [hcsA]; exact hq1')
    rw [hq2'] at this
    simp only [ownersOf, hnA] at this
    rw [hvq]; exact this
  · have := hs2'.chain.2.1 v.id.step q.id.step hv0 hq0' (by rw [hcsA]; exact hv1) (by rw [hcsA]; exact hq1') hqv
    rw [hv2', hq2'] at this
    simp only [ownersAt, ownersOf, hnA] at this
    exact (List.mem_filter.mp this).1

/-- info: 'AbsSatBin.GraphPath.Model.PieceFilter.filter_in_piece' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms filter_in_piece

/-- **The filtered joined state is a kernel**, self-owned, below its step, with owners above `0`. -/
theorem filter_ctx (d : NodeId) (J : GPathM) (hJ : (d, J) ∈ line φ (n + 1)) (k : NodeId)
    (hvF : isValid (filterAll J [k]) = true) :
    NodupIds J ∧ Kernel (filterAll J [k]) ∧ Ownership.SelfOwned (filterAll J [k]) ∧
      (∀ m ∈ (filterAll J [k]).nodes, m.id.id.step < (filterAll J [k]).current_step) ∧
      KernelReader.OwnAbove (filterAll J [k]) := by
  have hokJ : StateOk φ ((n + 1 : Nat) : Int) (d, J) := (lineOk φ (n + 1)).2 _ hJ
  have hreachJ := MapReachable.reachable_of_mapReachable φ hbd _ hokJ.reach
  have hndJ := Reader.NodupIds_reachable (reqOf φ) (isProhibited φ) _ hreachJ
  have cJ := Reader.RCtx_reachable (reqOf φ) (isProhibited φ) _ hndJ hreachJ
  have sJ := (SymMachine.symInv_reachable (reqOf φ) (isProhibited φ) _ hreachJ hokJ.valid).1
  have abJ := KernelReader.ownAbove_reachable (reqOf φ) (isProhibited φ) _ hreachJ
  have cX : Reader.RCtx ([k].foldl filterRequire J) :=
    ReaderAgg.RCtx_of_keeps (ReaderAgg.keeps_foldl _ ReaderAgg.keeps_filterRequire [k] J) cJ
  have abX : KernelReader.OwnAbove ([k].foldl filterRequire J) := by
    intro m hm; rw [SymMachine.foldl_filterRequire_nodes] at hm; exact abJ m hm
  have hk : Kernel (filterAll J [k]) :=
    KernelReader.kernel_of_review _ cX (SymMachine.sym_foldl_filterRequire [k] J sJ) abX hvF
  have cF := Reader.RCtx_filterAll J cJ [k]
  exact ⟨hndJ, hk, SelfOwn.SelfOwned_of_OOS (filterRequire J k) hvF cF.oos cF.snn cF.below, cF.below,
    KernelReader.ownAbove_of_pruned (pruned_filterAll J [k]) abJ⟩

/-- **Under `MapCert` of the joined state, the join is decompressed exactly**: the filter by the key of a
source leaves only that piece (and `piece_survives_filter` gives the reviewed piece back). -/
theorem filter_in_piece_of_mapCert (hn : (n : Int) + 1 < stepCount φ) (kv : NodeId × GPathM)
    (hkv : kv ∈ line φ n) (d : NodeId) (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true)
    (J : GPathM) (hJ : (d, J) ∈ line φ (n + 1)) (hvF : isValid (filterAll J [kv.1]) = true)
    (hmJ : MapCert.MapCert J) :
    ∀ q nq, (filterAll J [kv.1]).node? q = some nq →
      ∃ nA, (upF φ kv.2 d).node? q = some nA ∧ ∀ v ∈ nq.owners, v ∈ nA.owners := by
  obtain ⟨hndJ, hk, hso, hbelow, hab⟩ := filter_ctx φ hbd n d J hJ kv.1 hvF
  have hokJ : StateOk φ ((n + 1 : Nat) : Int) (d, J) := (lineOk φ (n + 1)).2 _ hJ
  have hkey : kv.1.step = (n : Int) := mapNodes_step φ n kv.1 ((lineOk φ n).2 kv hkv).onMap
  exact filter_in_piece φ hbd n hn kv hkv d hd hv J hJ hvF
    (entryOnChain_of_mapCert hk hso hbelow hab
      (mapCert_filter_pin J hndJ kv.1 hk (by omega) (by rw [hokJ.step, hkey]; push_cast; omega) hmJ))

/-- info: 'AbsSatBin.GraphPath.Model.PieceFilter.filter_in_piece_of_mapCert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms filter_in_piece_of_mapCert

end AbsSatBin.GraphPath.Model.PieceFilter
