-- lean/improves_bin/AbsSatBin/GraphPath/Model/PrefixTri.lean
import AbsSatBin.GraphPath.Model.CertInvariant
import AbsSatBin.GraphPath.Model.AmbHighCore

/-!
# `PrefixTri`: the reader only needs prefix cliques

`CliqueTri` asks the pair rule relative to **every** clique. The reader never forms most of them: its
pins go at increasing steps, and everything below the last pin is forced (a single node, in every
table). The cliques it uses are **prefixes**: one node at each step `0 … k`, and none above.

* **`PrefixTri g`**: `TriP g Q` for every prefix clique `Q`. It follows from `CliqueTri`
  (`prefixTri_of_cliqueTri`) and asks nothing about cliques with gaps — the ones where witnesses of
  different branches can mix at a merge (`docs/context/ambfar.md` §4.2g–h).
* **At a reader state it gives `TriPin₁`** at the first choice (`triPin₁_of_prefixTri`): the forced
  nodes below `k` and the pin `x` form a prefix clique, and forced nodes are in every table, so the
  pair rule relative to it is `TriPin₁ g x` (`triP_congr`).
* **The pin keeps it** (`prefixTri_pin`): a prefix clique of the pinned state, with `x` and the forced
  nodes added, is a prefix clique of the state before, and `CliqueTri.triP_of_cut` carries the rule.
* So **`PrefixTri` at the starting states is enough** (`readerVerdictW_iff_of_prefixTri`). It is weaker
  than `CliqueTri`, and it runs along the machine's own order: left to right.
-/

namespace AbsSatBin.GraphPath.Model.PrefixTri

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.Kernel
open AbsSatBin.GraphPath.Model.KernelSplit
open AbsSatBin.GraphPath.Model.TriPinCut
open AbsSatBin.GraphPath.Model.TriPinAll (exists_owner_of_choiceAt)
open AbsSatBin.GraphPath.Model.CliqueTri
open AbsSatBin.GraphPath.Model.AmbTriCore
open AbsSatBin.GraphPath.Model.AmbHighCore
open AbsSatBin.GraphPath.Model.ReaderExec
open AbsSatBin.GraphPath.Model.ReaderPrefix
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.OtherBitSem (ReadPins)

/-- **A prefix clique**: a clique with a node at every step `0 … k` and none above. -/
def PrefixClique (g : GPathM) (Q : List PathNodeId) (k : Int) : Prop :=
  Clique g Q ∧ (∀ l, 0 ≤ l → l ≤ k → ∃ q ∈ Q, q.id.step = l) ∧ ∀ q ∈ Q, q.id.step ≤ k

/-- **The pair rule relative to every prefix clique.** -/
def PrefixTri (g : GPathM) : Prop := ∀ Q k, PrefixClique g Q k → TriP g Q

theorem prefixTri_of_cliqueTri {g : GPathM} (h : CliqueTri g) : PrefixTri g := fun Q _ hQ => h Q hQ.1

-- ============================================================
-- `TriP` only reads which nodes own the clique
-- ============================================================

theorem cxP_congr {g : GPathM} {P Q : List PathNodeId}
    (h : ∀ p n, g.node? p = some n → (OwnsAll P n ↔ OwnsAll Q n)) {ny : PNodeM} {w : PathNodeId}
    (hC : CxP g Q ny w) : CxP g P ny w := by
  obtain ⟨nw, hnw, hwy, hl⟩ := hC
  refine ⟨nw, hnw, hwy, fun l h0 h1 => ?_⟩
  obtain ⟨r, hr, hrw, hrs, nr, hnr, hrQ⟩ := hl l h0 h1
  exact ⟨r, hr, hrw, hrs, nr, hnr, (h r nr hnr).mpr hrQ⟩

/-- **`TriP g P` depends on `P` only through which nodes own it.** -/
theorem triP_congr {g : GPathM} {P Q : List PathNodeId}
    (h : ∀ p n, g.node? p = some n → (OwnsAll P n ↔ OwnsAll Q n)) (hT : TriP g Q) : TriP g P := by
  have h' : ∀ p n, g.node? p = some n → (OwnsAll Q n ↔ OwnsAll P n) := fun p n hn => (h p n hn).symm
  intro y ny w nw hy hw hyP hwP hC l h0 h1
  obtain ⟨r, hr, hrw, hrs, ⟨nr, hnr, hrQ⟩, cy, cw⟩ :=
    hT y ny w nw hy hw ((h y ny hy).mp hyP) ((h w nw hw).mp hwP) (cxP_congr h' hC) l h0 h1
  exact ⟨r, hr, hrw, hrs, ⟨nr, hnr, (h r nr hnr).mpr hrQ⟩, cxP_congr h cy, cxP_congr h cw⟩

-- ============================================================
-- At a reader state: the forced nodes
-- ============================================================

/-- The live entries below the choice. -/
def forced (g : GPathM) (k : Int) : List PathNodeId := g.gowners.filter (fun q => decide (q.id.step < k))

theorem mem_forced {g : GPathM} {k : Int} {q : PathNodeId} (hq : q ∈ forced g k) :
    q ∈ g.gowners ∧ q.id.step < k := by
  obtain ⟨h1, h2⟩ := List.mem_filter.mp hq
  exact ⟨h1, of_decide_eq_true h2⟩

/-- Below the choice every step has a live entry. -/
theorem forced_cover {g : GPathM} {k : Int} (hv : isValid g = true) (l : Int) (h0 : 0 ≤ l) (hl : l < k)
    (h1 : l < g.current_step) : ∃ q ∈ forced g k, q.id.step = l := by
  have hl' : l ∈ intRange 0 (g.current_step - 1) := mem_intRange h0 (by omega)
  obtain ⟨q, hq, hqs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hv l hl')
  have hqs' : q.id.step = l := eq_of_beq hqs
  exact ⟨q, List.mem_filter.mpr ⟨hq, decide_eq_true (by omega)⟩, hqs'⟩

section
variable {g : GPathM} (c : ACtx g) {k : Int} (hp : PrefixUpTo g k)
include c hp

/-- Forced nodes are in every table, so adding them to a clique changes nothing. -/
theorem ownsAll_forced (P : List PathNodeId) (p : PathNodeId) (n : PNodeM) (hn : g.node? p = some n) :
    OwnsAll (P ++ forced g k) n ↔ OwnsAll P n := by
  refine ⟨fun h q hq => h q (List.mem_append_left _ hq), fun h q hq => ?_⟩
  rcases List.mem_append.mp hq with hq | hq
  · exact h q hq
  · obtain ⟨hqg, hqs⟩ := mem_forced hq
    obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn q hqg)
    exact forced_in_all c hp q nq hnq hqs p n hn

/-- A clique of `g`, with the forced nodes added, is still a clique. -/
theorem clique_forced (P : List PathNodeId) (hP : Clique g P) : Clique g (P ++ forced g k) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨nq, hnq, hqP⟩ := hP q hq
    exact ⟨nq, hnq, (ownsAll_forced c hp P q nq hnq).mpr hqP⟩
  · obtain ⟨hqg, hqs⟩ := mem_forced hq
    obtain ⟨nq, hnq⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn q hqg)
    refine ⟨nq, hnq, fun s hs => ?_⟩
    obtain ⟨ns, hns⟩ : ∃ ns, g.node? s = some ns := by
      rcases List.mem_append.mp hs with hs | hs
      · obtain ⟨ns, hns, _⟩ := hP s hs; exact ⟨ns, hns⟩
      · exact Option.isSome_iff_exists.mp (c.pc.ker.gn s (mem_forced hs).1)
    exact forced_owns_all c hp q nq hnq hqs s (c.pc.ker.gow s ns hns)

/-- **At a reader state, `PrefixTri` gives `TriPin₁` at the first choice.** -/
theorem triPin₁_of_prefixTri (hv : isValid g = true) (x : PathNodeId) (hx : x ∈ ownersAt g.gowners k)
    (h : PrefixTri g) : TriPin₁ g x := by
  obtain ⟨hxg, hxs'⟩ := List.mem_filter.mp hx
  have hxs : x.id.step = k := eq_of_beq hxs'
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn x hxg)
  have hk1 : k < g.current_step := by rw [← hxs]; exact (CertFix.step_range c.pc x nx hnx).2
  have hxc : Clique g [x] := fun p hp => by
    rw [List.mem_singleton.mp hp]
    exact ⟨nx, hnx, fun s hs => by rw [List.mem_singleton.mp hs]; exact self_own_pc c.pc x nx hnx⟩
  have hQ : PrefixClique g ([x] ++ forced g k) k := by
    refine ⟨clique_forced c hp [x] hxc, fun l h0 hl => ?_, fun q hq => ?_⟩
    · rcases Int.lt_or_le l k with hlt | hge
      · obtain ⟨q, hq, hqs⟩ := forced_cover hv l h0 hlt (by omega)
        exact ⟨q, List.mem_append_right _ hq, hqs⟩
      · exact ⟨x, List.mem_append_left _ (List.mem_singleton.mpr rfl), by omega⟩
    · rcases List.mem_append.mp hq with hq | hq
      · rw [List.mem_singleton.mp hq, hxs]; exact Int.le_refl k
      · exact Int.le_of_lt (mem_forced hq).2
  exact triPin₁_of_triP c.pc x nx hnx
    (triP_congr (fun p n hn => (ownsAll_forced c hp [x] p n hn).symm) (h _ k hQ))
end

-- ============================================================
-- The pin keeps `PrefixTri`
-- ============================================================

/-- **The pin keeps `PrefixTri`.** -/
theorem prefixTri_pin {g : GPathM} (c : ACtx g) {k : Int} (hp : PrefixUpTo g k) (hv : isValid g = true)
    (x : PathNodeId) (hx : x ∈ ownersAt g.gowners k) (hk' : Kernel (filterAll g [x.id]))
    (h : PrefixTri g) : PrefixTri (filterAll g [x.id]) := by
  obtain ⟨hxg, hxs'⟩ := List.mem_filter.mp hx
  have hxs : x.id.step = k := eq_of_beq hxs'
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp (c.pc.ker.gn x hxg)
  have hk1 : k < g.current_step := by rw [← hxs]; exact (CertFix.step_range c.pc x nx hnx).2
  have ht := triPin₁_of_prefixTri c hp hv x hx h
  obtain ⟨e0, e1, e2, ecs⟩ := pin_cut_facts c hp x hx hk' ht
  intro P k' hP
  refine triP_of_cut c.pc x nx hnx e0 e1 e2 ecs P hP.1 (fun hxP => ?_)
  -- `x :: P`, with the forced nodes, is a prefix clique of `g`
  have hQc := clique_forced c hp (x :: P) hxP
  have hcov : ∀ K, k ≤ K → k' ≤ K → (K = k ∨ K = k') → PrefixClique g ((x :: P) ++ forced g k) K := by
    intro K hkK hk'K hK
    refine ⟨hQc, fun l h0 hl => ?_, fun q hq => ?_⟩
    · rcases Int.lt_or_le l k with hlt | hge
      · obtain ⟨q, hq, hqs⟩ := forced_cover hv l h0 hlt (by omega)
        exact ⟨q, List.mem_append_right _ hq, hqs⟩
      · rcases Int.lt_or_le k l with hgt | hle
        · -- above the pin: `P` covers it
          have hlk' : l ≤ k' := by
            rcases hK with e | e
            · omega
            · omega
          obtain ⟨q, hq, hqs⟩ := hP.2.1 l h0 hlk'
          exact ⟨q, List.mem_append_left _ (List.mem_cons_of_mem _ hq), hqs⟩
        · exact ⟨x, List.mem_append_left _ List.mem_cons_self, by omega⟩
    · rcases List.mem_append.mp hq with hq | hq
      · rcases List.mem_cons.mp hq with e | hq
        · rw [e, hxs]; exact hkK
        · exact Int.le_trans (hP.2.2 q hq) hk'K
      · exact Int.le_trans (Int.le_of_lt (mem_forced hq).2) hkK
  have hcg : ∀ p n, g.node? p = some n → (OwnsAll (x :: P) n ↔ OwnsAll ((x :: P) ++ forced g k) n) :=
    fun p n hn => (ownsAll_forced c hp (x :: P) p n hn).symm
  rcases Int.le_total k' k with hle | hle
  · exact triP_congr hcg (h _ k (hcov k (Int.le_refl k) hle (Or.inl rfl)))
  · exact triP_congr hcg (h _ k' (hcov k' hle (Int.le_refl k') (Or.inr rfl)))

-- ============================================================
-- With the reader: only the starting states matter
-- ============================================================

variable (φ : Cnf)

/-- **Along the reader, `PrefixTri` at the start is enough.** -/
theorem prefixTri_reader (hbd : Bounded φ) (kv : NodeId × GPathM) (hkv : kv ∈ pureRun φ)
    (h0 : isValid (filterAll kv.2 []) = true → PrefixTri (filterAll kv.2 [])) :
    ∀ ps g, ReadPins (filterAll kv.2 []) ps g → isValid g = true → PrefixTri g := by
  intro ps g hp
  induction hp with
  | start => exact h0
  | pin g k q ps hp hv hf hq hv' ih =>
    intro _
    have c := aCtx_readPins φ hbd kv hkv ps g hp hv
    have hk' := KernelReader.kernel_readPins φ hbd kv hkv (q.id :: ps) _
      (ReadPins.pin g k q ps hp hv hf hq hv') hv'
    exact prefixTri_pin c (prefixUpTo_firstChoice g k hf) hv q hq hk' (ih hv)

/-- **The reader decides `φ` when every valid starting state satisfies `PrefixTri`.** -/
theorem readerVerdictW_iff_of_prefixTri (hbd : Bounded φ)
    (h0 : ∀ kv ∈ pureRun φ, isValid (filterAll kv.2 []) = true → PrefixTri (filterAll kv.2 [])) :
    readerVerdictW φ = true ↔ Satisfiable φ := by
  refine readerVerdictW_iff_of_triPin₁ φ hbd (fun kv hkv g hF hv k hf => ?_)
  obtain ⟨ps, hp⟩ := OtherBitSem.readPins_of_readFirst _ g hF
  have c := aCtx_readPins φ hbd kv hkv ps g hp hv
  obtain ⟨q, hq⟩ := exists_owner_of_choiceAt g k (choiceAt_of_firstChoice g k hf)
  exact ⟨q, hq, triPin₁_of_prefixTri c (prefixUpTo_firstChoice g k hf) hv q hq
    (prefixTri_reader φ hbd kv hkv (h0 kv hkv) ps g hp hv)⟩

/-- info: 'AbsSatBin.GraphPath.Model.PrefixTri.prefixTri_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prefixTri_pin

/-- info: 'AbsSatBin.GraphPath.Model.PrefixTri.readerVerdictW_iff_of_prefixTri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readerVerdictW_iff_of_prefixTri

end AbsSatBin.GraphPath.Model.PrefixTri
