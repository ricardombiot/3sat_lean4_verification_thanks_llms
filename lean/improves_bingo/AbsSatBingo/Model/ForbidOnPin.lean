-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnPin.lean
import AbsSatBingo.Model.ForbidOnFix
import AbsSatBingo.Model.LivePin
import AbsSatBingo.Model.KernelUp

/-!
# La llegada fijada con la regla activa: la dirección 2

`pinOn g R`: fijar `R` y revisar con la regla (espejo `:on` de `pinF`; con `R = []` es `reviewAllOn`).

**Dirección 2** (`liveChain_down`): sea `E` un remitente, `A = upOn (filterAllOn E reqs) d` su llegada y
`h = pinOn A R` la llegada fijada. Toda cadena viva de `h` (con sus tríos), sin su cima, es cadena viva de la entrada
fijada `X = pinOn E (reqs ++ R)` (con los suyos). La parte baja de `h` es una estructura cerrada que baja al
remitente y sobrevive al filtro; el review con la regla de `X` la conserva y no prohíbe ninguno de sus triángulos que
`h` no prohíba (`downInv_reviewOn`), porque `h` salió en el punto fijo de la regla (`trioGood_low`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- Fijar `R` y revisar con la regla (espejo `:on` de `pinF`). -/
def pinOn (g : GPathB) (R : List NodeId) : GPathB := reviewOn { R.foldl filterRequire g with dirty := true }

-- ============================================================
-- Contabilidad por las operaciones `:on`
-- ============================================================

theorem sInvB_reviewOn {g : GPathB} (h : SInvB g) : SInvB g.reviewOn :=
  ⟨revPrims_reviewOn revPrims_linksInv trioBlind_linksInv _ h.links,
   revPrims_reviewOn revPrims_nodupIds trioBlind_nodupIds _ h.nodup,
   revPrims_reviewOn revPrims_below trioBlind_below _ h.below,
   revPrims_reviewOn revPrims_aboveZero trioBlind_aboveZero _ h.zero,
   revPrims_reviewOn revPrims_linksStep trioBlind_linksStep _ h.lstep,
   revPrims_reviewOn revPrims_edgesAlive trioBlind_edgesAlive _ h.edges,
   rootNone_of_sub (shrinks_reviewOn g).1 h.root⟩

theorem sInvB_setT {g : GPathB} (h : SInvB g) (T : List (PathNodeId × PathNodeId × PathNodeId)) : SInvB (g.setT T) :=
  ⟨h.links, h.nodup, h.below, h.zero, h.lstep, h.edges, h.root⟩

theorem sInvB_foldlF {g : GPathB} (h : SInvB g) (R : List NodeId) : SInvB (R.foldl filterRequire g) := sInvB_foldl h R

theorem sInvB_pinOn {g : GPathB} (h : SInvB g) (R : List NodeId) : SInvB (g.pinOn R) :=
  sInvB_reviewOn (sInvB_dirty (sInvB_foldl h R) true)

theorem sInvB_filterAllOn {g : GPathB} (h : SInvB g) (R : List NodeId) : SInvB (g.filterAllOn R) :=
  sInvB_reviewOn (sInvB_foldl h R)

theorem sInvB_upOn {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool} (h : SInvB g)
    (hd : d.step = g.current_step) (hd0 : 0 ≤ d.step) : SInvB (g.upOn d title forb) := by
  unfold upOn
  split
  · obtain ⟨T', hT⟩ := upForbidRow_eq ((g.addNode d title forb).setT g.trios) (g.newRowIds d forb)
    rw [hT]
    exact sInvB_reviewOn (sInvB_setT (sInvB_setT (sInvB_addNode h hd hd0) g.trios) T')
  · exact h

-- ============================================================
-- Los tríos crecen por el filtro, el UP y el pin
-- ============================================================

theorem trios_grow_foldlF (R : List NodeId) (g : GPathB) : ∀ t ∈ g.trios, t ∈ (R.foldl filterRequire g).trios := by
  intro t ht; rw [trios_foldl_filterRequire]; exact ht

theorem trios_grow_filterAllOn (g : GPathB) (R : List NodeId) : ∀ t ∈ g.trios, t ∈ (g.filterAllOn R).trios :=
  fun t ht => trios_grow_reviewOn _ t (trios_grow_foldlF R g t ht)

theorem trios_grow_pinOn (g : GPathB) (R : List NodeId) : ∀ t ∈ g.trios, t ∈ (g.pinOn R).trios :=
  fun t ht => trios_grow_reviewOn _ t (trios_grow_foldlF R g t ht)

theorem trios_grow_upOn (g : GPathB) (d : NodeId) (title : String) (forb : PathNodeId → Bool) :
    ∀ t ∈ g.trios, t ∈ (g.upOn d title forb).trios := by
  intro t ht
  unfold upOn
  split
  · apply trios_grow_reviewOn
    unfold upForbidRow addTrios
    exact List.mem_append_left _ ht
  · exact ht

theorem sub_upOn_addNode {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}
    (hv : g.isValid = true) : Sub (g.upOn d title forb) (g.addNode d title forb) := by
  obtain ⟨T', hT⟩ := upOn_eq (d := d) (title := title) (forb := forb) hv
  rw [hT]
  exact (shrinks_reviewOn _).1.trans (shrinks_setT _ T').1

theorem sub_pinOn (g : GPathB) (R : List NodeId) : Sub (g.pinOn R) g :=
  (shrinks_reviewOn _).1.trans ((shrinks_dirty _ true).1.trans (shrinks_foldl filterRequire shrinks_filterRequire R g).1)

theorem step_pinOn (g : GPathB) (R : List NodeId) : (g.pinOn R).current_step = g.current_step := (sub_pinOn g R).step

/-- **El pin `:on` fija los pasos de sus requisitos.** -/
theorem pinned_pinOn {g : GPathB} (hd : AliveDocs g) {R : List NodeId} (hv : (g.pinOn R).isValid = true) :
    ∀ b ∈ R, ∀ q ∈ (g.pinOn R).alive, q.id.step = b.step → q.id = b := by
  have hs1 : Sub (g.pinOn R) (R.foldl filterRequire g) := (shrinks_reviewOn _).1.trans (shrinks_dirty _ true).1
  have hv1 : (R.foldl filterRequire g).isValid = true := isValid_of_sub hs1 hv
  intro b hb q hq hqs
  exact pinned_foldl R g hd hv1 q (hs1.alive q hq) hb hqs

-- ============================================================
-- NoSelf y NoDegT por el filtro, el UP y el pin
-- ============================================================

theorem noSelf_foldlF (R : List NodeId) {g : GPathB} (h : NoSelf g) : NoSelf (R.foldl filterRequire g) :=
  foldl_filterRequire_pres revPrims_noSelf R g h

theorem noSelf_pinOn {g : GPathB} (h : NoSelf g) (R : List NodeId) : NoSelf (g.pinOn R) :=
  revPrims_reviewOn revPrims_noSelf trioBlind_noSelf _ (noSelf_foldlF R h)

theorem noDegT_foldlF (R : List NodeId) {g : GPathB} (h : NoDegT g) : NoDegT (R.foldl filterRequire g) :=
  noDegT_of_trios (trios_foldl_filterRequire R g) h

theorem noDegT_filterAllOn {g : GPathB} (hns : NoSelf g) (h : NoDegT g) (R : List NodeId) :
    NoDegT (g.filterAllOn R) :=
  noDegT_reviewOn (noSelf_foldlF R hns) (noDegT_foldlF R h)

theorem noDegT_pinOn {g : GPathB} (hns : NoSelf g) (h : NoDegT g) (R : List NodeId) : NoDegT (g.pinOn R) :=
  noDegT_reviewOn (noSelf_foldlF R hns) (noDegT_foldlF R h)

theorem noDegT_upOn {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool} (hns : NoSelf g)
    (h : NoDegT g) : NoDegT (g.upOn d title forb) := by
  unfold upOn
  split
  · have hns' : NoSelf ((g.addNode d title forb).setT g.trios) := noSelf_addNode (title := title) hns
    have hup := noDegT_upForbidRow hns' h
    obtain ⟨T', hT⟩ := upForbidRow_eq ((g.addNode d title forb).setT g.trios) (g.newRowIds d forb)
    exact noDegT_reviewOn (by rw [hT]; exact hns') hup
  · exact h

-- ============================================================
-- La dirección 2
-- ============================================================

section Down

variable {E : GPathB} {reqs R : List NodeId} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

theorem valid_of_upOn {Y : GPathB} (hv : (Y.upOn d title forb).isValid = true) : Y.isValid = true := by
  unfold upOn at hv; split at hv
  · assumption
  · exact hv

/-- **Dirección 2**: una cadena viva de la llegada fijada, sin su cima, es cadena viva de la entrada fijada. -/
theorem liveChain_down (hE : SInvB E) (hns : NoSelf E) (hndt : NoDegT E) (hlen : reqs.length ≤ 1)
    (hd : d.step = E.current_step) (hpos : 1 ≤ E.current_step)
    (hvh : (((E.filterAllOn reqs).upOn d title forb).pinOn R).isValid = true)
    {C : Int → PathNodeId} {j : Int}
    (hC : LiveChain (((E.filterAllOn reqs).upOn d title forb).pinOn R)
      (TF (((E.filterAllOn reqs).upOn d title forb).pinOn R)) C j) :
    LiveChain (E.pinOn (reqs ++ R)) (TF (E.pinOn (reqs ++ R))) C j := by
  -- los estados
  let Y := E.filterAllOn reqs
  let A := Y.upOn d title forb
  let h := A.pinOn R
  let X := E.pinOn (reqs ++ R)
  let c := E.current_step
  have hcsY : Y.current_step = c := step_filterAllOn E reqs
  have hvA : A.isValid = true := isValid_of_sub (sub_pinOn A R) hvh
  have hvY : Y.isValid = true := valid_of_upOn hvA
  have hdY : d.step = Y.current_step := by rw [hcsY]; exact hd
  have hiY : SInvB Y := sInvB_filterAllOn hE reqs
  have hiA : SInvB A := sInvB_upOn hiY hdY (by omega)
  have hcsA : A.current_step = c + 1 := by
    rw [(sub_upOn_addNode hvY).step]; show Y.current_step + 1 = _; rw [hcsY]
  have hcsh : h.current_step = c + 1 := (step_pinOn A R).trans hcsA
  have hcsX : X.current_step = c := step_pinOn E _
  -- la llegada fijada está cerrada y en el punto fijo de la regla
  have hiAf := sInvB_dirty (sInvB_foldl hiA R) true
  have hcl : ClosedState h := closedState_reviewOn (g := { R.foldl filterRequire A with dirty := true }) rfl hvh
    hiAf.docs hiAf.nodup hiAf.below hiAf.zero (by
      show 2 ≤ (R.foldl filterRequire A).current_step
      rw [(shrinks_foldl filterRequire shrinks_filterRequire R A).1.step, hcsA]; omega)
  have hfix : FixClosed h := fixClosed_reviewOn (g := { R.foldl filterRequire A with dirty := true }) rfl hvh
  have hnsA : NoSelf A := noSelf_upOn (noSelf_filterAllOn hns reqs)
  have hndtA : NoDegT A := noDegT_upOn (noSelf_filterAllOn hns reqs) (noDegT_filterAllOn hns hndt reqs)
  have hndth : NoDegT h := noDegT_pinOn hnsA hndtA R
  -- la parte baja de la llegada fijada baja al remitente
  have hsubh : Sub h (Y.addNode d title forb) := (sub_pinOn A R).trans (sub_upOn_addNode hvY)
  have hiYa : SInvB (Y.addNode d title forb) := sInvB_addNode hiY hdY (by omega)
  have hU := secStruct_of_sub hsubh hiYa.nodup hcl
  have hdown := secStruct_addNode_down hiY.docs hiY.below hiY.lstep hdY hU
  have hLow : SecStruct Y (LowV h c) (LowR h c) := by
    unfold LowV LowR; rw [← hcsY]; exact hdown
  have hLowE : SecStruct E (LowV h c) (LowR h c) := secStruct_of_sub (shrinks_filterAllOn E reqs).1 hE.nodup hLow
  -- los tríos crecen del remitente a la llegada fijada
  have hgrow : ∀ t ∈ E.trios, t ∈ h.trios := fun t ht =>
    trios_grow_pinOn A R t (trios_grow_upOn Y d title forb t (trios_grow_filterAllOn E reqs t ht))
  have hsymm : ∀ {y w}, LowR h c y w → LowR h c w y :=
    fun hr => ⟨⟨hr.1.2.1, hr.1.1, (adj_symm h _ _).mp hr.1.2.2⟩, hr.2.2, hr.2.1⟩
  -- el invariante en el remitente
  have h0 : DownInv (LowV h c) (LowR h c) (TF h) c E :=
    ⟨hLowE, hns, rfl, fun hab _ _ hf => tF_mono hgrow hab.1.2.2 hf⟩
  -- los pins: la parte baja los cumple
  have hagree : ∀ p ∈ reqs ++ R, SecAgrees (LowV h c) p := by
    intro p hp q ⟨hq, hqc⟩ hqs
    rcases List.mem_append.mp hp with hp | hp
    · rcases alive_addNode_cases hiY.docs hiY.below hdY (hsubh.alive q hq) with ⟨hqY, _⟩ | ⟨_, h2⟩
      · exact filtered_filterAllOn hE.docs reqs hlen hvY q hqY p hp hqs
      · rw [hcsY] at h2; omega
    · exact pinned_pinOn hiA.docs hvh p hp q hq hqs
  have hfold : ∀ (l : List NodeId) (x : GPathB), (∀ p ∈ l, SecAgrees (LowV h c) p) →
      DownInv (LowV h c) (LowR h c) (TF h) c x → DownInv (LowV h c) (LowR h c) (TF h) c (l.foldl filterRequire x) := by
    intro l
    induction l with
    | nil => intro x _ hx; exact hx
    | cons p ps ih =>
      intro x hl hx
      rw [List.foldl_cons]
      exact ih _ (fun p' hp' => hl p' (List.mem_cons_of_mem _ hp')) (downInv_filterRequire hx (hl p List.mem_cons_self))
  have h1 := hfold _ E hagree h0
  have h2 : DownInv (LowV h c) (LowR h c) (TF h) c { (reqs ++ R).foldl filterRequire E with dirty := true } :=
    downInv_shrink h1 (shrinks_dirty _ true).1 rfl (sec_dirty h1.sec true) h1.ns
  have hTG : TrioGood (LowV h c) (LowR h c) (TF h) c := trioGood_low hfix hndth (by rw [hcsh]; omega)
  have hX : DownInv (LowV h c) (LowR h c) (TF h) c X := downInv_reviewOn h2 hTG hsymm
  -- la cadena
  have hliX : LinksInv X := (sInvB_pinOn hE _).links
  have hlih : LinksInv h := (sInvB_pinOn hiA R).links
  have hlow : ∀ k, j ≤ k → k ≤ c - 1 → LowV h c (C k) := fun k h1 h2 =>
    ⟨(hC.chain.node k h1 (by rw [hcsh]; omega)).2, by rw [(hC.chain.node k h1 (by rw [hcsh]; omega)).1]; omega⟩
  have hlowR : ∀ k l, j ≤ k → k ≤ c - 1 → j ≤ l → l ≤ c - 1 → LowR h c (C k) (C l) := fun k l h1 h2 h3 h4 =>
    ⟨⟨(hlow k h1 h2).1, (hlow l h3 h4).1, hC.chain.adj k l h1 (by rw [hcsh]; omega) h3 (by rw [hcsh]; omega)⟩,
      (hlow k h1 h2).2, (hlow l h3 h4).2⟩
  refine ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩, fun a b c' ha hab hbc hc hs => ?_⟩
  · rw [hcsX] at h2
    exact ⟨(hC.chain.node k h1 (by rw [hcsh]; omega)).1, hX.sec.alive (hlow k h1 h2)⟩
  · rw [hcsX] at h2 h4
    exact hX.sec.adj (hlowR k l h1 h2 h3 h4)
  · rw [hcsX] at h2
    have hk := hlow k (by omega) h2
    have hk1 := hlow (k - 1) (by omega) (by omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hliX.1 (hX.sec.alive hk))
    refine ⟨n, hn, ?_⟩
    -- el enlace en la llegada fijada da la compatibilidad; en `X` la completitud de los enlaces da el padre
    obtain ⟨m, hm, hpm⟩ := hC.chain.link k h1 (by rw [hcsh]; omega)
    have hcomp := (hlih.2.2 m (node?_mem hm)).1 _ hpm
    rw [node?_id hm] at hcomp
    have hadj : X.Adj n.id (C (k - 1)) := by
      rw [node?_id hn]; exact hX.sec.adj (hlowR k (k - 1) (by omega) h2 (by omega) (by omega))
    exact (hliX.2.1 n (node?_mem hn) (C (k - 1)) (hX.sec.alive hk1) hadj).1 (by rw [node?_id hn]; exact hcomp)
  · rw [hcsX] at hc
    apply hC.live a b c' ha hab hbc (by rw [hcsh]; omega)
    have ab := hlowR a b ha (by omega) (by omega) (by omega)
    have ac := hlowR a c' ha (by omega) (by omega) hc
    have bc := hlowR b c' (by omega) (by omega) (by omega) hc
    have tri := fun {x y z} (hxy : LowR h c x y) (hxz : LowR h c x z) (hyz : LowR h c y z)
      (hf : TF X x y z) => hX.tri hxy hxz hyz hf
    unfold Sym at hs ⊢
    rcases hs with hf | hf | hf | hf | hf | hf
    · exact Or.inl (tri ab ac bc hf)
    · exact Or.inr (Or.inl (tri ac ab (hsymm bc) hf))
    · exact Or.inr (Or.inr (Or.inl (tri (hsymm ab) bc ac hf)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (tri bc (hsymm ab) (hsymm ac) hf))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (tri (hsymm ac) (hsymm bc) ab hf)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (tri (hsymm bc) (hsymm ac) (hsymm ab) hf)))))

end Down

end GPathB

end AbsSatBingo.Model
