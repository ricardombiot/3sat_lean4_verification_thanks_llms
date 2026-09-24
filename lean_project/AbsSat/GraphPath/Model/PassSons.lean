-- lean_project/AbsSat/GraphPath/Model/PassSons.lean
import AbsSat.GraphPath.Model.PassCtx

/-!
# La pasada de hijos, nodo a nodo: el espejo

Lo mismo que `PassCtx` para la pasada de padres, con los hijos como vecinos: la tabla de cada nodo se
corta por la unión de las de sus hijos, de arriba abajo. El hijo vivo `s` de `x` alarga el tramo
`[x]` hacia arriba, a `[x, s]`, y sus entradas comunes sobreviven al corte.
-/

namespace AbsSat.GraphPath.Model.PassSons

open AbsSat.Utils.Alias
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.NodeIds (Ids ids_updateAt ids_unlinkIncompatible)
open AbsSat.GraphPath.Model.Extendable (upd upd_self upd_other)
open AbsSat.GraphPath.Model.PassCtx

/-- **La validez, desde sus piezas, raíz o no.** -/
theorem isValidNode_of' (h : GPathM) (n : PNodeM)
    (hok : ∀ k, 0 ≤ k → k ≤ h.current_step - 1 → ∃ q ∈ n.owners, q.id.step = k)
    (hpar : n.id.parent_id.isNone = false → n.parents ≠ [])
    (hsons : n.id.id.step ≠ h.current_step - 1 → n.sons ≠ []) : isValidNode h n = true := by
  cases hroot : n.id.parent_id.isNone with
  | false => exact isValidNode_of h n hok hroot (hpar hroot) hsons
  | true =>
    have hok' : (intRange 0 (h.current_step - 1)).all (fun k => hasStepEntry n.owners k) = true := by
      refine List.all_eq_true.mpr (fun k hk => ?_)
      obtain ⟨q, hq, hqs⟩ := hok k (mem_intRange_lower hk) (mem_intRange_upper hk)
      exact List.any_eq_true.mpr ⟨q, hq, beq_iff_eq.mpr hqs⟩
    unfold isValidNode
    dsimp only
    rw [hroot, if_pos rfl, hok']
    cases hl : (n.id.id.step == h.current_step - 1) with
    | true => rfl
    | false =>
      have hne : n.id.id.step ≠ h.current_step - 1 := fun e => by
        rw [beq_iff_eq.mpr e] at hl; exact Bool.noConfusion hl
      have hs : (!n.sons.isEmpty) = true := by
        cases hq : n.sons with
        | nil => exact absurd hq (hsons hne)
        | cons _ _ => rfl
      rw [hs]; rfl

/-- **La pasada de hijos no elimina el nodo que procesa.** -/
theorem kept_reviewNode_sons (g : GPathM) (hsgl : SegGoodL g) (hI1 : I1L g) (hI1s : I1sL g)
    (hself : SelfL g) (hlsymU : SegReview.LocSymUp g) (hrootz : Sons.RootAtZero g)
    (x : PathNodeId) (d : PNodeM) (hd : g.node? x = some d)
    (hx0 : 0 ≤ x.id.step) (hxl : x.id.step ≤ g.current_step - 2) :
    ((reviewNode g (·.sons) x).node? x).isSome := by
  have hdid : d.id = x := node?_id_eq g x d hd
  have hdm : d ∈ g.nodes := List.mem_of_find?_eq_some hd
  have hs1 := seg_single g x d hd
  have hxl' : x.id.step ≤ g.current_step - 1 := by omega
  -- un hijo vivo `s` en la tabla de `x`
  obtain ⟨s, hss, hsl, hsu⟩ := hsgl (fun _ => x) x.id.step x.id.step hx0 (Int.le_refl _) hxl'
    hs1.1 hs1.2 (x.id.step + 1) (by omega) (by omega) (Or.inr (by omega))
  have hsd : s ∈ d.owners := hsu x.id.step (Int.le_refl _) (Int.le_refl _) d hd
  have hson : s ∈ d.sons := hI1s x d hd s hsd hsl hss
  obtain ⟨ns, hns⟩ := Option.isSome_iff_exists.mp hsl
  have hxs : x ∈ ns.owners := hlsymU (fun _ => x) x.id.step x.id.step (Int.le_refl _) hs1 s ns hns
    hss hsu x.id.step (Int.le_refl _) (Int.le_refl _)
  have hxl0 : (g.node? x).isSome := by rw [hd]; rfl
  have hxp : x ∈ ns.parents := hI1 s ns hns x hxs hxl0 (by omega)
  -- el tramo `[x, s]`
  have hs2 := SegReview.seg_extend_up g (fun _ => x) x.id.step x.id.step (Int.le_refl _) hs1 s ns
    hns hss hxp hsu (fun _ _ _ => hxs)
  have hsel_x : upd (fun _ => x) (x.id.step + 1) s x.id.step = x := upd_other _ _ _ (by omega)
  have hsel_s : upd (fun _ => x) (x.id.step + 1) s (x.id.step + 1) = s := upd_self _ _ _
  have common : ∀ k, 0 ≤ k → k ≤ g.current_step - 1 → k ≠ x.id.step → k ≠ x.id.step + 1 →
      ∃ r, r.id.step = k ∧ (g.node? r).isSome ∧ r ∈ ns.owners ∧ r ∈ d.owners := by
    intro k hk0 hk1 hkne hkne'
    obtain ⟨r, hrs, hrl, hr⟩ := hsgl _ x.id.step (x.id.step + 1) hx0 (by omega) (by omega)
      hs2.1 hs2.2 k hk0 hk1 (by omega)
    refine ⟨r, hrs, hrl, ?_, ?_⟩
    · exact hr (x.id.step + 1) (by omega) (Int.le_refl _) ns (by rw [hsel_s]; exact hns)
    · exact hr x.id.step (Int.le_refl _) (by omega) d (by rw [hsel_x]; exact hd)
  let T' := intersectOwners d.owners (unionOwnersOf g d.sons)
  have inT' : ∀ r, r ∈ d.owners → r ∈ ns.owners → r ∈ T' :=
    fun r hr hrn => SegReview.mem_intersect_of_nb g d d.sons r hr s hson ns hns hrn
  have hT'sub : ∀ r, r ∈ T' → r ∈ d.owners := fun r hr => (List.mem_filter.mp hr).1
  have hokT : ∀ k, 0 ≤ k → k ≤ g.current_step - 1 → ∃ q ∈ T', q.id.step = k := by
    intro k hk0 hk1
    rcases int_eq_or_ne k x.id.step with he | he
    · exact ⟨x, inT' x (hself x d hd) hxs, he.symm⟩
    · rcases int_eq_or_ne k (x.id.step + 1) with he' | he'
      · exact ⟨s, inT' s hsd (hself s ns hns), by rw [hss, he']⟩
      · obtain ⟨r, hrs, _, hrn, hrd⟩ := common k hk0 hk1 he he'
        exact ⟨r, inT' r hrd hrn, hrs⟩
  -- un padre que queda, si no es raíz
  have hpar : d.id.parent_id.isNone = false → ∃ u ∈ d.parents, u ∈ T' := by
    intro hnr
    have hx1 : 1 ≤ x.id.step := by
      rcases int_eq_or_ne x.id.step 0 with h0 | h0
      · have := hrootz d hdm (by rw [hdid]; exact h0)
        rw [this] at hnr; exact absurd hnr (by decide)
      · omega
    obtain ⟨u, hus, hul, hun, hud⟩ := common (x.id.step - 1) (by omega) (by omega) (by omega)
      (by omega)
    exact ⟨u, hI1 x d hd u hud hul (by omega), inT' u hud hun⟩
  have hvd : isValidNode g d = true := by
    refine isValidNode_of' g d (fun k hk0 hk1 => ?_) (fun hnr => ?_) (fun _ => List.ne_nil_of_mem hson)
    · obtain ⟨q, hq, hqs⟩ := hokT k hk0 hk1
      exact ⟨q, hT'sub q hq, hqs⟩
    · obtain ⟨u, hu, _⟩ := hpar hnr
      exact List.ne_nil_of_mem hu
  have hcs : (unlinkIncompatible (mirrorDrop (updateAt g x
      (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g d.sons) })) x (cutRemoved d (unionOwnersOf g d.sons))) x
      ).current_step = g.current_step := PinAliveChain.current_step_unlinkIncompatible _ x
  have hvd' : isValidNode (unlinkIncompatible (mirrorDrop (updateAt g x
      (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g d.sons) })) x (cutRemoved d (unionOwnersOf g d.sons))) x)
      (relink T' d) = true := by
    refine isValidNode_of' _ _ (fun k hk0 hk1 => ?_) (fun hnr => ?_) (fun _ => ?_)
    · rw [hcs] at hk1; exact hokT k hk0 hk1
    · obtain ⟨u, hu, huT⟩ := hpar hnr
      exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hu, List.elem_iff.mpr huT⟩)
    · exact List.ne_nil_of_mem
        (List.mem_filter.mpr ⟨hson, List.elem_iff.mpr (inT' s hsd (hself s ns hns))⟩)
  have hxin : x ∈ Ids g := mem_ids_of_node g x (by rw [hd]; rfl)
  unfold reviewNode
  rw [hd]
  simp only [hvd, ↓reduceIte]
  rw [if_pos hvd']
  apply node_of_mem_ids
  rw [ids_unlinkIncompatible, NodeIds.ids_mirrorDrop,
    ids_updateAt g x (fun n => { n with owners := intersectOwners n.owners (unionOwnersOf g d.sons) })
      (fun _ => rfl)]
  exact hxin

/-- info: 'AbsSat.GraphPath.Model.PassSons.kept_reviewNode_sons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kept_reviewNode_sons

theorem live_reviewNode_sons (g : GPathM) (hsgl : SegGoodL g) (hI1 : I1L g) (hI1s : I1sL g)
    (hself : SelfL g) (hlsymU : SegReview.LocSymUp g) (hrootz : Sons.RootAtZero g)
    (x : PathNodeId) (hx0 : 0 ≤ x.id.step) (hxl : x.id.step ≤ g.current_step - 2)
    (r : PathNodeId) (hr : (g.node? r).isSome) :
    ((reviewNode g (·.sons) x).node? r).isSome := by
  if hrx : r = x then
    subst hrx
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hr
    exact kept_reviewNode_sons g hsgl hI1 hI1s hself hlsymU hrootz r d hd hx0 hxl
  else
    exact survives_reviewNode g (·.sons) x r hr hrx

/-- **`reviewNode x`, con los hijos como vecinos, conserva `SegGoodL`** (review simétrico): el
argumento de `PassCtx.segGoodL_reviewNode_parents` con el hijo de `x` en la cadena completa `Q`, que
`I1sL` saca de la posesión por pares. -/
theorem segGoodL_reviewNode_sons (g : GPathM) (hnd : NodupIds g) (hI1 : I1L g) (hI1s : I1sL g)
    (hplive : PLive g) (hslive : SLive g) (hself : SelfL g) (hlsym : SegReview.LocSym g)
    (hlsymU : SegReview.LocSymUp g)
    (hrootz : Sons.RootAtZero g) (hseg : SegGoodL g) (x : PathNodeId) (hx0 : 0 ≤ x.id.step)
    (hxl : x.id.step ≤ g.current_step - 2) :
    SegGoodL (reviewNode g (·.sons) x) := by
  have hpr := pruned_reviewNode (·.sons) x g
  have live := live_reviewNode_sons g hseg hI1 hI1s hself hlsymU hrootz x hx0 hxl
  have lift : ∀ y n', (reviewNode g (·.sons) x).node? y = some n' →
      ∃ n, g.node? y = some n ∧ (∀ q ∈ n'.owners, q ∈ n.owners) ∧ (∀ p ∈ n'.parents, p ∈ n.parents) := by
    intro y n' h
    obtain ⟨n0, hn0, hid0, hown0, hpar0⟩ := hpr.nodes_derived n' (List.mem_of_find?_eq_some h)
    have hy : n'.id = y := node?_id_eq _ y n' h
    exact ⟨n0, by rw [← hy, hid0]; exact node?_of_mem hnd n0 hn0, hown0, hpar0⟩
  intro sel lo hi hlo0 hlohi hhi hch' hpw' i hi0 hic hout
  rw [hpr.step_eq] at hhi hic
  have hsG : TopGoodUp.Seg g sel lo hi := by
    refine ⟨⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_⟩, fun a b ha1 hb1 ha2 hb2 hab nb hnb => ?_⟩
    · obtain ⟨hs, hjs⟩ := hch'.1 j hj1 hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _⟩ := lift _ m hm
      exact ⟨by rw [hn]; rfl, hjs⟩
    · obtain ⟨hs, _⟩ := hch'.1 (j + 1) (by omega) hj2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, _, hpar⟩ := lift _ m hm
      have hl := hch'.2 j hj1 hj2
      rw [hm] at hl
      rw [hn]
      simp only [Option.map_some, Option.getD_some] at hl ⊢
      exact hpar _ hl
    · obtain ⟨hs, _⟩ := hch'.1 b hb1 hb2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, hn, hown, _⟩ := lift _ m hm
      rw [← Option.some.inj (hn.symm.trans hnb)]
      exact hown _ (hpw' a b ha1 hb1 ha2 hb2 hab m hm)
  obtain ⟨Q, hQ, hQag⟩ := seg_full_L g hseg hI1 hI1s hplive hslive hlsym hlsymU sel lo hi hlo0 hlohi
    hhi hsG
  have hQnode : ∀ k, 0 ≤ k → k ≤ g.current_step - 1 → ∃ nk, g.node? (Q k) = some nk :=
    fun k hk0 hk1 => Option.isSome_iff_exists.mp (hQ.1.1 k hk0 hk1).1
  have hQown : ∀ a b, 0 ≤ a → 0 ≤ b → a ≤ g.current_step - 1 → b ≤ g.current_step - 1 →
      ∀ nb, g.node? (Q b) = some nb → Q a ∈ nb.owners := by
    intro a b ha hb ha' hb' nb hnb
    rcases int_eq_or_ne a b with hab | hab
    · subst hab; exact hself _ nb hnb
    · exact hQ.2 a b ha hb ha' hb' hab nb hnb
  have hQson : ∀ k, 0 ≤ k → k + 1 ≤ g.current_step - 1 → ∀ nk, g.node? (Q k) = some nk →
      Q (k + 1) ∈ nk.sons := by
    intro k hk0 hk1 nk hnk
    have hks : (Q k).id.step = k := (hQ.1.1 k hk0 (by omega)).2
    have hk1s : (Q (k + 1)).id.step = k + 1 := (hQ.1.1 (k + 1) (by omega) hk1).2
    exact hI1s _ nk hnk _ (hQown (k + 1) k (by omega) hk0 hk1 (by omega) nk hnk)
      (hQ.1.1 (k + 1) (by omega) hk1).1 (by rw [hk1s, hks])
  refine ⟨Q i, (hQ.1.1 i hi0 hic).2, live (Q i) (hQ.1.1 i hi0 hic).1, fun j hj1 hj2 nj' hnj' => ?_⟩
  obtain ⟨n, hn, hne, heq⟩ := SegReview.reviewNode_owners g hnd (·.sons) x (sel j) nj' hnj'
  have hQj : Q j = sel j := hQag j hj1 hj2
  have hjs : (sel j).id.step = j := (hsG.1.1 j hj1 hj2).2
  have hnQ : g.node? (Q j) = some n := by rw [hQj]; exact hn
  have hci : Q i ∈ n.owners := hQown i j hi0 (by omega) hic (by omega) n hnQ
  if hjx : sel j = x then
    rw [heq hjx]
    have hj2' : j + 1 ≤ g.current_step - 1 := by rw [← hjs, hjx]; omega
    obtain ⟨ns, hns⟩ := hQnode (j + 1) (by omega) hj2'
    exact SegReview.mem_intersect_of_nb g n n.sons (Q i) hci (Q (j + 1)) (hQson j (by omega) hj2' n hnQ)
      ns hns (hQown i (j + 1) hi0 (by omega) hic hj2' ns hns)
  else
    obtain ⟨_, hkeep, hmk⟩ := hne hjx
    if hcx : Q i = x then
      rw [hmk (fun dx hdx hin => ?_)]
      · exact hci
      · have hdx' : g.node? (Q i) = some dx := by rw [hcx]; exact hdx
        have hi2 : i + 1 ≤ g.current_step - 1 := by rw [← (hQ.1.1 i hi0 hic).2, hcx]; omega
        obtain ⟨ns, hns⟩ := hQnode (i + 1) (by omega) hi2
        exact SegReview.mem_intersect_of_nb g dx dx.sons (sel j) hin (Q (i + 1)) (hQson i hi0 hi2 dx hdx')
          ns hns (by rw [← hQj]; exact hQown j (i + 1) (by omega) (by omega) (by omega) hi2 ns hns)
    else
      exact hkeep _ hci hcx

/-- info: 'AbsSat.GraphPath.Model.PassSons.segGoodL_reviewNode_sons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms segGoodL_reviewNode_sons

/-- **La pasada de hijos conserva `I1L`.** Caso con contenido: `x` padre de un `y` vivo que lo tiene
en su tabla. `LocSym` en `[y]` pone a `y` en la tabla de `x`; `y` es hijo de `x` (`I1sL`) y se
posee, así que queda en el corte. -/
theorem i1L_reviewNode_sons (g : GPathM) (hnd : NodupIds g) (hsgl : SegGoodL g) (hI1 : I1L g)
    (hI1s : I1sL g) (hself : SelfL g) (hlsym : SegReview.LocSym g) (hlsymU : SegReview.LocSymUp g)
    (hrootz : Sons.RootAtZero g) (x : PathNodeId) (hx0 : 0 ≤ x.id.step)
    (hxl : x.id.step ≤ g.current_step - 2) :
    I1L (reviewNode g (·.sons) x) := by
  have hsub := NodeIds.ids_reviewNode g (·.sons) x
  have liveG : ∀ w, ((reviewNode g (·.sons) x).node? w).isSome → (g.node? w).isSome :=
    fun w h => node_of_mem_ids g w (hsub.subset (mem_ids_of_node _ w h))
  intro y ny hy w hw hwl hws
  cases hd : g.node? x with
  | none =>
    have hR : reviewNode g (·.sons) x = g := by unfold reviewNode; rw [hd]
    rw [hR] at hy hwl
    exact hI1 y ny hy w hw hwl hws
  | some d =>
    have hk := kept_reviewNode_sons g hsgl hI1 hI1s hself hlsymU hrootz x d hd hx0 hxl
    obtain ⟨n, hn, _, _⟩ := SegReview.reviewNode_owners g hnd (·.sons) x y ny hy
    have hform := node_after g (·.sons) x d hd hk y n hn
    rw [hy] at hform
    have hny := Option.some.inj hform
    have hwlg := liveG w hwl
    if hyx : y = x then
      subst hyx
      rw [if_pos rfl, PinAliveChain.unlinkMap_self
        { d with owners := intersectOwners d.owners (unionOwnersOf g d.sons) } y
        (node?_id_eq g y d hd)] at hny
      rw [hny] at hw ⊢
      have hwd : w ∈ d.owners := (List.mem_filter.mp hw).1
      exact List.mem_filter.mpr ⟨hI1 y d hd w hwd hwlg hws, List.elem_iff.mpr hw⟩
    else
      rw [if_neg hyx] at hny
      have hnid : n.id = y := node?_id_eq g y n hn
      have hwn : w ∈ n.owners := by
        rw [hny, PinAliveChain.owners_unlinkMap] at hw; exact mirrorMap_owners_sub _ _ n w hw
      have hwp := hI1 y n hn w hwn hwlg hws
      if hwx : w = x then
        subst hwx
        have hsy := seg_single g y n hn
        have hyd : y ∈ d.owners := hlsym (fun _ => y) y.id.step y.id.step (Int.le_refl _) hsy w d hd
          (by omega) (fun _ _ _ nj hnj => by rw [← Option.some.inj (hn.symm.trans hnj)]; exact hwn)
          y.id.step (Int.le_refl _) (Int.le_refl _)
        have hyl : (g.node? y).isSome := by rw [hn]; rfl
        have hys : y ∈ d.sons := hI1s w d hd y hyd hyl (by omega)
        have hyT : y ∈ intersectOwners d.owners (unionOwnersOf g d.sons) :=
          SegReview.mem_intersect_of_nb g d d.sons y hyd y hys n hn (hself y n hn)
        rw [PinAliveChain.unlinkMap_keeps _ _ _ (by rw [mirrorMap_id, hnid]; exact hyx)
          (by rw [mirrorMap_id, hnid]; exact List.elem_iff.mpr hyT)] at hny
        rw [hny, mirrorMap_parents]; exact hwp
      else
        rw [hny]
        exact PinAliveChain.parents_unlinkMap_keeps _ x _ (by rw [mirrorMap_id, hnid]; exact hyx) w
          (by rw [mirrorMap_parents]; exact hwp) hwx

/-- **La pasada de hijos conserva `I1sL`.** Caso con contenido: `x` hijo de un `y` vivo que lo tiene
en su tabla. `LocSymUp` en `[y]` pone a `y` en la tabla de `x`; el tramo `[y, x]` da un hijo vivo `s`
de `x` que tiene a `y` en su tabla (`LocSymUp` en `[y, x]`), así que `y` queda en el corte. -/
theorem i1sL_reviewNode_sons (g : GPathM) (hnd : NodupIds g) (hsgl : SegGoodL g) (hI1 : I1L g)
    (hI1s : I1sL g) (hself : SelfL g) (hlsymU : SegReview.LocSymUp g)
    (hrootz : Sons.RootAtZero g) (hsnn : SelfOwn.SNN g) (x : PathNodeId) (hx0 : 0 ≤ x.id.step)
    (hxl : x.id.step ≤ g.current_step - 2) :
    I1sL (reviewNode g (·.sons) x) := by
  have hsub := NodeIds.ids_reviewNode g (·.sons) x
  have liveG : ∀ w, ((reviewNode g (·.sons) x).node? w).isSome → (g.node? w).isSome :=
    fun w h => node_of_mem_ids g w (hsub.subset (mem_ids_of_node _ w h))
  intro y ny hy w hw hwl hws
  cases hd : g.node? x with
  | none =>
    have hR : reviewNode g (·.sons) x = g := by unfold reviewNode; rw [hd]
    rw [hR] at hy hwl
    exact hI1s y ny hy w hw hwl hws
  | some d =>
    have hk := kept_reviewNode_sons g hsgl hI1 hI1s hself hlsymU hrootz x d hd hx0 hxl
    obtain ⟨n, hn, _, _⟩ := SegReview.reviewNode_owners g hnd (·.sons) x y ny hy
    have hform := node_after g (·.sons) x d hd hk y n hn
    rw [hy] at hform
    have hny := Option.some.inj hform
    have hwlg := liveG w hwl
    if hyx : y = x then
      subst hyx
      rw [if_pos rfl, PinAliveChain.unlinkMap_self
        { d with owners := intersectOwners d.owners (unionOwnersOf g d.sons) } y
        (node?_id_eq g y d hd)] at hny
      rw [hny] at hw ⊢
      have hwd : w ∈ d.owners := (List.mem_filter.mp hw).1
      exact List.mem_filter.mpr ⟨hI1s y d hd w hwd hwlg hws, List.elem_iff.mpr hw⟩
    else
      rw [if_neg hyx] at hny
      have hnid : n.id = y := node?_id_eq g y n hn
      have hwn : w ∈ n.owners := by
        rw [hny, PinAliveChain.owners_unlinkMap] at hw; exact mirrorMap_owners_sub _ _ n w hw
      have hws' := hI1s y n hn w hwn hwlg hws
      if hwx : w = x then
        subst hwx
        have hy0 : 0 ≤ y.id.step := by
          rw [← hnid]; exact hsnn n (List.mem_of_find?_eq_some hn)
        have hsy := seg_single g y n hn
        have hyd : y ∈ d.owners := hlsymU (fun _ => y) y.id.step y.id.step (Int.le_refl _) hsy w d
          hd (by omega)
          (fun _ _ _ nj hnj => by rw [← Option.some.inj (hn.symm.trans hnj)]; exact hwn)
          y.id.step (Int.le_refl _) (Int.le_refl _)
        have hyl : (g.node? y).isSome := by rw [hn]; rfl
        have hyp : y ∈ d.parents := hI1 w d hd y hyd hyl (by omega)
        -- el tramo `[y, w]`
        have hs2 := SegReview.seg_extend_up g (fun _ => y) y.id.step y.id.step (Int.le_refl _) hsy
          w d hd (by omega) hyp
          (fun _ _ _ nj hnj => by rw [← Option.some.inj (hn.symm.trans hnj)]; exact hwn)
          (fun _ _ _ => hyd)
        have hsel_y : upd (fun _ => y) (y.id.step + 1) w y.id.step = y := upd_other _ _ _ (by omega)
        have hsel_w : upd (fun _ => y) (y.id.step + 1) w (y.id.step + 1) = w := upd_self _ _ _
        obtain ⟨sn, hsns, hsnl, hsn⟩ := hsgl _ y.id.step (y.id.step + 1) (by omega) (by omega)
          (by omega) hs2.1 hs2.2 (y.id.step + 2) (by omega) (by omega) (Or.inr (by omega))
        have hsnd : sn ∈ d.owners := hsn (y.id.step + 1) (by omega) (Int.le_refl _) d
          (by rw [hsel_w]; exact hd)
        have hsnson : sn ∈ d.sons := hI1s w d hd sn hsnd hsnl (by omega)
        obtain ⟨nsn, hnsn⟩ := Option.isSome_iff_exists.mp hsnl
        have hysn : y ∈ nsn.owners := by
          have := hlsymU _ y.id.step (y.id.step + 1) (by omega) hs2 sn nsn hnsn (by omega) hsn
            y.id.step (Int.le_refl _) (by omega)
          rw [hsel_y] at this; exact this
        have hyT : y ∈ intersectOwners d.owners (unionOwnersOf g d.sons) :=
          SegReview.mem_intersect_of_nb g d d.sons y hyd sn hsnson nsn hnsn hysn
        rw [PinAliveChain.unlinkMap_keeps _ _ _ (by rw [mirrorMap_id, hnid]; exact hyx)
          (by rw [mirrorMap_id, hnid]; exact List.elem_iff.mpr hyT)] at hny
        rw [hny, mirrorMap_sons]; exact hws'
      else
        rw [hny]
        exact PinAliveChain.sons_unlinkMap_keeps _ x _ (by rw [mirrorMap_id, hnid]; exact hyx) w
          (by rw [mirrorMap_sons]; exact hws') hwx

-- ============================================================
-- La pasada de hijos entera
-- ============================================================

/-- **La simetría local se conserva nodo a nodo en la pasada de hijos.** -/
def LocSymStableS : Prop :=
  ∀ g x, PState g → 0 ≤ x.id.step → x.id.step ≤ g.current_step - 2 →
    SegReview.LocSym (reviewNode g (·.sons) x) ∧ SegReview.LocSymUp (reviewNode g (·.sons) x)

theorem pstate_reviewNode_sons (hLS : LocSymStableS) (g : GPathM) (h : PState g) (x : PathNodeId)
    (hx0 : 0 ≤ x.id.step) (hxl : x.id.step ≤ g.current_step - 2) :
    PState (reviewNode g (·.sons) x) := by
  have hpr := pruned_reviewNode (·.sons) x g
  obtain ⟨hl, hlu⟩ := hLS g x h hx0 hxl
  exact
    { nd := List.Nodup.sublist (NodeIds.ids_reviewNode g (·.sons) x) h.nd
      sgl := segGoodL_reviewNode_sons g h.nd h.i1 h.i1s h.plive h.slive h.self h.lsym h.lsymU h.rootz
        h.sgl x hx0 hxl
      i1 := i1L_reviewNode_sons g h.nd h.sgl h.i1 h.i1s h.self h.lsym h.lsymU h.rootz x hx0 hxl
      i1s := i1sL_reviewNode_sons g h.nd h.sgl h.i1 h.i1s h.self h.lsymU h.rootz h.snn x hx0 hxl
      plive := pLive_reviewNode g h.nd h.plive _ x
      slive := sLive_reviewNode g h.nd h.slive _ x
      self := selfL_reviewNode g h.nd h.oos h.snn h.below h.self _ x
      lsym := hl
      lsymU := hlu
      nr := Parents.NotRoot_of_pruned hpr h.nr
      below := Certifies.nodes_below_of_pruned hpr h.below
      oos := SelfOwn.OOS_of_pruned hpr h.oos
      snn := SelfOwn.SNN_of_pruned hpr h.snn
      rootz := Sons.RootAtZero_of_pruned hpr h.rootz }

theorem pstate_foldl_sons (hLS : LocSymStableS) (k : Int) (hk0 : 0 ≤ k) :
    ∀ (L : List PathNodeId) (g : GPathM), PState g → k ≤ g.current_step - 2 →
      (∀ id ∈ L, id.id.step = k) →
      PState (L.foldl (fun g id => reviewNode g (·.sons) id) g) := by
  intro L
  induction L with
  | nil => intro g h _ _; exact h
  | cons x xs ih =>
    intro g h hkc hL
    have hxs := hL x List.mem_cons_self
    have hstep := (pruned_reviewNode (·.sons) x g).step_eq
    exact ih _ (pstate_reviewNode_sons hLS g h x (by omega) (by omega)) (by rw [hstep]; exact hkc)
      (fun id hid => hL id (List.mem_cons_of_mem _ hid))

theorem pstate_reviewSteps_sons (hLS : LocSymStableS) (c : Int) :
    ∀ (ks : List Int) (g : GPathM), PState g → g.current_step - 2 = c →
      (∀ k ∈ ks, 0 ≤ k ∧ k ≤ c) → PState (reviewSteps g (·.sons) ks) := by
  intro ks
  induction ks with
  | nil => intro g h _ _; exact h
  | cons k ks ih =>
    intro g h hc hks
    unfold reviewSteps
    split
    · have hk := hks k List.mem_cons_self
      have hstep := (pruned_reviewLine (·.sons) k g).step_eq
      refine ih _ ?_ (by rw [hstep]; exact hc) (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      refine pstate_foldl_sons hLS k hk.1 _ g h (by omega) (fun id hid => ?_)
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hid
      exact eq_of_beq (List.mem_filter.mp hn).2
    · exact h

/-- **La pasada de hijos entera conserva `PState`.** Única hipótesis: `LocSymStableS`. -/
theorem pstate_reviewSons (hLS : LocSymStableS) (g : GPathM) (h : PState g) :
    PState (reviewSons g) :=
  pstate_reviewSteps_sons hLS (g.current_step - 2) _ g h rfl
    (fun _ hk => ⟨mem_intRange_lower (List.mem_reverse.mp hk),
      mem_intRange_upper (List.mem_reverse.mp hk)⟩)

/-- info: 'AbsSat.GraphPath.Model.PassSons.pstate_reviewSons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pstate_reviewSons

end AbsSat.GraphPath.Model.PassSons
