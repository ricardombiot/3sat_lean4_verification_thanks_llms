-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnDown.lean
import AbsSatBingo.Model.ForbidOnLive
import AbsSatBingo.Model.SecStruct

/-!
# La dirección 2: lo que la llegada fijada deja vivo, la entrada fijada no lo prohíbe

Un estado revisado con la regla (`h`, la llegada fijada) sale con la regla en su punto fijo: todo triángulo suyo sin
prohibir tiene testigo bueno en cada paso, y toda arista suya también. Sea `(V, R)` una estructura cerrada suya (la
parte baja) y `T` sus tríos. Si `(V, R)` es estructura cerrada de otro estado `x` (la entrada fijada, antes de su
review) y los tríos de `x` sobre triángulos de `R` están en `T`, **el review con la regla de `x` lo conserva todo**:
la estructura (los lemas `sec_*` de siempre) y la inclusión de los tríos (la regla solo prohíbe triángulos sin testigo
bueno, y los de `R` fuera de `T` lo tienen; solo corta aristas sin testigo bueno, y las de `R` lo tienen).

La regla de `:on` es la que hace esto demostrable: sin tríos, el review de `x` podría dejar en su estructura cosas que
la llegada fijada descarta, y al revés.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

variable {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop} {T : Trios}

/-- **Testigos buenos de la estructura** respecto de los tríos `T`, en los pasos por debajo de `c`: toda arista de `R`
y todo triángulo de `R` fuera de `T` tienen, en cada paso, un nodo de `V` que los posee sin trío de `T`. Y `T` no
distingue el orden en los triángulos de `R`. -/
structure TrioGood (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop) (T : Trios) (c : Int) : Prop where
  edge : ∀ {a b}, R a b → a ≠ b → ∀ l, 0 ≤ l → l < c →
    ∃ s, s.id.step = l ∧ R a s ∧ R b s ∧ (s = a ∨ s = b ∨ ¬ T a b s)
  trio : ∀ {a b r}, R a b → R a r → R b r → a ≠ b → a ≠ r → b ≠ r → ¬ T a b r → ∀ l, 0 ≤ l → l < c →
    ∃ s, s.id.step = l ∧ R a s ∧ R b s ∧ R r s ∧ (s = a ∨ s = b ∨ s = r ∨ (¬ T a b s ∧ ¬ T a r s ∧ ¬ T b r s))
  swap23 : ∀ {a b r}, R a b → R a r → R b r → T a b r → T a r b
  swap12 : ∀ {a b r}, R a b → R a r → R b r → T a b r → T b a r

/-- **El invariante del review de la entrada fijada.** -/
structure DownInv (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop) (T : Trios) (c : Int) (x : GPathB) :
    Prop where
  sec  : SecStruct x V R
  ns   : NoSelf x
  step : x.current_step = c
  tri  : ∀ {a b r}, R a b → R a r → R b r → TF x a b r → T a b r

theorem downInv_shrink {x y : GPathB} (h : DownInv V R T c x) (hs : Sub y x) (ht : y.trios = x.trios)
    (hsec : SecStruct y V R) (hns : NoSelf y) : DownInv V R T c y :=
  ⟨hsec, hns, hs.step.trans h.step, fun hab har hbr hf => h.tri hab har hbr (tF_sub hs ht hf)⟩

theorem downInv_setT {x : GPathB} (h : DownInv V R T c x) (T' : List (PathNodeId × PathNodeId × PathNodeId))
    (htri : ∀ {a b r}, R a b → R a r → R b r → TF (x.setT T') a b r → T a b r) : DownInv V R T c (x.setT T') :=
  ⟨⟨h.sec.alive, h.sec.refl, h.sec.symm, h.sec.dom, h.sec.adj, h.sec.pair, h.sec.node, h.sec.par, h.sec.son⟩,
    h.ns, h.step, htri⟩

/-- `T` es la misma en cualquier orden de un triángulo de `R`. -/
theorem trioGood_perm (hg : TrioGood V R T c) (hs : ∀ {y w}, R y w → R w y) {a b r : PathNodeId} (hab : R a b)
    (har : R a r) (hbr : R b r) {p q w : PathNodeId} (hp : (p, q, w) ∈ perms a b r) (ht : T p q w) : T a b r := by
  have s23 : ∀ x y z, R x y → R x z → R y z → T x y z → T x z y := fun _ _ _ h1 h2 h3 h => hg.swap23 h1 h2 h3 h
  have s12 : ∀ x y z, R x y → R x z → R y z → T x y z → T y x z := fun _ _ _ h1 h2 h3 h => hg.swap12 h1 h2 h3 h
  have hba := hs hab
  have hra := hs har
  have hrb := hs hbr
  simp only [perms, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · exact ht
  · exact s23 _ _ _ har hab hrb ht
  · exact s12 _ _ _ hba hbr har ht
  · exact s12 _ _ _ hba hbr har (s23 _ _ _ hbr hba hra ht)
  · exact s23 _ _ _ har hab hrb (s12 _ _ _ hra hrb hab ht)
  · exact s23 _ _ _ har hab hrb (s12 _ _ _ hra hrb hab (s23 _ _ _ hrb hra hba ht))

theorem trioIs_iff_perms (a b r : PathNodeId) (t : PathNodeId × PathNodeId × PathNodeId) :
    trioIs a b r t = true ↔ t ∈ perms a b r := by
  obtain ⟨x, y, z⟩ := t
  simp only [trioIs, perms, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq]
  constructor
  · rintro (((((⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) |
      ⟨⟨h1, h2⟩, h3⟩) <;> subst h1 <;> subst h2 <;> subst h3 <;> simp
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;>
      subst h1 <;> subst h2 <;> subst h3 <;> simp

/-- Un orden de un triángulo de `R` es un triángulo de `R`. -/
theorem tri_of_perms (hs : ∀ {y w}, R y w → R w y) {a b r : PathNodeId} (hab : R a b) (har : R a r) (hbr : R b r)
    {p q w : PathNodeId} (hp : (p, q, w) ∈ perms a b r) : R p q ∧ R p w ∧ R q w := by
  simp only [perms, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · exact ⟨hab, har, hbr⟩
  · exact ⟨har, hab, hs hbr⟩
  · exact ⟨hs hab, hbr, har⟩
  · exact ⟨hbr, hs hab, hs har⟩
  · exact ⟨hs har, hs hbr, hab⟩
  · exact ⟨hs hbr, hs har, hs hab⟩

-- ============================================================
-- La estructura es testigo bueno en `x`
-- ============================================================

section Witness

variable {c : Int} {x : GPathB}

theorem incAt_of_R (hsec : SecStruct x V R) {a s : PathNodeId} (ha : V a) (hR : R a s) {l : Int}
    (hl : s.id.step = l) : s ∈ (Idx.of x).incAt a l := by
  unfold Idx.incAt
  by_cases he : s = a
  · subst he
    apply List.mem_append_left
    rw [if_pos (by simp [hl, (idx_alive x s).mpr (hsec.alive ha)])]
    exact List.mem_singleton_self _
  · apply List.mem_append_right
    rw [List.mem_filter, idx_mem_nbrs]
    exact ⟨⟨he, hsec.alive (hsec.dom hR).2, hasEdge_of_adj (hsec.adj hR) (fun h => he h.symm)⟩, by simp [hl]⟩

theorem not_dead_R (h : DownInv V R T c x) {a b s : PathNodeId} (hab : R a b) (has : R a s) (hbs : R b s)
    (hn : ¬ T a b s) : x.deadTrio a b s = false := by
  cases hd : x.deadTrio a b s
  · rfl
  · exfalso
    by_cases he : a = b
    · subst he
      unfold deadTrio at hd
      rw [hasEdge_self_false h.ns] at hd; cases hd
    · exact hn (h.tri hab has hbs ⟨he, hd⟩)

theorem trioAlive_of_R (h : DownInv V R T c x) (hg : TrioGood V R T c)
    {a b r : PathNodeId} (hab : R a b) (har : R a r) (hbr : R b r) (nab : a ≠ b) (nar : a ≠ r) (nbr : b ≠ r)
    (hn : ¬ T a b r) : (Idx.of x).trioAlive a b r = true := by
  unfold Idx.trioAlive
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨h0, h1⟩ := intRange_bounds hl
  have hcs : (Idx.of x).cs = c := h.step
  rw [hcs] at h1
  obtain ⟨s, hsl, has, hbs, hrs, hw⟩ := hg.trio hab har hbr nab nar nbr hn l h0 (by omega)
  rw [List.any_eq_true]
  refine ⟨s, incAt_of_R h.sec (h.sec.dom hab).1 has hsl, ?_⟩
  unfold Idx.goodWitness
  rcases hw with rfl | rfl | rfl | ⟨w1, w2, w3⟩
  · simp
  · simp
  · simp
  by_cases hsa : s = a
  · simp [hsa]
  by_cases hsb : s = b
  · simp [hsb]
  by_cases hsr : s = r
  · simp [hsr]
  simp only [Bool.or_eq_true, beq_iff_eq, hsa, hsb, hsr, false_or, Bool.and_eq_true, Bool.not_eq_true',
    idx_hasEdge, idx_deadTrio]
  exact ⟨⟨⟨⟨⟨hasEdge_of_adj (h.sec.adj has) (fun e => hsa e.symm), hasEdge_of_adj (h.sec.adj hbs) (fun e => hsb e.symm)⟩,
    hasEdge_of_adj (h.sec.adj hrs) (fun e => hsr e.symm)⟩, not_dead_R h hab has hbs w1⟩,
    not_dead_R h har has hrs w2⟩, not_dead_R h hbr hbs hrs w3⟩

theorem edgeAlive_of_R (h : DownInv V R T c x) (hg : TrioGood V R T c) {a b : PathNodeId} (hab : R a b)
    (nab : a ≠ b) : (Idx.of x).edgeAlive a b = true := by
  unfold Idx.edgeAlive
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨h0, h1⟩ := intRange_bounds hl
  have hcs : (Idx.of x).cs = c := h.step
  rw [hcs] at h1
  obtain ⟨s, hsl, has, hbs, hw⟩ := hg.edge hab nab l h0 (by omega)
  rw [List.any_eq_true]
  refine ⟨s, incAt_of_R h.sec (h.sec.dom hab).1 has hsl, ?_⟩
  rcases hw with rfl | rfl | hw
  · simp
  · simp
  by_cases hsa : s = a
  · simp [hsa]
  by_cases hsb : s = b
  · simp [hsb]
  simp only [Bool.or_eq_true, beq_iff_eq, hsa, hsb, false_or, Bool.and_eq_true, Bool.not_eq_true', idx_hasEdge,
    idx_deadTrio]
  exact ⟨hasEdge_of_adj (h.sec.adj hbs) (fun e => hsb e.symm), not_dead_R h hab has hbs hw⟩

end Witness

-- ============================================================
-- La regla y el review `:on` conservan el invariante
-- ============================================================

section Review

variable {c : Int}

theorem downInv_forbidRound {x : GPathB} (h : DownInv V R T c x) (hg : TrioGood V R T c)
    (hs : ∀ {y w}, R y w → R w y) : DownInv V R T c x.forbidRound.1 := by
  obtain ⟨T', hT⟩ := addTrios_eq x (Idx.of x) (x.newTrios (Idx.of x))
  -- los tríos nuevos sobre triángulos de `R` están en `T`
  have hnew : ∀ {a b r}, R a b → R a r → R b r → TF (x.setT T') a b r → T a b r := by
    intro a b r hab har hbr ⟨hne, hd⟩
    unfold deadTrio at hd
    rw [Bool.and_eq_true] at hd
    obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd.2
    have ht' : t ∈ (x.addTrios (Idx.of x) (x.newTrios (Idx.of x))).1.trios := by rw [hT]; exact ht
    rcases mem_addTrios x _ _ t ht' with hold | hn
    · exact h.tri hab har hbr ⟨hne, by unfold deadTrio; rw [Bool.and_eq_true]; exact ⟨hd.1,
        List.any_eq_true.mpr ⟨t, hold, hti⟩⟩⟩
    · refine Classical.byContradiction fun hT0 => ?_
      unfold newTrios at hn
      obtain ⟨e, he, hn⟩ := List.mem_flatMap.mp hn
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hn
      obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr'
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hr2
      have hnb := (idx_mem_nbrs x e.1 r').mp hr1
      have dt : e.1 ≠ e.2 ∧ e.1 ≠ r' ∧ e.2 ≠ r' := ⟨h.ns e he, fun q => hnb.1 q.symm, fun q => hr2.1.1.1 q.symm⟩
      have hp := (trioIs_iff_perms a b r _).mp hti
      obtain ⟨t1, t2, t3⟩ := tri_of_perms (R := R) hs hab har hbr hp
      have hnT : ¬ T e.1 e.2 r' := fun q => hT0 (trioGood_perm hg hs hab har hbr hp q)
      rw [trioAlive_of_R h hg t1 t2 t3 dt.1 dt.2.1 dt.2.2 hnT] at hr2
      exact absurd hr2.2 (by simp)
  have h₁ : DownInv V R T c (x.setT T') := downInv_setT h T' hnew
  simp only [forbidRound]
  rw [hT]
  split
  · exact h₁
  · -- las aristas malas no son de `R`
    have hbad : ∀ e ∈ (x.setT T').edges.filter (fun e => !(Idx.of (x.setT T')).edgeAlive e.1 e.2), ¬ R e.1 e.2 := by
      intro e he hR
      have := (List.mem_filter.mp he).2
      rw [edgeAlive_of_R h₁ hg hR (fun q => h₁.ns e (List.mem_filter.mp he).1 q)] at this
      exact absurd this (by simp)
    have key : ∀ (l : List (PathNodeId × PathNodeId)), (∀ e ∈ l, ¬ R e.1 e.2) → ∀ y : GPathB, DownInv V R T c y →
        DownInv V R T c (l.foldl (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) y) := by
      intro l
      induction l with
      | nil => intro _ y hy; exact hy
      | cons e es ih =>
        intro hl y hy
        rw [List.foldl_cons]
        exact ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) _
          (downInv_shrink hy (shrinks_removeEdge y e.1 e.2).1 rfl (sec_removeEdge hy.sec (hl e List.mem_cons_self))
            (revPrims_noSelf.rmEdge y e.1 e.2 hy.ns))
    have h₂ := key _ hbad _ h₁
    have h₃ := downInv_shrink h₂ (shrinks_dirty _ true).1 rfl (sec_dirty h₂.sec true) h₂.ns
    exact downInv_shrink h₃ (shrinks_clean _).1 (trios_clean _) (sec_clean h₃.sec) (revPrims_clean revPrims_noSelf _ h₃.ns)

theorem downInv_forbidFuel (hg : TrioGood V R T c) (hs : ∀ {y w}, R y w → R w y) :
    ∀ (n : Nat) (x : GPathB), DownInv V R T c x → DownInv V R T c (forbidFuel n x) := by
  intro n
  induction n with
  | zero => intro x h; exact h
  | succ n ih =>
    intro x h
    unfold forbidFuel
    split
    · simp only
      split
      · exact ih _ (downInv_forbidRound h hg hs)
      · exact downInv_forbidRound h hg hs
    · exact h

theorem downInv_reviewPassOn {x : GPathB} (h : DownInv V R T c x) (hg : TrioGood V R T c)
    (hs : ∀ {y w}, R y w → R w y) : DownInv V R T c x.reviewPassOn := by
  have h1 := downInv_shrink h (shrinks_cleanPair x).1 (trios_cleanPair x) (sec_cleanPair h.sec)
    (revPrims_cleanPair revPrims_noSelf x h.ns)
  have h2 : DownInv V R T c x.cleanPair.forbidRule := downInv_forbidFuel hg hs x.cleanPair.forbidBound _ h1
  have h3 := downInv_shrink h2 (shrinks_pruneLinks _).1 (trios_pruneLinks _) (sec_pruneLinks h2.sec)
    (revPrims_noSelf.links _ h2.ns)
  have h4 := downInv_shrink h3 (shrinks_reviewParents _).1 (trios_reviewParents _) (sec_reviewParents h3.sec)
    (by unfold reviewParents; split
        · exact revPrims_reviewSteps revPrims_noSelf _ _ _ h3.ns
        · exact h3.ns)
  have h5 := downInv_shrink h4 (shrinks_reviewSons _).1 (trios_reviewSons _) (sec_reviewSons h4.sec)
    (by unfold reviewSons; split
        · exact revPrims_reviewSteps revPrims_noSelf _ _ _ h4.ns
        · exact h4.ns)
  exact downInv_shrink h5 (shrinks_pruneLinks _).1 (trios_pruneLinks _) (sec_pruneLinks h5.sec)
    (revPrims_noSelf.links _ h5.ns)

/-- **El review con la regla conserva el invariante.** -/
theorem downInv_reviewOn {x : GPathB} (h : DownInv V R T c x) (hg : TrioGood V R T c)
    (hs : ∀ {y w}, R y w → R w y) : DownInv V R T c x.reviewOn :=
  reviewFuelOn_pres (DownInv V R T c)
    (fun y hy => downInv_reviewPassOn (downInv_shrink hy (shrinks_dirty y false).1 rfl (sec_dirty hy.sec false) hy.ns)
      hg hs)
    (fun y hy => downInv_shrink hy (shrinks_finalPass y).1 (trios_finalPass y) (sec_finalPass hy.sec)
      (revPrims_finalPass revPrims_noSelf y hy.ns)) _ x h

/-- **El filtro por requisitos que la estructura cumple conserva el invariante.** -/
theorem downInv_filterRequire {x : GPathB} (h : DownInv V R T c x) {r : NodeId} (ha : SecAgrees V r) :
    DownInv V R T c (x.filterRequire r) :=
  downInv_shrink h (shrinks_filterRequire x r).1
    (trios_of_comm (f := fun y => y.filterRequire r) (fun y T' => filterRequire_setT T' y r) x)
    (sec_filterRequire h.sec ha) (Final.revPrims_filterRequire revPrims_noSelf x r h.ns)

end Review

end GPathB

end AbsSatBingo.Model
