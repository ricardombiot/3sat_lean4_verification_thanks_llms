-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnLive.lean
import AbsSatBingo.Model.ForbidOnLine
import AbsSatBingo.Model.LiveUp
import AbsSatBingo.Model.LiveJoin

/-!
# `LiveExt` con los tríos reales (`docs/plans/lean_forbid_on.md`, F4)

La maquinaria de `LiveUp.lean` es genérica en la relación de tríos. Aquí se aplica a la relación del propio estado,
`TF g`, en la máquina `:on`:

* **`liveExt_of_keep'`**: `liveExt_of_keep` pide que los tríos del estado mayor estén en el menor. Con los tríos reales
  eso falla fuera de las cadenas (al cortar una arista, los tríos que colgaban de ella dejan de contar), pero basta
  pedirlo en los triángulos del estado menor, que es donde viven las cadenas.
* **`liveExt_reviewOn`**: el review con la regla conserva `LiveExt` con los tríos reales. Toda camarilla que esquiva
  los tríos es testigo bueno de sus tríos y aristas (`ct_reviewOn`), y los tríos solo crecen.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

variable {S : Int → PathNodeId}

-- ============================================================
-- Tríos no degenerados
-- ============================================================

/-- Los tríos guardados tienen tres nodos distintos. -/
def NoDegT (g : GPathB) : Prop := ∀ t ∈ g.trios, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

/-- Un trío `{a, b, r}` de un trío guardado sin repeticiones tiene tres nodos distintos. -/
theorem distinct_of_trioIs {a b r : PathNodeId} {t : PathNodeId × PathNodeId × PathNodeId} (h : trioIs a b r t = true)
    (hd : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) : a ≠ b ∧ a ≠ r ∧ b ≠ r := by
  obtain ⟨x, y, z⟩ := t
  obtain ⟨d1, d2, d3⟩ := hd
  simp only at d1 d2 d3
  simp only [trioIs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (((((⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) |
    ⟨⟨h1, h2⟩, h3⟩) <;> subst h1 <;> subst h2 <;> subst h3 <;>
    exact ⟨fun h => by simp_all, fun h => by simp_all, fun h => by simp_all⟩

theorem noDeg_TF {g : GPathB} (h : NoDegT g) : NoDeg (TF g) := by
  intro x y z ⟨_, hd⟩
  unfold deadTrio at hd
  rw [Bool.and_eq_true] at hd
  obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd.2
  exact distinct_of_trioIs hti (h t ht)

-- ============================================================
-- Conservar camarillas, con la monotonía solo en los triángulos
-- ============================================================

/-- **Una cadena viva del subestado es viva en el estado mayor**, si los tríos del mayor sobre triángulos del
menor están en el menor. -/
theorem liveChain_sub' {h g : GPathB} {F G : Trios} (hs : Sub h g) (hnd : NodupIds g)
    (hFG : ∀ x y z, h.Adj x y → h.Adj x z → h.Adj y z → F x y z → G x y z) {C : Int → PathNodeId} {j : Int}
    (hC : LiveChain h G C j) : LiveChain g F C j := by
  have hst := hs.step
  refine ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩, fun a b c ha hab hbc hc hf => ?_⟩
  · obtain ⟨a, b⟩ := hC.chain.node k h1 (by rw [hst]; exact h2); exact ⟨a, hs.alive _ b⟩
  · exact hs.adj _ _ (hC.chain.adj k l h1 (by rw [hst]; exact h2) h3 (by rw [hst]; exact h4))
  · obtain ⟨n, hn, hp⟩ := hC.chain.link k h1 (by rw [hst]; exact h2)
    obtain ⟨m, hm, hpm⟩ := node?_sub hs hnd hn
    exact ⟨m, hm, hpm _ hp⟩
  · have hc' : c ≤ h.current_step - 1 := by rw [hst]; exact hc
    have e : ∀ p q, j ≤ p → p ≤ h.current_step - 1 → j ≤ q → q ≤ h.current_step - 1 → h.Adj (C p) (C q) :=
      fun p q h1 h2 h3 h4 => hC.chain.adj p q h1 h2 h3 h4
    have eab := e a b ha (by omega) (by omega) (by omega)
    have eac := e a c ha (by omega) (by omega) hc'
    have ebc := e b c (by omega) (by omega) (by omega) hc'
    have eba := e b a (by omega) (by omega) ha (by omega)
    have eca := e c a (by omega) hc' ha (by omega)
    have ecb := e c b (by omega) hc' (by omega) (by omega)
    apply hC.live a b c ha hab hbc hc'
    unfold Sym at hf ⊢
    rcases hf with hf | hf | hf | hf | hf | hf
    · exact Or.inl (hFG _ _ _ eab eac ebc hf)
    · exact Or.inr (Or.inl (hFG _ _ _ eac eab ecb hf))
    · exact Or.inr (Or.inr (Or.inl (hFG _ _ _ eba ebc eac hf)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hFG _ _ _ ebc eba eca hf))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hFG _ _ _ eca ecb eab hf)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hFG _ _ _ ecb eca eba hf)))))

/-- **Conservar camarillas conserva `LiveExt`**, con la monotonía de los tríos solo en los triángulos del menor. -/
theorem liveExt_of_keep' {g h : GPathB} {F G : Trios} (hext : LiveExt g F) (hdocs : AliveDocs g) (hli : LinksInv g)
    (hr : RootNone g) (hnd : NodupIds g) (hnF : NoDeg F) (hs : Sub h g)
    (hFG : ∀ x y z, h.Adj x y → h.Adj x z → h.Adj y z → F x y z → G x y z)
    (hkeep : ∀ D, Carried g D → Avoids F g.current_step D → Carried h D ∧ Avoids G h.current_step D) :
    LiveExt h G := by
  intro C j hC hj1 hjt
  have hst := hs.step
  obtain ⟨D, hD, hag⟩ := liveChain_extend_full hext (liveChain_sub' hs hnd hFG hC) (by omega) (by rw [← hst]; exact hjt)
  obtain ⟨hcD, hAD⟩ := hkeep D (carried_of_liveChain hdocs hli hr hD) (avoids_of_liveChain hnF hD)
  exact ⟨D, liveChain_of_carried hcD hAD (by omega), hag⟩

-- ============================================================
-- En el review `:on` los tríos solo crecen y siguen sin degenerar
-- ============================================================

/-- Los tríos de la vuelta de la regla: los de `addTrios` (el corte y la limpieza no los tocan). -/
theorem forbidRound_trios (g : GPathB) :
    g.forbidRound.1.trios = (g.addTrios (Idx.of g) (g.newTrios (Idx.of g))).1.trios := by
  simp only [forbidRound]
  obtain ⟨T', hT⟩ := addTrios_eq g (Idx.of g) (g.newTrios (Idx.of g))
  rw [hT]
  split
  · rfl
  · rw [trios_clean]
    show (List.foldl (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) (g.setT T') _).trios = T'
    have key : ∀ (l : List (PathNodeId × PathNodeId)) (x : GPathB),
        (l.foldl (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) x).trios = x.trios := by
      intro l
      induction l with
      | nil => intro x; rfl
      | cons e es ih => intro x; rw [List.foldl_cons, ih]; rfl
    rw [key]

theorem trios_grow_forbidRound (g : GPathB) : ∀ t ∈ g.trios, t ∈ g.forbidRound.1.trios := by
  intro t ht
  rw [forbidRound_trios]
  unfold addTrios
  exact List.mem_append_left _ ht

theorem trios_grow_forbidFuel : ∀ (n : Nat) (g : GPathB), ∀ t ∈ g.trios, t ∈ (forbidFuel n g).trios := by
  intro n
  induction n with
  | zero => intro g t ht; exact ht
  | succ n ih =>
    intro g t ht
    unfold forbidFuel
    split
    · simp only
      split
      · exact ih _ t (trios_grow_forbidRound g t ht)
      · exact trios_grow_forbidRound g t ht
    · exact ht

theorem trios_grow_reviewPassOn (g : GPathB) : ∀ t ∈ g.trios, t ∈ g.reviewPassOn.trios := by
  intro t ht
  unfold reviewPassOn
  rw [trios_pruneLinks, trios_reviewSons, trios_reviewParents, trios_pruneLinks]
  exact trios_grow_forbidFuel _ _ t (by rw [trios_cleanPair]; exact ht)

theorem trios_grow_reviewOn (g : GPathB) : ∀ t ∈ g.trios, t ∈ g.reviewOn.trios := by
  have := reviewFuelOn_pres (fun x => ∀ t ∈ g.trios, t ∈ x.trios)
    (fun x hx t ht => trios_grow_reviewPassOn { x with dirty := false } t (hx t ht))
    (fun x hx t ht => by rw [trios_finalPass]; exact hx t ht) (g.measure + 1) g (fun _ h => h)
  exact this

theorem noDegT_forbidRound {g : GPathB} (hns : NoSelf g) (h : NoDegT g) : NoDegT g.forbidRound.1 := by
  intro t ht
  rw [forbidRound_trios] at ht
  rcases mem_addTrios g _ _ t ht with h1 | h1
  · exact h t h1
  · unfold newTrios at h1
    obtain ⟨e, he, h1⟩ := List.mem_flatMap.mp h1
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h1
    obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
    have hn := (idx_mem_nbrs g e.1 r).mp hr1
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hr2
    exact ⟨hns e he, fun h' => hn.1 h'.symm, fun h' => hr2.1.1.1 h'.symm⟩

theorem noDegT_forbidFuel : ∀ (n : Nat) (g : GPathB), NoSelf g → NoDegT g → NoDegT (forbidFuel n g) := by
  intro n
  induction n with
  | zero => intro g _ h; exact h
  | succ n ih =>
    intro g hns h
    unfold forbidFuel
    split
    · simp only
      split
      · exact ih _ (revPrims_forbidRound revPrims_noSelf trioBlind_noSelf g hns) (noDegT_forbidRound hns h)
      · exact noDegT_forbidRound hns h
    · exact h

theorem noDegT_of_trios {g h : GPathB} (ht : h.trios = g.trios) (hg : NoDegT g) : NoDegT h := by
  intro t htt; rw [ht] at htt; exact hg t htt

theorem noDegT_reviewPassOn {g : GPathB} (hns : NoSelf g) (h : NoDegT g) : NoDegT g.reviewPassOn := by
  have h1 : NoDegT g.cleanPair := noDegT_of_trios (trios_cleanPair g) h
  have hns1 : NoSelf g.cleanPair := revPrims_cleanPair revPrims_noSelf g hns
  have h2 : NoDegT g.cleanPair.forbidRule := noDegT_forbidFuel _ _ hns1 h1
  unfold reviewPassOn
  exact noDegT_of_trios ((trios_pruneLinks _).trans ((trios_reviewSons _).trans ((trios_reviewParents _).trans
    (trios_pruneLinks _)))) h2

theorem noDegT_reviewOn {g : GPathB} (hns : NoSelf g) (h : NoDegT g) : NoDegT g.reviewOn := by
  have := reviewFuelOn_pres (fun x => NoSelf x ∧ NoDegT x)
    (fun x hx => ⟨revPrims_reviewPassOn revPrims_noSelf trioBlind_noSelf _ hx.1,
      noDegT_reviewPassOn (g := { x with dirty := false }) hx.1 hx.2⟩)
    (fun x hx => ⟨revPrims_finalPass revPrims_noSelf x hx.1, noDegT_of_trios (trios_finalPass x) hx.2⟩)
    (g.measure + 1) g ⟨hns, h⟩
  exact this.2

-- ============================================================
-- El review `:on` conserva LiveExt con los tríos reales
-- ============================================================

/-- Los tríos de `g` sobre una arista que sigue en `h` y con los tríos de `g` en `h` siguen en `h`. -/
theorem tF_mono {g h : GPathB} (hgrow : ∀ t ∈ g.trios, t ∈ h.trios) {x y z : PathNodeId} (hxy : h.Adj x y)
    (hf : TF g x y z) : TF h x y z := by
  obtain ⟨hne, hd⟩ := hf
  refine ⟨hne, ?_⟩
  unfold deadTrio at hd ⊢
  rw [Bool.and_eq_true] at hd ⊢
  obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd.2
  exact ⟨hasEdge_of_adj hxy hne, List.any_eq_true.mpr ⟨t, hgrow t ht, hti⟩⟩

/-- **El review con la regla conserva `LiveExt` con los tríos reales.** -/
theorem liveExt_reviewOn {g : GPathB} (hext : LiveExt g (TF g)) (hdocs : AliveDocs g) (hli : LinksInv g)
    (hr : RootNone g) (hnd : NodupIds g) (hns : NoSelf g) (hndt : NoDegT g) :
    LiveExt g.reviewOn (TF g.reviewOn) := by
  have hs := (shrinks_reviewOn g).1
  refine liveExt_of_keep' hext hdocs hli hr hnd (noDeg_TF hndt) hs
    (fun x y z hxy _ _ hf => tF_mono (trios_grow_reviewOn g) hxy hf) ?_
  intro D hc hA
  have hct := ct_reviewOn (S := D) ⟨hc, hA, hns⟩
  exact ⟨hct.1, hct.2.1⟩

-- ============================================================
-- LiveExt no mira los tríos del estado
-- ============================================================

theorem liveChain_setT {g : GPathB} {F : Trios} {T : List (PathNodeId × PathNodeId × PathNodeId)}
    {C : Int → PathNodeId} {j : Int} (h : LiveChain g F C j) : LiveChain (g.setT T) F C j :=
  ⟨⟨h.chain.node, h.chain.adj, h.chain.link⟩, h.live⟩

theorem liveChain_of_setT {g : GPathB} {F : Trios} {T : List (PathNodeId × PathNodeId × PathNodeId)}
    {C : Int → PathNodeId} {j : Int} (h : LiveChain (g.setT T) F C j) : LiveChain g F C j :=
  ⟨⟨h.chain.node, h.chain.adj, h.chain.link⟩, h.live⟩

theorem liveExt_setT {g : GPathB} {F : Trios} (h : LiveExt g F) (T : List (PathNodeId × PathNodeId × PathNodeId)) :
    LiveExt (g.setT T) F := by
  intro C j hC hj1 hjt
  obtain ⟨C', hC', hag⟩ := h C j (liveChain_of_setT hC) hj1 hjt
  exact ⟨C', liveChain_setT hC', hag⟩

-- ============================================================
-- El UP `:on` conserva LiveExt con los tríos reales
-- ============================================================

section Up

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool} {D : Int → PathNodeId}

/-- **Los tríos de `up_forbid!` no son de ninguna camarilla que esquive los tríos**: el padre de la camarilla es
padre del nodo nuevo y no corta el trío. -/
theorem upTodo_notOnS (hdS : d.step = g.current_step) (hct : CT ((g.addNode d title forb).setT g.trios) D) :
    ∀ t ∈ (g.newRowIds d forb).flatMap (fun n => upForbidTodo (Idx.of ((g.addNode d title forb).setT g.trios)) n
        (((g.addNode d title forb).setT g.trios).parentsOf n)),
      ¬ (OnS (g.current_step + 1) D t.1 ∧ OnS (g.current_step + 1) D t.2.1 ∧ OnS (g.current_step + 1) D t.2.2) := by
  let a' := (g.addNode d title forb).setT g.trios
  have hcs : a'.current_step = g.current_step + 1 := rfl
  have onA : ∀ x, OnS (g.current_step + 1) D x → OnS a'.current_step D x := fun x h => h
  have hc : Carried a' D := hct.1
  have hid : ∀ q ∈ g.newRowIds d forb, q.id = d := fun q hq => newRow_id' hq
  have hidx : ∀ k, 0 ≤ k → k < g.current_step + 1 → (D k).id.step = k := fun k h0 h1 => hc.step k h0 h1
  intro t ht ⟨hn, hw, hr⟩
  obtain ⟨n, hnm, ht⟩ := List.mem_flatMap.mp ht
  unfold upForbidTodo at ht
  obtain ⟨wr, hwr, rfl⟩ := List.mem_map.mp ht
  simp only at hn hw hr
  obtain ⟨hwr1, hwr2⟩ := List.mem_filter.mp hwr
  simp only [Bool.and_eq_true, List.all_eq_true] at hwr2
  obtain ⟨kn, hk0, hk1, hkn⟩ := hn
  have hkcs : kn = g.current_step := by
    have := hidx kn hk0 hk1; rw [hkn, hid _ hnm, hdS] at this; omega
  subst hkcs
  obtain ⟨hw1, _⟩ := mem_pairsOf hwr1
  have hwn : wr.1 ≠ n := ((idx_mem_nbrs a' n wr.1).mp hw1).1
  obtain ⟨j, hj0, hj1, hjw⟩ := hw
  have hjcs : j < g.current_step := by
    rcases Int.lt_or_eq_of_le (show j ≤ g.current_step by omega) with h | h
    · exact h
    · exfalso; apply hwn; rw [← hjw, ← hkn, h]
  have hpos : 0 < g.current_step := by omega
  obtain ⟨m, hm, hmp, _⟩ := hc.node g.current_step (by omega) (by rw [hcs]; omega)
  have hpm : D (g.current_step - 1) ∈ a'.parentsOf n := by
    unfold parentsOf; rw [← hkn, hm]; exact hmp hpos
  have hsf := hwr2.2 _ hpm
  rw [idx_sideForbids, sideForbidsB_false hct (onA _ ⟨g.current_step - 1, by omega, by omega, rfl⟩)
    (onA _ ⟨j, hj0, by omega, hjw⟩) (onA _ hr)] at hsf
  cases hsf

/-- Con los tríos por debajo del paso, la fila nueva no cambia la relación de tríos. -/
theorem tF_addNode (htb : TBelow g) (hdS : d.step = g.current_step) :
    TF ((g.addNode d title forb).setT g.trios) = TF g := by
  funext x y z
  apply propext
  have hid : ∀ q ∈ g.newRowIds d forb, q.id = d := fun q hq => newRow_id' hq
  constructor
  · rintro ⟨hne, hd⟩
    refine ⟨hne, ?_⟩
    unfold deadTrio at hd ⊢
    rw [Bool.and_eq_true] at hd ⊢
    obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd.2
    obtain ⟨c1, c2, _⟩ := trioIs_mem' hti
    have hbt := htb t ht
    have hx := step_of_comp hbt c1
    have hy := step_of_comp hbt c2
    have nx : x ∉ g.newRowIds d forb := fun h => by rw [hid _ h, hdS] at hx; omega
    have ny : y ∉ g.newRowIds d forb := fun h => by rw [hid _ h, hdS] at hy; omega
    exact ⟨hasEdge_addNode_old (title := title) nx ny hd.1, hd.2⟩
  · rintro ⟨hne, hd⟩
    refine ⟨hne, ?_⟩
    unfold deadTrio at hd ⊢
    rw [Bool.and_eq_true] at hd ⊢
    refine ⟨?_, hd.2⟩
    obtain ⟨e, he, hj⟩ := List.any_eq_true.mp hd.1
    exact List.any_eq_true.mpr ⟨e, List.mem_append_left _ he, hj⟩

theorem noDegT_upForbidRow (hns : NoSelf ((g.addNode d title forb).setT g.trios)) (hndt : NoDegT g) :
    NoDegT (((g.addNode d title forb).setT g.trios).upForbidRow (g.newRowIds d forb)) := by
  let a' := (g.addNode d title forb).setT g.trios
  intro t ht
  unfold upForbidRow at ht
  rcases mem_addTrios a' _ _ t ht with h1 | h1
  · exact hndt t h1
  · obtain ⟨n, _, h1⟩ := List.mem_flatMap.mp h1
    unfold upForbidTodo at h1
    obtain ⟨wr, hwr, rfl⟩ := List.mem_map.mp h1
    obtain ⟨hwr1, hwr2⟩ := List.mem_filter.mp hwr
    simp only [Bool.and_eq_true] at hwr2
    obtain ⟨hw, hr⟩ := mem_pairsOf hwr1
    have hwn := ((idx_mem_nbrs a' n wr.1).mp hw).1
    have hrn := ((idx_mem_nbrs a' n wr.2).mp hr).1
    have hwr' : wr.1 ≠ wr.2 := by
      intro h
      have he := hwr2.1
      rw [idx_hasEdge, h, hasEdge_self_false hns] at he
      cases he
    exact ⟨fun h => hwn h.symm, fun h => hrn h.symm, hwr'⟩

/-- **El UP `:on` conserva `LiveExt` con los tríos reales.** -/
theorem liveExt_upOn (hv : g.isValid = true) (hext : LiveExt g (TF g)) (hdocs : AliveDocs g) (hb : Machine.Below g)
    (hda : DocsAlive g) (hli : LinksInv g) (hz : AboveZero g) (hnd : NodupIds g) (hr : RootNone g)
    (hns : NoSelf g) (hndt : NoDegT g) (htb : TB g) (hdS : d.step = g.current_step) :
    LiveExt (g.upOn d title forb) (TF (g.upOn d title forb)) := by
  unfold upOn
  rw [if_pos hv]
  let a := g.addNode d title forb
  let a' := a.setT g.trios
  have hB : FBelow (TF g) g.current_step := by
    intro x y z ⟨_, hd⟩
    unfold deadTrio at hd
    rw [Bool.and_eq_true] at hd
    obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd.2
    obtain ⟨c1, c2, c3⟩ := trioIs_mem' hti
    have hbt := htb.1 t ht
    exact ⟨step_of_comp hbt c1, step_of_comp hbt c2, step_of_comp hbt c3⟩
  -- la fila, con los tríos de antes
  have h1 : LiveExt a (TF g) := liveExt_addNode_same (title := title) (forb := forb) hext hdocs hb hda hdS hB
  have h2 : LiveExt a' (TF a') := by
    rw [show TF a' = TF g from tF_addNode htb.1 hdS]; exact liveExt_setT h1 g.trios
  have hdocs' : AliveDocs a' := Machine.aliveDocs_addNode (title := title) (forb := forb) hdocs
  have hli' : LinksInv a' := linksInv_addNode (title := title) (forb := forb) hli hb hz hdS
  have hr' : RootNone a' := rootNone_addNode (title := title) (forb := forb) hr hdS
  have hnd' : NodupIds a' := nodupIds_addNode (title := title) (forb := forb) hnd hb hdS
  have hns' : NoSelf a' := noSelf_addNode (title := title) hns
  have hndt' : NoDegT a' := hndt
  -- `up_forbid!`
  obtain ⟨T', hT⟩ := upForbidRow_eq a' (g.newRowIds d forb)
  have h3 : LiveExt (a'.upForbidRow (g.newRowIds d forb)) (TF (a'.upForbidRow (g.newRowIds d forb))) := by
    have hgrow : ∀ t ∈ a'.trios, t ∈ (a'.upForbidRow (g.newRowIds d forb)).trios := by
      intro t ht; unfold upForbidRow addTrios; exact List.mem_append_left _ ht
    refine liveExt_of_keep' h2 hdocs' hli' hr' hnd' (noDeg_TF hndt')
      (by rw [hT]; exact (shrinks_setT a' T').1)
      (fun x y z hxy _ _ hf => tF_mono hgrow hxy hf) ?_
    intro D hc hA
    have hA' := avoids_addTrios hA (Idx.of a') _ (upTodo_notOnS hdS ⟨hc, hA, hns'⟩)
    refine ⟨?_, hA'⟩
    rw [hT]; exact ⟨hc.step, hc.alive, hc.adj, hc.root, hc.node⟩
  -- el review
  have hns'' : NoSelf (a'.upForbidRow (g.newRowIds d forb)) := by rw [hT]; exact hns'
  exact liveExt_reviewOn h3 (by rw [hT]; exact hdocs') (by rw [hT]; exact hli') (by rw [hT]; exact hr')
    (by rw [hT]; exact hnd') hns'' (noDegT_upForbidRow hns' hndt)

end Up

-- ============================================================
-- LiveExt solo mira tríos de tres nodos distintos
-- ============================================================

theorem liveChain_congrD {g : GPathB} {F G : Trios}
    (hGF : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → G x y z → F x y z) {C : Int → PathNodeId} {j : Int}
    (hC : LiveChain g F C j) : LiveChain g G C j := by
  refine ⟨hC.chain, fun a b c ha hab hbc hc hs => hC.live a b c ha hab hbc hc ?_⟩
  have st : ∀ k, j ≤ k → k ≤ g.current_step - 1 → (C k).id.step = k := fun k h1 h2 => (hC.chain.node k h1 h2).1
  have ne : ∀ k l, j ≤ k → k ≤ g.current_step - 1 → j ≤ l → l ≤ g.current_step - 1 → k ≠ l → C k ≠ C l := by
    intro k l h1 h2 h3 h4 hkl h
    have := st k h1 h2; rw [h, st l h3 h4] at this; exact hkl this.symm
  have nab := ne a b ha (by omega) (by omega) (by omega) (by omega)
  have nac := ne a c ha (by omega) (by omega) hc (by omega)
  have nbc := ne b c (by omega) (by omega) (by omega) hc (by omega)
  unfold Sym at hs ⊢
  rcases hs with h | h | h | h | h | h
  · exact Or.inl (hGF _ _ _ nab nac nbc h)
  · exact Or.inr (Or.inl (hGF _ _ _ nac nab (Ne.symm nbc) h))
  · exact Or.inr (Or.inr (Or.inl (hGF _ _ _ (Ne.symm nab) nbc nac h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hGF _ _ _ nbc (Ne.symm nab) (Ne.symm nac) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hGF _ _ _ (Ne.symm nac) (Ne.symm nbc) nab h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hGF _ _ _ (Ne.symm nbc) (Ne.symm nac) (Ne.symm nab) h)))))

theorem liveExt_congrD {g : GPathB} {F G : Trios} (hFG : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → F x y z → G x y z)
    (hGF : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → G x y z → F x y z) (h : LiveExt g F) : LiveExt g G := by
  intro C j hC hj1 hjt
  obtain ⟨C', hC', hag⟩ := h C j (liveChain_congrD hFG hC) hj1 hjt
  exact ⟨C', liveChain_congrD hGF hC', hag⟩

-- ============================================================
-- Tríos: simetría, cobertura de addTrios, SideForbids en Bool
-- ============================================================

theorem trioIs_swap12 {a b r : PathNodeId} {t : PathNodeId × PathNodeId × PathNodeId} (h : trioIs b a r t = true) :
    trioIs a b r t = true := by
  obtain ⟨x, y, z⟩ := t
  simp only [trioIs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (((((⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) |
    ⟨⟨h1, h2⟩, h3⟩) <;> subst h1 <;> subst h2 <;> subst h3 <;> simp [trioIs]

theorem trioIs_self (a b r : PathNodeId) : trioIs a b r (a, b, r) = true := by simp [trioIs]

theorem tF_swap12 {g : GPathB} {a b r : PathNodeId} (h : TF g b a r) : TF g a b r := by
  obtain ⟨hne, hd⟩ := h
  refine ⟨Ne.symm hne, ?_⟩
  unfold deadTrio at hd ⊢
  rw [Bool.and_eq_true] at hd ⊢
  obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd.2
  refine ⟨?_, List.any_eq_true.mpr ⟨t, ht, trioIs_swap12 hti⟩⟩
  obtain ⟨e, he, hj⟩ := List.any_eq_true.mp hd.1
  exact List.any_eq_true.mpr ⟨e, he, by rw [joins_iff] at hj ⊢; rcases hj with h | h; exact Or.inr h; exact Or.inl h⟩

theorem sideForbids_swap12 {g : GPathB} {F : Trios} (hF : ∀ a b r, F b a r → F a b r) {a b r : PathNodeId}
    (h : SideForbids g F b a r) : SideForbids g F a b r := by
  rcases h with h | h
  · left; rintro ⟨h1, h2, h3⟩; exact h ⟨(adj_symm g a b).mp h1, h3, h2⟩
  · exact Or.inr (hF _ _ _ h)

theorem sideForbids_of_B {g : GPathB} {a b r : PathNodeId} (hab : a ≠ b) (har : a ≠ r) (hbr : b ≠ r)
    (h : g.sideForbidsB a b r = true) : SideForbids g (TF g) a b r := by
  unfold sideForbidsB at h
  by_cases ht : (g.adjb a b && g.adjb a r && g.adjb b r) = true
  · rw [if_neg (by simp [ht])] at h
    rw [if_neg (by simp [beq_iff_eq, hab, Ne.symm har, Ne.symm hbr])] at h
    exact Or.inr ⟨hab, h⟩
  · left
    rintro ⟨h1, h2, h3⟩
    unfold Adj at h1 h2 h3
    exact ht (by simp [h1, h2, h3])

theorem B_of_sideForbids {g : GPathB} {a b r : PathNodeId} (hab : a ≠ b) (har : a ≠ r) (hbr : b ≠ r)
    (h : SideForbids g (TF g) a b r) : g.sideForbidsB a b r = true := by
  unfold sideForbidsB
  rcases h with h | h
  · rw [if_pos]
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff]
    unfold Adj at h
    by_cases h1 : g.adjb a b = true <;> by_cases h2 : g.adjb a r = true <;> simp_all
  · by_cases ht : (g.adjb a b && g.adjb a r && g.adjb b r) = true
    · rw [if_neg (by simp [ht]), if_neg (by simp [beq_iff_eq, hab, Ne.symm har, Ne.symm hbr])]
      exact h.2
    · rw [if_pos (by revert ht; cases g.adjb a b <;> cases g.adjb a r <;> cases g.adjb b r <;> simp)]

/-- **`addTrios` escribe todo trío de su lista** (o uno de sus órdenes), salvo los que ya estaban. -/
theorem addTrios_covers (g : GPathB) (i : Idx) (ts : List (PathNodeId × PathNodeId × PathNodeId))
    (t : PathNodeId × PathNodeId × PathNodeId) (ht : t ∈ ts) :
    (g.addTrios i ts).1.trios.any (trioIs t.1 t.2.1 t.2.2) = true ∨ i.deadTrio t.1 t.2.1 t.2.2 = true := by
  unfold addTrios
  -- el acumulador: lo que ya contiene (en algún orden) está escrito
  let step := fun (acc : List (PathNodeId × PathNodeId × PathNodeId) ×
      Std.HashSet (PathNodeId × PathNodeId × PathNodeId)) (u : PathNodeId × PathNodeId × PathNodeId) =>
    if acc.2.contains u || i.deadTrio u.1 u.2.1 u.2.2 then acc
    else (u :: acc.1, acc.2.insertMany (perms u.1 u.2.1 u.2.2))
  have inv : ∀ (l : List (PathNodeId × PathNodeId × PathNodeId))
      (acc : List (PathNodeId × PathNodeId × PathNodeId) × Std.HashSet (PathNodeId × PathNodeId × PathNodeId)),
      (∀ u : PathNodeId × PathNodeId × PathNodeId, acc.2.contains u = true →
        acc.1.any (trioIs u.1 u.2.1 u.2.2) = true) →
      (∀ u : PathNodeId × PathNodeId × PathNodeId, (l.foldl step acc).2.contains u = true →
        (l.foldl step acc).1.any (trioIs u.1 u.2.1 u.2.2) = true) ∧
      (∀ u ∈ l, (l.foldl step acc).1.any (trioIs u.1 u.2.1 u.2.2) = true ∨ i.deadTrio u.1 u.2.1 u.2.2 = true) ∧
      (∀ u : PathNodeId × PathNodeId × PathNodeId, acc.1.any (trioIs u.1 u.2.1 u.2.2) = true →
        (l.foldl step acc).1.any (trioIs u.1 u.2.1 u.2.2) = true) := by
    intro l
    induction l with
    | nil => intro acc hacc; exact ⟨hacc, fun u hu => absurd hu List.not_mem_nil, fun _ h => h⟩
    | cons v vs ih =>
      intro acc hacc
      rw [List.foldl_cons]
      have hstep : (∀ u : PathNodeId × PathNodeId × PathNodeId, (step acc v).2.contains u = true →
            (step acc v).1.any (trioIs u.1 u.2.1 u.2.2) = true) ∧
          ((step acc v).1.any (trioIs v.1 v.2.1 v.2.2) = true ∨ i.deadTrio v.1 v.2.1 v.2.2 = true) ∧
          (∀ u : PathNodeId × PathNodeId × PathNodeId, acc.1.any (trioIs u.1 u.2.1 u.2.2) = true →
            (step acc v).1.any (trioIs u.1 u.2.1 u.2.2) = true) := by
        simp only [step]
        split
        · rename_i hc
          simp only [Bool.or_eq_true] at hc
          refine ⟨hacc, ?_, fun _ h => h⟩
          rcases hc with hc | hc
          · exact Or.inl (hacc v hc)
          · exact Or.inr hc
        · refine ⟨?_, Or.inl (List.any_eq_true.mpr ⟨v, List.mem_cons_self, by obtain ⟨a, b, c⟩ := v; exact trioIs_self a b c⟩), fun u h => by simp [h]⟩
          intro u hu
          rw [Std.HashSet.contains_insertMany_list] at hu
          simp only [Bool.or_eq_true, List.contains_iff_mem] at hu
          rcases hu with hu | hu
          · have := hacc u hu; simp [this]
          · have hp := (mem_perms_iff u.1 u.2.1 u.2.2 v).mp (by simpa using hu)
            simp [hp]
      obtain ⟨r1, r2, r3⟩ := ih (step acc v) hstep.1
      refine ⟨r1, ?_, fun u h => r3 u (hstep.2.2 u h)⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · rcases hstep.2.1 with h | h
        · exact Or.inl (r3 _ h)
        · exact Or.inr h
      · exact r2 u hu
  have := (inv ts ([], {}) (fun u h => by simp at h)).2.1 t ht
  rcases this with h | h
  · left
    show (g.trios ++ (List.foldl step ([], ∅) ts).1.reverse).any (trioIs t.1 t.2.1 t.2.2) = true
    rw [List.any_append, List.any_reverse, h, Bool.or_true]
  · exact Or.inr h

-- ============================================================
-- El join `:on` conserva LiveExt con los tríos reales bajo (★)
-- ============================================================

/-- `joinF` restringido a tríos de tres nodos distintos. -/
def joinFD (T : Int) (g₁ : GPathB) (F₁ : Trios) (g₂ : GPathB) (F₂ : Trios) : Trios := fun a b r =>
  a ≠ b ∧ a ≠ r ∧ b ≠ r ∧ joinF T g₁ F₁ g₂ F₂ a b r

/-- Los tríos de `joinForbid` tienen tres nodos distintos, vivos en algún lado. -/
theorem joinForbid_facts {g₁ g₂ : GPathB} (hns₁ : NoSelf g₁) (hns₂ : NoSelf g₂) (hea₁ : EdgesAlive g₁)
    (hea₂ : EdgesAlive g₂) {t : PathNodeId × PathNodeId × PathNodeId} (ht : t ∈ joinForbid g₁ g₂) :
    (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) ∧
    (t.1 ∈ g₁.alive ∨ t.1 ∈ g₂.alive) ∧ (t.2.1 ∈ g₁.alive ∨ t.2.1 ∈ g₂.alive) ∧ (t.2.2 ∈ g₁.alive ∨ t.2.2 ∈ g₂.alive) := by
  unfold joinForbid at ht
  obtain ⟨e, he, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hr2
  have hne12 : e.1 ≠ e.2 := by
    rcases List.mem_append.mp he with h | h
    · exact hns₁ e h
    · exact hns₂ e h
  have hrn : r ≠ e.1 ∧ (r ∈ g₁.alive ∨ r ∈ g₂.alive) := by
    rcases List.mem_append.mp hr1 with h | h
    · have := (idx_mem_nbrs g₁ e.1 r).mp h; exact ⟨this.1, Or.inl this.2.1⟩
    · have := (idx_mem_nbrs g₂ e.1 r).mp h; exact ⟨this.1, Or.inr this.2.1⟩
  have hal : (e.1 ∈ g₁.alive ∨ e.1 ∈ g₂.alive) ∧ (e.2 ∈ g₁.alive ∨ e.2 ∈ g₂.alive) := by
    rcases List.mem_append.mp he with h | h
    · have := alive_of_hasEdge hea₁ (hasEdge_of_mem h); exact ⟨Or.inl this.1, Or.inl this.2⟩
    · have := alive_of_hasEdge hea₂ (hasEdge_of_mem h); exact ⟨Or.inr this.1, Or.inr this.2⟩
  exact ⟨⟨hne12, fun h => hrn.1 h.symm, fun h => hr2.1.1.1 h.symm⟩, hal.1, hal.2, hrn.2⟩

/-- **El join `:on` conserva `LiveExt` con los tríos reales, bajo (★) con los tríos reales de los lados.** -/
theorem liveExt_joinOn {g₁ g₂ : GPathB} (h₁ : LiveExt g₁ (TF g₁)) (h₂ : LiveExt g₂ (TF g₂))
    (hcs : g₁.current_step = g₂.current_step) (hside : JoinSide g₁ (TF g₁) g₂ (TF g₂))
    (hdocs₁ : AliveDocs g₁) (hdocs₂ : AliveDocs g₂) (hli₁ : LinksInv g₁) (hli₂ : LinksInv g₂)
    (hea₁ : EdgesAlive g₁) (hea₂ : EdgesAlive g₂) (hr₁ : RootNone g₁) (hr₂ : RootNone g₂)
    (hnd₁ : NodupIds g₁) (hnd₂ : NodupIds g₂) (hns₁ : NoSelf g₁) (hns₂ : NoSelf g₂)
    (hab₁ : AliveBelow g₁) (hab₂ : AliveBelow g₂) :
    LiveExt (joinOn g₁ g₂) (TF (joinOn g₁ g₂)) := by
  let U := join g₁ g₂
  let T := g₁.current_step
  have hcsU : U.current_step = T := rfl
  have hJ := liveExt_join h₁ h₂ hcs hside
  have hJD : LiveExt U (joinFD T g₁ (TF g₁) g₂ (TF g₂)) :=
    liveExt_congrD (fun _ _ _ a b c h => ⟨a, b, c, h⟩) (fun _ _ _ _ _ _ h => h.2.2.2) hJ
  obtain ⟨T', hT⟩ := joinOn_eq g₁ g₂
  have hsub : Sub (joinOn g₁ g₂) U := by rw [hT]; exact (shrinks_setT U T').1
  have hadjU : ∀ x y, (joinOn g₁ g₂).Adj x y → U.Adj x y := fun x y h => by rw [hT] at h; exact h
  have hrU : RootNone U := fun x hx hx0 =>
    ((alive_join g₁ g₂ x).mp hx).elim (fun h => hr₁ x h hx0) (fun h => hr₂ x h hx0)
  -- los tríos guardados por el join
  let u : GPathB := { join g₁ g₂ with trios := [] }
  have htr : (joinOn g₁ g₂).trios = (u.addTrios (Idx.of u) (joinForbid g₁ g₂)).1.trios := rfl
  have below : ∀ x, x ∈ g₁.alive ∨ x ∈ g₂.alive → x.id.step < T := by
    intro x hx; rcases hx with hx | hx
    · exact hab₁ x hx
    · have := hab₂ x hx; rw [← hcs] at this; exact this
  refine liveExt_of_keep' hJD (Machine.aliveDocs_join hdocs₁ hdocs₂) (linksInv_join hli₁ hli₂ hea₁ hea₂) hrU
    (nodupIds_join hnd₁ hnd₂) (fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩) hsub ?_ ?_
  · -- en los triángulos de la unión, lo que cortan los dos lados está guardado
    intro x y z hxy hxz hyz ⟨nxy, nxz, nyz, _, _, _, s1, s2⟩
    have exy := hasEdge_of_adj (hadjU _ _ hxy) nxy
    have exz := hasEdge_of_adj (hadjU _ _ hxz) nxz
    have eyz := hasEdge_of_adj (hadjU _ _ hyz) nyz
    -- la arista x–y está en un lado, en algún orden
    obtain ⟨e, he, hj⟩ := List.any_eq_true.mp exy
    have he' : e ∈ g₁.edges ++ g₂.edges := by
      rcases List.mem_append.mp he with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_filter.mp h).1
    -- `z` es vecino de `e.1` en algún lado, y `e.2`–`z` es arista en algún lado
    have nbr_of : ∀ a, a ≠ z → U.hasEdge a z = true →
        z ∈ (Idx.of g₁).nbrs a ++ (Idx.of g₂).nbrs a ∧ ((Idx.of g₁).hasEdge a z || (Idx.of g₂).hasEdge a z) = true := by
      intro a haz he2
      obtain ⟨e', he2', hj'⟩ := List.any_eq_true.mp he2
      rcases List.mem_append.mp he2' with h | h
      · have hE : g₁.hasEdge a z = true := List.any_eq_true.mpr ⟨e', h, hj'⟩
        refine ⟨List.mem_append_left _ ((idx_mem_nbrs g₁ a z).mpr ⟨fun h => haz h.symm, (hea₁ a z (by
          unfold Adj adjb; simp [hE])).2, hE⟩), by simp [idx_hasEdge, hE]⟩
      · have hE : g₂.hasEdge a z = true := List.any_eq_true.mpr ⟨e', (List.mem_filter.mp h).1, hj'⟩
        refine ⟨List.mem_append_right _ ((idx_mem_nbrs g₂ a z).mpr ⟨fun h => haz h.symm, (hea₂ a z (by
          unfold Adj adjb; simp [hE])).2, hE⟩), by simp [idx_hasEdge, hE]⟩
    have hcov : ∃ t ∈ joinForbid g₁ g₂, trioIs x y z t = true := by
      rcases (joins_iff x y e).mp hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨(e.1, e.2, z), ?_, by rw [h1, h2]; exact trioIs_self x y z⟩
        unfold joinForbid
        refine List.mem_flatMap.mpr ⟨e, he', List.mem_map.mpr ⟨z, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩⟩
        · rw [h1]; exact (nbr_of x nxz exz).1
        · rw [h1, h2]
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, idx_sideForbids]
          exact ⟨⟨⟨fun h => nyz h.symm, by rw [← adj_symm] at hyz; exact (nbr_of y nyz eyz).2⟩,
            B_of_sideForbids nxy nxz nyz s1⟩, B_of_sideForbids nxy nxz nyz s2⟩
      · refine ⟨(e.1, e.2, z), ?_, by rw [h1, h2]; exact trioIs_swap12 (trioIs_self y x z)⟩
        unfold joinForbid
        refine List.mem_flatMap.mpr ⟨e, he', List.mem_map.mpr ⟨z, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩⟩
        · rw [h1]; exact (nbr_of y nyz eyz).1
        · rw [h1, h2]
          have tsw : ∀ a b r, TF g₁ b a r → TF g₁ a b r := fun _ _ _ h => tF_swap12 h
          have tsw2 : ∀ a b r, TF g₂ b a r → TF g₂ a b r := fun _ _ _ h => tF_swap12 h
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, idx_sideForbids]
          exact ⟨⟨⟨fun h => nxz h.symm, (nbr_of x nxz exz).2⟩,
            B_of_sideForbids (Ne.symm nxy) nyz nxz (sideForbids_swap12 tsw s1)⟩,
            B_of_sideForbids (Ne.symm nxy) nyz nxz (sideForbids_swap12 tsw2 s2)⟩
    obtain ⟨t, ht, hti⟩ := hcov
    refine ⟨nxy, ?_⟩
    unfold deadTrio
    rw [Bool.and_eq_true]
    refine ⟨by rw [hT]; exact exy, ?_⟩
    rw [htr]
    rcases addTrios_covers u (Idx.of u) _ t ht with h | h
    · obtain ⟨t', ht', hti'⟩ := List.any_eq_true.mp h
      -- `trioIs x y z t` y `trioIs t t'`: `t'` es un orden de `{x, y, z}`
      refine List.any_eq_true.mpr ⟨t', ht', ?_⟩
      obtain ⟨a, b, c⟩ := t
      simp only [trioIs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hti
      rcases hti with (((((⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) |
        ⟨⟨h1, h2⟩, h3⟩) <;> subst h1 <;> subst h2 <;> subst h3 <;>
        (obtain ⟨p, q, w⟩ := t'; simp only [trioIs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hti' ⊢;
         rcases hti' with (((((⟨⟨k1, k2⟩, k3⟩ | ⟨⟨k1, k2⟩, k3⟩) | ⟨⟨k1, k2⟩, k3⟩) | ⟨⟨k1, k2⟩, k3⟩) |
           ⟨⟨k1, k2⟩, k3⟩) | ⟨⟨k1, k2⟩, k3⟩) <;> subst k1 <;> subst k2 <;> subst k3 <;> simp)
    · exfalso
      rw [idx_deadTrio] at h
      unfold deadTrio at h
      simp [u] at h
  · -- una camarilla de la unión que esquiva lo que cortan los dos lados esquiva lo guardado
    intro D hc hA
    refine ⟨by rw [hT]; exact ⟨hc.step, hc.alive, hc.adj, hc.root, hc.node⟩, ?_⟩
    intro p q s h0 h1 h2 h3 h4 h5 ⟨_, hd⟩
    unfold deadTrio at hd
    rw [Bool.and_eq_true, htr] at hd
    obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd.2
    rcases mem_addTrios u _ _ t ht with h | h
    · exact absurd h (List.not_mem_nil)
    · obtain ⟨dt, a1, a2, a3⟩ := joinForbid_facts hns₁ hns₂ hea₁ hea₂ h
      obtain ⟨f1, f2⟩ := mem_joinForbid h
      obtain ⟨c1, c2, c3⟩ := trioIs_mem hti
      have hcsD : (joinOn g₁ g₂).current_step = U.current_step := by rw [hT]
      rw [hcsD] at h1 h3 h5
      have idx : ∀ x, (x = D p ∨ x = D q ∨ x = D s) → ∃ i, 0 ≤ i ∧ i < U.current_step ∧ D i = x := by
        intro x hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨p, h0, h1, rfl⟩
        · exact ⟨q, h2, h3, rfl⟩
        · exact ⟨s, h4, h5, rfl⟩
      obtain ⟨i1, i10, i11, hi1⟩ := idx _ c1
      obtain ⟨i2, i20, i21, hi2⟩ := idx _ c2
      obtain ⟨i3, i30, i31, hi3⟩ := idx _ c3
      apply hA i1 i2 i3 i10 i11 i20 i21 i30 i31
      rw [hi1, hi2, hi3]
      exact ⟨dt.1, dt.2.1, dt.2.2, below _ a1, below _ a2, below _ a3,
        sideForbids_of_B dt.1 dt.2.1 dt.2.2 f1, sideForbids_of_B dt.1 dt.2.1 dt.2.2 f2⟩

end GPathB

end AbsSatBingo.Model
