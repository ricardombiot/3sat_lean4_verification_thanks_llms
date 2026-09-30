-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnLive.lean
import AbsSatBingo.Model.ForbidOnLine
import AbsSatBingo.Model.LiveUp

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

end GPathB

end AbsSatBingo.Model
