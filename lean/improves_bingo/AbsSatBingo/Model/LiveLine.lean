-- lean/improves_bingo/AbsSatBingo/Model/LiveLine.lean
import AbsSatBingo.Model.LiveJoin

/-!
# La inducción de línea con pins extra (etapa 2: el paso abstracto)

Cada estado de la línea lleva una **familia** de relaciones de tríos, una por lista de pins `R`: la relación de "la
máquina con los requisitos `R` añadidos".

* llegada `up (filterAll D reqs) d`: `R ↦ F (reqs ++ R)` (el UP no hereda tríos: `liveExt_addNode_same`);
* unión `join A B`: `R ↦ joinF` de los dos lados fijados por `R` (si los dos fijados son válidos; si no, la del lado
  válido).

**`Good g F`**: contabilidad (`SInvB`), paso `≥ 2`, y para todo `R` con `pinF g R` válido, `LiveExt (pinF g R) (F R)`
con `F R` por debajo del paso y sin tríos degenerados.

* **`good_arrival`**: `Good D F ⟹ Good (up (filterAll D reqs) d) (F (reqs ++ ·))`, por `arrival_pin_commute`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

open Machine (Below)

/-- Una familia de relaciones de tríos, una por lista de pins. -/
abbrev FamT := List NodeId → Trios

/-- **El invariante de un estado de la línea.** -/
structure Good (g : GPathB) (F : FamT) : Prop where
  inv   : SInvB g
  pos   : 2 ≤ g.current_step
  live  : ∀ R, (pinF g R).isValid = true → LiveExt (pinF g R) (F R)
  below : ∀ R, FBelow (F R) g.current_step
  nodeg : ∀ R, NoDeg (F R)

theorem sInvB_join {A B : GPathB} (hA : SInvB A) (hB : SInvB B) (hcs : A.current_step = B.current_step) :
    SInvB (join A B) :=
  ⟨linksInv_join hA.links hB.links hA.edges hB.edges, nodupIds_join hA.nodup hB.nodup, below_join hA.below hB.below hcs,
   aboveZero_join hA.zero hB.zero, linksStep_join hA.lstep hB.lstep, edgesAlive_join hA.edges hB.edges,
   fun x hx hx0 => ((alive_join A B x).mp hx).elim (fun h => hA.root x h hx0) (fun h => hB.root x h hx0)⟩

theorem fBelow_mono {F : Trios} {T T' : Int} (h : FBelow F T) (hT : T ≤ T') : FBelow F T' :=
  fun x y z hf => by obtain ⟨a, b, c⟩ := h x y z hf; exact ⟨by omega, by omega, by omega⟩

variable {d : NodeId} {title : String} {forb : PathNodeId → Bool}

theorem sInvB_up {Z : GPathB} (hZ : SInvB Z) (hd : d.step = Z.current_step) (hd0 : 0 ≤ d.step) :
    SInvB (Z.up d title forb) := by
  unfold up
  split
  · exact sInvB_review (sInvB_addNode hZ hd hd0)
  · exact hZ

/-- **La llegada es `Good`** con la familia del remitente desplazada por sus requisitos. -/
theorem good_arrival {D : GPathB} {F : FamT} {reqs : List NodeId} (hD : Good D F) (hd : d.step = D.current_step)
    (hvY : (D.filterAll reqs).isValid = true) :
    Good ((D.filterAll reqs).up d title forb) (fun R => F (reqs ++ R)) := by
  have hcsY : (D.filterAll reqs).current_step = D.current_step := (shrinks_filterAll D reqs).1.step
  have hcsA : ((D.filterAll reqs).up d title forb).current_step = D.current_step + 1 := by
    rw [step_up hvY, hcsY]
  refine ⟨sInvB_up (sInvB_filterAll hD.inv reqs) (by rw [hcsY]; exact hd) (by have := hD.pos; omega),
    by rw [hcsA]; have := hD.pos; omega, fun R hvA => ?_, fun R => by rw [hcsA]; exact fBelow_mono (hD.below _) (by omega),
    fun R => hD.nodeg _⟩
  obtain ⟨hvX, halive, hadj⟩ := arrival_pin_commute (title := title) (forb := forb) hD.inv (by have := hD.pos; omega)
    hd hvA
  have hiX := sInvB_pinF hD.inv (reqs ++ R)
  have hcsX : (pinF D (reqs ++ R)).current_step = D.current_step := step_pinF D _
  have hdX : d.step = (pinF D (reqs ++ R)).current_step := by rw [hcsX]; exact hd
  have hiXa : SInvB ((pinF D (reqs ++ R)).addNode d title forb) := sInvB_addNode hiX hdX (by have := hD.pos; omega)
  have hiXd := sInvB_dirty hiXa true
  have hda : DocsAlive (pinF D (reqs ++ R)) := docsAlive_review hvX (Or.inr rfl)
  have hext := hD.live (reqs ++ R) hvX
  have hextA := liveExt_addNode_same (title := title) (forb := forb) hext hiX.docs hiX.below hda hdX
    (by rw [hcsX]; exact hD.below _)
  have hextB := liveExt_review (liveExt_dirty hiXa.links hextA true) hiXd.docs hiXd.links hiXd.root hiXd.nodup
    (hD.nodeg _)
  refine liveExt_congr ?_ halive hadj (sInvB_pinF (sInvB_up (sInvB_filterAll hD.inv reqs)
    (by rw [hcsY]; exact hd) (by have := hD.pos; omega)) R).links (sInvB_review hiXd).links hextB
  rw [step_pinF, hcsA]
  show D.current_step + 1 = ((({ (pinF D (reqs ++ R)).addNode d title forb with dirty := true } : GPathB)).review).current_step
  rw [(shrinks_review _).1.step]
  show D.current_step + 1 = (pinF D (reqs ++ R)).current_step + 1
  rw [hcsX]

-- ============================================================
-- LiveExt solo mira tríos de nodos distintos
-- ============================================================

theorem liveChain_congrF {g : GPathB} {F G : Trios}
    (h : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → F x y z → G x y z) {C : Int → PathNodeId} {j : Int}
    (hC : LiveChain g G C j) : LiveChain g F C j := by
  refine ⟨hC.chain, fun a b c ha hab hbc hc' hs => hC.live a b c ha hab hbc hc' ?_⟩
  have sa := (hC.chain.node a ha (by omega)).1
  have sb := (hC.chain.node b (by omega) (by omega)).1
  have sc := (hC.chain.node c (by omega) hc').1
  have n1 : C a ≠ C b := fun e => by rw [e] at sa; omega
  have n2 : C a ≠ C c := fun e => by rw [e] at sa; omega
  have n3 : C b ≠ C c := fun e => by rw [e] at sb; omega
  unfold Sym at hs ⊢
  rcases hs with h' | h' | h' | h' | h' | h'
  · exact Or.inl (h _ _ _ n1 n2 n3 h')
  · exact Or.inr (Or.inl (h _ _ _ n2 n1 (Ne.symm n3) h'))
  · exact Or.inr (Or.inr (Or.inl (h _ _ _ (Ne.symm n1) n3 n2 h')))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h _ _ _ n3 (Ne.symm n1) (Ne.symm n2) h'))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h _ _ _ (Ne.symm n2) (Ne.symm n3) n1 h')))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h _ _ _ (Ne.symm n3) (Ne.symm n2) (Ne.symm n1) h')))))

/-- **`LiveExt` solo depende de la relación en tríos de nodos distintos.** -/
theorem liveExt_congrF {g : GPathB} {F G : Trios}
    (h : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → (F x y z ↔ G x y z)) (hext : LiveExt g F) : LiveExt g G := by
  intro C j hC hj1 hjt
  obtain ⟨C', hC', hag⟩ := hext C j (liveChain_congrF (fun x y z a b c hf => (h x y z a b c).mp hf) hC) hj1 hjt
  exact ⟨C', liveChain_congrF (fun x y z a b c hf => (h x y z a b c).mpr hf) hC', hag⟩

-- ============================================================
-- El join
-- ============================================================

/-- `joinF` solo en tríos de nodos distintos (Julia solo prohíbe esos). -/
def joinFD (T : Int) (A : GPathB) (FA : Trios) (B : GPathB) (FB : Trios) : Trios := fun x y z =>
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ joinF T A FA B FB x y z

/-- Los mismos vivos y las mismas aristas entre vivos. -/
def SameGraph (U V : GPathB) : Prop :=
  (∀ q, q ∈ U.alive ↔ q ∈ V.alive) ∧ (∀ y w, y ∈ U.alive → w ∈ U.alive → (U.Adj y w ↔ V.Adj y w))

/-- La unión de los lados fijados (o el lado fijado válido, si solo uno lo es). -/
def pinJoin (A B : GPathB) (R : List NodeId) : GPathB :=
  if (pinF A R).isValid then (if (pinF B R).isValid then join (pinF A R) (pinF B R) else pinF A R) else pinF B R

/-- La familia de la unión. -/
def joinFam (A B : GPathB) (FA FB : FamT) : FamT := fun R =>
  if (pinF A R).isValid then
    (if (pinF B R).isValid then joinFD (pinF A R).current_step (pinF A R) (FA R) (pinF B R) (FB R) else FA R)
  else FB R

/-- **`PinJoinSplit` para toda lista de pins** (con el lado válido si solo uno lo es): fijar la unión da la unión de
los lados fijados. Es `SecSplit` con pins; medido: 0 diferencias (`probe_pinjoin.jl`). -/
def PinJoinSplitAll (A B : GPathB) : Prop :=
  ∀ R, (pinF (join A B) R).isValid = true →
    SameGraph (pinF (join A B) R) (pinJoin A B R) ∧ ((pinF A R).isValid = true ∨ (pinF B R).isValid = true)

/-- **La unión es `Good`**, bajo `CrossClosed` entre los lados fijados, cimas separadas y `PinJoinSplitAll`. -/
theorem good_join {A B : GPathB} {FA FB : FamT} (hA : Good A FA) (hB : Good B FB)
    (hcs : A.current_step = B.current_step)
    (htopA : ∀ t ∈ A.alive, t.id.step = A.current_step - 1 → t ∉ B.alive)
    (htopB : ∀ t ∈ B.alive, t.id.step = B.current_step - 1 → t ∉ A.alive)
    (hcc : ∀ R, CrossClosed (pinF A R) (FA R) (pinF B R) (FB R) ∧ CrossClosed (pinF B R) (FB R) (pinF A R) (FA R))
    (hsplit : PinJoinSplitAll A B) : Good (join A B) (joinFam A B FA FB) := by
  have hcsU : (join A B).current_step = A.current_step := rfl
  have hiU := sInvB_join hA.inv hB.inv hcs
  refine ⟨hiU, hA.pos, fun R hvU => ?_, fun R => ?_, fun R => ?_⟩
  · obtain ⟨hsame, hone⟩ := hsplit R hvU
    have hiUR := sInvB_pinF hiU R
    have hiA := sInvB_pinF hA.inv R
    have hiB := sInvB_pinF hB.inv R
    have hcsA : (pinF A R).current_step = A.current_step := step_pinF A R
    have hcsB : (pinF B R).current_step = B.current_step := step_pinF B R
    have hcsUR : (pinF (join A B) R).current_step = A.current_step := by rw [step_pinF]; rfl
    unfold joinFam
    unfold pinJoin at hsame
    by_cases hvA : (pinF A R).isValid = true <;> by_cases hvB : (pinF B R).isValid = true
    · rw [if_pos hvA, if_pos hvB] at hsame ⊢
      have hside : JoinSide (pinF A R) (FA R) (pinF B R) (FB R) :=
        joinSide_of_crossClosed (by rw [hcsA, hcsB, hcs])
          (fun t ht hts hb => htopA t ((sub_pinF A R).alive t ht) (by rw [hts, hcsA])
            ((sub_pinF B R).alive t hb))
          (fun t ht hts ha => htopB t ((sub_pinF B R).alive t ht) (by rw [hts, hcsB])
            ((sub_pinF A R).alive t ha))
          hiA.edges hiB.edges hiA.links hiB.links (hcc R).1 (hcc R).2
      have hJ := liveExt_join (hA.live R hvA) (hB.live R hvB) (by rw [hcsA, hcsB, hcs]) hside
      have hJ' := liveExt_congrF (G := joinFD (pinF A R).current_step (pinF A R) (FA R) (pinF B R) (FB R))
        (fun x y z a b c => ⟨fun h => ⟨a, b, c, h⟩, fun h => h.2.2.2⟩) hJ
      exact liveExt_congr (by rw [hcsUR]; show A.current_step = (pinF A R).current_step; rw [hcsA]) hsame.1 hsame.2 hiUR.links
        (sInvB_join hiA hiB (by rw [hcsA, hcsB, hcs])).links hJ'
    · rw [if_pos hvA, if_neg hvB] at hsame ⊢
      exact liveExt_congr (by rw [hcsUR, hcsA]) hsame.1 hsame.2 hiUR.links hiA.links (hA.live R hvA)
    · rw [if_neg hvA] at hsame ⊢
      exact liveExt_congr (by rw [hcsUR, hcsB, hcs]) hsame.1 hsame.2 hiUR.links hiB.links (hB.live R hvB)
    · exact absurd hone (by simp [hvA, hvB])
  · unfold joinFam
    split
    · split
      · intro x y z ⟨_, _, _, hj⟩
        exact fBelow_joinF _ _ _ _ _ x y z hj |> fun ⟨a, b, c⟩ => by
          rw [step_pinF] at a b c; exact ⟨a, b, c⟩
      · exact hA.below R
    · rw [hcsU, hcs]; exact hB.below R
  · unfold joinFam
    split
    · split
      · exact fun x y z ⟨a, b, c, _⟩ => ⟨a, b, c⟩
      · exact hA.nodeg R
    · exact hB.nodeg R

-- ============================================================
-- CrossClosed en la forma de la conmutación: la fila nueva revisada sobre el remitente fijado
-- ============================================================

/-- La llegada en la forma de la conmutación. -/
def upR (X : GPathB) (d : NodeId) (title : String) (forb : PathNodeId → Bool) : GPathB :=
  ({ X.addNode d title forb with dirty := true } : GPathB).review

theorem sub_upR (X : GPathB) (d : NodeId) (title : String) (forb : PathNodeId → Bool) :
    Sub (upR X d title forb) (X.addNode d title forb) := (shrinks_review _).1.trans (shrinks_dirty _ true).1

theorem step_upR (X : GPathB) (d : NodeId) (title : String) (forb : PathNodeId → Bool) :
    (upR X d title forb).current_step = X.current_step + 1 := (sub_upR X d title forb).step

/-- Una cadena de `upR X d`, sin su cima, es una cadena de `X`. -/
theorem spineChain_upR {X : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool} (hX : SInvB X)
    (hd : d.step = X.current_step) {C : Int → PathNodeId} {j : Int} (hC : SpineChain (upR X d title forb) C j) :
    SpineChain X C j := by
  have hsA := sub_upR X d title forb
  have hcsA := step_upR X d title forb
  have hndA : NodupIds (X.addNode d title forb) := nodupIds_addNode hX.nodup hX.below hd
  have hn := fun k (h1 : j ≤ k) (h2 : k ≤ X.current_step - 1) => hC.node k h1 (by rw [hcsA]; omega)
  have hold : ∀ k, j ≤ k → k ≤ X.current_step - 1 → C k ∈ X.alive := by
    intro k h1 h2
    obtain ⟨hs, ha⟩ := hn k h1 h2
    rcases alive_addNode_cases hX.docs hX.below hd (hsA.alive _ ha) with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · omega
  refine ⟨fun k h1 h2 => ⟨(hn k h1 h2).1, hold k h1 h2⟩, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩
  · exact adj_addNode_old hd (by rw [(hn k h1 h2).1]; omega) (by rw [(hn l h3 h4).1]; omega)
      (hsA.adj _ _ (hC.adj k l h1 (by rw [hcsA]; omega) h3 (by rw [hcsA]; omega)))
  · obtain ⟨n, hn', hp⟩ := hC.link k h1 (by rw [hcsA]; omega)
    obtain ⟨m, hm, hpm⟩ := node?_sub hsA hndA hn'
    rw [node?_addNode_old hd (by rw [(hn k (by omega) h2).1]; omega)] at hm
    cases hy : X.node? (C k) with
    | none => rw [hy] at hm; cases hm
    | some m0 => rw [hy] at hm; cases hm; exact ⟨m0, rfl, hpm _ hp⟩

/-- **`CrossClosed` pasa de los remitentes fijados a sus llegadas** (en la forma de la conmutación). -/
theorem crossClosed_upR {X₀ X₁ : GPathB} {F₀ F₁ : Trios} {d₀ d₁ : NodeId} {t₀ t₁ : String}
    {f₀ f₁ : PathNodeId → Bool} (hc : CrossClosed X₀ F₀ X₁ F₁) (hB : FBelow F₀ X₀.current_step)
    (hX₀ : SInvB X₀) (hcs : X₀.current_step = X₁.current_step)
    (hd₀ : d₀.step = X₀.current_step) (hd₁ : d₁.step = X₁.current_step) :
    CrossClosed (upR X₀ d₀ t₀ f₀) F₀ (upR X₁ d₁ t₁ f₁) F₁ := by
  intro C j hC p q r h1 h2 h3 h4 h5 h6 hf
  have hcsA := step_upR X₀ d₀ t₀ f₀
  obtain ⟨sp, sq, sr⟩ := hB _ _ _ hf
  rw [(hC.node p h1 h2).1] at sp; rw [(hC.node q h3 h4).1] at sq; rw [(hC.node r h5 h6).1] at sr
  have hs := hc C j (spineChain_upR hX₀ hd₀ hC) p q r h1 (by omega) h3 (by omega) h5 (by omega) hf
  have hsub := sub_upR X₁ d₁ t₁ f₁
  have hstep := fun k (h1 : j ≤ k) (h2 : k ≤ (upR X₀ d₀ t₀ f₀).current_step - 1) => (hC.node k h1 h2).1
  have hadj : ∀ u v : Int, j ≤ u → u < X₀.current_step → j ≤ v → v < X₀.current_step →
      (upR X₁ d₁ t₁ f₁).Adj (C u) (C v) → X₁.Adj (C u) (C v) := by
    intro u v hu1 hu2 hv1 hv2 ha
    exact adj_addNode_old hd₁ (by rw [hstep u hu1 (by omega), ← hcs]; exact hu2)
      (by rw [hstep v hv1 (by omega), ← hcs]; exact hv2) (hsub.adj _ _ ha)
  rcases hs with hn | hF
  · exact Or.inl fun ⟨a, b, c⟩ => hn ⟨hadj p q h1 (by omega) h3 (by omega) a, hadj p r h1 (by omega) h5 (by omega) b,
      hadj q r h3 (by omega) h5 (by omega) c⟩
  · exact Or.inr hF

end GPathB

end AbsSatBingo.Model
