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
    (hcc : ∀ R, (pinF A R).isValid = true → (pinF B R).isValid = true →
      CrossClosed (pinF A R) (FA R) (pinF B R) (FB R) ∧ CrossClosed (pinF B R) (FB R) (pinF A R) (FA R))
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
          hiA.edges hiB.edges hiA.links hiB.links (hcc R hvA hvB).1 (hcc R hvA hvB).2
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

/-- `CrossClosed` entre dos estados con los mismos vivos y aristas que otros dos. -/
theorem crossClosed_same {A A' B B' : GPathB} {FA FB : Trios} (hc : CrossClosed A FA B FB)
    (hcsA : A'.current_step = A.current_step) (hA : SameGraph A' A) (hB : SameGraph B' B)
    (hkA' : LinksCompat A') (hliA : LinksInv A) (heaB' : EdgesAlive B') : CrossClosed A' FA B' FB :=
  crossClosed_congr hc hcsA (fun q hq => (hA.1 q).mp hq) (fun y w hy hw h => (hA.2 y w hy hw).mp h) hkA' hliA
    (fun y w h => (hB.2 y w (heaB' _ _ h).1 (heaB' _ _ h).2).mp h)

variable {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **`CrossClosed` entre las llegadas fijadas de un join**, desde `CrossClosed` entre los remitentes fijados con los
requisitos del UP añadidos. -/
theorem cc_arrivals {D₀ D₁ : GPathB} {F₀ F₁ : FamT} {reqs : List NodeId} (hD₀ : Good D₀ F₀) (hD₁ : Good D₁ F₁)
    (hcs : D₀.current_step = D₁.current_step) (hd : d.step = D₀.current_step)
    (hcc : ∀ R, (pinF D₀ R).isValid = true → (pinF D₁ R).isValid = true →
      CrossClosed (pinF D₀ R) (F₀ R) (pinF D₁ R) (F₁ R)) (R : List NodeId)
    (hv₀ : (pinF ((D₀.filterAll reqs).up d title forb) R).isValid = true)
    (hv₁ : (pinF ((D₁.filterAll reqs).up d title forb) R).isValid = true) :
    CrossClosed (pinF ((D₀.filterAll reqs).up d title forb) R) (F₀ (reqs ++ R))
      (pinF ((D₁.filterAll reqs).up d title forb) R) (F₁ (reqs ++ R)) := by
  have hd₁ : d.step = D₁.current_step := by rw [← hcs]; exact hd
  obtain ⟨hvX₀, ha₀, hj₀⟩ := arrival_pin_commute (title := title) (forb := forb) hD₀.inv (by have := hD₀.pos; omega) hd hv₀
  obtain ⟨hvX₁, ha₁, hj₁⟩ := arrival_pin_commute (title := title) (forb := forb) hD₁.inv (by have := hD₁.pos; omega) hd₁ hv₁
  have hcX := hcc (reqs ++ R) hvX₀ hvX₁
  have hcsX₀ : (pinF D₀ (reqs ++ R)).current_step = D₀.current_step := step_pinF _ _
  have hcsX₁ : (pinF D₁ (reqs ++ R)).current_step = D₁.current_step := step_pinF _ _
  have hup := crossClosed_upR (d₀ := d) (d₁ := d) (t₀ := title) (t₁ := title) (f₀ := forb) (f₁ := forb) hcX
    (by rw [hcsX₀]; exact hD₀.below _) (sInvB_pinF hD₀.inv _) (by rw [hcsX₀, hcsX₁, hcs])
    (by rw [hcsX₀]; exact hd) (by rw [hcsX₁]; exact hd₁)
  have hiA₀ := sInvB_pinF (sInvB_up (sInvB_filterAll hD₀.inv reqs) (d := d) (title := title) (forb := forb)
    (by rw [(shrinks_filterAll D₀ reqs).1.step]; exact hd) (by have := hD₀.pos; omega)) R
  have hiA₁ := sInvB_pinF (sInvB_up (sInvB_filterAll hD₁.inv reqs) (d := d) (title := title) (forb := forb)
    (by rw [(shrinks_filterAll D₁ reqs).1.step]; exact hd₁) (by have := hD₁.pos; omega)) R
  have hiX₀ : SInvB (upR (pinF D₀ (reqs ++ R)) d title forb) :=
    sInvB_review (sInvB_dirty (sInvB_addNode (sInvB_pinF hD₀.inv _) (by rw [hcsX₀]; exact hd)
      (by have := hD₀.pos; omega)) true)
  have hvY₀ : (D₀.filterAll reqs).isValid = true := valid_of_up (isValid_of_sub (sub_pinF _ R) hv₀)
  refine crossClosed_same hup ?_ ⟨ha₀, hj₀⟩ ⟨ha₁, hj₁⟩ hiA₀.links.2.2 hiX₀.links hiA₁.edges
  rw [step_pinF, step_up hvY₀, (shrinks_filterAll D₀ reqs).1.step, step_upR, hcsX₀]

-- ============================================================
-- Más pins: un estado más pequeño
-- ============================================================

/-- **Fijar más da un estado dentro**: el estado cerrado de `pinF g (L ++ R)` es una estructura cerrada de `g` que
concuerda con `R`, así que queda en `pinF g R` (vivos y aristas). -/
theorem pinF_append_sub {g : GPathB} {L R : List NodeId} (hg : SInvB g) (hcs : 2 ≤ g.current_step)
    (hv : (pinF g (L ++ R)).isValid = true) :
    (∀ q ∈ (pinF g (L ++ R)).alive, q ∈ (pinF g R).alive) ∧
    (∀ y w, y ∈ (pinF g (L ++ R)).alive → w ∈ (pinF g (L ++ R)).alive → (pinF g (L ++ R)).Adj y w →
      (pinF g R).Adj y w) := by
  have hc := closedState_pinF hg hv hcs
  have hs := secStruct_of_sub (sub_pinF g _) hg.nodup hc
  have hp := secStruct_pinF hs R (fun b hb y hy hys =>
    pinned_pinF hg.docs hv b (List.mem_append_right _ hb) y hy hys)
  exact ⟨fun q hq => hp.alive hq, fun y w hy hw ha => hp.adj ⟨hy, hw, ha⟩⟩

/-- **Fijar más (como conjunto) da un estado dentro.** -/
theorem pinF_sub_superset {g : GPathB} {R R' : List NodeId} (hRR : ∀ b ∈ R, b ∈ R') (hg : SInvB g)
    (hcs : 2 ≤ g.current_step) (hv : (pinF g R').isValid = true) :
    (∀ q ∈ (pinF g R').alive, q ∈ (pinF g R).alive) ∧
    (∀ y w, (pinF g R').Adj y w → (pinF g R).Adj y w) := by
  have hc := closedState_pinF hg hv hcs
  have hs := secStruct_of_sub (sub_pinF g _) hg.nodup hc
  have hp := secStruct_pinF hs R (fun b hb y hy hys => pinned_pinF hg.docs hv b (hRR b hb) y hy hys)
  have hea := (sInvB_pinF hg R').edges
  exact ⟨fun q hq => hp.alive hq, fun y w ha => hp.adj ⟨(hea _ _ ha).1, (hea _ _ ha).2, ha⟩⟩

/-- La validez de un estado solo depende de sus vivos. -/
theorem isValid_of_alive {h g : GPathB} (hcs : h.current_step = g.current_step)
    (ha : ∀ q ∈ h.alive, q ∈ g.alive) (hv : h.isValid = true) : g.isValid = true := by
  unfold isValid at hv ⊢
  rw [← hcs]
  rw [List.all_eq_true] at hv ⊢
  intro k hk
  obtain ⟨q, hq, hqk⟩ := List.any_eq_true.mp (hv k hk)
  exact List.any_eq_true.mpr ⟨q, ha q hq, hqk⟩

/-- **Al fijar más, la validez solo se pierde.** -/
theorem valid_pinF_mono {g : GPathB} {R R' : List NodeId} (hRR : ∀ b ∈ R, b ∈ R') (hg : SInvB g)
    (hcs : 2 ≤ g.current_step) (hv : (pinF g R').isValid = true) : (pinF g R).isValid = true :=
  isValid_of_alive (by rw [step_pinF, step_pinF]) (pinF_sub_superset hRR hg hcs hv).1 hv

-- ============================================================
-- FamMono: la familia crece al fijar más
-- ============================================================

/-- **`FamMono g F`**: lo que la relación corta con los pins `R`, la relación con más pins `R' ⊇ R` lo sigue cortando en
el estado más fijado. -/
def FamMono (g : GPathB) (F : FamT) : Prop :=
  ∀ R R', (∀ b ∈ R, b ∈ R') → (pinF g R').isValid = true → ∀ x y z, F R x y z →
    SideForbids (pinF g R') (F R') x y z

/-- `SideForbids` pasa a un estado con los mismos vivos y aristas. -/
theorem sideForbids_same {U V : GPathB} {G : Trios} (hs : SameGraph U V) (hea : EdgesAlive U)
    {x y z : PathNodeId} (h : SideForbids V G x y z) : SideForbids U G x y z := by
  rcases h with hn | hF
  · refine Or.inl fun ⟨a, b, c⟩ => hn ⟨?_, ?_, ?_⟩
    · exact (hs.2 _ _ (hea _ _ a).1 (hea _ _ a).2).mp a
    · exact (hs.2 _ _ (hea _ _ b).1 (hea _ _ b).2).mp b
    · exact (hs.2 _ _ (hea _ _ c).1 (hea _ _ c).2).mp c
  · exact Or.inr hF

/-- Un lado: lo cortado con `R` sigue cortado con más pins. -/
theorem sideForbids_mono {g : GPathB} {F : FamT} (hg : Good g F) (hm : FamMono g F) {R R' : List NodeId}
    (hRR : ∀ b ∈ R, b ∈ R') (hv : (pinF g R').isValid = true) {x y z : PathNodeId}
    (h : SideForbids (pinF g R) (F R) x y z) : SideForbids (pinF g R') (F R') x y z := by
  rcases h with hn | hF
  · have hadj := (pinF_sub_superset hRR hg.inv hg.pos hv).2
    exact Or.inl fun ⟨a, b, c⟩ => hn ⟨hadj _ _ a, hadj _ _ b, hadj _ _ c⟩
  · exact hm R R' hRR hv x y z hF

/-- **`FamMono` en la llegada.** -/
theorem famMono_arrival {D : GPathB} {F : FamT} {reqs : List NodeId} (hD : Good D F) (hm : FamMono D F)
    (hd : d.step = D.current_step) :
    FamMono ((D.filterAll reqs).up d title forb) (fun R => F (reqs ++ R)) := by
  intro R R' hRR hvA x y z hf
  obtain ⟨hvX, halive, hadj⟩ := arrival_pin_commute (title := title) (forb := forb) hD.inv
    (by have := hD.pos; omega) hd hvA
  have hs := hm (reqs ++ R) (reqs ++ R') (fun b hb => by
    rcases List.mem_append.mp hb with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (hRR b h)) hvX x y z hf
  obtain ⟨sx, sy, sz⟩ := hD.below _ x y z hf
  have hcsX : (pinF D (reqs ++ R')).current_step = D.current_step := step_pinF _ _
  have hiA := sInvB_pinF (sInvB_up (sInvB_filterAll hD.inv reqs) (d := d) (title := title) (forb := forb)
    (by rw [(shrinks_filterAll D reqs).1.step]; exact hd) (by have := hD.pos; omega)) R'
  have hsub := sub_upR (pinF D (reqs ++ R')) d title forb
  have hdX : d.step = (pinF D (reqs ++ R')).current_step := by rw [hcsX]; exact hd
  -- una arista entre nodos viejos de la llegada fijada es arista del remitente fijado
  have hold : ∀ u v, u.id.step < D.current_step → v.id.step < D.current_step →
      (pinF ((D.filterAll reqs).up d title forb) R').Adj u v → (pinF D (reqs ++ R')).Adj u v := by
    intro u v hu hv ha
    have ha' := (hadj u v (hiA.edges _ _ ha).1 (hiA.edges _ _ ha).2).mp ha
    exact adj_addNode_old hdX (by rw [hcsX]; exact hu) (by rw [hcsX]; exact hv) (hsub.adj _ _ ha')
  rcases hs with hn | hF
  · exact Or.inl fun ⟨a, b, c⟩ => hn ⟨hold _ _ sx sy a, hold _ _ sx sz b, hold _ _ sy sz c⟩
  · exact Or.inr hF

/-- **`FamMono` en la unión** (con `PinJoinSplitAll`). -/
theorem famMono_join {A B : GPathB} {FA FB : FamT} (hA : Good A FA) (hB : Good B FB) (hmA : FamMono A FA)
    (hmB : FamMono B FB) (hcs : A.current_step = B.current_step) (hsplit : PinJoinSplitAll A B) :
    FamMono (join A B) (joinFam A B FA FB) := by
  intro R R' hRR hvU x y z hf
  obtain ⟨hsame, hone⟩ := hsplit R' hvU
  have hiU := sInvB_pinF (sInvB_join hA.inv hB.inv hcs) R'
  apply sideForbids_same hsame hiU.edges
  have hmonoA := fun hv => valid_pinF_mono hRR hA.inv hA.pos hv
  have hmonoB := fun hv => valid_pinF_mono hRR hB.inv hB.pos hv
  -- el trío de partida, cortado en cada lado válido con R
  unfold joinFam at hf
  unfold pinJoin joinFam
  by_cases hvA' : (pinF A R').isValid = true <;> by_cases hvB' : (pinF B R').isValid = true
  · have hvA := hmonoA hvA'
    have hvB := hmonoB hvB'
    simp only [hvA', hvB', hvA, hvB, if_true] at hf ⊢
    obtain ⟨n1, n2, n3, sx, sy, sz, sA, sB⟩ := hf
    refine Or.inr ⟨n1, n2, n3, ?_, ?_, ?_, sideForbids_mono hA hmA hRR hvA' sA, sideForbids_mono hB hmB hRR hvB' sB⟩
    · rw [step_pinF] at sx ⊢; exact sx
    · rw [step_pinF] at sy ⊢; exact sy
    · rw [step_pinF] at sz ⊢; exact sz
  · have hvA := hmonoA hvA'
    simp only [hvA', hvB', hvA, if_true] at hf ⊢
    by_cases hvB : (pinF B R).isValid = true
    · simp only [hvB, if_true] at hf
      exact sideForbids_mono hA hmA hRR hvA' hf.2.2.2.2.2.2.1
    · simp only [hvB] at hf
      exact hmA R R' hRR hvA' x y z hf
  · have hvB := hmonoB hvB'
    simp only [hvA', hvB', hvB, if_true] at hf ⊢
    by_cases hvA : (pinF A R).isValid = true
    · simp only [hvA, if_true] at hf
      exact sideForbids_mono hB hmB hRR hvB' hf.2.2.2.2.2.2.2
    · simp only [hvA] at hf
      exact hmB R R' hRR hvB' x y z hf
  · exact absurd hone (by simp [hvA', hvB'])

-- ============================================================
-- La línea siguiente (variable y cláusula): CrossClosed desde NoNewClose
-- ============================================================

/-- **Un corte en el remitente fijado pasa a su llegada fijada** (a cualquier destino), para tríos cuyos nodos del paso
de la cima no viven en la llegada. -/
theorem sf_to_arrival {D : GPathB} {F : FamT} {reqs R : List NodeId} (hD : Good D F) (hm : FamMono D F)
    (hd : d.step = D.current_step) (hvA : (pinF ((D.filterAll reqs).up d title forb) R).isValid = true)
    {x y z : PathNodeId}
    (hn : ∀ u, (u = x ∨ u = y ∨ u = z) → u.id.step < D.current_step ∨
      u ∉ (pinF ((D.filterAll reqs).up d title forb) R).alive)
    (h : SideForbids (pinF D R) (F R) x y z) :
    SideForbids (pinF ((D.filterAll reqs).up d title forb) R) (F (reqs ++ R)) x y z := by
  obtain ⟨hvX, halive, hadj⟩ := arrival_pin_commute (title := title) (forb := forb) hD.inv
    (by have := hD.pos; omega) hd hvA
  have hs := sideForbids_mono hD hm (R := R) (R' := reqs ++ R) (fun b hb => List.mem_append_right _ hb) hvX h
  have hcsX : (pinF D (reqs ++ R)).current_step = D.current_step := step_pinF _ _
  have hiA := sInvB_pinF (sInvB_up (sInvB_filterAll hD.inv reqs) (d := d) (title := title) (forb := forb)
    (by rw [(shrinks_filterAll D reqs).1.step]; exact hd) (by have := hD.pos; omega)) R
  have hsub := sub_upR (pinF D (reqs ++ R)) d title forb
  have hdX : d.step = (pinF D (reqs ++ R)).current_step := by rw [hcsX]; exact hd
  have hold : ∀ u v, (u = x ∨ u = y ∨ u = z) → (v = x ∨ v = y ∨ v = z) →
      (pinF ((D.filterAll reqs).up d title forb) R).Adj u v → (pinF D (reqs ++ R)).Adj u v := by
    intro u v hu hv ha
    have hua := (hiA.edges _ _ ha).1
    have hva := (hiA.edges _ _ ha).2
    have su : u.id.step < D.current_step := (hn u hu).resolve_right (fun h => h hua)
    have sv : v.id.step < D.current_step := (hn v hv).resolve_right (fun h => h hva)
    have ha' := (hadj u v hua hva).mp ha
    exact adj_addNode_old hdX (by rw [hcsX]; exact su) (by rw [hcsX]; exact sv) (hsub.adj _ _ ha')
  rcases hs with hn' | hF
  · exact Or.inl fun ⟨a, b, c⟩ => hn' ⟨hold _ _ (Or.inl rfl) (Or.inr (Or.inl rfl)) a,
      hold _ _ (Or.inl rfl) (Or.inr (Or.inr rfl)) b, hold _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) c⟩
  · exact Or.inr hF


theorem step_up_le {Z : GPathB} : (Z.up d title forb).current_step ≤ Z.current_step + 1 := by
  unfold up; split
  · rw [(shrinks_review _).1.step]; show Z.current_step + 1 ≤ _; omega
  · omega

theorem up_step_eq {Z : GPathB} : (Z.up d title forb).current_step =
    if Z.isValid then Z.current_step + 1 else Z.current_step := by
  unfold up; split
  · rw [(shrinks_review _).1.step]; rfl
  · rfl

/-- Un vivo de la llegada en el paso de su cima es de la fila nueva: su id es el destino. -/
theorem arrival_top_id {D : GPathB} {reqs : List NodeId} (hD : SInvB D) (hd : d.step = D.current_step)
    {x : PathNodeId} (hx : x ∈ ((D.filterAll reqs).up d title forb).alive) (hs : x.id.step = D.current_step) :
    x.id = d := by
  have hcsY : (D.filterAll reqs).current_step = D.current_step := (shrinks_filterAll D reqs).1.step
  have hiY := sInvB_filterAll hD reqs
  by_cases hvY : (D.filterAll reqs).isValid = true
  · have hx' := (sub_up_addNode (d := d) (title := title) (forb := forb) hvY).alive x hx
    rcases alive_addNode_cases hiY.docs hiY.below (by rw [hcsY]; exact hd) hx' with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact newRow_id h
  · have hx' : x ∈ (D.filterAll reqs).alive := by
      unfold up at hx; rw [if_neg hvY] at hx; exact hx
    have := alive_below hiY.docs hiY.below hx'
    omega

/-- **`CrossClosed` entre las dos entradas de la línea siguiente** (paso de variable o de cláusula: cada entrada es la
unión de las llegadas de los dos remitentes), desde `NoNewClose` con pins extra. -/
theorem cc_line {D₀ D₁ : GPathB} {F₀ F₁ : FamT} {rq₀ rq₁ : List NodeId} {d₀ d₁ : NodeId} {t₀ t₁ : String}
    {f₀ f₁ : PathNodeId → Bool} (hD₀ : Good D₀ F₀) (hD₁ : Good D₁ F₁) (hm₀ : FamMono D₀ F₀) (hm₁ : FamMono D₁ F₁)
    (hcs : D₀.current_step = D₁.current_step) (hd₀ : d₀.step = D₀.current_step) (hd₁ : d₁.step = D₀.current_step)
    (hdd : d₀ ≠ d₁)
    (hE₀ : Good (join ((D₀.filterAll rq₀).up d₀ t₀ f₀) ((D₁.filterAll rq₀).up d₀ t₀ f₀))
      (joinFam ((D₀.filterAll rq₀).up d₀ t₀ f₀) ((D₁.filterAll rq₀).up d₀ t₀ f₀)
        (fun R => F₀ (rq₀ ++ R)) (fun R => F₁ (rq₀ ++ R))))
    (hsplit₁ : PinJoinSplitAll ((D₀.filterAll rq₁).up d₁ t₁ f₁) ((D₁.filterAll rq₁).up d₁ t₁ f₁))
    (hvY₀ : (D₀.filterAll rq₁).isValid = true) (hvY₁ : (D₁.filterAll rq₁).isValid = true)
    (hnew : ∀ R, ∀ C j p q r,
      OnChain3 (pinF (join ((D₀.filterAll rq₀).up d₀ t₀ f₀) ((D₁.filterAll rq₀).up d₀ t₀ f₀)) R) C j p q r →
      joinFam ((D₀.filterAll rq₀).up d₀ t₀ f₀) ((D₁.filterAll rq₀).up d₀ t₀ f₀)
        (fun R => F₀ (rq₀ ++ R)) (fun R => F₁ (rq₀ ++ R)) R (C p) (C q) (C r) →
      SideForbids (pinF D₀ R) (F₀ R) (C p) (C q) (C r) ∧ SideForbids (pinF D₁ R) (F₁ R) (C p) (C q) (C r))
    (R : List NodeId)
    (hv₁ : (pinF (join ((D₀.filterAll rq₁).up d₁ t₁ f₁) ((D₁.filterAll rq₁).up d₁ t₁ f₁)) R).isValid = true) :
    CrossClosed (pinF (join ((D₀.filterAll rq₀).up d₀ t₀ f₀) ((D₁.filterAll rq₀).up d₀ t₀ f₀)) R)
      (joinFam ((D₀.filterAll rq₀).up d₀ t₀ f₀) ((D₁.filterAll rq₀).up d₀ t₀ f₀)
        (fun R => F₀ (rq₀ ++ R)) (fun R => F₁ (rq₀ ++ R)) R)
      (pinF (join ((D₀.filterAll rq₁).up d₁ t₁ f₁) ((D₁.filterAll rq₁).up d₁ t₁ f₁)) R)
      (joinFam ((D₀.filterAll rq₁).up d₁ t₁ f₁) ((D₁.filterAll rq₁).up d₁ t₁ f₁)
        (fun R => F₀ (rq₁ ++ R)) (fun R => F₁ (rq₁ ++ R)) R) := by
  intro C j hC p q r h1 h2 h3 h4 h5 h6 hf
  obtain ⟨c0, c1⟩ := hnew R C j p q r ⟨hC, h1, h2, h3, h4, h5, h6⟩ hf
  have hd₁' : d₁.step = D₁.current_step := by rw [← hcs]; exact hd₁
  have hd₀' : d₀.step = D₁.current_step := by rw [← hcs]; exact hd₀
  -- los nodos del trío están en pasos ≤ T; los del paso T tienen id d₀
  have hcsE : (pinF (join ((D₀.filterAll rq₀).up d₀ t₀ f₀) ((D₁.filterAll rq₀).up d₀ t₀ f₀)) R).current_step ≤
      D₀.current_step + 1 := by
    rw [step_pinF]; show ((D₀.filterAll rq₀).up d₀ t₀ f₀).current_step ≤ _
    have := step_up_le (Z := D₀.filterAll rq₀) (d := d₀) (title := t₀) (forb := f₀)
    rw [(shrinks_filterAll D₀ rq₀).1.step] at this; exact this
  have hEalive : ∀ u, (u = C p ∨ u = C q ∨ u = C r) →
      u ∈ (join ((D₀.filterAll rq₀).up d₀ t₀ f₀) ((D₁.filterAll rq₀).up d₀ t₀ f₀)).alive ∧
        u.id.step ≤ D₀.current_step := by
    rintro u (rfl | rfl | rfl)
    · exact ⟨(sub_pinF _ R).alive _ (hC.node p h1 h2).2, by rw [(hC.node p h1 h2).1]; omega⟩
    · exact ⟨(sub_pinF _ R).alive _ (hC.node q h3 h4).2, by rw [(hC.node q h3 h4).1]; omega⟩
    · exact ⟨(sub_pinF _ R).alive _ (hC.node r h5 h6).2, by rw [(hC.node r h5 h6).1]; omega⟩
  have hid₀ : ∀ u, (u = C p ∨ u = C q ∨ u = C r) → u.id.step = D₀.current_step → u.id = d₀ := by
    intro u hu hs
    rcases (alive_join _ _ u).mp (hEalive u hu).1 with h | h
    · exact arrival_top_id hD₀.inv hd₀ h hs
    · exact arrival_top_id hD₁.inv hd₀' h (by rw [← hcs]; exact hs)
  -- el corte en cada remitente pasa a su llegada fijada a d₁
  have hto : ∀ (D : GPathB) (F : FamT), Good D F → FamMono D F → d₁.step = D.current_step →
      D.current_step = D₀.current_step →
      (pinF ((D.filterAll rq₁).up d₁ t₁ f₁) R).isValid = true →
      SideForbids (pinF D R) (F R) (C p) (C q) (C r) →
      SideForbids (pinF ((D.filterAll rq₁).up d₁ t₁ f₁) R) (F (rq₁ ++ R)) (C p) (C q) (C r) := by
    intro D F hD hm hd hcsD hvA h
    refine sf_to_arrival hD hm hd hvA (fun u hu => ?_) h
    obtain ⟨_, hus⟩ := hEalive u hu
    rcases Int.lt_or_eq_of_le hus with hlt | heq
    · exact Or.inl (by rw [hcsD]; exact hlt)
    · refine Or.inr fun hA => hdd ?_
      rw [← hid₀ u hu heq]
      exact arrival_top_id hD.inv hd ((sub_pinF _ R).alive _ hA) (by rw [hcsD]; exact heq)
  -- el destino: la unión fijada es la de las llegadas fijadas
  obtain ⟨hsame, hone⟩ := hsplit₁ R hv₁
  have hiU := sInvB_pinF (sInvB_join
    (sInvB_up (sInvB_filterAll hD₀.inv rq₁) (d := d₁) (title := t₁) (forb := f₁)
      (by rw [(shrinks_filterAll D₀ rq₁).1.step]; exact hd₁) (by have := hD₀.pos; omega))
    (sInvB_up (sInvB_filterAll hD₁.inv rq₁) (d := d₁) (title := t₁) (forb := f₁)
      (by rw [(shrinks_filterAll D₁ rq₁).1.step]; exact hd₁') (by have := hD₁.pos; omega))
    (by rw [step_up hvY₀, step_up hvY₁, (shrinks_filterAll D₀ rq₁).1.step, (shrinks_filterAll D₁ rq₁).1.step, hcs])) R
  apply sideForbids_same hsame hiU.edges
  have hdist := hE₀.nodeg R _ _ _ hf
  have hbel := hE₀.below R _ _ _ hf
  unfold pinJoin joinFam
  by_cases hvA : (pinF ((D₀.filterAll rq₁).up d₁ t₁ f₁) R).isValid = true <;>
    by_cases hvB : (pinF ((D₁.filterAll rq₁).up d₁ t₁ f₁) R).isValid = true
  · simp only [hvA, hvB, if_true]
    refine Or.inr ⟨hdist.1, hdist.2.1, hdist.2.2, ?_, ?_, ?_,
      hto D₀ F₀ hD₀ hm₀ hd₁ rfl hvA c0, hto D₁ F₁ hD₁ hm₁ hd₁' hcs.symm hvB c1⟩
    all_goals
      have hTE : (join ((D₀.filterAll rq₀).up d₀ t₀ f₀) ((D₁.filterAll rq₀).up d₀ t₀ f₀)).current_step ≤
          D₀.current_step + 1 := by
        show ((D₀.filterAll rq₀).up d₀ t₀ f₀).current_step ≤ _
        have := step_up_le (Z := D₀.filterAll rq₀) (d := d₀) (title := t₀) (forb := f₀)
        rw [(shrinks_filterAll D₀ rq₀).1.step] at this; exact this
      have hTA : (pinF ((D₀.filterAll rq₁).up d₁ t₁ f₁) R).current_step = D₀.current_step + 1 := by
        rw [step_pinF, step_up (valid_of_up (isValid_of_sub (sub_pinF _ R) hvA)), (shrinks_filterAll D₀ rq₁).1.step]
      rw [hTA]
      obtain ⟨b1, b2, b3⟩ := hbel
      omega
  · simp only [hvA, hvB, if_true]
    exact hto D₀ F₀ hD₀ hm₀ hd₁ rfl hvA c0
  · simp only [hvA, hvB, if_true]
    exact hto D₁ F₁ hD₁ hm₁ hd₁' hcs.symm hvB c1
  · exact absurd hone (by simp [hvA, hvB])

-- ============================================================
-- Pins triviales
-- ============================================================

/-- Ningún documento del paso de `b` es de otro nodo de mapa: fijar `b` no mata nada. -/
def NoVictims (g : GPathB) (b : NodeId) : Prop := ∀ n ∈ g.nodes, n.id.id.step = b.step → n.id.id = b

theorem noVictims_sub {h g : GPathB} {b : NodeId} (hs : Sub h g) (hg : NoVictims g b) : NoVictims h b := by
  intro n hn hst
  obtain ⟨m, hm, hid, _, _⟩ := hs.nodes n hn
  rw [← hid] at hst ⊢
  exact hg m hm hst

/-- **Fijar un nodo sin víctimas no cambia el estado.** -/
theorem filterRequire_noop {g : GPathB} {b : NodeId} (h : NoVictims g b) : g.filterRequire b = g := by
  unfold filterRequire
  split
  · have hv : ((g.line b.step).map (·.id)).filter (fun q => q.id != b) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hq
      have ⟨hnm, hns⟩ := List.mem_filter.mp hn
      have := h n hnm (by simpa using hns)
      simp [this]
    simp only [hv, List.foldl_nil, List.isEmpty_nil, Bool.not_true, Bool.or_false]
  · rfl

/-- **`pinF` ignora un pin sin víctimas**, esté donde esté en la lista. -/
theorem pinF_triv {g : GPathB} {b : NodeId} (h : NoVictims g b) (L R : List NodeId) :
    pinF g (L ++ b :: R) = pinF g (L ++ R) := by
  unfold pinF
  have hL : NoVictims (L.foldl filterRequire g) b := noVictims_sub (shrinks_foldl _ shrinks_filterRequire L g).1 h
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, filterRequire_noop hL]

/-- **Pin trivial para un estado y su familia.** -/
def Triv (g : GPathB) (F : FamT) (b : NodeId) : Prop := NoVictims g b ∧ ∀ L R, F (L ++ b :: R) = F (L ++ R)

/-- Pins por encima del paso de un estado: ninguno cambia nada. -/
def AboveTriv (g : GPathB) (F : FamT) : Prop := ∀ b : NodeId, g.current_step ≤ b.step → Triv g F b

theorem noVictims_above {g : GPathB} (hb : Below g) {b : NodeId} (hs : g.current_step ≤ b.step) :
    NoVictims g b := fun n hn hst => by have := hb n hn; omega

/-- **Los pins por encima pasan a la llegada.** -/
theorem aboveTriv_arrival {D : GPathB} {F : FamT} {reqs : List NodeId} (hD : SInvB D) (hT : AboveTriv D F)
    (hd : d.step = D.current_step) (h0 : 0 ≤ D.current_step) :
    AboveTriv ((D.filterAll reqs).up d title forb) (fun R => F (reqs ++ R)) := by
  intro b hb
  have hi := sInvB_up (sInvB_filterAll hD reqs) (d := d) (title := title) (forb := forb)
    (by rw [(shrinks_filterAll D reqs).1.step]; exact hd) (by omega)
  refine ⟨noVictims_above hi.below hb, fun L R => ?_⟩
  have hcs : D.current_step ≤ b.step := by
    have := step_up_le (Z := D.filterAll reqs) (d := d) (title := title) (forb := forb)
    have h2 : D.current_step ≤ ((D.filterAll reqs).up d title forb).current_step := by
      rw [up_step_eq]; split <;> rw [(shrinks_filterAll D reqs).1.step] <;> omega
    omega
  show F (reqs ++ (L ++ b :: R)) = F (reqs ++ (L ++ R))
  rw [← List.append_assoc, ← List.append_assoc]
  exact (hT b hcs).2 _ _

/-- **La clave de su cima es un pin trivial para la llegada** (todos sus documentos de la cima son de `d`). -/
theorem triv_arrival_top {D : GPathB} {F : FamT} {reqs : List NodeId} (hD : SInvB D) (hT : AboveTriv D F)
    (hd : d.step = D.current_step) :
    Triv ((D.filterAll reqs).up d title forb) (fun R => F (reqs ++ R)) d := by
  refine ⟨fun n hn hst => ?_, fun L R => ?_⟩
  · have hsY : Sub (D.filterAll reqs) D := (shrinks_filterAll D reqs).1
    have hcsY : (D.filterAll reqs).current_step = D.current_step := hsY.step
    unfold up at hn
    split at hn
    · have hn' := (shrinks_review _).1.nodes n hn
      obtain ⟨m, hm, hid, _, _⟩ := hn'
      rw [← hid] at hst ⊢
      rcases List.mem_append.mp hm with h | h
      · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp h
        have := (sInvB_filterAll hD reqs).below m0 hm0
        exfalso
        have h1 : m0.id.id.step = d.step := hst
        rw [hcsY] at this; omega
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
        exact newRow_id hq
    · obtain ⟨m, hm, hid, _, _⟩ := hsY.nodes n hn
      have := hD.below m hm
      rw [hid] at this; omega
  · show F (reqs ++ (L ++ d :: R)) = F (reqs ++ (L ++ R))
    rw [← List.append_assoc, ← List.append_assoc]
    exact (hT d (by omega)).2 _ _

theorem noVictims_join {A B : GPathB} {b : NodeId} (hA : NoVictims A b) (hB : NoVictims B b) :
    NoVictims (join A B) b := by
  intro n hn hst
  rcases List.mem_append.mp hn with h | h
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
    cases hq : B.node? m.id with
    | none => simp only [hq] at hst ⊢; exact hA m hm hst
    | some m1 => simp only [hq] at hst ⊢; exact hA m hm hst
  · exact hB n (List.mem_filter.mp h).1 hst

/-- **Un pin trivial en los dos lados es trivial en la unión.** -/
theorem triv_join {A B : GPathB} {FA FB : FamT} {b : NodeId} (hA : Triv A FA b) (hB : Triv B FB b) :
    Triv (join A B) (joinFam A B FA FB) b := by
  refine ⟨noVictims_join hA.1 hB.1, fun L R => ?_⟩
  unfold joinFam
  rw [pinF_triv hA.1, pinF_triv hB.1, hA.2, hB.2]

theorem aboveTriv_join {A B : GPathB} {FA FB : FamT} (hA : AboveTriv A FA) (hB : AboveTriv B FB)
    (hcs : A.current_step = B.current_step) : AboveTriv (join A B) (joinFam A B FA FB) :=
  fun b hb => triv_join (hA b hb) (hB b (by rw [← hcs]; exact hb))

-- ============================================================
-- La línea siguiente en el paso de negación
-- ============================================================

/-- **`CrossClosed` entre las dos entradas tras un paso de negación**: `E₀ = up (filterAll D₁ [k₁]) d₀` y
`E₁ = up (filterAll D₀ [k₀]) d₁`, cada una desde el otro remitente fijado a su propia cima (pin trivial). -/
theorem cc_neg {D₀ D₁ : GPathB} {F₀ F₁ : FamT} {k₀ k₁ d₀ d₁ : NodeId} {t₀ t₁ : String}
    {f₀ f₁ : PathNodeId → Bool} (hD₀ : Good D₀ F₀) (hD₁ : Good D₁ F₁)
    (hT₀ : Triv D₀ F₀ k₀) (hT₁ : Triv D₁ F₁ k₁)
    (hcs : D₀.current_step = D₁.current_step) (hd₀ : d₀.step = D₁.current_step) (hd₁ : d₁.step = D₀.current_step)
    (hcc : ∀ R, (pinF D₁ R).isValid = true → (pinF D₀ R).isValid = true →
      CrossClosed (pinF D₁ R) (F₁ R) (pinF D₀ R) (F₀ R)) (R : List NodeId)
    (hv₀ : (pinF ((D₁.filterAll [k₁]).up d₀ t₀ f₀) R).isValid = true)
    (hv₁ : (pinF ((D₀.filterAll [k₀]).up d₁ t₁ f₁) R).isValid = true) :
    CrossClosed (pinF ((D₁.filterAll [k₁]).up d₀ t₀ f₀) R) (F₁ ([k₁] ++ R))
      (pinF ((D₀.filterAll [k₀]).up d₁ t₁ f₁) R) (F₀ ([k₀] ++ R)) := by
  obtain ⟨hvX₀, ha₀, hj₀⟩ := arrival_pin_commute (title := t₀) (forb := f₀) hD₁.inv (by have := hD₁.pos; omega) hd₀ hv₀
  obtain ⟨hvX₁, ha₁, hj₁⟩ := arrival_pin_commute (title := t₁) (forb := f₁) hD₀.inv (by have := hD₀.pos; omega) hd₁ hv₁
  have e₁ : pinF D₁ ([k₁] ++ R) = pinF D₁ R := pinF_triv hT₁.1 [] R
  have e₀ : pinF D₀ ([k₀] ++ R) = pinF D₀ R := pinF_triv hT₀.1 [] R
  have g₁ : F₁ ([k₁] ++ R) = F₁ R := hT₁.2 [] R
  have g₀ : F₀ ([k₀] ++ R) = F₀ R := hT₀.2 [] R
  rw [e₁] at hvX₀ ha₀ hj₀
  rw [e₀] at hvX₁ ha₁ hj₁
  rw [g₁, g₀]
  have hcX := hcc R hvX₀ hvX₁
  have hup := crossClosed_upR (d₀ := d₀) (d₁ := d₁) (t₀ := t₀) (t₁ := t₁) (f₀ := f₀) (f₁ := f₁) hcX
    (by rw [step_pinF]; exact hD₁.below R) (sInvB_pinF hD₁.inv R) (by rw [step_pinF, step_pinF, hcs])
    (by rw [step_pinF]; exact hd₀) (by rw [step_pinF]; exact hd₁)
  have hiA₀ := sInvB_pinF (sInvB_up (sInvB_filterAll hD₁.inv [k₁]) (d := d₀) (title := t₀) (forb := f₀)
    (by rw [(shrinks_filterAll D₁ [k₁]).1.step]; exact hd₀) (by have := hD₁.pos; omega)) R
  have hiA₁ := sInvB_pinF (sInvB_up (sInvB_filterAll hD₀.inv [k₀]) (d := d₁) (title := t₁) (forb := f₁)
    (by rw [(shrinks_filterAll D₀ [k₀]).1.step]; exact hd₁) (by have := hD₀.pos; omega)) R
  have hiX : SInvB (upR (pinF D₁ R) d₀ t₀ f₀) :=
    sInvB_review (sInvB_dirty (sInvB_addNode (sInvB_pinF hD₁.inv _) (by rw [step_pinF]; exact hd₀)
      (by have := hD₁.pos; omega)) true)
  have hvY : (D₁.filterAll [k₁]).isValid = true := valid_of_up (isValid_of_sub (sub_pinF _ R) hv₀)
  refine crossClosed_same hup ?_ ⟨ha₀, hj₀⟩ ⟨ha₁, hj₁⟩ hiA₀.links.2.2 hiX.links hiA₁.edges
  rw [step_pinF, step_up hvY, (shrinks_filterAll D₁ [k₁]).1.step, step_upR, step_pinF]

end GPathB

end AbsSatBingo.Model
