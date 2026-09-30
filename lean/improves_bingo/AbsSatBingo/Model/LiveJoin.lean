-- lean/improves_bingo/AbsSatBingo/Model/LiveJoin.lean
import AbsSatBingo.Model.LivePin

/-!
# `LiveExt` en el join: se reduce a (★)

En la unión de dos llegadas, con los tríos `joinF` (los que prohíben los dos lados):

* **`liveChain_join_left` / `_right`**: una cadena viva de un lado es viva en la unión (sus tríos tienen las tres
  aristas en el lado y no están prohibidos en él, luego no los prohíben los dos lados).
* **`liveExt_join`**: si los dos lados cumplen `LiveExt` y vale **(★) `JoinSide`** (toda cadena viva de la unión es
  viva en alguno de los lados), la unión cumple `LiveExt`.

* **`joinSide_of_crossClosed`**: (★) sale de **`CrossClosed`** en los dos sentidos (un trío de una cadena de un lado,
  prohibido en ese lado, está cortado en el otro) y de que las cimas de un lado no vivan en el otro. Una cadena viva de
  la unión que empieza en una cima de `A` usa solo aristas de `A` (los tríos con la cima solo existen en `A`), y un
  trío suyo prohibido en `A` lo cortan los dos lados.

(★) es lo que queda del acuerdo entre ramas; con esto, en la forma `CrossClosed`. Medido: 0 violaciones (`probe_joinside.jl`: 79 040 cadenas vivas en 131
joins). No sale de propiedades locales de tríos: los lados no coinciden en sus tríos prohibidos, y `TopDom` es falsa
(`probe_topdom.jl`). Con tríos sólidos es equivalente a `LiveExt` de la unión.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

variable {g₁ g₂ : GPathB} {F₁ F₂ : Trios}

/-- **(★)**: toda cadena viva de la unión es viva en alguno de los dos lados. -/
def JoinSide (g₁ : GPathB) (F₁ : Trios) (g₂ : GPathB) (F₂ : Trios) : Prop :=
  ∀ C j, LiveChain (join g₁ g₂) (joinF g₁.current_step g₁ F₁ g₂ F₂) C j → 1 ≤ j →
    LiveChain g₁ F₁ C j ∨ LiveChain g₂ F₂ C j

/-- En un trío de nodos que se poseen dos a dos en el lado, `SideForbids` es `F`. -/
theorem sideForbids_F {g : GPathB} {F : Trios} {u v w : PathNodeId} (huv : g.Adj u v) (huw : g.Adj u w)
    (hvw : g.Adj v w) (h : SideForbids g F u v w) : F u v w := by
  rcases h with h | h
  · exact absurd ⟨huv, huw, hvw⟩ h
  · exact h

/-- Si `joinF` prohíbe un trío (en algún orden) de nodos que se poseen dos a dos en un lado, ese lado lo prohíbe. -/
theorem sym_F_of_joinF {g : GPathB} {F : Trios} (hside : ∀ u v w, joinF g₁.current_step g₁ F₁ g₂ F₂ u v w →
      g.Adj u v → g.Adj u w → g.Adj v w → F u v w)
    {x y z : PathNodeId} (hxy : g.Adj x y) (hxz : g.Adj x z) (hyz : g.Adj y z)
    (h : Sym (joinF g₁.current_step g₁ F₁ g₂ F₂) x y z) : Sym F x y z := by
  have s := fun a b => (adj_symm g a b).mp
  unfold Sym at h ⊢
  rcases h with h | h | h | h | h | h
  · exact Or.inl (hside _ _ _ h hxy hxz hyz)
  · exact Or.inr (Or.inl (hside _ _ _ h hxz hxy (s _ _ hyz)))
  · exact Or.inr (Or.inr (Or.inl (hside _ _ _ h (s _ _ hxy) hyz hxz)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hside _ _ _ h hyz (s _ _ hxy) (s _ _ hxz)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hside _ _ _ h (s _ _ hxz) (s _ _ hyz) hxy)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hside _ _ _ h (s _ _ hyz) (s _ _ hxz) (s _ _ hxy))))))

/-- **Una cadena viva del lado izquierdo es viva en la unión.** -/
theorem liveChain_join_left {C : Int → PathNodeId} {j : Int} (hC : LiveChain g₁ F₁ C j) :
    LiveChain (join g₁ g₂) (joinF g₁.current_step g₁ F₁ g₂ F₂) C j := by
  have hcs : (join g₁ g₂).current_step = g₁.current_step := rfl
  refine ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩, fun a b c ha hab hbc hc hs => ?_⟩
  · obtain ⟨hs, ha⟩ := hC.chain.node k h1 h2; exact ⟨hs, (alive_join g₁ g₂ _).mpr (Or.inl ha)⟩
  · exact adj_join_left (hC.chain.adj k l h1 h2 h3 h4)
  · obtain ⟨n, hn, hp⟩ := hC.chain.link k h1 h2
    obtain ⟨n', hn', hpp, _⟩ := node?_join_left_sup (g := g₂) hn
    exact ⟨n', hn', hpp _ hp⟩
  · have hA := fun k l (h1 : j ≤ k) (h2 : k ≤ g₁.current_step - 1) (h3 : j ≤ l) (h4 : l ≤ g₁.current_step - 1) =>
      hC.chain.adj k l h1 h2 h3 h4
    exact hC.live a b c ha hab hbc hc (sym_F_of_joinF
      (fun u v w hj huv huw hvw => sideForbids_F huv huw hvw hj.2.2.2.1)
      (hA a b ha (by omega) (by omega) (by omega)) (hA a c ha (by omega) (by omega) hc)
      (hA b c (by omega) (by omega) (by omega) hc) hs)

/-- **Una cadena viva del lado derecho es viva en la unión.** -/
theorem liveChain_join_right (hcs : g₁.current_step = g₂.current_step) {C : Int → PathNodeId} {j : Int}
    (hC : LiveChain g₂ F₂ C j) : LiveChain (join g₁ g₂) (joinF g₁.current_step g₁ F₁ g₂ F₂) C j := by
  have hcs' : (join g₁ g₂).current_step = g₂.current_step := hcs
  refine ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩, fun a b c ha hab hbc hc hs => ?_⟩
  · obtain ⟨hs, ha⟩ := hC.chain.node k h1 (by rw [← hcs']; exact h2)
    exact ⟨hs, (alive_join g₁ g₂ _).mpr (Or.inr ha)⟩
  · exact adj_join_right (hC.chain.adj k l h1 (by rw [← hcs']; exact h2) h3 (by rw [← hcs']; exact h4))
  · obtain ⟨n, hn, hp⟩ := hC.chain.link k h1 (by rw [← hcs']; exact h2)
    obtain ⟨n', hn', hpp, _⟩ := node?_join_right_sup (e := g₁) hn
    exact ⟨n', hn', hpp _ hp⟩
  · rw [hcs'] at hc
    have hA := fun k l (h1 : j ≤ k) (h2 : k ≤ g₂.current_step - 1) (h3 : j ≤ l) (h4 : l ≤ g₂.current_step - 1) =>
      hC.chain.adj k l h1 h2 h3 h4
    exact hC.live a b c ha hab hbc hc (sym_F_of_joinF
      (fun u v w hj huv huw hvw => sideForbids_F huv huw hvw hj.2.2.2.2)
      (hA a b ha (by omega) (by omega) (by omega)) (hA a c ha (by omega) (by omega) hc)
      (hA b c (by omega) (by omega) (by omega) hc) hs)

/-- **El join conserva `LiveExt` bajo (★).** -/
theorem liveExt_join (h₁ : LiveExt g₁ F₁) (h₂ : LiveExt g₂ F₂) (hcs : g₁.current_step = g₂.current_step)
    (hside : JoinSide g₁ F₁ g₂ F₂) : LiveExt (join g₁ g₂) (joinF g₁.current_step g₁ F₁ g₂ F₂) := by
  intro C j hC hj1 hjt
  have hcsU : (join g₁ g₂).current_step = g₁.current_step := rfl
  rcases hside C j hC hj1 with h | h
  · obtain ⟨C', hC', hag⟩ := h₁ C j h hj1 (by rw [← hcsU]; exact hjt)
    exact ⟨C', liveChain_join_left hC', hag⟩
  · obtain ⟨C', hC', hag⟩ := h₂ C j h hj1 (by rw [← hcs, ← hcsU]; exact hjt)
    exact ⟨C', liveChain_join_right hcs hC', hag⟩

-- ============================================================
-- (★) desde CrossClosed
-- ============================================================

/-- **`CrossClosed A FA B FB`**: un trío de una cadena de `A` prohibido en `A` está cortado en `B` (le falta una
arista o está prohibido). Medido: 0 fallos (`probe_joinside.jl`, `sbad_open`). -/
def CrossClosed (A : GPathB) (FA : Trios) (B : GPathB) (FB : Trios) : Prop :=
  ∀ C j, SpineChain A C j → ∀ p q r, j ≤ p → p ≤ A.current_step - 1 → j ≤ q → q ≤ A.current_step - 1 →
    j ≤ r → r ≤ A.current_step - 1 → FA (C p) (C q) (C r) → SideForbids B FB (C p) (C q) (C r)

/-- **Una cadena viva de la unión que empieza en una cima de `A` es una cadena viva de `A`**, si la cima no vive en
`B` y vale `CrossClosed A FA B FB`. `J` es la relación de la unión: prohíbe lo que los dos lados cortan. -/
theorem liveChain_side {A B U : GPathB} {FA FB J : Trios} {C : Int → PathNodeId} {j : Int}
    (hcsU : U.current_step = A.current_step)
    (hadjU : ∀ x y, U.Adj x y → A.Adj x y ∨ B.Adj x y)
    (hJ : ∀ u v w, SideForbids A FA u v w → SideForbids B FB u v w → u.id.step < A.current_step →
      v.id.step < A.current_step → w.id.step < A.current_step → J u v w)
    (heaA : EdgesAlive A) (heaB : EdgesAlive B) (hliA : LinksInv A) (hkU : LinksCompat U)
    (hcross : CrossClosed A FA B FB) (hC : LiveChain U J C j)
    (hjt : j ≤ A.current_step - 1)
    (htB : C (A.current_step - 1) ∉ B.alive) : LiveChain A FA C j := by
  have hnode := fun k (h1 : j ≤ k) (h2 : k ≤ A.current_step - 1) => hC.chain.node k h1 (by rw [hcsU]; exact h2)
  have hadjC := fun k l (h1 : j ≤ k) (h2 : k ≤ A.current_step - 1) (h3 : j ≤ l) (h4 : l ≤ A.current_step - 1) =>
    hC.chain.adj k l h1 (by rw [hcsU]; exact h2) h3 (by rw [hcsU]; exact h4)
  -- la cima solo tiene aristas de A
  have htop : ∀ k, j ≤ k → k ≤ A.current_step - 1 → A.Adj (C (A.current_step - 1)) (C k) := by
    intro k h1 h2
    rcases hadjU _ _ (hadjC (A.current_step - 1) k hjt (Int.le_refl _) h1 h2) with h | h
    · exact h
    · exact absurd (heaB _ _ h).1 htB
  have halive : ∀ k, j ≤ k → k ≤ A.current_step - 1 → C k ∈ A.alive := fun k h1 h2 => (heaA _ _ (htop k h1 h2)).2
  have hsteps : ∀ k, j ≤ k → k ≤ A.current_step - 1 → (C k).id.step = k := fun k h1 h2 => (hnode k h1 h2).1
  -- `B` no posee la cima
  have hnB : ∀ x, ¬ B.Adj (C (A.current_step - 1)) x := fun x h => htB (heaB _ _ h).1
  -- toda pareja es de A: si no, el trío con la cima lo cortan los dos lados
  have hpair : ∀ k l, j ≤ k → k ≤ A.current_step - 1 → j ≤ l → l ≤ A.current_step - 1 → A.Adj (C k) (C l) := by
    intro k l h1 h2 h3 h4
    by_cases hkl : k = l
    · subst hkl; exact adj_refl _ _ (halive k h1 h2)
    by_cases hk : k = A.current_step - 1
    · subst hk; exact htop l h3 h4
    by_cases hl : l = A.current_step - 1
    · subst hl; exact (adj_symm _ _ _).mp (htop k h1 h2)
    refine Classical.byContradiction fun hna => ?_
    have hJt := hJ (C (A.current_step - 1)) (C k) (C l) (Or.inl fun ⟨_, _, h⟩ => hna h) (Or.inl fun ⟨h, _, _⟩ => hnB _ h)
      (by rw [hsteps _ hjt (Int.le_refl _)]; omega) (by rw [hsteps k h1 h2]; omega) (by rw [hsteps l h3 h4]; omega)
    rcases Int.lt_or_gt_of_ne hkl with hlt | hlt
    · exact hC.live k l (A.current_step - 1) h1 hlt (by omega) (by rw [hcsU]; omega) (by unfold Sym; simp [hJt])
    · exact hC.live l k (A.current_step - 1) h3 hlt (by omega) (by rw [hcsU]; omega) (by unfold Sym; simp [hJt])
  have hchain : SpineChain A C j := by
    refine ⟨fun k h1 h2 => ⟨hsteps k h1 h2, halive k h1 h2⟩, hpair, fun k h1 h2 => ?_⟩
    obtain ⟨n, hn, hp⟩ := hC.chain.link k h1 (by rw [hcsU]; exact h2)
    have hc := (hkU n (node?_mem hn)).1 _ hp
    rw [node?_id hn] at hc
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hliA.1 (halive k (by omega) h2))
    have hab : A.Adj m.id (C (k - 1)) := by rw [node?_id hm]; exact hpair k (k - 1) (by omega) h2 (by omega) (by omega)
    exact ⟨m, hm, (hliA.2.1 m (node?_mem hm) _ (halive (k - 1) (by omega) (by omega)) hab).1 (by rw [node?_id hm]; exact hc)⟩
  refine ⟨hchain, fun a b c ha hab hbc hc hs => ?_⟩
  -- un trío prohibido en A lo corta B (CrossClosed) y A: la unión lo prohíbe
  have key : ∀ p q r, j ≤ p → p ≤ A.current_step - 1 → j ≤ q → q ≤ A.current_step - 1 → j ≤ r → r ≤ A.current_step - 1 →
      FA (C p) (C q) (C r) → J (C p) (C q) (C r) := fun p q r h1 h2 h3 h4 h5 h6 hf =>
    hJ _ _ _ (Or.inr hf) (hcross C j hchain p q r h1 h2 h3 h4 h5 h6 hf)
      (by rw [hsteps p h1 h2]; omega) (by rw [hsteps q h3 h4]; omega) (by rw [hsteps r h5 h6]; omega)
  apply hC.live a b c ha hab hbc (by rw [hcsU]; exact hc)
  unfold Sym at hs ⊢
  rcases hs with h | h | h | h | h | h
  · exact Or.inl (key a b c ha (by omega) (by omega) (by omega) (by omega) hc h)
  · exact Or.inr (Or.inl (key a c b ha (by omega) (by omega) hc (by omega) (by omega) h))
  · exact Or.inr (Or.inr (Or.inl (key b a c (by omega) (by omega) ha (by omega) (by omega) hc h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key b c a (by omega) (by omega) (by omega) hc ha (by omega) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key c a b (by omega) hc ha (by omega) (by omega) (by omega) h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key c b a (by omega) hc (by omega) (by omega) ha (by omega) h)))))

/-- **(★) desde `CrossClosed`**: si las cimas de cada lado no viven en el otro y vale `CrossClosed` en los dos
sentidos, toda cadena viva de la unión es viva en el lado de su cima. -/
theorem joinSide_of_crossClosed (hcs : g₁.current_step = g₂.current_step)
    (htop₁ : ∀ t ∈ g₁.alive, t.id.step = g₁.current_step - 1 → t ∉ g₂.alive)
    (htop₂ : ∀ t ∈ g₂.alive, t.id.step = g₂.current_step - 1 → t ∉ g₁.alive)
    (hea₁ : EdgesAlive g₁) (hea₂ : EdgesAlive g₂) (hli₁ : LinksInv g₁) (hli₂ : LinksInv g₂)
    (hc₁₂ : CrossClosed g₁ F₁ g₂ F₂) (hc₂₁ : CrossClosed g₂ F₂ g₁ F₁) : JoinSide g₁ F₁ g₂ F₂ := by
  intro C j hC hj1
  have hkU := (linksInv_join hli₁ hli₂ hea₁ hea₂).2.2
  have hcsU : (join g₁ g₂).current_step = g₁.current_step := rfl
  by_cases hjt : j ≤ g₁.current_step - 1
  · have ht := (hC.chain.node (g₁.current_step - 1) hjt (by rw [hcsU]; omega)).2
    rcases (alive_join g₁ g₂ _).mp ht with h | h
    · refine Or.inl (liveChain_side (B := g₂) hcsU (fun x y hxy => adj_join_cases hxy)
        (fun u v w h1 h2 hu hv hw => ⟨hu, hv, hw, h1, h2⟩) hea₁ hea₂ hli₁ hkU hc₁₂ hC hjt ?_)
      exact htop₁ _ h (hC.chain.node _ hjt (by rw [hcsU]; omega)).1
    · have hcs2 : (join g₁ g₂).current_step = g₂.current_step := hcs
      have ht2 : C (g₂.current_step - 1) ∈ g₂.alive := by rw [← hcs]; exact h
      refine Or.inr (liveChain_side (B := g₁) hcs2 (fun x y hxy => (adj_join_cases hxy).symm)
        (fun u v w h1 h2 hu hv hw => ⟨by rw [hcs]; exact hu, by rw [hcs]; exact hv, by rw [hcs]; exact hw, h2, h1⟩)
        hea₂ hea₁ hli₂ hkU hc₂₁ hC (by rw [← hcs]; exact hjt) ?_)
      exact htop₂ _ ht2 (by rw [← hcs]; exact (hC.chain.node _ hjt (by rw [hcsU]; omega)).1)
  · exact Or.inl ⟨⟨fun k h1 h2 => absurd (by omega : j ≤ g₁.current_step - 1) hjt,
      fun k l h1 h2 _ _ => absurd (by omega : j ≤ g₁.current_step - 1) hjt,
      fun k h1 h2 => absurd (by omega : j ≤ g₁.current_step - 1) hjt⟩,
      fun a b c ha hab hbc hc => absurd (by omega : j ≤ g₁.current_step - 1) hjt⟩

-- ============================================================
-- CrossClosed pasa de los remitentes a las llegadas de un join
-- ============================================================

open Machine (Below) in
/-- Una cadena de la llegada `up (filterAll D reqs) d`, sin su cima, es una cadena del remitente `D`. -/
theorem spineChain_sender {D : GPathB} {reqs : List NodeId} {d : NodeId} {title : String}
    {forb : PathNodeId → Bool} (hv : (D.filterAll reqs).isValid = true) (hnd : NodupIds D)
    (hdocs : AliveDocs (D.filterAll reqs)) (hb : Below (D.filterAll reqs))
    (hd : d.step = D.current_step) {C : Int → PathNodeId} {j : Int}
    (hC : SpineChain ((D.filterAll reqs).up d title forb) C j) : SpineChain D C j := by
  have hsY : Sub (D.filterAll reqs) D := (shrinks_filterAll D reqs).1
  have hcsY : (D.filterAll reqs).current_step = D.current_step := hsY.step
  have hdY : d.step = (D.filterAll reqs).current_step := by rw [hcsY]; exact hd
  have hsA : Sub ((D.filterAll reqs).up d title forb) ((D.filterAll reqs).addNode d title forb) := sub_up_addNode hv
  have hcsA : ((D.filterAll reqs).up d title forb).current_step = D.current_step + 1 := by
    rw [step_up hv, hcsY]
  have hndY : NodupIds (D.filterAll reqs) := revPrims_filterAll revPrims_nodupIds D reqs hnd
  have hndA : NodupIds ((D.filterAll reqs).addNode d title forb) := nodupIds_addNode hndY hb hdY
  have hn := fun k (h1 : j ≤ k) (h2 : k ≤ D.current_step - 1) => hC.node k h1 (by rw [hcsA]; omega)
  have hold : ∀ k, j ≤ k → k ≤ D.current_step - 1 → C k ∈ (D.filterAll reqs).alive := by
    intro k h1 h2
    obtain ⟨hs, ha⟩ := hn k h1 h2
    rcases alive_addNode_cases hdocs hb hdY (hsA.alive _ ha) with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · rw [hcsY] at h; omega
  refine ⟨fun k h1 h2 => ⟨(hn k h1 h2).1, hsY.alive _ (hold k h1 h2)⟩, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩
  · have hA := hsA.adj _ _ (hC.adj k l h1 (by rw [hcsA]; omega) h3 (by rw [hcsA]; omega))
    exact hsY.adj _ _ (adj_addNode_old hdY (by rw [(hn k h1 h2).1, hcsY]; omega)
      (by rw [(hn l h3 h4).1, hcsY]; omega) hA)
  · obtain ⟨n, hn', hp⟩ := hC.link k h1 (by rw [hcsA]; omega)
    obtain ⟨m, hm, hpm⟩ := node?_sub hsA hndA hn'
    rw [node?_addNode_old hdY (by rw [(hn k (by omega) h2).1, hcsY]; omega)] at hm
    cases hy : (D.filterAll reqs).node? (C k) with
    | none => rw [hy] at hm; cases hm
    | some m0 =>
      rw [hy] at hm; cases hm
      obtain ⟨m1, hm1, hpm1⟩ := node?_sub hsY hnd hy
      exact ⟨m1, hm1, hpm1 _ (hpm _ hp)⟩

open Machine (Below) in
/-- **`CrossClosed` pasa de los remitentes a las llegadas** del mismo destino (con los mismos requisitos): una cadena
de la llegada sin su cima es una cadena del remitente, los tríos que nombran `F` son de nodos viejos, y el filtro, la
fila nueva y la revisión solo quitan aristas entre nodos viejos. -/
theorem crossClosed_up {D₀ D₁ : GPathB} {F₀ F₁ : Trios} {reqs reqs₁ : List NodeId} {d d₁ : NodeId}
    {title title₁ : String} {forb forb₁ : PathNodeId → Bool} (hc : CrossClosed D₀ F₀ D₁ F₁) (hB : FBelow F₀ D₀.current_step)
    (hcs : D₀.current_step = D₁.current_step)
    (hv₀ : (D₀.filterAll reqs).isValid = true) (hnd₀ : NodupIds D₀) (hdocs₀ : AliveDocs (D₀.filterAll reqs))
    (hb₀ : Below (D₀.filterAll reqs)) (hd₀ : d.step = D₀.current_step)
    (hv₁ : (D₁.filterAll reqs₁).isValid = true) (hd₁ : d₁.step = D₁.current_step) :
    CrossClosed ((D₀.filterAll reqs).up d title forb) F₀ ((D₁.filterAll reqs₁).up d₁ title₁ forb₁) F₁ := by
  intro C j hC p q r h1 h2 h3 h4 h5 h6 hf
  have hcsY₀ : (D₀.filterAll reqs).current_step = D₀.current_step := (shrinks_filterAll D₀ reqs).1.step
  have hcsY₁ : (D₁.filterAll reqs₁).current_step = D₁.current_step := (shrinks_filterAll D₁ reqs₁).1.step
  have hcsA : ((D₀.filterAll reqs).up d title forb).current_step = D₀.current_step + 1 := by
    rw [step_up hv₀, hcsY₀]
  -- los tres nodos son viejos
  obtain ⟨sp, sq, sr⟩ := hB _ _ _ hf
  rw [(hC.node p h1 h2).1] at sp; rw [(hC.node q h3 h4).1] at sq; rw [(hC.node r h5 h6).1] at sr
  have hch := spineChain_sender hv₀ hnd₀ hdocs₀ hb₀ hd₀ hC
  have hs := hc C j hch p q r h1 (by omega) h3 (by omega) h5 (by omega) hf
  -- lo cortado en D₁ sigue cortado en la llegada
  have hdY₁ : d₁.step = (D₁.filterAll reqs₁).current_step := by rw [hcsY₁]; exact hd₁
  have hsub : Sub ((D₁.filterAll reqs₁).up d₁ title₁ forb₁) ((D₁.filterAll reqs₁).addNode d₁ title₁ forb₁) :=
    sub_up_addNode hv₁
  have hsY := (shrinks_filterAll D₁ reqs₁).1
  have hstep := fun k (h1 : j ≤ k) (h2 : k ≤ ((D₀.filterAll reqs).up d title forb).current_step - 1) =>
    (hC.node k h1 h2).1
  have hadj : ∀ u v : Int, j ≤ u → u < D₀.current_step → j ≤ v → v < D₀.current_step →
      ((D₁.filterAll reqs₁).up d₁ title₁ forb₁).Adj (C u) (C v) → D₁.Adj (C u) (C v) := by
    intro u v hu1 hu2 hv1 hv2 ha
    exact hsY.adj _ _ (adj_addNode_old hdY₁ (by rw [hstep u hu1 (by omega), hcsY₁, ← hcs]; exact hu2)
      (by rw [hstep v hv1 (by omega), hcsY₁, ← hcs]; exact hv2) (hsub.adj _ _ ha))
  rcases hs with hn | hF
  · exact Or.inl fun ⟨a, b, c⟩ => hn ⟨hadj p q h1 (by omega) h3 (by omega) a, hadj p r h1 (by omega) h5 (by omega) b,
      hadj q r h3 (by omega) h5 (by omega) c⟩
  · exact Or.inr hF

-- ============================================================
-- CrossClosed entre las dos entradas de una línea
-- ============================================================

/-- Un trío de una cadena de `E` (índices en el tramo de la cadena). -/
def OnChain3 (E : GPathB) (C : Int → PathNodeId) (j p q r : Int) : Prop :=
  SpineChain E C j ∧ j ≤ p ∧ p ≤ E.current_step - 1 ∧ j ≤ q ∧ q ≤ E.current_step - 1 ∧ j ≤ r ∧
    r ≤ E.current_step - 1

/-- **`PinSwap`**: un trío de una cadena de `E = A₀ ∪ A₁` que cortan las dos llegadas `A₀`, `A₁` lo cortan también
las llegadas `A₀'`, `A₁'` de los mismos remitentes a la otra entrada. -/
def PinSwap (E A₀ : GPathB) (F₀ : Trios) (A₁ : GPathB) (F₁ : Trios) (A₀' : GPathB) (F₀' : Trios) (A₁' : GPathB)
    (F₁' : Trios) : Prop :=
  ∀ C j p q r, OnChain3 E C j p q r → SideForbids A₀ F₀ (C p) (C q) (C r) → SideForbids A₁ F₁ (C p) (C q) (C r) →
    SideForbids A₀' F₀' (C p) (C q) (C r) ∧ SideForbids A₁' F₁' (C p) (C q) (C r)

/-- **`CrossClosed` entre dos uniones por `PinSwap`**. -/
theorem crossClosed_join {A₀ A₁ A₀' A₁' : GPathB} {F₀ F₁ F₀' F₁' : Trios}
    (hcs : A₀.current_step = A₀'.current_step) (h : PinSwap (join A₀ A₁) A₀ F₀ A₁ F₁ A₀' F₀' A₁' F₁') :
    CrossClosed (join A₀ A₁) (joinF A₀.current_step A₀ F₀ A₁ F₁) (join A₀' A₁')
      (joinF A₀'.current_step A₀' F₀' A₁' F₁') := by
  intro C j hC p q r h1 h2 h3 h4 h5 h6 ⟨sp, sq, sr, s0, s1⟩
  obtain ⟨t0, t1⟩ := h C j p q r ⟨hC, h1, h2, h3, h4, h5, h6⟩ s0 s1
  exact Or.inr ⟨by rw [← hcs]; exact sp, by rw [← hcs]; exact sq, by rw [← hcs]; exact sr, t0, t1⟩

/-- **`NoNewClose`**: un trío de una cadena de `E` que cortan las dos llegadas ya lo cortaban los dos remitentes.
Medido: 300/300 en las líneas de cláusula (`probe_crossline.jl`, `sender_closed`). -/
def NoNewClose (E A₀ A₁ D₀ D₁ : GPathB) (F₀ F₁ : Trios) : Prop :=
  ∀ C j p q r, OnChain3 E C j p q r → SideForbids A₀ F₀ (C p) (C q) (C r) → SideForbids A₁ F₁ (C p) (C q) (C r) →
    SideForbids D₀ F₀ (C p) (C q) (C r) ∧ SideForbids D₁ F₁ (C p) (C q) (C r)

open Machine (Below) in
/-- **Lo cortado en el remitente sigue cortado en su llegada a la otra entrada.** Los nodos viejos solo pierden
aristas; un nodo de la cima de `E` no vive en la otra llegada (`hsep`). -/
theorem sideForbids_arrival {D E : GPathB} {F : Trios} {reqs : List NodeId} {d : NodeId} {title : String}
    {forb : PathNodeId → Bool} (hv : (D.filterAll reqs).isValid = true) (hd : d.step = D.current_step)
    (hea : EdgesAlive ((D.filterAll reqs).up d title forb))
    (hsep : ∀ x ∈ ((D.filterAll reqs).up d title forb).alive, x.id.step = D.current_step → x ∉ E.alive)
    {u v w : PathNodeId} (hu : u ∈ E.alive) (hv' : v ∈ E.alive) (hw : w ∈ E.alive)
    (su : u.id.step ≤ D.current_step) (sv : v.id.step ≤ D.current_step) (sw : w.id.step ≤ D.current_step)
    (h : SideForbids D F u v w) : SideForbids ((D.filterAll reqs).up d title forb) F u v w := by
  have hcsY : (D.filterAll reqs).current_step = D.current_step := (shrinks_filterAll D reqs).1.step
  have hdY : d.step = (D.filterAll reqs).current_step := by rw [hcsY]; exact hd
  have hsub := sub_up_addNode (d := d) (title := title) (forb := forb) hv
  have hsY := (shrinks_filterAll D reqs).1
  have hadj : ∀ x y, x ∈ E.alive → y ∈ E.alive → x.id.step ≤ D.current_step → y.id.step ≤ D.current_step →
      ((D.filterAll reqs).up d title forb).Adj x y → D.Adj x y := by
    intro x y hx hy sx sy ha
    have hxa := (hea _ _ ha).1
    have hya := (hea _ _ ha).2
    have hxs : x.id.step < D.current_step := by
      rcases Int.lt_or_eq_of_le sx with h | h
      · exact h
      · exact absurd hx (hsep x hxa h)
    have hys : y.id.step < D.current_step := by
      rcases Int.lt_or_eq_of_le sy with h | h
      · exact h
      · exact absurd hy (hsep y hya h)
    exact hsY.adj _ _ (adj_addNode_old hdY (by rw [hcsY]; exact hxs) (by rw [hcsY]; exact hys) (hsub.adj _ _ ha))
  rcases h with hn | hF
  · exact Or.inl fun ⟨a, b, c⟩ => hn ⟨hadj _ _ hu hv' su sv a, hadj _ _ hu hw su sw b, hadj _ _ hv' hw sv sw c⟩
  · exact Or.inr hF

open Machine (Below) in
/-- **`PinSwap` desde `NoNewClose`** (monotonía): cortado en las dos llegadas ⟹ cortado en los dos remitentes ⟹
cortado en sus llegadas a la otra entrada. -/
theorem pinSwap_of_noNewClose {D₀ D₁ E A₀ A₁ : GPathB} {F₀ F₁ : Trios} {reqs : List NodeId} {d : NodeId}
    {title : String} {forb : PathNodeId → Bool}
    (hnew : NoNewClose E A₀ A₁ D₀ D₁ F₀ F₁) (hcs₀ : E.current_step = D₀.current_step + 1)
    (hcs₁ : D₁.current_step = D₀.current_step)
    (hv₀ : (D₀.filterAll reqs).isValid = true) (hv₁ : (D₁.filterAll reqs).isValid = true)
    (hd : d.step = D₀.current_step)
    (hea₀ : EdgesAlive ((D₀.filterAll reqs).up d title forb)) (hea₁ : EdgesAlive ((D₁.filterAll reqs).up d title forb))
    (hsep₀ : ∀ x ∈ ((D₀.filterAll reqs).up d title forb).alive, x.id.step = D₀.current_step → x ∉ E.alive)
    (hsep₁ : ∀ x ∈ ((D₁.filterAll reqs).up d title forb).alive, x.id.step = D₁.current_step → x ∉ E.alive) :
    PinSwap E A₀ F₀ A₁ F₁ ((D₀.filterAll reqs).up d title forb) F₀ ((D₁.filterAll reqs).up d title forb) F₁ := by
  intro C j p q r hT h0 h1
  obtain ⟨hC, a1, a2, a3, a4, a5, a6⟩ := hT
  obtain ⟨t0, t1⟩ := hnew C j p q r ⟨hC, a1, a2, a3, a4, a5, a6⟩ h0 h1
  obtain ⟨sp, ap⟩ := hC.node p a1 a2
  obtain ⟨sq, aq⟩ := hC.node q a3 a4
  obtain ⟨sr, ar⟩ := hC.node r a5 a6
  refine ⟨sideForbids_arrival hv₀ hd hea₀ hsep₀ ap aq ar (by omega) (by omega) (by omega) t0,
    sideForbids_arrival hv₁ (by rw [hcs₁]; exact hd) hea₁ hsep₁ ap aq ar (by omega) (by omega) (by omega) t1⟩

-- ============================================================
-- CrossClosed es monótono (sobrevive a los pins de los dos lados)
-- ============================================================

/-- Una cadena de un subestado es cadena del estado (con ids únicos arriba). -/
theorem spineChain_sub {h g : GPathB} (hs : Sub h g) (hnd : NodupIds g) {C : Int → PathNodeId} {j : Int}
    (hC : SpineChain h C j) : SpineChain g C j := by
  refine ⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩
  · obtain ⟨a, b⟩ := hC.node k h1 (by rw [hs.step]; exact h2); exact ⟨a, hs.alive _ b⟩
  · exact hs.adj _ _ (hC.adj k l h1 (by rw [hs.step]; exact h2) h3 (by rw [hs.step]; exact h4))
  · obtain ⟨n, hn, hp⟩ := hC.link k h1 (by rw [hs.step]; exact h2)
    obtain ⟨m, hm, hpm⟩ := node?_sub hs hnd hn
    exact ⟨m, hm, hpm _ hp⟩

theorem sideForbids_sub {h g : GPathB} {F : Trios} (hs : Sub h g) {u v w : PathNodeId}
    (hf : SideForbids g F u v w) : SideForbids h F u v w := by
  rcases hf with hn | hF
  · exact Or.inl fun ⟨a, b, c⟩ => hn ⟨hs.adj _ _ a, hs.adj _ _ b, hs.adj _ _ c⟩
  · exact Or.inr hF

/-- **`CrossClosed` es monótono**: pasa a subestados de los dos lados (p. ej. `pinF A R`, `pinF B R`). -/
theorem crossClosed_mono {A A' B B' : GPathB} {FA FB : Trios} (hc : CrossClosed A FA B FB) (hA : Sub A' A)
    (hnd : NodupIds A) (hB : Sub B' B) : CrossClosed A' FA B' FB := by
  intro C j hC p q r h1 h2 h3 h4 h5 h6 hf
  rw [hA.step] at h2 h4 h6
  exact sideForbids_sub hB (hc C j (spineChain_sub hA hnd hC) p q r h1 h2 h3 h4 h5 h6 hf)

-- ============================================================
-- Fijar y unir: el sentido fácil de la conmutación
-- ============================================================

/-- **Lo que queda de un lado fijado queda en la unión fijada**: la estructura cerrada de `pinF A R` es una estructura
cerrada de `A`, de la unión y, concordando con `R`, de la unión fijada. -/
theorem pinF_side_sub_left {A B : GPathB} {R : List NodeId} (hdA : AliveDocs A) (hndA : NodupIds A)
    (hvA : (pinF A R).isValid = true) (hcA : ClosedState (pinF A R)) :
    (∀ q ∈ (pinF A R).alive, q ∈ (pinF (join A B) R).alive) ∧
    (∀ y w, y ∈ (pinF A R).alive → w ∈ (pinF A R).alive → (pinF A R).Adj y w → (pinF (join A B) R).Adj y w) := by
  have hs := secStruct_of_sub (sub_pinF A R) hndA hcA
  have hj := secStruct_join_left (g := B) hs
  have hp := secStruct_pinF hj R (fun b hb y hy hys => pinned_pinF hdA hvA b hb y hy hys)
  exact ⟨fun q hq => hp.alive hq, fun y w hy hw ha => hp.adj ⟨hy, hw, ha⟩⟩

theorem pinF_side_sub_right {A B : GPathB} {R : List NodeId} (hcs : A.current_step = B.current_step)
    (hdB : AliveDocs B) (hndB : NodupIds B) (hvB : (pinF B R).isValid = true) (hcB : ClosedState (pinF B R)) :
    (∀ q ∈ (pinF B R).alive, q ∈ (pinF (join A B) R).alive) ∧
    (∀ y w, y ∈ (pinF B R).alive → w ∈ (pinF B R).alive → (pinF B R).Adj y w → (pinF (join A B) R).Adj y w) := by
  have hs := secStruct_of_sub (sub_pinF B R) hndB hcB
  have hj := secStruct_join_right (e := A) hcs hs
  have hp := secStruct_pinF hj R (fun b hb y hy hys => pinned_pinF hdB hvB b hb y hy hys)
  exact ⟨fun q hq => hp.alive hq, fun y w hy hw ha => hp.adj ⟨hy, hw, ha⟩⟩

/-- **El sentido fácil**: la unión de los lados fijados (válidos y cerrados) está dentro de la unión fijada, en vivos y
en aristas. -/
theorem join_pinF_sub {A B : GPathB} {R : List NodeId} (hcs : A.current_step = B.current_step)
    (hdA : AliveDocs A) (hndA : NodupIds A) (hdB : AliveDocs B) (hndB : NodupIds B)
    (hvA : (pinF A R).isValid = true) (hcA : ClosedState (pinF A R))
    (hvB : (pinF B R).isValid = true) (hcB : ClosedState (pinF B R))
    (heaA : EdgesAlive (pinF A R)) (heaB : EdgesAlive (pinF B R)) :
    (∀ q ∈ (join (pinF A R) (pinF B R)).alive, q ∈ (pinF (join A B) R).alive) ∧
    (∀ y w, (join (pinF A R) (pinF B R)).Adj y w → (pinF (join A B) R).Adj y w) := by
  obtain ⟨aA, eA⟩ := pinF_side_sub_left (B := B) hdA hndA hvA hcA
  obtain ⟨aB, eB⟩ := pinF_side_sub_right hcs hdB hndB hvB hcB
  refine ⟨fun q hq => ?_, fun y w ha => ?_⟩
  · rcases (alive_join _ _ q).mp hq with h | h
    · exact aA q h
    · exact aB q h
  · rcases adj_join_cases ha with h | h
    · exact eA y w (heaA _ _ h).1 (heaA _ _ h).2 h
    · exact eB y w (heaB _ _ h).1 (heaB _ _ h).2 h

/-- **El sentido difícil, como hipótesis**: fijar la unión no conserva nada que no conserve algún lado fijado. Es la
forma de `SecSplit` (una estructura cerrada de la unión viene de un lado) para los pins. Medido: 0 diferencias
(`probe_pinjoin.jl`). -/
def PinJoinSplit (A B : GPathB) (R : List NodeId) : Prop :=
  (∀ q ∈ (pinF (join A B) R).alive, q ∈ (join (pinF A R) (pinF B R)).alive) ∧
  (∀ y w, y ∈ (pinF (join A B) R).alive → w ∈ (pinF (join A B) R).alive →
    (pinF (join A B) R).Adj y w → (join (pinF A R) (pinF B R)).Adj y w)

-- ============================================================
-- Congruencias: CrossClosed solo depende de vivos, aristas y compatibilidad
-- ============================================================

/-- Una cadena pasa a otro estado con (al menos) los mismos vivos y aristas entre ellos, con `LinksInv` en el de
llegada (los enlaces de una cadena unen vecinos compatibles). -/
theorem spineChain_transfer {A B : GPathB} (hcs : A.current_step = B.current_step)
    (halive : ∀ q ∈ A.alive, q ∈ B.alive) (hadj : ∀ y w, y ∈ A.alive → w ∈ A.alive → A.Adj y w → B.Adj y w)
    (hkA : LinksCompat A) (hliB : LinksInv B) {C : Int → PathNodeId} {j : Int} (hC : SpineChain A C j) :
    SpineChain B C j :=
  (liveChain_transfer (F := fun _ _ _ => False) hcs halive hadj hkA hliB ⟨hC, fun _ _ _ _ _ _ _ h => by
    unfold Sym at h; simp at h⟩).chain

/-- **`CrossClosed` pasa a estados con los mismos vivos y aristas.** -/
theorem crossClosed_congr {A A' B B' : GPathB} {FA FB : Trios} (hc : CrossClosed A FA B FB)
    (hcsA : A'.current_step = A.current_step)
    (haA : ∀ q ∈ A'.alive, q ∈ A.alive) (hjA : ∀ y w, y ∈ A'.alive → w ∈ A'.alive → A'.Adj y w → A.Adj y w)
    (hkA' : LinksCompat A') (hliA : LinksInv A) (hjB : ∀ y w, B'.Adj y w → B.Adj y w) :
    CrossClosed A' FA B' FB := by
  intro C j hC p q r h1 h2 h3 h4 h5 h6 hf
  rw [hcsA] at h2 h4 h6
  have hs := hc C j (spineChain_transfer hcsA haA hjA hkA' hliA hC) p q r h1 h2 h3 h4 h5 h6 hf
  rcases hs with hn | hF
  · exact Or.inl fun ⟨a, b, c⟩ => hn ⟨hjB _ _ a, hjB _ _ b, hjB _ _ c⟩
  · exact Or.inr hF

end GPathB

end AbsSatBingo.Model
