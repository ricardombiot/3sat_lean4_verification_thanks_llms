-- lean/improves_bingo/AbsSatBingo/Model/StarUp.lean
import AbsSatBingo.Model.KernelUp

/-!
# Subir la estrella de un padre por la fila nueva (paso 3 de la inducción de `StarNodes`)

Plan (conversación del 29-sept-2026): `StarNodes` se hereda a lo largo de la línea. Un paso antes, el padre `p` de la
cima `t` era cima; la hipótesis de inducción da una estructura cerrada `(W₀, R₀)` en su estrella. Este módulo hace la
subida por `addNode`:

> **`secStruct_addNode_star`**: si `(W₀, R₀)` es cerrada en `g`, contiene a `p`, todo nodo suyo está relacionado con
> `p` y en el paso de `p` solo está `p`, entonces `W₀ ∪ {t}` con `R₀` más las parejas de `t` con todo `W₀` es cerrada
> en `g.addNode d …`, para todo nodo `t` de la fila nueva del que `p` es padre.

`t` hereda los vecinos de sus padres (`rowNeighbors`), así que posee todo `W₀`; los testigos de las parejas nuevas
son los de `W₀`, y en el paso nuevo el testigo es `t`. `p` gana a `t` como hijo, que es el hijo que pide la
estructura en el paso de `p`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

open Machine (Below)

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- La relación subida: `R₀`, más `t` con todo `W₀` y consigo mismo. -/
def starUpRel (W₀ : PathNodeId → Prop) (R₀ : PathNodeId → PathNodeId → Prop) (t : PathNodeId)
    (y w : PathNodeId) : Prop :=
  R₀ y w ∨ (y = t ∧ (W₀ w ∨ w = t)) ∨ (w = t ∧ W₀ y)

/-- **La estrella del padre, con la cima nueva, es cerrada tras la fila.** -/
theorem secStruct_addNode_star {W₀ : PathNodeId → Prop} {R₀ : PathNodeId → PathNodeId → Prop}
    (hdocs : AliveDocs g) (hb : Below g) (hd : d.step = g.current_step)
    (hst : SecStruct g W₀ R₀) {p t : PathNodeId} (ht : t ∈ g.newRowIds d forb) (hp : p ∈ g.rowParents d t)
    (hpW : W₀ p) (hstar : ∀ y, W₀ y → R₀ y p)
    (htop : ∀ y, W₀ y → y.id.step = g.current_step - 1 → y = p) :
    SecStruct (g.addNode d title forb) (fun y => W₀ y ∨ y = t) (starUpRel W₀ R₀ t) := by
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  have halive : ∀ q ∈ g.alive, q ∈ (g.addNode d title forb).alive := fun q hq => List.mem_append_left _ hq
  have hedge : ∀ e ∈ g.edges, e ∈ (g.addNode d title forb).edges := fun e he => List.mem_append_left _ he
  have hts : t.id.step = g.current_step := newRow_step hd ht
  have hWs : ∀ {y}, W₀ y → y.id.step < g.current_step := fun hy => alive_below hdocs hb (hst.alive hy)
  have hpos : 0 < g.current_step := by
    have hq := rowParents_sub hp
    unfold newParents at hq
    split at hq
    · assumption
    · cases hq
  have hWt : ∀ {y}, W₀ y → y ≠ t := fun hy he => by have := hWs hy; rw [he] at this; omega
  -- t posee todo W₀: por su padre p
  have hnewadj : ∀ {y}, W₀ y → (g.addNode d title forb).Adj t y := by
    intro y hy
    rw [adj_iff]
    refine Or.inr ⟨(t, y), List.mem_append_right _ ?_, Or.inl ⟨rfl, rfl⟩⟩
    refine List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨y, ?_, rfl⟩⟩
    refine List.mem_filter.mpr ⟨hst.alive hy, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨decide_eq_true (by rw [hts]; exact hWs hy), List.any_eq_true.mpr ⟨p, hp, ?_⟩⟩
    exact hst.adj (hst.symm (hstar y hy))
  -- las parejas de t
  have hTo : ∀ {r}, W₀ r → starUpRel W₀ R₀ t t r := fun hr => Or.inr (Or.inl ⟨rfl, Or.inl hr⟩)
  have hToT : ∀ {r}, W₀ r → starUpRel W₀ R₀ t r t := fun hr => Or.inr (Or.inr ⟨rfl, hr⟩)
  have htt : starUpRel W₀ R₀ t t t := Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)
  have hRt : ∀ {y}, (W₀ y ∨ y = t) → starUpRel W₀ R₀ t y t := by
    rintro y (hy | rfl)
    · exact hToT hy
    · exact htt
  have hdom : ∀ {y w}, starUpRel W₀ R₀ t y w → (W₀ y ∨ y = t) ∧ (W₀ w ∨ w = t) := by
    rintro y w (h | ⟨rfl, hw⟩ | ⟨rfl, hy⟩)
    · exact ⟨Or.inl (hst.dom h).1, Or.inl (hst.dom h).2⟩
    · exact ⟨Or.inr rfl, hw⟩
    · exact ⟨Or.inl hy, Or.inr rfl⟩
  -- el documento viejo de un nodo de W₀
  have hdoc : ∀ {q m}, W₀ q → (g.addNode d title forb).node? q = some m →
      ∃ n, g.node? q = some n ∧ m = g.withGained d forb n := by
    intro q m hq hm
    rw [node?_addNode_old (title := title) hd (hWs hq)] at hm
    cases hn : g.node? q with
    | none => rw [hn] at hm; cases hm
    | some n => rw [hn] at hm; cases hm; exact ⟨n, rfl, rfl⟩
  -- t es hijo ganado de p
  have hgain : ∀ {n}, g.node? p = some n → t ∈ (g.withGained d forb n).sons := by
    intro n hn
    refine List.mem_append_right _ (List.mem_filter.mpr ⟨ht, ?_⟩)
    rw [node?_id hn]
    exact List.contains_iff_mem.mpr hp
  -- un testigo de W₀ en otro paso
  have hwit : ∀ {x}, W₀ x → ∀ l, 0 ≤ l → l < g.current_step → l ≠ x.id.step → ∃ r, R₀ x r ∧ r ≠ x := by
    intro x hx l h0 h1 hne
    obtain ⟨r, hrl, hxr, _⟩ := hst.pair (hst.refl hx) l h0 h1
    exact ⟨r, hxr, fun he => hne (by rw [← hrl, he])⟩
  refine ⟨?_, ?_, ?_, hdom, ?_, ?_, ?_, ?_, ?_⟩
  · -- vivos
    rintro y (hy | rfl)
    · exact halive _ (hst.alive hy)
    · exact List.mem_append_right _ ht
  · -- reflexiva
    rintro y (hy | rfl)
    · exact Or.inl (hst.refl hy)
    · exact htt
  · -- simetría
    rintro y w (h | ⟨rfl, hw | rfl⟩ | ⟨rfl, hy⟩)
    · exact Or.inl (hst.symm h)
    · exact hToT hw
    · exact htt
    · exact hTo hy
  · -- posesiones
    rintro y w (h | ⟨rfl, hw | rfl⟩ | ⟨rfl, hy⟩)
    · exact adj_mono halive hedge _ _ (hst.adj h)
    · exact hnewadj hw
    · exact adj_refl _ _ (List.mem_append_right _ ht)
    · exact (adj_symm _ _ _).mp (hnewadj hy)
  · -- parejas
    intro y w h l h0 h1
    rw [hcs] at h1
    rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp h1) with hl | rfl
    · rcases h with h | ⟨rfl, hw | rfl⟩ | ⟨rfl, hy⟩
      · obtain ⟨r, hrl, hyr, hwr⟩ := hst.pair h l h0 hl
        exact ⟨r, hrl, Or.inl hyr, Or.inl hwr⟩
      · obtain ⟨r, hrl, hwr, _⟩ := hst.pair (hst.refl hw) l h0 hl
        exact ⟨r, hrl, hTo (hst.dom hwr).2, Or.inl hwr⟩
      · obtain ⟨r, hrl, hpr, _⟩ := hst.pair (hst.refl hpW) l h0 hl
        exact ⟨r, hrl, hTo (hst.dom hpr).2, hTo (hst.dom hpr).2⟩
      · obtain ⟨r, hrl, hyr, _⟩ := hst.pair (hst.refl hy) l h0 hl
        exact ⟨r, hrl, Or.inl hyr, hTo (hst.dom hyr).2⟩
    · exact ⟨t, hts, hRt (hdom h).1, hRt (hdom h).2⟩
  · -- enlaces
    rintro y (hy | rfl)
    · obtain ⟨n, hn, hpar, hson⟩ := hst.node hy
      refine ⟨g.withGained d forb n, ?_, fun hr => ?_, fun _ => ?_⟩
      · rw [node?_addNode_old (title := title) hd (hWs hy), hn]; rfl
      · obtain ⟨q, hq, hyq⟩ := hpar hr
        exact ⟨q, hq, Or.inl hyq⟩
      · by_cases hyc : y.id.step = g.current_step - 1
        · have e := htop y hy hyc
          subst e
          exact ⟨t, hgain hn, hToT hy⟩
        · obtain ⟨s, hs, hys⟩ := hson hyc
          exact ⟨s, List.mem_append_left _ hs, Or.inl hys⟩
    · refine ⟨g.rowNode d title y, node?_addNode_new hb hd ht, fun _ => ⟨p, hp, hTo hpW⟩, fun hl => ?_⟩
      exact absurd (by rw [hcs, hts]; omega) hl
  · -- apoyo de los padres
    rintro x w m h hxw hm hx1
    rcases h with h | ⟨rfl, hw | rfl⟩ | ⟨rfl, hx⟩
    · obtain ⟨n, hn, rfl⟩ := hdoc (hst.dom h).1 hm
      obtain ⟨q, hq, hxq, hqw⟩ := hst.par h hxw hn hx1
      exact ⟨q, hq, Or.inl hxq, Or.inl hqw⟩
    · rw [node?_addNode_new hb hd ht] at hm
      cases hm
      exact ⟨p, hp, hTo hpW, Or.inl (hst.symm (hstar w hw))⟩
    · exact absurd rfl hxw
    · obtain ⟨n, hn, rfl⟩ := hdoc hx hm
      obtain ⟨r, hxr, hrx⟩ := hwit hx 0 (by omega) (by have := hWs hx; omega) (by omega)
      obtain ⟨q, hq, hxq, _⟩ := hst.par hxr (Ne.symm hrx) hn hx1
      exact ⟨q, hq, Or.inl hxq, hToT (hst.dom hxq).2⟩
  · -- apoyo de los hijos
    rintro x w m h hxw hm hx1
    rw [hcs] at hx1
    have hxW : W₀ x := by
      rcases (hdom h).1 with hx | rfl
      · exact hx
      · exact absurd hx1 (by rw [hts]; omega)
    obtain ⟨n, hn, rfl⟩ := hdoc hxW hm
    by_cases hxc : x.id.step = g.current_step - 1
    · have e := htop x hxW hxc
      subst e
      refine ⟨t, hgain hn, hToT hxW, ?_⟩
      rcases (hdom h).2 with hw | rfl
      · exact hTo hw
      · exact htt
    · have hx1' : x.id.step + 1 < g.current_step := by have := hWs hxW; omega
      rcases h with h | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · obtain ⟨s, hs, hxs, hsw⟩ := hst.son h hxw hn hx1'
        exact ⟨s, List.mem_append_left _ hs, Or.inl hxs, Or.inl hsw⟩
      · exact absurd hxW (fun h => hWt h rfl)
      · obtain ⟨r, hxr, hrx⟩ := hwit hxW (g.current_step - 1) (by omega) (by omega) (Ne.symm hxc)
        obtain ⟨s, hs, hxs, _⟩ := hst.son hxr (Ne.symm hrx) hn hx1'
        exact ⟨s, List.mem_append_left _ hs, Or.inl hxs, hToT (hst.dom hxs).2⟩

end GPathB

end AbsSatBingo.Model
