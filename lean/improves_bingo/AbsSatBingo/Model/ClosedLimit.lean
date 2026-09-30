-- lean/improves_bingo/AbsSatBingo/Model/ClosedLimit.lean
import AbsSatBingo.Model.ChainLine
import AbsSatBingo.Model.ReviewClean

/-!
# El límite de la revisión: cerrado no basta (`closed_not_chainInv`)

La revisión solo quita: nunca fabrica un testigo. Lo que deja es un estado cerrado (`ClosedState`, `PairClosed`),
y en un grafo cualquiera eso **no** garantiza que el lector con revisión no se atasque.

El ejemplo es colorear $K_5$ con la cima fijada: 5 pasos; los pasos 0–3 tienen 3 nodos (colores 1, 2, 3) y el paso
4, la cima, uno solo (color 0). Dos nodos de pasos distintos son vecinos si tienen colores distintos; los enlaces
padre–hijo van de todo nodo a todos los del paso siguiente. Entonces:

* toda arista tiene testigo en cada paso (queda un color libre) y el estado es cerrado (`k5_closed`,
  `k5_pairClosed`);
* pero cuatro vecinos dos a dos en los pasos 0–3 necesitarían cuatro colores de {1, 2, 3}: no hay camarilla
  (`k5_not_noZombie`), y fijar un nodo del paso 3 no deja ninguna estructura cerrada (`k5_not_chainInv`).

**`closed_not_chainInv`**: existe un estado válido, cerrado y cerrado por parejas donde `ChainInv` y `NoZombie`
fallan. El obstáculo es un cuarteto (el palomar), no un trío: tampoco lo vería una regla de tríos.

Consecuencia: el eslabón que falta (`SibStarInv`, el primer pin) no puede salir de la revisión sola; tiene que usar
cómo construye la máquina sus estados (documentos, UP, joins).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

namespace K5

def mk (s i : Int) : PathNodeId := ⟨⟨s, i⟩, none, none⟩

def aliveL : List PathNodeId :=
  [mk 0 1, mk 0 2, mk 0 3, mk 1 1, mk 1 2, mk 1 3, mk 2 1, mk 2 2, mk 2 3, mk 3 1, mk 3 2, mk 3 3, mk 4 0]

def edgesL : List (PathNodeId × PathNodeId) :=
  aliveL.flatMap (fun y => (aliveL.filter (fun w => decide (y.id.step < w.id.step) && y.id.index != w.id.index)).map
    (fun w => (y, w)))

def nodesL : List PNodeB :=
  aliveL.map (fun y => { id := y, title := "",
                         parents := aliveL.filter (fun p => p.id.step == y.id.step - 1),
                         sons := aliveL.filter (fun s => s.id.step == y.id.step + 1) })

/-- $K_5$ con 4 colores y la cima fijada. -/
def g : GPathB :=
  { nodes := nodesL, alive := aliveL, edges := edgesL, current_step := 5, map_parent := none, dirty := false }

/-- La posesión es «mismo nodo, o pasos distintos y colores distintos». -/
theorem adjb_iff : ∀ y ∈ g.alive, ∀ w ∈ g.alive,
    g.adjb y w = (y == w || (y.id.step != w.id.step && y.id.index != w.id.index)) := by
  decide +kernel

theorem idx : ∀ y ∈ g.alive, y.id.step < 4 → 1 ≤ y.id.index ∧ y.id.index ≤ 3 := by decide +kernel

theorem diff {y w : PathNodeId} (hy : y ∈ g.alive) (hw : w ∈ g.alive) (ha : g.Adj y w)
    (hs : y.id.step ≠ w.id.step) : y.id.index ≠ w.id.index := by
  unfold Adj at ha
  rw [adjb_iff y hy w hw] at ha
  intro hi
  have hne : y ≠ w := fun h => hs (by rw [h])
  simp [hne, hi] at ha

theorem steps5 {l : Int} (h0 : 0 ≤ l) (h1 : l < g.current_step) : l ∈ [0, 1, 2, 3, 4] := by
  have : g.current_step = 5 := rfl
  have : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

theorem pairB : ∀ y ∈ g.alive, ∀ w ∈ g.alive,
    (y == w || (y.id.step != w.id.step && y.id.index != w.id.index)) = true →
    ∀ l ∈ ([0, 1, 2, 3, 4] : List Int), ∃ r ∈ g.alive, r.id.step = l ∧
      (y == r || (y.id.step != r.id.step && y.id.index != r.id.index)) = true ∧
      (w == r || (w.id.step != r.id.step && w.id.index != r.id.index)) = true := by
  decide +kernel

theorem nodeB : ∀ y ∈ g.alive, ∃ n ∈ g.nodes, g.node? y = some n ∧
    (y.id.step ≠ 4 → ∃ s ∈ n.sons, s ∈ g.alive ∧ (y.id.step != s.id.step && y.id.index != s.id.index) = true) := by
  decide +kernel

theorem parB : ∀ x ∈ g.alive, ∀ w ∈ g.alive, (x.id.step != w.id.step && x.id.index != w.id.index) = true →
    ∀ n ∈ g.nodes, n.id = x → 1 ≤ x.id.step → ∃ p ∈ n.parents, p ∈ g.alive ∧
      (x.id.step != p.id.step && x.id.index != p.id.index) = true ∧
      (p == w || (p.id.step != w.id.step && p.id.index != w.id.index)) = true := by
  decide +kernel

theorem sonB : ∀ x ∈ g.alive, ∀ w ∈ g.alive, (x.id.step != w.id.step && x.id.index != w.id.index) = true →
    ∀ n ∈ g.nodes, n.id = x → x.id.step + 1 < 5 → ∃ s ∈ n.sons, s ∈ g.alive ∧
      (x.id.step != s.id.step && x.id.index != s.id.index) = true ∧
      (s == w || (s.id.step != w.id.step && s.id.index != w.id.index)) = true := by
  decide +kernel

theorem adj_of {y w : PathNodeId} (hy : y ∈ g.alive) (hw : w ∈ g.alive)
    (h : (y == w || (y.id.step != w.id.step && y.id.index != w.id.index)) = true) : g.Adj y w := by
  unfold Adj; rw [adjb_iff y hy w hw]; exact h

/-- Dos nodos distintos que se poseen están en pasos distintos (un paso no tiene aristas dentro). -/
theorem adj_ne {y w : PathNodeId} (hy : y ∈ g.alive) (hw : w ∈ g.alive) (ha : g.Adj y w) (hne : y ≠ w) :
    (y.id.step != w.id.step && y.id.index != w.id.index) = true := by
  unfold Adj at ha; rw [adjb_iff y hy w hw] at ha
  simpa [hne] using ha

theorem node?_mem {x : PathNodeId} {n : PNodeB} (h : g.node? x = some n) : n ∈ g.nodes ∧ n.id = x := by
  unfold node? at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  exact ⟨hm, by simpa using hp⟩

theorem k5_closed : ClosedState g := by
  refine ⟨fun hy => hy, fun hy => ⟨hy, hy, adj_refl _ _ hy⟩,
    fun ⟨a, b, c⟩ => ⟨b, a, (adj_symm _ _ _).1 c⟩, fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨_, _, c⟩ => c, ?_, ?_, ?_, ?_⟩
  · rintro y w ⟨hy, hw, ha⟩ l h0 h1
    have ha' : (y == w || (y.id.step != w.id.step && y.id.index != w.id.index)) = true := by
      unfold Adj at ha; rwa [adjb_iff y hy w hw] at ha
    obtain ⟨r, hr, hrl, h1, h2⟩ := pairB y hy w hw ha' l (steps5 h0 h1)
    exact ⟨r, hrl, ⟨hy, hr, adj_of hy hr h1⟩, ⟨hw, hr, adj_of hw hr h2⟩⟩
  · intro y hy
    obtain ⟨n, _, hn, hs⟩ := nodeB y hy
    refine ⟨n, hn, fun hp => ?_, fun hst => ?_⟩
    · simp [mk, aliveL, g] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp at hp
    · obtain ⟨s, hs1, hs2, hs3⟩ := hs (by have : g.current_step = 5 := rfl; omega)
      exact ⟨s, hs1, hy, hs2, adj_of hy hs2 (by simp [hs3])⟩
  · rintro x w n ⟨hx, hw, ha⟩ hne hn h1
    obtain ⟨hnm, hid⟩ := node?_mem hn
    obtain ⟨p, hp, hpa, h1', h2'⟩ := parB x hx w hw (adj_ne hx hw ha hne) n hnm hid h1
    exact ⟨p, hp, ⟨hx, hpa, adj_of hx hpa (by simp [h1'])⟩, ⟨hpa, hw, adj_of hpa hw h2'⟩⟩
  · rintro x w n ⟨hx, hw, ha⟩ hne hn h1
    obtain ⟨hnm, hid⟩ := node?_mem hn
    obtain ⟨s, hs, hsa, h1', h2'⟩ := sonB x hx w hw (adj_ne hx hw ha hne) n hnm hid h1
    exact ⟨s, hs, ⟨hx, hsa, adj_of hx hsa (by simp [h1'])⟩, ⟨hsa, hw, adj_of hsa hw h2'⟩⟩

theorem k5_valid : g.isValid = true := by decide +kernel

theorem k5_pairClosed : PairClosed g := by
  have h : ∀ y ∈ g.alive, ∀ w ∈ g.alive, g.adjb y w = true → g.pairOk y w = true := by decide +kernel
  intro y w _ hy hw ha
  exact h y hy w hw ha

/-- **Cuatro vecinos dos a dos en los pasos 0–3 no caben en tres colores.** -/
theorem no_four {a b c d : PathNodeId} (ha : a ∈ g.alive) (hb : b ∈ g.alive) (hc : c ∈ g.alive)
    (hd : d ∈ g.alive) (sa : a.id.step = 0) (sb : b.id.step = 1) (sc : c.id.step = 2) (sd : d.id.step = 3)
    (hab : g.Adj a b) (hac : g.Adj a c) (had : g.Adj a d) (hbc : g.Adj b c) (hbd : g.Adj b d)
    (hcd : g.Adj c d) : False := by
  have i1 := diff ha hb hab (by omega)
  have i2 := diff ha hc hac (by omega)
  have i3 := diff ha hd had (by omega)
  have i4 := diff hb hc hbc (by omega)
  have i5 := diff hb hd hbd (by omega)
  have i6 := diff hc hd hcd (by omega)
  have ja := idx a ha (by omega)
  have jb := idx b hb (by omega)
  have jc := idx c hc (by omega)
  have jd := idx d hd (by omega)
  omega

/-- **No hay camarilla**: el estado cerrado es un zombi. -/
theorem k5_not_noZombie : ¬ NoZombie g := by
  intro h
  obtain ⟨S, hS⟩ := h k5_valid
  have c5 : g.current_step = 5 := rfl
  have al := fun k (h0 : (0 : Int) ≤ k) (h1 : k < 5) => hS.alive k h0 (by omega)
  have st := fun k (h0 : (0 : Int) ≤ k) (h1 : k < 5) => hS.step k h0 (by omega)
  have ad := fun k l (h0 : (0 : Int) ≤ k) (h1 : k < 5) (h2 : (0 : Int) ≤ l) (h3 : l < 5) =>
    hS.adj k l h0 (by omega) h2 (by omega)
  exact no_four (al 0 (by omega) (by omega)) (al 1 (by omega) (by omega)) (al 2 (by omega) (by omega))
    (al 3 (by omega) (by omega)) (st 0 (by omega) (by omega)) (st 1 (by omega) (by omega))
    (st 2 (by omega) (by omega)) (st 3 (by omega) (by omega))
    (ad 0 1 (by omega) (by omega) (by omega) (by omega)) (ad 0 2 (by omega) (by omega) (by omega) (by omega))
    (ad 0 3 (by omega) (by omega) (by omega) (by omega)) (ad 1 2 (by omega) (by omega) (by omega) (by omega))
    (ad 1 3 (by omega) (by omega) (by omega) (by omega)) (ad 2 3 (by omega) (by omega) (by omega) (by omega))

theorem pinned4 : ∀ y ∈ g.alive, ∀ w ∈ g.alive, 4 ≤ y.id.step → y.id.step = w.id.step → y = w := by
  decide +kernel

/-- **`ChainInv` falla**: el estado entero está fijado desde la cima, y fijar `mk 3 1` no deja estructura cerrada. -/
theorem k5_not_chainInv : ¬ ChainInv g := by
  intro h
  have c5 : g.current_step = 5 := rfl
  have hx : mk 3 1 ∈ g.alive := by decide
  obtain ⟨W, R', hW, _, hWx, hpin⟩ := h (fun y => y ∈ g.alive) _ k5_closed 4 (by omega)
    (fun y w hy hw h4 hs => pinned4 y hy w hw h4 hs) (mk 3 1) hx
  obtain ⟨r0, s0, hx0, _⟩ := hW.pair (hW.refl hWx) 0 (by omega) (by omega)
  obtain ⟨r1, s1, hx1, h01⟩ := hW.pair hx0 1 (by omega) (by omega)
  obtain ⟨r2, s2, h02, h12⟩ := hW.pair h01 2 (by omega) (by omega)
  obtain ⟨s, s3, h2s, _⟩ := hW.pair (hW.refl (hW.dom h02).2) 3 (by omega) (by omega)
  have hs : s = mk 3 1 := hpin s (hW.dom h2s).2 (by rw [s3]; rfl)
  subst hs
  exact no_four (hW.alive (hW.dom hx0).2) (hW.alive (hW.dom hx1).2) (hW.alive (hW.dom h02).2) hx s0 s1 s2 rfl
    (hW.adj h01) (hW.adj h02) ((adj_symm _ _ _).1 (hW.adj hx0)) (hW.adj h12)
    ((adj_symm _ _ _).1 (hW.adj hx1)) (hW.adj h2s)

end K5

/-- **El límite de la revisión**: un estado válido, cerrado y cerrado por parejas donde `ChainInv` y `NoZombie`
fallan. La revisión sola no puede dar el lector sin atascos: hace falta la construcción de la máquina. -/
theorem closed_not_chainInv : ∃ g : GPathB, g.isValid = true ∧ ClosedState g ∧ PairClosed g ∧
    ¬ ChainInv g ∧ ¬ NoZombie g :=
  ⟨K5.g, K5.k5_valid, K5.k5_closed, K5.k5_pairClosed, K5.k5_not_chainInv, K5.k5_not_noZombie⟩

end GPathB

end AbsSatBingo.Model
