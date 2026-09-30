-- lean/improves_bingo/AbsSatBingo/Model/ForbidSound.lean
import AbsSatBingo.Model.Machine

/-!
# Tríos prohibidos: solidez (`ForbidSound`)

Espejo de `FORBID` en Julia (`PathOwnersGraph.Edge.forbid`, `up_forbid!`, `join_forbid`, `forbid_rule!`): cada arista
guarda los tríos que ninguna solución puede contener. Aquí los tríos son una relación `F : Trios` junto al estado, y
cada operación de Julia es una función que da la relación nueva. **Cada definición de Lean contiene a la de Julia**
(Julia solo guarda tríos entre vecinos vivos, y comprueba menos casos), así que la solidez de Lean da la de Julia.

**`ForbidSound Sol g F`**: una rama solución llevada por el estado (`Carried g S`; las de las asignaciones que
satisfacen `φ` lo son, `run_carries`) no pasa por ningún trío prohibido (`Avoids F T S`). Se conserva:

* **UP** (`avoids_upF`): `(n, y, z)` se prohíbe si `(p, y, z)` lo está en `g` para **todo** padre `p` de `n` (o falta
  una de sus aristas). La rama pasa por uno de los padres (`hpar`, la hipótesis de `carried_up`).
* **join** (`avoids_joinF_left`, `avoids_joinF_right`): se prohíbe lo que lo está **en los dos lados**. La rama está
  en uno de ellos. Aquí nacen los tríos que mezclan ramas: sus tres aristas no están en ningún lado.
* **review** (`avoids_ruleF`, `carried_forbidSweep`): un trío sin testigo bueno en algún paso se prohíbe, y una
  arista sin testigo bueno se corta. El nodo de la rama en cada paso es un testigo bueno.

Ninguno de los tres pasos usa B1 ni `SibStarInv`: solo que la rama viene de un padre (UP) y de un lado (join).
`Avoids` mira todos los órdenes de un trío (`avoids_sym`), como Julia, que guarda el trío en sus tres aristas.

El límite (`ClosedLimit.lean`) sigue en pie: guardar tríos no hace que el estado tenga camarilla. Lo que da es
memoria: la espina sin revisión que no elige ningún trío prohibido no se atascó nunca (`probe_forbid.jl`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- Tríos de nodos de camino. -/
abbrev Trios := PathNodeId → PathNodeId → PathNodeId → Prop

/-- Los tríos solo nombran nodos de pasos por debajo de `T`. -/
def FBelow (F : Trios) (T : Int) : Prop :=
  ∀ x y z, F x y z → x.id.step < T ∧ y.id.step < T ∧ z.id.step < T

/-- **La rama `S` (pasos `0 … T-1`) no pasa por ningún trío de `F`**, en ningún orden. -/
def Avoids (F : Trios) (T : Int) (S : Int → PathNodeId) : Prop :=
  ∀ i j k, 0 ≤ i → i < T → 0 ≤ j → j < T → 0 ≤ k → k < T → ¬ F (S i) (S j) (S k)

/-- **`ForbidSound Sol g F`**: toda rama solución (`Sol`) llevada por `g` esquiva los tríos prohibidos. `Sol` son las
ramas de las asignaciones que satisfacen `φ` (`pidOfAssign`). No vale para toda camarilla de `g`: una camarilla del
join puede mezclar los dos lados, y el join prohíbe justo esos tríos. -/
def ForbidSound (Sol : (Int → PathNodeId) → Prop) (g : GPathB) (F : Trios) : Prop :=
  ∀ S, Sol S → Carried g S → Avoids F g.current_step S

/-- El cierre simétrico: el trío guardado en sus tres aristas (Julia `forbid!`). -/
def Sym (F : Trios) : Trios := fun x y z =>
  F x y z ∨ F x z y ∨ F y x z ∨ F y z x ∨ F z x y ∨ F z y x

theorem avoids_sym {F : Trios} {T : Int} {S : Int → PathNodeId} (h : Avoids F T S) : Avoids (Sym F) T S := by
  intro i j k h0 h1 h2 h3 h4 h5 hs
  rcases hs with hs | hs | hs | hs | hs | hs
  · exact h i j k h0 h1 h2 h3 h4 h5 hs
  · exact h i k j h0 h1 h4 h5 h2 h3 hs
  · exact h j i k h2 h3 h0 h1 h4 h5 hs
  · exact h j k i h2 h3 h4 h5 h0 h1 hs
  · exact h k i j h4 h5 h0 h1 h2 h3 hs
  · exact h k j i h4 h5 h2 h3 h0 h1 hs

theorem avoids_mono {F G : Trios} {T : Int} {S : Int → PathNodeId} (h : Avoids F T S)
    (hGF : ∀ x y z, G x y z → F x y z) : Avoids G T S :=
  fun i j k h0 h1 h2 h3 h4 h5 hg => h i j k h0 h1 h2 h3 h4 h5 (hGF _ _ _ hg)

/-- En el lado `g`, no hay solución por `a`, `b` y `r`: falta una de las tres aristas, o el trío está prohibido
(Julia `side_forbids`). -/
def SideForbids (g : GPathB) (F : Trios) (a b r : PathNodeId) : Prop :=
  ¬ (g.Adj a b ∧ g.Adj a r ∧ g.Adj b r) ∨ F a b r

/-- **Una rama llevada que esquiva `F` no está prohibida en su lado.** -/
theorem not_sideForbids {g : GPathB} {F : Trios} {S : Int → PathNodeId} (h : Carried g S)
    (hA : Avoids F g.current_step S) {i j k : Int} (h0 : 0 ≤ i) (h1 : i < g.current_step) (h2 : 0 ≤ j)
    (h3 : j < g.current_step) (h4 : 0 ≤ k) (h5 : k < g.current_step) : ¬ SideForbids g F (S i) (S j) (S k) := by
  rintro (hn | hf)
  · exact hn ⟨h.adj i j h0 h1 h2 h3, h.adj i k h0 h1 h4 h5, h.adj j k h2 h3 h4 h5⟩
  · exact hA i j k h0 h1 h2 h3 h4 h5 hf

-- ============================================================
-- UP
-- ============================================================

/-- **Los tríos tras el UP** (Julia `up_forbid!`): los de antes, y `(x, y, z)` con `x` de la fila nueva e `y`, `z`
debajo, si para todo padre `p` de `x` el lado prohíbe `(p, y, z)`. -/
def upF (g : GPathB) (F : Trios) (d : NodeId) : Trios := fun x y z =>
  F x y z ∨ (x.id.step = g.current_step ∧ y.id.step < g.current_step ∧ z.id.step < g.current_step ∧
    ∀ p ∈ g.rowParents d x, SideForbids g F p y z)

theorem fBelow_upF {g : GPathB} {F : Trios} {d : NodeId} (hB : FBelow F g.current_step) :
    FBelow (upF g F d) (g.current_step + 1) := by
  rintro x y z (hf | ⟨hx, hy, hz, _⟩)
  · obtain ⟨a, b, c⟩ := hB x y z hf; exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩

/-- **El UP es sólido**: con las hipótesis de `carried_up` (la rama viene de un padre de su nodo nuevo). -/
theorem avoids_upF {g : GPathB} {F : Trios} {d : NodeId} {S : Int → PathNodeId} (h : Carried g S)
    (hA : Avoids F g.current_step S) (hB : FBelow F g.current_step)
    (hpar : 0 < g.current_step → S (g.current_step - 1) ∈ g.rowParents d (S g.current_step))
    (hstep : (S g.current_step).id.step = g.current_step) :
    Avoids (upF g F d) (g.current_step + 1) S := by
  have hst : ∀ i, 0 ≤ i → i < g.current_step + 1 → (S i).id.step = i := by
    intro i h0 h1
    by_cases hi : i < g.current_step
    · exact h.step i h0 hi
    · rw [show i = g.current_step by omega]; exact hstep
  intro i j k h0 h1 h2 h3 h4 h5 hf
  rcases hf with hf | ⟨hx, hy, hz, hall⟩
  · obtain ⟨a, b, c⟩ := hB _ _ _ hf
    rw [hst i h0 h1] at a; rw [hst j h2 h3] at b; rw [hst k h4 h5] at c
    exact hA i j k h0 a h2 b h4 c hf
  · rw [hst i h0 h1] at hx; rw [hst j h2 h3] at hy; rw [hst k h4 h5] at hz
    subst hx
    have hpos : 0 < g.current_step := by omega
    exact not_sideForbids h hA (by omega) (by omega) h2 hy h4 hz (hall _ (hpar hpos))

-- ============================================================
-- join
-- ============================================================

/-- **Los tríos tras el join** (Julia `join_forbid`): los que los dos lados prohíben, entre nodos por debajo de `T`. -/
def joinF (T : Int) (g₁ : GPathB) (F₁ : Trios) (g₂ : GPathB) (F₂ : Trios) : Trios := fun a b r =>
  a.id.step < T ∧ b.id.step < T ∧ r.id.step < T ∧ SideForbids g₁ F₁ a b r ∧ SideForbids g₂ F₂ a b r

theorem fBelow_joinF (T : Int) (g₁ : GPathB) (F₁ : Trios) (g₂ : GPathB) (F₂ : Trios) :
    FBelow (joinF T g₁ F₁ g₂ F₂) T :=
  fun _ _ _ ⟨a, b, c, _, _⟩ => ⟨a, b, c⟩

/-- **El join es sólido** para una rama del lado izquierdo. -/
theorem avoids_joinF_left {g₁ g₂ : GPathB} {F₁ F₂ : Trios} {S : Int → PathNodeId} (h : Carried g₁ S)
    (hA : Avoids F₁ g₁.current_step S) : Avoids (joinF g₁.current_step g₁ F₁ g₂ F₂) g₁.current_step S :=
  fun _ _ _ h0 h1 h2 h3 h4 h5 ⟨_, _, _, hs, _⟩ => not_sideForbids h hA h0 h1 h2 h3 h4 h5 hs

/-- **El join es sólido** para una rama del lado derecho. -/
theorem avoids_joinF_right {g₁ g₂ : GPathB} {F₁ F₂ : Trios} {S : Int → PathNodeId}
    (hcs : g₁.current_step = g₂.current_step) (h : Carried g₂ S) (hA : Avoids F₂ g₂.current_step S) :
    Avoids (joinF g₁.current_step g₁ F₁ g₂ F₂) g₁.current_step S := by
  rw [hcs]
  exact fun i j k h0 h1 h2 h3 h4 h5 ⟨_, _, _, _, hs⟩ => not_sideForbids h hA h0 h1 h2 h3 h4 h5 hs

/-- **El join, a nivel de estado**: si cada rama solución de la unión está llevada por uno de los lados (las de las
asignaciones lo están: la del lado de su clave, `advance_has`), los tríos de la unión son sólidos. -/
theorem forbidSound_join {Sol : (Int → PathNodeId) → Prop} {g₁ g₂ : GPathB} {F₁ F₂ : Trios}
    (h₁ : ForbidSound Sol g₁ F₁) (h₂ : ForbidSound Sol g₂ F₂) (hcs : g₁.current_step = g₂.current_step)
    (hside : ∀ S, Sol S → Carried (join g₁ g₂) S → Carried g₁ S ∨ Carried g₂ S) :
    ForbidSound Sol (join g₁ g₂) (joinF g₁.current_step g₁ F₁ g₂ F₂) := by
  intro S hS hc
  show Avoids _ g₁.current_step S
  rcases hside S hS hc with h | h
  · exact avoids_joinF_left h (h₁ S hS h)
  · exact avoids_joinF_right hcs h (h₂ S hS h)

-- ============================================================
-- review: la regla
-- ============================================================

/-- `s` es testigo bueno del trío `(a, b, r)`: vecino de los tres, sin trío prohibido con ninguna pareja. -/
def GoodWitness (g : GPathB) (F : Trios) (a b r s : PathNodeId) : Prop :=
  g.Adj a s ∧ g.Adj b s ∧ g.Adj r s ∧ ¬ F a b s ∧ ¬ F a r s ∧ ¬ F b r s

/-- **Los tríos tras una vuelta de la regla** (Julia `forbid_rule!`, fase 1): los de antes, y los que en algún paso
no tienen testigo bueno. -/
def ruleF (g : GPathB) (F : Trios) : Trios := fun a b r =>
  F a b r ∨ (a.id.step < g.current_step ∧ b.id.step < g.current_step ∧ r.id.step < g.current_step ∧
    ∃ l, 0 ≤ l ∧ l < g.current_step ∧ ∀ s, s ∈ g.alive → s.id.step = l → ¬ GoodWitness g F a b r s)

theorem fBelow_ruleF {g : GPathB} {F : Trios} (hB : FBelow F g.current_step) : FBelow (ruleF g F) g.current_step := by
  rintro x y z (hf | ⟨a, b, c, _⟩)
  · exact hB x y z hf
  · exact ⟨a, b, c⟩

/-- El nodo de la rama en cada paso es testigo bueno de todo trío de la rama. -/
theorem goodWitness_of {g : GPathB} {F : Trios} {S : Int → PathNodeId} (h : Carried g S)
    (hA : Avoids F g.current_step S) {i j k l : Int} (h0 : 0 ≤ i) (h1 : i < g.current_step) (h2 : 0 ≤ j)
    (h3 : j < g.current_step) (h4 : 0 ≤ k) (h5 : k < g.current_step) (h6 : 0 ≤ l) (h7 : l < g.current_step) :
    GoodWitness g F (S i) (S j) (S k) (S l) :=
  ⟨h.adj i l h0 h1 h6 h7, h.adj j l h2 h3 h6 h7, h.adj k l h4 h5 h6 h7, hA i j l h0 h1 h2 h3 h6 h7,
   hA i k l h0 h1 h4 h5 h6 h7, hA j k l h2 h3 h4 h5 h6 h7⟩

/-- **La regla es sólida**: no prohíbe ningún trío de una rama llevada. -/
theorem avoids_ruleF {g : GPathB} {F : Trios} {S : Int → PathNodeId} (h : Carried g S)
    (hA : Avoids F g.current_step S) : Avoids (ruleF g F) g.current_step S := by
  intro i j k h0 h1 h2 h3 h4 h5 hf
  rcases hf with hf | ⟨_, _, _, l, h6, h7, hno⟩
  · exact hA i j k h0 h1 h2 h3 h4 h5 hf
  · exact hno (S l) (h.alive l h6 h7) (h.step l h6 h7) (goodWitness_of h hA h0 h1 h2 h3 h4 h5 h6 h7)

-- ============================================================
-- review: el corte de aristas
-- ============================================================

/-- La arista `a`–`b` tiene testigo bueno en cada paso (Julia `edge_alive`). -/
def EdgeAliveF (g : GPathB) (F : Trios) (a b : PathNodeId) : Prop :=
  ∀ l, 0 ≤ l → l < g.current_step → ∃ r ∈ g.alive, r.id.step = l ∧ g.Adj a r ∧ g.Adj b r ∧ ¬ F a b r

theorem edgeAliveF_of_onS {g : GPathB} {F : Trios} {S : Int → PathNodeId} (h : Carried g S)
    (hA : Avoids F g.current_step S) {x w : PathNodeId} (hx : OnS g.current_step S x)
    (hw : OnS g.current_step S w) : EdgeAliveF g F x w := by
  obtain ⟨i, h0, h1, rfl⟩ := hx
  obtain ⟨j, h2, h3, rfl⟩ := hw
  intro l h6 h7
  exact ⟨S l, h.alive l h6 h7, h.step l h6 h7, h.adj i l h0 h1 h6 h7, h.adj j l h2 h3 h6 h7,
    hA i j l h0 h1 h2 h3 h6 h7⟩

open Classical in
/-- **El corte de la regla** (Julia `forbid_rule!`, fase 2): se quitan a la vez las aristas sin testigo bueno. -/
noncomputable def forbidSweep (g : GPathB) (F : Trios) : GPathB :=
  (g.edges.filter (fun e => !decide (EdgeAliveF g F e.1 e.2))).foldl (fun h e => h.removeEdge e.1 e.2) g

open Classical in
/-- **El corte conserva la rama.** -/
theorem carried_forbidSweep {g : GPathB} {F : Trios} {S : Int → PathNodeId} (h : Carried g S)
    (hA : Avoids F g.current_step S) : Carried (forbidSweep g F) S := by
  unfold forbidSweep
  refine (carried_foldl (cs := g.current_step) (fun h (e : PathNodeId × PathNodeId) => h.removeEdge e.1 e.2) _
    ?_ g h rfl).1
  intro g' e he hc hcs
  refine ⟨carried_removeEdge hc ?_, hcs⟩
  rw [hcs]
  rintro ⟨hx, hw⟩
  have := (List.mem_filter.mp he).2
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
  exact this (edgeAliveF_of_onS h hA hx hw)

theorem step_forbidSweep (g : GPathB) (F : Trios) : (forbidSweep g F).current_step = g.current_step := by
  unfold forbidSweep
  generalize g.edges.filter _ = l
  induction l generalizing g with
  | nil => rfl
  | cons e es ih => exact ih (g.removeEdge e.1 e.2)

/-- **Una vuelta de la regla**: tríos nuevos y corte, con la rama llevada y esquivando los tríos. -/
theorem forbidRound_sound {g : GPathB} {F : Trios} {S : Int → PathNodeId} (h : Carried g S)
    (hA : Avoids F g.current_step S) :
    Carried (forbidSweep g (ruleF g F)) S ∧ Avoids (ruleF g F) (forbidSweep g (ruleF g F)).current_step S := by
  have hA' := avoids_ruleF h hA
  refine ⟨carried_forbidSweep h hA', ?_⟩
  rw [step_forbidSweep]; exact hA'

-- ============================================================
-- Lo que da al lector
-- ============================================================

/-- **Un trío prohibido no está en ninguna solución**: si la rama de una asignación que satisface `φ` está llevada
por un estado con tríos sólidos, no pasa por ningún trío prohibido (en ningún orden). -/
theorem not_forbidden_of_sound {Sol : (Int → PathNodeId) → Prop} {g : GPathB} {F : Trios}
    (hs : ForbidSound Sol g F) {S : Int → PathNodeId} (hS : Sol S) (h : Carried g S) :
    Avoids (Sym F) g.current_step S :=
  avoids_sym (hs S hS h)

end GPathB

end AbsSatBingo.Model
