-- lean/improves_bingo/AbsSatBingo/Model/SecPair.lean
import AbsSatBingo.Model.Reader
import AbsSatBingo.Model.ReviewClean

/-!
# `SecPair`: el grafo de owners es la unión de sus secciones por nodo del mapa

Propuesta §4.3 de `docs/context/escalera_reader.md` (tablas descomponibles por bit), en el grafo de owners.

**Una sección** de `g` por el nodo del mapa `b` (en el paso `b.step`) es una relación `R` entre vivos, simétrica,
dentro de la posesión, **anclada** en `b` (cada pareja de `R` tiene un nodo vivo de `b` que posee a los dos) y
**cerrada por la regla de parejas dentro de ella** (cada pareja de `R` tiene, en cada paso, una entrada común que
forma pareja de `R` con los dos). Es la parte del grafo compatible con fijar `b`, llevada a su punto fijo de
parejas.

**`SecPair g`**: en cada paso con elección, cada arista está en alguna sección de algún nodo del mapa de ese paso.
Es decir, el grafo es la unión de sus fijaciones por el paso, que es la forma de «el kernel de un estado fijado es
la unión de sus fijaciones por cualquier fila».

**Espejo en Julia**: `julia/improves_bingo/src/graph_path/graph_path_secpair.jl`. Ahí `sec_pair_bad(og; by)` calcula
la mayor sección de cada grupo (`by = :map` para `SecClosed`, `:node` para `SecClosedX`) en los pasos con
elección (`choice_at` = `choiceAt`); si no devuelve nada, vale `SecPair`/`SecPairX`. Test en
`test/graph_path/test_secpair.jl`.

`SecPairX` es lo mismo con una sección por nodo del camino (el ancla es un solo `x` para toda la sección); es más
fuerte (`secPair_of_secPairX`).

## Lo demostrado aquí

* `secClosed_of_carried`: la camarilla llevada de una solución es una sección de cada uno de sus nodos. Por eso
  `SecPair` como regla del review **no pierde soluciones**.
* `secPair_of_secPairX`.
* `pairOk_of_secPair`: `SecPair` implica la regla de parejas en cada arista (si hay algún paso con elección).
* **`PinEqSec g b`** (el pin de `b` es la mayor sección de `b`), enunciado. Mitad fácil, `sec_of_pinEdge`: toda
  arista del pin de `b` está en una sección de `b`, si el review deja el pin cerrado por parejas (`PairClosed`, que
  da `pairClosed_filterAll` bajo `ReviewExitsClean`; ver `ReviewClean.lean`).
  Con la mitad difícil (`SecInPin`, abierta): `pinEqSec_of_secInPin`.
* `noDeadEnd_of_secInPin`: `SecPair` + `SecInPin` ⇒ `NoDeadEndAt` (en un estado con alguna arista).

## Lo medido, abierto

* **`SecPairReader g₀`**: todo estado válido que visita el lector desde `g₀` cumple `SecPairX` (y así `SecPair`).
  Medido en Julia bingo (`julia/improves_bingo/test_3sat/probe_tri_sec.jl`, modos `sec`/`secx`, 28-sept-2026):
  como regla del review hasta su punto fijo, en la máquina y en todas las ramas del lector, **0 aristas cortadas**
  en 88 instancias. La sonda mira los pasos con al menos dos grupos, que son los de `choiceAt` en `sec`.
* **`SecDeadEnd`**: el puente hacia `NoDeadEnd`, que en un estado del lector `SecPair` deje algún pin válido en
  cada paso con elección. No es inmediato: la sección solo está cerrada por parejas, y el review también corta por
  padres e hijos y por enlaces.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

namespace GPathB

open Driver

-- ============================================================
-- Secciones
-- ============================================================

/-- `R` es una sección de `g` anclada en el nodo del mapa `b`. -/
structure SecClosed (g : GPathB) (b : NodeId) (R : PathNodeId → PathNodeId → Prop) : Prop where
  symm   : ∀ {y w}, R y w → R w y
  alive  : ∀ {y w}, R y w → y ∈ g.alive ∧ w ∈ g.alive
  adj    : ∀ {y w}, R y w → g.Adj y w
  anchor : ∀ {y w}, R y w → ∃ x, x ∈ g.alive ∧ x.id = b ∧ g.Adj x y ∧ g.Adj x w
  pair   : ∀ {y w}, R y w → ∀ l, 0 ≤ l → l < g.current_step → ∃ r, r.id.step = l ∧ R y r ∧ R w r

/-- `R` es una sección de `g` anclada en el nodo del camino `x`: un único ancla para todas sus parejas. -/
structure SecClosedX (g : GPathB) (x : PathNodeId) (R : PathNodeId → PathNodeId → Prop) : Prop where
  symm   : ∀ {y w}, R y w → R w y
  alive  : ∀ {y w}, R y w → y ∈ g.alive ∧ w ∈ g.alive
  adj    : ∀ {y w}, R y w → g.Adj y w
  anchor : ∀ {y w}, R y w → g.Adj x y ∧ g.Adj x w
  pair   : ∀ {y w}, R y w → ∀ l, 0 ≤ l → l < g.current_step → ∃ r, r.id.step = l ∧ R y r ∧ R w r

/-- **`SecPair`**: en cada paso con elección, cada arista está en una sección de un nodo del mapa de ese paso. -/
def SecPair (g : GPathB) : Prop :=
  ∀ k, choiceAt g k = true → ∀ y w, g.Adj y w → y ≠ w →
    ∃ b R, b.step = k ∧ SecClosed g b R ∧ R y w

/-- **`SecPairX`**: lo mismo con secciones por nodo del camino. -/
def SecPairX (g : GPathB) : Prop :=
  ∀ k, choiceAt g k = true → ∀ y w, g.Adj y w → y ≠ w →
    ∃ x R, x ∈ g.alive ∧ x.id.step = k ∧ SecClosedX g x R ∧ R y w

theorem SecClosedX.toSecClosed {g : GPathB} {x : PathNodeId} {R : PathNodeId → PathNodeId → Prop}
    (hx : x ∈ g.alive) (h : SecClosedX g x R) : SecClosed g x.id R where
  symm := h.symm
  alive := h.alive
  adj := h.adj
  anchor := fun hr => ⟨x, hx, rfl, h.anchor hr⟩
  pair := h.pair

theorem secPair_of_secPairX {g : GPathB} (h : SecPairX g) : SecPair g := by
  intro k hk y w hyw hne
  obtain ⟨x, R, hx, hxk, hsec, hr⟩ := h k hk y w hyw hne
  exact ⟨x.id, R, hxk, hsec.toSecClosed hx, hr⟩

-- ============================================================
-- No pierde soluciones: la camarilla llevada es una sección
-- ============================================================

/-- **La camarilla de una solución es una sección de cada uno de sus nodos.** Con `R` = «los dos están en la
selección», anclada en `S k`. -/
theorem secClosed_of_carried {g : GPathB} {S : Int → PathNodeId} (hc : Carried g S) {k : Int} (hk0 : 0 ≤ k)
    (hk1 : k < g.current_step) :
    SecClosedX g (S k) (fun y w => OnS g.current_step S y ∧ OnS g.current_step S w) where
  symm := fun ⟨hy, hw⟩ => ⟨hw, hy⟩
  alive := fun ⟨⟨a, ha0, ha1, hya⟩, ⟨b, hb0, hb1, hwb⟩⟩ =>
    ⟨hya ▸ hc.alive a ha0 ha1, hwb ▸ hc.alive b hb0 hb1⟩
  adj := fun ⟨hy, hw⟩ => hc.adj_on hy hw
  anchor := fun ⟨hy, hw⟩ => ⟨hc.adj_on ⟨k, hk0, hk1, rfl⟩ hy, hc.adj_on ⟨k, hk0, hk1, rfl⟩ hw⟩
  pair := fun ⟨hy, hw⟩ l hl0 hl1 =>
    ⟨S l, hc.step l hl0 hl1, ⟨hy, ⟨l, hl0, hl1, rfl⟩⟩, ⟨hw, ⟨l, hl0, hl1, rfl⟩⟩⟩

/-- Por eso toda pareja de la camarilla está en una sección del nodo que la solución elige en cada paso. -/
theorem sec_of_carried {g : GPathB} {S : Int → PathNodeId} (hc : Carried g S) {k : Int} (hk0 : 0 ≤ k)
    (hk1 : k < g.current_step) {y w : PathNodeId} (hy : OnS g.current_step S y) (hw : OnS g.current_step S w) :
    ∃ x R, x ∈ g.alive ∧ x.id.step = k ∧ SecClosedX g x R ∧ R y w :=
  ⟨S k, _, hc.alive k hk0 hk1, hc.step k hk0 hk1, secClosed_of_carried hc hk0 hk1, hy, hw⟩

-- ============================================================
-- SecPair da la regla de parejas
-- ============================================================

/-- Dentro de una sección, cada pareja tiene entrada común viva en cada paso (`commonAt`). -/
theorem commonAt_of_secClosed {g : GPathB} {b : NodeId} {R : PathNodeId → PathNodeId → Prop}
    (hs : SecClosed g b R) {y w : PathNodeId} (hr : R y w) {l : Int} (hl0 : 0 ≤ l) (hl1 : l < g.current_step) :
    g.commonAt y w l = true := by
  obtain ⟨r, hrl, hyr, hwr⟩ := hs.pair hr l hl0 hl1
  unfold commonAt
  refine List.any_eq_true.mpr ⟨r, (hs.alive hyr).2, ?_⟩
  have h1 : g.adjb y r = true := hs.adj hyr
  have h2 : g.adjb w r = true := hs.adj hwr
  simp [hrl, h1, h2]

/-- **`SecPair` implica la regla de parejas** en cada arista, en cuanto hay un paso con elección. -/
theorem pairOk_of_secPair {g : GPathB} (h : SecPair g) {k : Int} (hk : choiceAt g k = true) {y w : PathNodeId}
    (hyw : g.Adj y w) (hne : y ≠ w) : g.pairOk y w = true := by
  obtain ⟨b, R, _, hs, hr⟩ := h k hk y w hyw hne
  unfold pairOk
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨hl0, hl1⟩ := intRange_bounds hl
  exact commonAt_of_secClosed hs hr hl0 (by omega)

-- ============================================================
-- Lo medido y el puente, como enunciados abiertos
-- ============================================================

/-- **Medido, abierto**: todo estado válido del lector desde `g₀` cumple `SecPairX`. -/
def SecPairReader (g₀ : GPathB) : Prop :=
  ∀ h, Visited g₀ h → h.isValid = true → SecPairX h

/-- `NoDeadEnd` en un estado: en cada paso con elección, algún pin deja el estado válido. -/
def NoDeadEndAt (h : GPathB) : Prop :=
  ∀ k, choiceAt h k = true → ∃ q ∈ h.alive, q.id.step = k ∧ (h.filterAll [q.id]).isValid = true

/-- **El puente, abierto**: en un estado del lector, `SecPair` no deja callejones. -/
def SecDeadEnd (g₀ : GPathB) : Prop :=
  ∀ h, Visited g₀ h → h.isValid = true → SecPair h → NoDeadEndAt h

theorem noDeadEnd_of_secPair {g₀ : GPathB} (hr : SecPairReader g₀) (hb : SecDeadEnd g₀) {h : GPathB}
    (hv : Visited g₀ h) (hval : h.isValid = true) : NoDeadEndAt h :=
  hb h hv hval (secPair_of_secPairX (hr h hv hval))


-- ============================================================
-- PinEqSec: el pin de `b` es la mayor sección de `b`
-- ============================================================

/-! Medido en Julia (`test_3sat/probe_sec_vs_pin.jl`): 17 158 de 17 158 iguales en 88 instancias, todas las ramas
del lector. Aquí: la mitad fácil (el pin es una sección) demostrada, bajo que el review deje el pin cerrado por
parejas; la mitad difícil (toda sección sobrevive al review del pin) queda como `SecInPin`; y con ella y `SecPair`,
`NoDeadEndAt` (`noDeadEnd_of_secInPin`). -/

/-- Una arista del estado tras el pin: válido, sus dos extremos vivos y se poseen. -/
def PinEdge (h : GPathB) (y w : PathNodeId) : Prop :=
  h.isValid = true ∧ y ∈ h.alive ∧ w ∈ h.alive ∧ h.Adj y w

/-- **`PinEqSec g b`**: las aristas del pin de `b` son exactamente las que están en alguna sección de `b` (aristas:
`y ≠ w`, como compara Julia). -/
def PinEqSec (g : GPathB) (b : NodeId) : Prop :=
  ∀ y w, y ≠ w → (PinEdge (g.filterAll [b]) y w ↔ ∃ R, SecClosed g b R ∧ R y w)

/-- La mitad difícil, **abierta**: toda sección de `b` sobrevive al pin de `b` (el review no corta dentro de ella). -/
def SecInPin (g : GPathB) (b : NodeId) : Prop :=
  ∀ R, SecClosed g b R → ∀ y w, y ≠ w → R y w → PinEdge (g.filterAll [b]) y w

/-- Tras `filterRequire b` (sobre un estado válido en el que todo vivo tiene documento), en el paso de `b` solo
quedan vivos de `b`. -/
theorem pinned_filterRequire {g : GPathB} (hd : AliveDocs g) (hv : g.isValid = true) (b : NodeId) :
    ∀ q ∈ (g.filterRequire b).alive, q.id.step = b.step → q.id = b := by
  intro q hq hqs
  unfold filterRequire at hq
  rw [if_pos hv] at hq
  dsimp only at hq
  rw [alive_foldl_killVertex] at hq
  obtain ⟨hqa, hnc⟩ := List.mem_filter.mp hq
  by_cases hqb : q.id = b
  · exact hqb
  · exfalso
    obtain ⟨n, hn, hnid⟩ := hd q hqa
    have hmem : q ∈ ((g.line b.step).map (·.id)).filter (fun q => q.id != b) := by
      refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨n, ?_, hnid⟩, by simp [hqb]⟩
      unfold line
      exact List.mem_filter.mpr ⟨hn, by simp [hnid, hqs]⟩
    have hcont : List.contains (((g.line b.step).map (·.id)).filter (fun q => q.id != b)) q = true :=
      List.elem_eq_true_of_mem hmem
    rw [hcont] at hnc
    exact absurd hnc (by decide)

theorem pinned_filterAll {g : GPathB} (hd : AliveDocs g) (hv : g.isValid = true) (b : NodeId) :
    ∀ q ∈ (g.filterAll [b]).alive, q.id.step = b.step → q.id = b := by
  intro q hq hqs
  have hsub := (shrinks_review (g.filterRequire b)).1
  exact pinned_filterRequire hd hv b q (hsub.alive q hq) hqs

/-- **El pin es una sección** (la mitad fácil, en abstracto): un estado `h` por debajo de `g`, cerrado por parejas,
en el que el paso de `b` solo tiene vivos de `b`, da una sección de `b` en `g`: sus parejas buenas. -/
theorem secClosed_of_pinned {g h : GPathB} {b : NodeId} (hs : Sub h g)
    (hpin : ∀ q ∈ h.alive, q.id.step = b.step → q.id = b) (hpc : PairClosed h)
    (hb0 : 0 ≤ b.step) (hb1 : b.step < h.current_step) :
    SecClosed g b (fun y w => y ∈ h.alive ∧ w ∈ h.alive ∧ h.Adj y w ∧ h.pairOk y w = true) where
  symm := fun ⟨hy, hw, ha, hp⟩ => ⟨hw, hy, (adj_symm h _ _).mp ha, by rw [pairOk_comm]; exact hp⟩
  alive := fun ⟨hy, hw, _, _⟩ => ⟨hs.alive _ hy, hs.alive _ hw⟩
  adj := fun ⟨_, _, ha, _⟩ => hs.adj _ _ ha
  anchor := by
    rintro y w ⟨_, _, _, hok⟩
    unfold pairOk at hok
    have hc := List.all_eq_true.mp hok b.step (mem_intRange hb0 (by omega))
    unfold commonAt at hc
    obtain ⟨r, hr, hrc⟩ := List.any_eq_true.mp hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hrc
    obtain ⟨⟨hrs, hyr⟩, hwr⟩ := hrc
    refine ⟨r, hs.alive r hr, hpin r hr hrs, ?_, ?_⟩
    · exact hs.adj _ _ ((adj_symm h _ _).mp hyr)
    · exact hs.adj _ _ ((adj_symm h _ _).mp hwr)
  pair := by
    rintro y w ⟨hy, hw, _, hok⟩ l hl0 hl1
    have hok' := hok
    unfold pairOk at hok'
    rw [hs.step] at hok'
    have hc := List.all_eq_true.mp hok' l (mem_intRange hl0 (by omega))
    unfold commonAt at hc
    obtain ⟨r, hr, hrc⟩ := List.any_eq_true.mp hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hrc
    obtain ⟨⟨hrs, hyr⟩, hwr⟩ := hrc
    -- la pareja con `r` es buena: si `r` es el propio nodo, por la reflexiva; si no, por `PairClosed`
    have good : ∀ z, z ∈ h.alive → h.pairOk z z = true → h.adjb z r = true → h.pairOk z r = true := by
      intro z hz hzz hzr
      by_cases hzr' : z = r
      · subst hzr'; exact hzz
      · exact hpc z r hzr' hz hr hzr
    have hyy : h.pairOk y y = true := pairOk_self_of hok
    have hww : h.pairOk w w = true := pairOk_self_of (by rw [pairOk_comm]; exact hok)
    exact ⟨r, hrs, ⟨hy, hr, hyr, good y hy hyy hyr⟩, ⟨hw, hr, hwr, good w hw hww hwr⟩⟩

/-- **La mitad fácil de `PinEqSec`**: toda arista del pin de `b` está en una sección de `b`, si el review deja el
pin cerrado por parejas. -/
theorem sec_of_pinEdge {g : GPathB} (hd : AliveDocs g) (hv : g.isValid = true) {b : NodeId}
    (hb0 : 0 ≤ b.step) (hb1 : b.step < g.current_step) (hpc : PairClosed (g.filterAll [b]))
    {y w : PathNodeId} (hne : y ≠ w) (he : PinEdge (g.filterAll [b]) y w) : ∃ R, SecClosed g b R ∧ R y w := by
  have hsub := (shrinks_filterAll g [b]).1
  obtain ⟨_, hy, hw, ha⟩ := he
  exact ⟨_, secClosed_of_pinned hsub (pinned_filterAll hd hv b) hpc hb0 (by rw [hsub.step]; exact hb1),
    hy, hw, ha, hpc y w hne hy hw ha⟩

/-- El pin sale cerrado por parejas si el filtro quitó algo (`dirty`) y el review sale sin `dirty`
(`pairClosed_review`; lo segundo es `ReviewExitsClean`). -/
theorem pairClosed_filterAll {g : GPathB} {b : NodeId} (hd : (g.filterRequire b).dirty = true)
    (hce : ReviewExitsClean (g.filterRequire b)) (hv : (g.filterAll [b]).isValid = true) :
    PairClosed (g.filterAll [b]) :=
  pairClosed_review hd hv (hce hv)

/-- `PinEqSec` a partir de su mitad difícil. -/
theorem pinEqSec_of_secInPin {g : GPathB} (hd : AliveDocs g) (hv : g.isValid = true) {b : NodeId}
    (hb0 : 0 ≤ b.step) (hb1 : b.step < g.current_step) (hpc : PairClosed (g.filterAll [b]))
    (hin : SecInPin g b) : PinEqSec g b := by
  intro y w hne
  constructor
  · exact sec_of_pinEdge hd hv hb0 hb1 hpc hne
  · rintro ⟨R, hs, hr⟩
    exact hin R hs y w hne hr

/-- **`SecPair` y la mitad difícil dan `NoDeadEnd`**: en un estado con alguna arista, en cada paso con elección el
nodo del mapa de la sección que contiene esa arista deja un pin válido. -/
theorem noDeadEnd_of_secInPin {g : GPathB} (hsp : SecPair g) (hin : ∀ b, SecInPin g b)
    (hedge : ∃ y w, g.Adj y w ∧ y ≠ w) : NoDeadEndAt g := by
  intro k hk
  obtain ⟨y, w, hyw, hne⟩ := hedge
  obtain ⟨b, R, hbk, hs, hr⟩ := hsp k hk y w hyw hne
  obtain ⟨x, hx, hxb, _, _⟩ := hs.anchor hr
  refine ⟨x, hx, by rw [hxb, hbk], ?_⟩
  rw [hxb]
  exact (hin b R hs y w hne hr).1

end GPathB

end AbsSatBingo.Model
