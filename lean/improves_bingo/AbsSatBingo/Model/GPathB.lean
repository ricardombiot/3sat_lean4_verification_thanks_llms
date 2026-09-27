-- lean/improves_bingo/AbsSatBingo/Model/GPathB.lean
import AbsSatBin.GraphPath.Model.GPathM

/-!
# `GPathB` — el gpath con grafo de owners

Fase L1 de `docs/plans/lean_bingo.md`. Espejo de `julia/improves_bingo` (`GPath` + `PathOwnersGraph`): los owners
ya no son una tabla por nodo sino un **grafo por gpath**:

* `alive` — los nodos vivos (Julia `og.alive`; en `GPathM`, `gowners`);
* `edges` — las compatibilidades entre dos nodos distintos (Julia `og.edges`), en **una** orientación cualquiera.

La relación de posesión es `Adj`: reflexiva en los vivos y **simétrica por definición** (`adj_symm`), sin orden
entre ids. Quitar una arista quita sus dos orientaciones. Como en `GPathM`, es un modelo de especificación: listas
planas, validez derivada y cada poda un `filter`, de modo que «solo borra» (`Sub`) sale de lemas genéricos.

Diferencia con Julia a propósito: Julia guarda la incidencia (`inc`) como índice; aquí los vecinos se calculan
(`neighborsAt`), y una arista con un extremo muerto no cuenta (`neighborsAt` filtra por `alive`), así que el modelo
no necesita el invariante «aristas entre vivos» para dar la validez de Julia.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange)

-- ============================================================
-- Estructuras
-- ============================================================

/-- Un nodo de camino: solo la estructura (Julia `PathDocNode` sin owners). -/
structure PNodeB where
  id      : PathNodeId
  title   : String
  parents : List PathNodeId
  sons    : List PathNodeId
  deriving Repr, DecidableEq

def PNodeB.weight (n : PNodeB) : Nat :=
  1 + n.parents.length + n.sons.length

/-- El gpath: los nodos, y el grafo de owners (`alive` + `edges`). -/
structure GPathB where
  nodes        : List PNodeB
  alive        : List PathNodeId
  edges        : List (PathNodeId × PathNodeId)
  current_step : Int
  map_parent   : Option NodeId
  /-- Julia `review_owners`: algo cambió y el review tiene que correr. Lo activan el filtro por requisito,
  la ventana saltada del UP y toda poda del review; el review solo corre con él activo. Hace falta para que
  los estados coincidan con los de Julia (sin él, el modelo revisaría más a menudo). -/
  dirty        : Bool
  deriving Repr

namespace GPathB

def empty : GPathB :=
  { nodes := [], alive := [], edges := [], current_step := 0, map_parent := none, dirty := false }

-- ============================================================
-- Vistas derivadas
-- ============================================================

def line (g : GPathB) (k : Int) : List PNodeB :=
  g.nodes.filter (fun n => n.id.id.step == k)

def node? (g : GPathB) (id : PathNodeId) : Option PNodeB :=
  g.nodes.find? (fun n => n.id == id)

def isAlive (g : GPathB) (x : PathNodeId) : Bool :=
  g.alive.contains x

/-- La arista `e` une `x` y `w`, en cualquiera de sus dos orientaciones. -/
def joins (x w : PathNodeId) (e : PathNodeId × PathNodeId) : Bool :=
  (e.1 == x && e.2 == w) || (e.1 == w && e.2 == x)

def hasEdge (g : GPathB) (x w : PathNodeId) : Bool :=
  g.edges.any (joins x w)

/-- **La posesión**: `x` posee a `w` si son el mismo nodo vivo o hay una arista entre ellos. -/
def adjb (g : GPathB) (x w : PathNodeId) : Bool :=
  (x == w && g.isAlive x) || g.hasEdge x w

def Adj (g : GPathB) (x w : PathNodeId) : Prop := g.adjb x w = true

instance (g : GPathB) (x w : PathNodeId) : Decidable (g.Adj x w) :=
  inferInstanceAs (Decidable (g.adjb x w = true))

/-- Los vecinos vivos de `x` en el paso `k` (Julia `neighbors(og, x, k)`). -/
def neighborsAt (g : GPathB) (x : PathNodeId) (k : Int) : List PathNodeId :=
  g.alive.filter (fun w => w.id.step == k && g.adjb x w)

def hasNeighborAt (g : GPathB) (x : PathNodeId) (k : Int) : Bool :=
  g.alive.any (fun w => w.id.step == k && g.adjb x w)

/-- La tabla de `x` es válida: `x` vive y tiene un vecino vivo en cada paso por debajo de `current_step`
(Julia `is_owners_valid`). -/
def ownersOk (g : GPathB) (x : PathNodeId) : Bool :=
  g.isAlive x && (intRange 0 (g.current_step - 1)).all (g.hasNeighborAt x)

/-- El gpath es válido si cada paso por debajo de `current_step` tiene un vivo (Julia `og.valid`). -/
def isValid (g : GPathB) : Bool :=
  (intRange 0 (g.current_step - 1)).all (fun k => g.alive.any (fun q => q.id.step == k))

/-- Las reglas de validez de un nodo (Julia `is_valid_node_by`), con la tabla leída del grafo. -/
def isValidNode (g : GPathB) (n : PNodeB) : Bool :=
  let owners_ok := g.ownersOk n.id
  let is_root := n.id.parent_id.isNone
  let is_last := n.id.id.step == g.current_step - 1
  let have_parents := !n.parents.isEmpty
  let have_sons := !n.sons.isEmpty
  if is_root then
    if is_last then owners_ok else owners_ok && have_sons
  else if is_last then
    owners_ok && have_parents
  else
    owners_ok && have_parents && have_sons

/-- Todo lo que una poda puede encoger: vivos, aristas y enlaces. -/
def measure (g : GPathB) : Nat :=
  g.alive.length + g.edges.length + (g.nodes.map PNodeB.weight).sum

-- ============================================================
-- La simetría
-- ============================================================

theorem joins_comm (x w : PathNodeId) (e : PathNodeId × PathNodeId) : joins x w e = joins w x e := by
  unfold joins; exact Bool.or_comm _ _

theorem hasEdge_comm (g : GPathB) (x w : PathNodeId) : g.hasEdge x w = g.hasEdge w x := by
  unfold hasEdge
  have : joins x w = joins w x := funext (joins_comm x w)
  rw [this]

theorem adjb_comm (g : GPathB) (x w : PathNodeId) : g.adjb x w = g.adjb w x := by
  unfold adjb
  rw [hasEdge_comm g x w]
  by_cases h : x = w
  · subst h; rfl
  · have h1 : (x == w) = false := beq_false_of_ne h
    have h2 : (w == x) = false := beq_false_of_ne (Ne.symm h)
    rw [h1, h2]; simp

/-- **La posesión es simétrica**, por definición. -/
theorem adj_symm (g : GPathB) (x w : PathNodeId) : g.Adj x w ↔ g.Adj w x := by
  unfold Adj; rw [adjb_comm]

theorem adj_refl (g : GPathB) (x : PathNodeId) (h : x ∈ g.alive) : g.Adj x x := by
  unfold Adj adjb isAlive
  simp [h]

theorem adj_iff (g : GPathB) (x w : PathNodeId) :
    g.Adj x w ↔ (x = w ∧ x ∈ g.alive) ∨ ∃ e ∈ g.edges, (e.1 = x ∧ e.2 = w) ∨ (e.1 = w ∧ e.2 = x) := by
  unfold Adj adjb isAlive hasEdge joins
  simp [List.any_eq_true]

-- ============================================================
-- Primitivas
-- ============================================================

/-- Quita la arista entre `x` y `w`, en sus dos orientaciones. -/
def removeEdge (g : GPathB) (x w : PathNodeId) : GPathB :=
  { g with edges := g.edges.filter (fun e => !joins x w e) }

/-- Añade la arista entre `x` y `w` si son distintos y todavía no está. -/
def addEdge (g : GPathB) (x w : PathNodeId) : GPathB :=
  if x == w || g.hasEdge x w then g else { g with edges := g.edges ++ [(x, w)] }

/-- La arista toca a `id`. -/
def touches (id : PathNodeId) (e : PathNodeId × PathNodeId) : Bool :=
  e.1 == id || e.2 == id

/-- El nodo sale del grafo de owners con todas sus aristas (Julia `PathOwnersGraph.remove_node!`). Su
documento sigue en `nodes`: lo quita la purga (`removeNode`), como en Julia. -/
def killVertex (g : GPathB) (id : PathNodeId) : GPathB :=
  { g with alive := g.alive.filter (· != id), edges := g.edges.filter (fun e => !touches id e) }

def unlinkAll (id : PathNodeId) (n : PNodeB) : PNodeB :=
  { n with parents := n.parents.filter (· != id), sons := n.sons.filter (· != id) }

/-- Eliminar un nodo: sale del grafo y de la colección, y nadie lo tiene ya como padre o hijo
(Julia `remove_node_owner!` + `clean_links!` + la retirada física del `filter!`). -/
def removeNode (g : GPathB) (id : PathNodeId) : GPathB :=
  let g := g.killVertex id
  { g with nodes := (g.nodes.filter (fun n => n.id != id)).map (unlinkAll id) }

-- ============================================================
-- «Solo borra»
-- ============================================================

/-- `h` está por debajo de `g`: mismos pasos, y vivos, posesiones, nodos y enlaces de `h` están en `g`.
Toda regla del review cumple `Sub (regla g) g` (plan L6, `Rule.defl`). -/
structure Sub (h g : GPathB) : Prop where
  step  : h.current_step = g.current_step
  alive : ∀ q ∈ h.alive, q ∈ g.alive
  adj   : ∀ x w, h.Adj x w → g.Adj x w
  nodes : ∀ n ∈ h.nodes, ∃ m ∈ g.nodes, m.id = n.id ∧
            (∀ p ∈ n.parents, p ∈ m.parents) ∧ (∀ s ∈ n.sons, s ∈ m.sons)

theorem Sub.refl (g : GPathB) : Sub g g :=
  ⟨rfl, fun _ h => h, fun _ _ h => h,
   fun n hn => ⟨n, hn, rfl, fun _ h => h, fun _ h => h⟩⟩

theorem Sub.trans {a b c : GPathB} (hab : Sub a b) (hbc : Sub b c) : Sub a c := by
  refine ⟨hab.step.trans hbc.step, fun q hq => hbc.alive q (hab.alive q hq),
    fun x w h => hbc.adj x w (hab.adj x w h), ?_⟩
  intro n hn
  obtain ⟨m, hm, hid, hp, hs⟩ := hab.nodes n hn
  obtain ⟨m', hm', hid', hp', hs'⟩ := hbc.nodes m hm
  exact ⟨m', hm', hid'.trans hid, fun p h => hp' p (hp p h), fun s h => hs' s (hs s h)⟩

/-- Posesión con menos aristas (y los mismos vivos, o menos). -/
theorem adj_mono {h g : GPathB} (ha : ∀ q ∈ h.alive, q ∈ g.alive)
    (he : ∀ e ∈ h.edges, e ∈ g.edges) (x w : PathNodeId) (hx : h.Adj x w) : g.Adj x w := by
  rw [adj_iff] at hx ⊢
  rcases hx with ⟨rfl, hal⟩ | ⟨e, he', hj⟩
  · exact Or.inl ⟨rfl, ha _ hal⟩
  · exact Or.inr ⟨e, he e he', hj⟩

theorem sub_removeEdge (g : GPathB) (x w : PathNodeId) : Sub (g.removeEdge x w) g :=
  ⟨rfl, fun _ h => h,
   adj_mono (fun _ h => h) (fun _ he => (List.mem_filter.mp he).1),
   fun n hn => ⟨n, hn, rfl, fun _ h => h, fun _ h => h⟩⟩

theorem sub_killVertex (g : GPathB) (id : PathNodeId) : Sub (g.killVertex id) g :=
  ⟨rfl, fun _ h => (List.mem_filter.mp h).1,
   adj_mono (fun _ h => (List.mem_filter.mp h).1) (fun _ he => (List.mem_filter.mp he).1),
   fun n hn => ⟨n, hn, rfl, fun _ h => h, fun _ h => h⟩⟩

theorem sub_removeNode (g : GPathB) (id : PathNodeId) : Sub (g.removeNode id) g := by
  have hk := sub_killVertex g id
  refine ⟨rfl, hk.alive, hk.adj, ?_⟩
  intro n hn
  simp only [removeNode, killVertex, List.mem_map, List.mem_filter] at hn
  obtain ⟨m, ⟨hm, _⟩, rfl⟩ := hn
  exact ⟨m, hm, rfl, fun p hp => (List.mem_filter.mp hp).1, fun s hs => (List.mem_filter.mp hs).1⟩

-- ============================================================
-- Lo que se va
-- ============================================================

/-- Tras quitarla, dos nodos distintos `x`, `w` ya no se poseen. -/
theorem not_adj_removeEdge (g : GPathB) (x w : PathNodeId) (hne : x ≠ w) :
    ¬ (g.removeEdge x w).Adj x w := by
  rw [adj_iff]
  rintro (⟨h, _⟩ | ⟨e, he, hj⟩)
  · exact hne h
  · have hk := (List.mem_filter.mp he).2
    simp only [joins, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq] at hk
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hk.1.elim (· h1) (· h2))
    · exact (hk.2.elim (· h1) (· h2))

/-- Tras `killVertex id`, `id` no posee a nadie (ni a sí mismo). -/
theorem not_adj_killVertex (g : GPathB) (id w : PathNodeId) : ¬ (g.killVertex id).Adj id w := by
  rw [adj_iff]
  rintro (⟨_, hal⟩ | ⟨e, he, hj⟩)
  · simp [killVertex] at hal
  · have hk := (List.mem_filter.mp he).2
    simp only [touches, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hk
    rcases hj with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hk.1 h1
    · exact hk.2 h2

theorem not_alive_killVertex (g : GPathB) (id : PathNodeId) : id ∉ (g.killVertex id).alive := by
  simp [killVertex]

-- ============================================================
-- La medida
-- ============================================================

theorem sum_map_filter_le {α : Type} (f : α → Nat) (p : α → Bool) :
    ∀ l : List α, ((l.filter p).map f).sum ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.filter_cons]
    split <;> simp only [List.map_cons, List.sum_cons] <;> omega

theorem sum_map_le_of_le {α : Type} (f g : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ g a) → (l.map f).sum ≤ (l.map g).sum := by
  intro l
  induction l with
  | nil => simp
  | cons a as ih =>
    intro h
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

theorem weight_unlinkAll (id : PathNodeId) (n : PNodeB) : (unlinkAll id n).weight ≤ n.weight := by
  simp only [unlinkAll, PNodeB.weight]
  have := List.length_filter_le (· != id) n.parents
  have := List.length_filter_le (· != id) n.sons
  omega

theorem measure_removeEdge_le (g : GPathB) (x w : PathNodeId) : (g.removeEdge x w).measure ≤ g.measure := by
  simp only [measure, removeEdge]
  have := List.length_filter_le (fun e => !joins x w e) g.edges
  omega

/-- Quitar una arista que está baja la medida. -/
theorem measure_removeEdge_lt (g : GPathB) (x w : PathNodeId) (h : g.hasEdge x w = true) :
    (g.removeEdge x w).measure < g.measure := by
  simp only [measure, removeEdge]
  have : (g.edges.filter (fun e => !joins x w e)).length < g.edges.length := by
    apply List.length_filter_lt_length_iff_exists.mpr
    obtain ⟨e, he, hj⟩ := List.any_eq_true.mp h
    exact ⟨e, he, by simp [hj]⟩
  omega

theorem measure_killVertex_le (g : GPathB) (id : PathNodeId) : (g.killVertex id).measure ≤ g.measure := by
  simp only [measure, killVertex]
  have := List.length_filter_le (· != id) g.alive
  have := List.length_filter_le (fun e => !touches id e) g.edges
  omega

theorem measure_removeNode_le (g : GPathB) (id : PathNodeId) : (g.removeNode id).measure ≤ g.measure := by
  have hk := measure_killVertex_le g id
  simp only [measure, removeNode, killVertex] at hk ⊢
  have h1 := sum_map_filter_le PNodeB.weight (fun n => n.id != id) g.nodes
  have h2 : (((g.nodes.filter (fun n => n.id != id)).map (unlinkAll id)).map PNodeB.weight).sum ≤
      ((g.nodes.filter (fun n => n.id != id)).map PNodeB.weight).sum := by
    rw [List.map_map]
    exact sum_map_le_of_le _ _ _ (fun n _ => weight_unlinkAll id n)
  omega

theorem sum_filter_id_lt (id : PathNodeId) :
    ∀ l : List PNodeB, (∃ n ∈ l, n.id = id) →
      ((l.filter (fun n => n.id != id)).map PNodeB.weight).sum < (l.map PNodeB.weight).sum := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a as ih =>
    intro h
    rw [List.filter_cons]
    by_cases ha : a.id = id
    · have hw : 1 ≤ a.weight := by simp only [PNodeB.weight]; omega
      have := sum_map_filter_le PNodeB.weight (fun n => n.id != id) as
      simp [ha]; omega
    · obtain ⟨n, hn, hid⟩ := h
      have hn' : n ∈ as := by
        rcases List.mem_cons.mp hn with rfl | hn'
        · exact absurd hid ha
        · exact hn'
      have := ih ⟨n, hn', hid⟩
      simp [ha]; omega

/-- Eliminar un nodo que está en la colección baja la medida (su peso es al menos 1). -/
theorem measure_removeNode_lt (g : GPathB) (id : PathNodeId) (h : ∃ n ∈ g.nodes, n.id = id) :
    (g.removeNode id).measure < g.measure := by
  have hk := measure_killVertex_le g id
  simp only [measure, removeNode, killVertex] at hk ⊢
  have h2 : (((g.nodes.filter (fun n => n.id != id)).map (unlinkAll id)).map PNodeB.weight).sum ≤
      ((g.nodes.filter (fun n => n.id != id)).map PNodeB.weight).sum := by
    rw [List.map_map]
    exact sum_map_le_of_le _ _ _ (fun n _ => weight_unlinkAll id n)
  have h3 := sum_filter_id_lt id g.nodes h
  omega

-- ============================================================
-- Ejemplos
-- ============================================================

private def pa : PathNodeId := { id := ⟨0, 0⟩, parent_id := none }
private def pb : PathNodeId := { id := ⟨1, 1⟩, parent_id := some ⟨0, 0⟩ }
private def ex : GPathB :=
  { nodes := [], alive := [pa, pb], edges := [(pa, pb)], current_step := 2, map_parent := none, dirty := false }

example : ex.adjb pb pa = true := by decide
example : ex.adjb pa pa = true := by decide
example : (ex.removeEdge pb pa).adjb pa pb = false := by decide
example : (ex.killVertex pa).adjb pb pb = true := by decide
example : ex.ownersOk pa = true := by decide
example : (ex.removeEdge pa pb).ownersOk pa = false := by decide

end GPathB

end AbsSatBingo.Model
