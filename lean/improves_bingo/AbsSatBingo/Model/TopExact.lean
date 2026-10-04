-- lean/improves_bingo/AbsSatBingo/Model/TopExact.lean
import AbsSatBingo.Model.SplitWitness
import AbsSatBingo.Model.SideAbsorb

/-!
# `TopExact`: la exactitud solo para las cimas

`KernelExact` pide que **cada pareja** del núcleo fijado esté en una camarilla. El lector necesita mucho menos: que un
estado fijado válido lleve alguna camarilla. Basta con las **cimas**:

* **`TopExact g`**: una cima (nodo del paso `c - 1`) del núcleo de `g` fijado en `P` está en una camarilla que
  concuerda con `P`.

Lo conservan:
* la selección (`topExact_filterAll`), como `KernelExact`;
* **el UP, sin ninguna hipótesis y aunque salte una ventana** (`topExact_addNode`): una cima nueva del núcleo tiene
  su padre dentro, y ese padre es una cima vieja del núcleo con hijo permitido (el que es la cima nueva);
* el join, bajo **`TopUnion`** (`topExact_join`): una cima del núcleo de la unión está en el núcleo de algún lado.
  Es una afirmación por nodo, no por pareja: más débil que `KernelUnion`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Machine (Below mapId_of_mem_shiftRowIds)

/-- **`TopExact`**: toda cima del núcleo fijado en `P` está en una camarilla que concuerda con `P`. -/
def TopExact (g : GPathB) : Prop :=
  ∀ (P : List NodeId) (t : PathNodeId), t.id.step = g.current_step - 1 → Kernel g P t t →
    ∃ S, Carried g S ∧ (∀ r ∈ P, Agrees g.current_step S r) ∧ OnS g.current_step S t

/-- **`TopUnion`**: una cima del núcleo de la unión fijado en `P` está en el núcleo de algún lado. -/
def TopUnion (e g : GPathB) : Prop :=
  ∀ (P : List NodeId) (t : PathNodeId), t.id.step = e.current_step - 1 → Kernel (join e g) P t t →
    Kernel e P t t ∨ Kernel g P t t

theorem topExact_of_kernelExact {g : GPathB} (hk : KernelExact g) : TopExact g := by
  intro P t _ h
  obtain ⟨S, hc, ha, ht, _⟩ := hk P t t h
  exact ⟨S, hc, ha, ht⟩

/-- **La selección conserva `TopExact`.** -/
theorem topExact_filterAll {g : GPathB} (hk : TopExact g) (hd : AliveDocs g) (hnd : NodupIds g)
    (B : List NodeId) : TopExact (g.filterAll B) := by
  intro P t hts hker
  have hcs : (g.filterAll B).current_step = g.current_step := (shrinks_filterAll g B).1.step
  obtain ⟨S, hc, ha, ht⟩ := hk (B ++ P) t (by rw [← hcs]; exact hts) ((kernel_pin_list_iff hd hnd t t).mp hker)
  refine ⟨S, carried_filterAll hc B (fun r hr => ha r (List.mem_append_left _ hr)), ?_, ?_⟩
  · intro r hr; rw [hcs]; exact ha r (List.mem_append_right _ hr)
  · rw [hcs]; exact ht

variable {g : GPathB} {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **El UP conserva `TopExact`, sin hipótesis y con o sin ventana saltada.** -/
theorem topExact_addNode (hk : TopExact g) (hdocs : AliveDocs g) (hb : Below g) (hls : LinksStep g)
    (hpos : 0 < g.current_step) (hd : d.step = g.current_step) : TopExact (g.addNode d title forb) := by
  intro P y hys ⟨V, R, hst, ha, hr⟩
  have hcs : (g.addNode d title forb).current_step = g.current_step + 1 := rfl
  rw [hcs] at hys
  have hys : y.id.step = g.current_step := by omega
  have hdown := secStruct_addNode_down (title := title) (forb := forb) hdocs hb hls hd hst
  -- y es de la fila nueva
  have hyn : y ∈ g.newRowIds d forb := by
    rcases alive_addNode_cases (title := title) hdocs hb hd (hst.alive (hst.dom hr).1) with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact h
  -- lo que P fija en el paso nuevo es d
  have hP : ∀ r ∈ P, r.step = g.current_step → r = d := by
    intro r hr' hrs
    rw [← mapId_of_mem_shiftRowIds (List.mem_filter.mp hyn).1]
    exact (ha r hr' (hst.dom hr).1 (by rw [hys, hrs])).symm
  -- su padre en V
  obtain ⟨m, hm, hpar, _⟩ := hst.node (hst.dom hr).1
  rw [node?_addNode_new (title := title) hb hd hyn] at hm
  cases hm
  obtain ⟨q, _, hq⟩ := parent_of_row hpos hyn
  have hroot : y.parent_id.isNone = false := by rw [hq]; rfl
  obtain ⟨p, hp, hyp⟩ := hpar hroot
  obtain ⟨_, _, _, hps⟩ := step_of_newParents (rowParents_sub hp)
  -- el padre es una cima del núcleo del estado anterior
  have hpk : Kernel g P p p :=
    ⟨_, _, hdown, fun r hr' q hq hqs => ha r hr' hq.1 hqs, hst.refl (hst.dom hyp).2, by omega, by omega⟩
  obtain ⟨S, hc, hag, hpS⟩ := hk P p hps hpk
  have htop' := top_of_onS hc hpS hps
  obtain ⟨hc', hag', _, hn'⟩ := extend_through (title := title) hc hpos hb hd hag hP hyn (by rw [htop']; exact hp)
  exact ⟨_, hc', hag', hn'⟩

/-- **El join conserva `TopExact` bajo `TopUnion`.** -/
theorem topExact_doJoin {e g : GPathB} (he : TopExact e) (hg : TopExact g) (hu : TopUnion e g) :
    TopExact (doJoin e g) := by
  unfold doJoin
  split
  · rename_i hok
    have hcs : e.current_step = g.current_step := by
      unfold okJoin at hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      exact hok.1.1.1
    have hjs : (join e g).current_step = e.current_step := rfl
    intro P t hts hk
    rw [hjs] at hts
    rcases hu P t hts hk with h | h
    · obtain ⟨S, hc, ha, ht⟩ := he P t hts h
      exact ⟨S, carried_join_left hc, by rw [hjs]; exact ha, by rw [hjs]; exact ht⟩
    · obtain ⟨S, hc, ha, ht⟩ := hg P t (hcs ▸ hts) h
      refine ⟨S, carried_join_right hcs hc, ?_, ?_⟩
      · rw [hjs, hcs]; exact ha
      · rw [hjs, hcs]; exact ht
  · exact he

/-- Cambiar `dirty` no cambia `TopExact`. -/
theorem topExact_dirty {g : GPathB} (hk : TopExact g) (b : Bool) : TopExact { g with dirty := b } := by
  intro P t hts ⟨V, R, hst, ha, hr⟩
  have hst' : SecStruct g V R := ⟨hst.alive, hst.refl, hst.symm, hst.dom, hst.adj, hst.pair, hst.node, hst.par, hst.son⟩
  obtain ⟨S, hc, hag, ht⟩ := hk P t hts ⟨V, R, hst', ha, hr⟩
  exact ⟨S, carried_dirty hc b, hag, ht⟩

/-- **`TopExact` y el cierre dan `NoZombie`**: un estado válido cerrado tiene una cima viva, que está en su núcleo. -/
theorem noZombie_of_topExact {h : GPathB} (hk : TopExact h) (hcl : ClosedState h) (hpos : 0 < h.current_step) :
    NoZombie h := by
  intro hv
  have hm : h.current_step - 1 ∈ intRange 0 (h.current_step - 1) := mem_intRange (by omega) (Int.le_refl _)
  have := (List.all_eq_true.mp hv) _ hm
  obtain ⟨t, ht, hts⟩ := List.any_eq_true.mp this
  have hts : t.id.step = h.current_step - 1 := by simpa using hts
  obtain ⟨S, hc, _, _⟩ := hk [] t hts ⟨_, _, hcl, fun _ hb => absurd hb List.not_mem_nil, ht, ht, adj_refl _ _ ht⟩
  exact ⟨S, hc⟩

-- ============================================================
-- `TopUnion` por el origen de la cima
-- ============================================================

/-- **`TopSplit`**: `SplitAt` solo para las cimas: una cima del núcleo de `u` fijado en `P` sobrevive fijando además
un nodo del mapa del paso `k`. Medido (`test_3sat/probe_topsplit.jl`): sin fallos, fijando el origen de la cima. -/
def TopSplit (u : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) (t : PathNodeId), t.id.step = u.current_step - 1 → Kernel u P t t →
    ∃ b : NodeId, b.step = k ∧ Kernel u (P ++ [b]) t t

/-- **`TopUnion` ⇐ `TopSplit` + `SidePinned`** en el paso de origen. -/
theorem topUnion_of_topSplit {e g : GPathB} {k : Int} (hs : TopSplit (join e g) k)
    (hp : SidePinned (join e g) e g k) : TopUnion e g := by
  intro P t hts hk
  obtain ⟨b, hbk, hkb⟩ := hs P t hts hk
  rcases hp b hbk with he | hg
  · exact Or.inl (kernel_of_append (he P t t hkb))
  · exact Or.inr (kernel_of_append (hg P t t hkb))

/-- **`TopUnion` ⇐ `TopSplit` + `Absorb` en los dos lados** (con la separación y los enlaces completos): la forma
con las piezas ya reducidas. -/
theorem topUnion_of_absorb {e g : GPathB} {k : Int} (hk0 : 0 ≤ k) (hkc : k < e.current_step)
    (hcs : e.current_step = g.current_step) (hle : LinksInv e) (hlg : LinksInv g) (hee : EdgesAlive e)
    (heg : EdgesAlive g) (hsep : SepAt e g k) (hts : TopSplit (join e g) k) (hae : Absorb (join e g) e)
    (hag : Absorb (join e g) g) : TopUnion e g :=
  topUnion_of_topSplit hts (sidePinned_of_sideEdges hk0 hkc hcs hle hlg hee heg hsep
    (sideEdgesAt_of_absorb hk0 hkc hcs hle hlg hee heg hae hag))

-- ============================================================
-- `TopSplit` por la estrella de la cima
-- ============================================================

/-- **`TopNbr`**: en el paso de origen, una cima solo posee a sus padres (a nodos cuyo id es su `parent_id`). -/
def TopNbr (g : GPathB) : Prop :=
  ∀ t y, t.id.step = g.current_step - 1 → y.id.step = g.current_step - 2 → g.Adj t y → t.parent_id = some y.id

/-- **`TopStarK`**: una cima del núcleo fijado en `P` está en una estructura cerrada que concuerda con `P` y vive en
su estrella (todos sus nodos los posee la cima). Medido como `TopStar` (`test_3sat/probe_topstar.jl`: el review de la
estrella de la cima la conserva): sin fallos. -/
def TopStarK (u : GPathB) : Prop :=
  ∀ (P : List NodeId) (t : PathNodeId), t.id.step = u.current_step - 1 → Kernel u P t t →
    ∃ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct u V R ∧ (∀ b ∈ P, SecAgrees V b) ∧
      V t ∧ ∀ y, V y → u.Adj t y

/-- **`TopSplit` ⇐ `TopStarK` + `TopNbr`**: la estructura de la estrella concuerda con el origen de la cima (sus
nodos del paso de origen los posee la cima, luego son sus padres y tienen su id). Sin Helly: todo pasa por la cima. -/
theorem topSplit_of_topStar {u : GPathB} (hs : TopStarK u) (hn : TopNbr u) (hc : 2 ≤ u.current_step) :
    TopSplit u (u.current_step - 2) := by
  intro P t hts hk
  obtain ⟨V, R, hst, ha, hvt, hstar⟩ := hs P t hts hk
  obtain ⟨r, hrs, htr, _⟩ := hst.pair (hst.refl hvt) (u.current_step - 2) (by omega) (by omega)
  have hpr : t.parent_id = some r.id := hn t r hts hrs (hstar r (hst.dom htr).2)
  refine ⟨r.id, hrs, V, R, hst, ?_, hst.refl hvt⟩
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact ha b hb
  · rw [List.mem_singleton] at hb
    subst hb
    intro y hy hys
    have := hn t y hts (hys.trans hrs) (hstar y hy)
    rw [hpr] at this
    exact (Option.some.inj this).symm

end GPathB

end AbsSatBingo.Model
