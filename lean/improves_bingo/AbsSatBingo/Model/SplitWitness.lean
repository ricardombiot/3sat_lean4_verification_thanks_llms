-- lean/improves_bingo/AbsSatBingo/Model/SplitWitness.lean
import AbsSatBingo.Model.UnionEquiv

/-!
# `SplitAt` por testigos, y la unión de estructuras cerradas

* **`secStruct_iUnion`**: la unión de una familia de estructuras cerradas es cerrada. Así, las parejas que sobreviven
  a algún pin del origen forman una estructura cerrada (`SplitKernel`), y `SplitAt` dice que es todo el núcleo.
* **`WitSplit`**: `SplitAt` eligiendo el origen entre los testigos de la pareja (un nodo del paso de origen que el
  núcleo empareja con los dos). Medido (`test_3sat/probe_splitat.jl`): `SplitAt` sin fallos; **algún** testigo
  común siempre sirve, pero **no cualquiera** (unas pocas parejas por mil fallan con algún testigo).
* `splitAt_of_witSplit`, y `witSplit_of_kernelUnion`: con los lados exactos, `KernelUnion` da `WitSplit` (el testigo
  es el nodo del origen de la camarilla del lado). `WitSplit` es la forma de `SplitAt` que habría que demostrar.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- **La unión de estructuras cerradas es cerrada.** -/
theorem secStruct_iUnion {g : GPathB} {ι : Type} {V : ι → PathNodeId → Prop}
    {R : ι → PathNodeId → PathNodeId → Prop} (h : ∀ i, SecStruct g (V i) (R i)) :
    SecStruct g (fun y => ∃ i, V i y) (fun y w => ∃ i, R i y w) := by
  refine ⟨fun ⟨i, hy⟩ => (h i).alive hy, fun ⟨i, hy⟩ => ⟨i, (h i).refl hy⟩, fun ⟨i, hr⟩ => ⟨i, (h i).symm hr⟩,
    fun ⟨i, hr⟩ => ⟨⟨i, ((h i).dom hr).1⟩, ⟨i, ((h i).dom hr).2⟩⟩, fun ⟨i, hr⟩ => (h i).adj hr, ?_, ?_, ?_, ?_⟩
  · intro y w ⟨i, hr⟩ l h0 h1
    obtain ⟨r, hrs, h1, h2⟩ := (h i).pair hr l h0 h1
    exact ⟨r, hrs, ⟨i, h1⟩, ⟨i, h2⟩⟩
  · intro y ⟨i, hy⟩
    obtain ⟨n, hn, hp, hs⟩ := (h i).node hy
    refine ⟨n, hn, fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨p, hp', hr⟩ := hp hk; exact ⟨p, hp', ⟨i, hr⟩⟩
    · obtain ⟨s, hs', hr⟩ := hs hk; exact ⟨s, hs', ⟨i, hr⟩⟩
  · intro x w n ⟨i, hr⟩ hne hn h1
    obtain ⟨p, hp, h1, h2⟩ := (h i).par hr hne hn h1
    exact ⟨p, hp, ⟨i, h1⟩, ⟨i, h2⟩⟩
  · intro x w n ⟨i, hr⟩ hne hn h1
    obtain ⟨s, hs, h1, h2⟩ := (h i).son hr hne hn h1
    exact ⟨s, hs, ⟨i, h1⟩, ⟨i, h2⟩⟩

/-- Las parejas que sobreviven a algún pin del paso `k` (tras `P`). -/
def SplitKernel (u : GPathB) (P : List NodeId) (k : Int) (y w : PathNodeId) : Prop :=
  ∃ b : NodeId, b.step = k ∧ Kernel u (P ++ [b]) y w

/-- **`SplitKernel` es una estructura cerrada** (la unión de las de cada pin), que concuerda con `P`. -/
theorem splitKernel_closed (u : GPathB) (P : List NodeId) (k : Int) :
    ∃ V, SecStruct u V (SplitKernel u P k) ∧ ∀ b ∈ P, SecAgrees V b := by
  -- la familia: una estructura por cada (b, estructura cerrada que concuerda con P ++ [b])
  let ι := { x : NodeId × (PathNodeId → Prop) × (PathNodeId → PathNodeId → Prop) //
    x.1.step = k ∧ SecStruct u x.2.1 x.2.2 ∧ ∀ b ∈ P ++ [x.1], SecAgrees x.2.1 b }
  have hU := secStruct_iUnion (g := u) (V := fun i : ι => i.1.2.1) (R := fun i : ι => i.1.2.2) (fun i => i.2.2.1)
  refine ⟨fun y => ∃ i : ι, i.1.2.1 y, ?_, ?_⟩
  · have heq : SplitKernel u P k = fun y w => ∃ i : ι, i.1.2.2 y w := by
      funext y w
      apply propext
      constructor
      · rintro ⟨b, hb, V, R, hst, ha, hr⟩
        exact ⟨⟨(b, V, R), hb, hst, ha⟩, hr⟩
      · rintro ⟨⟨⟨b, V, R⟩, hb, hst, ha⟩, hr⟩
        exact ⟨b, hb, V, R, hst, ha, hr⟩
    rw [heq]; exact hU
  · intro b hb y ⟨i, hy⟩ hs
    exact i.2.2.2 b (List.mem_append_left _ hb) hy hs

/-- **`SplitAt` por testigos**: la pareja se conserva fijando el origen de alguno de sus testigos en el núcleo. -/
def WitSplit (u : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) y w, Kernel u P y w →
    ∃ r : PathNodeId, r.id.step = k ∧ Kernel u P y r ∧ Kernel u P w r ∧ Kernel u (P ++ [r.id]) y w

theorem splitAt_of_witSplit {u : GPathB} {k : Int} (h : WitSplit u k) : SplitAt u k := by
  intro P y w hk
  obtain ⟨r, hr, _, _, h'⟩ := h P y w hk
  exact ⟨r.id, hr, h'⟩

/-- El núcleo de un lado exacto da testigo: el nodo de la camarilla en el paso `k`. -/
theorem wit_of_exact {g : GPathB} (hk : KernelExact g) {P : List NodeId} {y w : PathNodeId}
    (hker : Kernel g P y w) {k : Int} (hk0 : 0 ≤ k) (hk1 : k < g.current_step) :
    ∃ r : PathNodeId, r.id.step = k ∧ Kernel g P y r ∧ Kernel g P w r ∧ Kernel g (P ++ [r.id]) y w := by
  obtain ⟨S, hc, ha, hy, hw⟩ := hk P y w hker
  have hr : OnS g.current_step S (S k) := ⟨k, hk0, hk1, rfl⟩
  refine ⟨S k, hc.step k hk0 hk1, kernel_of_clique hc ha hy hr, kernel_of_clique hc ha hw hr, ?_⟩
  refine kernel_of_clique hc ?_ hy hw
  intro r' hr'
  rcases List.mem_append.mp hr' with hr' | hr'
  · exact ha r' hr'
  · rw [List.mem_singleton] at hr'
    subst hr'
    intro _ _
    rw [hc.step k hk0 hk1]

/-- **Con los lados exactos, `KernelUnion` da `WitSplit`.** -/
theorem witSplit_of_kernelUnion {e g : GPathB} {k : Int} (hk0 : 0 ≤ k) (hkc : k < e.current_step)
    (hcs : e.current_step = g.current_step) (hke : KernelExact e) (hkg : KernelExact g) (hu : KernelUnion e g) :
    WitSplit (join e g) k := by
  intro P y w h
  rcases hu P y w h with h | h
  · obtain ⟨r, hr, h1, h2, h3⟩ := wit_of_exact hke h hk0 hkc
    exact ⟨r, hr, kernel_join_left h1, kernel_join_left h2, kernel_join_left h3⟩
  · obtain ⟨r, hr, h1, h2, h3⟩ := wit_of_exact hkg h hk0 (hcs ▸ hkc)
    exact ⟨r, hr, kernel_join_right hcs h1, kernel_join_right hcs h2, kernel_join_right hcs h3⟩

-- ============================================================
-- `WitSplit` por lados: testigo del propio lado, y que ese testigo sirva
-- ============================================================

/-- **`OwnWitness`**: una pareja del núcleo de la unión que es arista de un lado tiene, en el núcleo, un testigo en
el paso `k` vivo en ese lado. -/
def OwnWitness (e g : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) y w, Kernel (join e g) P y w →
    (e.Adj y w → ∃ r : PathNodeId, r.id.step = k ∧ r ∈ e.alive ∧ Kernel (join e g) P y r ∧ Kernel (join e g) P w r) ∧
    (g.Adj y w → ∃ r : PathNodeId, r.id.step = k ∧ r ∈ g.alive ∧ Kernel (join e g) P y r ∧ Kernel (join e g) P w r)

/-- **`OwnSideGood`**: fijar la unión en un testigo del mismo lado que la arista conserva la pareja. Medido
(`test_3sat/probe_badwit.jl`): todos los testigos malos son del otro lado. -/
def OwnSideGood (e g : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) y w (r : PathNodeId), Kernel (join e g) P y w → r.id.step = k →
    Kernel (join e g) P y r → Kernel (join e g) P w r →
    ((e.Adj y w ∧ r ∈ e.alive) ∨ (g.Adj y w ∧ r ∈ g.alive)) → Kernel (join e g) (P ++ [r.id]) y w

/-- **`WitSplit` ⇐ `OwnWitness` + `OwnSideGood`.** -/
theorem witSplit_of_own {e g : GPathB} {k : Int} (hw : OwnWitness e g k) (hg : OwnSideGood e g k) :
    WitSplit (join e g) k := by
  intro P y w h
  have hadj : (join e g).Adj y w := by
    obtain ⟨V, R, hst, _, hr⟩ := h
    exact hst.adj hr
  rcases adj_join_cases hadj with ha | ha
  · obtain ⟨r, hr, hre, h1, h2⟩ := (hw P y w h).1 ha
    exact ⟨r, hr, h1, h2, hg P y w r h hr h1 h2 (Or.inl ⟨ha, hre⟩)⟩
  · obtain ⟨r, hr, hrg, h1, h2⟩ := (hw P y w h).2 ha
    exact ⟨r, hr, h1, h2, hg P y w r h hr h1 h2 (Or.inr ⟨ha, hrg⟩)⟩

-- ============================================================
-- `OwnSideGood` por el triángulo dentro del lado
-- ============================================================

/-- **`WitAll g k`**: dentro de un estado, cualquier testigo del núcleo sirve: si `r` (paso `k`) empareja en el
núcleo fijado en `P` con `y` y con `w`, la pareja sobrevive fijando además `r.id`. Medido dentro de los lados de los
joins (`test_3sat/probe_triangle.jl`): 0 fallos. -/
def WitAll (g : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) y w (r : PathNodeId), r.id.step = k → Kernel g P y w → Kernel g P y r → Kernel g P w r →
    Kernel g (P ++ [r.id]) y w

/-- **`TriIn`**: un triángulo del núcleo de la unión con las tres aristas de un lado (y el testigo vivo en él) es un
triángulo del núcleo de ese lado. Medido (`probe_triangle.jl`, `tri_out`): 0 fallos. -/
def TriIn (e g : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) y w (r : PathNodeId), r.id.step = k → Kernel (join e g) P y w → Kernel (join e g) P y r →
    Kernel (join e g) P w r →
    (e.Adj y w → r ∈ e.alive → Kernel e P y w ∧ Kernel e P y r ∧ Kernel e P w r) ∧
    (g.Adj y w → r ∈ g.alive → Kernel g P y w ∧ Kernel g P y r ∧ Kernel g P w r)

/-- **`OwnSideGood` ⇐ `TriIn` + `WitAll` en los dos lados** (la monotonía lleva el núcleo del lado a la unión). -/
theorem ownSideGood_of_tri {e g : GPathB} {k : Int} (hcs : e.current_step = g.current_step) (ht : TriIn e g k)
    (hwe : WitAll e k) (hwg : WitAll g k) : OwnSideGood e g k := by
  intro P y w r h hr h1 h2 hside
  rcases hside with ⟨ha, hre⟩ | ⟨ha, hrg⟩
  · obtain ⟨k1, k2, k3⟩ := (ht P y w r hr h h1 h2).1 ha hre
    exact kernel_join_left (hwe P y w r hr k1 k2 k3)
  · obtain ⟨k1, k2, k3⟩ := (ht P y w r hr h h1 h2).2 ha hrg
    exact kernel_join_right hcs (hwg P y w r hr k1 k2 k3)

-- ============================================================
-- Lados de un solo origen
-- ============================================================

/-- Todos los vivos de `g` en el paso `k` son del nodo del mapa `b` (un lado que sale de un UP: su paso de origen es
la cima del estado de un solo nodo del mapa). -/
def SingleAt (g : GPathB) (k : Int) (b : NodeId) : Prop := ∀ q ∈ g.alive, q.id.step = k → q.id = b

/-- Con un solo nodo del mapa en `k`, fijarlo no cambia el núcleo. -/
theorem kernel_pin_single {g : GPathB} {k : Int} {b : NodeId} (hs : SingleAt g k b) (hb : b.step = k)
    {P : List NodeId} {y w : PathNodeId} (h : Kernel g P y w) : Kernel g (P ++ [b]) y w := by
  obtain ⟨V, R, hst, ha, hr⟩ := h
  refine ⟨V, R, hst, fun b' hb' => ?_, hr⟩
  rcases List.mem_append.mp hb' with hb' | hb'
  · exact ha b' hb'
  · rw [List.mem_singleton] at hb'
    subst hb'
    intro q hq hqs
    exact hs q (hst.alive hq) (hqs.trans hb)

/-- **Con un solo nodo del mapa en `k`, `WitAll` en `k` es automático.** -/
theorem witAll_of_single {g : GPathB} {k : Int} {b : NodeId} (hs : SingleAt g k b) : WitAll g k := by
  intro P y w r hr h h1 _
  obtain ⟨V, R, hst, _, hyr⟩ := h1
  have hrb : r.id = b := hs r (hst.alive (hst.dom hyr).2) hr
  rw [hrb]
  exact kernel_pin_single hs (hrb ▸ hr) h

/-- **`PairIn`**: una pareja del núcleo de la unión que es arista de un lado y tiene un testigo de ese lado está en
el núcleo de ese lado (la primera pieza de `TriIn`; medida en `probe_triangle.jl`). -/
def PairIn (e g : GPathB) (k : Int) : Prop :=
  ∀ (P : List NodeId) y w (r : PathNodeId), r.id.step = k → Kernel (join e g) P y w → Kernel (join e g) P y r →
    Kernel (join e g) P w r →
    (e.Adj y w → r ∈ e.alive → Kernel e P y w) ∧ (g.Adj y w → r ∈ g.alive → Kernel g P y w)

/-- **Con lados de un solo origen, `OwnSideGood` ⇐ `PairIn`.** -/
theorem ownSideGood_of_single {e g : GPathB} {k : Int} {a b : NodeId} (hcs : e.current_step = g.current_step)
    (hse : SingleAt e k a) (hsg : SingleAt g k b) (hp : PairIn e g k) : OwnSideGood e g k := by
  intro P y w r h hr h1 h2 hside
  rcases hside with ⟨ha, hre⟩ | ⟨ha, hrg⟩
  · have hra : r.id = a := hse r hre hr
    rw [hra]
    exact kernel_join_left (kernel_pin_single hse (hra ▸ hr) ((hp P y w r hr h h1 h2).1 ha hre))
  · have hrb : r.id = b := hsg r hrg hr
    rw [hrb]
    exact kernel_join_right hcs (kernel_pin_single hsg (hrb ▸ hr) ((hp P y w r hr h h1 h2).2 ha hrg))

end GPathB

end AbsSatBingo.Model
