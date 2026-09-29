-- lean/improves_bingo/AbsSatBingo/Model/OneSideHist.lean
import AbsSatBingo.Model.StarSplit

/-!
# StarOneSide por la historia: el caso de las parejas ausentes

En el join `u = e ∪ g` de dos llegadas (`e` desde el remitente `A`, `g` desde `B`), una pareja `y–w` de la
estrella de una cima `t` de `e` que es de `g` y no de `e` o bien estaba en `A` (la **quitó** la llegada) o bien no
(**ausente**). Medido (`probe_oneside_history.jl`): ~99 % ausentes, y todas están en la estrella del grupo de padres
de `t` en `A` con un paso libre allí (`probe_cross_oneside.jl`: `CrossOneSide` por grupos, 0 fallos).

> **`CrossAt A B SQ`**: toda pareja de `B` que no es de `A`, entre nodos de `SQ`, tiene un paso en el que ningún
> nodo de `SQ` posee a los dos por aristas de `A ∪ B`.

**`starOneSide_absent`** (demostrado): con `CrossAt` en la estrella del grupo de padres de `t` (los padres que pasan
el filtro de la llegada), una pareja ausente tiene un paso libre en la estrella de `t` en la unión. La llegada solo
quita aristas entre nodos viejos, y la estrella de `t` está dentro de la del grupo (`t` hereda los vecinos de sus
padres).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

open Machine (Below)

variable {d : NodeId} {title : String} {forb : PathNodeId → Bool}

/-- **Un paso libre** de una pareja en un conjunto `SQ`, con aristas de `A ∪ B`. -/
def CrossAt (A B : GPathB) (SQ : PathNodeId → Prop) : Prop :=
  ∀ y w, SQ y → SQ w → B.Adj y w → ¬ A.Adj y w →
    ∃ l, 0 ≤ l ∧ l < A.current_step ∧
      ∀ r, SQ r → r.id.step = l → ¬ ((A.Adj y r ∨ B.Adj y r) ∧ (A.Adj w r ∨ B.Adj w r))

/-- La estrella del grupo de padres de `t` en el remitente `A` (padres que pasan el filtro `f`). -/
def GroupStar (A f : GPathB) (d : NodeId) (t z : PathNodeId) : Prop :=
  z ∈ A.alive ∧ ∃ q ∈ f.rowParents d t, A.Adj z q

/-- Entre nodos viejos, una posesión de la llegada lo es del remitente. -/
theorem adj_old_of_arrival {A f : GPathB} (hs : Sub f A) (hd : d.step = f.current_step) {y w : PathNodeId}
    (hy : y.id.step < f.current_step) (hw : w.id.step < f.current_step)
    (h : ((f.addNode d title forb).review).Adj y w) : A.Adj y w :=
  hs.adj _ _ (adj_addNode_old hd hy hw ((shrinks_review _).1.adj _ _ h))

/-- **Un vecino viejo de un nodo nuevo está en la estrella de sus padres.** -/
theorem groupStar_of_adj {A f : GPathB} (hs : Sub f A) (hdocs : AliveDocs f) (hb : Below f) (hea : EdgesAlive f)
    (hd : d.step = f.current_step) {t r : PathNodeId} (ht : t ∈ f.newRowIds d forb)
    (hr : r.id.step < f.current_step) (h : ((f.addNode d title forb).review).Adj t r) : GroupStar A f d t r := by
  have hts : t.id.step = f.current_step := newRow_step hd ht
  have h' := (shrinks_review _).1.adj _ _ h
  rw [adj_iff] at h'
  rcases h' with ⟨rfl, _⟩ | ⟨e, he, hj⟩
  · omega
  · rcases List.mem_append.mp he with h1 | h1
    · have hold : f.Adj t r := (adj_iff f t r).mpr (Or.inr ⟨e, h1, hj⟩)
      have := alive_below hdocs hb (hea t r hold).1
      omega
    · obtain ⟨pid, hpid, he'⟩ := List.mem_flatMap.mp h1
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp he'
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 : pid = t := h1
        have e2 : w' = r := h2
        subst e1; subst e2
        obtain ⟨halw, hany⟩ := List.mem_filter.mp hw'
        obtain ⟨_, hany⟩ := Bool.and_eq_true_iff.mp hany
        obtain ⟨q, hq, hqw⟩ := List.any_eq_true.mp hany
        exact ⟨hs.alive _ halw, q, hq, (adj_symm _ _ _).mp (hs.adj _ _ hqw)⟩
      · have e1 : pid = r := h1
        subst e1
        have := newRow_step hd hpid
        omega

/-- **El caso ausente de StarOneSide.** -/
theorem starOneSide_absent {A B fA fB : GPathB} {forbA forbB : PathNodeId → Bool}
    (hsA : Sub fA A) (hsB : Sub fB B) (hdA : d.step = fA.current_step) (hdB : d.step = fB.current_step)
    (hdocs : AliveDocs fA) (hb : Below fA) (hea : EdgesAlive fA)
    (heaG : EdgesAlive ((fB.addNode d "" forbB).review))
    {t : PathNodeId} (ht : t ∈ fA.newRowIds d forbA) (htg : t ∉ ((fB.addNode d "" forbB).review).alive)
    (hX : CrossAt A B (GroupStar A fA d t))
    {y w : PathNodeId}
    (hty : (join ((fA.addNode d "" forbA).review) ((fB.addNode d "" forbB).review)).Adj t y)
    (htw : (join ((fA.addNode d "" forbA).review) ((fB.addNode d "" forbB).review)).Adj t w)
    (hg : ((fB.addNode d "" forbB).review).Adj y w) (habs : ¬ A.Adj y w) :
    ∃ l, 0 ≤ l ∧ l < (join ((fA.addNode d "" forbA).review) ((fB.addNode d "" forbB).review)).current_step ∧
      ∀ r, r.id.step = l →
        (join ((fA.addNode d "" forbA).review) ((fB.addNode d "" forbB).review)).Adj t r →
        ¬ ((join ((fA.addNode d "" forbA).review) ((fB.addNode d "" forbB).review)).Adj y r ∧
          (join ((fA.addNode d "" forbA).review) ((fB.addNode d "" forbB).review)).Adj w r) := by
  generalize heE : (fA.addNode d "" forbA).review = e at *
  generalize heGd : (fB.addNode d "" forbB).review = g at *
  have hcsu : (join e g).current_step = fA.current_step + 1 := by
    rw [← heE]; exact (shrinks_review _).1.step
  have hcsB : fA.current_step = fB.current_step := hdA.symm.trans hdB
  have hts : t.id.step = fA.current_step := newRow_step hdA ht
  -- las posesiones de t en la unión son de e
  have hte : ∀ {r}, (join e g).Adj t r → e.Adj t r := by
    intro r h
    rcases adj_join_cases h with h | h
    · exact h
    · exact absurd (heaG t r h).1 htg
  -- un vecino de t distinto de t es viejo
  have hold : ∀ {r}, e.Adj t r → r ≠ t → r.id.step < fA.current_step := by
    intro r h hne
    have h' := (shrinks_review _).1.adj _ _ (heE ▸ h)
    have hr := (edgesAlive_addNode hea r t ((adj_symm _ _ _).mp h')).1
    rcases alive_addNode_cases (title := "") hdocs hb hdA hr with ⟨_, h1⟩ | ⟨_, h1⟩
    · exact h1
    · exact absurd (adj_addNode_new hdocs hb hea hts h1 h').symm hne
  have hyt : y ≠ t := fun h => by subst h; exact htg (heaG _ _ hg).1
  have hwt : w ≠ t := fun h => by subst h; exact htg (heaG _ _ hg).2
  have hyo := hold (hte hty) hyt
  have hwo := hold (hte htw) hwt
  have hstar : ∀ {r}, (join e g).Adj t r → r.id.step < fA.current_step → GroupStar A fA d t r :=
    fun {r} h hr => groupStar_of_adj hsA hdocs hb hea hdA ht hr (by rw [heE]; exact hte h)
  -- una posesión de la unión entre nodos viejos es de A o de B
  have hAB : ∀ {a b}, (join e g).Adj a b → a.id.step < fA.current_step → b.id.step < fA.current_step →
      A.Adj a b ∨ B.Adj a b := by
    intro a b h ha hb'
    rcases adj_join_cases h with h | h
    · exact Or.inl (adj_old_of_arrival hsA hdA ha hb' (by rw [heE]; exact h))
    · exact Or.inr (adj_old_of_arrival hsB hdB (hcsB ▸ ha) (hcsB ▸ hb') (by rw [heGd]; exact h))
  have hB : B.Adj y w := adj_old_of_arrival hsB hdB (hcsB ▸ hyo) (hcsB ▸ hwo) (by rw [heGd]; exact hg)
  have hAcs : fA.current_step = A.current_step := hsA.step
  obtain ⟨l, h0, h1, hl⟩ := hX y w (hstar hty hyo) (hstar htw hwo) hB habs
  refine ⟨l, h0, by rw [hcsu]; omega, fun r hrl hrt ⟨hyr, hwr⟩ => ?_⟩
  have hrne : r ≠ t := fun h => by subst h; omega
  have hro := hold (hte hrt) hrne
  exact hl r (hstar hrt hro) hrl ⟨hAB hyr hyo hro, hAB hwr hwo hro⟩

end GPathB

end AbsSatBingo.Model
