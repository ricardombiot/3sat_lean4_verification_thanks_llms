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

/-- **El caso ausente de StarOneSide**, para una unión `u` cuyas posesiones vienen de la llegada `e` (desde `A`) o
de la llegada `g` (desde `B`). -/
theorem starOneSide_absent {A B fA fB u : GPathB} {forbA forbB : PathNodeId → Bool}
    (hsA : Sub fA A) (hsB : Sub fB B) (hdA : d.step = fA.current_step) (hdB : d.step = fB.current_step)
    (hdocs : AliveDocs fA) (hb : Below fA) (hea : EdgesAlive fA)
    (heaG : EdgesAlive ((fB.addNode d "" forbB).review))
    (hu : ∀ {a b}, u.Adj a b → ((fA.addNode d "" forbA).review).Adj a b ∨ ((fB.addNode d "" forbB).review).Adj a b)
    (hcsu : u.current_step = fA.current_step + 1)
    {t : PathNodeId} (ht : t ∈ fA.newRowIds d forbA) (htg : t ∉ ((fB.addNode d "" forbB).review).alive)
    (hX : CrossAt A B (GroupStar A fA d t))
    {y w : PathNodeId} (hty : u.Adj t y) (htw : u.Adj t w)
    (hg : ((fB.addNode d "" forbB).review).Adj y w) (habs : ¬ A.Adj y w) :
    ∃ l, 0 ≤ l ∧ l < u.current_step ∧ ∀ r, r.id.step = l → u.Adj t r → ¬ (u.Adj y r ∧ u.Adj w r) := by
  generalize heE : (fA.addNode d "" forbA).review = e at *
  generalize heGd : (fB.addNode d "" forbB).review = g at *
  have hcsB : fA.current_step = fB.current_step := hdA.symm.trans hdB
  have hts : t.id.step = fA.current_step := newRow_step hdA ht
  -- las posesiones de t en la unión son de e
  have hte : ∀ {r}, u.Adj t r → e.Adj t r := by
    intro r h
    rcases hu h with h | h
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
  have hstar : ∀ {r}, u.Adj t r → r.id.step < fA.current_step → GroupStar A fA d t r :=
    fun {r} h hr => groupStar_of_adj hsA hdocs hb hea hdA ht hr (by rw [heE]; exact hte h)
  -- una posesión de la unión entre nodos viejos es de A o de B
  have hAB : ∀ {a b}, u.Adj a b → a.id.step < fA.current_step → b.id.step < fA.current_step →
      A.Adj a b ∨ B.Adj a b := by
    intro a b h ha hb'
    rcases hu h with h | h
    · exact Or.inl (adj_old_of_arrival hsA hdA ha hb' (by rw [heE]; exact h))
    · exact Or.inr (adj_old_of_arrival hsB hdB (hcsB ▸ ha) (hcsB ▸ hb') (by rw [heGd]; exact h))
  have hB : B.Adj y w := adj_old_of_arrival hsB hdB (hcsB ▸ hyo) (hcsB ▸ hwo) (by rw [heGd]; exact hg)
  have hAcs : fA.current_step = A.current_step := hsA.step
  obtain ⟨l, h0, h1, hl⟩ := hX y w (hstar hty hyo) (hstar htw hwo) hB habs
  refine ⟨l, h0, by rw [hcsu]; omega, fun r hrl hrt ⟨hyr, hwr⟩ => ?_⟩
  have hrne : r ≠ t := fun h => by subst h; omega
  have hro := hold (hte hrt) hrne
  exact hl r (hstar hrt hro) hrl ⟨hAB hyr hyo hro, hAB hwr hwo hro⟩

/-- **El caso repartido, demostrado**: si ningún padre de `t` posee (en `A`) a la vez a `y` y a `w`, el paso de los
padres está libre en la estrella de `t`: allí la estrella solo tiene padres de `t`, que no viven en la otra llegada. -/
theorem starOneSide_split {A fA fB u : GPathB} {forbA forbB : PathNodeId → Bool}
    (hsA : Sub fA A) (hdA : d.step = fA.current_step) (hpos : 0 < fA.current_step)
    (hdocs : AliveDocs fA) (hb : Below fA) (hea : EdgesAlive fA) (hta : TopsApart fA)
    (heaG : EdgesAlive ((fB.addNode d "" forbB).review))
    (hu : ∀ {a b}, u.Adj a b → ((fA.addNode d "" forbA).review).Adj a b ∨ ((fB.addNode d "" forbB).review).Adj a b)
    (hcsu : u.current_step = fA.current_step + 1)
    {t : PathNodeId} (ht : t ∈ fA.newRowIds d forbA) (htg : t ∉ ((fB.addNode d "" forbB).review).alive)
    (hrg : ∀ r, r ∈ fA.rowParents d t → r ∉ ((fB.addNode d "" forbB).review).alive)
    {y w : PathNodeId} (hyo : y.id.step < fA.current_step) (hwo : w.id.step < fA.current_step)
    (hsplit : ¬ ∃ q ∈ fA.rowParents d t, A.Adj y q ∧ A.Adj w q) :
    ∃ l, 0 ≤ l ∧ l < u.current_step ∧ ∀ r, r.id.step = l → u.Adj t r → ¬ (u.Adj y r ∧ u.Adj w r) := by
  refine ⟨fA.current_step - 1, by omega, by rw [hcsu]; omega, fun r hrl hrt hr => hsplit ?_⟩
  have hro : r.id.step < fA.current_step := by omega
  have hrp : r ∈ fA.rowParents d t := by
    rcases hu hrt with h | h
    · exact rowParent_of_adj hdocs hb hea hta hdA ht hrl ((shrinks_review _).1.adj _ _ h)
    · exact absurd (heaG t r h).1 htg
  have hA : ∀ {z}, z.id.step < fA.current_step → u.Adj z r → A.Adj z r := by
    intro z hz h
    rcases hu h with h | h
    · exact adj_old_of_arrival hsA hdA hz hro h
    · exact absurd (heaG z r h).2 (hrg r hrp)
  exact ⟨r, hrp, hA hyo hr.1, hA hwo hr.2⟩

/-- **CrossAt bajo un mismo padre**: como `CrossAt`, pero solo para parejas que un mismo padre de `t` posee. -/
def CrossAt1 (A B f : GPathB) (d : NodeId) (t : PathNodeId) : Prop :=
  ∀ y w, GroupStar A f d t y → GroupStar A f d t w → (∃ q ∈ f.rowParents d t, A.Adj y q ∧ A.Adj w q) →
    B.Adj y w → ¬ A.Adj y w →
    ∃ l, 0 ≤ l ∧ l < A.current_step ∧
      ∀ r, GroupStar A f d t r → r.id.step = l → ¬ ((A.Adj y r ∨ B.Adj y r) ∧ (A.Adj w r ∨ B.Adj w r))

theorem crossAt1_of_crossAt {A B f : GPathB} {t : PathNodeId} (h : CrossAt A B (GroupStar A f d t)) :
    CrossAt1 A B f d t := fun y w hy hw _ hB hA => h y w hy hw hB hA

/-- **El caso ausente con `CrossAt1`**: bajo un mismo padre, `CrossAt1`; repartida, el paso de los padres. -/
theorem starOneSide_absent1 {A B fA fB u : GPathB} {forbA forbB : PathNodeId → Bool}
    (hsA : Sub fA A) (hsB : Sub fB B) (hdA : d.step = fA.current_step) (hdB : d.step = fB.current_step)
    (hpos : 0 < fA.current_step)
    (hdocs : AliveDocs fA) (hb : Below fA) (hea : EdgesAlive fA) (hta : TopsApart fA)
    (heaG : EdgesAlive ((fB.addNode d "" forbB).review))
    (hu : ∀ {a b}, u.Adj a b → ((fA.addNode d "" forbA).review).Adj a b ∨ ((fB.addNode d "" forbB).review).Adj a b)
    (hcsu : u.current_step = fA.current_step + 1)
    {t : PathNodeId} (ht : t ∈ fA.newRowIds d forbA) (htg : t ∉ ((fB.addNode d "" forbB).review).alive)
    (hrg : ∀ r, r ∈ fA.rowParents d t → r ∉ ((fB.addNode d "" forbB).review).alive)
    (hX : CrossAt1 A B fA d t)
    {y w : PathNodeId} (hty : u.Adj t y) (htw : u.Adj t w)
    (hg : ((fB.addNode d "" forbB).review).Adj y w) (habs : ¬ A.Adj y w) :
    ∃ l, 0 ≤ l ∧ l < u.current_step ∧ ∀ r, r.id.step = l → u.Adj t r → ¬ (u.Adj y r ∧ u.Adj w r) := by
  generalize heE : (fA.addNode d "" forbA).review = e at *
  generalize heGd : (fB.addNode d "" forbB).review = g at *
  have hcsB : fA.current_step = fB.current_step := hdA.symm.trans hdB
  have hts : t.id.step = fA.current_step := newRow_step hdA ht
  have hte : ∀ {r}, u.Adj t r → e.Adj t r := by
    intro r h
    rcases hu h with h | h
    · exact h
    · exact absurd (heaG t r h).1 htg
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
  by_cases hone : ∃ q ∈ fA.rowParents d t, A.Adj y q ∧ A.Adj w q
  · have hstar : ∀ {r}, u.Adj t r → r.id.step < fA.current_step → GroupStar A fA d t r :=
      fun {r} h hr => groupStar_of_adj hsA hdocs hb hea hdA ht hr (by rw [heE]; exact hte h)
    have hAB : ∀ {a b}, u.Adj a b → a.id.step < fA.current_step → b.id.step < fA.current_step →
        A.Adj a b ∨ B.Adj a b := by
      intro a b h ha hb'
      rcases hu h with h | h
      · exact Or.inl (adj_old_of_arrival hsA hdA ha hb' (by rw [heE]; exact h))
      · exact Or.inr (adj_old_of_arrival hsB hdB (hcsB ▸ ha) (hcsB ▸ hb') (by rw [heGd]; exact h))
    have hB : B.Adj y w := adj_old_of_arrival hsB hdB (hcsB ▸ hyo) (hcsB ▸ hwo) (by rw [heGd]; exact hg)
    have hAcs : fA.current_step = A.current_step := hsA.step
    obtain ⟨l, h0, h1, hl⟩ := hX y w (hstar hty hyo) (hstar htw hwo) hone hB habs
    refine ⟨l, h0, by rw [hcsu]; omega, fun r hrl hrt ⟨hyr, hwr⟩ => ?_⟩
    have hrne : r ≠ t := fun h => by subst h; omega
    have hro := hold (hte hrt) hrne
    exact hl r (hstar hrt hro) hrl ⟨hAB hyr hyo hro, hAB hwr hwo hro⟩
  · subst heE; subst heGd
    exact starOneSide_split hsA hdA hpos hdocs hb hea hta heaG hu hcsu ht htg hrg hyo hwo hone

/-- **El caso quitado (hipótesis local de la llegada)**: una pareja que estaba en el remitente `A` y la llegada `e`
quitó tiene un paso en el que ningún vivo de `e` es testigo común en la unión. Medido (`probe_oneside_history.jl`):
el hueco de la regla de parejas que dejó la llegada sigue libre; allí los testigos de la otra llegada están muertos
en `e`. -/
def GapDead (A e g u : GPathB) : Prop :=
  ∀ t, t ∈ e.alive → t.id.step = u.current_step - 1 → ∀ y w, u.Adj t y → u.Adj t w → g.Adj y w → ¬ e.Adj y w →
    A.Adj y w → ∃ l, 0 ≤ l ∧ l < u.current_step ∧ ∀ r, r ∈ e.alive → r.id.step = l → ¬ (u.Adj y r ∧ u.Adj w r)

/-- **StarOneSide en el lado de una llegada** ⇐ `CrossAt` (caso ausente) + `GapDead` (caso quitado). -/
theorem starOneSideAt_of_hist {A B fA fB u : GPathB} {forbA forbB : PathNodeId → Bool}
    (hsA : Sub fA A) (hsB : Sub fB B) (hdA : d.step = fA.current_step) (hdB : d.step = fB.current_step)
    (hdocs : AliveDocs fA) (hb : Below fA) (hea : EdgesAlive fA)
    (heaE : EdgesAlive ((fA.addNode d "" forbA).review)) (heaG : EdgesAlive ((fB.addNode d "" forbB).review))
    (hu : ∀ {a b}, u.Adj a b → ((fA.addNode d "" forbA).review).Adj a b ∨ ((fB.addNode d "" forbB).review).Adj a b)
    (hcsu : u.current_step = fA.current_step + 1)
    (hD2 : ∀ t, t ∈ ((fA.addNode d "" forbA).review).alive → t.id.step = u.current_step - 1 →
      t ∉ ((fB.addNode d "" forbB).review).alive)
    (hX : ∀ t, t ∈ fA.newRowIds d forbA → CrossAt A B (GroupStar A fA d t))
    (hGap : GapDead A ((fA.addNode d "" forbA).review) ((fB.addNode d "" forbB).review) u) :
    StarOneSideAt u ((fA.addNode d "" forbA).review) := by
  intro t htL hts y w hty htw hyw hne
  have htg := hD2 t htL hts
  -- t es de la fila nueva
  have htnew : t ∈ fA.newRowIds d forbA := by
    have ha := (shrinks_review (fA.addNode d "" forbA)).1.alive t htL
    rcases alive_addNode_cases (title := "") hdocs hb hdA ha with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact h
  have hg : ((fB.addNode d "" forbB).review).Adj y w := by
    rcases hu hyw with h | h
    · exact absurd h hne
    · exact h
  by_cases hA : A.Adj y w
  · obtain ⟨l, h0, h1, hl⟩ := hGap t htL hts y w hty htw hg hne hA
    refine ⟨l, h0, h1, fun r hrl hrt hyr => hl r ?_ hrl hyr⟩
    rcases hu hrt with h | h
    · exact (heaE t r h).2
    · exact absurd (heaG t r h).1 htg
  · exact starOneSide_absent hsA hsB hdA hdB hdocs hb hea heaG hu hcsu htnew htg (hX t htnew) hty htw hg hA

/-- **StarOneSide en el lado de una llegada** ⇐ `CrossAt1` (bajo un mismo padre) + `GapDead` (caso quitado); el caso
repartido está demostrado. -/
theorem starOneSideAt_of_hist1 {A B fA fB u : GPathB} {forbA forbB : PathNodeId → Bool}
    (hsA : Sub fA A) (hsB : Sub fB B) (hdA : d.step = fA.current_step) (hdB : d.step = fB.current_step)
    (hpos : 0 < fA.current_step)
    (hdocs : AliveDocs fA) (hb : Below fA) (hea : EdgesAlive fA) (hta : TopsApart fA)
    (heaE : EdgesAlive ((fA.addNode d "" forbA).review)) (heaG : EdgesAlive ((fB.addNode d "" forbB).review))
    (hu : ∀ {a b}, u.Adj a b → ((fA.addNode d "" forbA).review).Adj a b ∨ ((fB.addNode d "" forbB).review).Adj a b)
    (hcsu : u.current_step = fA.current_step + 1)
    (hD2 : ∀ t, t ∈ ((fA.addNode d "" forbA).review).alive → t.id.step = u.current_step - 1 →
      t ∉ ((fB.addNode d "" forbB).review).alive)
    (hrg : ∀ t, t ∈ fA.newRowIds d forbA → ∀ r, r ∈ fA.rowParents d t →
      r ∉ ((fB.addNode d "" forbB).review).alive)
    (hX : ∀ t, t ∈ fA.newRowIds d forbA → CrossAt1 A B fA d t)
    (hGap : GapDead A ((fA.addNode d "" forbA).review) ((fB.addNode d "" forbB).review) u) :
    StarOneSideAt u ((fA.addNode d "" forbA).review) := by
  intro t htL hts y w hty htw hyw hne
  have htg := hD2 t htL hts
  have htnew : t ∈ fA.newRowIds d forbA := by
    have ha := (shrinks_review (fA.addNode d "" forbA)).1.alive t htL
    rcases alive_addNode_cases (title := "") hdocs hb hdA ha with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact h
  have hg : ((fB.addNode d "" forbB).review).Adj y w := by
    rcases hu hyw with h | h
    · exact absurd h hne
    · exact h
  by_cases hA : A.Adj y w
  · obtain ⟨l, h0, h1, hl⟩ := hGap t htL hts y w hty htw hg hne hA
    refine ⟨l, h0, h1, fun r hrl hrt hyr => hl r ?_ hrl hyr⟩
    rcases hu hrt with h | h
    · exact (heaE t r h).2
    · exact absurd (heaG t r h).1 htg
  · exact starOneSide_absent1 hsA hsB hdA hdB hpos hdocs hb hea hta heaG hu hcsu htnew htg (hrg t htnew)
      (hX t htnew) hty htw hg hA

end GPathB

end AbsSatBingo.Model
