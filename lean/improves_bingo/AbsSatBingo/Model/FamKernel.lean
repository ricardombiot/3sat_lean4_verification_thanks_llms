-- lean/improves_bingo/AbsSatBingo/Model/FamKernel.lean
import AbsSatBingo.Model.Lineage

/-!
# Estructuras cerradas sobre una familia de estados

Para no construir la unión de toda una línea como un solo estado (joins encadenados), una estructura cerrada «de la
unión» de una familia `F` se define con los vivos, las posesiones y los enlaces de sus miembros (`FamStruct`). La
relación **`Covers F F'`** (todo lo de un miembro de `F` está en algún miembro de `F'`) lleva las estructuras de `F` a
`F'` (`famStruct_covers`); el join (`covers_join`) y lo que solo quita (`covers_sub`) son coberturas.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- `p` es padre de `x` en algún miembro de `F`. -/
def FPar (F : GPathB → Prop) (x p : PathNodeId) : Prop := ∃ g n, F g ∧ g.node? x = some n ∧ p ∈ n.parents
/-- `s` es hijo de `x` en algún miembro de `F`. -/
def FSon (F : GPathB → Prop) (x s : PathNodeId) : Prop := ∃ g n, F g ∧ g.node? x = some n ∧ s ∈ n.sons
/-- `x` tiene documento en algún miembro de `F`. -/
def FDoc (F : GPathB → Prop) (x : PathNodeId) : Prop := ∃ g n, F g ∧ g.node? x = some n

/-- **Una estructura cerrada de la unión de la familia `F`** (todos sus miembros en el paso `c`). -/
structure FamStruct (F : GPathB → Prop) (c : Int) (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop) :
    Prop where
  alive : ∀ {y}, V y → ∃ g, F g ∧ y ∈ g.alive
  refl  : ∀ {y}, V y → R y y
  symm  : ∀ {y w}, R y w → R w y
  dom   : ∀ {y w}, R y w → V y ∧ V w
  adj   : ∀ {y w}, R y w → ∃ g, F g ∧ g.Adj y w
  pair  : ∀ {y w}, R y w → ∀ l, 0 ≤ l → l < c → ∃ r, r.id.step = l ∧ R y r ∧ R w r
  doc   : ∀ {y}, V y → FDoc F y
  node  : ∀ {y}, V y → (y.parent_id.isNone = false → ∃ p, FPar F y p ∧ R y p) ∧
            (y.id.step ≠ c - 1 → ∃ s, FSon F y s ∧ R y s)
  par   : ∀ {x w}, R x w → x ≠ w → 1 ≤ x.id.step → ∃ p, FPar F x p ∧ R x p ∧ R p w
  son   : ∀ {x w}, R x w → x ≠ w → x.id.step + 1 < c → ∃ s, FSon F x s ∧ R x s ∧ R s w

/-- El núcleo de la familia fijado en `P`. -/
def FamKernel (F : GPathB → Prop) (c : Int) (P : List NodeId) (y w : PathNodeId) : Prop :=
  ∃ V R, FamStruct F c V R ∧ (∀ b ∈ P, SecAgrees V b) ∧ R y w

/-- **`F'` cubre a `F`**: vivos, posesiones, documentos y enlaces de cada miembro de `F` están en algún miembro de
`F'`. -/
def Covers (F F' : GPathB → Prop) : Prop :=
  ∀ g, F g → (∀ y ∈ g.alive, ∃ g', F' g' ∧ y ∈ g'.alive) ∧ (∀ y w, g.Adj y w → ∃ g', F' g' ∧ g'.Adj y w) ∧
    (∀ x n, g.node? x = some n → FDoc F' x ∧ (∀ p ∈ n.parents, FPar F' x p) ∧ (∀ s ∈ n.sons, FSon F' x s))

theorem fDoc_covers {F F' : GPathB → Prop} (hc : Covers F F') {x : PathNodeId} (h : FDoc F x) : FDoc F' x := by
  obtain ⟨g, n, hg, hn⟩ := h; exact ((hc g hg).2.2 x n hn).1

theorem fPar_covers {F F' : GPathB → Prop} (hc : Covers F F') {x p : PathNodeId} (h : FPar F x p) : FPar F' x p := by
  obtain ⟨g, n, hg, hn, hp⟩ := h; exact ((hc g hg).2.2 x n hn).2.1 p hp

theorem fSon_covers {F F' : GPathB → Prop} (hc : Covers F F') {x s : PathNodeId} (h : FSon F x s) : FSon F' x s := by
  obtain ⟨g, n, hg, hn, hs⟩ := h; exact ((hc g hg).2.2 x n hn).2.2 s hs

/-- **Una cobertura lleva las estructuras de `F` a `F'`.** -/
theorem famStruct_covers {F F' : GPathB → Prop} {c : Int} {V : PathNodeId → Prop}
    {R : PathNodeId → PathNodeId → Prop} (hc : Covers F F') (hst : FamStruct F c V R) : FamStruct F' c V R := by
  refine ⟨fun hy => ?_, hst.refl, hst.symm, hst.dom, fun h => ?_, hst.pair, fun hy => fDoc_covers hc (hst.doc hy),
    fun hy => ?_, fun hr hne h1 => ?_, fun hr hne h1 => ?_⟩
  · obtain ⟨g, hg, ha⟩ := hst.alive hy; exact (hc g hg).1 _ ha
  · obtain ⟨g, hg, ha⟩ := hst.adj h; exact (hc g hg).2.1 _ _ ha
  · obtain ⟨h1, h2⟩ := hst.node hy
    exact ⟨fun hk => by obtain ⟨p, hp, hr⟩ := h1 hk; exact ⟨p, fPar_covers hc hp, hr⟩,
      fun hk => by obtain ⟨s, hs, hr⟩ := h2 hk; exact ⟨s, fSon_covers hc hs, hr⟩⟩
  · obtain ⟨p, hp, h2, h3⟩ := hst.par hr hne h1
    exact ⟨p, fPar_covers hc hp, h2, h3⟩
  · obtain ⟨s, hs, h2, h3⟩ := hst.son hr hne h1
    exact ⟨s, fSon_covers hc hs, h2, h3⟩

theorem famKernel_covers {F F' : GPathB → Prop} {c : Int} (hc : Covers F F') {P : List NodeId} {y w : PathNodeId}
    (h : FamKernel F c P y w) : FamKernel F' c P y w := by
  obtain ⟨V, R, hst, ha, hr⟩ := h
  exact ⟨V, R, famStruct_covers hc hst, ha, hr⟩

-- ============================================================
-- Un estado y la familia de un solo miembro
-- ============================================================

/-- Una estructura de un estado miembro es una estructura de la familia. -/
theorem famStruct_of_secStruct {F : GPathB → Prop} {g : GPathB} (hg : F g) {V : PathNodeId → Prop}
    {R : PathNodeId → PathNodeId → Prop} (hst : SecStruct g V R) : FamStruct F g.current_step V R := by
  refine ⟨fun hy => ⟨g, hg, hst.alive hy⟩, hst.refl, hst.symm, hst.dom, fun h => ⟨g, hg, hst.adj h⟩, hst.pair,
    fun hy => ?_, fun hy => ?_, fun hr hne h1 => ?_, fun hr hne h1 => ?_⟩
  · obtain ⟨n, hn, _⟩ := hst.node hy; exact ⟨g, n, hg, hn⟩
  · obtain ⟨n, hn, h1, h2⟩ := hst.node hy
    exact ⟨fun hk => by obtain ⟨p, hp, hr⟩ := h1 hk; exact ⟨p, ⟨g, n, hg, hn, hp⟩, hr⟩,
      fun hk => by obtain ⟨s, hs, hr⟩ := h2 hk; exact ⟨s, ⟨g, n, hg, hn, hs⟩, hr⟩⟩
  · obtain ⟨n, hn, _⟩ := hst.node (hst.dom hr).1
    obtain ⟨p, hp, h2, h3⟩ := hst.par hr hne hn h1
    exact ⟨p, ⟨g, n, hg, hn, hp⟩, h2, h3⟩
  · obtain ⟨n, hn, _⟩ := hst.node (hst.dom hr).1
    obtain ⟨s, hs, h2, h3⟩ := hst.son hr hne hn h1
    exact ⟨s, ⟨g, n, hg, hn, hs⟩, h2, h3⟩

theorem famKernel_of_kernel {F : GPathB → Prop} {g : GPathB} (hg : F g) {P : List NodeId} {y w : PathNodeId}
    (h : Kernel g P y w) : FamKernel F g.current_step P y w := by
  obtain ⟨V, R, hst, ha, hr⟩ := h
  exact ⟨V, R, famStruct_of_secStruct hg hst, ha, hr⟩

/-- **Una estructura de la familia de un solo estado es una estructura de ese estado.** -/
theorem secStruct_of_famStruct {g : GPathB} {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop}
    (hst : FamStruct (· = g) g.current_step V R) : SecStruct g V R := by
  refine ⟨fun hy => ?_, hst.refl, hst.symm, hst.dom, fun h => ?_, hst.pair, fun hy => ?_, fun hr hne hn h1 => ?_,
    fun hr hne hn h1 => ?_⟩
  · obtain ⟨g', rfl, ha⟩ := hst.alive hy; exact ha
  · obtain ⟨g', rfl, ha⟩ := hst.adj h; exact ha
  · obtain ⟨g', n, rfl, hn⟩ := hst.doc hy
    obtain ⟨h1, h2⟩ := hst.node hy
    refine ⟨n, hn, fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨p, ⟨g'', n', rfl, hn', hp⟩, hr⟩ := h1 hk
      rw [hn] at hn'; cases hn'; exact ⟨p, hp, hr⟩
    · obtain ⟨s, ⟨g'', n', rfl, hn', hs⟩, hr⟩ := h2 hk
      rw [hn] at hn'; cases hn'; exact ⟨s, hs, hr⟩
  · obtain ⟨p, ⟨g'', n', rfl, hn', hp⟩, h2, h3⟩ := hst.par hr hne h1
    rw [hn] at hn'; cases hn'; exact ⟨p, hp, h2, h3⟩
  · obtain ⟨s, ⟨g'', n', rfl, hn', hs⟩, h2, h3⟩ := hst.son hr hne h1
    rw [hn] at hn'; cases hn'; exact ⟨s, hs, h2, h3⟩

theorem kernel_of_famKernel {g : GPathB} {P : List NodeId} {y w : PathNodeId}
    (h : FamKernel (· = g) g.current_step P y w) : Kernel g P y w := by
  obtain ⟨V, R, hst, ha, hr⟩ := h
  exact ⟨V, R, secStruct_of_famStruct hst, ha, hr⟩

-- ============================================================
-- Coberturas: el join, lo que solo quita, la transitividad
-- ============================================================

theorem covers_trans {F F' F'' : GPathB → Prop} (h1 : Covers F F') (h2 : Covers F' F'') : Covers F F'' := by
  intro g hg
  obtain ⟨ha, hj, hn⟩ := h1 g hg
  refine ⟨fun y hy => ?_, fun y w h => ?_, fun x n hx => ?_⟩
  · obtain ⟨g', hg', hy'⟩ := ha y hy; exact (h2 g' hg').1 y hy'
  · obtain ⟨g', hg', h'⟩ := hj y w h; exact (h2 g' hg').2.1 y w h'
  · obtain ⟨hd, hp, hs⟩ := hn x n hx
    exact ⟨fDoc_covers h2 hd, fun p h => fPar_covers h2 (hp p h), fun s' h => fSon_covers h2 (hs s' h)⟩

/-- Una familia está cubierta por cualquier familia que la contenga. -/
theorem covers_of_sub {F F' : GPathB → Prop} (h : ∀ g, F g → F' g) : Covers F F' := by
  intro g hg
  refine ⟨fun y hy => ⟨g, h g hg, hy⟩, fun y w hyw => ⟨g, h g hg, hyw⟩, fun x n hx => ⟨⟨g, n, h g hg, hx⟩,
    fun p hp => ⟨g, n, h g hg, hx, hp⟩, fun s' hs => ⟨g, n, h g hg, hx, hs⟩⟩⟩

/-- **El join está cubierto por sus dos lados.** -/
theorem covers_join (e g : GPathB) : Covers (· = join e g) (fun h => h = e ∨ h = g) := by
  intro u hu
  subst hu
  refine ⟨fun y hy => ?_, fun y w h => ?_, fun x n hx => ?_⟩
  · rcases (alive_join e g y).mp hy with h | h
    · exact ⟨e, Or.inl rfl, h⟩
    · exact ⟨g, Or.inr rfl, h⟩
  · rcases adj_join_cases h with h | h
    · exact ⟨e, Or.inl rfl, h⟩
    · exact ⟨g, Or.inr rfl, h⟩
  · rw [node?_join] at hx
    cases he : e.node? x with
    | some a =>
      rw [he] at hx
      simp only [Option.map_some, Option.some_or, Option.some.injEq] at hx
      have haid := node?_id he
      revert hx
      split
      · rename_i m hm
        intro hx; subst hx
        have hm' : g.node? x = some m := by rw [← haid]; exact hm
        refine ⟨⟨e, a, Or.inl rfl, he⟩, fun p hp => ?_, fun s' hs => ?_⟩
        · rcases merge_parents_cases hp with hp | hp
          · exact ⟨e, a, Or.inl rfl, he, hp⟩
          · exact ⟨g, m, Or.inr rfl, hm', hp⟩
        · rcases merge_sons_cases hs with hs | hs
          · exact ⟨e, a, Or.inl rfl, he, hs⟩
          · exact ⟨g, m, Or.inr rfl, hm', hs⟩
      · intro hx; subst hx
        exact ⟨⟨e, a, Or.inl rfl, he⟩, fun p hp => ⟨e, a, Or.inl rfl, he, hp⟩,
          fun s' hs => ⟨e, a, Or.inl rfl, he, hs⟩⟩
    | none =>
      rw [he] at hx
      simp only [Option.map_none, Option.none_or] at hx
      rw [find?_filter_of] at hx
      · have hg : g.node? x = some n := hx
        exact ⟨⟨g, n, Or.inr rfl, hg⟩, fun p hp => ⟨g, n, Or.inr rfl, hg, hp⟩,
          fun s' hs => ⟨g, n, Or.inr rfl, hg, hs⟩⟩
      · intro a _ ha
        have : a.id = x := by simpa using ha
        rw [this, he]; rfl

/-- **Lo que solo quita está cubierto por el estado de antes** (con un documento por id en el de antes). -/
theorem covers_sub {h g : GPathB} (hs : Sub h g) (hnd : NodupIds g) : Covers (· = h) (· = g) := by
  intro h' hh
  subst hh
  refine ⟨fun y hy => ⟨g, rfl, hs.alive y hy⟩, fun y w hyw => ⟨g, rfl, hs.adj y w hyw⟩, fun x n hx => ?_⟩
  obtain ⟨m, hm, hid, hp, hso⟩ := hs.nodes n (node?_mem hx)
  have hgm : g.node? x = some m := by
    rw [← node?_id hx, ← hid]; exact node?_of_nodup hnd hm
  exact ⟨⟨g, m, rfl, hgm⟩, fun p hp' => ⟨g, m, rfl, hgm, hp p hp'⟩, fun s' hs' => ⟨g, m, rfl, hgm, hso s' hs'⟩⟩

-- ============================================================
-- La bajada por las filas nuevas, en familia
-- ============================================================

open Machine (Below)

section down
variable {title : String} {forb : PathNodeId → Bool}

/-- La familia de las filas nuevas de los pares `(f, d)` de `G`. -/
def RowsOf (G : GPathB → NodeId → Prop) (title : String) (forb : PathNodeId → Bool) : GPathB → Prop :=
  fun a => ∃ f d, G f d ∧ a = f.addNode d title forb

/-- **Una estructura de la unión de filas nuevas, restringida a los pasos viejos, es de la unión de los estados de
partida.** -/
theorem famStruct_rows_down {G : GPathB → NodeId → Prop} {c : Int}
    (hG : ∀ f d, G f d → AliveDocs f ∧ Below f ∧ LinksStep f ∧ f.current_step = c ∧ d.step = c)
    {V : PathNodeId → Prop} {R : PathNodeId → PathNodeId → Prop} (hst : FamStruct (RowsOf G title forb) (c + 1) V R) :
    FamStruct (fun f => ∃ d, G f d) c (fun q => V q ∧ q.id.step < c)
      (fun y w => R y w ∧ y.id.step < c ∧ w.id.step < c) := by
  -- un documento viejo de una fila nueva es el documento del estado de partida, con los hijos ganados
  have hold : ∀ {a y m}, RowsOf G title forb a → y.id.step < c → a.node? y = some m →
      ∃ f d n, G f d ∧ f.node? y = some n ∧ m = f.withGained d forb n := by
    intro a y m ha hy hm
    obtain ⟨f, d, hfd, rfl⟩ := ha
    obtain ⟨_, _, _, hcs, hds⟩ := hG f d hfd
    rw [node?_addNode_old (title := title) (hds.trans hcs.symm) (by omega)] at hm
    cases hn : f.node? y with
    | none => rw [hn] at hm; cases hm
    | some n => rw [hn] at hm; cases hm; exact ⟨f, d, n, hfd, hn, rfl⟩
  have hparstep : ∀ {f d y n p}, G f d → f.node? y = some n → p ∈ n.parents → p.id.step < c := by
    intro f d y n p hfd hn hp
    obtain ⟨_, hb, hls, hcs, _⟩ := hG f d hfd
    have h1 := (hls n (node?_mem hn)).1 p hp
    have h2 := hb n (node?_mem hn)
    omega
  have hsonstep : ∀ {f d y n s'}, G f d → f.node? y = some n → s' ∈ n.sons → y.id.step + 1 < c → s'.id.step < c := by
    intro f d y n s' hfd hn hs hy
    obtain ⟨_, hb, hls, hcs, _⟩ := hG f d hfd
    have h1 := (hls n (node?_mem hn)).2 s' hs
    rw [node?_id hn] at h1
    omega
  -- un hijo ganado solo lo tiene una cima del estado de partida
  have hgain : ∀ {f d y n s'}, G f d → f.node? y = some n → s' ∈ f.gainedSons d forb n → y.id.step + 1 = c := by
    intro f d y n s' hfd hn hs
    obtain ⟨_, _, _, hcs, _⟩ := hG f d hfd
    obtain ⟨_, hp⟩ := gained_new hs
    obtain ⟨_, _, _, hstep⟩ := step_of_newParents hp
    rw [node?_id hn] at hstep
    omega
  refine ⟨fun ⟨hq, hqs⟩ => ?_, fun ⟨hq, hqs⟩ => ⟨hst.refl hq, hqs, hqs⟩, fun ⟨hr, h1, h2⟩ => ⟨hst.symm hr, h2, h1⟩,
    fun ⟨hr, h1, h2⟩ => ⟨⟨(hst.dom hr).1, h1⟩, ⟨(hst.dom hr).2, h2⟩⟩, fun ⟨hr, h1, h2⟩ => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ⟨f, d, hfd, rfl⟩, ha⟩ := hst.alive hq
    obtain ⟨hdoc, hb, _, hcs, hds⟩ := hG f d hfd
    rcases alive_addNode_cases (title := title) hdoc hb (hds.trans hcs.symm) ha with ⟨h, _⟩ | ⟨_, h⟩
    · exact ⟨f, ⟨d, hfd⟩, h⟩
    · omega
  · obtain ⟨a, ⟨f, d, hfd, rfl⟩, ha⟩ := hst.adj hr
    obtain ⟨_, _, _, hcs, hds⟩ := hG f d hfd
    exact ⟨f, ⟨d, hfd⟩, adj_addNode_old (title := title) (forb := forb) (hds.trans hcs.symm) (by omega) (by omega) ha⟩
  · rintro y w ⟨hr, h1, h2⟩ l hl0 hl1
    obtain ⟨r, hrl, hyr, hwr⟩ := hst.pair hr l hl0 (by omega)
    exact ⟨r, hrl, ⟨hyr, h1, by omega⟩, ⟨hwr, h2, by omega⟩⟩
  · rintro y ⟨hy, hys⟩
    obtain ⟨a, m, ha, hm⟩ := hst.doc hy
    obtain ⟨f, d, n, hfd, hn, _⟩ := hold ha hys hm
    exact ⟨f, n, ⟨d, hfd⟩, hn⟩
  · rintro y ⟨hy, hys⟩
    obtain ⟨hp, hs⟩ := hst.node hy
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨p, ⟨a, m, ha, hm, hpm⟩, hyp⟩ := hp hk
      obtain ⟨f, d, n, hfd, hn, rfl⟩ := hold ha hys hm
      exact ⟨p, ⟨f, n, ⟨d, hfd⟩, hn, hpm⟩, hyp, hys, hparstep hfd hn hpm⟩
    · obtain ⟨s', ⟨a, m, ha, hm, hsm⟩, hys'⟩ := hs (by omega)
      obtain ⟨f, d, n, hfd, hn, rfl⟩ := hold ha hys hm
      rcases List.mem_append.mp hsm with h | h
      · have hlt : y.id.step + 1 < c := by
          rcases Int.lt_or_eq_of_le (show y.id.step + 1 ≤ c by omega) with h' | h'
          · exact h'
          · exact absurd h' (by omega)
        exact ⟨s', ⟨f, n, ⟨d, hfd⟩, hn, h⟩, hys', hys, hsonstep hfd hn h hlt⟩
      · exact absurd (hgain hfd hn h) (by omega)
  · rintro x w ⟨hr, h1, h2⟩ hne hx1
    obtain ⟨p, ⟨a, m, ha, hm, hpm⟩, hxp, hpw⟩ := hst.par hr hne hx1
    obtain ⟨f, d, n, hfd, hn, rfl⟩ := hold ha h1 hm
    have hpo := hparstep hfd hn hpm
    exact ⟨p, ⟨f, n, ⟨d, hfd⟩, hn, hpm⟩, ⟨hxp, h1, hpo⟩, ⟨hpw, hpo, h2⟩⟩
  · rintro x w ⟨hr, h1, h2⟩ hne hx1
    obtain ⟨s', ⟨a, m, ha, hm, hsm⟩, hxs, hsw⟩ := hst.son hr hne (by omega)
    obtain ⟨f, d, n, hfd, hn, rfl⟩ := hold ha h1 hm
    rcases List.mem_append.mp hsm with h | h
    · have hso := hsonstep hfd hn h hx1
      exact ⟨s', ⟨f, n, ⟨d, hfd⟩, hn, h⟩, ⟨hxs, h1, hso⟩, ⟨hsw, hso, h2⟩⟩
    · exact absurd (hgain hfd hn h) (by omega)

end down

end GPathB

end AbsSatBingo.Model
