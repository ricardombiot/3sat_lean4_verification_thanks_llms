-- lean/improves_bingo/AbsSatBingo/Model/Lineage.lean
import AbsSatBingo.Model.TopsFrom
import AbsSatBingo.Model.StarLocal

/-!
# La inducción por linajes: esqueleto

**La copia por linaje** de un estado de la línea `z` es `z.filterAll R`, con `R` los requisitos del camino de
destinos por encima (`R` crece al bajar: `req d ++ R'`).

**La hipótesis de inducción** (`LinIH x y`): para dos estados de la línea del mismo paso en nodos del mapa distintos,
y **cualquier** filtro común `R`, `TopUnion` entre sus copias. Que el filtro sea cualquiera es lo que deja absorber
los requisitos de todo el linaje.

**El paso** (`lin_step`): `LinIH` para los remitentes de `d` (`x`, `y`) da `TopUnion` entre las copias de los estados
del paso siguiente `u = UP x d ∪ UP y d` y `u' = UP x' d' ∪ UP y' d'`, con la bajada estructural **`JoinDownGen`** como
hipótesis explícita. La cadena: cima viva en la unión de copias → `JoinDownGen` → padre vivo en la unión de las copias
de los remitentes con el filtro compuesto `req d ++ R'` → `LinIH` → padre en la copia de su linaje → (A) → la cima en
el UP → en `u` → en su copia `u.filterAll R'`.

**La inducción conjunta** (`ltu_step`): `LTU` (la partición de la unión de la línea por remitentes) pasa de un paso
al siguiente con `PinFree` en el siguiente (fijar los requisitos de la fila de una cima no la mata) y la bajada y la
subida estructurales (`LineDown`, `LineUp`, monotonía). `PinFree` sale de `TopStarK` en esa unión
(`pinFree_of_topStar`); ninguna de las dos se deduce del paso anterior. Medido (`test_3sat/probe_pinfree.jl`):
`PinFree` y, con lados = remitentes y el pin ampliado, `TopsSep`, `TopStar` y `StarKinds`, sin fallos.

**Caso base**: en el paso 1 la línea tiene un solo estado (la semilla), así que no hay pares de estados de nodos del
mapa distintos y `LinIH` es vacía.

**`JoinDownGen` no es monotonía.** Su premisa es una estructura de la unión de las copias de `u` y `u'` (las llegadas a
`d` y a `d'`), y su conclusión vive solo en las copias de los remitentes de `d` con el filtro `req d ++ R'`: pasar de
un estado mayor a uno menor exige partir la estructura por el nodo del mapa de la cima (`TopSplit` entre nodos del mapa
distintos), que es el contenido de `KernelUnion`. En los joins de la máquina (un solo destino, filtro común) la bajada
sí es monotonía (`JoinDown`), pero `LinIH` compara estados de destinos distintos.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

open Machine (Below below_of_shrinks mapId_of_mem_shiftRowIds)

variable (rq : NodeId → List NodeId) (title : String) (forb : PathNodeId → Bool)

/-- El UP de la máquina hacia `d`: filtrar con sus requisitos, la fila nueva y el review. -/
def upL (z : GPathB) (d : NodeId) : GPathB := ((z.filterAll (rq d)).addNode d title forb).review

/-- **La hipótesis de inducción**: `TopUnion` entre las copias de `x` e `y` con cualquier filtro común. -/
def LinIH (x y : GPathB) : Prop := ∀ R : List NodeId, TopUnion (x.filterAll R) (y.filterAll R)

/-- **`JoinDownGen`** (hipótesis): una cima viva en la unión de las copias de `u` y `u'` (con filtro `R'`) que está en
la copia de `u` es hija, en la fila de uno de los remitentes de `d`, de un padre vivo en la unión de las copias de
los remitentes con el filtro compuesto `req d ++ R'`. -/
def JoinDownGen (x y : GPathB) (d : NodeId) (u U : GPathB) (R' : List NodeId) : Prop :=
  ∀ (Q : List NodeId) (t : PathNodeId), t.id.step = u.current_step - 1 →
    Kernel U Q t t → t ∈ (u.filterAll R').alive →
    ∃ z p, (z = x ∨ z = y) ∧ p ∈ (z.filterAll (rq d)).rowParents d t ∧ t ∈ (z.filterAll (rq d)).newRowIds d forb ∧
      Kernel (join (x.filterAll (rq d ++ R')) (y.filterAll (rq d ++ R'))) Q p p

/-- Fijar primero `A` y luego `B` es fijar `A ++ B`. -/
theorem kernel_filter_append {z : GPathB} (hd : AliveDocs z) (hnd : NodupIds z) {A B Q : List NodeId}
    {y w : PathNodeId} : Kernel (z.filterAll (A ++ B)) Q y w ↔ Kernel (z.filterAll A) (B ++ Q) y w := by
  rw [kernel_pin_list_iff hd hnd, kernel_pin_list_iff hd hnd, List.append_assoc]

theorem topDocsId_filterAll {z : GPathB} {k : NodeId} (h : TopDocsId z k) (R : List NodeId) :
    TopDocsId (z.filterAll R) k := by
  have hs := (shrinks_filterAll z R).1
  intro n hn h1
  obtain ⟨m, hm, hid, _, _⟩ := hs.nodes n hn
  rw [← hid]
  exact h m hm (by rw [hid, ← hs.step]; exact h1)

theorem step_upL (z : GPathB) (d : NodeId) : (upL rq title forb z d).current_step = z.current_step + 1 := by
  unfold upL
  rw [(shrinks_review _).1.step]
  show (z.filterAll (rq d)).current_step + 1 = _
  rw [(shrinks_filterAll z (rq d)).1.step]

/-- **El paso, del lado de `u`** (`U` es la unión de las copias): con `LinIH` para los remitentes de `d` y `JoinDownGen`, una cima de la copia de `u`
viva en la unión de copias está en el núcleo de la copia de `u`. -/
theorem lin_step_side {x y u U : GPathB} {d kx ky : NodeId} {R' : List NodeId}
    (hu : u = join (upL rq title forb x d) (upL rq title forb y d))
    (hjd : JoinDownGen rq forb x y d u U R') (hih : LinIH x y)
    (hcs : x.current_step = y.current_step) (hpos : 0 < x.current_step) (hd : d.step = x.current_step)
    (hdx : AliveDocs x) (hdy : AliveDocs y) (hnx : NodupIds x) (hny : NodupIds y)
    (hkx : TopExact x) (hky : TopExact y) (hbx : Below x) (hby : Below y)
    (htx : TopDocsId x kx) (hty : TopDocsId y ky) (hk : kx ≠ ky)
    (hdu : AliveDocs u) (hnu : NodupIds u) (hvu : (u.filterAll R').isValid = true)
    {Q : List NodeId} {t : PathNodeId} (hts : t.id.step = u.current_step - 1)
    (hker : Kernel U Q t t) (hta : t ∈ (u.filterAll R').alive) :
    Kernel (u.filterAll R') Q t t := by
  have hus : u.current_step = x.current_step + 1 := by rw [hu]; exact step_upL rq title forb x d
  obtain ⟨z, p, hz, hp, htn, hkp⟩ := hjd Q t hts hker hta
  -- los datos del remitente z
  have hzs : z.current_step = x.current_step := by rcases hz with rfl | rfl; rfl; exact hcs.symm
  have hdz : AliveDocs z := by rcases hz with rfl | rfl; exact hdx; exact hdy
  have hnz : NodupIds z := by rcases hz with rfl | rfl; exact hnx; exact hny
  have htez : TopExact z := by rcases hz with rfl | rfl; exact hkx; exact hky
  have hbz : Below z := by rcases hz with rfl | rfl; exact hbx; exact hby
  have hfs : (z.filterAll (rq d)).current_step = z.current_step := (shrinks_filterAll z _).1.step
  -- el padre es una cima con el id de la clave de z
  obtain ⟨n, hn, hnp, hps⟩ := step_of_newParents (rowParents_sub hp)
  have hps' : p.id.step = x.current_step - 1 := by rw [hps, hfs, hzs]
  -- un vivo de una copia de `o` en el paso de la cima tiene el id de la clave de `o`
  have hkey : ∀ {o : GPathB} {ko : NodeId} (S : List NodeId), AliveDocs o → TopDocsId o ko →
      o.current_step = x.current_step → p ∈ (o.filterAll S).alive → p.id = ko := by
    intro o ko S hdo hto hos hal
    obtain ⟨m, hm, hmid⟩ := aliveDocs_filterAll hdo S p hal
    rw [← hmid]
    exact topDocsId_filterAll hto S m hm (by rw [hmid, (shrinks_filterAll o S).1.step, hos]; exact hps')
  obtain ⟨kz, htz, hkzc⟩ : ∃ kz, TopDocsId z kz ∧ ((z = x ∧ kz = kx) ∨ (z = y ∧ kz = ky)) := by
    rcases hz with rfl | rfl
    · exact ⟨kx, htx, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨ky, hty, Or.inr ⟨rfl, rfl⟩⟩
  have hpz : p.id = kz := by
    rw [← hnp]; exact topDocsId_filterAll htz (rq d) n hn (by rw [hnp]; exact hps)
  -- la hipótesis de inducción con el filtro compuesto
  have hts2 : p.id.step = (x.filterAll (rq d ++ R')).current_step - 1 := by
    rw [(shrinks_filterAll x _).1.step]; exact hps'
  have hkz : Kernel (z.filterAll (rq d ++ R')) Q p p := by
    rcases hih (rq d ++ R') Q p hts2 hkp with h | h
    · rcases hkzc with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
      · exact h
      · exfalso
        obtain ⟨V, R, hst, _, hr⟩ := h
        exact hk ((hkey (rq d ++ R') hdx htx rfl (hst.alive (hst.dom hr).1)).symm.trans hpz)
    · rcases hkzc with ⟨rfl, rfl⟩ | ⟨rfl, _⟩
      · exfalso
        obtain ⟨V, R, hst, _, hr⟩ := h
        exact hk (hpz.symm.trans (hkey (rq d ++ R') hdy hty hcs.symm (hst.alive (hst.dom hr).1)))
      · exact h
  have hkz' : Kernel (z.filterAll (rq d)) (R' ++ Q) p p := (kernel_filter_append hdz hnz).mp hkz
  -- lo que R' ++ Q fija en el paso de t es d
  have htd : t.id = d := mapId_of_mem_shiftRowIds (List.mem_filter.mp htn).1
  have htstep : t.id.step = x.current_step := by omega
  have hP : ∀ r ∈ R' ++ Q, r.step = (z.filterAll (rq d)).current_step → r = d := by
    intro r hr hrs
    rw [hfs, hzs] at hrs
    rcases List.mem_append.mp hr with hr | hr
    · rw [← htd]
      exact (pinned_filterAll_list hdu R' hvu r hr t hta (by rw [htstep, hrs])).symm
    · obtain ⟨V, R, hst, ha, hr'⟩ := hker
      rw [← htd]
      exact (ha r hr (hst.dom hr').1 (by rw [htstep, hrs])).symm
  -- (A): la cima en el UP del remitente, luego en `u`, luego en su copia
  have hup : Kernel (upL rq title forb z d) (R' ++ Q) t t :=
    kernel_up_of_parent (topExact_filterAll htez hdz hnz _) (below_of_shrinks (shrinks_filterAll z _) hbz)
      (by rw [hfs, hzs]; exact hpos) (by rw [hfs, hzs]; exact hd) hp htn hP hkz'
  have hinu : Kernel u (R' ++ Q) t t := by
    rw [hu]
    rcases hz with rfl | rfl
    · exact kernel_join_left hup
    · exact kernel_join_right (by rw [step_upL, step_upL, hcs]) hup
  exact (kernel_pin_list_iff hdu hnu t t).mpr hinu

/-- Los datos de un par de remitentes. -/
structure Senders (x y : GPathB) (d kx ky : NodeId) : Prop where
  cs  : x.current_step = y.current_step
  pos : 0 < x.current_step
  dst : d.step = x.current_step
  dx  : AliveDocs x
  dy  : AliveDocs y
  nx  : NodupIds x
  ny  : NodupIds y
  ex  : TopExact x
  ey  : TopExact y
  bx  : Below x
  by_ : Below y
  tx  : TopDocsId x kx
  ty  : TopDocsId y ky
  ne  : kx ≠ ky

/-- **El paso inductivo** (`LinIH` de los remitentes ⇒ `LinIH` de los estados siguientes), con `JoinDownGen` como
hipótesis explícita en los dos lados. -/
theorem lin_step {x y x' y' u u' : GPathB} {d d' kx ky kx' ky' : NodeId}
    (hu : u = join (upL rq title forb x d) (upL rq title forb y d))
    (hu' : u' = join (upL rq title forb x' d') (upL rq title forb y' d'))
    (hs : Senders x y d kx ky) (hs' : Senders x' y' d' kx' ky')
    (hih : LinIH x y) (hih' : LinIH x' y') (hcs : u.current_step = u'.current_step)
    (hdu : AliveDocs u) (hnu : NodupIds u) (hdu' : AliveDocs u') (hnu' : NodupIds u')
    (hjd : ∀ R', JoinDownGen rq forb x y d u (join (u.filterAll R') (u'.filterAll R')) R')
    (hjd' : ∀ R', JoinDownGen rq forb x' y' d' u' (join (u.filterAll R') (u'.filterAll R')) R')
    (hvu : ∀ R', (u.filterAll R').isValid = true) (hvu' : ∀ R', (u'.filterAll R').isValid = true) :
    LinIH u u' := by
  intro R' Q t hts hk
  have hfs : (u.filterAll R').current_step = u.current_step := (shrinks_filterAll u R').1.step
  have hfs' : (u'.filterAll R').current_step = u'.current_step := (shrinks_filterAll u' R').1.step
  have hk0 := hk
  obtain ⟨V, R, hst, _, hr⟩ := hk0
  rcases (alive_join _ _ t).mp (hst.alive (hst.dom hr).1) with hta | hta
  · exact Or.inl (lin_step_side rq title forb hu (hjd R') hih hs.cs hs.pos hs.dst hs.dx hs.dy hs.nx hs.ny hs.ex hs.ey
      hs.bx hs.by_ hs.tx hs.ty hs.ne hdu hnu (hvu R') (by rw [← hfs]; exact hts) hk hta)
  · exact Or.inr (lin_step_side rq title forb hu' (hjd' R') hih' hs'.cs hs'.pos hs'.dst hs'.dx hs'.dy hs'.nx hs'.ny
      hs'.ex hs'.ey hs'.bx hs'.by_ hs'.tx hs'.ty hs'.ne hdu' hnu' (hvu' R') (by rw [← hcs, ← hfs]; exact hts) hk hta)

-- ============================================================
-- La estrella en el marco cruzado: la partición sin `JoinDownGen`
-- ============================================================

/-- **La estrella da la partición en el marco cruzado**: si en la unión de las copias de dos estados de la línea (de
nodos del mapa distintos) se cumplen `TopStarK`, `StarOrder` en las estrellas de cada lado y `TopsSep`, entonces
`TopUnion` entre las copias, para todo filtro: es decir, `LinIH u u'` directamente, sin `JoinDownGen` y sin
`LinIH` en el paso anterior. Medido en el marco cruzado (`test_3sat/probe_cross_star.jl`): las tres sin fallos. -/
theorem linIH_of_star {u u' : GPathB} (μ : PathNodeId → PathNodeId → Nat)
    (hcs : ∀ R', (u.filterAll R').current_step = (u'.filterAll R').current_step)
    (hle : ∀ R', LinksInv (u.filterAll R')) (hlg : ∀ R', LinksInv (u'.filterAll R'))
    (hee : ∀ R', EdgesAlive (u.filterAll R')) (heg : ∀ R', EdgesAlive (u'.filterAll R'))
    (hstar : ∀ R', TopStarK (join (u.filterAll R') (u'.filterAll R')))
    (hoe : ∀ R' t, t ∈ (u.filterAll R').alive → t ∉ (u'.filterAll R').alive →
      StarOrder (join (u.filterAll R') (u'.filterAll R')) (u.filterAll R') t μ)
    (hog : ∀ R' t, t ∈ (u'.filterAll R').alive → t ∉ (u.filterAll R').alive →
      StarOrder (join (u.filterAll R') (u'.filterAll R')) (u'.filterAll R') t μ)
    (hts : ∀ R', TopsSep (u.filterAll R') (u'.filterAll R')) : LinIH u u' :=
  fun R' => topUnion_of_order (hcs R') (hle R') (hlg R') (hee R') (heg R') (hstar R') μ (hoe R') (hog R') (hts R')

-- ============================================================
-- La inducción conjunta con `PinFree`
-- ============================================================

/-- **`LTU`**: en la unión `U` de la línea (un estado por nodo del mapa, `S k` el de la clave `k`), una cima del núcleo
fijado está en el núcleo de su propio estado, fijado igual. Es la partición por remitentes. -/
def LTU (S : NodeId → GPathB) (U : GPathB) : Prop :=
  ∀ (Q : List NodeId) (p : PathNodeId), p.id.step = U.current_step - 1 → Kernel U Q p p → Kernel (S p.id) Q p p

/-- **`PinFree`**: fijar por los requisitos de la fila de una cima no la mata en la unión. -/
def PinFree (U : GPathB) : Prop :=
  ∀ (Q : List NodeId) (t : PathNodeId), t.id.step = U.current_step - 1 → Kernel U Q t t → Kernel U (rq t.id ++ Q) t t

/-- **La bajada estructural** de la unión de un paso a la del anterior, ya con el pin de la fila: la cima es hija, en
la fila de su estado `t.id`, de un padre del núcleo de la unión anterior fijado igual (en la copia de su remitente).
Es monotonía: la estructura fijada con `rq t.id` concuerda con esos requisitos y baja por las filas nuevas. -/
def LineDown (S : NodeId → GPathB) (U U' : GPathB) : Prop :=
  ∀ (Q : List NodeId) (t : PathNodeId), t.id.step = U'.current_step - 1 → Kernel U' (rq t.id ++ Q) t t →
    ∃ p, p.id.step = U.current_step - 1 ∧ p ∈ ((S p.id).filterAll (rq t.id)).rowParents t.id t ∧
      t ∈ ((S p.id).filterAll (rq t.id)).newRowIds t.id forb ∧ Kernel U (rq t.id ++ Q) p p

/-- **La subida al estado siguiente** (monotonía): el UP de un remitente hacia `d` está dentro del estado `S' d`. -/
def LineUp (S S' : NodeId → GPathB) : Prop :=
  ∀ (k d : NodeId) (Q : List NodeId) (t : PathNodeId), Kernel (upL rq title forb (S k) d) Q t t → Kernel (S' d) Q t t

/-- **El paso de la inducción conjunta**: `LTU` en un paso da `LTU` en el siguiente, con `PinFree` en el siguiente y la
bajada y la subida estructurales. La estrella no hace falta en el paso: la partición entre remitentes la da la
hipótesis de inducción, y la elección de copia, `PinFree`. -/
theorem ltu_step {S S' : NodeId → GPathB} {U U' : GPathB}
    (hpos : ∀ k, 0 < (S k).current_step) (hst : ∀ k, (S k).current_step = U.current_step)
    (hdoc : ∀ k, AliveDocs (S k)) (hnd : ∀ k, NodupIds (S k)) (hte : ∀ k, TopExact (S k)) (hb : ∀ k, Below (S k))
    (hdst : ∀ (t : PathNodeId), t.id.step = U'.current_step - 1 → t.id.step = U.current_step)
    (hdown : LineDown rq forb S U U') (hup : LineUp rq title forb S S') (hpf : PinFree rq U')
    (hih : LTU S U) : LTU S' U' := by
  intro Q t hts hk
  obtain ⟨p, hps, hp, htn, hkp⟩ := hdown Q t hts (hpf Q t hts hk)
  have hk1 := hih (rq t.id ++ Q) p hps hkp
  have hk2 : Kernel ((S p.id).filterAll (rq t.id)) Q p p := (kernel_pin_list_iff (hdoc _) (hnd _) p p).mpr hk1
  have hfs : ((S p.id).filterAll (rq t.id)).current_step = U.current_step := by
    rw [(shrinks_filterAll _ _).1.step, hst]
  have hP : ∀ r ∈ Q, r.step = ((S p.id).filterAll (rq t.id)).current_step → r = t.id := by
    intro r hr hrs
    obtain ⟨V, R, hst', ha, hr'⟩ := hk
    exact (ha r hr (hst'.dom hr').1 (by rw [hdst t hts, hrs, hfs])).symm
  have hup' := kernel_up_of_parent (title := title) (topExact_filterAll (hte _) (hdoc _) (hnd _) _)
    (below_of_shrinks (shrinks_filterAll _ _) (hb _)) (by rw [(shrinks_filterAll _ _).1.step]; exact hpos _)
    (by rw [hfs]; exact hdst t hts) hp htn hP hk2
  exact hup p.id t.id Q t hup'

/-- **`PinFree` ⇐ `TopStarK`**: la estructura de la estrella de una cima vive en su propio estado (la cima solo posee
nodos de él) y ese estado concuerda con los requisitos de su fila. -/
theorem pinFree_of_topStar {S' : NodeId → GPathB} {U' : GPathB} (hs : TopStarK U')
    (hown : ∀ (t y : PathNodeId), t.id.step = U'.current_step - 1 → U'.Adj t y → y ∈ (S' t.id).alive)
    (hag : ∀ (d : NodeId), ∀ b ∈ rq d, ∀ q ∈ (S' d).alive, q.id.step = b.step → q.id = b) : PinFree rq U' := by
  intro Q t hts hk
  obtain ⟨V, R, hst, ha, hvt, hstar⟩ := hs Q t hts hk
  refine ⟨V, R, hst, fun b hb => ?_, hst.refl hvt⟩
  rcases List.mem_append.mp hb with hb | hb
  · intro q hq hqs
    exact hag t.id b hb q (hown t q hts (hstar q hq)) hqs
  · exact ha b hb

end GPathB

end AbsSatBingo.Model
