-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnSplit.lean
import AbsSatBingo.Model.ForbidOnBirth

/-!
# `Star4At` en el paso de los padres: un padre lo sostiene todo, o hay dos padres complementarios

`Star4At` pide, para cada tetraedro vivo `(t; x, y, z)` de la unión fijada `u` y cada paso, un nodo que lo complete.
En el paso de la cima y en los de `x`, `y`, `z` es trivial. Aquí se demuestra qué pasa en **el paso de los padres**
de `t`, sin hipótesis (`tetra_parent_or_split`), y sin usar que la base esté viva:

* o un padre `s` de `t` completa el tetraedro (`Wit4`),
* o `t` tiene dos padres distintos, `sf` y `sh`: `sf` es vecino de los cuatro, con todas sus caras vivas salvo una,
  `(p, q, sf)`, que está prohibida; y `sh` sostiene la cara `(t, p, q)` (`ParSplitAt`).

Es la misma forma que el nacimiento de `PrevCut` (`birth_pattern`), vista en la unión fijada: allí la base está muerta
en la llegada, aquí puede estar viva. Sale del punto fijo de la regla (cada cara con la cima tiene su testigo bueno en
el paso de los padres, `fix_witness`), de que esos testigos son padres de `t` (`AdjPar`), y del mismo palomar: el
color del abuelo de un padre es la clave de una entrada de dos líneas atrás (`unionParent_gparent`, por
`holder_gparent_mem`).

Consecuencia (`star4At_of_low_noSplit`): `Star4At` sale de su parte por debajo del paso de los padres
(`Star4LowAt`) y de que no haya dos padres complementarios sobre una base viva (`NoParSplitAt`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Driver Machine MachineOn

-- ============================================================
-- Los testigos del punto fijo, en el cierre simétrico
-- ============================================================

/-- **Un triángulo sin prohibir de la unión fijada tiene en cada paso un testigo bueno** (el punto fijo de la regla,
`trioGood_low`), escrito con el cierre simétrico de los tríos. -/
theorem fix_witness {J : GPathB} {Rp : List NodeId} (hJ : SInvB J) (hnsJ : NoSelf J) (hndJ : NoDegT J)
    (hv : (J.pinOn Rp).isValid = true) {p q w : PathNodeId} (hpq : (J.pinOn Rp).Adj p q)
    (hpw : (J.pinOn Rp).Adj p w) (hqw : (J.pinOn Rp).Adj q w) (npq : p ≠ q) (npw : p ≠ w) (nqw : q ≠ w)
    (hn : ¬ Sym (TF (J.pinOn Rp)) p q w) (l : Int) (h0 : 0 ≤ l) (h1 : l < J.current_step) :
    ∃ s, s.id.step = l ∧ (J.pinOn Rp).Adj p s ∧ (J.pinOn Rp).Adj q s ∧ (J.pinOn Rp).Adj w s ∧
      (s = p ∨ s = q ∨ s = w ∨ (¬ Sym (TF (J.pinOn Rp)) p q s ∧ ¬ Sym (TF (J.pinOn Rp)) p w s ∧
        ¬ Sym (TF (J.pinOn Rp)) q w s)) := by
  let u := J.pinOn Rp
  let c := J.current_step
  have hcsu : u.current_step = c := step_pinOn J Rp
  have hiu : SInvB u := sInvB_pinOn hJ Rp
  have hbs : ∀ q ∈ u.alive, q.id.step < c := fun q hq => by
    have := alive_below hiu.docs hiu.below hq; rw [hcsu] at this; exact this
  have hfix : FixClosed u := fixClosed_reviewOn (g := { Rp.foldl filterRequire J with dirty := true }) rfl hv
  have hTGu : TrioGood (LowV u c) (LowR u c) (TF u) c :=
    trioGood_low hfix (noDegT_pinOn hnsJ hndJ Rp) (by rw [hcsu]; exact Int.le_refl _)
  have low : ∀ {y w}, u.Adj y w → LowR u c y w := fun {y w} h =>
    ⟨⟨(hiu.edges y w h).1, (hiu.edges y w h).2, h⟩, hbs y (hiu.edges y w h).1, hbs w (hiu.edges y w h).2⟩
  have nsym : ∀ {a b r}, u.Adj a b → u.Adj a r → u.Adj b r → ¬ TF u a b r → ¬ Sym (TF u) a b r :=
    fun hab har hbr hn hs => hn (tF_of_sym hTGu (low hab) (low har) (low hbr) hs)
  obtain ⟨s, hsl, has, hbs', hrs, hw⟩ := hTGu.trio (low hpq) (low hpw) (low hqw) npq npw nqw
    (fun h => hn (Or.inl h)) l h0 h1
  refine ⟨s, hsl, has.1.2.2, hbs'.1.2.2, hrs.1.2.2, ?_⟩
  rcases hw with e | e | e | ⟨w1, w2, w3⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inr (Or.inr ⟨nsym hpq has.1.2.2 hbs'.1.2.2 w1, nsym hpw has.1.2.2 hrs.1.2.2 w2,
      nsym hqw hbs'.1.2.2 hrs.1.2.2 w3⟩))

-- ============================================================
-- Padres que sostienen caras, y los dos padres complementarios
-- ============================================================

/-- **El padre `s` de `t` sostiene la cara `(t, p, q)`** en `u`: es vecino de los tres y los tres tríos nuevos no
están prohibidos. -/
def FaceWit (u : GPathB) (t p q s : PathNodeId) : Prop :=
  s.id.step + 1 = t.id.step ∧ u.Adj t s ∧ u.Adj p s ∧ u.Adj q s ∧ ¬ Sym (TF u) p q s ∧ ¬ Sym (TF u) p t s ∧
    ¬ Sym (TF u) q t s

theorem faceWit_swap {u : GPathB} {t p q s : PathNodeId} (h : FaceWit u t p q s) : FaceWit u t q p s :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1, nsym_perm h.2.2.2.2.1 (by simp [perms]), h.2.2.2.2.2.2, h.2.2.2.2.2.1⟩

/-- **Dos padres complementarios**: `sf` sostiene las caras `(t, v, p)` y `(t, v, q)` y tiene prohibido el trío
`{p, q, sf}`; `sh`, otro padre, sostiene `(t, p, q)` y no completa el tetraedro. -/
def ParSplitAt (u : GPathB) (t v p q : PathNodeId) : Prop :=
  ∃ sf sh, sf ≠ sh ∧ FaceWit u t v p sf ∧ FaceWit u t v q sf ∧ Sym (TF u) p q sf ∧ FaceWit u t p q sh ∧
    ¬ Wit4 u t v p q sh

/-- Un padre que sostiene dos caras, y otro que sostiene la tercera: o uno de los dos completa el tetraedro, o son
dos padres complementarios. -/
theorem wit4_or_split {u : GPathB} {t v p q sf sh : PathNodeId} (h1 : FaceWit u t v p sf)
    (h2 : FaceWit u t v q sf) (h3 : FaceWit u t p q sh) :
    Wit4 u t v p q sf ∨ Wit4 u t v p q sh ∨ ParSplitAt u t v p q := by
  by_cases hd : Sym (TF u) p q sf
  · by_cases hw : Wit4 u t v p q sh
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr ⟨sf, sh, fun e => h3.2.2.2.2.1 (e ▸ hd), h1, h2, hd, h3, hw⟩)
  · exact Or.inl ⟨h1.2.1, h1.2.2.1, h1.2.2.2.1, h2.2.2.2.1, nsym_perm h1.2.2.2.2.2.1 (by simp [perms]),
      nsym_perm h1.2.2.2.2.2.2 (by simp [perms]), nsym_perm h2.2.2.2.2.2.2 (by simp [perms]), h1.2.2.2.2.1,
      h2.2.2.2.2.1, hd⟩

theorem wit4_swap12 {u : GPathB} {t x y z s : PathNodeId} (h : Wit4 u t y x z s) : Wit4 u t x y z s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
  exact ⟨a1, a3, a2, a4, a6, a5, a7, nsym_perm a8 (by simp [perms]), a10, a9⟩

theorem wit4_rot {u : GPathB} {t x y z s : PathNodeId} (h : Wit4 u t z x y s) : Wit4 u t x y z s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
  exact ⟨a1, a3, a4, a2, a6, a7, a5, a10, nsym_perm a8 (by simp [perms]), nsym_perm a9 (by simp [perms])⟩

-- ============================================================
-- El abuelo de un padre de una cima de la unión fijada
-- ============================================================

section Union

variable {φ : Cnf} {T : Int} {L0 : Line}

/-- **El color del abuelo de un padre de una cima de la unión fijada** que sostiene una cara `(p, q, s)` es la clave
de una entrada de dos líneas antes de los remitentes: el padre `s` es una cima de un remitente, de un solo lado de la
unión; la cara baja a ese lado (el join habría prohibido el triángulo) y de ahí al remitente. -/
theorem unionParent_gparent (hT : 1 ≤ T) (h0 : LInvTop φ T L0) (hbk0 : LineBk L0)
    (h1 : LInvTop φ (T + 1) (advanceM .on φ L0)) (hbk1 : LineBk (advanceM .on φ L0))
    (h2 : LInvTop φ (T + 1 + 1) (advanceM .on φ (advanceM .on φ L0)))
    (hbk2 : LineBk (advanceM .on φ (advanceM .on φ L0)))
    {a b : NodeId × GPathB} (ha : a ∈ advanceM .on φ (advanceM .on φ L0))
    (hb : b ∈ advanceM .on φ (advanceM .on φ L0)) (hab : a.1 ≠ b.1) {d : NodeId} (hsa : SendsOn φ a d)
    (hsb : SendsOn φ b d) {R : List NodeId} {s p q : PathNodeId} (hss : s.id.step = T + 1)
    (hp : p.id.step < T + 1) (hq : q.id.step < T + 1) (npq : p ≠ q)
    (hsp : ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj s p)
    (hsq : ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj s q)
    (hpq : ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj p q)
    (hn : ¬ Sym (TF ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R)) p q s) :
    ∃ E ∈ L0, s.gparent_id = some E.1 := by
  have hT2 : (1 : Int) ≤ T + 1 + 1 := by omega
  obtain ⟨ea, ia, _, _, _⟩ := arrTop_facts hT2 h2 ha hsa
  obtain ⟨eb, ib, _, _, _⟩ := arrTop_facts hT2 h2 hb hsb
  have hsub := sub_pinOn (joinOn (arrOn φ a d) (arrOn φ b d)) R
  have hJ : SInvB (joinOn (arrOn φ a d) (arrOn φ b d)) := sInvB_joinOn ia ib (ea.1.step.trans eb.1.step.symm)
  obtain ⟨T', hT'e⟩ := joinOn_eq (arrOn φ a d) (arrOn φ b d)
  have hadj : ∀ x w, (joinOn (arrOn φ a d) (arrOn φ b d)).Adj x w →
      (arrOn φ a d).Adj x w ∨ (arrOn φ b d).Adj x w := fun x w h => by
    rw [hT'e] at h; exact adj_join_cases h
  have jsp := hsub.adj _ _ hsp
  have jsq := hsub.adj _ _ hsq
  have jpq := hsub.adj _ _ hpq
  have hnJ : ¬ TF (joinOn (arrOn φ a d) (arrOn φ b d)) s p q := fun hf =>
    hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (tF_mono (trios_grow_pinOn _ R) hsp hf))))))
  have hsJ : s ∈ (joinOn (arrOn φ a d) (arrOn φ b d)).alive := (hJ.edges s p jsp).1
  have halive : s ∈ (arrOn φ a d).alive ∨ s ∈ (arrOn φ b d).alive := by
    rw [hT'e] at hsJ; exact (alive_join _ _ s).mp hsJ
  have nsp : s ≠ p := fun e => by rw [← e, hss] at hp; omega
  have nsq : s ≠ q := fun e => by rw [← e, hss] at hq; omega
  -- la clave de un remitente que tiene a `s`
  have keyOf : ∀ kv ∈ advanceM .on φ (advanceM .on φ L0), s ∈ kv.2.alive → s.id = kv.1 := by
    intro kv hkv hs
    obtain ⟨n, hn', hnid⟩ := (h2.inv kv hkv).docs s hs
    have := (hbk2 kv hkv).1 n hn' (by rw [hnid, (h2.on kv hkv).1.step, hss]; omega)
    rw [hnid] at this
    exact this
  -- el lado de `s`, con el otro lado sin `s`
  have side : ∀ kv ∈ advanceM .on φ (advanceM .on φ L0), ∀ ko ∈ advanceM .on φ (advanceM .on φ L0),
      kv.1 ≠ ko.1 → ∀ (hsv : SendsOn φ kv d) (hso : SendsOn φ ko d), EdgesAlive (arrOn φ ko d) →
      s ∈ (arrOn φ kv d).alive →
      (∀ x w, (joinOn (arrOn φ a d) (arrOn φ b d)).Adj x w → (arrOn φ kv d).Adj x w ∨ (arrOn φ ko d).Adj x w) →
      (SideForbids (arrOn φ kv d) (TF (arrOn φ kv d)) s p q → SideForbids (arrOn φ ko d) (TF (arrOn φ ko d)) s p q →
        TF (joinOn (arrOn φ a d) (arrOn φ b d)) s p q) →
      ∃ E ∈ L0, s.gparent_id = some E.1 := by
    intro kv hkv ko hko hne hsv hso heO hsS hadj' hcut
    have hentv := h2.on kv hkv
    have hsv' : s ∈ kv.2.alive := arrOn_alive_old hentv (h2.inv kv hkv) hsv (by omega) hsS
    have sO : s ∉ (arrOn φ ko d).alive := fun hs' =>
      hne ((keyOf kv hkv hsv').symm.trans
        (keyOf ko hko (arrOn_alive_old (h2.on ko hko) (h2.inv ko hko) hso (by omega) hs')))
    have noO : ¬ ((arrOn φ ko d).Adj s p ∧ (arrOn φ ko d).Adj s q ∧ (arrOn φ ko d).Adj p q) :=
      fun hh => sO (heO s p hh.1).1
    have ssp := (hadj' s p jsp).resolve_right (fun ho => sO (heO s p ho).1)
    have ssq := (hadj' s q jsq).resolve_right (fun ho => sO (heO s q ho).1)
    have spq : (arrOn φ kv d).Adj p q := by
      apply Classical.byContradiction
      intro hno
      exact hnJ (hcut (Or.inl fun hh => hno hh.2.2) (Or.inl noO))
    have hnS : ¬ TF (arrOn φ kv d) s p q := fun hf => hnJ (hcut (Or.inr hf) (Or.inl noO))
    have ksp := arrOn_adj_old hentv hsv (by omega) (by omega) ssp
    have ksq := arrOn_adj_old hentv hsv (by omega) (by omega) ssq
    have kpq := arrOn_adj_old hentv hsv (by omega) (by omega) spq
    have unl : ∀ τ ∈ kv.2.trios, trioIs s p q τ = false := by
      intro τ hτ
      cases hc : trioIs s p q τ
      · rfl
      · exfalso
        apply hnS
        exact tF_mono (g := kv.2) (h := (kv.2.filterAllOn (reqOf φ d)).upOn d "" (isProhibited φ))
          (fun t ht => trios_grow_upOn _ d "" (isProhibited φ) t (trios_grow_filterAllOn kv.2 (reqOf φ d) t ht))
          ssp (tF_of_trioIs ksp nsp hτ hc)
    exact holder_gparent_mem hT h0 hbk0 h1 hbk1 hkv hsv' (by rw [hentv.1.step, hss]; omega) hp hq npq ksp ksq kpq unl
  rcases halive with hs | hs
  · exact side a ha b hb hab hsa hsb ib.edges hs hadj
      (fun c1 c2 => tF_joinOn_of_cut ia.edges ib.edges jsp jsq jpq nsp nsq npq c1 c2)
  · exact side b hb a ha (Ne.symm hab) hsb hsa ia.edges hs (fun x w h => (hadj x w h).symm)
      (fun c2 c1 => tF_joinOn_of_cut ia.edges ib.edges jsp jsq jpq nsp nsq npq c1 c2)

/-- **El tetraedro en el paso de los padres.** En la unión fijada de dos llegadas, un tetraedro `(t; x, y, z)` con
cima `t` y sus tres nodos por debajo del paso de los padres: o un padre de `t` lo completa, o `t` tiene dos padres
complementarios, con alguno de los tres nodos en el papel de `v`. No usa que la base esté viva. -/
theorem tetra_parent_or_split (hT : 1 ≤ T) (h0 : LInvTop φ T L0) (hbk0 : LineBk L0)
    (h1 : LInvTop φ (T + 1) (advanceM .on φ L0)) (hbk1 : LineBk (advanceM .on φ L0))
    (h2 : LInvTop φ (T + 1 + 1) (advanceM .on φ (advanceM .on φ L0)))
    (hbk2 : LineBk (advanceM .on φ (advanceM .on φ L0)))
    {a b : NodeId × GPathB} (ha : a ∈ advanceM .on φ (advanceM .on φ L0))
    (hb : b ∈ advanceM .on φ (advanceM .on φ L0)) (hab : a.1 ≠ b.1) {d : NodeId} (hsa : SendsOn φ a d)
    (hsb : SendsOn φ b d) {R : List NodeId}
    (hv : ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).isValid = true) {t x y z : PathNodeId}
    (hts : t.id.step = (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 1)
    (htet : Tetra ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t x y z)
    (hx : x.id.step < T + 1) (hy : y.id.step < T + 1) (hz : z.id.step < T + 1) :
    (∃ s, s.id.step + 1 = t.id.step ∧ Wit4 ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t x y z s) ∨
    ParSplitAt ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t x y z ∨
    ParSplitAt ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t y x z ∨
    ParSplitAt ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t z x y := by
  have hT2 : (1 : Int) ≤ T + 1 + 1 := by omega
  obtain ⟨ea, ia, na, _, _⟩ := arrTop_facts hT2 h2 ha hsa
  obtain ⟨eb, ib, nb, _, _⟩ := arrTop_facts hT2 h2 hb hsb
  have hcs : (arrOn φ a d).current_step = (arrOn φ b d).current_step := ea.1.step.trans eb.1.step.symm
  have hJ : SInvB (joinOn (arrOn φ a d) (arrOn φ b d)) := sInvB_joinOn ia ib hcs
  have hnsJ : NoSelf (joinOn (arrOn φ a d) (arrOn φ b d)) := noSelf_joinOn ea.2.1 eb.2.1
  have hndJ : NoDegT (joinOn (arrOn φ a d) (arrOn φ b d)) := noDegT_joinOn ea.2.1 eb.2.1 ia.edges ib.edges
  have hcsJ : (joinOn (arrOn φ a d) (arrOn φ b d)).current_step = T + 1 + 1 + 1 := by
    rw [step_joinOn]; exact ea.1.step
  have htT : t.id.step = T + 1 + 1 := by rw [hts, hcsJ]; omega
  -- `AdjPar` de la unión fijada
  obtain ⟨pa, _⟩ := arrOn_adjPar (h2.on a ha) (h2.inv a ha) (hbk2 a ha).2.1 (hbk2 a ha).2.2 hsa
  obtain ⟨pb, _⟩ := arrOn_adjPar (h2.on b hb) (h2.inv b hb) (hbk2 b hb).2.1 (hbk2 b hb).2.2 hsb
  obtain ⟨T', hT'e⟩ := joinOn_eq (arrOn φ a d) (arrOn φ b d)
  have hapJ : AdjPar (joinOn (arrOn φ a d) (arrOn φ b d)) := by
    rw [hT'e]; exact adjPar_setT (adjPar_join pa pb) T'
  have hapu := adjPar_of_sub (sub_pinOn (joinOn (arrOn φ a d) (arrOn φ b d)) R) hapJ
  obtain ⟨nxt, nyt, nzt, nxy, nxz, nyz, htx, hty, htz, hxy, hxz, hyz, f1, f2, f3⟩ := htet
  have usymm : ∀ {y w}, ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj y w →
      ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj w y := fun h => (adj_symm _ _ _).mp h
  -- el testigo de una cara con la cima, en el paso de los padres
  have wit : ∀ {p q : PathNodeId}, p.id.step < T + 1 → q.id.step < T + 1 → p ≠ q → p ≠ t → q ≠ t →
      ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj p q →
      ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj t p →
      ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj t q →
      ¬ Sym (TF ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R)) p q t →
      ∃ s, FaceWit ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t p q s ∧ ∃ E ∈ L0, s.gparent_id = some E.1 := by
    intro p q hp hq npq npt nqt hpq htp htq hf
    obtain ⟨s, hsl, hps, hqs, hts', hw⟩ := fix_witness hJ hnsJ hndJ hv hpq (usymm htp) (usymm htq) npq npt nqt hf
      (t.id.step - 1) (by omega) (by rw [hcsJ]; omega)
    have hw' : ¬ Sym (TF ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R)) p q s ∧
        ¬ Sym (TF ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R)) p t s ∧
        ¬ Sym (TF ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R)) q t s := by
      rcases hw with e | e | e | hw
      · rw [e] at hsl; omega
      · rw [e] at hsl; omega
      · rw [e] at hsl; omega
      · exact hw
    exact ⟨s, ⟨by omega, hts', hps, hqs, hw'.1, hw'.2.1, hw'.2.2⟩,
      unionParent_gparent hT h0 hbk0 h1 hbk1 h2 hbk2 ha hb hab hsa hsb (by omega) hp hq npq (usymm hps) (usymm hqs)
        hpq hw'.1⟩
  obtain ⟨s1, w1, E1, m1, g1⟩ := wit hx hy nxy nxt nyt hxy htx hty f1
  obtain ⟨s2, w2, E2, m2, g2⟩ := wit hx hz nxz nxt nzt hxz htx htz f2
  obtain ⟨s3, w3, E3, m3, g3⟩ := wit hy hz nyz nyt nzt hyz hty htz f3
  -- dos padres con el mismo abuelo son el mismo nodo
  have same : ∀ {s s' p q p' q' : PathNodeId} {E E' : NodeId × GPathB},
      FaceWit ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t p q s →
      FaceWit ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t p' q' s' → s.gparent_id = some E.1 →
      s'.gparent_id = some E'.1 → E = E' → s = s' := by
    intro s s' p q p' q' E E' hs hs' gs gs' e
    have c := hapu t s hs.2.1 hs.1
    have c' := hapu t s' hs'.2.1 hs'.1
    refine pid_ext (Option.some.inj (c.1.symm.trans c'.1)) (c.2.1.symm.trans c'.2.1) ?_
    rw [gs, gs', e]
  rcases pigeon3 (line_cases h0.nodup h0.keys) m1 m2 m3 with e | e | e
  · have e' := same w1 w2 g1 g2 e
    subst e'
    rcases wit4_or_split w1 w2 w3 with hw | hw | hsp
    · exact Or.inl ⟨s1, w1.1, hw⟩
    · exact Or.inl ⟨s3, w3.1, hw⟩
    · exact Or.inr (Or.inl hsp)
  · have e' := same w1 w3 g1 g3 e
    subst e'
    rcases wit4_or_split (faceWit_swap w1) w3 w2 with hw | hw | hsp
    · exact Or.inl ⟨s1, w1.1, wit4_swap12 hw⟩
    · exact Or.inl ⟨s2, w2.1, wit4_swap12 hw⟩
    · exact Or.inr (Or.inr (Or.inl hsp))
  · have e' := same w2 w3 g2 g3 e
    subst e'
    rcases wit4_or_split (faceWit_swap w2) (faceWit_swap w3) w1 with hw | hw | hsp
    · exact Or.inl ⟨s2, w2.1, wit4_rot hw⟩
    · exact Or.inl ⟨s1, w1.1, wit4_rot hw⟩
    · exact Or.inr (Or.inr (Or.inr hsp))

end Union

-- ============================================================
-- `Star4At` por debajo del paso de los padres, y sin padres complementarios
-- ============================================================

/-- **`Star4At` por debajo del paso de los padres** de la cima. -/
def Star4LowAt (J : GPathB) (Rp : List NodeId) : Prop :=
  (J.pinOn Rp).isValid = true → ∀ t ∈ (J.pinOn Rp).alive, t.id.step = J.current_step - 1 →
    ∀ a b r, Tetra (J.pinOn Rp) t a b r → ¬ Sym (TF (J.pinOn Rp)) a b r → ∀ l, 0 ≤ l → l < J.current_step - 2 →
      ∃ s, s.id.step = l ∧ (s = a ∨ s = b ∨ s = r ∨ s = t ∨ Wit4 (J.pinOn Rp) t a b r s)

/-- **Sin padres complementarios sobre una base viva**: un tetraedro vivo de la unión fijada, con sus tres nodos por
debajo del paso de los padres, no tiene dos padres complementarios, con ninguno de los tres en el papel de `v`. -/
def NoParSplitAt (J : GPathB) (Rp : List NodeId) : Prop :=
  (J.pinOn Rp).isValid = true → ∀ t ∈ (J.pinOn Rp).alive, t.id.step = J.current_step - 1 →
    ∀ a b r, Tetra (J.pinOn Rp) t a b r → ¬ Sym (TF (J.pinOn Rp)) a b r →
      a.id.step < J.current_step - 2 → b.id.step < J.current_step - 2 → r.id.step < J.current_step - 2 →
      ¬ ParSplitAt (J.pinOn Rp) t a b r ∧ ¬ ParSplitAt (J.pinOn Rp) t b a r ∧ ¬ ParSplitAt (J.pinOn Rp) t r a b

/-- **`Star4At` sale de su parte baja y de que no haya padres complementarios sobre bases vivas.** -/
theorem star4At_of_low_noSplit {φ : Cnf} {T : Int} {L0 : Line} (hT : 1 ≤ T) (h0 : LInvTop φ T L0)
    (hbk0 : LineBk L0) (h1 : LInvTop φ (T + 1) (advanceM .on φ L0)) (hbk1 : LineBk (advanceM .on φ L0))
    (h2 : LInvTop φ (T + 1 + 1) (advanceM .on φ (advanceM .on φ L0)))
    (hbk2 : LineBk (advanceM .on φ (advanceM .on φ L0)))
    {a b : NodeId × GPathB} (ha : a ∈ advanceM .on φ (advanceM .on φ L0))
    (hb : b ∈ advanceM .on φ (advanceM .on φ L0)) (hab : a.1 ≠ b.1) {d : NodeId} (hsa : SendsOn φ a d)
    (hsb : SendsOn φ b d) {R : List NodeId} (hlow : Star4LowAt (joinOn (arrOn φ a d) (arrOn φ b d)) R)
    (hns : NoParSplitAt (joinOn (arrOn φ a d) (arrOn φ b d)) R) : Star4At (joinOn (arrOn φ a d) (arrOn φ b d)) R := by
  intro hv t ht hts x y z htet hbase l h0' h1'
  obtain ⟨ea, _⟩ := arrTop_facts (by omega : (1 : Int) ≤ T + 1 + 1) h2 ha hsa
  have hcsJ : (joinOn (arrOn φ a d) (arrOn φ b d)).current_step = T + 1 + 1 + 1 := by
    rw [step_joinOn]; exact ea.1.step
  by_cases hl : l < (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 2
  · exact hlow hv t ht hts x y z htet hbase l h0' hl
  by_cases hlt : l = (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 1
  · exact ⟨t, by rw [hts, hlt], Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  have hlp : l = T + 1 := by omega
  -- el paso de los padres
  by_cases cx : x.id.step = l
  · exact ⟨x, cx, Or.inl rfl⟩
  by_cases cy : y.id.step = l
  · exact ⟨y, cy, Or.inr (Or.inl rfl)⟩
  by_cases cz : z.id.step = l
  · exact ⟨z, cz, Or.inr (Or.inr (Or.inl rfl))⟩
  -- los vecinos de la cima están por debajo de ella
  have hiu := sInvB_pinOn (sInvB_joinOn (arrTop_facts (by omega : (1 : Int) ≤ T + 1 + 1) h2 ha hsa).2.1
    (arrTop_facts (by omega : (1 : Int) ≤ T + 1 + 1) h2 hb hsb).2.1
    (ea.1.step.trans (arrTop_facts (by omega : (1 : Int) ≤ T + 1 + 1) h2 hb hsb).1.1.step.symm)) R
  obtain ⟨_, ta⟩ := arrOn_adjPar (h2.on a ha) (h2.inv a ha) (hbk2 a ha).2.1 (hbk2 a ha).2.2 hsa
  obtain ⟨_, tb⟩ := arrOn_adjPar (h2.on b hb) (h2.inv b hb) (hbk2 b hb).2.1 (hbk2 b hb).2.2 hsb
  obtain ⟨T', hT'e⟩ := joinOn_eq (arrOn φ a d) (arrOn φ b d)
  have htaJ : TopsApart (joinOn (arrOn φ a d) (arrOn φ b d)) := by
    rw [hT'e]
    exact topsApart_setT (topsApart_join ta tb
      (ea.1.step.trans (arrTop_facts (by omega : (1 : Int) ≤ T + 1 + 1) h2 hb hsb).1.1.step.symm)) T'
  have below : ∀ {q : PathNodeId}, ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj t q → q ≠ t →
      q.id.step ≠ l → q.id.step < T + 1 := by
    intro q hq hne hql
    have hb1 := alive_below hiu.docs hiu.below (hiu.edges t q hq).2
    rw [step_pinOn, hcsJ] at hb1
    have hb2 : q.id.step ≠ (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 1 := fun e =>
      hne (htaJ t q hts e ((sub_pinOn _ R).adj _ _ hq)).symm
    rw [hcsJ] at hb2
    omega
  have htet' := htet
  obtain ⟨nxt, nyt, nzt, _, _, _, htx, hty, htz, _⟩ := htet
  obtain ⟨n1, n2, n3⟩ := hns hv t ht hts x y z htet' hbase (by have := below htx nxt cx; rw [hcsJ]; omega)
    (by have := below hty nyt cy; rw [hcsJ]; omega) (by have := below htz nzt cz; rw [hcsJ]; omega)
  rcases tetra_parent_or_split hT h0 hbk0 h1 hbk1 h2 hbk2 ha hb hab hsa hsb hv hts htet' (below htx nxt cx)
    (below hty nyt cy) (below htz nzt cz) with ⟨s, hs, hw⟩ | hsp | hsp | hsp
  · exact ⟨s, by rw [hts, hcsJ] at hs; omega, Or.inr (Or.inr (Or.inr (Or.inr hw)))⟩
  · exact absurd hsp n1
  · exact absurd hsp n2
  · exact absurd hsp n3

/-- **Recíproco**: `Star4At` excluye los padres complementarios sobre bases vivas. El nodo que completa el tetraedro en
el paso de los padres es un padre de `t`, y `t` no tiene más padres que `sf` y `sh` (el mismo palomar): `sf` tiene una
cara prohibida y `sh` no lo completa. Así `NoParSplitAt` queda medida por las medidas de `Star4At`. -/
theorem noParSplit_of_star4 {φ : Cnf} {T : Int} {L0 : Line} (hT : 1 ≤ T) (h0 : LInvTop φ T L0)
    (hbk0 : LineBk L0) (h1 : LInvTop φ (T + 1) (advanceM .on φ L0)) (hbk1 : LineBk (advanceM .on φ L0))
    (h2 : LInvTop φ (T + 1 + 1) (advanceM .on φ (advanceM .on φ L0)))
    (hbk2 : LineBk (advanceM .on φ (advanceM .on φ L0)))
    {a b : NodeId × GPathB} (ha : a ∈ advanceM .on φ (advanceM .on φ L0))
    (hb : b ∈ advanceM .on φ (advanceM .on φ L0)) (hab : a.1 ≠ b.1) {d : NodeId} (hsa : SendsOn φ a d)
    (hsb : SendsOn φ b d) {R : List NodeId} (h4 : Star4At (joinOn (arrOn φ a d) (arrOn φ b d)) R) :
    NoParSplitAt (joinOn (arrOn φ a d) (arrOn φ b d)) R := by
  intro hv t ht hts x y z htet hbase hx hy hz
  have hT2 : (1 : Int) ≤ T + 1 + 1 := by omega
  obtain ⟨ea, _⟩ := arrTop_facts hT2 h2 ha hsa
  have hcsJ : (joinOn (arrOn φ a d) (arrOn φ b d)).current_step = T + 1 + 1 + 1 := by
    rw [step_joinOn]; exact ea.1.step
  rw [hcsJ] at hx hy hz
  have hx : x.id.step < T + 1 := by omega
  have hy : y.id.step < T + 1 := by omega
  have hz : z.id.step < T + 1 := by omega
  have htT : t.id.step = T + 1 + 1 := by rw [hts, hcsJ]; omega
  -- `AdjPar` de la unión fijada
  obtain ⟨pa, _⟩ := arrOn_adjPar (h2.on a ha) (h2.inv a ha) (hbk2 a ha).2.1 (hbk2 a ha).2.2 hsa
  obtain ⟨pb, _⟩ := arrOn_adjPar (h2.on b hb) (h2.inv b hb) (hbk2 b hb).2.1 (hbk2 b hb).2.2 hsb
  obtain ⟨T', hT'e⟩ := joinOn_eq (arrOn φ a d) (arrOn φ b d)
  have hapJ : AdjPar (joinOn (arrOn φ a d) (arrOn φ b d)) := by
    rw [hT'e]; exact adjPar_setT (adjPar_join pa pb) T'
  have hapu := adjPar_of_sub (sub_pinOn (joinOn (arrOn φ a d) (arrOn φ b d)) R) hapJ
  have usymm : ∀ {y w}, ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj y w →
      ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj w y := fun h => (adj_symm _ _ _).mp h
  -- el nodo que completa el tetraedro en el paso de los padres
  obtain ⟨s, hsl, hs⟩ := h4 hv t ht hts x y z htet hbase (T + 1) (by omega) (by rw [hcsJ]; omega)
  have hw : Wit4 ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t x y z s := by
    rcases hs with e | e | e | e | hw
    · rw [e] at hsl; omega
    · rw [e] at hsl; omega
    · rw [e] at hsl; omega
    · rw [e] at hsl; omega
    · exact hw
  obtain ⟨_, _, _, nxy, nxz, nyz, _, _, _, hxy, hxz, hyz, _⟩ := htet
  -- con los papeles repartidos: `s` es `sf` o `sh`, y ninguno de los dos completa el tetraedro
  have role : ∀ {v p q : PathNodeId}, v.id.step < T + 1 → p.id.step < T + 1 → q.id.step < T + 1 → v ≠ p → p ≠ q →
      ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj v p →
      ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj p q →
      Wit4 ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t v p q s →
      ¬ ParSplitAt ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t v p q := by
    intro v p q hv' hp hq nvp npq avp apq ⟨a1, a2, a3, _, _, _, _, a8, _, a10⟩ ⟨sf, sh, nfh, f1, _, hdead, f3, hnw⟩
    have key := @unionParent_gparent φ T L0 hT h0 hbk0 h1 hbk1 h2 hbk2 a b ha hb hab d hsa hsb R
    obtain ⟨Es, ms, gs⟩ := key (s := s) (by omega) hv' hp nvp (usymm a2) (usymm a3) avp a8
    obtain ⟨Ef, mf, gf⟩ := key (s := sf) (by have := f1.1; omega) hv' hp nvp (usymm f1.2.2.1) (usymm f1.2.2.2.1) avp
      f1.2.2.2.2.1
    obtain ⟨Eh, mh, gh⟩ := key (s := sh) (by have := f3.1; omega) hp hq npq (usymm f3.2.2.1) (usymm f3.2.2.2.1) apq
      f3.2.2.2.2.1
    have cs := hapu t s a1 (by omega)
    have cf := hapu t sf f1.2.1 f1.1
    have ch := hapu t sh f3.2.1 f3.1
    have eq : ∀ {p q : PathNodeId} {E E' : NodeId × GPathB}, Compat p t → Compat q t → p.gparent_id = some E.1 →
        q.gparent_id = some E'.1 → E = E' → p = q := fun c c' g g' e =>
      pid_ext (Option.some.inj (c.1.symm.trans c'.1)) (c.2.1.symm.trans c'.2.1) (by rw [g, g', e])
    rcases pigeon3 (line_cases h0.nodup h0.keys) ms mf mh with e | e | e
    · have e' := eq cs cf gs gf e
      subst e'
      exact a10 hdead
    · have e' := eq cs ch gs gh e
      subst e'
      exact hnw ⟨a1, a2, a3, by assumption, by assumption, by assumption, by assumption, a8, by assumption, a10⟩
    · exact nfh (eq cf ch gf gh e)
  refine ⟨role hx hy hz nxy nyz hxy hyz hw, ?_, ?_⟩
  · exact role hy hx hz (Ne.symm nxy) nxz (usymm hxy) hxz (wit4_swap12 hw)
  · exact role hz hx hy (Ne.symm nxz) nxy (usymm hxz) hxy (wit4_rot (wit4_rot hw))

end GPathB

end AbsSatBingo.Model
