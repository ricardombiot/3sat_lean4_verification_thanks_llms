-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnFam.lean
import AbsSatBingo.Model.ForbidOnStarD

/-!
# Qué dice de verdad la primera hipótesis de `star_coreD`

`star_coreD` pide (`hface`) que cada cara viva `(a, b, t)` de la unión fijada `u` tenga en cada paso un testigo bueno
`s` de `u` cuyo trío `(a, b, s)` no esté prohibido en el lado `S`. Aquí se demuestra que eso es lo mismo que decir
que **las caras de la cima viven en su lado fijado** `P = pinOn S R`:

* `star_coreD_fam`: bajo las dos hipótesis de `star_coreD`, cada cara viva de `u` con la cima es un triángulo sin
  prohibir de `P` (es lo que la prueba de `star_coreD` demuestra por dentro);
* `hface_of_sideFace`: si la cara es un triángulo sin prohibir de `P`, el punto fijo de la regla **en `P`** da el
  testigo: `P` vive entero en `u` (`downInv_joinOn_left/right`, sin hipótesis), así que el testigo de `P` es un
  testigo de `u`, y un trío sin prohibir en `P` no lo está en `S`.

Los únicos testigos que se saben construir son los de un punto fijo: el de `u` no dice nada de los tríos de `S`, y el
de `P` solo existe si la cara ya vive en `P`. Así que la hipótesis `hface` no se puede debilitar por este camino: es,
dada la de las bases, equivalente a «las caras de la cima viven en su lado fijado», que es más fuerte que la
conclusión que se busca (`TopSideAt`: la cima vive en su lado fijado). Es medible directamente, sin testigos ni
pasos (`probe_topdead.jl`, `sf_fail`).

Además: en la primera línea no hay joins (`hStarDOn_init`), así que la primera parte de `HypsStarDLowOn` sobra
(`hypsStarDLowOn_of_tail`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Driver Machine MachineOn

/-- **El núcleo, con la familia**: bajo las hipótesis de `star_coreD`, además de la cima, **cada cara viva `(a, b, t)`
de la unión fijada es un triángulo sin prohibir del lado fijado**. -/
theorem star_coreD_fam {J S O : GPathB} {Rp : List NodeId} (hJ : SInvB J) (hnsJ : NoSelf J) (hndJ : NoDegT J)
    (hc2 : 2 ≤ J.current_step) (hv : (J.pinOn Rp).isValid = true) (hS : SInvB S) (hnsS : NoSelf S)
    (hndS : NoDegT S) (hcs : J.current_step = S.current_step) (hap : AdjPar S)
    (hadj : ∀ x w, J.Adj x w → S.Adj x w ∨ O.Adj x w) (heO : EdgesAlive O)
    (hcut : ∀ {x y z}, J.Adj x y → J.Adj x z → J.Adj y z → x ≠ y → x ≠ z → y ≠ z → SideForbids S (TF S) x y z →
      ¬ (O.Adj x y ∧ O.Adj x z ∧ O.Adj y z) → TF J x y z)
    {t : PathNodeId} (ht : t ∈ (J.pinOn Rp).alive) (htO : t ∉ O.alive)
    (hface : ∀ a b, a ≠ t → b ≠ t → a ≠ b → (J.pinOn Rp).Adj t a → (J.pinOn Rp).Adj t b → (J.pinOn Rp).Adj a b →
      ¬ Sym (TF (J.pinOn Rp)) a b t → ∀ l, 0 ≤ l → l < J.current_step →
      ∃ s, s.id.step = l ∧ (J.pinOn Rp).Adj a s ∧ (J.pinOn Rp).Adj b s ∧ (J.pinOn Rp).Adj t s ∧
        (s = a ∨ s = b ∨ s = t ∨ (¬ Sym (TF (J.pinOn Rp)) a b s ∧ ¬ Sym (TF (J.pinOn Rp)) a t s ∧
          ¬ Sym (TF (J.pinOn Rp)) b t s ∧ ¬ Sym (TF S) a b s)))
    (hbase : ∀ a b r, Tetra (J.pinOn Rp) t a b r → ¬ Sym (TF (J.pinOn Rp)) a b r → ¬ Sym (TF S) a b r →
      (∀ τ ∈ (S.pinOn Rp).trios, trioIs a b r τ = false) ∨
      (∀ l, 0 ≤ l → l < J.current_step →
        ∃ s, s.id.step = l ∧ (s = a ∨ s = b ∨ s = r ∨ s = t ∨ (Wit4 (J.pinOn Rp) t a b r s ∧
          ¬ Sym (TF S) a b s ∧ ¬ Sym (TF S) a r s ∧ ¬ Sym (TF S) b r s)))) :
    (S.pinOn Rp).isValid = true ∧ t ∈ (S.pinOn Rp).alive ∧
    ∀ a b, a ≠ t → b ≠ t → a ≠ b → (J.pinOn Rp).Adj t a → (J.pinOn Rp).Adj t b → (J.pinOn Rp).Adj a b →
      ¬ Sym (TF (J.pinOn Rp)) a b t →
      (S.pinOn Rp).Adj t a ∧ (S.pinOn Rp).Adj t b ∧ (S.pinOn Rp).Adj a b ∧ ¬ Sym (TF (S.pinOn Rp)) a b t := by
  let u := J.pinOn Rp
  let c := J.current_step
  have hcsu : u.current_step = c := step_pinOn J Rp
  have hiu : SInvB u := sInvB_pinOn hJ Rp
  have hbs : ∀ q ∈ u.alive, q.id.step < c := fun q hq => by
    have := alive_below hiu.docs hiu.below hq; rw [hcsu] at this; exact this
  have hcl : ClosedState u := closedState_pinOn hJ hv hc2
  have hfix : FixClosed u := fixClosed_reviewOn (g := { Rp.foldl filterRequire J with dirty := true }) rfl hv
  have hTGu : TrioGood (LowV u c) (LowR u c) (TF u) c :=
    trioGood_low hfix (noDegT_pinOn hnsJ hndJ Rp) (by rw [hcsu]; exact Int.le_refl _)
  have hsub : Sub u J := sub_pinOn J Rp
  have low : ∀ {y w}, u.Adj y w → LowR u c y w := fun {y w} h =>
    ⟨⟨(hiu.edges y w h).1, (hiu.edges y w h).2, h⟩, hbs y (hiu.edges y w h).1, hbs w (hiu.edges y w h).2⟩
  have usymm : ∀ {y w}, u.Adj y w → u.Adj w y := fun h => (adj_symm u _ _).mp h
  -- un trío sin prohibir en `u`, en su cierre simétrico
  have nsym : ∀ {a b r}, u.Adj a b → u.Adj a r → u.Adj b r → ¬ TF u a b r → ¬ Sym (TF u) a b r :=
    fun hab har hbr hn hs => hn (tF_of_sym hTGu (low hab) (low har) (low hbr) hs)
  -- una arista de `u` con un extremo fuera de `O` es de `S`
  have key : ∀ a b, u.Adj a b → a ∉ O.alive → S.Adj a b := fun a b h hn =>
    (hadj a b (hsub.adj _ _ h)).resolve_right (fun ho => hn (heO a b ho).1)
  -- la familia
  let V : PathNodeId → Prop := fun y => u.Adj t y
  let Rr : PathNodeId → PathNodeId → Prop := fun y w =>
    u.Adj t y ∧ u.Adj t w ∧ u.Adj y w ∧ (y = w ∨ y = t ∨ w = t ∨ ¬ Sym (TF u) y w t)
  let T : Trios := fun a b r => Sym (TF u) a b r ∨ (a ≠ t ∧ b ≠ t ∧ r ≠ t ∧ Sym (TF S) a b r)
  let K : Trios := fun a b r => a ≠ t ∧ b ≠ t ∧ r ≠ t ∧ ¬ Sym (TF u) a b r ∧
    ∀ τ ∈ (S.pinOn Rp).trios, trioIs a b r τ = false
  have htt : u.Adj t t := adj_refl u t ht
  have rsymm : ∀ {y w}, Rr y w → Rr w y := by
    intro y w ⟨h1, h2, h3, h4⟩
    refine ⟨h2, h1, usymm h3, ?_⟩
    rcases h4 with e | e | e | e
    · exact Or.inl e.symm
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inr (nsym_perm e (by simp [perms]))))
  -- los tríos de la familia: los de `u`, y las bases prohibidas en `S`
  have notT_t : ∀ {a b s}, (a = t ∨ b = t ∨ s = t) → ¬ Sym (TF u) a b s → ¬ T a b s := by
    intro a b s ht' hn h
    rcases h with h | ⟨h1, h2, h3, _⟩
    · exact hn h
    · rcases ht' with e | e | e
      · exact h1 e
      · exact h2 e
      · exact h3 e
  have notT : ∀ {a b s}, ¬ Sym (TF u) a b s → ¬ Sym (TF S) a b s → ¬ T a b s :=
    fun hu hs h => h.elim hu (fun h' => hs h'.2.2.2)
  have tsw12 : ∀ {a b r}, T a b r → T b a r := by
    intro a b r h
    rcases h with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl (sym_perm h (by simp [perms]))
    · exact Or.inr ⟨h2, h1, h3, sym_perm h4 (by simp [perms])⟩
  have tsw23 : ∀ {a b r}, T a b r → T a r b := by
    intro a b r h
    rcases h with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl (sym_perm h (by simp [perms]))
    · exact Or.inr ⟨h1, h3, h2, sym_perm h4 (by simp [perms])⟩
  -- el testigo de una cara con la cima
  have faceW : ∀ {p q}, p ≠ t → q ≠ t → p ≠ q → Rr p q → ¬ Sym (TF u) p q t → ∀ l, 0 ≤ l → l < c →
      ∃ s, s.id.step = l ∧ Rr p s ∧ Rr q s ∧ Rr t s ∧
        (s = p ∨ s = q ∨ s = t ∨ (¬ T p q s ∧ ¬ T p t s ∧ ¬ T q t s)) := by
    intro p q hpt hqt npq ⟨htp, htq, hpq, _⟩ hf l h0 h1
    obtain ⟨s, hsl, hps, hqs, hts', hw⟩ := hface p q hpt hqt npq htp htq hpq hf l h0 h1
    refine ⟨s, hsl, ⟨htp, hts', hps, ?_⟩, ⟨htq, hts', hqs, ?_⟩, ⟨htt, hts', hts', Or.inr (Or.inl rfl)⟩, ?_⟩
    · rcases hw with e | e | e | ⟨_, n2, _, _⟩
      · exact Or.inl e.symm
      · rw [e]; exact Or.inr (Or.inr (Or.inr hf))
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (nsym_perm n2 (by simp [perms]))))
    · rcases hw with e | e | e | ⟨_, _, n3, _⟩
      · rw [e]; exact Or.inr (Or.inr (Or.inr (nsym_perm hf (by simp [perms]))))
      · exact Or.inl e.symm
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (nsym_perm n3 (by simp [perms]))))
    · rcases hw with e | e | e | ⟨n1, n2, n3, n4⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr ⟨notT n1 n4, notT_t (Or.inr (Or.inl rfl)) n2,
          notT_t (Or.inr (Or.inl rfl)) n3⟩))
  -- los testigos de las aristas
  have hedge : ∀ {a b}, Rr a b → a ≠ b → ∀ l, 0 ≤ l → l < c →
      ∃ s, s.id.step = l ∧ Rr a s ∧ Rr b s ∧ (s = a ∨ s = b ∨ ¬ T a b s) := by
    intro a b hR nab l h0 h1
    obtain ⟨hta, htb, hab, hc⟩ := hR
    by_cases hat : a = t
    · obtain ⟨s, hsl, has, hbs', hw⟩ := hTGu.edge (low hab) nab l h0 h1
      have hts' : u.Adj t s := by rw [← hat]; exact has.1.2.2
      refine ⟨s, hsl, ⟨hta, hts', has.1.2.2, Or.inr (Or.inl hat)⟩, ⟨htb, hts', hbs'.1.2.2, ?_⟩, ?_⟩
      · rcases hw with e | e | e
        · exact Or.inr (Or.inr (Or.inl (e.trans hat)))
        · exact Or.inl e.symm
        · refine Or.inr (Or.inr (Or.inr ?_))
          have := nsym hab has.1.2.2 hbs'.1.2.2 e
          rw [hat] at this
          exact nsym_perm this (by simp [perms])
      · rcases hw with e | e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (notT_t (Or.inl hat) (nsym hab has.1.2.2 hbs'.1.2.2 e)))
    · by_cases hbt : b = t
      · obtain ⟨s, hsl, has, hbs', hw⟩ := hTGu.edge (low hab) nab l h0 h1
        have hts' : u.Adj t s := by rw [← hbt]; exact hbs'.1.2.2
        refine ⟨s, hsl, ⟨hta, hts', has.1.2.2, ?_⟩, ⟨htb, hts', hbs'.1.2.2, Or.inr (Or.inl hbt)⟩, ?_⟩
        · rcases hw with e | e | e
          · exact Or.inl e.symm
          · exact Or.inr (Or.inr (Or.inl (e.trans hbt)))
          · refine Or.inr (Or.inr (Or.inr ?_))
            have := nsym hab has.1.2.2 hbs'.1.2.2 e
            rw [hbt] at this
            exact nsym_perm this (by simp [perms])
        · rcases hw with e | e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (notT_t (Or.inr (Or.inl hbt)) (nsym hab has.1.2.2 hbs'.1.2.2 e)))
      · have habt : ¬ Sym (TF u) a b t := by
          rcases hc with e | e | e | e
          · exact absurd e nab
          · exact absurd e hat
          · exact absurd e hbt
          · exact e
        obtain ⟨s, hsl, r1, r2, _, hw⟩ := faceW hat hbt nab ⟨hta, htb, hab, hc⟩ habt l h0 h1
        refine ⟨s, hsl, r1, r2, ?_⟩
        rcases hw with e | e | e | ⟨n1, _, _⟩
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · rw [e]; exact Or.inr (Or.inr (notT_t (Or.inr (Or.inr rfl)) habt))
        · exact Or.inr (Or.inr n1)
  -- todo nodo de la familia tiene un vecino de la familia en cada paso
  have hstep : ∀ {y}, V y → ∀ l, 0 ≤ l → l < c → ∃ r, r.id.step = l ∧ Rr y r := by
    intro y hy l h0 h1
    by_cases hyt : y = t
    · subst hyt
      obtain ⟨r, hrl, hyr, _⟩ := hcl.pair (hcl.refl ht) l h0 (by rw [hcsu]; exact h1)
      exact ⟨r, hrl, htt, hyr.2.2, hyr.2.2, Or.inr (Or.inl rfl)⟩
    · obtain ⟨s, hsl, _, hys, _⟩ := hedge (a := t) (b := y) ⟨htt, hy, hy, Or.inr (Or.inl rfl)⟩
        (fun e => hyt e.symm) l h0 h1
      exact ⟨s, hsl, hys⟩
  have hValive : ∀ {y}, V y → y ∈ S.alive := fun {y} hy => (hS.edges t y (key t y hy htO)).2
  have hRadj : ∀ {y w}, Rr y w → S.Adj y w := by
    intro y w ⟨h1, h2, h3, h4⟩
    by_cases hyw : y = w
    · subst hyw; exact adj_refl S y (hValive h1)
    by_cases hyt : y = t
    · rw [hyt]; exact key t w h2 htO
    by_cases hwt : w = t
    · rw [hwt]; exact (adj_symm S _ _).mp (key t y h1 htO)
    have hn : ¬ Sym (TF u) y w t := by
      rcases h4 with e | e | e | e
      · exact absurd e hyw
      · exact absurd e hyt
      · exact absurd e hwt
      · exact e
    apply Classical.byContradiction
    intro hno
    have hJf : TF J y w t := hcut (hsub.adj _ _ h3) (hsub.adj _ _ (usymm h1)) (hsub.adj _ _ (usymm h2)) hyw hyt hwt
      (Or.inl fun h => hno h.1) (fun h => htO (heO y t h.2.1).2)
    exact hn (Or.inl (tF_mono (trios_grow_pinOn J Rp) h3 hJf))
  -- los enlaces: un vecino del paso anterior es padre, y uno del paso siguiente es hijo
  have hpar : ∀ {x p : PathNodeId} {n : PNodeB}, S.node? x = some n → Rr x p → p.id.step + 1 = x.id.step →
      p ∈ n.parents := by
    intro x p n hn hR hst
    have hA := hRadj hR
    exact (hS.links.2.1 n (node?_mem hn) p (hValive hR.2.1) (by rw [node?_id hn]; exact hA)).1
      (by rw [node?_id hn]; exact hap x p hA hst)
  have hson : ∀ {x q : PathNodeId} {n : PNodeB}, S.node? x = some n → Rr x q → x.id.step + 1 = q.id.step →
      q ∈ n.sons := by
    intro x q n hn hR hst
    have hA := hRadj hR
    exact (hS.links.2.1 n (node?_mem hn) q (hValive hR.2.1) (by rw [node?_id hn]; exact hA)).2
      (by rw [node?_id hn]; exact hap q x ((adj_symm S _ _).mp hA) hst)
  have hstep0 : ∀ {y}, V y → 0 ≤ y.id.step := by
    intro y hy
    obtain ⟨n, hn, hnid⟩ := hS.docs y (hValive hy)
    have := hS.zero n hn
    rw [hnid] at this; exact this
  have hsec : SecStruct S V Rr := by
    refine ⟨fun hy => hValive hy, fun hy => ⟨hy, hy, adj_refl u _ (hiu.edges _ _ hy).2, Or.inl rfl⟩, rsymm,
      fun hr => ⟨hr.1, hr.2.1⟩, hRadj, ?_, ?_, ?_, ?_⟩
    · intro y w hR l h0 h1
      rw [← hcs] at h1
      by_cases hyw : y = w
      · subst hyw
        obtain ⟨r, hrl, hyr⟩ := hstep hR.1 l h0 h1
        exact ⟨r, hrl, hyr, hyr⟩
      · obtain ⟨s, hsl, h1', h2', _⟩ := hedge hR hyw l h0 h1
        exact ⟨s, hsl, h1', h2'⟩
    · intro y hy
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hS.docs (hValive hy))
      refine ⟨n, hn, fun hp => ?_, fun hs => ?_⟩
      · have h0 := hstep0 hy
        have hne : y.id.step ≠ 0 := by
          intro e
          rw [hS.root y (hValive hy) e] at hp
          simp at hp
        obtain ⟨r, hrl, hyr⟩ := hstep hy (y.id.step - 1) (by omega)
          (by have := hbs y (hiu.edges _ _ hy).2; omega)
        exact ⟨r, hpar hn hyr (by omega), hyr⟩
      · rw [← hcs] at hs
        have hlt := hbs y (hiu.edges _ _ hy).2
        obtain ⟨r, hrl, hyr⟩ := hstep hy (y.id.step + 1) (by have := hstep0 hy; omega) (by omega)
        exact ⟨r, hson hn hyr (by omega), hyr⟩
    · intro x w n hR hne hn hst
      obtain ⟨s, hsl, hxs, hws, _⟩ := hedge hR hne (x.id.step - 1) (by omega)
        (by have := hbs x (hiu.edges _ _ hR.1).2; omega)
      exact ⟨s, hpar hn hxs (by omega), hxs, rsymm hws⟩
    · intro x w n hR hne hn hst
      rw [← hcs] at hst
      obtain ⟨s, hsl, hxs, hws, _⟩ := hedge hR hne (x.id.step + 1) (by have := hstep0 hR.1; omega) (by omega)
      exact ⟨s, hson hn hxs (by omega), hxs, rsymm hws⟩
  -- las bases bajo la cima
  have f : ∀ {y w}, Rr y w → y ≠ w → y ≠ t → w ≠ t → ¬ Sym (TF u) y w t := by
    intro y w hR h1 h2 h3
    rcases hR.2.2.2 with e | e | e | e
    · exact absurd e h1
    · exact absurd e h2
    · exact absurd e h3
    · exact e
  have tetra : ∀ {a b r}, Rr a b → Rr a r → Rr b r → a ≠ b → a ≠ r → b ≠ r → a ≠ t → b ≠ t → r ≠ t →
      Tetra u t a b r := fun hab har hbr nab nar nbr nat nbt nrt =>
    ⟨nat, nbt, nrt, nab, nar, nbr, hab.1, hab.2.1, har.2.1, hab.2.2.1, har.2.2.1, hbr.2.2.1, f hab nab nat nbt,
      f har nar nat nrt, f hbr nbr nbt nrt⟩
  have hK : KeptOut Rr K (S.pinOn Rp).trios := fun a b r _ _ _ hk => hk.2.2.2.2
  -- el invariante en el lado sin fijar
  have h0 : DownInv V Rr T c S := by
    refine ⟨hsec, hnsS, hcs.symm, ?_⟩
    intro a b r hab har hbr hf
    apply Classical.byContradiction
    intro hnT
    obtain ⟨nab, hd⟩ := hf
    have hd' := hd
    unfold deadTrio at hd'
    rw [Bool.and_eq_true] at hd'
    obtain ⟨τ, hτ, hti⟩ := List.any_eq_true.mp hd'.2
    obtain ⟨_, nar, nbr⟩ := distinct_of_trioIs hti (hndS τ hτ)
    by_cases hno : a ≠ t ∧ b ≠ t ∧ r ≠ t
    · -- sin la cima: una base prohibida en el lado es un trío de la familia
      exact hnT (Or.inr ⟨hno.1, hno.2.1, hno.2.2, Or.inl ⟨nab, hd⟩⟩)
    · -- con la cima: el otro lado no tiene el triángulo, y el join lo habría prohibido
      have hO : ¬ (O.Adj a b ∧ O.Adj a r ∧ O.Adj b r) := by
        intro ⟨h1, h2, h3⟩
        apply htO
        by_cases e1 : a = t
        · rw [← e1]; exact (heO a b h1).1
        by_cases e2 : b = t
        · rw [← e2]; exact (heO a b h1).2
        by_cases e3 : r = t
        · rw [← e3]; exact (heO a r h2).2
        exact absurd ⟨e1, e2, e3⟩ hno
      have hJf : TF J a b r := hcut (hsub.adj _ _ hab.2.2.1) (hsub.adj _ _ har.2.2.1) (hsub.adj _ _ hbr.2.2.1)
        nab nar nbr (Or.inr ⟨nab, hd⟩) hO
      exact hnT (Or.inl (Or.inl (tF_mono (trios_grow_pinOn J Rp) hab.2.2.1 hJf)))
  -- los testigos de los triángulos con la cima
  have hTGK : TrioGoodK V Rr T K c := by
    refine ⟨hedge, ?_, fun _ _ _ h => tsw23 h, fun _ _ _ h => tsw12 h⟩
    intro a b r hab har hbr nab nar nbr hnT
    have hnU : ¬ Sym (TF u) a b r := fun h => hnT (Or.inl h)
    by_cases hno : a ≠ t ∧ b ≠ t ∧ r ≠ t
    · have htet := tetra hab har hbr nab nar nbr hno.1 hno.2.1 hno.2.2
      have hnS : ¬ Sym (TF S) a b r := fun h => hnT (Or.inr ⟨hno.1, hno.2.1, hno.2.2, h⟩)
      rcases hbase a b r htet hnU hnS with hk | hw
      · exact Or.inl ⟨hno.1, hno.2.1, hno.2.2, hnU, hk⟩
      · right
        intro l h0' h1'
        obtain ⟨s, hsl, hs⟩ := hw l h0' h1'
        refine ⟨s, hsl, ?_⟩
        have rrefl : ∀ {y}, u.Adj t y → Rr y y := fun {y} hy => ⟨hy, hy, adj_refl u y (hiu.edges _ _ hy).2, Or.inl rfl⟩
        have rt : ∀ {y}, u.Adj t y → Rr y t := fun {y} hy => ⟨hy, htt, usymm hy, Or.inr (Or.inr (Or.inl rfl))⟩
        rcases hs with e | e | e | e | ⟨⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩, m1, m2, m3⟩
        · rw [e]; exact ⟨rrefl hab.1, rsymm hab, rsymm har, Or.inl rfl⟩
        · rw [e]; exact ⟨hab, rrefl hab.2.1, rsymm hbr, Or.inr (Or.inl rfl)⟩
        · rw [e]; exact ⟨har, hbr, rrefl har.2.1, Or.inr (Or.inr (Or.inl rfl))⟩
        · rw [e]
          exact ⟨rt hab.1, rt hab.2.1, rt har.2.1, Or.inr (Or.inr (Or.inr
            ⟨notT_t (Or.inr (Or.inr rfl)) (f hab nab hno.1 hno.2.1),
             notT_t (Or.inr (Or.inr rfl)) (f har nar hno.1 hno.2.2),
             notT_t (Or.inr (Or.inr rfl)) (f hbr nbr hno.2.1 hno.2.2)⟩))⟩
        · exact ⟨⟨hab.1, k1, k2, Or.inr (Or.inr (Or.inr k5))⟩, ⟨hab.2.1, k1, k3, Or.inr (Or.inr (Or.inr k6))⟩,
            ⟨har.2.1, k1, k4, Or.inr (Or.inr (Or.inr k7))⟩,
            Or.inr (Or.inr (Or.inr ⟨notT k8 m1, notT k9 m2, notT k10 m3⟩))⟩
    · right
      intro l h0' h1'
      by_cases e1 : a = t
      · -- la cima es `a`: la cara es `(b, r, t)`
        have nbt : b ≠ t := fun e => nab (e1.trans e.symm)
        have nrt : r ≠ t := fun e => nar (e1.trans e.symm)
        have hf' : ¬ Sym (TF u) b r t := by rw [← e1]; exact nsym_perm hnU (by simp [perms])
        obtain ⟨s, hsl, r1, r2, r3, hw⟩ := faceW nbt nrt nbr hbr hf' l h0' h1'
        refine ⟨s, hsl, by rw [e1]; exact r3, r1, r2, ?_⟩
        rcases hw with e | e | e | ⟨n1, n2, n3⟩
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inl (e.trans e1.symm)
        · exact Or.inr (Or.inr (Or.inr ⟨by rw [e1]; exact fun h => n2 (tsw12 h),
            by rw [e1]; exact fun h => n3 (tsw12 h), n1⟩))
      by_cases e2 : b = t
      · -- la cima es `b`: la cara es `(a, r, t)`
        have nrt : r ≠ t := fun e => nbr (e2.trans e.symm)
        have hf' : ¬ Sym (TF u) a r t := by rw [← e2]; exact nsym_perm hnU (by simp [perms])
        obtain ⟨s, hsl, r1, r2, r3, hw⟩ := faceW e1 nrt nar har hf' l h0' h1'
        refine ⟨s, hsl, r1, by rw [e2]; exact r3, r2, ?_⟩
        rcases hw with e | e | e | ⟨n1, n2, n3⟩
        · exact Or.inl e
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inr (Or.inl (e.trans e2.symm))
        · exact Or.inr (Or.inr (Or.inr ⟨by rw [e2]; exact n2, n1, by rw [e2]; exact fun h => n3 (tsw12 h)⟩))
      · -- la cima es `r`: la cara es `(a, b, t)`
        have e3 : r = t := by
          apply Classical.byContradiction
          intro e3
          exact hno ⟨e1, e2, e3⟩
        have hf' : ¬ Sym (TF u) a b t := by rw [← e3]; exact hnU
        obtain ⟨s, hsl, r1, r2, r3, hw⟩ := faceW e1 e2 nab hab hf' l h0' h1'
        refine ⟨s, hsl, r1, r2, by rw [e3]; exact r3, ?_⟩
        rcases hw with e | e | e | ⟨n1, n2, n3⟩
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (Or.inl (e.trans e3.symm)))
        · exact Or.inr (Or.inr (Or.inr ⟨n1, by rw [e3]; exact n2, by rw [e3]; exact n3⟩))
  have hagree : ∀ p ∈ Rp, SecAgrees V p := fun p hp q hq hqs =>
    pinned_pinOn hJ.docs hv p hp q (hiu.edges _ _ hq).2 hqs
  have hX := downInv_pinOnK hTGK rsymm h0 hagree hK
  refine ⟨isValid_of_sec hX.sec (y := t) htt, hX.sec.alive htt, ?_⟩
  intro a b _ _ _ hta htb hab hf
  have rta : Rr t a := ⟨htt, hta, hta, Or.inr (Or.inl rfl)⟩
  have rtb : Rr t b := ⟨htt, htb, htb, Or.inr (Or.inl rfl)⟩
  have rab : Rr a b := ⟨hta, htb, hab, Or.inr (Or.inr (Or.inr hf))⟩
  refine ⟨hX.sec.adj rta, hX.sec.adj rtb, hX.sec.adj rab, ?_⟩
  intro hs
  apply hf
  have key : ∀ p q w, (p, q, w) ∈ perms a b t → TF (S.pinOn Rp) p q w → Sym (TF u) a b t := by
    intro p q w hp hfp
    obtain ⟨r1, r2, r3⟩ := tri_of_perms (R := Rr) rsymm rab (rsymm rta) (rsymm rtb) hp
    rcases hX.tri r1 r2 r3 hfp with h | ⟨h1, h2, h3, _⟩
    · exact sym_perm h hp
    · rcases perms_mem3 hp with e | e | e
      · exact absurd e.symm h1
      · exact absurd e.symm h2
      · exact absurd e.symm h3
  unfold Sym at hs
  rcases hs with h | h | h | h | h | h <;> exact key _ _ _ (by simp [perms]) h

/-- **Una cara que vive en el lado fijado tiene sus testigos.** Si `(a, b, t)` es un triángulo sin prohibir de
`P = pinOn S Rp` y `P` vive entero en `u` (`hX`), el punto fijo de la regla en `P` da en cada paso un testigo que
también lo es en `u`, con `(a, b, s)` sin prohibir en `S`. -/
theorem hface_of_sideFace {S u : GPathB} {Rp : List NodeId} (hS : SInvB S) (hnsS : NoSelf S) (hndS : NoDegT S)
    (hvP : (S.pinOn Rp).isValid = true)
    (hX : DownInv (LowV (S.pinOn Rp) S.current_step) (LowR (S.pinOn Rp) S.current_step) (TF (S.pinOn Rp))
      S.current_step u)
    {a b t : PathNodeId} (hab : (S.pinOn Rp).Adj a b) (hat : (S.pinOn Rp).Adj a t) (hbt : (S.pinOn Rp).Adj b t)
    (nab : a ≠ b) (nat : a ≠ t) (nbt : b ≠ t) (hf : ¬ Sym (TF (S.pinOn Rp)) a b t) (l : Int) (h0 : 0 ≤ l)
    (h1 : l < S.current_step) :
    ∃ s, s.id.step = l ∧ u.Adj a s ∧ u.Adj b s ∧ u.Adj t s ∧
      (s = a ∨ s = b ∨ s = t ∨ (¬ Sym (TF u) a b s ∧ ¬ Sym (TF u) a t s ∧ ¬ Sym (TF u) b t s ∧
        ¬ Sym (TF S) a b s)) := by
  have hiP : SInvB (S.pinOn Rp) := sInvB_pinOn hS Rp
  have hbs : ∀ q ∈ (S.pinOn Rp).alive, q.id.step < S.current_step := fun q hq => by
    have := alive_below hiP.docs hiP.below hq; rw [step_pinOn] at this; exact this
  have lowP : ∀ {y w}, (S.pinOn Rp).Adj y w → LowR (S.pinOn Rp) S.current_step y w := fun {y w} h =>
    ⟨⟨(hiP.edges y w h).1, (hiP.edges y w h).2, h⟩, hbs y (hiP.edges y w h).1, hbs w (hiP.edges y w h).2⟩
  have psymm : ∀ {y w}, (S.pinOn Rp).Adj y w → (S.pinOn Rp).Adj w y := fun h => (adj_symm _ _ _).mp h
  -- un triángulo de `P` sin prohibir en `P` no está prohibido en `u` ni en `S`
  have upU : ∀ {x y z}, (S.pinOn Rp).Adj x y → (S.pinOn Rp).Adj x z → (S.pinOn Rp).Adj y z →
      ¬ Sym (TF (S.pinOn Rp)) x y z → ¬ Sym (TF u) x y z := by
    intro x y z hxy hxz hyz hn hs
    apply hn
    refine sym_mono (fun p q w hp hfp => ?_) hs
    obtain ⟨k1, k2, k3⟩ := tri_of_perms (R := fun y w => (S.pinOn Rp).Adj y w) psymm hxy hxz hyz hp
    exact hX.tri (lowP k1) (lowP k2) (lowP k3) hfp
  have upS : ∀ {x y z}, (S.pinOn Rp).Adj x y → (S.pinOn Rp).Adj x z → (S.pinOn Rp).Adj y z →
      ¬ Sym (TF (S.pinOn Rp)) x y z → ¬ Sym (TF S) x y z := by
    intro x y z hxy hxz hyz hn hs
    apply hn
    refine sym_mono (fun p q w hp hfp => ?_) hs
    obtain ⟨k1, _, _⟩ := tri_of_perms (R := fun y w => (S.pinOn Rp).Adj y w) psymm hxy hxz hyz hp
    exact tF_mono (trios_grow_pinOn S Rp) k1 hfp
  obtain ⟨s, hsl, has, hbs', hts, hw⟩ := fix_witness hS hnsS hndS hvP hab hat hbt nab nat nbt hf l h0 h1
  refine ⟨s, hsl, hX.sec.adj (lowP has), hX.sec.adj (lowP hbs'), hX.sec.adj (lowP hts), ?_⟩
  rcases hw with e | e | e | ⟨n1, n2, n3⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inr (Or.inr ⟨upU hab has hbs' n1, upU hat has hts n2, upU hbt hbs' hts n3,
      upS hab has hbs' n1⟩))

-- ============================================================
-- La primera línea no tiene joins
-- ============================================================

/-- En la primera línea hay una sola entrada: no hay joins y `HStarDOn` es vacía. -/
theorem hStarDOn_init (φ : Cnf) : HStarDOn φ (initM .on φ) := by
  intro a ha b hb hab
  rw [initM_eq, List.mem_singleton] at ha hb
  exact absurd (by rw [ha, hb]) hab

/-- `HypsStarDLowOn` sin su primera parte: basta `StarDAt` en la segunda línea y, desde la tercera, su parte por
debajo del paso de los padres y la ausencia de padres complementarios. -/
theorem hypsStarDLowOn_of_tail {φ : Cnf} (h1 : HStarDOn φ (advanceM .on φ (initM .on φ)))
    (hn : ∀ n : Nat, HStarDLowOn φ (advanceM .on φ (advanceM .on φ (stepsM .on φ n (initM .on φ))))) :
    HypsStarDLowOn φ :=
  ⟨hStarDOn_init φ, h1, hn⟩

end GPathB

end AbsSatBingo.Model
