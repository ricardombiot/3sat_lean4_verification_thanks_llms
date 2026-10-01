-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnStarD.lean
import AbsSatBingo.Model.ForbidOnSplit

/-!
# «El primero que muere», sin el corte cruzado

`star_core` (`ForbidOnStar.lean`) lleva la familia de una cima `t` de la unión fijada `u` al lado `S`, y para las
bases bajo la cima pedía (`hlow1`) que una base prohibida en `S` estuviera prohibida en `u`. Eso salía de `CrossCut`,
que es **falso** en `v7` (`probe_prevbig.jl`): el join reinicia los tríos y una base prohibida en un solo lado revive
en la unión.

Aquí la familia lleva sus propios tríos: los de `u`, **y las bases prohibidas en `S`**. Ya no hace falta que la unión
las prohíba (`star_coreD` no tiene `hlow1`). A cambio, los testigos de la familia tienen que esquivarlas:

* `hface`: cada cara viva `(a, b, t)` tiene en cada paso un testigo bueno `s` de `u` con `(a, b, s)` sin prohibir
  también en `S` (el punto fijo de `u` da el testigo; lo nuevo es la última condición);
* `hbase`: como `hlow2`, para las bases vivas en `u` y sin prohibir en `S`, con las tres caras nuevas de la base sin
  prohibir en `S`.

Las dos hablan de testigos de la unión fijada frente a los tríos del lado sin fijar. Las mide `probe_topdead.jl`
(`tt_fail`, `tb_fail`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

namespace GPathB

open Driver Machine MachineOn

/-- **El núcleo, sin corte cruzado.** Una cima viva de `pinOn J Rp` que no está en el otro lado `O` está viva en
`pinOn S Rp`, tratando como prohibidas en la familia de la cima las bases prohibidas en el lado `S` (aunque la unión
no las prohíba). Hipótesis, las dos sobre testigos de la unión fijada:

* `hface`: cada cara viva `(a, b, t)` tiene en cada paso un testigo bueno cuyo trío `(a, b, s)` tampoco está
  prohibido en `S`;
* `hbase`: una base viva en la unión fijada y sin prohibir en `S`, o no está en los tríos de `pinOn S Rp`, o tiene en
  cada paso un nodo que completa el tetraedro con sus tres caras nuevas de la base sin prohibir en `S`. -/
theorem star_coreD {J S O : GPathB} {Rp : List NodeId} (hJ : SInvB J) (hnsJ : NoSelf J) (hndJ : NoDegT J)
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
    (S.pinOn Rp).isValid = true ∧ t ∈ (S.pinOn Rp).alive := by
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
  exact ⟨isValid_of_sec hX.sec (y := t) htt, hX.sec.alive htt⟩

-- ============================================================
-- `TopSideAt` y el veredicto, sin corte cruzado
-- ============================================================

/-- **`StarDAt`**: las dos hipótesis de `star_coreD`, para las cimas de la unión fijada `pinOn J Rp` que son del lado
`S`. Testigos de la unión fijada que esquivan las bases prohibidas en `S`. -/
def StarDAt (S J : GPathB) (Rp : List NodeId) : Prop :=
  (J.pinOn Rp).isValid = true → ∀ t ∈ (J.pinOn Rp).alive, t.id.step = J.current_step - 1 → t ∈ S.alive →
    (∀ a b, a ≠ t → b ≠ t → a ≠ b → (J.pinOn Rp).Adj t a → (J.pinOn Rp).Adj t b → (J.pinOn Rp).Adj a b →
      ¬ Sym (TF (J.pinOn Rp)) a b t → ∀ l, 0 ≤ l → l < J.current_step →
      ∃ s, s.id.step = l ∧ (J.pinOn Rp).Adj a s ∧ (J.pinOn Rp).Adj b s ∧ (J.pinOn Rp).Adj t s ∧
        (s = a ∨ s = b ∨ s = t ∨ (¬ Sym (TF (J.pinOn Rp)) a b s ∧ ¬ Sym (TF (J.pinOn Rp)) a t s ∧
          ¬ Sym (TF (J.pinOn Rp)) b t s ∧ ¬ Sym (TF S) a b s))) ∧
    (∀ a b r, Tetra (J.pinOn Rp) t a b r → ¬ Sym (TF (J.pinOn Rp)) a b r → ¬ Sym (TF S) a b r →
      (∀ τ ∈ (S.pinOn Rp).trios, trioIs a b r τ = false) ∨
      (∀ l, 0 ≤ l → l < J.current_step →
        ∃ s, s.id.step = l ∧ (s = a ∨ s = b ∨ s = r ∨ s = t ∨ (Wit4 (J.pinOn Rp) t a b r s ∧
          ¬ Sym (TF S) a b s ∧ ¬ Sym (TF S) a r s ∧ ¬ Sym (TF S) b r s))))

/-- **`TopSideAt` bajo `StarDAt` en los dos lados**, sin corte cruzado. `bA`, `bB`: los colores de los padres de las cimas de cada lado,
distintos (las cimas de un lado no están vivas en el otro). -/
theorem topSideAt_of_starD {A B : GPathB} {Rp : List NodeId} {bA bB : NodeId} (hA : SInvB A) (hB : SInvB B)
    (hnsA : NoSelf A) (hnsB : NoSelf B) (hndA : NoDegT A) (hndB : NoDegT B)
    (hcs : A.current_step = B.current_step) (hc2 : 2 ≤ A.current_step) (hne : bA ≠ bB)
    (hfA : TopsFrom A (fun a => a = bA)) (hfB : TopsFrom B (fun a => a = bB)) (hapA : AdjPar A) (hapB : AdjPar B)
    (hsA : StarDAt A (joinOn A B) Rp) (hsB : StarDAt B (joinOn A B) Rp) : TopSideAt A B Rp := by
  intro hv t ht hts
  have hcsJ : (joinOn A B).current_step = A.current_step := step_joinOn A B
  have hJ : SInvB (joinOn A B) := sInvB_joinOn hA hB hcs
  have hnsJ : NoSelf (joinOn A B) := noSelf_joinOn hnsA hnsB
  have hndJ : NoDegT (joinOn A B) := noDegT_joinOn hnsA hnsB hA.edges hB.edges
  obtain ⟨T', hT⟩ := joinOn_eq A B
  have halive : ∀ q ∈ (joinOn A B).alive, q ∈ A.alive ∨ q ∈ B.alive := fun q hq => by
    rw [hT] at hq; exact (alive_join A B q).mp hq
  have hadj : ∀ x w, (joinOn A B).Adj x w → A.Adj x w ∨ B.Adj x w := fun x w h => by
    rw [hT] at h; exact adj_join_cases h
  have parA : ∀ q ∈ A.alive, q.id.step = A.current_step - 1 → q.parent_id = some bA := fun q hq hs => by
    obtain ⟨a, rfl, hp⟩ := hfA q hq hs; exact hp
  have parB : ∀ q ∈ B.alive, q.id.step = A.current_step - 1 → q.parent_id = some bB := fun q hq hs => by
    obtain ⟨a, rfl, hp⟩ := hfB q hq (by rw [← hcs]; exact hs); exact hp
  have hsep : t ∈ A.alive → t ∈ B.alive → False := fun h1 h2 => by
    have e := parA t h1 hts
    rw [parB t h2 hts] at e
    exact hne (Option.some.inj e).symm
  rcases halive t ((sub_pinOn _ Rp).alive t ht) with htA | htB
  · exact Or.inl (star_coreD (S := A) (O := B) hJ hnsJ hndJ (by rw [hcsJ]; exact hc2) hv hA hnsA hndA hcsJ hapA hadj
      hB.edges
      (fun hxy hxz hyz nxy nxz nyz s1 hO => tF_joinOn_of_cut hA.edges hB.edges hxy hxz hyz nxy nxz nyz s1 (Or.inl hO))
      ht (fun h => hsep htA h) (hsA hv t ht (by rw [hcsJ]; exact hts) htA).1
      (hsA hv t ht (by rw [hcsJ]; exact hts) htA).2)
  · exact Or.inr (star_coreD (S := B) (O := A) hJ hnsJ hndJ (by rw [hcsJ]; exact hc2) hv hB hnsB hndB (hcsJ.trans hcs)
      hapB (fun x w h => (hadj x w h).symm) hA.edges
      (fun hxy hxz hyz nxy nxz nyz s2 hO => tF_joinOn_of_cut hA.edges hB.edges hxy hxz hyz nxy nxz nyz (Or.inl hO) s2)
      ht (fun h => hsep h htB) (hsB hv t ht (by rw [hcsJ]; exact hts) htB).1
      (hsB hv t ht (by rw [hcsJ]; exact hts) htB).2)

/-- **`StarDAt` en los joins de la máquina**, de cada llegada en la unión, para los pins de `PinsFrom`. -/
def HStarDOn (φ : Cnf) (line : Line) : Prop :=
  ∀ a ∈ line, ∀ b ∈ line, a.1 ≠ b.1 → ∀ d, SendsOn φ a d → SendsOn φ b d → ∀ R, PinsFrom φ d R →
    StarDAt (arrOn φ a d) (joinOn (arrOn φ a d) (arrOn φ b d)) R ∧
    StarDAt (arrOn φ b d) (joinOn (arrOn φ a d) (arrOn φ b d)) R

/-- **`StarDAt` da `TopSideAt` en los joins de la línea.** -/
theorem hTopOn_of_starD {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (hbk : LineBk line) (hp : HStarDOn φ line) : HTopOn φ line := by
  intro a ha b hb hab d hsa hsb R hR
  obtain ⟨ea, ia, na, _, _⟩ := arrTop_facts hT h ha hsa
  obtain ⟨eb, ib, nb, _, _⟩ := arrTop_facts hT h hb hsb
  obtain ⟨fa, _⟩ := arrOn_tops hT (h.on a ha) (hbk a ha).1 hsa
  obtain ⟨fb, _⟩ := arrOn_tops hT (h.on b hb) (hbk b hb).1 hsb
  obtain ⟨pa, _⟩ := arrOn_adjPar (h.on a ha) (h.inv a ha) (hbk a ha).2.1 (hbk a ha).2.2 hsa
  obtain ⟨pb, _⟩ := arrOn_adjPar (h.on b hb) (h.inv b hb) (hbk b hb).2.1 (hbk b hb).2.2 hsb
  obtain ⟨hsA, hsB⟩ := hp a ha b hb hab d hsa hsb R hR
  exact topSideAt_of_starD ia ib ea.2.1 eb.2.1 na nb (ea.1.step.trans eb.1.step.symm) (by rw [ea.1.step]; omega)
    hab fa fb pa pb hsA hsB

/-- **La hipótesis sin corte cruzado**, en cada línea de la máquina `:on`. -/
def HypsStarDOn (φ : Cnf) : Prop := ∀ n : Nat, HStarDOn φ (stepsM .on φ n (initM .on φ))

theorem hypsTopOn_of_starD {φ : Cnf} (H : HypsStarDOn φ) : HypsTopOn φ := by
  have hs := lInvBk_steps (φ := φ) (fun n hl hbk => hTopOn_of_starD (by omega) hl hbk (H n))
  exact fun n => hTopOn_of_starD (by omega) (hs n).1 (hs n).2 (H n)

-- ============================================================
-- Donde vale el corte cruzado, `StarDAt` sale de las hipótesis anteriores
-- ============================================================

/-- **Donde ninguna base revive, `StarDAt` es `Star4At`**: si toda base bajo la cima `t` prohibida en `S` está
prohibida en la unión fijada, las dos hipótesis de `star_coreD` para `t` salen del punto fijo de la regla y de
`Star4At`. Lo propio de `StarDAt` solo tiene contenido en las cimas con alguna base prohibida en su lado y viva en la
unión fijada (las que mide `probe_topdead.jl`). -/
theorem starD_of_noRevive {J S : GPathB} {Rp : List NodeId} (hJ : SInvB J) (hnsJ : NoSelf J) (hndJ : NoDegT J)
    (hv : (J.pinOn Rp).isValid = true) {t : PathNodeId} (ht : t ∈ (J.pinOn Rp).alive) (hts : t.id.step = J.current_step - 1)
    (hnr : ∀ p q w, p ≠ t → q ≠ t → w ≠ t → p ≠ q → p ≠ w → q ≠ w → (J.pinOn Rp).Adj t p → (J.pinOn Rp).Adj t q → (J.pinOn Rp).Adj t w →
      (J.pinOn Rp).Adj p q → (J.pinOn Rp).Adj p w → (J.pinOn Rp).Adj q w → ¬ Sym (TF (J.pinOn Rp)) p q t → ¬ Sym (TF (J.pinOn Rp)) p w t →
      ¬ Sym (TF (J.pinOn Rp)) q w t → Sym (TF S) p q w → Sym (TF (J.pinOn Rp)) p q w)
    (h4 : Star4At J Rp) :
    (∀ a b, a ≠ t → b ≠ t → a ≠ b → (J.pinOn Rp).Adj t a → (J.pinOn Rp).Adj t b → (J.pinOn Rp).Adj a b →
      ¬ Sym (TF (J.pinOn Rp)) a b t → ∀ l, 0 ≤ l → l < J.current_step →
      ∃ s, s.id.step = l ∧ (J.pinOn Rp).Adj a s ∧ (J.pinOn Rp).Adj b s ∧ (J.pinOn Rp).Adj t s ∧
        (s = a ∨ s = b ∨ s = t ∨ (¬ Sym (TF (J.pinOn Rp)) a b s ∧ ¬ Sym (TF (J.pinOn Rp)) a t s ∧
          ¬ Sym (TF (J.pinOn Rp)) b t s ∧ ¬ Sym (TF S) a b s))) ∧
    (∀ a b r, Tetra (J.pinOn Rp) t a b r → ¬ Sym (TF (J.pinOn Rp)) a b r → ¬ Sym (TF S) a b r →
      (∀ τ ∈ (S.pinOn Rp).trios, trioIs a b r τ = false) ∨
      (∀ l, 0 ≤ l → l < J.current_step →
        ∃ s, s.id.step = l ∧ (s = a ∨ s = b ∨ s = r ∨ s = t ∨ (Wit4 (J.pinOn Rp) t a b r s ∧
          ¬ Sym (TF S) a b s ∧ ¬ Sym (TF S) a r s ∧ ¬ Sym (TF S) b r s)))) := by
  let u := J.pinOn Rp
  have usymm : ∀ {y w}, u.Adj y w → u.Adj w y := fun h => (adj_symm u _ _).mp h
  have upS : ∀ {p q w}, p ≠ t → q ≠ t → w ≠ t → p ≠ q → p ≠ w → q ≠ w → u.Adj t p → u.Adj t q → u.Adj t w →
      u.Adj p q → u.Adj p w → u.Adj q w → ¬ Sym (TF u) p q t → ¬ Sym (TF u) p w t → ¬ Sym (TF u) q w t →
      Sym (TF S) p q w → Sym (TF u) p q w := fun {p q w} => hnr p q w
  refine ⟨?_, ?_⟩
  · intro a b hat hbt nab hta htb hab hf l h0 h1
    obtain ⟨s, hsl, has, hbs, hts', hw⟩ := fix_witness hJ hnsJ hndJ hv hab (usymm hta) (usymm htb) nab hat hbt hf
      l h0 h1
    refine ⟨s, hsl, has, hbs, hts', ?_⟩
    by_cases e1 : s = a
    · exact Or.inl e1
    by_cases e2 : s = b
    · exact Or.inr (Or.inl e2)
    by_cases e3 : s = t
    · exact Or.inr (Or.inr (Or.inl e3))
    rcases hw with e | e | e | ⟨n1, n2, n3⟩
    · exact absurd e e1
    · exact absurd e e2
    · exact absurd e e3
    · exact Or.inr (Or.inr (Or.inr ⟨n1, n2, n3, fun hS => n1 (upS hat hbt e3 nab (Ne.symm e1) (Ne.symm e2) hta htb
        hts' hab has hbs hf (nsym_perm n2 (by simp [perms])) (nsym_perm n3 (by simp [perms])) hS)⟩))
  · intro a b r htet hnU _
    right
    intro l h0 h1
    obtain ⟨s, hsl, hs⟩ := h4 hv t ht hts a b r htet hnU l h0 h1
    refine ⟨s, hsl, ?_⟩
    by_cases e1 : s = a
    · exact Or.inl e1
    by_cases e2 : s = b
    · exact Or.inr (Or.inl e2)
    by_cases e3 : s = r
    · exact Or.inr (Or.inr (Or.inl e3))
    by_cases e4 : s = t
    · exact Or.inr (Or.inr (Or.inr (Or.inl e4)))
    obtain ⟨nat, nbt, nrt, nab, nar, nbr, hta, htb, htr, hab, har, hbr, f1, f2, f3⟩ := htet
    rcases hs with e | e | e | e | ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩
    · exact absurd e e1
    · exact absurd e e2
    · exact absurd e e3
    · exact absurd e e4
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩,
        fun hS => k8 (upS nat nbt e4 nab (Ne.symm e1) (Ne.symm e2) hta htb k1 hab k2 k3 f1 k5 k6 hS),
        fun hS => k9 (upS nat nrt e4 nar (Ne.symm e1) (Ne.symm e3) hta htr k1 har k2 k4 f2 k5 k7 hS),
        fun hS => k10 (upS nbt nrt e4 nbr (Ne.symm e2) (Ne.symm e3) htb htr k1 hbr k3 k4 f3 k6 k7 hS)⟩)))

/-- **`CrossCut` + `Star4At` dan las dos hipótesis de `star_coreD`** para una cima del lado `S`: bajo el corte
cruzado una base bajo la cima prohibida en `S` está prohibida en la unión fijada, así que los testigos del punto fijo
y los de `Star4At`, que esquivan los tríos de la unión, esquivan también los de `S`. -/
theorem starD_of_cross4 {J S O : GPathB} {Rp : List NodeId} (hJ : SInvB J) (hnsJ : NoSelf J) (hndJ : NoDegT J)
    (hv : (J.pinOn Rp).isValid = true) (hndS : NoDegT S) (hcs : J.current_step = S.current_step)
    (hadj : ∀ x w, J.Adj x w → S.Adj x w ∨ O.Adj x w) (heO : EdgesAlive O)
    (hcut2 : ∀ {x y z}, J.Adj x y → J.Adj x z → J.Adj y z → x ≠ y → x ≠ z → y ≠ z → SideForbids S (TF S) x y z →
      SideForbids O (TF O) x y z → TF J x y z)
    {t : PathNodeId} (ht : t ∈ (J.pinOn Rp).alive) (hts : t.id.step = J.current_step - 1) (htS : t ∈ S.alive)
    (htO : t ∉ O.alive) (hcross : CrossCut S O) (h4 : Star4At J Rp) :
    (∀ a b, a ≠ t → b ≠ t → a ≠ b → (J.pinOn Rp).Adj t a → (J.pinOn Rp).Adj t b → (J.pinOn Rp).Adj a b →
      ¬ Sym (TF (J.pinOn Rp)) a b t → ∀ l, 0 ≤ l → l < J.current_step →
      ∃ s, s.id.step = l ∧ (J.pinOn Rp).Adj a s ∧ (J.pinOn Rp).Adj b s ∧ (J.pinOn Rp).Adj t s ∧
        (s = a ∨ s = b ∨ s = t ∨ (¬ Sym (TF (J.pinOn Rp)) a b s ∧ ¬ Sym (TF (J.pinOn Rp)) a t s ∧
          ¬ Sym (TF (J.pinOn Rp)) b t s ∧ ¬ Sym (TF S) a b s))) ∧
    (∀ a b r, Tetra (J.pinOn Rp) t a b r → ¬ Sym (TF (J.pinOn Rp)) a b r → ¬ Sym (TF S) a b r →
      (∀ τ ∈ (S.pinOn Rp).trios, trioIs a b r τ = false) ∨
      (∀ l, 0 ≤ l → l < J.current_step →
        ∃ s, s.id.step = l ∧ (s = a ∨ s = b ∨ s = r ∨ s = t ∨ (Wit4 (J.pinOn Rp) t a b r s ∧
          ¬ Sym (TF S) a b s ∧ ¬ Sym (TF S) a r s ∧ ¬ Sym (TF S) b r s)))) := by
  let u := J.pinOn Rp
  have hsub : Sub u J := sub_pinOn J Rp
  have usymm : ∀ {y w}, u.Adj y w → u.Adj w y := fun h => (adj_symm u _ _).mp h
  -- un triángulo de `u` con la cima, prohibido en `S`, está prohibido en `u`
  have face_up : ∀ {p q w}, u.Adj p q → u.Adj p w → u.Adj q w → (t = p ∨ t = q ∨ t = w) → TF S p q w →
      TF u p q w := by
    intro p q w hpq hpw hqw htin hf
    have hd := hf.2
    unfold deadTrio at hd
    rw [Bool.and_eq_true] at hd
    obtain ⟨τ, hτ, hti⟩ := List.any_eq_true.mp hd.2
    obtain ⟨npq, npw, nqw⟩ := distinct_of_trioIs hti (hndS τ hτ)
    have hO : SideForbids O (TF O) p q w := by
      left
      intro ⟨h1, h2, _⟩
      apply htO
      rcases htin with e | e | e
      · rw [e]; exact (heO p q h1).1
      · rw [e]; exact (heO p q h1).2
      · rw [e]; exact (heO p w h2).2
    exact tF_mono (trios_grow_pinOn J Rp) hpq
      (hcut2 (hsub.adj _ _ hpq) (hsub.adj _ _ hpw) (hsub.adj _ _ hqw) npq npw nqw (Or.inr hf) hO)
  have nsymS : ∀ {y w}, u.Adj y w → u.Adj t y → u.Adj t w → ¬ Sym (TF u) y w t → ¬ Sym (TF S) y w t := by
    intro y w hyw hty htw hn hs
    apply hn
    refine sym_mono (fun p q x hp hf => ?_) hs
    obtain ⟨h1, h2, h3⟩ := tri_of_perms (R := fun y w => u.Adj y w) usymm hyw (usymm hty) (usymm htw) hp
    exact face_up h1 h2 h3 (perms_mem3 hp) hf
  have key : ∀ a b, u.Adj a b → a ∉ O.alive → S.Adj a b := fun a b h hn =>
    (hadj a b (hsub.adj _ _ h)).resolve_right (fun ho => hn (heO a b ho).1)
  have sadj : ∀ {y w}, y ≠ w → y ≠ t → w ≠ t → u.Adj y w → u.Adj t y → u.Adj t w → ¬ Sym (TF u) y w t →
      S.Adj y w := by
    intro y w hyw hyt hwt h3 h1 h2 hn
    apply Classical.byContradiction
    intro hno
    have hJf : TF J y w t := hcut2 (hsub.adj _ _ h3) (hsub.adj _ _ (usymm h1)) (hsub.adj _ _ (usymm h2)) hyw hyt hwt
      (Or.inl fun h => hno h.1) (Or.inl fun h => htO (heO y t h.2.1).2)
    exact hn (Or.inl (tF_mono (trios_grow_pinOn J Rp) h3 hJf))
  -- una base bajo la cima prohibida en `S` está prohibida en `u`
  have up : ∀ {p q w}, p ≠ t → q ≠ t → w ≠ t → p ≠ q → p ≠ w → q ≠ w → u.Adj t p → u.Adj t q → u.Adj t w →
      u.Adj p q → u.Adj p w → u.Adj q w → ¬ Sym (TF u) p q t → ¬ Sym (TF u) p w t → ¬ Sym (TF u) q w t →
      TF S p q w → TF u p q w := by
    intro p q w npt nqt nwt npq npw nqw htp htq htw hpq hpw hqw f1 f2 f3 hf
    have hO := hcross t p q w htS (by rw [← hcs]; exact hts) npt nqt nwt npq npw nqw (key t p htp htO)
      (key t q htq htO) (key t w htw htO) (sadj npq npt nqt hpq htp htq f1) (sadj npw npt nwt hpw htp htw f2)
      (sadj nqw nqt nwt hqw htq htw f3) (nsymS hpq htp htq f1) (nsymS hpw htp htw f2) (nsymS hqw htq htw f3) hf
    exact tF_mono (trios_grow_pinOn J Rp) hpq
      (hcut2 (hsub.adj _ _ hpq) (hsub.adj _ _ hpw) (hsub.adj _ _ hqw) npq npw nqw (Or.inr hf) hO)
  have upS : ∀ {p q w}, p ≠ t → q ≠ t → w ≠ t → p ≠ q → p ≠ w → q ≠ w → u.Adj t p → u.Adj t q → u.Adj t w →
      u.Adj p q → u.Adj p w → u.Adj q w → ¬ Sym (TF u) p q t → ¬ Sym (TF u) p w t → ¬ Sym (TF u) q w t →
      Sym (TF S) p q w → Sym (TF u) p q w := by
    intro p q w npt nqt nwt npq npw nqw htp htq htw hpq hpw hqw f1 f2 f3 hs
    have g1 : ¬ Sym (TF u) q p t := nsym_perm f1 (by simp [perms])
    have g2 : ¬ Sym (TF u) w p t := nsym_perm f2 (by simp [perms])
    have g3 : ¬ Sym (TF u) w q t := nsym_perm f3 (by simp [perms])
    unfold Sym at hs
    rcases hs with h | h | h | h | h | h
    · exact Or.inl (up npt nqt nwt npq npw nqw htp htq htw hpq hpw hqw f1 f2 f3 h)
    · exact Or.inr (Or.inl (up npt nwt nqt npw npq (Ne.symm nqw) htp htw htq hpw hpq (usymm hqw) f2 f1 g3 h))
    · exact Or.inr (Or.inr (Or.inl (up nqt npt nwt (Ne.symm npq) nqw npw htq htp htw (usymm hpq) hqw hpw g1 f3 f2
        h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (up nqt nwt npt nqw (Ne.symm npq) (Ne.symm npw) htq htw htp hqw
        (usymm hpq) (usymm hpw) f3 g1 g2 h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (up nwt npt nqt (Ne.symm npw) (Ne.symm nqw) npq htw htp htq
        (usymm hpw) (usymm hqw) hpq g2 g3 f1 h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (up nwt nqt npt (Ne.symm nqw) (Ne.symm npw) (Ne.symm npq) htw
        htq htp (usymm hqw) (usymm hpw) (usymm hpq) g3 g2 g1 h)))))
  exact starD_of_noRevive hJ hnsJ hndJ hv ht hts (fun _ _ _ => upS) h4

/-- **`StarDAt` en los dos lados, bajo el corte cruzado y el cierre a nivel cuatro.** -/
theorem starDAt_of_cross4 {A B : GPathB} {Rp : List NodeId} {bA bB : NodeId} (hA : SInvB A) (hB : SInvB B)
    (hnsA : NoSelf A) (hnsB : NoSelf B) (hndA : NoDegT A) (hndB : NoDegT B)
    (hcs : A.current_step = B.current_step) (hne : bA ≠ bB)
    (hfA : TopsFrom A (fun a => a = bA)) (hfB : TopsFrom B (fun a => a = bB))
    (hxA : CrossCut A B) (hxB : CrossCut B A) (h4 : Star4At (joinOn A B) Rp) :
    StarDAt A (joinOn A B) Rp ∧ StarDAt B (joinOn A B) Rp := by
  have hcsJ : (joinOn A B).current_step = A.current_step := step_joinOn A B
  have hJ : SInvB (joinOn A B) := sInvB_joinOn hA hB hcs
  have hnsJ : NoSelf (joinOn A B) := noSelf_joinOn hnsA hnsB
  have hndJ : NoDegT (joinOn A B) := noDegT_joinOn hnsA hnsB hA.edges hB.edges
  obtain ⟨T', hT⟩ := joinOn_eq A B
  have hadj : ∀ x w, (joinOn A B).Adj x w → A.Adj x w ∨ B.Adj x w := fun x w h => by
    rw [hT] at h; exact adj_join_cases h
  have hsep : ∀ t : PathNodeId, t.id.step = (joinOn A B).current_step - 1 → t ∈ A.alive → t ∈ B.alive → False := by
    intro t hts h1 h2
    obtain ⟨a, ha, hp⟩ := hfA t h1 (by rw [← hcsJ]; exact hts)
    obtain ⟨b, hb, hp'⟩ := hfB t h2 (by rw [← hcs, ← hcsJ]; exact hts)
    rw [hp, ha, hb] at hp'
    exact hne (Option.some.inj hp')
  constructor
  · intro hv t ht hts htA
    exact starD_of_cross4 (S := A) (O := B) hJ hnsJ hndJ hv hndA hcsJ hadj hB.edges
      (fun hxy hxz hyz nxy nxz nyz s1 s2 => tF_joinOn_of_cut hA.edges hB.edges hxy hxz hyz nxy nxz nyz s1 s2)
      ht hts htA (fun h => hsep t hts htA h) hxA h4
  · intro hv t ht hts htB
    exact starD_of_cross4 (S := B) (O := A) hJ hnsJ hndJ hv hndB (hcsJ.trans hcs) (fun x w h => (hadj x w h).symm)
      hA.edges
      (fun hxy hxz hyz nxy nxz nyz s2 s1 => tF_joinOn_of_cut hA.edges hB.edges hxy hxz hyz nxy nxz nyz s1 s2)
      ht hts htB (fun h => hsep t hts h htB) hxB h4

theorem hStarDOn_of_cross4 {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    (hbk : LineBk line) (hp : HCross4On φ line) : HStarDOn φ line := by
  intro a ha b hb hab d hsa hsb R hR
  obtain ⟨ea, ia, na, _, _⟩ := arrTop_facts hT h ha hsa
  obtain ⟨eb, ib, nb, _, _⟩ := arrTop_facts hT h hb hsb
  obtain ⟨fa, _⟩ := arrOn_tops hT (h.on a ha) (hbk a ha).1 hsa
  obtain ⟨fb, _⟩ := arrOn_tops hT (h.on b hb) (hbk b hb).1 hsb
  obtain ⟨hxA, hxB, h4⟩ := hp a ha b hb hab d hsa hsb
  exact starDAt_of_cross4 ia ib ea.2.1 eb.2.1 na nb (ea.1.step.trans eb.1.step.symm) hab fa fb hxA hxB (h4 R hR)

/-- **Las hipótesis anteriores dan la nueva**: donde valen `CrossCut` y `Star4At` vale `StarDAt`. Las medidas sin
fallos de `CrossCut` y `Star4At` respaldan también `HypsStarDOn` en esas instancias. -/
theorem hypsStarDOn_of_cross4 {φ : Cnf} (H : HypsCross4On φ) : HypsStarDOn φ := by
  have hs := lInvBk_steps (φ := φ) (fun n hl hbk => hTopOn_of_cross4 (by omega) hl hbk (H n))
  exact fun n => hStarDOn_of_cross4 (by omega) (hs n).1 (hs n).2 (H n)

-- ============================================================
-- En el paso de los padres no hay nada nuevo: lo propio de `StarDAt` está por debajo
-- ============================================================

/-- **`StarDAt` por debajo del paso de los padres** de la cima. -/
def StarDLowAt (S J : GPathB) (Rp : List NodeId) : Prop :=
  (J.pinOn Rp).isValid = true → ∀ t ∈ (J.pinOn Rp).alive, t.id.step = J.current_step - 1 → t ∈ S.alive →
    (∀ a b, a ≠ t → b ≠ t → a ≠ b → (J.pinOn Rp).Adj t a → (J.pinOn Rp).Adj t b → (J.pinOn Rp).Adj a b →
      ¬ Sym (TF (J.pinOn Rp)) a b t → ∀ l, 0 ≤ l → l < J.current_step - 2 →
      ∃ s, s.id.step = l ∧ (J.pinOn Rp).Adj a s ∧ (J.pinOn Rp).Adj b s ∧ (J.pinOn Rp).Adj t s ∧
        (s = a ∨ s = b ∨ s = t ∨ (¬ Sym (TF (J.pinOn Rp)) a b s ∧ ¬ Sym (TF (J.pinOn Rp)) a t s ∧
          ¬ Sym (TF (J.pinOn Rp)) b t s ∧ ¬ Sym (TF S) a b s))) ∧
    (∀ a b r, Tetra (J.pinOn Rp) t a b r → ¬ Sym (TF (J.pinOn Rp)) a b r → ¬ Sym (TF S) a b r →
      (∀ τ ∈ (S.pinOn Rp).trios, trioIs a b r τ = false) ∨
      (∀ l, 0 ≤ l → l < J.current_step - 2 →
        ∃ s, s.id.step = l ∧ (s = a ∨ s = b ∨ s = r ∨ s = t ∨ (Wit4 (J.pinOn Rp) t a b r s ∧
          ¬ Sym (TF S) a b s ∧ ¬ Sym (TF S) a r s ∧ ¬ Sym (TF S) b r s))))

/-- **`StarDAt` para una cima, desde su parte baja**, en abstracto. En el paso de la cima el testigo es la cima. En el
paso de los padres los nodos de `S` no están en el otro lado (`hex`), así que un triángulo con uno de ellos prohibido en
`S` lo guarda el join: los testigos del punto fijo y el padre que completa el tetraedro (`hdich`, sin padres
complementarios, `hns`) esquivan los tríos de `S` sin pedirlo. -/
theorem starD_of_low {J S O : GPathB} {Rp : List NodeId} (hJ : SInvB J) (hnsJ : NoSelf J) (hndJ : NoDegT J)
    (hv : (J.pinOn Rp).isValid = true) (hndS : NoDegT S) (heS : EdgesAlive S)
    (hadj : ∀ x w, J.Adj x w → S.Adj x w ∨ O.Adj x w) (heO : EdgesAlive O)
    (hcut2 : ∀ {x y z}, J.Adj x y → J.Adj x z → J.Adj y z → x ≠ y → x ≠ z → y ≠ z → SideForbids S (TF S) x y z →
      SideForbids O (TF O) x y z → TF J x y z)
    {t : PathNodeId} (ht : t ∈ (J.pinOn Rp).alive) (hts : t.id.step = J.current_step - 1) (htO : t ∉ O.alive)
    (hex : ∀ s : PathNodeId, s.id.step = J.current_step - 2 → s ∈ S.alive → s ∉ O.alive)
    (hbelow : ∀ q, (J.pinOn Rp).Adj t q → q ≠ t → q.id.step < J.current_step - 1)
    (hdich : ∀ x y z, Tetra (J.pinOn Rp) t x y z → x.id.step < J.current_step - 2 → y.id.step < J.current_step - 2 →
      z.id.step < J.current_step - 2 →
      (∃ s, s.id.step + 1 = t.id.step ∧ Wit4 (J.pinOn Rp) t x y z s) ∨ ParSplitAt (J.pinOn Rp) t x y z ∨
        ParSplitAt (J.pinOn Rp) t y x z ∨ ParSplitAt (J.pinOn Rp) t z x y)
    (hns : ∀ x y z, Tetra (J.pinOn Rp) t x y z → ¬ Sym (TF (J.pinOn Rp)) x y z → x.id.step < J.current_step - 2 →
      y.id.step < J.current_step - 2 → z.id.step < J.current_step - 2 →
      ¬ ParSplitAt (J.pinOn Rp) t x y z ∧ ¬ ParSplitAt (J.pinOn Rp) t y x z ∧ ¬ ParSplitAt (J.pinOn Rp) t z x y)
    (hlowF : (∀ a b, a ≠ t → b ≠ t → a ≠ b → (J.pinOn Rp).Adj t a → (J.pinOn Rp).Adj t b → (J.pinOn Rp).Adj a b →
      ¬ Sym (TF (J.pinOn Rp)) a b t → ∀ l, 0 ≤ l → l < J.current_step - 2 →
      ∃ s, s.id.step = l ∧ (J.pinOn Rp).Adj a s ∧ (J.pinOn Rp).Adj b s ∧ (J.pinOn Rp).Adj t s ∧
        (s = a ∨ s = b ∨ s = t ∨ (¬ Sym (TF (J.pinOn Rp)) a b s ∧ ¬ Sym (TF (J.pinOn Rp)) a t s ∧
          ¬ Sym (TF (J.pinOn Rp)) b t s ∧ ¬ Sym (TF S) a b s))))
    (hlowB : (∀ a b r, Tetra (J.pinOn Rp) t a b r → ¬ Sym (TF (J.pinOn Rp)) a b r → ¬ Sym (TF S) a b r →
      (∀ τ ∈ (S.pinOn Rp).trios, trioIs a b r τ = false) ∨
      (∀ l, 0 ≤ l → l < J.current_step - 2 →
        ∃ s, s.id.step = l ∧ (s = a ∨ s = b ∨ s = r ∨ s = t ∨ (Wit4 (J.pinOn Rp) t a b r s ∧
          ¬ Sym (TF S) a b s ∧ ¬ Sym (TF S) a r s ∧ ¬ Sym (TF S) b r s))))) :
    (∀ a b, a ≠ t → b ≠ t → a ≠ b → (J.pinOn Rp).Adj t a → (J.pinOn Rp).Adj t b → (J.pinOn Rp).Adj a b →
      ¬ Sym (TF (J.pinOn Rp)) a b t → ∀ l, 0 ≤ l → l < J.current_step →
      ∃ s, s.id.step = l ∧ (J.pinOn Rp).Adj a s ∧ (J.pinOn Rp).Adj b s ∧ (J.pinOn Rp).Adj t s ∧
        (s = a ∨ s = b ∨ s = t ∨ (¬ Sym (TF (J.pinOn Rp)) a b s ∧ ¬ Sym (TF (J.pinOn Rp)) a t s ∧
          ¬ Sym (TF (J.pinOn Rp)) b t s ∧ ¬ Sym (TF S) a b s))) ∧
    (∀ a b r, Tetra (J.pinOn Rp) t a b r → ¬ Sym (TF (J.pinOn Rp)) a b r → ¬ Sym (TF S) a b r →
      (∀ τ ∈ (S.pinOn Rp).trios, trioIs a b r τ = false) ∨
      (∀ l, 0 ≤ l → l < J.current_step →
        ∃ s, s.id.step = l ∧ (s = a ∨ s = b ∨ s = r ∨ s = t ∨ (Wit4 (J.pinOn Rp) t a b r s ∧
          ¬ Sym (TF S) a b s ∧ ¬ Sym (TF S) a r s ∧ ¬ Sym (TF S) b r s)))) := by
  let u := J.pinOn Rp
  have hsub : Sub u J := sub_pinOn J Rp
  have usymm : ∀ {y w}, u.Adj y w → u.Adj w y := fun h => (adj_symm u _ _).mp h
  have htt : u.Adj t t := adj_refl u t ht
  -- un triángulo de `u` con un nodo que no es del otro lado: sin prohibir en `u`, sin prohibir en `S`
  have excl : ∀ {y w e : PathNodeId}, u.Adj y w → u.Adj e y → u.Adj e w → e ∉ O.alive → ¬ Sym (TF u) y w e →
      ¬ Sym (TF S) y w e := by
    intro y w e hyw hey hew heO' hn hs
    apply hn
    refine sym_mono (fun p q x hp hf => ?_) hs
    obtain ⟨h1, h2, h3⟩ := tri_of_perms (R := fun y w => u.Adj y w) usymm hyw (usymm hey) (usymm hew) hp
    have hd := hf.2
    unfold deadTrio at hd
    rw [Bool.and_eq_true] at hd
    obtain ⟨τ, hτ, hti⟩ := List.any_eq_true.mp hd.2
    obtain ⟨npq, npx, nqx⟩ := distinct_of_trioIs hti (hndS τ hτ)
    have hO : SideForbids O (TF O) p q x := by
      left
      intro ⟨k1, k2, _⟩
      apply heO'
      rcases perms_mem3 hp with e' | e' | e'
      · rw [e']; exact (heO p q k1).1
      · rw [e']; exact (heO p q k1).2
      · rw [e']; exact (heO p x k2).2
    exact tF_mono (trios_grow_pinOn J Rp) h1
      (hcut2 (hsub.adj _ _ h1) (hsub.adj _ _ h2) (hsub.adj _ _ h3) npq npx nqx (Or.inr hf) hO)
  -- un vecino de la cima en el paso de los padres no es del otro lado
  have parO : ∀ {s : PathNodeId}, u.Adj t s → s.id.step = J.current_step - 2 → s ∉ O.alive := by
    intro s hs hstep
    have hS : S.Adj t s := (hadj t s (hsub.adj _ _ hs)).resolve_right (fun ho => htO (heO t s ho).1)
    exact hex s hstep (heS t s hS).2
  refine ⟨?_, ?_⟩
  · intro a b hat hbt nab hta htb hab hf l h0 h1
    by_cases hl : l < J.current_step - 2
    · exact hlowF a b hat hbt nab hta htb hab hf l h0 hl
    by_cases hl1 : l = J.current_step - 1
    · exact ⟨t, by rw [hts, hl1], usymm hta, usymm htb, htt, Or.inr (Or.inr (Or.inl rfl))⟩
    have hl2 : l = J.current_step - 2 := by omega
    obtain ⟨s, hsl, has, hbs, hts', hw⟩ := fix_witness hJ hnsJ hndJ hv hab (usymm hta) (usymm htb) nab hat hbt hf
      l h0 h1
    refine ⟨s, hsl, has, hbs, hts', ?_⟩
    rcases hw with e | e | e | ⟨n1, n2, n3⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr ⟨n1, n2, n3,
        excl hab (usymm has) (usymm hbs) (parO hts' (by rw [hsl, hl2])) n1⟩))
  · intro a b r htet hnU hnS
    rcases hlowB a b r htet hnU hnS with hk | hw
    · exact Or.inl hk
    right
    intro l h0 h1
    by_cases hl : l < J.current_step - 2
    · exact hw l h0 hl
    by_cases hl1 : l = J.current_step - 1
    · exact ⟨t, by rw [hts, hl1], Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    have hl2 : l = J.current_step - 2 := by omega
    by_cases ca : a.id.step = l
    · exact ⟨a, ca, Or.inl rfl⟩
    by_cases cb : b.id.step = l
    · exact ⟨b, cb, Or.inr (Or.inl rfl)⟩
    by_cases cr : r.id.step = l
    · exact ⟨r, cr, Or.inr (Or.inr (Or.inl rfl))⟩
    have htet' := htet
    obtain ⟨nat, nbt, nrt, _, _, _, hta, htb, htr, hab, har, hbr, _⟩ := htet
    have ha : a.id.step < J.current_step - 2 := by have := hbelow a hta nat; omega
    have hb : b.id.step < J.current_step - 2 := by have := hbelow b htb nbt; omega
    have hr : r.id.step < J.current_step - 2 := by have := hbelow r htr nrt; omega
    obtain ⟨m1, m2, m3⟩ := hns a b r htet' hnU ha hb hr
    rcases hdich a b r htet' ha hb hr with ⟨s, hs, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩ | hsp | hsp | hsp
    · have hsl : s.id.step = l := by rw [hts] at hs; omega
      have hsO := parO k1 (by rw [hsl, hl2])
      exact ⟨s, hsl, Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩,
        excl hab (usymm k2) (usymm k3) hsO k8, excl har (usymm k2) (usymm k4) hsO k9,
        excl hbr (usymm k3) (usymm k4) hsO k10⟩)))⟩
    · exact absurd hsp m1
    · exact absurd hsp m2
    · exact absurd hsp m3

/-- **`StarDAt` sale de su parte baja y de que no haya padres complementarios sobre bases vivas**, en los dos lados
de un join de la máquina. Lo que `StarDAt` añade a `Star4At` (esquivar las bases prohibidas en el lado) solo tiene
contenido por debajo del paso de los padres. -/
theorem starDAt_of_low_noSplit {φ : Cnf} {T : Int} {L0 : Line} (hT : 1 ≤ T) (h0 : LInvTop φ T L0)
    (hbk0 : LineBk L0) (h1 : LInvTop φ (T + 1) (advanceM .on φ L0)) (hbk1 : LineBk (advanceM .on φ L0))
    (h2 : LInvTop φ (T + 1 + 1) (advanceM .on φ (advanceM .on φ L0)))
    (hbk2 : LineBk (advanceM .on φ (advanceM .on φ L0)))
    {a b : NodeId × GPathB} (ha : a ∈ advanceM .on φ (advanceM .on φ L0))
    (hb : b ∈ advanceM .on φ (advanceM .on φ L0)) (hab : a.1 ≠ b.1) {d : NodeId} (hsa : SendsOn φ a d)
    (hsb : SendsOn φ b d) {R : List NodeId}
    (hlA : StarDLowAt (arrOn φ a d) (joinOn (arrOn φ a d) (arrOn φ b d)) R)
    (hlB : StarDLowAt (arrOn φ b d) (joinOn (arrOn φ a d) (arrOn φ b d)) R)
    (hns : NoParSplitAt (joinOn (arrOn φ a d) (arrOn φ b d)) R) :
    StarDAt (arrOn φ a d) (joinOn (arrOn φ a d) (arrOn φ b d)) R ∧
    StarDAt (arrOn φ b d) (joinOn (arrOn φ a d) (arrOn φ b d)) R := by
  have hT2 : (1 : Int) ≤ T + 1 + 1 := by omega
  obtain ⟨ea, ia, na, _, _⟩ := arrTop_facts hT2 h2 ha hsa
  obtain ⟨eb, ib, nb, _, _⟩ := arrTop_facts hT2 h2 hb hsb
  have hcs : (arrOn φ a d).current_step = (arrOn φ b d).current_step := ea.1.step.trans eb.1.step.symm
  have hJ : SInvB (joinOn (arrOn φ a d) (arrOn φ b d)) := sInvB_joinOn ia ib hcs
  have hnsJ : NoSelf (joinOn (arrOn φ a d) (arrOn φ b d)) := noSelf_joinOn ea.2.1 eb.2.1
  have hndJ : NoDegT (joinOn (arrOn φ a d) (arrOn φ b d)) := noDegT_joinOn ea.2.1 eb.2.1 ia.edges ib.edges
  have hcsJ : (joinOn (arrOn φ a d) (arrOn φ b d)).current_step = T + 1 + 1 + 1 := by
    rw [step_joinOn]; exact ea.1.step
  obtain ⟨T', hT'e⟩ := joinOn_eq (arrOn φ a d) (arrOn φ b d)
  have hadj : ∀ x w, (joinOn (arrOn φ a d) (arrOn φ b d)).Adj x w →
      (arrOn φ a d).Adj x w ∨ (arrOn φ b d).Adj x w := fun x w h => by
    rw [hT'e] at h; exact adj_join_cases h
  obtain ⟨fa, _⟩ := arrOn_tops hT2 (h2.on a ha) (hbk2 a ha).1 hsa
  obtain ⟨fb, _⟩ := arrOn_tops hT2 (h2.on b hb) (hbk2 b hb).1 hsb
  have hsep : ∀ t : PathNodeId, t.id.step = (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 1 →
      t ∈ (arrOn φ a d).alive → t ∈ (arrOn φ b d).alive → False := by
    intro t hts k1 k2
    obtain ⟨x, hx, hp⟩ := fa t k1 (by rw [ea.1.step, hts, hcsJ])
    obtain ⟨y, hy, hp'⟩ := fb t k2 (by rw [eb.1.step, hts, hcsJ])
    rw [hp, hx, hy] at hp'
    exact hab (Option.some.inj hp')
  -- los nodos del paso de los padres son de un solo lado
  have keyOf : ∀ kv ∈ advanceM .on φ (advanceM .on φ L0), ∀ s : PathNodeId, s.id.step = T + 1 → s ∈ kv.2.alive →
      s.id = kv.1 := by
    intro kv hkv s hss hs
    obtain ⟨n, hn', hnid⟩ := (h2.inv kv hkv).docs s hs
    have := (hbk2 kv hkv).1 n hn' (by rw [hnid, (h2.on kv hkv).1.step, hss]; omega)
    rw [hnid] at this
    exact this
  have hexc : ∀ s : PathNodeId, s.id.step = (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 2 →
      s ∈ (arrOn φ a d).alive → s ∈ (arrOn φ b d).alive → False := by
    intro s hss k1 k2
    have hs' : s.id.step = T + 1 := by rw [hss, hcsJ]; omega
    exact hab ((keyOf a ha s hs' (arrOn_alive_old (h2.on a ha) (h2.inv a ha) hsa (by omega) k1)).symm.trans
      (keyOf b hb s hs' (arrOn_alive_old (h2.on b hb) (h2.inv b hb) hsb (by omega) k2)))
  -- los vecinos de una cima están por debajo de ella
  obtain ⟨_, ta⟩ := arrOn_adjPar (h2.on a ha) (h2.inv a ha) (hbk2 a ha).2.1 (hbk2 a ha).2.2 hsa
  obtain ⟨_, tb⟩ := arrOn_adjPar (h2.on b hb) (h2.inv b hb) (hbk2 b hb).2.1 (hbk2 b hb).2.2 hsb
  have htaJ : TopsApart (joinOn (arrOn φ a d) (arrOn φ b d)) := by
    rw [hT'e]; exact topsApart_setT (topsApart_join ta tb hcs) T'
  have hiu := sInvB_pinOn hJ R
  have below : ∀ {t : PathNodeId}, t.id.step = (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 1 →
      ∀ q, ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj t q → q ≠ t →
      q.id.step < (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 1 := by
    intro t hts q hq hne
    have hb1 := alive_below hiu.docs hiu.below (hiu.edges t q hq).2
    rw [step_pinOn] at hb1
    have hb2 : q.id.step ≠ (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 1 := fun e =>
      hne (htaJ t q hts e ((sub_pinOn _ R).adj _ _ hq)).symm
    omega
  have dich : ∀ {t : PathNodeId}, t.id.step = (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 1 →
      ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).isValid = true → ∀ x y z,
      Tetra ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t x y z →
      x.id.step < (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 2 →
      y.id.step < (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 2 →
      z.id.step < (joinOn (arrOn φ a d) (arrOn φ b d)).current_step - 2 →
      (∃ s, s.id.step + 1 = t.id.step ∧ Wit4 ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t x y z s) ∨
        ParSplitAt ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t x y z ∨
        ParSplitAt ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t y x z ∨
        ParSplitAt ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) t z x y := by
    intro t hts hv x y z htet hx hy hz
    rw [hcsJ] at hx hy hz
    exact tetra_parent_or_split hT h0 hbk0 h1 hbk1 h2 hbk2 ha hb hab hsa hsb hv hts htet (by omega) (by omega)
      (by omega)
  constructor
  · intro hv t ht hts htA
    obtain ⟨lf, lb⟩ := hlA hv t ht hts htA
    exact starD_of_low (S := arrOn φ a d) (O := arrOn φ b d) hJ hnsJ hndJ hv na ia.edges hadj ib.edges
      (fun hxy hxz hyz nxy nxz nyz s1 s2 => tF_joinOn_of_cut ia.edges ib.edges hxy hxz hyz nxy nxz nyz s1 s2)
      ht hts (fun h => hsep t hts htA h) (fun s hss k1 k2 => hexc s hss k1 k2) (below hts) (dich hts hv)
      (fun x y z htet hnU hx hy hz => hns hv t ht hts x y z htet hnU hx hy hz) lf lb
  · intro hv t ht hts htB
    obtain ⟨lf, lb⟩ := hlB hv t ht hts htB
    exact starD_of_low (S := arrOn φ b d) (O := arrOn φ a d) hJ hnsJ hndJ hv nb ib.edges
      (fun x w h => (hadj x w h).symm) ia.edges
      (fun hxy hxz hyz nxy nxz nyz s2 s1 => tF_joinOn_of_cut ia.edges ib.edges hxy hxz hyz nxy nxz nyz s1 s2)
      ht hts (fun h => hsep t hts h htB) (fun s hss k2 k1 => hexc s hss k1 k2) (below hts) (dich hts hv)
      (fun x y z htet hnU hx hy hz => hns hv t ht hts x y z htet hnU hx hy hz) lf lb

-- ============================================================
-- De dónde sale una base que revive
-- ============================================================

/-- **Una base que revive es un triángulo sin prohibir del otro lado.** Si un triángulo de la unión `J` está prohibido
en el lado `S` y no en `J`, el otro lado `O` tiene sus tres aristas y no lo tiene prohibido: el join solo deja caer
un trío de un lado cuando el otro lado lo tiene vivo. -/
theorem revive_other {J S O : GPathB}
    (hcut2 : ∀ {x y z}, J.Adj x y → J.Adj x z → J.Adj y z → x ≠ y → x ≠ z → y ≠ z → SideForbids S (TF S) x y z →
      SideForbids O (TF O) x y z → TF J x y z)
    {x y z : PathNodeId} (hxy : J.Adj x y) (hxz : J.Adj x z) (hyz : J.Adj y z) (nxy : x ≠ y) (nxz : x ≠ z)
    (nyz : y ≠ z) (hS : TF S x y z) (hn : ¬ TF J x y z) :
    O.Adj x y ∧ O.Adj x z ∧ O.Adj y z ∧ ¬ TF O x y z := by
  have hO : ¬ SideForbids O (TF O) x y z := fun h => hn (hcut2 hxy hxz hyz nxy nxz nyz (Or.inr hS) h)
  have hadj : O.Adj x y ∧ O.Adj x z ∧ O.Adj y z := by
    apply Classical.byContradiction
    intro hno
    exact hO (Or.inl hno)
  exact ⟨hadj.1, hadj.2.1, hadj.2.2, fun h => hO (Or.inr h)⟩

/-- **Un triángulo viejo sin prohibir de una llegada es un triángulo sin prohibir de su remitente**: la llegada no gana
aristas viejas y sus tríos crecen. -/
theorem open_sender_of_arr {φ : Cnf} {T : Int} {kv : NodeId × GPathB} (hent : EntOn T kv.1 kv.2) {d : NodeId}
    (hs : SendsOn φ kv d) {x y z : PathNodeId} (hx : x.id.step < T) (hy : y.id.step < T) (hz : z.id.step < T)
    (hxy : (arrOn φ kv d).Adj x y) (hxz : (arrOn φ kv d).Adj x z) (hyz : (arrOn φ kv d).Adj y z)
    (hn : ¬ TF (arrOn φ kv d) x y z) : kv.2.Adj x y ∧ kv.2.Adj x z ∧ kv.2.Adj y z ∧ ¬ TF kv.2 x y z := by
  refine ⟨arrOn_adj_old hent hs hx hy hxy, arrOn_adj_old hent hs hx hz hxz, arrOn_adj_old hent hs hy hz hyz, ?_⟩
  intro hf
  apply hn
  exact tF_mono (g := kv.2) (h := (kv.2.filterAllOn (reqOf φ d)).upOn d "" (isProhibited φ))
    (fun t ht => trios_grow_upOn _ d "" (isProhibited φ) t (trios_grow_filterAllOn kv.2 (reqOf φ d) t ht)) hxy hf

/-- **En la máquina: una base que revive en la unión fijada está sin prohibir en la entrada que envía la otra
llegada.** La base está prohibida en la llegada de `a`, viva en la unión fijada de las llegadas de `a` y `b`, y sus
nodos son de la línea de `a` y `b` (por debajo de sus cimas no hace falta: basta que sean viejos): entonces `b` la
tiene como triángulo sin prohibir. Es un desacuerdo de tríos entre las dos entradas de la línea. -/
theorem revive_sender_open {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvTop φ T line)
    {a b : NodeId × GPathB} (ha : a ∈ line) (hb : b ∈ line) {d : NodeId} (hsa : SendsOn φ a d)
    (hsb : SendsOn φ b d) {R : List NodeId} {x y z : PathNodeId} (hx : x.id.step < T) (hy : y.id.step < T)
    (hz : z.id.step < T) (nxy : x ≠ y) (nxz : x ≠ z) (nyz : y ≠ z)
    (hxy : ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj x y)
    (hxz : ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj x z)
    (hyz : ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R).Adj y z)
    (hS : TF (arrOn φ a d) x y z) (hn : ¬ TF ((joinOn (arrOn φ a d) (arrOn φ b d)).pinOn R) x y z) :
    b.2.Adj x y ∧ b.2.Adj x z ∧ b.2.Adj y z ∧ ¬ TF b.2 x y z := by
  obtain ⟨_, ia, _, _, _⟩ := arrTop_facts hT h ha hsa
  obtain ⟨_, ib, _, _, _⟩ := arrTop_facts hT h hb hsb
  have hsub := sub_pinOn (joinOn (arrOn φ a d) (arrOn φ b d)) R
  have hnJ : ¬ TF (joinOn (arrOn φ a d) (arrOn φ b d)) x y z := fun hf =>
    hn (tF_mono (trios_grow_pinOn _ R) hxy hf)
  obtain ⟨o1, o2, o3, o4⟩ := revive_other (S := arrOn φ a d) (O := arrOn φ b d)
    (fun k1 k2 k3 n1 n2 n3 s1 s2 => tF_joinOn_of_cut ia.edges ib.edges k1 k2 k3 n1 n2 n3 s1 s2)
    (hsub.adj _ _ hxy) (hsub.adj _ _ hxz) (hsub.adj _ _ hyz) nxy nxz nyz hS hnJ
  exact open_sender_of_arr (h.on b hb) hsb hx hy hz o1 o2 o3 o4

-- ============================================================
-- El veredicto desde la parte baja
-- ============================================================

/-- **La parte baja de `StarDAt` y la ausencia de padres complementarios**, en los joins de una línea. -/
def HStarDLowOn (φ : Cnf) (line : Line) : Prop :=
  ∀ a ∈ line, ∀ b ∈ line, a.1 ≠ b.1 → ∀ d, SendsOn φ a d → SendsOn φ b d → ∀ R, PinsFrom φ d R →
    StarDLowAt (arrOn φ a d) (joinOn (arrOn φ a d) (arrOn φ b d)) R ∧
    StarDLowAt (arrOn φ b d) (joinOn (arrOn φ a d) (arrOn φ b d)) R ∧
    NoParSplitAt (joinOn (arrOn φ a d) (arrOn φ b d)) R

theorem hStarDOn_of_low {φ : Cnf} {T : Int} {L0 : Line} (hT : 1 ≤ T) (h0 : LInvTop φ T L0) (hbk0 : LineBk L0)
    (h1 : LInvTop φ (T + 1) (advanceM .on φ L0)) (hbk1 : LineBk (advanceM .on φ L0))
    (h2 : LInvTop φ (T + 1 + 1) (advanceM .on φ (advanceM .on φ L0)))
    (hbk2 : LineBk (advanceM .on φ (advanceM .on φ L0)))
    (hp : HStarDLowOn φ (advanceM .on φ (advanceM .on φ L0))) :
    HStarDOn φ (advanceM .on φ (advanceM .on φ L0)) := by
  intro a ha b hb hab d hsa hsb R hR
  obtain ⟨lA, lB, ns⟩ := hp a ha b hb hab d hsa hsb R hR
  exact starDAt_of_low_noSplit hT h0 hbk0 h1 hbk1 h2 hbk2 ha hb hab hsa hsb lA lB ns

/-- **Las hipótesis desde la parte baja**: `StarDAt` entera en las dos primeras líneas (no tienen dos líneas detrás),
y en las demás su parte por debajo del paso de los padres y la ausencia de padres complementarios sobre bases vivas. -/
def HypsStarDLowOn (φ : Cnf) : Prop :=
  HStarDOn φ (initM .on φ) ∧ HStarDOn φ (advanceM .on φ (initM .on φ)) ∧
  ∀ n : Nat, HStarDLowOn φ (advanceM .on φ (advanceM .on φ (stepsM .on φ n (initM .on φ))))

/-- La inducción de línea bajo `HypsStarDLowOn`: el invariante y la contabilidad de tres líneas seguidas, y
`TopSideAt` en los joins de las dos primeras. -/
theorem lInvStarDLow_steps {φ : Cnf} (H : HypsStarDLowOn φ) :
    ∀ n : Nat, LInvTop φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) ∧ LineBk (stepsM .on φ n (initM .on φ)) ∧
      LInvTop φ ((n : Int) + 1 + 1) (advanceM .on φ (stepsM .on φ n (initM .on φ))) ∧
      LineBk (advanceM .on φ (stepsM .on φ n (initM .on φ))) ∧
      LInvTop φ ((n : Int) + 1 + 1 + 1) (advanceM .on φ (advanceM .on φ (stepsM .on φ n (initM .on φ)))) ∧
      LineBk (advanceM .on φ (advanceM .on φ (stepsM .on φ n (initM .on φ)))) ∧
      HTopOn φ (stepsM .on φ n (initM .on φ)) ∧ HTopOn φ (advanceM .on φ (stepsM .on φ n (initM .on φ))) := by
  intro n
  induction n with
  | zero =>
    have hl0 := lInvTop_init φ
    have hbk0 := lineBk_init φ
    have hT : (1 : Int) ≤ 1 := by omega
    have hT1 : (1 : Int) ≤ 1 + 1 := by omega
    have ht0 := hTopOn_of_starD hT hl0 hbk0 H.1
    have hl1 := lInvTop_advance hT hl0 ht0
    have hbk1 := lineBk_advance hT hl0 hbk0
    have ht1 := hTopOn_of_starD hT1 hl1 hbk1 H.2.1
    exact ⟨hl0, hbk0, hl1, hbk1, lInvTop_advance hT1 hl1 ht1, lineBk_advance hT1 hl1 hbk1, ht0, ht1⟩
  | succ n ih =>
    obtain ⟨hl0, hbk0, hl1, hbk1, hl2, hbk2, _, ht1⟩ := ih
    have hT : (1 : Int) ≤ (n : Int) + 1 := by omega
    have hT2 : (1 : Int) ≤ (n : Int) + 1 + 1 + 1 := by omega
    have ht2 := hTopOn_of_starD hT2 hl2 hbk2 (hStarDOn_of_low hT hl0 hbk0 hl1 hbk1 hl2 hbk2 (H.2.2 n))
    have hl3 := lInvTop_advance hT2 hl2 ht2
    have hbk3 := lineBk_advance hT2 hl2 hbk2
    have hcast : ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 := by push_cast; omega
    rw [stepsM_succ, hcast]
    exact ⟨hl1, hbk1, hl2, hbk2, hl3, hbk3, ht1, ht2⟩

theorem hypsTopOn_of_starDLow {φ : Cnf} (H : HypsStarDLowOn φ) : HypsTopOn φ :=
  fun n => (lInvStarDLow_steps H n).2.2.2.2.2.2.1

end GPathB

namespace MachineOn

open GPathB Driver

/-- **El veredicto sin corte cruzado**: la espina `:on` decide la satisfacibilidad bajo `StarDAt` en los joins de la
máquina. La familia de cada cima de la unión fijada lleva como tríos los de la unión y las bases prohibidas en su
lado; la hipótesis pide que sus testigos las esquiven. No pide que la unión prohíba lo que prohíbe un lado
(`CrossCut`, falso en `v7`). -/
theorem spineVerdictOn_iff_of_starD {φ : Cnf} (hbd : Bounded φ) (H : HypsStarDOn φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_topOn hbd (hypsTopOn_of_starD H)

/-- **El veredicto desde la parte baja**: la espina `:on` decide la satisfacibilidad si, en los joins de la máquina
desde la tercera línea, vale `StarDAt` por debajo del paso de los padres de cada cima y no hay padres complementarios
sobre bases vivas (en las dos primeras líneas, `StarDAt` entera). El paso de los padres está demostrado
(`starD_of_low`). -/
theorem spineVerdictOn_iff_of_starDLow {φ : Cnf} (hbd : Bounded φ) (H : HypsStarDLowOn φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_topOn hbd (hypsTopOn_of_starDLow H)

end MachineOn

end AbsSatBingo.Model
