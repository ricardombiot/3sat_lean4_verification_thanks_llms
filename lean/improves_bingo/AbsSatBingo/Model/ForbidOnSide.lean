-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnSide.lean
import AbsSatBingo.Model.ForbidOnGood
import AbsSatBingo.Model.UnionEquiv

/-!
# El recíproco de `PinSideAt`, sin hipótesis: un lado fijado vive entero en la unión fijada

Sea `s = pinOn g R` un lado fijado y válido, y `J` un estado que contiene a `g` (la unión). Entonces `s` entero es una
estructura cerrada de `pinOn J R`, y los tríos de `pinOn J R` sobre sus triángulos están entre los de `s`
(`downInv_side`). Es la técnica de la dirección 2 de la llegada: `s` salió del review en el punto fijo de la regla, así
que tiene testigos buenos (`trioGood_low`), y el review de `J` fijado no puede cortar nada suyo (`downInv_reviewOn`).

De ahí, para el join (`liveChain_side_left/right`): **toda cadena viva de `pinOn A R` o de `pinOn B R` es cadena viva
de `pinOn (joinOn A B) R`**, y la unión fijada es válida si lo es un lado. Lo único que el join `:on` tiene que
aportar es que los tríos que guarda los cortan los dos lados (`mem_joinForbid`).

Con esto, `PinSideAt` (la hipótesis de `spineVerdictOn_iff_of_joinOn`) dice exactamente que las cadenas vivas de la
unión fijada son las de sus dos lados fijados (`pinSideAt_iff`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

/-- Un estado cerrado, con sus vivos por debajo de `c`, es su propia parte baja. -/
theorem closed_low {s : GPathB} {c : Int} (hcl : ClosedState s) (hb : ∀ q ∈ s.alive, q.id.step < c) :
    SecStruct s (LowV s c) (LowR s c) := by
  have up : ∀ {y w}, (y ∈ s.alive ∧ w ∈ s.alive ∧ s.Adj y w) → LowR s c y w :=
    fun h => ⟨h, hb _ h.1, hb _ h.2.1⟩
  refine ⟨fun hy => hy.1, fun hy => up (hcl.refl hy.1), fun hr => up (hcl.symm hr.1),
    fun hr => ⟨⟨hr.1.1, hr.2.1⟩, ⟨hr.1.2.1, hr.2.2⟩⟩, fun hr => hr.1.2.2, ?_, ?_, ?_, ?_⟩
  · intro y w hr l h0 h1
    obtain ⟨r, hrl, h1', h2'⟩ := hcl.pair hr.1 l h0 h1
    exact ⟨r, hrl, up h1', up h2'⟩
  · intro y hy
    obtain ⟨n, hn, hp, hs⟩ := hcl.node hy.1
    exact ⟨n, hn, fun h => (hp h).imp fun p hp' => ⟨hp'.1, up hp'.2⟩,
      fun h => (hs h).imp fun p hp' => ⟨hp'.1, up hp'.2⟩⟩
  · intro x w n hr hne hn h1
    obtain ⟨p, hp, h1', h2'⟩ := hcl.par hr.1 hne hn h1
    exact ⟨p, hp, up h1', up h2'⟩
  · intro x w n hr hne hn h1
    obtain ⟨p, hp, h1', h2'⟩ := hcl.son hr.1 hne hn h1
    exact ⟨p, hp, up h1', up h2'⟩

/-- **Una cadena viva de `s` es cadena viva de `x`**, si la parte baja de `s` (aquí, `s` entero) cumple el invariante
en `x`. -/
theorem liveChain_of_downInv {s x : GPathB} {c : Int} (hX : DownInv (LowV s c) (LowR s c) (TF s) c x)
    (hliX : LinksInv x) (hlis : LinksInv s) (hcs : s.current_step = c) (hb : ∀ q ∈ s.alive, q.id.step < c)
    {C : Int → PathNodeId} {j : Int} (hC : LiveChain s (TF s) C j) : LiveChain x (TF x) C j := by
  have hsymm : ∀ {y w}, LowR s c y w → LowR s c w y :=
    fun hr => ⟨⟨hr.1.2.1, hr.1.1, (adj_symm s _ _).mp hr.1.2.2⟩, hr.2.2, hr.2.1⟩
  have hcsX : x.current_step = c := hX.step
  have hlow : ∀ k, j ≤ k → k ≤ c - 1 → LowV s c (C k) := fun k h1 h2 =>
    ⟨(hC.chain.node k h1 (by rw [hcs]; exact h2)).2, hb _ (hC.chain.node k h1 (by rw [hcs]; exact h2)).2⟩
  have hlowR : ∀ k l, j ≤ k → k ≤ c - 1 → j ≤ l → l ≤ c - 1 → LowR s c (C k) (C l) := fun k l h1 h2 h3 h4 =>
    ⟨⟨(hlow k h1 h2).1, (hlow l h3 h4).1, hC.chain.adj k l h1 (by rw [hcs]; exact h2) h3 (by rw [hcs]; exact h4)⟩,
      (hlow k h1 h2).2, (hlow l h3 h4).2⟩
  refine ⟨⟨fun k h1 h2 => ?_, fun k l h1 h2 h3 h4 => ?_, fun k h1 h2 => ?_⟩, fun a b c' ha hab hbc hc hs => ?_⟩
  · rw [hcsX] at h2
    exact ⟨(hC.chain.node k h1 (by rw [hcs]; exact h2)).1, hX.sec.alive (hlow k h1 h2)⟩
  · rw [hcsX] at h2 h4
    exact hX.sec.adj (hlowR k l h1 h2 h3 h4)
  · rw [hcsX] at h2
    have hk := hlow k (by omega) h2
    have hk1 := hlow (k - 1) (by omega) (by omega)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hliX.1 (hX.sec.alive hk))
    refine ⟨n, hn, ?_⟩
    obtain ⟨m, hm, hpm⟩ := hC.chain.link k h1 (by rw [hcs]; exact h2)
    have hcomp := (hlis.2.2 m (node?_mem hm)).1 _ hpm
    rw [node?_id hm] at hcomp
    have hadj : x.Adj n.id (C (k - 1)) := by
      rw [node?_id hn]; exact hX.sec.adj (hlowR k (k - 1) (by omega) h2 (by omega) (by omega))
    exact (hliX.2.1 n (node?_mem hn) (C (k - 1)) (hX.sec.alive hk1) hadj).1 (by rw [node?_id hn]; exact hcomp)
  · rw [hcsX] at hc
    apply hC.live a b c' ha hab hbc (by rw [hcs]; exact hc)
    have ab := hlowR a b ha (by omega) (by omega) (by omega)
    have ac := hlowR a c' ha (by omega) (by omega) hc
    have bc := hlowR b c' (by omega) (by omega) (by omega) hc
    have tri := fun {p q w} (hpq : LowR s c p q) (hpw : LowR s c p w) (hqw : LowR s c q w)
      (hf : TF x p q w) => hX.tri hpq hpw hqw hf
    unfold Sym at hs ⊢
    rcases hs with hf | hf | hf | hf | hf | hf
    · exact Or.inl (tri ab ac bc hf)
    · exact Or.inr (Or.inl (tri ac ab (hsymm bc) hf))
    · exact Or.inr (Or.inr (Or.inl (tri (hsymm ab) bc ac hf)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (tri bc (hsymm ab) (hsymm ac) hf))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (tri (hsymm ac) (hsymm bc) ab hf)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (tri (hsymm bc) (hsymm ac) (hsymm ab) hf)))))

/-- **Un lado fijado vive entero en el estado mayor fijado.** `J` contiene las estructuras de `g`, y todo trío de `J`
sobre un triángulo de `g` lo corta `g` en algún orden. -/
theorem downInv_side_gen {g J : GPathB} {R R' : List NodeId} (hRR : ∀ p ∈ R, p ∈ R') (hg : SInvB g) (hns : NoSelf g)
    (hnd : NoDegT g) (hcs2 : 2 ≤ g.current_step) (hv : (g.pinOn R').isValid = true)
    (hJstep : J.current_step = g.current_step) (hJns : NoSelf J)
    (hJsec : ∀ {V : PathNodeId → Prop} {Rr : PathNodeId → PathNodeId → Prop}, SecStruct g V Rr → SecStruct J V Rr)
    (hJtri : ∀ {a b r}, g.Adj a b → g.Adj a r → g.Adj b r → TF J a b r →
      ∃ p q w, (p, q, w) ∈ perms a b r ∧ TF g p q w) :
    DownInv (LowV (g.pinOn R') g.current_step) (LowR (g.pinOn R') g.current_step) (TF (g.pinOn R')) g.current_step
      (J.pinOn R) := by
  let s := g.pinOn R'
  let c := g.current_step
  have hcss : s.current_step = c := step_pinOn g R'
  have his : SInvB s := sInvB_pinOn hg R'
  have hbs : ∀ q ∈ s.alive, q.id.step < c := fun q hq => by
    have := alive_below his.docs his.below hq; rw [hcss] at this; exact this
  have hcl : ClosedState s := closedState_pinOn hg hv hcs2
  have hfix : FixClosed s := fixClosed_reviewOn (g := { R'.foldl filterRequire g with dirty := true }) rfl hv
  have hTG : TrioGood (LowV s c) (LowR s c) (TF s) c :=
    trioGood_low hfix (noDegT_pinOn hns hnd R') (by rw [hcss]; exact Int.le_refl _)
  have hsymm : ∀ {y w}, LowR s c y w → LowR s c w y :=
    fun hr => ⟨⟨hr.1.2.1, hr.1.1, (adj_symm s _ _).mp hr.1.2.2⟩, hr.2.2, hr.2.1⟩
  have hsub : Sub s g := sub_pinOn g R'
  have hsec : SecStruct J (LowV s c) (LowR s c) := hJsec (secStruct_of_sub hsub hg.nodup (closed_low hcl hbs))
  have h0 : DownInv (LowV s c) (LowR s c) (TF s) c J := by
    refine ⟨hsec, hJns, hJstep, ?_⟩
    intro a b r hab har hbr hf
    obtain ⟨p, q, w, hp, ht⟩ := hJtri (hsub.adj _ _ hab.1.2.2) (hsub.adj _ _ har.1.2.2) (hsub.adj _ _ hbr.1.2.2) hf
    obtain ⟨hpq, _, _⟩ := tri_of_perms (R := LowR s c) hsymm hab har hbr hp
    exact trioGood_perm hTG hsymm hab har hbr hp (tF_mono (trios_grow_pinOn g R') hpq.1.2.2 ht)
  have hagree : ∀ p ∈ R, SecAgrees (LowV s c) p := fun p hp q hq hqs =>
    pinned_pinOn hg.docs hv p (hRR p hp) q hq.1 hqs
  have hfold : ∀ (l : List NodeId) (x : GPathB), (∀ p ∈ l, SecAgrees (LowV s c) p) →
      DownInv (LowV s c) (LowR s c) (TF s) c x → DownInv (LowV s c) (LowR s c) (TF s) c (l.foldl filterRequire x) := by
    intro l
    induction l with
    | nil => intro x _ hx; exact hx
    | cons p ps ih =>
      intro x hl hx
      rw [List.foldl_cons]
      exact ih _ (fun p' hp' => hl p' (List.mem_cons_of_mem _ hp')) (downInv_filterRequire hx (hl p List.mem_cons_self))
  have h1 := hfold _ J hagree h0
  have h2 : DownInv (LowV s c) (LowR s c) (TF s) c { R.foldl filterRequire J with dirty := true } :=
    downInv_shrink h1 (shrinks_dirty _ true).1 rfl (sec_dirty h1.sec true) h1.ns
  exact downInv_reviewOn h2 hTG hsymm

theorem downInv_side {g J : GPathB} {R : List NodeId} (hg : SInvB g) (hns : NoSelf g) (hnd : NoDegT g)
    (hcs2 : 2 ≤ g.current_step) (hv : (g.pinOn R).isValid = true)
    (hJstep : J.current_step = g.current_step) (hJns : NoSelf J)
    (hJsec : ∀ {V : PathNodeId → Prop} {Rr : PathNodeId → PathNodeId → Prop}, SecStruct g V Rr → SecStruct J V Rr)
    (hJtri : ∀ {a b r}, g.Adj a b → g.Adj a r → g.Adj b r → TF J a b r →
      ∃ p q w, (p, q, w) ∈ perms a b r ∧ TF g p q w) :
    DownInv (LowV (g.pinOn R) g.current_step) (LowR (g.pinOn R) g.current_step) (TF (g.pinOn R)) g.current_step
      (J.pinOn R) :=
  downInv_side_gen (fun _ h => h) hg hns hnd hcs2 hv hJstep hJns hJsec hJtri

/-- **Más pins, menos cadenas vivas**: con `R ⊆ R'`, el estado fijado en `R'` (válido) vive entero en el fijado en
`R`, y toda cadena viva suya lo es del fijado en `R`. Sin hipótesis. -/
theorem liveChain_pin_mono {g : GPathB} {R R' : List NodeId} (hRR : ∀ p ∈ R, p ∈ R') (hg : SInvB g) (hns : NoSelf g)
    (hnd : NoDegT g) (hcs2 : 2 ≤ g.current_step) (hv : (g.pinOn R').isValid = true)
    {C : Int → PathNodeId} {j : Int} (hC : LiveChain (g.pinOn R') (TF (g.pinOn R')) C j) :
    (g.pinOn R).isValid = true ∧ LiveChain (g.pinOn R) (TF (g.pinOn R)) C j := by
  have his := sInvB_pinOn hg R'
  have hb : ∀ q ∈ (g.pinOn R').alive, q.id.step < g.current_step := fun q hq => by
    have := alive_below his.docs his.below hq; rw [step_pinOn] at this; exact this
  have hX : DownInv (LowV (g.pinOn R') g.current_step) (LowR (g.pinOn R') g.current_step) (TF (g.pinOn R'))
      g.current_step (g.pinOn R) :=
    downInv_side_gen hRR hg hns hnd hcs2 hv rfl hns (fun h => h)
      (fun {a b r} _ _ _ hf => ⟨a, b, r, by simp [perms], hf⟩)
  obtain ⟨q, hq, _⟩ := exists_alive_at hv (k := 0) (Int.le_refl 0) (by rw [step_pinOn]; omega)
  exact ⟨isValid_of_sec hX.sec (y := q) ⟨hq, hb q hq⟩,
    liveChain_of_downInv hX (sInvB_pinOn hg R).links his.links (step_pinOn g R') hb hC⟩

/-- Un trío de la unión `:on` lo cortan los dos lados; sobre un triángulo de un lado, ese lado lo tiene prohibido. -/
theorem tF_joinOn_side {A B : GPathB} (hnsA : NoSelf A) (hnsB : NoSelf B) (heA : EdgesAlive A) (heB : EdgesAlive B)
    {a b r : PathNodeId} (hf : TF (joinOn A B) a b r) :
    ∃ p q w, (p, q, w) ∈ perms a b r ∧ SideForbids A (TF A) p q w ∧ SideForbids B (TF B) p q w := by
  obtain ⟨_, hd⟩ := hf
  unfold deadTrio at hd
  rw [Bool.and_eq_true] at hd
  obtain ⟨t, ht, hti⟩ := List.any_eq_true.mp hd.2
  rcases mem_addTrios ({ join A B with trios := [] } : GPathB) _ _ t ht with h | h
  · exact absurd h List.not_mem_nil
  · obtain ⟨dt, _⟩ := joinForbid_facts hnsA hnsB heA heB h
    obtain ⟨f1, f2⟩ := mem_joinForbid h
    exact ⟨t.1, t.2.1, t.2.2, (trioIs_iff_perms a b r t).mp hti, sideForbids_of_B dt.1 dt.2.1 dt.2.2 f1,
      sideForbids_of_B dt.1 dt.2.1 dt.2.2 f2⟩

theorem noSelf_joinOn {A B : GPathB} (hnsA : NoSelf A) (hnsB : NoSelf B) : NoSelf (joinOn A B) := by
  obtain ⟨T', hT⟩ := joinOn_eq A B
  rw [hT]; exact noSelf_join hnsA hnsB

theorem secStruct_setT' {g : GPathB} {V : PathNodeId → Prop} {Rr : PathNodeId → PathNodeId → Prop}
    (h : SecStruct g V Rr) (T : List (PathNodeId × PathNodeId × PathNodeId)) : SecStruct (g.setT T) V Rr :=
  ⟨h.alive, h.refl, h.symm, h.dom, h.adj, h.pair, h.node, h.par, h.son⟩

section Join

variable {A B : GPathB} {R : List NodeId}

/-- **El lado izquierdo fijado vive entero en la unión fijada.** -/
theorem downInv_joinOn_left (hA : SInvB A) (hnsA : NoSelf A) (hnsB : NoSelf B) (hndA : NoDegT A)
    (heB : EdgesAlive B) (hcs2 : 2 ≤ A.current_step) (hv : (A.pinOn R).isValid = true) :
    DownInv (LowV (A.pinOn R) A.current_step) (LowR (A.pinOn R) A.current_step) (TF (A.pinOn R)) A.current_step
      ((joinOn A B).pinOn R) := by
  refine downInv_side hA hnsA hndA hcs2 hv (step_joinOn A B) (noSelf_joinOn hnsA hnsB) ?_ ?_
  · intro V Rr h
    obtain ⟨T', hT⟩ := joinOn_eq A B
    rw [hT]; exact secStruct_setT' (secStruct_join_left h) T'
  · intro a b r hab har hbr hf
    obtain ⟨p, q, w, hp, f1, _⟩ := tF_joinOn_side hnsA hnsB hA.edges heB hf
    obtain ⟨h1, h2, h3⟩ := tri_of_perms (R := fun y w => A.Adj y w) (fun h => (adj_symm A _ _).mp h) hab har hbr hp
    exact ⟨p, q, w, hp, f1.resolve_left (fun hn => hn ⟨h1, h2, h3⟩)⟩

/-- **El lado derecho fijado vive entero en la unión fijada.** -/
theorem downInv_joinOn_right (hB : SInvB B) (hnsA : NoSelf A) (hnsB : NoSelf B) (hndB : NoDegT B)
    (heA : EdgesAlive A) (hcs : A.current_step = B.current_step) (hcs2 : 2 ≤ B.current_step)
    (hv : (B.pinOn R).isValid = true) :
    DownInv (LowV (B.pinOn R) B.current_step) (LowR (B.pinOn R) B.current_step) (TF (B.pinOn R)) B.current_step
      ((joinOn A B).pinOn R) := by
  refine downInv_side hB hnsB hndB hcs2 hv ((step_joinOn A B).trans hcs) (noSelf_joinOn hnsA hnsB) ?_ ?_
  · intro V Rr h
    obtain ⟨T', hT⟩ := joinOn_eq A B
    rw [hT]; exact secStruct_setT' (secStruct_join_right hcs h) T'
  · intro a b r hab har hbr hf
    obtain ⟨p, q, w, hp, _, f2⟩ := tF_joinOn_side hnsA hnsB heA hB.edges hf
    obtain ⟨h1, h2, h3⟩ := tri_of_perms (R := fun y w => B.Adj y w) (fun h => (adj_symm B _ _).mp h) hab har hbr hp
    exact ⟨p, q, w, hp, f2.resolve_left (fun hn => hn ⟨h1, h2, h3⟩)⟩

/-- **Toda cadena viva del lado izquierdo fijado es cadena viva de la unión fijada**, sin hipótesis. -/
theorem liveChain_side_left (hA : SInvB A) (hB : SInvB B) (hnsA : NoSelf A) (hnsB : NoSelf B) (hndA : NoDegT A)
    (hcs : A.current_step = B.current_step) (hcs2 : 2 ≤ A.current_step) (hv : (A.pinOn R).isValid = true)
    {C : Int → PathNodeId} {j : Int} (hC : LiveChain (A.pinOn R) (TF (A.pinOn R)) C j) :
    LiveChain ((joinOn A B).pinOn R) (TF ((joinOn A B).pinOn R)) C j := by
  have his := sInvB_pinOn hA R
  have hX := downInv_joinOn_left (R := R) hA hnsA hnsB hndA hB.edges hcs2 hv
  exact liveChain_of_downInv hX (sInvB_pinOn (sInvB_joinOn hA hB hcs) R).links his.links (step_pinOn A R)
    (fun q hq => by have := alive_below his.docs his.below hq; rw [step_pinOn] at this; exact this) hC

/-- **Toda cadena viva del lado derecho fijado es cadena viva de la unión fijada**, sin hipótesis. -/
theorem liveChain_side_right (hA : SInvB A) (hB : SInvB B) (hnsA : NoSelf A) (hnsB : NoSelf B) (hndB : NoDegT B)
    (hcs : A.current_step = B.current_step) (hcs2 : 2 ≤ B.current_step) (hv : (B.pinOn R).isValid = true)
    {C : Int → PathNodeId} {j : Int} (hC : LiveChain (B.pinOn R) (TF (B.pinOn R)) C j) :
    LiveChain ((joinOn A B).pinOn R) (TF ((joinOn A B).pinOn R)) C j := by
  have his := sInvB_pinOn hB R
  have hX := downInv_joinOn_right (R := R) hB hnsA hnsB hndB hA.edges hcs hcs2 hv
  exact liveChain_of_downInv hX (sInvB_pinOn (sInvB_joinOn hA hB hcs) R).links his.links (step_pinOn B R)
    (fun q hq => by have := alive_below his.docs his.below hq; rw [step_pinOn] at this; exact this) hC

/-- **La unión fijada es válida si lo es un lado fijado.** -/
theorem valid_joinOn_of_left (hA : SInvB A) (hnsA : NoSelf A) (hnsB : NoSelf B) (hndA : NoDegT A)
    (heB : EdgesAlive B) (hcs2 : 2 ≤ A.current_step) (hv : (A.pinOn R).isValid = true) :
    ((joinOn A B).pinOn R).isValid = true := by
  have hX := downInv_joinOn_left (B := B) (R := R) hA hnsA hnsB hndA heB hcs2 hv
  have his := sInvB_pinOn hA R
  obtain ⟨q, hq, _⟩ := exists_alive_at hv (k := 0) (Int.le_refl 0) (by rw [step_pinOn]; omega)
  exact isValid_of_sec hX.sec (y := q)
    ⟨hq, by have := alive_below his.docs his.below hq; rw [step_pinOn] at this; exact this⟩

theorem valid_joinOn_of_right (hB : SInvB B) (hnsA : NoSelf A) (hnsB : NoSelf B) (hndB : NoDegT B)
    (heA : EdgesAlive A) (hcs : A.current_step = B.current_step) (hcs2 : 2 ≤ B.current_step)
    (hv : (B.pinOn R).isValid = true) : ((joinOn A B).pinOn R).isValid = true := by
  have hX := downInv_joinOn_right (A := A) (R := R) hB hnsA hnsB hndB heA hcs hcs2 hv
  have his := sInvB_pinOn hB R
  obtain ⟨q, hq, _⟩ := exists_alive_at hv (k := 0) (Int.le_refl 0) (by rw [step_pinOn]; omega)
  exact isValid_of_sec hX.sec (y := q)
    ⟨hq, by have := alive_below his.docs his.below hq; rw [step_pinOn] at this; exact this⟩

/-- **`PinSideAt` dice que las cadenas vivas de la unión fijada son exactamente las de sus dos lados fijados.** La
vuelta (de un lado a la unión) está demostrada; la ida es la hipótesis. -/
theorem pinSideAt_iff (hA : SInvB A) (hB : SInvB B) (hnsA : NoSelf A) (hnsB : NoSelf B) (hndA : NoDegT A)
    (hndB : NoDegT B) (hcs : A.current_step = B.current_step) (hcs2 : 2 ≤ A.current_step) :
    PinSideAt A B R ↔ (((joinOn A B).pinOn R).isValid = true → ∀ C j, 1 ≤ j → j ≤ A.current_step - 1 →
      (LiveChain ((joinOn A B).pinOn R) (TF ((joinOn A B).pinOn R)) C j ↔
        ((A.pinOn R).isValid = true ∧ LiveChain (A.pinOn R) (TF (A.pinOn R)) C j) ∨
        ((B.pinOn R).isValid = true ∧ LiveChain (B.pinOn R) (TF (B.pinOn R)) C j))) := by
  constructor
  · intro h hv C j hj1 hjt
    refine ⟨fun hC => h hv C j hC hj1 hjt, ?_⟩
    rintro (⟨hvA, hC⟩ | ⟨hvB, hC⟩)
    · exact liveChain_side_left hA hB hnsA hnsB hndA hcs hcs2 hvA hC
    · exact liveChain_side_right hA hB hnsA hnsB hndB hcs (by rw [← hcs]; exact hcs2) hvB hC
  · intro h hv C j hC hj1 hjt
    exact (h hv C j hj1 hjt).mp hC

end Join

end GPathB

end AbsSatBingo.Model
