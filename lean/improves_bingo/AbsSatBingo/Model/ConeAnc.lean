-- lean/improves_bingo/AbsSatBingo/Model/ConeAnc.lean
import AbsSatBingo.Model.SenderLink

/-!
# El cono de antepasados

En bin, `shiftPid p d = ⟨d, some p.id, p.parent_id⟩`: los padres de `q` son las cimas `p` con `p.id = q.parent_id` y
`p.parent_id = q.gparent_id` (`Par q p`), y la entrada de la línea que las lleva es la de clave `p.id`. Los
**antepasados** de `t` en el nivel `k` (`AncL φ t k p`) son las cimas vivas de las entradas del nivel `k` a las que se
llega desde `t` por `Par`. El **cono** `ConeAt φ k t` son los vecinos de esos antepasados en sus entradas, y `EdgeL φ k`
las aristas de todas las entradas del nivel `k`.

* **`steps_tree`**: cada entrada del nivel `n + 1` es un árbol de llegadas del nivel `n`.
* **`line_topsApart`**: todas las entradas de todos los niveles tienen `TopsApart`.
* **Monotonía** (`cone_down`, `edge_down`, `freeL_succ`, `freeL_mono`): el cono de un nivel está dentro del cono del
  nivel de abajo y las aristas viejas bajan; un paso libre del cono (`FreeL`) sube hasta arriba.
* **Nacimiento**: sin antepasado común (`Common`) el paso de las cimas está libre (`freeL_of_noCommon`); en el nivel
  del nodo más alto de la pareja, un antepasado común tiene la arista (`commonE_of_top`). **`freeL_descent`**: se
  baja hasta la transición más alta a los niveles `P` (comunes sin la arista); allí, o no hay común, o hay común con
  la arista (`CommonE`) y se usa **`ConeGap`**.
* **`oneSide_cone`**: StarOneSide en el lado de una llegada bajo `ConeGap` (parejas ausentes) y `GapDead` (quitadas).
  **`readerVerdict_iff_of_cone`**: veredicto bajo B1 + `ConeGap` + `ArrivalGap`, sin `CrossAt`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model.GPathM (shiftPid)

namespace SecLine

open GPathB Driver Machine CliqueSplit

variable {φ : Cnf}

-- ============================================================
-- Las entradas de la línea son árboles de llegadas
-- ============================================================

theorem sendAll_tree {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ)) :
    ∀ (ds : List NodeId) (nx : Line), (∀ d ∈ ds, d ∈ sonsOfMap φ kv.1) → (∀ kv' ∈ nx, ArrTree φ n kv'.1 kv'.2) →
      ∀ kv' ∈ ds.foldl (sendTo φ kv.2) nx, ArrTree φ n kv'.1 kv'.2 := by
  intro ds
  induction ds with
  | nil => intro nx _ h; exact h
  | cons d ds ih =>
    intro nx hds hnx
    simp only [List.foldl_cons]
    refine ih _ (fun d' h => hds d' (List.mem_cons_of_mem _ h)) ?_
    unfold sendTo
    dsimp only
    split
    · rename_i hv
      have hleaf : ArrTree φ n d (arr φ kv d) := ArrTree.leaf kv hkv (hds d (List.mem_cons_self ..)) hv
      exact insert_pres (fun k x => ArrTree φ n k x) hnx hleaf (fun e he => ArrTree.node he hleaf)
    · exact hnx

/-- **Cada entrada del nivel `n + 1` es un árbol de llegadas del nivel `n`.** -/
theorem steps_tree (n : Nat) : ∀ kv ∈ steps φ (n + 1) (init φ), ArrTree φ n kv.1 kv.2 := by
  rw [steps_succ]
  unfold advance
  have key : ∀ (l : Line), (∀ kv ∈ l, kv ∈ steps φ n (init φ)) → ∀ nx : Line,
      (∀ kv' ∈ nx, ArrTree φ n kv'.1 kv'.2) →
      ∀ kv' ∈ l.foldl (fun next kv => sendAll φ kv next) nx, ArrTree φ n kv'.1 kv'.2 := by
    intro l
    induction l with
    | nil => intro _ nx h; exact h
    | cons kv rest ih =>
      intro hsub nx hnx
      simp only [List.foldl_cons]
      exact ih (fun k h => hsub k (List.mem_cons_of_mem _ h)) _
        (sendAll_tree (hsub kv (List.mem_cons_self ..)) _ nx (fun _ h => h) hnx)
  exact key _ (fun _ h => h) [] (fun _ h => absurd h List.not_mem_nil)

/-- Una posesión de un árbol es de una de sus hojas. -/
theorem tree_adj {n : Nat} {d : NodeId} {e : GPathB} (h : ArrTree φ n d e) {a b : PathNodeId} (hab : e.Adj a b) :
    ∃ kv ∈ steps φ n (init φ), d ∈ sonsOfMap φ kv.1 ∧ (arr φ kv d).isValid = true ∧ (arr φ kv d).Adj a b := by
  induction h with
  | leaf kv hkv hd hv => exact ⟨kv, hkv, hd, hv, hab⟩
  | node _ _ ih₁ ih₂ =>
    unfold doJoin at hab
    split at hab
    · rcases adj_join_iff.mp hab with h | h
      · exact ih₁ h
      · exact ih₂ h
    · exact ih₁ hab

/-- **TopsApart en todas las entradas de todos los niveles.** -/
theorem line_topsApart (hbd : Bounded φ) : ∀ n, ∀ kv ∈ steps φ n (init φ), TopsApart kv.2 := by
  intro n
  cases n with
  | zero =>
    intro kv hkv
    have hkv' : kv ∈ init φ := by simpa [steps] using hkv
    rw [init_eq, List.mem_singleton] at hkv'
    subst hkv'
    exact sInvT_initSeed.2.1
  | succ n =>
    intro kv hkv
    obtain ⟨hl, hent, _, _, _⟩ := line_facts hbd n
    have key : ∀ {d : NodeId} {e : GPathB}, ArrTree φ n d e → TopsApart e := by
      intro d e ht
      induction ht with
      | leaf kv hkv hd hv =>
        have ho := hl kv hkv
        have hs := shrinks_filterAll kv.2 (reqOf φ d)
        have hea := revPrims_filterAll revPrims_edgesAlive _ (reqOf φ d) (hent kv hkv).1.2.1
        rw [arr_eq hv]; show TopsApart (GPathB.filterAll _ [])
        exact revPrims_filterAll revPrims_topsApart _ _
          (topsApart_addNode (aliveDocs_filterAll ho.docs _) (below_of_shrinks hs ho.below) hea)
      | node _ _ ih₁ ih₂ => exact topsApart_doJoin ih₁ ih₂
    exact key (steps_tree n kv hkv)

theorem inj_of_nodup_fst {l : List (NodeId × GPathB)} (hnd : (l.map (·.1)).Nodup) {a b : NodeId × GPathB}
    (ha : a ∈ l) (hb : b ∈ l) (hk : a.1 = b.1) : a = b := by
  induction l with
  | nil => cases ha
  | cons x rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (List.mem_map.mpr ⟨b, hb', hk.symm⟩) hnd.1
    · exact absurd (List.mem_map.mpr ⟨a, ha', hk⟩) hnd.1
    · exact ih hnd.2 ha' hb'

/-- Una entrada por clave en cada nivel. -/
theorem entry_unique (hbd : Bounded φ) {n : Nat} {kv kv' : NodeId × GPathB} (h : kv ∈ steps φ n (init φ))
    (h' : kv' ∈ steps φ n (init φ)) (hk : kv.1 = kv'.1) : kv = kv' :=
  inj_of_nodup_fst (line_facts hbd n).2.2.1 h h' hk

/-- Una cima viva de una entrada del nivel `n` lleva la clave de la entrada. -/
theorem top_id (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ)) {p : PathNodeId}
    (hp : p ∈ kv.2.alive) (hs : p.id.step = n) : p.id = kv.1 := by
  obtain ⟨hl, hent, _, _, _⟩ := line_facts hbd n
  obtain ⟨m, hm, hmp⟩ := (hl kv hkv).docs p hp
  have := (hent kv hkv).2 m hm (by rw [hmp, hs, (hl kv hkv).step]; omega)
  rw [hmp] at this; exact this

-- ============================================================
-- Una llegada de la línea, vista desde su remitente
-- ============================================================

/-- En una llegada, un vecino viejo de una cima nueva es vecino, en el remitente, de un padre de la cima. -/
theorem parent_of_arr_adj (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {d : NodeId} (hd : d ∈ sonsOfMap φ kv.1) (hv : (arr φ kv d).isValid = true) {t r : PathNodeId}
    (hts : t.id.step = (n : Int) + 1) (hrs : r.id.step ≤ n) (h : (arr φ kv d).Adj t r) :
    ∃ q, t.parent_id = some q.id ∧ t.gparent_id = q.parent_id ∧ q.id.step = (n : Int) ∧ q ∈ kv.2.alive ∧ kv.2.Adj r q := by
  obtain ⟨hl, hent, _, _, _⟩ := line_facts hbd n
  have ho := hl kv hkv
  have hs := shrinks_filterAll kv.2 (reqOf φ d)
  have hcf : (kv.2.filterAll (reqOf φ d)).current_step = (n : Int) + 1 := hs.1.step.trans ho.step
  have hdstep : d.step = (kv.2.filterAll (reqOf φ d)).current_step := by
    rw [hcf, sonsOfMap_step φ kv.1 d hd, ho.key]; omega
  have hfd := aliveDocs_filterAll ho.docs (reqOf φ d)
  have hfb := below_of_shrinks hs ho.below
  have hea := revPrims_filterAll revPrims_edgesAlive _ (reqOf φ d) (hent kv hkv).1.2.1
  have hta := (edgesAlive_arr hbd hkv hv t r h).1
  rw [arr_eq hv] at h hta
  have ha := (shrinks_review _).1.alive t hta
  rcases alive_addNode_cases (title := "") hfd hfb hdstep ha with ⟨_, h1⟩ | ⟨hnew, _⟩
  · omega
  obtain ⟨_, q, hq, hqr⟩ := groupStar_of_adj hs.1 hfd hfb hea hdstep hnew (by omega) h
  obtain ⟨_, _, _, hqs⟩ := step_of_newParents (rowParents_sub hq)
  have hsh : shiftPid q d = t := by simpa using (List.mem_filter.mp hq).2
  subst hsh
  exact ⟨q, rfl, rfl, by rw [hqs, hcf]; omega, ((hent kv hkv).1.2.1 r q hqr).2, hqr⟩

/-- En una llegada, una posesión entre viejos es del remitente. -/
theorem old_of_arr_adj (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {d : NodeId} (hd : d ∈ sonsOfMap φ kv.1) (hv : (arr φ kv d).isValid = true) {a b : PathNodeId}
    (ha : a.id.step ≤ n) (hb : b.id.step ≤ n) (h : (arr φ kv d).Adj a b) : kv.2.Adj a b := by
  obtain ⟨hl, _, _, _, _⟩ := line_facts hbd n
  have ho := hl kv hkv
  have hs := shrinks_filterAll kv.2 (reqOf φ d)
  have hcf : (kv.2.filterAll (reqOf φ d)).current_step = (n : Int) + 1 := hs.1.step.trans ho.step
  have hdstep : d.step = (kv.2.filterAll (reqOf φ d)).current_step := by
    rw [hcf, sonsOfMap_step φ kv.1 d hd, ho.key]; omega
  rw [arr_eq hv] at h
  exact adj_old_of_arrival (title := "") hs.1 hdstep (by omega) (by omega) h

-- ============================================================
-- Antepasados, cono y paso libre
-- ============================================================

/-- **`p` es padre de `q`** por los ids (`q = shiftPid p d`). -/
def Par (q p : PathNodeId) : Prop := q.parent_id = some p.id ∧ q.gparent_id = p.parent_id

/-- **Antepasados de `t` en el nivel `k`**: cimas vivas de una entrada del nivel `k`, por `Par` desde `t`. -/
inductive AncL (φ : Cnf) (t : PathNodeId) : Nat → PathNodeId → Prop
  | par {k : Nat} {p : PathNodeId} : Par t p → p.id.step = (k : Int) → (∃ kv ∈ steps φ k (init φ), p ∈ kv.2.alive) →
      AncL φ t k p
  | up {k : Nat} {q p : PathNodeId} : AncL φ t (k + 1) q → Par q p → p.id.step = (k : Int) →
      (∃ kv ∈ steps φ k (init φ), p ∈ kv.2.alive) → AncL φ t k p

theorem AncL.step {t : PathNodeId} {k : Nat} {p : PathNodeId} (h : AncL φ t k p) : p.id.step = (k : Int) := by
  cases h <;> assumption

/-- **El cono de `t` en el nivel `k`**: vecinos, en su entrada, de un antepasado de `t` del nivel `k`. -/
def ConeAt (φ : Cnf) (k : Nat) (t r : PathNodeId) : Prop :=
  ∃ kv ∈ steps φ k (init φ), ∃ p, AncL φ t k p ∧ kv.2.Adj r p

/-- Las aristas de las entradas del nivel `k`. -/
def EdgeL (φ : Cnf) (k : Nat) (a b : PathNodeId) : Prop := ∃ kv ∈ steps φ k (init φ), kv.2.Adj a b

/-- **Un paso libre en el cono del nivel `k`**: ningún nodo del cono en ese paso es testigo común por `EdgeL`. -/
def FreeL (φ : Cnf) (k : Nat) (t y w : PathNodeId) : Prop :=
  ∃ l : Int, 0 ≤ l ∧ l ≤ k ∧ ∀ r, ConeAt φ k t r → r.id.step = l → ¬ (EdgeL φ k y r ∧ EdgeL φ k w r)

/-- **El cono baja**: un vecino viejo de un antepasado del nivel `k + 1` está en el cono del nivel `k`. -/
theorem cone_down (hbd : Bounded φ) {k : Nat} {t r : PathNodeId} (hrs : r.id.step ≤ k) (h : ConeAt φ (k + 1) t r) :
    ConeAt φ k t r := by
  obtain ⟨kv', hkv', p', hanc, hadj⟩ := h
  obtain ⟨kv, hkv, hd, hv, hx⟩ := tree_adj (steps_tree k kv' hkv') ((adj_symm _ _ _).mp hadj)
  obtain ⟨q, hq1, hq2, hqs, hqa, hrq⟩ := parent_of_arr_adj hbd hkv hd hv (by rw [hanc.step]; push_cast; rfl) hrs hx
  exact ⟨kv, hkv, q, AncL.up hanc ⟨hq1, hq2⟩ hqs ⟨kv, hkv, hqa⟩, hrq⟩

/-- **Las aristas bajan**: entre viejos, una arista del nivel `k + 1` es del nivel `k`. -/
theorem edge_down (hbd : Bounded φ) {k : Nat} {a b : PathNodeId} (ha : a.id.step ≤ k) (hb : b.id.step ≤ k)
    (h : EdgeL φ (k + 1) a b) : EdgeL φ k a b := by
  obtain ⟨kv', hkv', hadj⟩ := h
  obtain ⟨kv, hkv, hd, hv, hx⟩ := tree_adj (steps_tree k kv' hkv') hadj
  exact ⟨kv, hkv, old_of_arr_adj hbd hkv hd hv ha hb hx⟩

/-- **Monotonía**: un paso libre del cono sube un nivel. -/
theorem freeL_succ (hbd : Bounded φ) {k : Nat} {t y w : PathNodeId} (hy : y.id.step ≤ k) (hw : w.id.step ≤ k)
    (h : FreeL φ k t y w) : FreeL φ (k + 1) t y w := by
  obtain ⟨l, h0, h1, hl⟩ := h
  refine ⟨l, h0, by push_cast; omega, fun r hr hrl ⟨hyr, hwr⟩ => ?_⟩
  have hrs : r.id.step ≤ k := by omega
  exact hl r (cone_down hbd hrs hr) hrl ⟨edge_down hbd hy hrs hyr, edge_down hbd hw hrs hwr⟩

theorem freeL_mono (hbd : Bounded φ) {k : Nat} {t y w : PathNodeId} (hy : y.id.step ≤ k) (hw : w.id.step ≤ k)
    (h : FreeL φ k t y w) : ∀ n, k ≤ n → FreeL φ n t y w := by
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction j with
  | zero => exact h
  | succ j ih => exact freeL_succ hbd (k := k + j) (by omega) (by omega) ih

-- ============================================================
-- El nacimiento del paso libre
-- ============================================================

/-- Un antepasado común de `y` y `w` en el nivel `k` (en su entrada). -/
def Common (φ : Cnf) (k : Nat) (t y w : PathNodeId) : Prop :=
  ∃ kv ∈ steps φ k (init φ), ∃ p, AncL φ t k p ∧ kv.2.Adj y p ∧ kv.2.Adj w p

/-- Un antepasado común de `y` y `w` en el nivel `k` cuya entrada tiene la arista `y–w`. -/
def CommonE (φ : Cnf) (k : Nat) (t y w : PathNodeId) : Prop :=
  ∃ kv ∈ steps φ k (init φ), ∃ p, AncL φ t k p ∧ kv.2.Adj y p ∧ kv.2.Adj w p ∧ kv.2.Adj y w

theorem line_edgesAlive (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ)) :
    EdgesAlive kv.2 := ((line_facts hbd n).2.1 kv hkv).1.2.1

theorem line_step (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ)) :
    kv.2.current_step = (n : Int) + 1 := ((line_facts hbd n).1 kv hkv).step

/-- Dos cimas del mismo paso poseídas en una entrada son la misma. -/
theorem tops_eq (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {a b : PathNodeId} (ha : a.id.step = n) (hb : b.id.step = n) (h : kv.2.Adj a b) : a = b :=
  line_topsApart hbd n kv hkv a b (by rw [line_step hbd hkv]; omega) (by rw [line_step hbd hkv]; omega) h

/-- Si una arista de alguna entrada del nivel `k` llega a una cima viva `p` de la entrada `kv`, es de `kv`. -/
theorem edge_at_top (hbd : Bounded φ) {k : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ k (init φ))
    {p a : PathNodeId} (hp : p ∈ kv.2.alive) (hps : p.id.step = k) (h : EdgeL φ k a p) : kv.2.Adj a p := by
  obtain ⟨kv', hkv', h'⟩ := h
  have e1 := top_id hbd hkv hp hps
  have e2 := top_id hbd hkv' (line_edgesAlive hbd hkv' a p h').2 hps
  rw [entry_unique hbd hkv hkv' (e1.symm.trans e2)]
  exact h'

/-- **Sin antepasado común, el paso de las cimas está libre en el cono** (demostrado): allí el cono solo tiene
antepasados, y una arista hasta una cima es de su entrada. -/
theorem freeL_of_noCommon (hbd : Bounded φ) {k : Nat} {t y w : PathNodeId} (h : ¬ Common φ k t y w) :
    FreeL φ k t y w := by
  refine ⟨k, by omega, Int.le_refl _, fun r hr hrl ⟨hyr, hwr⟩ => h ?_⟩
  obtain ⟨kv, hkv, p, hanc, hrp⟩ := hr
  have hrp' := tops_eq hbd hkv hrl hanc.step hrp
  subst hrp'
  have hra := (line_edgesAlive hbd hkv r r hrp).1
  exact ⟨kv, hkv, r, hanc, edge_at_top hbd hkv hra hrl hyr, edge_at_top hbd hkv hra hrl hwr⟩

/-- En el nivel de `y`, un antepasado común tiene la arista `y–w`. -/
theorem commonE_of_top (hbd : Bounded φ) {k : Nat} {t y w : PathNodeId} (hy : y.id.step = k ∨ w.id.step = k)
    (h : Common φ k t y w) : CommonE φ k t y w := by
  obtain ⟨kv, hkv, p, hanc, hyp, hwp⟩ := h
  refine ⟨kv, hkv, p, hanc, hyp, hwp, ?_⟩
  rcases hy with hy | hy
  · have := tops_eq hbd hkv hy hanc.step hyp
    subst this
    exact (adj_symm _ _ _).mp hwp
  · have := tops_eq hbd hkv hy hanc.step hwp
    subst this
    exact hyp

/-- Los antepasados de `t` están por debajo del nivel de su padre. -/
theorem ancL_le {t : PathNodeId} {c : NodeId} (hc : t.parent_id = some c) {k : Nat} {p : PathNodeId}
    (h : AncL φ t k p) : (k : Int) ≤ c.step := by
  induction h with
  | par hpar hs _ =>
    rw [hpar.1] at hc
    cases hc
    omega
  | up _ _ _ _ ih => omega

/-- En el nivel del padre de `t`, los antepasados de `t` son sus padres. -/
theorem ancL_at_parent {t : PathNodeId} {c : NodeId} (hc : t.parent_id = some c) {k : Nat} {p : PathNodeId}
    (h : AncL φ t k p) (hk : (k : Int) = c.step) : p.id = c := by
  cases h with
  | par hpar _ _ =>
    rw [hpar.1] at hc
    exact Option.some.inj hc
  | up hq _ _ _ =>
    have := ancL_le hc hq
    push_cast at this
    omega

/-- **El descenso**: bajo `Q` y todo `P` por encima ⟹ paso libre arriba, una pareja que en el nivel `m` no es `P` y en el nivel
`n` no es `Q` tiene paso libre en el cono del nivel `n`. -/
theorem freeL_descent (hbd : Bounded φ) {t y w : PathNodeId} {m n : Nat} (hmn : m ≤ n)
    (hy : y.id.step ≤ m) (hw : w.id.step ≤ m)
    (hgap : ∀ k : Nat, m ≤ k → k + 1 ≤ n → CommonE φ k t y w →
      (∀ j : Nat, k + 1 ≤ j → j ≤ n → Common φ j t y w ∧ ¬ CommonE φ j t y w) → FreeL φ (k + 1) t y w)
    (hm : ¬ (Common φ m t y w ∧ ¬ CommonE φ m t y w)) (hn : ¬ CommonE φ n t y w) : FreeL φ n t y w := by
  classical
  let P : Nat → Prop := fun k => Common φ k t y w ∧ ¬ CommonE φ k t y w
  have hclimb : ∀ j, m + j ≤ n → ∃ k, m ≤ k ∧ k ≤ m + j ∧ ¬ P k ∧ ∀ i, k < i → i ≤ m + j → P i := by
    intro j
    induction j with
    | zero => intro _; exact ⟨m, Nat.le_refl _, by omega, hm, fun i h1 h2 => absurd h2 (by omega)⟩
    | succ j ih =>
      intro hj
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih (by omega)
      by_cases hP : P (m + (j + 1))
      · refine ⟨k, hk1, by omega, hk3, fun i h1 h2 => ?_⟩
        by_cases hi : i = m + (j + 1)
        · subst hi; exact hP
        · exact hk4 i h1 (by omega)
      · exact ⟨m + (j + 1), by omega, Nat.le_refl _, hP, fun i h1 h2 => absurd h2 (by omega)⟩
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hclimb (n - m) (by omega)
  have hup : ∀ {j}, FreeL φ j t y w → k ≤ j → j ≤ n → FreeL φ n t y w := fun h hkj hjn =>
    freeL_mono hbd (k := _) (by omega) (by omega) h n hjn
  by_cases hC : Common φ k t y w
  · have hCE : CommonE φ k t y w := Classical.byContradiction fun hne => hk3 ⟨hC, hne⟩
    have hkn : k < n := by
      rcases Nat.lt_or_ge k n with h | h
      · exact h
      · have hkn : k = n := by omega
        exact absurd (hkn ▸ hCE) hn
    exact hup (hgap k hk1 (by omega) hCE (fun j h1 h2 => hk4 j (by omega) (by omega))) (by omega) (by omega)
  · exact hup (freeL_of_noCommon hbd hC) (Nat.le_refl _) (by omega)

-- ============================================================
-- En el join: StarOneSide bajo ConeGap
-- ============================================================

/-- **ConeGap**: en la transición más alta de un nivel `Q` (antepasado común con la arista) a niveles `P` (antepasados
comunes, ninguno con la arista) hasta arriba, el nivel de encima de la transición tiene paso libre en el cono. Para
las cimas de las llegadas de la línea y parejas de su cono que son aristas del nivel y no de su remitente. Medido (`probe_cone.jl`, sonda rápida): 0 fallos. -/
def ConeGap (φ : Cnf) : Prop :=
  ∀ (n : Nat) (kv : NodeId × GPathB) (d : NodeId) (t y w : PathNodeId), kv ∈ steps φ n (init φ) →
    d ∈ sonsOfMap φ kv.1 → (arr φ kv d).isValid = true → t ∈ (arr φ kv d).alive → t.id.step = (n : Int) + 1 →
    ConeAt φ n t y → ConeAt φ n t w → EdgeL φ n y w → ¬ kv.2.Adj y w →
    ∀ k : Nat, k + 1 ≤ n → y.id.step ≤ k → w.id.step ≤ k → CommonE φ k t y w →
      (∀ j : Nat, k + 1 ≤ j → j ≤ n → Common φ j t y w ∧ ¬ CommonE φ j t y w) → FreeL φ (k + 1) t y w

theorem arr_topsApart (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {d : NodeId} (hv : (arr φ kv d).isValid = true) : TopsApart (arr φ kv d) := by
  obtain ⟨hl, hent, _, _, _⟩ := line_facts hbd n
  have ho := hl kv hkv
  have hs := shrinks_filterAll kv.2 (reqOf φ d)
  have hea := revPrims_filterAll revPrims_edgesAlive _ (reqOf φ d) (hent kv hkv).1.2.1
  rw [arr_eq hv]; show TopsApart (GPathB.filterAll _ [])
  exact revPrims_filterAll revPrims_topsApart _ _
    (topsApart_addNode (aliveDocs_filterAll ho.docs _) (below_of_shrinks hs ho.below) hea)

/-- Un vecino viejo de una cima de una llegada está en el cono del nivel del remitente. -/
theorem cone_of_arr (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {d : NodeId} (hd : d ∈ sonsOfMap φ kv.1) (hv : (arr φ kv d).isValid = true) {t r : PathNodeId}
    (hts : t.id.step = (n : Int) + 1) (hrs : r.id.step ≤ n) (h : (arr φ kv d).Adj t r) : ConeAt φ n t r := by
  obtain ⟨q, h1, h2, hqs, hqa, hrq⟩ := parent_of_arr_adj hbd hkv hd hv hts hrs h
  exact ⟨kv, hkv, q, AncL.par ⟨h1, h2⟩ hqs ⟨kv, hkv, hqa⟩, hrq⟩

theorem step_nonneg (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {q : PathNodeId} (hq : q ∈ kv.2.alive) : 0 ≤ q.id.step := by
  obtain ⟨hl, hent, _, _, _⟩ := line_facts hbd n
  obtain ⟨m, hm, hmq⟩ := (hl kv hkv).docs q hq
  have := (hent kv hkv).1.2.2.2 m hm
  rw [hmq] at this; exact this

/-- **StarOneSide en el lado de `kvA` bajo `ConeGap` y `GapDead`.** -/
theorem oneSide_cone (hbd : Bounded φ) {n : Nat} {kvA kvB : NodeId × GPathB} {d : NodeId}
    (hp : SenderPair φ n kvA kvB d) (hC : ConeGap φ)
    (hGap : GapDead kvA.2 (arr φ kvA d) (arr φ kvB d) (join (arr φ kvA d) (arr φ kvB d))) :
    StarOneSideAt (join (arr φ kvA d) (arr φ kvB d)) (arr φ kvA d) := by
  have hD2 := d2_of_pair hbd hp
  obtain ⟨hA, hB, _, hdA, hdB, hvA, hvB⟩ := hp
  obtain ⟨hl, _, _, _, _⟩ := line_facts hbd n
  have hoA := hl kvA hA
  have hokA := stateOk_upFiltering hoA hdA hvA
  have heaX := edgesAlive_arr hbd hA hvA
  have heaG := edgesAlive_arr hbd hB hvB
  have hcsX : (arr φ kvA d).current_step = (n : Int) + 1 + 1 := hokA.step
  have hcsu : (join (arr φ kvA d) (arr φ kvB d)).current_step = (n : Int) + 1 + 1 := hcsX
  have hu : ∀ {a b}, (join (arr φ kvA d) (arr φ kvB d)).Adj a b → (arr φ kvA d).Adj a b ∨ (arr φ kvB d).Adj a b :=
    fun h => adj_join_iff.mp h
  intro t htL hts y w hty htw hyw hne
  rw [hcsu] at hts
  have hts' : t.id.step = (n : Int) + 1 := by omega
  have htg := hD2 t htL (by rw [hcsX]; omega)
  have hte : ∀ {r}, (join (arr φ kvA d) (arr φ kvB d)).Adj t r → (arr φ kvA d).Adj t r := by
    intro r h
    rcases hu h with h | h
    · exact h
    · exact absurd (heaG t r h).1 htg
  have hg : (arr φ kvB d).Adj y w := by
    rcases hu hyw with h | h
    · exact absurd h hne
    · exact h
  -- los vecinos de t en la unión son viejos
  have hold : ∀ {r}, (join (arr φ kvA d) (arr φ kvB d)).Adj t r → r ≠ t → r.id.step ≤ n := by
    intro r h hrt
    have hx := hte h
    have hra := (heaX t r hx).2
    have hb := alive_below hokA.docs hokA.below hra
    rw [hcsX] at hb
    by_cases hr : r.id.step = (n : Int) + 1
    · exact absurd (arr_topsApart hbd hA hvA t r (by rw [hcsX]; omega) (by rw [hcsX]; omega) hx).symm hrt
    · omega
  have hyt : y ≠ t := fun h => by subst h; exact htg (heaG _ _ hg).1
  have hwt : w ≠ t := fun h => by subst h; exact htg (heaG _ _ hg).2
  have hyo := hold hty hyt
  have hwo := hold htw hwt
  by_cases hAyw : kvA.2.Adj y w
  · obtain ⟨l, h0, h1, hl'⟩ := hGap t htL (by rw [hcsu]; omega) y w hty htw hg hne hAyw
    exact ⟨l, h0, h1, fun r hrl hrt hyr => hl' r (heaX t r (hte hrt)).2 hrl hyr⟩
  -- caso ausente: el cono
  have hcy := cone_of_arr hbd hA hdA hvA hts' hyo (hte hty)
  have hcw := cone_of_arr hbd hA hdA hvA hts' hwo (hte htw)
  have hy0 : 0 ≤ y.id.step := by
    obtain ⟨kv, hkv, p, _, hyp⟩ := hcy
    exact step_nonneg hbd hkv ((line_edgesAlive hbd hkv y p hyp).1)
  have hw0 : 0 ≤ w.id.step := by
    obtain ⟨kv, hkv, p, _, hwp⟩ := hcw
    exact step_nonneg hbd hkv ((line_edgesAlive hbd hkv w p hwp).1)
  let m : Nat := (max y.id.step w.id.step).toNat
  have hmy : y.id.step ≤ m := by simp only [m]; omega
  have hmw : w.id.step ≤ m := by simp only [m]; omega
  have hmn : m ≤ n := by simp only [m]; omega
  have hm : ¬ (Common φ m t y w ∧ ¬ CommonE φ m t y w) := by
    intro ⟨hc, hce⟩
    exact hce (commonE_of_top hbd (by simp only [m]; omega) hc)
  have htp : t.parent_id = some kvA.1 := top_parent_of_arr hbd hA hdA hvA htL (by rw [hcsX]; omega)
  have hn : ¬ CommonE φ n t y w := by
    intro ⟨kv, hkv, p, hanc, hyp, _, hyw'⟩
    have hpid := ancL_at_parent htp hanc (by rw [hoA.key]; omega)
    have hpa := (line_edgesAlive hbd hkv y p hyp).2
    have := entry_unique hbd hkv hA ((top_id hbd hkv hpa hanc.step).symm.trans hpid)
    subst this
    exact hAyw hyw'
  have hF := freeL_descent hbd hmn hmy hmw
    (fun k _ hk1 hce hP => hC n kvA d t y w hA hdA hvA htL hts' hcy hcw
      ⟨kvB, hB, old_of_arr_adj hbd hB hdB hvB hyo hwo hg⟩ hAyw k hk1 (by omega) (by omega) hce hP) hm hn
  obtain ⟨l, h0, h1, hl'⟩ := hF
  refine ⟨l, h0, by rw [hcsu]; omega, fun r hrl hrt ⟨hyr, hwr⟩ => ?_⟩
  have hrt' : r ≠ t := fun h => by subst h; omega
  have hro := hold hrt hrt'
  have hedge : ∀ {a : PathNodeId}, a.id.step ≤ (n : Int) → (join (arr φ kvA d) (arr φ kvB d)).Adj a r → EdgeL φ n a r := by
    intro a ha h
    rcases hu h with h | h
    · exact ⟨kvA, hA, old_of_arr_adj hbd hA hdA hvA ha hro h⟩
    · exact ⟨kvB, hB, old_of_arr_adj hbd hB hdB hvB ha hro h⟩
  exact hl' r (cone_of_arr hbd hA hdA hvA hts' hro (hte hrt)) hrl ⟨hedge hyo hyr, hedge hwo hwr⟩

/-- **Las hipótesis**: B1 en los joins, `ConeGap` y `ArrivalGap`. -/
structure HypsCone (φ : Cnf) : Prop where
  b1 : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvC e → SInvC g → okJoin e g = true →
    StarNodes (join e g)
  cone : ConeGap φ
  agap : ∀ n kvA kvB d, SenderPair φ n kvA kvB d →
    ArrivalGap kvA.2 (arr φ kvA d) (fun a b => (arr φ kvA d).Adj a b ∨ (arr φ kvB d).Adj a b)

theorem hypsOne_of_cone (hbd : Bounded φ) (H : HypsCone φ) : HypsOne φ := by
  intro n kvA kvB d hp _ _
  have heaE := edgesAlive_arr hbd hp.1 hp.2.2.2.2.2.1
  have heaG := edgesAlive_arr hbd hp.2.1 hp.2.2.2.2.2.2
  exact oneSide_cone hbd hp H.cone
    (gapDead_of_arrivalGap adj_join_cases rfl heaE heaG (d2_of_pair hbd hp) (H.agap n kvA kvB d hp))

/-- **El veredicto del lector bajo B1, `ConeGap` y `ArrivalGap`**: sin `CrossAt`. -/
theorem readerVerdict_iff_of_cone (hbd : Bounded φ) (H : HypsCone φ) : readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_one hbd H.b1 (hypsOne_of_cone hbd H)

end SecLine

end AbsSatBingo.Model
