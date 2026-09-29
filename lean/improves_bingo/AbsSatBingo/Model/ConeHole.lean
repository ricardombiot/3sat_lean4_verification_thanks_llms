-- lean/improves_bingo/AbsSatBingo/Model/ConeHole.lean
import AbsSatBingo.Model.ConeAnc

/-!
# `ConeGap` desde el hueco de una llegada

**`ArrHole`** (hipótesis local sobre una llegada, sin contexto): si la llegada `X` de un remitente `S` del nivel `n`
quita una arista `y–w` de `S` y conserva a los dos, hay un paso en el que ningún vivo de `X` es vecino común de `y` y
`w` con las aristas de **todas** las entradas del nivel `n`. Medido (`probe_arrhole.jl`, sonda rápida): 6 441/6 441.

* **`arrivalGap_of_arrHole`**: `ArrHole` ⟹ `ArrivalGap`.
* **`tree_incl`**: si la cima de una llegada vive en un árbol, las aristas de la llegada son del árbol.
* **`freeL_one`**: en la transición de `ConeGap`, si todos los antepasados del nivel `k + 1` están en una llegada
  `X`, `ArrHole` da el paso libre: los antepasados del nivel `k` son cimas del remitente `S` (que tiene la arista),
  `X` la quitó, y el cono del nivel `k + 1` está dentro de los vivos de `X`.
* **`coneGap_of_arrHole`**: `ConeGap` ⇐ `ArrHole` + `ConeGapMulti` (la transición con antepasados en dos llegadas;
  ~4 % de las transiciones medidas).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace SecLine

open GPathB Driver Machine CliqueSplit

variable {φ : Cnf}

/-- **ArrHole**: una llegada que quita una arista de su remitente deja un hueco con las aristas de todo el nivel. -/
def ArrHole (φ : Cnf) : Prop :=
  ∀ (n : Nat) (kv : NodeId × GPathB) (d : NodeId) (y w : PathNodeId), kv ∈ steps φ n (init φ) →
    d ∈ sonsOfMap φ kv.1 → (arr φ kv d).isValid = true → y ∈ (arr φ kv d).alive → w ∈ (arr φ kv d).alive →
    kv.2.Adj y w → ¬ (arr φ kv d).Adj y w →
    ∃ l : Int, 0 ≤ l ∧ l ≤ n ∧ ∀ r, r ∈ (arr φ kv d).alive → r.id.step = l → ¬ (EdgeL φ n y r ∧ EdgeL φ n w r)

/-- Un vivo de una entrada del nivel `n` está por debajo de `n + 1`. -/
theorem line_below (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {q : PathNodeId} (hq : q ∈ kv.2.alive) : q.id.step ≤ n := by
  have ho := (line_facts hbd n).1 kv hkv
  have := alive_below ho.docs ho.below hq
  rw [ho.step] at this; omega

/-- **`ArrHole` ⟹ `ArrivalGap`** (las aristas de las llegadas entre viejos son del nivel del remitente). -/
theorem arrivalGap_of_arrHole (hbd : Bounded φ) (H : ArrHole φ) {n : Nat} {kvA kvB : NodeId × GPathB} {d : NodeId}
    (hp : SenderPair φ n kvA kvB d) :
    ArrivalGap kvA.2 (arr φ kvA d) (fun a b => (arr φ kvA d).Adj a b ∨ (arr φ kvB d).Adj a b) := by
  obtain ⟨hA, hB, _, hdA, hdB, hvA, hvB⟩ := hp
  intro y w hy hw hyw hne
  have hcs := (stateOk_upFiltering ((line_facts hbd n).1 kvA hA) hdA hvA).step
  have heA := line_edgesAlive hbd hA
  have hyo := line_below hbd hA (heA y w hyw).1
  have hwo := line_below hbd hA (heA y w hyw).2
  obtain ⟨l, h0, h1, hl⟩ := H n kvA d y w hA hdA hvA hy hw hyw hne
  refine ⟨l, h0, by rw [hcs]; omega, fun r hr hrl ⟨hyr, hwr⟩ => hl r hr hrl ⟨?_, ?_⟩⟩
  · rcases hyr with h | h
    · exact ⟨kvA, hA, old_of_arr_adj hbd hA hdA hvA hyo (by omega) h⟩
    · exact ⟨kvB, hB, old_of_arr_adj hbd hB hdB hvB hyo (by omega) h⟩
  · rcases hwr with h | h
    · exact ⟨kvA, hA, old_of_arr_adj hbd hA hdA hvA hwo (by omega) h⟩
    · exact ⟨kvB, hB, old_of_arr_adj hbd hB hdB hvB hwo (by omega) h⟩

/-- Una cima viva de una llegada lleva el id del destino. -/
theorem arr_top_id (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {d : NodeId} (hd : d ∈ sonsOfMap φ kv.1) (hv : (arr φ kv d).isValid = true) {q : PathNodeId}
    (hq : q ∈ (arr φ kv d).alive) (hqs : q.id.step = (n : Int) + 1) : q.id = d := by
  have hok := stateOk_upFiltering ((line_facts hbd n).1 kv hkv) hd hv
  obtain ⟨m, hm, hmq⟩ := hok.docs q hq
  have := topDocsId_arr hbd hkv hv m hm (by rw [hmq, hqs, hok.step]; omega)
  rw [hmq] at this; exact this

/-- La cima viva `q` de una llegada del nivel `n` es de la llegada del remitente de clave `q.parent_id`. -/
theorem arr_top_parent (hbd : Bounded φ) {n : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ))
    {d : NodeId} (hd : d ∈ sonsOfMap φ kv.1) (hv : (arr φ kv d).isValid = true) {q : PathNodeId}
    (hq : q ∈ (arr φ kv d).alive) (hqs : q.id.step = (n : Int) + 1) : q.parent_id = some kv.1 := by
  have hok := stateOk_upFiltering ((line_facts hbd n).1 kv hkv) hd hv
  exact top_parent_of_arr hbd hkv hd hv hq (by rw [hok.step]; omega)

/-- **Si la cima de una llegada vive en un árbol, las aristas de la llegada son del árbol.** -/
theorem tree_incl (hbd : Bounded φ) {n : Nat} {d : NodeId} {e : GPathB} (h : ArrTree φ n d e)
    {kv : NodeId × GPathB} (hkv : kv ∈ steps φ n (init φ)) {q : PathNodeId} (hq : q ∈ e.alive)
    (hqs : q.id.step = (n : Int) + 1) (hqp : q.parent_id = some kv.1) :
    ∀ a b, (arr φ kv d).Adj a b → e.Adj a b := by
  induction h with
  | leaf kv0 hkv0 hd0 hv0 =>
    have := arr_top_parent hbd hkv0 hd0 hv0 hq hqs
    rw [hqp] at this
    have he := entry_unique hbd hkv hkv0 (Option.some.inj this)
    subst he
    exact fun _ _ h => h
  | node _ _ ih₁ ih₂ =>
    unfold doJoin at hq ⊢
    split
    · rename_i hok
      rw [if_pos hok] at hq
      intro a b hab
      rcases (alive_join _ _ q).mp hq with h | h
      · exact adj_join_iff.mpr (Or.inl (ih₁ h a b hab))
      · exact adj_join_iff.mpr (Or.inr (ih₂ h a b hab))
    · rename_i hok
      rw [if_neg hok] at hq
      exact ih₁ hq

/-- Todos los antepasados de `t` del nivel `k + 1` están en la llegada de `c` a `D`. -/
def OneArr (φ : Cnf) (k : Nat) (t : PathNodeId) (D c : NodeId) : Prop :=
  ∀ q, AncL φ t (k + 1) q → q.id = D ∧ q.parent_id = some c

/-- **La transición con los antepasados en una sola llegada**: `ArrHole` da el paso libre del cono. -/
theorem freeL_one (hbd : Bounded φ) (H : ArrHole φ) {n k : Nat} {t y w : PathNodeId} {c₀ : NodeId}
    (htp : t.parent_id = some c₀) (hc₀ : c₀.step = (n : Int)) (hkn : k + 1 ≤ n)
    (hyk : y.id.step ≤ k) (hwk : w.id.step ≤ k)
    (hCE : CommonE φ k t y w) (hC1 : Common φ (k + 1) t y w) (hnCE1 : ¬ CommonE φ (k + 1) t y w)
    {D c : NodeId} (hone : OneArr φ k t D c) : FreeL φ (k + 1) t y w := by
  obtain ⟨kvq, hkvq, q, hancq, hyq, hwq⟩ := hC1
  have htq := steps_tree k kvq hkvq
  have hqs : q.id.step = (k : Int) + 1 := by rw [hancq.step]; push_cast; rfl
  obtain ⟨S, hS, hdS, hvS, hXyq⟩ := tree_adj htq hyq
  have hqa := (edgesAlive_arr hbd hS hvS y q hXyq).2
  have hqp := arr_top_parent hbd hS hdS hvS hqa hqs
  have hSc : S.1 = c := by
    have := (hone q hancq).2; rw [hqp] at this; exact Option.some.inj this
  have hy : y ∈ (arr φ S kvq.1).alive := (edgesAlive_arr hbd hS hvS y q hXyq).1
  have hw : w ∈ (arr φ S kvq.1).alive := by
    obtain ⟨S2, hS2, hdS2, hvS2, hX2⟩ := tree_adj htq hwq
    have hqa2 := (edgesAlive_arr hbd hS2 hvS2 w q hX2).2
    have hqp2 := arr_top_parent hbd hS2 hdS2 hvS2 hqa2 hqs
    rw [hqp] at hqp2
    have := entry_unique hbd hS hS2 (Option.some.inj hqp2)
    subst this
    exact (edgesAlive_arr hbd hS hvS w q hX2).1
  -- el remitente tiene la arista: los antepasados del nivel k son cimas de S
  have hSyw : S.2.Adj y w := by
    obtain ⟨kvp, hkvp, p, hancp, hyp, _, hywp⟩ := hCE
    cases hancp with
    | par hpar hps _ =>
      rw [hpar.1] at htp
      cases htp
      omega
    | up hq' hpar hps _ =>
      have h1 := (hone _ hq').2
      rw [hpar.1] at h1
      have hpc : p.id = c := Option.some.inj h1
      have hpa := (line_edgesAlive hbd hkvp y p hyp).2
      have := entry_unique hbd hkvp hS ((top_id hbd hkvp hpa hps).symm.trans (hpc.trans hSc.symm))
      subst this
      exact hywp
  -- la llegada la quitó
  have hnX : ¬ (arr φ S kvq.1).Adj y w := fun hX => hnCE1
    ⟨kvq, hkvq, q, hancq, hyq, hwq,
      tree_incl hbd htq hS (line_edgesAlive hbd hkvq y q hyq).2 hqs hqp y w hX⟩
  obtain ⟨l, h0, h1, hl⟩ := H k S kvq.1 y w hS hdS hvS hy hw hSyw hnX
  -- el cono del nivel k + 1 está en la llegada
  have hin : ∀ r, ConeAt φ (k + 1) t r → r ∈ (arr φ S kvq.1).alive := by
    intro r ⟨kv', hkv', q', hanc', hrq'⟩
    obtain ⟨S', hS', hdS', hvS', hX'⟩ := tree_adj (steps_tree k kv' hkv') ((adj_symm _ _ _).mp hrq')
    have hq's : q'.id.step = (k : Int) + 1 := by rw [hanc'.step]; push_cast; rfl
    have hq'a := (edgesAlive_arr hbd hS' hvS' q' r hX').1
    have hq'p := arr_top_parent hbd hS' hdS' hvS' hq'a hq's
    have h1 := (hone q' hanc').2
    rw [hq'p] at h1
    have hSS := entry_unique hbd hS' hS ((Option.some.inj h1).trans hSc.symm)
    subst hSS
    have hd1 := arr_top_id hbd hS' hdS' hvS' hq'a hq's
    have hd2 := arr_top_id hbd hS' hdS hvS hqa hqs
    have hkk : kv'.1 = kvq.1 := hd1.symm.trans ((hone q' hanc').1.trans ((hone q hancq).1.symm.trans hd2))
    rw [hkk] at hX'
    exact (edgesAlive_arr hbd hS' hvS q' r hX').2
  refine ⟨l, h0, by push_cast; omega, fun r hr hrl ⟨hyr, hwr⟩ => hl r (hin r hr) hrl ⟨?_, ?_⟩⟩
  · exact edge_down hbd hyk (by omega) hyr
  · exact edge_down hbd hwk (by omega) hwr

/-- **ConeGapMulti**: `ConeGap` solo cuando los antepasados del nivel `k + 1` no están en una sola llegada. -/
def ConeGapMulti (φ : Cnf) : Prop :=
  ∀ (n : Nat) (kv : NodeId × GPathB) (d : NodeId) (t y w : PathNodeId), kv ∈ steps φ n (init φ) →
    d ∈ sonsOfMap φ kv.1 → (arr φ kv d).isValid = true → t ∈ (arr φ kv d).alive → t.id.step = (n : Int) + 1 →
    ConeAt φ n t y → ConeAt φ n t w → EdgeL φ n y w → ¬ kv.2.Adj y w →
    ∀ k : Nat, k + 1 ≤ n → y.id.step ≤ k → w.id.step ≤ k → CommonE φ k t y w →
      (∀ j : Nat, k + 1 ≤ j → j ≤ n → Common φ j t y w ∧ ¬ CommonE φ j t y w) →
      (¬ ∃ D c, OneArr φ k t D c) → FreeL φ (k + 1) t y w

/-- **`ConeGap` ⇐ `ArrHole` + `ConeGapMulti`.** -/
theorem coneGap_of_arrHole (hbd : Bounded φ) (H : ArrHole φ) (HM : ConeGapMulti φ) : ConeGap φ := by
  intro n kv d t y w hkv hd hv ht hts hcy hcw hE hnA k hkn hyk hwk hCE hP
  by_cases hone : ∃ D c, OneArr φ k t D c
  · obtain ⟨D, c, hone⟩ := hone
    have ho := (line_facts hbd n).1 kv hkv
    have hok := stateOk_upFiltering ho hd hv
    have htp := top_parent_of_arr hbd hkv hd hv ht (by rw [hok.step]; omega)
    have hP1 := hP (k + 1) (Nat.le_refl _) hkn
    exact freeL_one hbd H htp (by rw [ho.key]; omega) hkn hyk hwk hCE hP1.1 hP1.2 hone
  · exact HM n kv d t y w hkv hd hv ht hts hcy hcw hE hnA k hkn hyk hwk hCE hP hone

/-- **Las hipótesis**: B1 en los joins, `ArrHole` (local, sobre llegadas) y `ConeGapMulti`. -/
structure HypsHole (φ : Cnf) : Prop where
  b1 : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvC e → SInvC g → okJoin e g = true →
    StarNodes (join e g)
  hole : ArrHole φ
  multi : ConeGapMulti φ

/-- **El veredicto del lector bajo B1, `ArrHole` y `ConeGapMulti`** (`ArrivalGap` y `ConeGap` de una llegada,
demostrados desde `ArrHole`). -/
theorem readerVerdict_iff_of_hole (hbd : Bounded φ) (H : HypsHole φ) : readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_cone hbd ⟨H.b1, coneGap_of_arrHole hbd H.hole H.multi,
    fun _ _ _ _ hp => arrivalGap_of_arrHole hbd H.hole hp⟩

end SecLine

end AbsSatBingo.Model
