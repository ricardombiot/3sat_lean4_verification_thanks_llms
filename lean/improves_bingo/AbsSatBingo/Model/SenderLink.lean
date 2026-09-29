-- lean/improves_bingo/AbsSatBingo/Model/SenderLink.lean
import AbsSatBingo.Model.OneSideHist
import AbsSatBingo.Model.LineCtxT

/-!
# StarOneSide conectado a la línea: las hipótesis sobre pares de remitentes

En cada join de la máquina, `e` (el estado del destino) es un árbol de llegadas y `g` la llegada del remitente `s`.

* **`tree_single`** (demostrado): en el mapa bin, `e` equivale a **una sola llegada** `arr φ kv₀ d`: sus orígenes
  son claves distintas de `s` del paso del remitente, así que todas son `other s`, y con claves únicas en la línea
  todas sus hojas son la misma llegada (mismos vivos, mismas posesiones).
* **`starOneSideAt_congr`**, **`gapDead_congr`**: las dos propiedades solo miran vivos, posesiones y el paso.
* **`readerVerdict_iff_of_senders`**: el veredicto del lector bajo B1 (`StarNodes` de la unión) y, para cada par de
  remitentes distintos de una línea con un hijo común, `CrossAt` en la estrella del grupo de padres, `GapDead` y D2
  (una cima de una llegada no vive en la otra).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace CliqueSplit

open GPathB Driver Machine SecLine

variable {φ : Cnf}

/-- Un estado válido tiene vivos en cada paso. -/
theorem alive_at_of_valid {g : GPathB} (hv : g.isValid = true) {k : Int} (h0 : 0 ≤ k) (h1 : k < g.current_step) :
    ∃ q ∈ g.alive, q.id.step = k := by
  unfold isValid at hv
  have := List.all_eq_true.mp hv k (mem_intRange h0 (by omega))
  obtain ⟨q, hq, hqk⟩ := List.any_eq_true.mp this
  exact ⟨q, hq, by simpa using hqk⟩

theorem adj_join_iff {e g : GPathB} {a b : PathNodeId} : (join e g).Adj a b ↔ e.Adj a b ∨ g.Adj a b :=
  ⟨adj_join_cases, fun h => h.elim adj_join_left adj_join_right⟩

/-- **En el mapa bin, el estado del destino es una sola llegada.** -/
theorem tree_single (hbd : Bounded φ) {n : Nat} {d : NodeId} {e : GPathB} (h : ArrTree φ n d e)
    {A : NodeId → Prop} {s : NodeId} (hoe : OriginIn e n A) (hsA : ¬ A s) (hAk : ∀ a, A a → Key n a)
    (hsk : Key n s) :
    ∃ kv₀, kv₀ ∈ steps φ n (init φ) ∧ d ∈ sonsOfMap φ kv₀.1 ∧ (arr φ kv₀ d).isValid = true ∧ kv₀.1 = other s ∧
      (∀ q, q ∈ e.alive ↔ q ∈ (arr φ kv₀ d).alive) ∧ (∀ a b, e.Adj a b ↔ (arr φ kv₀ d).Adj a b) := by
  obtain ⟨hl, hent, hnd, _, _⟩ := line_facts hbd n
  revert hoe
  induction h with
  | leaf kv hkv hd hv =>
    intro hoe
    have ho := hl kv hkv
    have hok := stateOk_upFiltering ho hd hv
    obtain ⟨q, hq, hqs⟩ := alive_at_of_valid hv (k := n) (by omega) (by rw [hok.step]; omega)
    have hon := originIn_upFiltering (φ := φ) ho (hent kv hkv).2 hd
    have hid : q.id = kv.1 := hon q hq (by rw [hqs]; omega)
    have hA : A kv.1 := hid ▸ hoe q hq hqs
    have hne : kv.1 ≠ s := fun h => hsA (h ▸ hA)
    exact ⟨kv, hkv, hd, hv, eq_other (hAk _ hA) hsk hne, fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  | node h₁ h₂ ih₁ ih₂ =>
    intro hoe
    unfold doJoin at hoe ⊢
    split
    · rename_i hok
      rw [if_pos hok] at hoe
      have ho₁ : OriginIn _ n A := fun q hq hk => hoe q ((alive_join _ _ q).mpr (Or.inl hq)) hk
      have ho₂ : OriginIn _ n A := fun q hq hk => hoe q ((alive_join _ _ q).mpr (Or.inr hq)) hk
      obtain ⟨kv₁, hkv₁, hd₁, hv₁, hk₁, ha₁, hj₁⟩ := ih₁ ho₁
      obtain ⟨kv₂, hkv₂, _, _, hk₂, ha₂, hj₂⟩ := ih₂ ho₂
      have heq : kv₁ = kv₂ := eq_of_nodup_keys hnd hkv₁ hkv₂ (hk₁.trans hk₂.symm)
      subst heq
      refine ⟨kv₁, hkv₁, hd₁, hv₁, hk₁, fun q => ?_, fun a b => ?_⟩
      · rw [alive_join, ha₁, ha₂, or_self]
      · rw [adj_join_iff, hj₁, hj₂, or_self]
    · rename_i hok
      rw [if_neg hok] at hoe
      exact ih₁ hoe

end CliqueSplit

namespace GPathB

/-- StarOneSide solo mira vivos, posesiones y el paso. -/
theorem starOneSideAt_congr {u u' L L' : GPathB} (hcs : u.current_step = u'.current_step)
    (hu : ∀ a b, u.Adj a b ↔ u'.Adj a b) (hLa : ∀ q, q ∈ L.alive ↔ q ∈ L'.alive)
    (hLj : ∀ a b, L.Adj a b ↔ L'.Adj a b) (h : StarOneSideAt u' L') : StarOneSideAt u L := by
  intro t htL hts y w hty htw hyw hne
  obtain ⟨l, h0, h1, hl⟩ := h t ((hLa t).mp htL) (by rw [← hcs]; exact hts) y w ((hu _ _).mp hty) ((hu _ _).mp htw)
    ((hu _ _).mp hyw) (fun h' => hne ((hLj _ _).mpr h'))
  exact ⟨l, h0, by rw [hcs]; exact h1, fun r hrl hrt hr =>
    hl r hrl ((hu _ _).mp hrt) ⟨(hu _ _).mp hr.1, (hu _ _).mp hr.2⟩⟩

theorem gapDead_congr {A e g u u' : GPathB} (hcs : u.current_step = u'.current_step)
    (hu : ∀ a b, u.Adj a b ↔ u'.Adj a b) (h : GapDead A e g u') : GapDead A e g u := by
  intro t hte hts y w hty htw hg hne hA
  obtain ⟨l, h0, h1, hl⟩ := h t hte (by rw [← hcs]; exact hts) y w ((hu _ _).mp hty) ((hu _ _).mp htw) hg hne hA
  exact ⟨l, h0, by rw [hcs]; exact h1, fun r hr hrl hyr => hl r hr hrl ⟨(hu _ _).mp hyr.1, (hu _ _).mp hyr.2⟩⟩

end GPathB

namespace SecLine

open GPathB Driver Machine Final CliqueSplit

variable {φ : Cnf}

/-- La llegada válida es la fila nueva revisada sobre el filtrado. -/
theorem arr_eq {kv : NodeId × GPathB} {d : NodeId} (hv : (arr φ kv d).isValid = true) :
    arr φ kv d = ((kv.2.filterAll (reqOf φ d)).addNode d "" (isProhibited φ)).review := by
  show kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ) = _
  unfold upFiltering up
  rw [if_pos (valid_filter_of_arr hv)]

/-- Las premisas de un par de remitentes con un hijo común. -/
def SenderPair (φ : Cnf) (n : Nat) (kvA kvB : NodeId × GPathB) (d : NodeId) : Prop :=
  kvA ∈ steps φ n (init φ) ∧ kvB ∈ steps φ n (init φ) ∧ kvA.1 ≠ kvB.1 ∧ d ∈ sonsOfMap φ kvA.1 ∧
    d ∈ sonsOfMap φ kvB.1 ∧ (arr φ kvA d).isValid = true ∧ (arr φ kvB d).isValid = true

/-- **StarOneSide en el lado de la llegada de `kvA`**, dentro de una unión `u` de las dos llegadas. -/
theorem oneSide_of_senders (hbd : Bounded φ) {n : Nat} {kvA kvB : NodeId × GPathB} {d : NodeId}
    (hp : SenderPair φ n kvA kvB d) (hIA : SInvC kvA.2) {u : GPathB}
    (hu : ∀ {a b}, u.Adj a b → (arr φ kvA d).Adj a b ∨ (arr φ kvB d).Adj a b)
    (hcsu : u.current_step = (arr φ kvA d).current_step)
    (heaE : EdgesAlive (arr φ kvA d)) (heaG : EdgesAlive (arr φ kvB d))
    (hD2 : ∀ t, t ∈ (arr φ kvA d).alive → t.id.step = (arr φ kvA d).current_step - 1 → t ∉ (arr φ kvB d).alive)
    (hX : ∀ t, t ∈ (kvA.2.filterAll (reqOf φ d)).newRowIds d (isProhibited φ) →
      CrossAt kvA.2 kvB.2 (GroupStar kvA.2 (kvA.2.filterAll (reqOf φ d)) d t))
    (hGap : GapDead kvA.2 (arr φ kvA d) (arr φ kvB d) u) :
    StarOneSideAt u (arr φ kvA d) := by
  obtain ⟨hA, hB, _, hdA, hdB, hvA, hvB⟩ := hp
  obtain ⟨hl, _, _, _, _⟩ := line_facts hbd n
  have hoA := hl kvA hA
  have hoB := hl kvB hB
  have hsA := (shrinks_filterAll kvA.2 (reqOf φ d)).1
  have hsB := (shrinks_filterAll kvB.2 (reqOf φ d)).1
  have hcA : (kvA.2.filterAll (reqOf φ d)).current_step = (n : Int) + 1 := hsA.step.trans hoA.step
  have hcB : (kvB.2.filterAll (reqOf φ d)).current_step = (n : Int) + 1 := hsB.step.trans hoB.step
  have hdsA : d.step = (kvA.2.filterAll (reqOf φ d)).current_step := by
    rw [hcA, sonsOfMap_step φ kvA.1 d hdA, hoA.key]; omega
  have hdsB : d.step = (kvB.2.filterAll (reqOf φ d)).current_step := by
    rw [hcB, sonsOfMap_step φ kvB.1 d hdB, hoB.key]; omega
  have hcsArr : (arr φ kvA d).current_step = (n : Int) + 1 + 1 := (stateOk_upFiltering hoA hdA hvA).step
  have heA : EdgesAlive kvA.2 := hIA.1.1.1.2.2.2.1
  have hea := revPrims_filterAll revPrims_edgesAlive _ (reqOf φ d) heA
  have heqA := arr_eq hvA
  have heqB := arr_eq hvB
  have hcsu' : u.current_step = (kvA.2.filterAll (reqOf φ d)).current_step + 1 := by rw [hcsu, hcsArr, hcA]
  have hu' : ∀ {a b}, u.Adj a b → (((kvA.2.filterAll (reqOf φ d)).addNode d "" (isProhibited φ)).review).Adj a b ∨
      (((kvB.2.filterAll (reqOf φ d)).addNode d "" (isProhibited φ)).review).Adj a b := by
    intro a b h; rw [← heqA, ← heqB]; exact hu h
  have heaE' : EdgesAlive (((kvA.2.filterAll (reqOf φ d)).addNode d "" (isProhibited φ)).review) := by
    rw [← heqA]; exact heaE
  have heaG' : EdgesAlive (((kvB.2.filterAll (reqOf φ d)).addNode d "" (isProhibited φ)).review) := by
    rw [← heqB]; exact heaG
  have hD2' : ∀ t, t ∈ (((kvA.2.filterAll (reqOf φ d)).addNode d "" (isProhibited φ)).review).alive →
      t.id.step = u.current_step - 1 →
      t ∉ (((kvB.2.filterAll (reqOf φ d)).addNode d "" (isProhibited φ)).review).alive := by
    intro t ht hts
    rw [← heqA] at ht; rw [← heqB]
    exact hD2 t ht (by rw [hts, hcsu])
  have hGap' : GapDead kvA.2 (((kvA.2.filterAll (reqOf φ d)).addNode d "" (isProhibited φ)).review)
      (((kvB.2.filterAll (reqOf φ d)).addNode d "" (isProhibited φ)).review) u := by
    rw [← heqA, ← heqB]; exact hGap
  rw [heqA]
  exact starOneSideAt_of_hist hsA hsB hdsA hdsB (aliveDocs_filterAll hoA.docs _)
    (below_of_shrinks (shrinks_filterAll kvA.2 (reqOf φ d)) hoA.below) hea heaE' heaG' hu' hcsu' hD2' hX hGap'

/-- **Las hipótesis sobre pares de remitentes**, y B1 en los joins. -/
structure HypsSenders (φ : Cnf) : Prop where
  b1 : ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvC e → SInvC g → okJoin e g = true →
    StarNodes (join e g)
  cross : ∀ n kvA kvB d, SenderPair φ n kvA kvB d → ∀ t, t ∈ (kvA.2.filterAll (reqOf φ d)).newRowIds d (isProhibited φ) →
    CrossAt kvA.2 kvB.2 (GroupStar kvA.2 (kvA.2.filterAll (reqOf φ d)) d t)
  gap : ∀ n kvA kvB d, SenderPair φ n kvA kvB d → GapDead kvA.2 (arr φ kvA d) (arr φ kvB d) (join (arr φ kvA d) (arr φ kvB d))
  d2 : ∀ n kvA kvB d, SenderPair φ n kvA kvB d → ∀ t, t ∈ (arr φ kvA d).alive →
    t.id.step = (arr φ kvA d).current_step - 1 → t ∉ (arr φ kvB d).alive

theorem other_ne {k : Int} {s : NodeId} (hs : Key k s) : other s ≠ s := by
  intro h
  have := congrArg NodeId.index h
  simp only [other] at this
  rcases hs.2 with h' | h' <;> omega

/-- **Quien resuelve el join con las hipótesis sobre remitentes.** -/
theorem joinProvT_senders (hbd : Bounded φ) (H : HypsSenders φ) {U : Int} (hU : 2 ≤ U) : JoinProvT φ SInvC U := by
  intro key s e g A he hg hke hkg hoe _ hsA hAk hsk n hUn hIl htree kv hkv hks hkd hga
  have hn : U - 2 = (n : Int) := by omega
  rw [hn] at hoe hAk hsk
  have hjd : okJoin e g = true → StarJoinDown e g := by
    intro hok
    obtain ⟨kv₀, hkv₀, hd₀, hv₀, hk₀, hal₀, hadj₀⟩ := tree_single hbd htree hoe hsA hAk hsk
    have hne : kv₀.1 ≠ kv.1 := by rw [hk₀, hks]; exact other_ne hsk
    have hvg : (arr φ kv key).isValid = true := by rw [← hga]; exact hg.valid
    have hp₁ : SenderPair φ n kv₀ kv key := ⟨hkv₀, hkv, hne, hd₀, hkd, hv₀, hvg⟩
    have hp₂ : SenderPair φ n kv kv₀ key := ⟨hkv, hkv₀, hne.symm, hkd, hd₀, hvg, hv₀⟩
    have hcs : e.current_step = g.current_step := he.step.trans hg.step.symm
    have hse := hke.1.1.1.2
    have hsg := hkg.1.1.1.2
    -- la llegada x = arr kv₀ key equivale a e
    have heaX : EdgesAlive (arr φ kv₀ key) := fun a b h => by
      have := hse.2.2.1 a b ((hadj₀ a b).mpr h)
      exact ⟨(hal₀ a).mp this.1, (hal₀ b).mp this.2⟩
    have heaG : EdgesAlive (arr φ kv key) := hga ▸ hsg.2.2.1
    have hcsX : (arr φ kv₀ key).current_step = U := by
      rw [(stateOk_upFiltering ((line_facts hbd n).1 kv₀ hkv₀) hd₀ hv₀).step]; omega
    have hcsG : (arr φ kv key).current_step = U := by rw [← hga]; exact hg.step
    have hje : (join e g).current_step = U := he.step
    -- las posesiones de la unión
    have hjx : ∀ a b, (join e g).Adj a b ↔ (join (arr φ kv₀ key) (arr φ kv key)).Adj a b := by
      intro a b; rw [adj_join_iff, adj_join_iff, hadj₀, hga]
    have hjy : ∀ a b, (join e g).Adj a b ↔ (join (arr φ kv key) (arr φ kv₀ key)).Adj a b := by
      intro a b; rw [adj_join_iff, adj_join_iff, hadj₀, hga, or_comm]
    have hE' := oneSide_of_senders hbd hp₁ (hIl kv₀ hkv₀) (u := join e g)
      (fun h => by rw [adj_join_iff, hadj₀, hga] at h; exact h) (by rw [hje, hcsX]) heaX heaG
      (H.d2 n kv₀ kv key hp₁) (H.cross n kv₀ kv key hp₁)
      (gapDead_congr (by rw [hje]; exact hcsX.symm ▸ rfl) hjx (H.gap n kv₀ kv key hp₁))
    have hG' := oneSide_of_senders hbd hp₂ (hIl kv hkv) (u := join e g)
      (fun h => by rw [adj_join_iff, hadj₀, hga, or_comm] at h; exact h) (by rw [hje, hcsG]) heaG heaX
      (H.d2 n kv kv₀ key hp₂) (H.cross n kv kv₀ key hp₂)
      (gapDead_congr (by rw [hje]; exact hcsG.symm ▸ rfl) hjy (H.gap n kv kv₀ key hp₂))
    have hE : StarOneSideAt (join e g) e :=
      starOneSideAt_congr rfl (fun _ _ => Iff.rfl) hal₀ hadj₀ hE'
    have hG : StarOneSideAt (join e g) g := by rw [hga]; rw [hga] at hG'; exact hG'
    exact starJoinDown_of_split hcs (by rw [he.step]; omega) hse.2.2.2.2.2.2 hsg.2.2.2.2.2.2 hse.2.2.1 hsg.2.2.1
      hke.1.1.2.1 hkg.1.1.2.1 (H.b1 U key e g hU he hg hke hkg hok) (starPure_of_oneSide hE hG)
  exact ⟨joinStep_ok hU he hke.1 hkg.1 hjd, chainInv_doJoin_ok (by rw [he.step]; omega) hke.2 hkg.2 hjd⟩

/-- **El veredicto del lector bajo B1 y las hipótesis sobre pares de remitentes** (`CrossAt`, `GapDead`, D2). -/
theorem readerVerdict_iff_of_senders (hbd : Bounded φ) (H : HypsSenders φ) :
    readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (fun kv hkv =>
    let h := run_provT hbd (upProv_C φ) (fun _ hU => joinProvT_senders hbd H hU) sInvC_initSeed kv hkv
    ⟨h.1, h.2.1.1.1.2⟩)

end SecLine

end AbsSatBingo.Model
