-- lean/improves_bingo/AbsSatBingo/Model/PinJoin.lean
import AbsSatBingo.Model.PinSide

/-!
# El join sin B1: fijar la historia de la cima

**`PinKeeps2`** (hipótesis sobre el join): en una estructura cerrada de la unión, con una cima `t` y una pareja `z–t`,
fijar el color de los padres y el del abuelo de `t` deja una estructura cerrada dentro con `z`, `t` y `z–t`. Es más
débil que B1: la estrella de `t` concuerda con esas dos fijaciones. Medido (`probe_pinstar.jl`, 6 instancias):
2 527 / 0, 1 942 de ellas con estructuras que mezclan las dos ramas.

**`starJoinDown_of_pin`**: `PinKeeps2` + `pinOneSide2` (desde `ArrHole` y `AbsHole`) + B3 ⟹ `StarJoinDown`.
**`readerVerdict_iff_of_pin`**: el veredicto del lector bajo `PinKeeps2`, `ArrHole` y `AbsHole`. Sin B1.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace SecLine

open GPathB Driver Machine CliqueSplit

variable {φ : Cnf}

/-- **PinKeeps2**: fijar los colores del padre y del abuelo de la cima conserva la pareja `z–t`. -/
def PinKeeps2 : Prop :=
  ∀ T key e g, 2 ≤ T → StateOk T key e → StateOk T key g → SInvC e → SInvC g → okJoin e g = true →
    ∀ (V : PathNodeId → Prop) (R : PathNodeId → PathNodeId → Prop), SecStruct (join e g) V R →
    ∀ t, V t → t.id.step = T - 1 → ∀ z, V z → R z t →
    ∃ (W : PathNodeId → Prop) (R' : PathNodeId → PathNodeId → Prop), SecStruct (join e g) W R' ∧
      (∀ y, W y → V y) ∧ W z ∧ W t ∧ R' z t ∧
      (∀ c, t.parent_id = some c → SecAgrees W c) ∧ (∀ c, t.gparent_id = some c → SecAgrees W c)

/-- Los colores del padre y del abuelo de una cima de la llegada de `kv` (nivel `m + 1`). -/
theorem top_colors (hbd : Bounded φ) {m : Nat} {kv : NodeId × GPathB} (hkv : kv ∈ steps φ (m + 1) (init φ))
    {d : NodeId} (hd : d ∈ sonsOfMap φ kv.1) (hv : (arr φ kv d).isValid = true) {t r : PathNodeId}
    (ht : t ∈ (arr φ kv d).alive) (hts : t.id.step = ((m + 1 : Nat) : Int) + 1)
    (hrs : r.id.step ≤ ((m + 1 : Nat) : Int)) (htr : (arr φ kv d).Adj t r) :
    t.parent_id = some kv.1 ∧ ∃ E ∈ steps φ m (init φ), t.gparent_id = some E.1 := by
  have hok := stateOk_upFiltering ((line_facts hbd (m + 1)).1 kv hkv) hd hv
  refine ⟨top_parent_of_arr hbd hkv hd hv ht (by rw [hok.step]; omega), ?_⟩
  obtain ⟨q, _, h2, hqs, _, hrq⟩ := parent_of_arr_adj hbd hkv hd hv hts hrs htr
  obtain ⟨S, hS, hdS, hvS, hY⟩ := tree_adj (steps_tree m kv hkv) hrq
  have hqs' : q.id.step = (m : Int) + 1 := by rw [hqs]; push_cast; rfl
  have hqa := (edgesAlive_arr hbd hS hvS r q hY).2
  exact ⟨S, hS, by rw [h2, arr_top_parent hbd hS hdS hvS hqa hqs']⟩

/-- **El join con `PinKeeps2` y los huecos.** -/
theorem joinProvT_pin (hbd : Bounded φ) (HP : PinKeeps2) (HR : ArrHole φ) (HA : AbsHole φ) {U : Int}
    (hU : 2 ≤ U) : JoinProvT φ SInvC U := by
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
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := senderPair_pos hp₁; omega⟩
    have hcs : e.current_step = g.current_step := he.step.trans hg.step.symm
    have hse := hke.1.1.1.2
    have hsg := hkg.1.1.1.2
    have hje : (join e g).current_step = U := he.step
    have hu : ∀ {a b}, (join e g).Adj a b → (arr φ kv₀ key).Adj a b ∨ (arr φ kv key).Adj a b := by
      intro a b h; rw [adj_join_iff, hadj₀, hga] at h; exact h
    have hu' : ∀ {a b}, (join e g).Adj a b → (arr φ kv key).Adj a b ∨ (arr φ kv₀ key).Adj a b :=
      fun h => (hu h).symm
    have hcsu : (join e g).current_step = ((m + 1 : Nat) : Int) + 1 + 1 := by rw [hje]; omega
    intro V R hst t htV hts z hzV hzt
    obtain ⟨W, R', hW, hsub, hzW, htW, hR', hpc, hgpc⟩ := HP U key e g hU he hg hke hkg hok V R hst t htV
      (by rw [hts, hje]) z hzV hzt
    -- el testigo de z–t en el paso de los remitentes
    obtain ⟨r, hrl, _, htr⟩ := hst.pair hzt ((m + 1 : Nat) : Int) (by omega) (by rw [hcsu]; omega)
    have hts' : t.id.step = ((m + 1 : Nat) : Int) + 1 := by rw [hts, hje]; omega
    have hrs : r.id.step ≤ ((m + 1 : Nat) : Int) := by omega
    rcases (alive_join e g t).mp (hst.alive htV) with hte | htg
    · -- t en el lado de kv₀
      have htX : t ∈ (arr φ kv₀ key).alive := (hal₀ t).mp hte
      have htgA : t ∉ (arr φ kv key).alive := d2_of_pair hbd hp₁ t htX
        (by rw [(stateOk_upFiltering ((line_facts hbd (m + 1)).1 kv₀ hkv₀) hd₀ hv₀).step, hts']; omega)
      have hXtr : (arr φ kv₀ key).Adj t r := by
        rcases hu (hst.adj htr) with h | h
        · exact h
        · exact absurd (edgesAlive_arr hbd hkv hvg t r h).1 htgA
      obtain ⟨hpar, E, hE, hgp⟩ := top_colors hbd hkv₀ hd₀ hv₀ htX hts' hrs hXtr
      have hside : ∀ {y w}, R' y w → (arr φ kv₀ key).Adj y w :=
        pinOneSide2 hbd HR HA hp₁ hE hu hcsu hW (hpc _ hpar) (hgpc _ hgp)
      refine ⟨W, R', Or.inl (secStruct_to_side (isUnion_join_left hse.2.2.2.2.2.2 hsg.2.2.2.2.2.2
        hse.2.2.1 hsg.2.2.1) hW hse.2.2.2.2.2.2 hse.2.2.1 (fun h => (hadj₀ _ _).mpr (hside h))), hzW, htW, hR', hsub⟩
    · -- t en el lado de kv
      have htX : t ∈ (arr φ kv key).alive := hga ▸ htg
      have htgA : t ∉ (arr φ kv₀ key).alive := d2_of_pair hbd hp₂ t htX
        (by rw [(stateOk_upFiltering ((line_facts hbd (m + 1)).1 kv hkv) hkd hvg).step, hts']; omega)
      have hXtr : (arr φ kv key).Adj t r := by
        rcases hu' (hst.adj htr) with h | h
        · exact h
        · exact absurd (edgesAlive_arr hbd hkv₀ hv₀ t r h).1 htgA
      obtain ⟨hpar, E, hE, hgp⟩ := top_colors hbd hkv hkd hvg htX hts' hrs hXtr
      have hside : ∀ {y w}, R' y w → (arr φ kv key).Adj y w :=
        pinOneSide2 hbd HR HA hp₂ hE hu' hcsu hW (hpc _ hpar) (hgpc _ hgp)
      refine ⟨W, R', Or.inr (secStruct_to_side (isUnion_join_right hcs hse.2.2.2.2.2.2 hsg.2.2.2.2.2.2
        hse.2.2.1 hsg.2.2.1) hW hsg.2.2.2.2.2.2 hsg.2.2.1 (fun h => by rw [hga]; exact hside h)), hzW, htW, hR', hsub⟩
  exact ⟨joinStep_ok hU he hke.1 hkg.1 hjd, chainInv_doJoin_ok (by rw [he.step]; omega) hke.2 hkg.2 hjd⟩

/-- **Las hipótesis sin B1**: `PinKeeps2` en los joins y los dos huecos de una llegada. -/
structure HypsPin (φ : Cnf) : Prop where
  pin : PinKeeps2
  rem : ArrHole φ
  abs : AbsHole φ

/-- **El veredicto del lector bajo `PinKeeps2`, `ArrHole` y `AbsHole`.** -/
theorem readerVerdict_iff_of_pin (hbd : Bounded φ) (H : HypsPin φ) : readerVerdict φ = true ↔ Satisfiable φ :=
  readerVerdict_iff_of_final hbd (fun kv hkv =>
    let h := run_provT hbd (upProv_C φ) (fun _ hU => joinProvT_pin hbd H.pin H.rem H.abs hU) sInvC_initSeed kv hkv
    ⟨h.1, h.2.1.1.1.2⟩)

end SecLine

end AbsSatBingo.Model
