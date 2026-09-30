-- lean/improves_bingo/AbsSatBingo/Model/LiveExt.lean
import AbsSatBingo.Model.SpineVerdict
import AbsSatBingo.Model.ForbidSound

/-!
# La espina con tríos prohibidos: `LiveExt` ⟹ veredicto

Con los tríos prohibidos (`FORBID`, `ForbidSound`), la espina de `SpineZombie` no elige un nodo que forme un trío
prohibido con dos de los ya elegidos. Una **cadena viva** es una cadena de la espina (`SpineChain`: vecinos dos a
dos, cada uno padre del siguiente) sin ningún trío prohibido.

> **`LiveExt g F`**: toda cadena viva desde la cima hasta un paso `j ≥ 1` se alarga con un padre, viva.

Es `SpineTrio` debilitada: solo pide alargar las cadenas vivas, no todas (`SpineTrio` es falsa en `clause_mix`;
`LiveExt` se cumple en lo medido, `probe_quartet.jl`). Con ella:

* **`liveChain_full`**: desde cualquier cima, una cadena viva llega al paso 0, **sin revisión y sin retroceso**;
* **`noZombie_of_liveExt`**: todo estado cerrado y válido con `LiveExt` lleva una camarilla (`carried_of_spine`);
* **`readerVerdict_iff_of_liveExt`**: el veredicto del lector es la satisfacibilidad si sus estados visitados cumplen
  `LiveExt` para alguna relación de tríos;
* **`spineVerdict_iff_of_liveExt`**: basta con los estados finales revisados, sin ningún pin: la espina con tríos lee
  una solución del primer estado revisado de la línea final.

La relación `F` no necesita ser sólida para esto: una cadena completa es una camarilla, y una camarilla es una
solución (`Decode`). La solidez (`ForbidSound`) es lo que hace creíble que `LiveExt` valga: los tríos que se prohíben
no son de ninguna solución. Lo abierto es demostrar `LiveExt` desde la construcción de la máquina (UP y join); por
`closed_not_chainInv`, no puede salir solo de que el estado sea cerrado.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Machine (Below)

/-- **Una cadena viva** desde el paso `j` hasta la cima: cadena de la espina sin trío prohibido. -/
structure LiveChain (g : GPathB) (F : Trios) (C : Int → PathNodeId) (j : Int) : Prop where
  chain : SpineChain g C j
  live  : ∀ a b c, j ≤ a → a < b → b < c → c ≤ g.current_step - 1 → ¬ Sym F (C a) (C b) (C c)

/-- **`LiveExt`**: toda cadena viva que no ha llegado al paso 0 se alarga, viva, con un paso más. -/
def LiveExt (g : GPathB) (F : Trios) : Prop :=
  ∀ C j, LiveChain g F C j → 1 ≤ j → j ≤ g.current_step - 1 →
    ∃ C', LiveChain g F C' (j - 1) ∧ ∀ k, j ≤ k → C' k = C k

/-- **Desde una cima, la cadena viva llega al paso 0.** -/
theorem liveChain_full {g : GPathB} {F : Trios} (hext : LiveExt g F) (hcs : 1 ≤ g.current_step) {t : PathNodeId}
    (ht : t ∈ g.alive) (hts : t.id.step = g.current_step - 1) :
    ∃ C, LiveChain g F C 0 ∧ C (g.current_step - 1) = t := by
  have key : ∀ i : Nat, (i : Int) ≤ g.current_step - 1 →
      ∃ C, LiveChain g F C (g.current_step - 1 - i) ∧ C (g.current_step - 1) = t := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨fun _ => t, ⟨⟨fun k hk1 hk2 => ⟨by rw [hts]; omega, ht⟩,
        fun _ _ _ _ _ _ => adj_refl _ _ ht, fun k hk1 hk2 => by omega⟩, fun a b c ha hab hbc hc => by omega⟩, rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨C, hC, hCt⟩ := ih (by omega)
      obtain ⟨C', hC', hagree⟩ := hext C _ hC (by push_cast at hi; omega) (by omega)
      refine ⟨C', ?_, by rw [hagree _ (by omega)]; exact hCt⟩
      have : g.current_step - 1 - ((i + 1 : Nat) : Int) = g.current_step - 1 - (i : Int) - 1 := by push_cast; omega
      rw [this]; exact hC'
  obtain ⟨C, hC, hCt⟩ := key (g.current_step - 1).toNat (by omega)
  refine ⟨C, ?_, hCt⟩
  have : g.current_step - 1 - ((g.current_step - 1).toNat : Int) = 0 := by omega
  rw [this] at hC; exact hC

/-- **Ningún zombi bajo `LiveExt`**: en un estado cerrado y válido, la espina con tríos baja hasta una camarilla. -/
theorem noZombie_of_liveExt {g : GPathB} {F : Trios} (hcl : ClosedState g) (hdocs : AliveDocs g) (hb : Below g)
    (hz : AboveZero g) (hls : LinksStep g) (hli : LinksInv g) (hcs : 1 ≤ g.current_step) (hext : LiveExt g F) :
    NoZombie g := by
  intro hv
  have ⟨t, ht, hts⟩ : ∃ q ∈ g.alive, q.id.step = g.current_step - 1 := by
    unfold isValid at hv
    have := List.all_eq_true.mp hv (g.current_step - 1) (mem_intRange (by omega) (by omega))
    obtain ⟨q, hq, hqk⟩ := List.any_eq_true.mp this
    exact ⟨q, hq, by simpa using hqk⟩
  obtain ⟨C, hC, _⟩ := liveChain_full hext hcs ht hts
  exact carried_of_spine hcl hdocs hb hz hls hli hcs hC.chain

end GPathB

namespace SecLine

open GPathB Driver Machine CliqueSplit Final Struct

variable {φ : Cnf}

/-- En un estado visitado válido: cerrado y con todo lo que pide `carried_of_spine`. -/
theorem visited_facts (hbd : Bounded φ) {kv : NodeId × GPathB} (hkv : kv ∈ run φ) {h : GPathB}
    (hvis : Visited kv.2 h) (hval : h.isValid = true) :
    ClosedState h ∧ AliveDocs h ∧ Below h ∧ AboveZero h ∧ LinksStep h ∧ LinksInv h ∧ 1 ≤ h.current_step := by
  have hrun : run φ = steps φ (stepCount φ - 1).toNat (init φ) := rfl
  rw [hrun] at hkv
  obtain ⟨hl, hent, _, _, _⟩ := line_facts hbd (stepCount φ - 1).toNat
  have hok := hl kv hkv
  have hcs : 2 ≤ kv.2.current_step := by
    have hsc : 2 ≤ stepCount φ := by unfold stepCount; omega
    rw [hok.step]; omega
  have hci := cInv_visited hok.docs (hent kv hkv).1.1 hok.below (hent kv hkv).1.2.2.2 hcs h hvis
  obtain ⟨hdocs, _, hb, hz, hcs', hcl⟩ := hci
  have hls := visited_pres revPrims_linksStep (hent kv hkv).1.2.2.1 h hvis
  have hli := visited_pres revPrims_linksInv (line_linksInv hbd _ kv hkv) h hvis
  exact ⟨hcl hval, hdocs, hb, hz, hls, hli, by omega⟩

/-- **Las hipótesis de la espina con tríos**: cada estado válido que visita el lector cumple `LiveExt` para alguna
relación de tríos (la de `FORBID`). -/
def HypsLive (φ : Cnf) : Prop :=
  ∀ kv ∈ run φ, ∀ h, Visited kv.2 h → h.isValid = true → ∃ F, LiveExt h F

/-- **El veredicto del lector es la satisfacibilidad bajo `LiveExt`** en sus estados visitados. -/
theorem readerVerdict_iff_of_liveExt (hbd : Bounded φ) (H : HypsLive φ) : readerVerdict φ = true ↔ Satisfiable φ := by
  apply Decode.readerVerdict_iff_of_noZombie hbd
  intro kv hkv h hvis hval
  obtain ⟨hcl, hdocs, hb, hz, hls, hli, hcs⟩ := visited_facts hbd hkv hvis hval
  obtain ⟨F, hext⟩ := H kv hkv h hvis hval
  exact noZombie_of_liveExt hcl hdocs hb hz hls hli hcs hext hval

/-- **La espina con tríos**: dice SAT si algún estado final, revisado, es válido. No fija nada ni revisa al leer. -/
def SpineVerdict (φ : Cnf) : Prop := ∃ kv ∈ run φ, (reviewAll kv.2).isValid = true

/-- **Sin pins y sin revisión al leer**: si los estados finales revisados cumplen `LiveExt`, la espina con tríos
decide la satisfacibilidad. -/
theorem spineVerdict_iff_of_liveExt (hbd : Bounded φ)
    (H : ∀ kv ∈ run φ, (reviewAll kv.2).isValid = true → ∃ F, LiveExt (reviewAll kv.2) F) :
    SpineVerdict φ ↔ Satisfiable φ := by
  constructor
  · rintro ⟨kv, hkv, hval⟩
    obtain ⟨hcl, hdocs, hb, hz, hls, hli, hcs⟩ := visited_facts hbd hkv Visited.start hval
    obtain ⟨F, hext⟩ := H kv hkv hval
    obtain ⟨S, hc⟩ := noZombie_of_liveExt hcl hdocs hb hz hls hli hcs hext hval
    have hstr : Struct φ (reviewAll kv.2) := struct_visited Visited.start (struct_run hbd kv hkv)
    have hrun : run φ = steps φ (stepCount φ - 1).toNat (init φ) := rfl
    have hcs' : (reviewAll kv.2).current_step = stepCount φ := by
      rw [(shrinks_visited (Visited.start (g₀ := kv.2))).1.step]; exact (Decode.lineOk_run φ kv hkv).step
    exact ⟨Decode.decode S, Decode.sat_of_carried hbd hstr hc hcs'⟩
  · rintro ⟨a, ha⟩
    obtain ⟨g, hf, hc, _⟩ := run_carries φ hbd a ha
    exact ⟨_, List.mem_of_find?_eq_some hf, isValid_of_carried (carried_review (carried_dirty hc _))⟩

end SecLine

end AbsSatBingo.Model
