-- lean/improves_bingo/AbsSatBingo/Model/SpineZombie.lean
import AbsSatBingo.Model.Spine
import AbsSatBingo.Model.ChainPin

/-!
# La espina da una camarilla en todo estado cerrado (bajo `SpineTrio`)

**`SpineChain g C j`**: los nodos `C k` de los pasos `j … cima` están vivos, son vecinos dos a dos y cada uno es padre
(en el documento del siguiente) del siguiente. Es lo que construye el lector sin retroceso de `probe_pathreader.jl`.

* **`spine_extend`**: con como mucho dos padres vivos (`TwoParents`) y `ChainTrio` para la cadena, se añade un paso.
* **`spine_full`**: desde cualquier cima, la cadena llega al paso 0.
* **`carried_of_spine`**: una cadena completa es una estructura cerrada fijada en todos los pasos, y por tanto una
  camarilla (`carried_of_pinned`).
* **`noZombie_of_spine`**: todo estado cerrado y válido lleva una camarilla, bajo `TwoParents` y `SpineTrio`.

**Aviso:** `SpineTrio` (la cadena sin revisión nunca se atasca) es falsa en `clause_mix` (ver `SpineVerdict`). La
pieza que sobrevive es **`carried_of_spine`**: una cadena completa (un nodo por paso, vecinos dos a dos, cada uno padre
del siguiente) en un estado cerrado es una camarilla.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

open Machine (Below)

/-- **La cadena de la espina** desde el paso `j` hasta la cima. -/
structure SpineChain (g : GPathB) (C : Int → PathNodeId) (j : Int) : Prop where
  node  : ∀ k, j ≤ k → k ≤ g.current_step - 1 → (C k).id.step = k ∧ C k ∈ g.alive
  adj   : ∀ k l, j ≤ k → k ≤ g.current_step - 1 → j ≤ l → l ≤ g.current_step - 1 → g.Adj (C k) (C l)
  link  : ∀ k, j < k → k ≤ g.current_step - 1 → ∃ n, g.node? (C k) = some n ∧ C (k - 1) ∈ n.parents

/-- **Como mucho dos padres vivos poseídos** por nodo (en bin, los padres solo difieren en el bisabuelo). -/
def TwoParents (g : GPathB) : Prop :=
  ∀ x n, x ∈ g.alive → g.node? x = some n → ∃ a b, ∀ q, LiveParent g n x q → q = a ∨ q = b

/-- **SpineTrio**: en toda cadena de la espina, para cada par de nodos de la cadena por encima del último, algún padre
vivo del último es vecino de los dos. -/
def SpineTrio (g : GPathB) : Prop :=
  ∀ C j, SpineChain g C j → 1 ≤ j → ∀ n, g.node? (C j) = some n →
    ChainTrio g n (C j) (fun w => ∃ k, j < k ∧ k ≤ g.current_step - 1 ∧ w = C k)

/-- En un estado cerrado, un nodo vivo de un paso `≥ 1` tiene un padre vivo poseído. -/
theorem exists_liveParent {g : GPathB} (hcl : ClosedState g) {x : PathNodeId} {n : PNodeB}
    (hn : g.node? x = some n) (hx : x ∈ g.alive) (hx1 : 1 ≤ x.id.step) (hcs : 1 ≤ g.current_step) :
    ∃ q, LiveParent g n x q := by
  obtain ⟨w, hw, hws, hxw⟩ := exists_at hcl hx 0 (Int.le_refl 0) (by omega)
  have hne : x ≠ w := fun h => by subst h; omega
  obtain ⟨q, hq, hxq, _⟩ := hcl.par hxw hne hn hx1
  exact ⟨q, hq, hxq.2.1, hxq.2.2⟩

/-- **Un paso de la espina.** -/
theorem spine_extend {g : GPathB} (hcl : ClosedState g) (hls : LinksStep g) (hdocs : AliveDocs g)
    (htwo : TwoParents g) (htrio : SpineTrio g) {C : Int → PathNodeId} {j : Int} (hC : SpineChain g C j)
    (hj : 1 ≤ j) (hjt : j ≤ g.current_step - 1) :
    ∃ C', SpineChain g C' (j - 1) ∧ ∀ k, j ≤ k → C' k = C k := by
  obtain ⟨hxs, hxa⟩ := hC.node j (Int.le_refl j) hjt
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hdocs hxa)
  have hex := exists_liveParent hcl hn hxa (by omega) (by omega)
  obtain ⟨a, b, hab⟩ := htwo (C j) n hxa hn
  obtain ⟨p, hp, hpK⟩ := parent_for_chain hab hex (htrio C j hC hj n hn)
  have hid : n.id = C j := node?_id hn
  have hps : p.id.step = j - 1 := by
    have := (hls n (node?_mem hn)).1 p hp.1
    rw [hid, hxs] at this; omega
  classical
  let C' : Int → PathNodeId := fun k => if k = j - 1 then p else C k
  have hC'a : ∀ k, j ≤ k → C' k = C k := fun k hk => by
    simp only [C']; rw [if_neg (by omega)]
  have hC'p : C' (j - 1) = p := by simp [C']
  refine ⟨C', ⟨?_, ?_, ?_⟩, hC'a⟩
  · intro k hk1 hk2
    by_cases hk : k = j - 1
    · subst hk; rw [hC'p]; exact ⟨hps, hp.2.1⟩
    · rw [hC'a k (by omega)]; exact hC.node k (by omega) hk2
  · -- p es vecino de todo lo de arriba
    have hpk : ∀ k, j ≤ k → k ≤ g.current_step - 1 → g.Adj p (C k) := by
      intro k hk1 hk2
      by_cases hkj : k = j
      · subst hkj; exact (adj_symm _ _ _).mp hp.2.2
      · exact hpK (C k) ⟨k, by omega, hk2, rfl⟩
    intro k l hk1 hk2 hl1 hl2
    by_cases hk : k = j - 1 <;> by_cases hl : l = j - 1
    · subst hk; subst hl; rw [hC'p]; exact adj_refl _ _ hp.2.1
    · subst hk; rw [hC'p, hC'a l (by omega)]; exact hpk l (by omega) hl2
    · subst hl; rw [hC'p, hC'a k (by omega)]; exact (adj_symm _ _ _).mp (hpk k (by omega) hk2)
    · rw [hC'a k (by omega), hC'a l (by omega)]; exact hC.adj k l (by omega) hk2 (by omega) hl2
  · intro k hk1 hk2
    by_cases hkj : k = j
    · subst hkj
      refine ⟨n, by rw [hC'a k (Int.le_refl k)]; exact hn, ?_⟩
      rw [hC'p]; exact hp.1
    · rw [hC'a k (by omega), hC'a (k - 1) (by omega)]
      exact hC.link k (by omega) hk2

/-- **Desde una cima, la cadena llega al paso 0.** -/
theorem spine_full {g : GPathB} (hcl : ClosedState g) (hls : LinksStep g) (hdocs : AliveDocs g)
    (htwo : TwoParents g) (htrio : SpineTrio g) (hcs : 1 ≤ g.current_step) {t : PathNodeId}
    (ht : t ∈ g.alive) (hts : t.id.step = g.current_step - 1) : ∃ C, SpineChain g C 0 ∧ C (g.current_step - 1) = t := by
  have key : ∀ i : Nat, (i : Int) ≤ g.current_step - 1 →
      ∃ C, SpineChain g C (g.current_step - 1 - i) ∧ C (g.current_step - 1) = t := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨fun _ => t, ⟨fun k hk1 hk2 => ⟨by rw [hts]; omega, ht⟩,
        fun _ _ _ _ _ _ => adj_refl _ _ ht, fun k hk1 hk2 => by omega⟩, rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨C, hC, hCt⟩ := ih (by omega)
      obtain ⟨C', hC', hagree⟩ := spine_extend hcl hls hdocs htwo htrio hC (by push_cast at hi; omega) (by omega)
      refine ⟨C', ?_, by rw [hagree _ (by omega)]; exact hCt⟩
      have : g.current_step - 1 - ((i + 1 : Nat) : Int) = g.current_step - 1 - (i : Int) - 1 := by push_cast; omega
      rw [this]; exact hC'
  obtain ⟨C, hC, hCt⟩ := key (g.current_step - 1).toNat (by omega)
  refine ⟨C, ?_, hCt⟩
  have : g.current_step - 1 - ((g.current_step - 1).toNat : Int) = 0 := by omega
  rw [this] at hC; exact hC

/-- **Una cadena completa de la espina es una camarilla.** -/
theorem carried_of_spine {g : GPathB} (hcl : ClosedState g) (hdocs : AliveDocs g) (hb : Below g) (hz : AboveZero g)
    (hls : LinksStep g) (hli : LinksInv g) (hcs : 1 ≤ g.current_step) {C : Int → PathNodeId}
    (hC : SpineChain g C 0) : ∃ S, Carried g S := by
  let W : PathNodeId → Prop := fun y => ∃ k, 0 ≤ k ∧ k ≤ g.current_step - 1 ∧ y = C k
  let R : PathNodeId → PathNodeId → Prop := fun y w => W y ∧ W w ∧ g.Adj y w
  have hWa : ∀ {y}, W y → y ∈ g.alive := by
    rintro y ⟨k, h0, h1, rfl⟩; exact (hC.node k h0 h1).2
  have hWs : ∀ {k}, 0 ≤ k → k ≤ g.current_step - 1 → (C k).id.step = k := fun h0 h1 => (hC.node _ h0 h1).1
  have hWstep : ∀ {y}, W y → y = C y.id.step ∧ 0 ≤ y.id.step ∧ y.id.step ≤ g.current_step - 1 := by
    rintro y ⟨k, h0, h1, rfl⟩; rw [hWs h0 h1]; exact ⟨rfl, h0, h1⟩
  have hadjW : ∀ {y w}, W y → W w → g.Adj y w := by
    rintro y w ⟨k, hk0, hk1, rfl⟩ ⟨l, hl0, hl1, rfl⟩; exact hC.adj k l hk0 hk1 hl0 hl1
  have hWC : ∀ {k}, 0 ≤ k → k ≤ g.current_step - 1 → W (C k) := fun h0 h1 => ⟨_, h0, h1, rfl⟩
  -- el documento de C k, su padre C (k-1) y su hijo C (k+1)
  have hpar : ∀ {k n}, 1 ≤ k → k ≤ g.current_step - 1 → g.node? (C k) = some n → C (k - 1) ∈ n.parents := by
    intro k n hk1 hk2 hn
    obtain ⟨n', hn', hp⟩ := hC.link k (by omega) hk2
    rw [hn] at hn'; cases hn'; exact hp
  have hson : ∀ {k n}, 0 ≤ k → k + 1 ≤ g.current_step - 1 → g.node? (C k) = some n → C (k + 1) ∈ n.sons := by
    intro k n hk0 hk1 hn
    obtain ⟨m, hm, hp⟩ := hC.link (k + 1) (by omega) hk1
    rw [show k + 1 - 1 = k by omega] at hp
    have hcomp := (hli.2.2 m (node?_mem hm)).1 _ hp
    rw [node?_id hm] at hcomp
    have hadj : g.Adj n.id (C (k + 1)) := by rw [node?_id hn]; exact hC.adj k (k + 1) hk0 (by omega) (by omega) hk1
    rw [← node?_id hn] at hcomp
    exact (hli.2.1 n (node?_mem hn) (C (k + 1)) (hC.node (k + 1) (by omega) hk1).2 hadj).2 hcomp
  have hst : SecStruct g W R := by
    refine ⟨fun hy => hWa hy, fun hy => ⟨hy, hy, adj_refl _ _ (hWa hy)⟩,
      fun ⟨h1, h2, h3⟩ => ⟨h2, h1, (adj_symm _ _ _).mp h3⟩, fun h => ⟨h.1, h.2.1⟩, fun h => h.2.2, ?_, ?_, ?_, ?_⟩
    · -- parejas: el nodo de la cadena en ese paso
      intro y w hyw l h0 h1
      have hCl := hWC (k := l) h0 (by omega)
      exact ⟨C l, hWs h0 (by omega), ⟨hyw.1, hCl, hadjW hyw.1 hCl⟩, ⟨hyw.2.1, hCl, hadjW hyw.2.1 hCl⟩⟩
    · -- documentos: padre e hijo en la cadena
      intro y hy
      obtain ⟨hyC, hy0, hy1⟩ := hWstep hy
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (node?_isSome_of_alive hdocs (hWa hy))
      refine ⟨n, hn, fun hp => ?_, fun hne => ?_⟩
      · by_cases hk : 1 ≤ y.id.step
        · have hn' : g.node? (C y.id.step) = some n := by rw [← hyC]; exact hn
          have hCk := hWC (k := y.id.step - 1) (by omega) (by omega)
          exact ⟨_, hpar hk hy1 hn', hy, hCk, hadjW hy hCk⟩
        · -- en el paso 0 no hay padre: el estado cerrado daría uno en el paso -1
          exfalso
          obtain ⟨n'', hn'', hp'', _⟩ := hcl.node (hWa hy)
          obtain ⟨q, hq, hyq⟩ := hp'' hp
          have h1 := (hls n'' (node?_mem hn'')).1 q hq
          rw [node?_id hn''] at h1
          obtain ⟨m, hm, hmq⟩ := hdocs q hyq.2.1
          have h2 := hz m hm
          rw [hmq] at h2
          omega
      · have hk : y.id.step + 1 ≤ g.current_step - 1 := by omega
        have hn' : g.node? (C y.id.step) = some n := by rw [← hyC]; exact hn
        have hCk := hWC (k := y.id.step + 1) (by omega) hk
        exact ⟨_, hson hy0 hk hn', hy, hCk, hadjW hy hCk⟩
    · -- par
      intro x w n hxw _ hn hx1
      obtain ⟨hxC, _, hx2⟩ := hWstep hxw.1
      have hn' : g.node? (C x.id.step) = some n := by rw [← hxC]; exact hn
      have hCk := hWC (k := x.id.step - 1) (by omega) (by omega)
      exact ⟨_, hpar hx1 hx2 hn', ⟨hxw.1, hCk, hadjW hxw.1 hCk⟩, ⟨hCk, hxw.2.1, hadjW hCk hxw.2.1⟩⟩
    · -- son
      intro x w n hxw _ hn hx1
      obtain ⟨hxC, hx0, _⟩ := hWstep hxw.1
      have hn' : g.node? (C x.id.step) = some n := by rw [← hxC]; exact hn
      have hk : x.id.step + 1 ≤ g.current_step - 1 := by omega
      have hCk := hWC (k := x.id.step + 1) (by omega) hk
      exact ⟨_, hson hx0 hk hn', ⟨hxw.1, hCk, hadjW hxw.1 hCk⟩, ⟨hCk, hxw.2.1, hadjW hCk hxw.2.1⟩⟩
  have hpin : PinnedFrom W 0 := by
    intro y w hy hw _ hyw
    rw [(hWstep hy).1, (hWstep hw).1, hyw]
  obtain ⟨S, hS, _⟩ := carried_of_pinned hdocs hb hz hls hst hpin (hWC (k := 0) (Int.le_refl 0) (by omega))
  exact ⟨S, hS⟩

/-- **Ningún zombi en un estado cerrado**, bajo `TwoParents` y `SpineTrio`: la espina baja desde cualquier cima sin
retroceso hasta una camarilla. -/
theorem noZombie_of_spine {g : GPathB} (hcl : ClosedState g) (hdocs : AliveDocs g) (hb : Below g) (hz : AboveZero g)
    (hls : LinksStep g) (hli : LinksInv g) (hcs : 1 ≤ g.current_step) (htwo : TwoParents g) (htrio : SpineTrio g) :
    NoZombie g := by
  intro hv
  have ⟨t, ht, hts⟩ : ∃ q ∈ g.alive, q.id.step = g.current_step - 1 := by
    unfold isValid at hv
    have := List.all_eq_true.mp hv (g.current_step - 1)
      (mem_intRange (by omega) (by omega))
    obtain ⟨q, hq, hqk⟩ := List.any_eq_true.mp this
    exact ⟨q, hq, by simpa using hqk⟩
  obtain ⟨C, hC, _⟩ := spine_full hcl hls hdocs htwo htrio hcs ht hts
  exact carried_of_spine hcl hdocs hb hz hls hli hcs hC

end GPathB

end AbsSatBingo.Model
