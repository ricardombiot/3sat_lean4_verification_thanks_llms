-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainPreM.lean
import AbsSatBingo.Model.ForbidOnChainPreGen

/-!
# El preproceso con varias cláusulas por bloque

**`ChainInM φ n zone sv zi e0a e0b eLa eLb bk`**: `φ` es una cadena de `n` bloques con la numeración de `ChainNum`, y
`bk c` es el bloque de la cláusula `c`. En un bloque puede haber **varias cláusulas**, en cualquier orden dentro de `φ`;
las de un bloque de en medio tienen sus tres variables distintas. Entonces son, todas, sobre sus dos separadores y su
variable de dentro (`midM`): en un bloque de en medio no hay más variables.

La construcción, la de `test_3sat/preprocess_chain.jl`:

* **`prsM`**: los bloques en orden, y en cada uno sus cláusulas reescritas con `preClM` (la de dentro, de en medio),
  cada una con su bloque.
* **`preCnfM`**: esas cláusulas. Los bloques no bajan a lo largo de la lista, así que la preprocesada está en
  **`ChainOrdM`** (`chainOrdM_pre`).

Resultado: **`renaming_preM`**, **`spineVerdictOn_preM_iff`** y **`machineExact_preM`**: la espina sobre la preprocesada
decide toda cadena con varias cláusulas por bloque, de cualquier longitud y numeración.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- **Una cadena de entrada con varias cláusulas por bloque.** -/
structure ChainInM (φ : Cnf) (n : Nat) (zone sv zi : Nat → Nat) (e0a e0b eLa eLb : Nat) (bk : Clause → Nat) :
    Prop where
  N    : ChainNum φ n zone sv zi e0a e0b eLa eLb
  hbk  : ∀ c ∈ φ.clauses, bk c < n ∧ ClIn (BlkN n zone (bk c)) c
  dist : ∀ c ∈ φ.clauses, 1 ≤ bk c → bk c + 1 < n → c.l1.v ≠ c.l2.v ∧ c.l1.v ≠ c.l3.v ∧ c.l2.v ≠ c.l3.v

/-! ## La construcción -/

section Def

variable (φ : Cnf) (n : Nat) (zone sv zi : Nat → Nat) (e0a eLa : Nat) (bk : Clause → Nat)

/-- La cláusula nueva de `c`, del bloque `p`. -/
def preClM (p : Nat) (c : Clause) : Clause :=
  if 1 ≤ p ∧ p + 1 < n then
    ⟨renL (fPre n zone e0a eLa) (litOf c (sv p)), renL (fPre n zone e0a eLa) (litOf c (zi p)),
      renL (fPre n zone e0a eLa) (litOf c (sv (p + 1)))⟩
  else ⟨renL (fPre n zone e0a eLa) c.l1, renL (fPre n zone e0a eLa) c.l2, renL (fPre n zone e0a eLa) c.l3⟩

/-- Los bloques en orden, y en cada uno sus cláusulas nuevas, con su bloque. -/
def prsM : List (Nat × Clause) :=
  (List.range n).flatMap (fun p => (φ.clauses.filter (fun c => bk c == p)).map (fun c => (p, preClM n zone sv zi e0a eLa p c)))

/-- **La fórmula preprocesada.** -/
def preCnfM : Cnf := ⟨2 * n + 1, (prsM φ n zone sv zi e0a eLa bk).map Prod.snd⟩

end Def

section Main

variable {n : Nat} {zone sv zi : Nat → Nat} {e0a e0b eLa eLb : Nat} {bk : Clause → Nat}

/-- **En un bloque de en medio, toda cláusula es sobre sus dos separadores y su variable de dentro.** -/
theorem midM (C : ChainInM φ n zone sv zi e0a e0b eLa eLb bk) {c : Clause} (hc : c ∈ φ.clauses)
    (h1 : 1 ≤ bk c) (h2 : bk c + 1 < n) :
    ClVar c (sv (bk c)) ∧ ClVar c (zi (bk c)) ∧ ClVar c (sv (bk c + 1)) := by
  obtain ⟨_, hB⟩ := C.hbk c hc
  obtain ⟨d12, d13, d23⟩ := C.dist c hc h1 h2
  have three : ∀ {y}, BlkN n zone (bk c) y → y = sv (bk c) ∨ y = zi (bk c) ∨ y = sv (bk c + 1) := by
    intro y hy
    rcases hy with h | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr (Or.inl (C.N.D.cardM _ h1 h2 _ _ h (C.N.hzi _ h1 h2)))
    · exact Or.inl (C.N.D.sep1 _ h1 (by omega) _ _ h (C.N.hsv _ h1 (by omega)))
    · exact Or.inr (Or.inr (C.N.D.sep1 _ (by omega) h2 _ _ (by omega) (C.N.hsv _ (by omega) h2)))
  have a := three hB.1
  have b := three hB.2.1
  have d := three hB.2.2
  unfold ClVar
  omega

theorem mem_prsM {x : Nat × Clause} (h : x ∈ prsM φ n zone sv zi e0a eLa bk) :
    ∃ c, c ∈ φ.clauses ∧ bk c < n ∧ x = (bk c, preClM n zone sv zi e0a eLa (bk c) c) := by
  unfold prsM at h
  obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp h
  obtain ⟨c, hcf, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hc, e⟩ := List.mem_filter.mp hcf
  have e : bk c = p := by simpa using e
  subst e
  exact ⟨c, hc, List.mem_range.mp hp, rfl⟩

theorem mem_preCnfM {c' : Clause} (h : c' ∈ (preCnfM φ n zone sv zi e0a eLa bk).clauses) :
    ∃ c, c ∈ φ.clauses ∧ bk c < n ∧ c' = preClM n zone sv zi e0a eLa (bk c) c := by
  unfold preCnfM at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨c, hc, hn, rfl⟩ := mem_prsM hx
  exact ⟨c, hc, hn, rfl⟩

theorem preClM_mem {c : Clause} (hc : c ∈ φ.clauses) (hn : bk c < n) :
    preClM n zone sv zi e0a eLa (bk c) c ∈ (preCnfM φ n zone sv zi e0a eLa bk).clauses := by
  unfold preCnfM prsM
  refine List.mem_map.mpr ⟨(bk c, preClM n zone sv zi e0a eLa (bk c) c), List.mem_flatMap.mpr ⟨bk c,
    List.mem_range.mpr hn, List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simp⟩, rfl⟩⟩, rfl⟩

/-- Las variables de la cláusula nueva: imágenes de las de `c`. -/
theorem preClM_vars (C : ChainInM φ n zone sv zi e0a e0b eLa eLb bk) {c : Clause} (hc : c ∈ φ.clauses) {w : Nat}
    (hw : ClVar (preClM n zone sv zi e0a eLa (bk c) c) w) : ∃ z, ClVar c z ∧ w = fPre n zone e0a eLa z := by
  unfold preClM at hw
  split at hw
  · rename_i hm
    obtain ⟨a, b, d⟩ := midM C hc hm.1 hm.2
    rcases hw with e | e | e
    · exact ⟨_, a, by rw [e]; simp only [renL, litOf_v a]⟩
    · exact ⟨_, b, by rw [e]; simp only [renL, litOf_v b]⟩
    · exact ⟨_, d, by rw [e]; simp only [renL, litOf_v d]⟩
  · rcases hw with e | e | e
    · exact ⟨_, Or.inl rfl, by rw [e]; rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), by rw [e]; rfl⟩
    · exact ⟨_, Or.inr (Or.inr rfl), by rw [e]; rfl⟩

/-- **El renombrado.** -/
theorem renaming_preM (C : ChainInM φ n zone sv zi e0a e0b eLa eLb bk) :
    Renaming φ (preCnfM φ n zone sv zi e0a eLa bk) (fPre n zone e0a eLa) (gPre n sv zi e0a e0b eLa eLb) := by
  have inz : ∀ {c}, c ∈ φ.clauses → ∀ {l}, l ∈ clLits c → InChainZ n zone l.v := fun {_} hc {_} hl =>
    inChainZ_of_blk (C.hbk _ hc).1 (clIn_var (C.hbk _ hc).2 (clLits_var hl))
  refine ⟨fun c hc l hl => gfPre C.N (inz hc hl), fun c hc => ?_, fun c' hc' => ?_⟩
  · refine ⟨preClM n zone sv zi e0a eLa (bk c) c, preClM_mem hc (C.hbk c hc).1, fun l' hl' => ?_⟩
    unfold preClM at hl'
    split at hl'
    · unfold clLits at hl'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
      rcases hl' with rfl | rfl | rfl
      · exact ⟨_, litOf_mem _ _, rfl, rfl⟩
      · exact ⟨_, litOf_mem _ _, rfl, rfl⟩
      · exact ⟨_, litOf_mem _ _, rfl, rfl⟩
    · unfold clLits at hl'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
      rcases hl' with rfl | rfl | rfl
      · exact ⟨_, by simp [clLits], rfl, rfl⟩
      · exact ⟨_, by simp [clLits], rfl, rfl⟩
      · exact ⟨_, by simp [clLits], rfl, rfl⟩
  · obtain ⟨c, hc, hn, rfl⟩ := mem_preCnfM hc'
    refine ⟨c, hc, fun l hl => ?_⟩
    unfold preClM
    split
    · rename_i hm
      obtain ⟨d12, d13, d23⟩ := C.dist c hc hm.1 hm.2
      have hs := litOf_self d12 d13 d23 hl
      -- la variable de `l` es una de las tres
      have hv : l.v = sv (bk c) ∨ l.v = zi (bk c) ∨ l.v = sv (bk c + 1) := by
        have hB := clIn_var (C.hbk c hc).2 (clLits_var hl)
        rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩
        · exact Or.inr (Or.inl (C.N.D.cardM _ hm.1 hm.2 _ _ h (C.N.hzi _ hm.1 hm.2)))
        · exact Or.inl (C.N.D.sep1 _ hm.1 (by omega) _ _ h (C.N.hsv _ hm.1 (by omega)))
        · exact Or.inr (Or.inr (C.N.D.sep1 _ (by omega) hm.2 _ _ (by omega) (C.N.hsv _ (by omega) hm.2)))
      rcases hv with e | e | e
      · exact ⟨renL (fPre n zone e0a eLa) (litOf c (sv (bk c))), by simp [clLits], by rw [← e, hs]; rfl,
          by rw [← e, hs]; rfl⟩
      · exact ⟨renL (fPre n zone e0a eLa) (litOf c (zi (bk c))), by simp [clLits], by rw [← e, hs]; rfl,
          by rw [← e, hs]; rfl⟩
      · exact ⟨renL (fPre n zone e0a eLa) (litOf c (sv (bk c + 1))), by simp [clLits], by rw [← e, hs]; rfl,
          by rw [← e, hs]; rfl⟩
    · unfold clLits at hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact ⟨renL (fPre n zone e0a eLa) c.l1, by simp [clLits], rfl, rfl⟩
      · exact ⟨renL (fPre n zone e0a eLa) c.l2, by simp [clLits], rfl, rfl⟩
      · exact ⟨renL (fPre n zone e0a eLa) c.l3, by simp [clLits], rfl, rfl⟩

/-- La preprocesada tiene sus variables en rango. -/
theorem bounded_preM (C : ChainInM φ n zone sv zi e0a e0b eLa eLb bk) :
    Bounded (preCnfM φ n zone sv zi e0a eLa bk) := by
  intro c' hc'
  obtain ⟨c, hc, hn, rfl⟩ := mem_preCnfM hc'
  have bd : ∀ {w}, ClVar (preClM n zone sv zi e0a eLa (bk c) c) w → w < 2 * n + 1 := fun hw => by
    obtain ⟨z, hz, rfl⟩ := preClM_vars C hc hw
    exact fPre_lt C.N (inChainZ_of_blk hn (clIn_var (C.hbk c hc).2 hz))
  exact ⟨bd (Or.inl rfl), bd (Or.inr (Or.inl rfl)), bd (Or.inr (Or.inr rfl))⟩

/-- **La preprocesada está en `ChainOrdM`.** -/
theorem chainOrdM_pre (C : ChainInM φ n zone sv zi e0a e0b eLa eLb bk) :
    ChainOrdM (preCnfM φ n zone sv zi e0a eLa bk) n (zoneO n) svO (prsM φ n zone sv zi e0a eLa bk) := by
  have two := C.N.D.two
  -- las cláusulas nuevas, en su bloque
  have blkO : ∀ {c}, c ∈ φ.clauses → ClIn (BlkN n (zoneO n) (bk c)) (preClM n zone sv zi e0a eLa (bk c) c) := by
    intro c hc
    have t : ∀ {w}, ClVar (preClM n zone sv zi e0a eLa (bk c) c) w → BlkN n (zoneO n) (bk c) w := fun hw => by
      obtain ⟨z, hz, rfl⟩ := preClM_vars C hc hw
      have hB := clIn_var (C.hbk c hc).2 hz
      unfold BlkN at hB ⊢
      rw [fPre_zone C.N (inChainZ_of_blk (C.hbk c hc).1 hB)]; exact hB
    exact ⟨t (Or.inl rfl), t (Or.inr (Or.inl rfl)), t (Or.inr (Or.inr rfl))⟩
  have getp : ∀ j c', (preCnfM φ n zone sv zi e0a eLa bk).clauses[j]? = some c' →
      ∃ c, c ∈ φ.clauses ∧ bk c < n ∧ c' = preClM n zone sv zi e0a eLa (bk c) c :=
    fun _ _ h => mem_preCnfM (List.mem_of_getElem? h)
  refine ⟨⟨two, fun w a b => ?_, fun i h1 h2 w w' hw hw' => ?_, fun y1 y2 y3 a b c d12 d13 d23 => ?_,
      fun y1 y2 y3 a b c d12 d13 d23 => ?_, fun j h1 h2 w w' hw hw' => ?_, fun c' hc' => ?_⟩,
    fun k h1 h2 => ?_, rfl, fun x hx => ?_, ?_, fun w p h1 h2 hz => ?_, fun j c' hj w p h1 h2 hz hcv => ?_⟩
  · -- los separadores, en rango
    show w < 2 * n + 1
    rcases zoneO_cases n w with ⟨_, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ <;> omega
  · -- un separador por zona
    have tz : ∀ {y}, zoneO n y = n + i → y = 2 * i := by
      intro y h
      rcases zoneO_cases n y with ⟨_, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ <;> omega
    exact (tz hw).trans (tz hw').symm
  · -- el bloque 0: a lo sumo `0, 1`
    have tz : ∀ {y}, zoneO n y = 0 → y ≤ 1 := by
      intro y h
      rcases zoneO_cases n y with ⟨_, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ <;> omega
    have := tz a; have := tz b; have := tz c; omega
  · -- el último: a lo sumo `2n - 1, 2n`
    have tz : ∀ {y}, zoneO n y = n - 1 → 2 * n - 1 ≤ y ∧ y ≤ 2 * n := by
      intro y h
      rcases zoneO_cases n y with ⟨_, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ <;> omega
    have := tz a; have := tz b; have := tz c; omega
  · exact (zoneO_mid h1 h2 hw).trans (zoneO_mid h1 h2 hw').symm
  · -- las cláusulas, en su bloque
    obtain ⟨c, hc, hn, rfl⟩ := mem_preCnfM hc'
    exact Or.inr ⟨bk c, hn, blkO hc⟩
  · -- los separadores nuevos
    show zoneO n (2 * k) = n + k
    unfold zoneO; rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]; omega
  · obtain ⟨c, hc, hn, rfl⟩ := mem_prsM hx
    exact ⟨hn, blkO hc⟩
  · -- los bloques no bajan
    unfold prsM
    refine List.pairwise_flatMap.mpr ⟨fun p _ => List.pairwise_map.mpr (List.pairwise_of_forall
      (fun _ _ => Nat.le_refl _)), List.pairwise_lt_range.imp (fun {p q} hpq => ?_)⟩
    intro x hx y hy
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
    exact Nat.le_of_lt hpq
  · -- `NumLocal`
    have e := zoneO_mid h1 h2 hz
    subst e
    refine ⟨by omega, by show 2 * p + 1 + 1 < 2 * n + 1; omega, Or.inl ?_, Or.inr ?_⟩ <;> simp only [svO] <;> omega
  · -- `LitLocal`
    obtain ⟨c, hc, hn, rfl⟩ := getp j c' hj
    have e := zoneO_mid h1 h2 hz
    subst e
    -- la cláusula es del bloque `p`
    have hjp : bk c = p := by
      have hB := clIn_var (blkO hc) hcv
      rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    obtain ⟨a, b, d⟩ := midM C hc (by omega) (by omega)
    rw [hjp] at a b d
    have fs : ∀ {k}, 1 ≤ k → k < n → fPre n zone e0a eLa (sv k) = 2 * k := fun h1 h2 => by
      unfold fPre; rw [C.N.hsv _ h1 h2, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      omega
    have fz : fPre n zone e0a eLa (zi p) = 2 * p + 1 := by
      unfold fPre; rw [C.N.hzi p h1 h2, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [hjp]
    unfold preClM; rw [if_pos ⟨h1, h2⟩]
    simp only [renL, litOf_v a, litOf_v b, litOf_v d, svO]
    exact ⟨fz, Or.inl (fs h1 (by omega)), Or.inr (fs (by omega) h2)⟩

end Main

namespace MachineOn

open GPathB Driver Machine

variable {n : Nat} {zone sv zi : Nat → Nat} {e0a e0b eLa eLb : Nat} {bk : Clause → Nat}

/-- **La espina sobre la preprocesada decide toda cadena con varias cláusulas por bloque, de cualquier longitud.** -/
theorem spineVerdictOn_preM_iff (C : ChainInM φ n zone sv zi e0a e0b eLa eLb bk) :
    SpineVerdictOn (preCnfM φ n zone sv zi e0a eLa bk) ↔ Satisfiable φ :=
  (spineVerdictOn_iff_of_chainOrdM (bounded_preM C) (chainOrdM_pre C)).trans
    (satisfiable_iff_of_renaming (renaming_preM C)).symm

/-- **Y la máquina sobre la preprocesada es exacta.** -/
theorem machineExact_preM (C : ChainInM φ n zone sv zi e0a e0b eLa eLb bk) :
    MachineExact (preCnfM φ n zone sv zi e0a eLa bk) :=
  machineExact_of_chainOrdM (bounded_preM C) (chainOrdM_pre C)

end MachineOn

end AbsSatBingo.Model

/-! ## La instancia: `chain4m_cross` -/

namespace AbsSatBingo.Model

open AbsSatBin.Cnf

/-- **`chain4m_cross`** (`scripts/cnf/multi/chain4m_cross.cnf`, variables desde 0): cuatro bloques
`{x0, x7, x4}`, `{x4, x2, x6}`, `{x6, x8, x1}`, `{x1, x3, x5}` con dos o tres cláusulas cada uno, desordenadas. -/
def chain4M : Cnf :=
  ⟨9, [⟨⟨6, false⟩, ⟨8, true⟩, ⟨1, true⟩⟩, ⟨⟨0, true⟩, ⟨7, true⟩, ⟨4, true⟩⟩, ⟨⟨2, true⟩, ⟨4, false⟩, ⟨6, true⟩⟩,
    ⟨⟨1, false⟩, ⟨3, true⟩, ⟨5, true⟩⟩, ⟨⟨2, false⟩, ⟨4, true⟩, ⟨6, true⟩⟩, ⟨⟨5, true⟩, ⟨3, false⟩, ⟨1, true⟩⟩,
    ⟨⟨0, false⟩, ⟨7, false⟩, ⟨4, true⟩⟩, ⟨⟨4, false⟩, ⟨2, false⟩, ⟨6, false⟩⟩, ⟨⟨6, true⟩, ⟨8, false⟩, ⟨1, false⟩⟩,
    ⟨⟨3, false⟩, ⟨5, false⟩, ⟨1, true⟩⟩]⟩

/-- **Su preprocesada** (`scripts/cnf/multi/pre/chain4m_cross_pre.cnf`). -/
def chain4MP : Cnf :=
  ⟨9, [⟨⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩⟩, ⟨⟨0, false⟩, ⟨1, false⟩, ⟨2, true⟩⟩, ⟨⟨2, false⟩, ⟨3, true⟩, ⟨4, true⟩⟩,
    ⟨⟨2, true⟩, ⟨3, false⟩, ⟨4, true⟩⟩, ⟨⟨2, false⟩, ⟨3, false⟩, ⟨4, false⟩⟩, ⟨⟨4, false⟩, ⟨5, true⟩, ⟨6, true⟩⟩,
    ⟨⟨4, true⟩, ⟨5, false⟩, ⟨6, false⟩⟩, ⟨⟨6, false⟩, ⟨7, true⟩, ⟨8, true⟩⟩, ⟨⟨8, true⟩, ⟨7, false⟩, ⟨6, true⟩⟩,
    ⟨⟨7, false⟩, ⟨8, false⟩, ⟨6, true⟩⟩]⟩

namespace GPathB

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 20000

def vals4M : List Nat := [0, 7, 1, 3, 5, 3, 6, 0, 2]
def sv4M (k : Nat) : Nat := [0, 4, 6, 1].getD k 0
def zi4M (p : Nat) : Nat := [0, 2, 8, 0].getD p 0
/-- El bloque de una cláusula: el de su primera variable de dentro. -/
def bk4M (c : Clause) : Nat :=
  if zoneV 4 vals4M c.l1.v < 4 then zoneV 4 vals4M c.l1.v
  else if zoneV 4 vals4M c.l2.v < 4 then zoneV 4 vals4M c.l2.v else zoneV 4 vals4M c.l3.v

theorem chainInM_chain4M : ChainInM chain4M 4 (zoneV 4 vals4M) sv4M zi4M 0 7 3 5 bk4M := by
  refine ⟨⟨chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    fun k h1 h2 => ?_, fun p h1 h2 => ?_, fun z hz => ?_, fun z hz => ?_⟩, fun c hc => ?_, fun c hc h1 h2 => ?_⟩
  · have h : ∀ k, k < 4 → 1 ≤ k → zoneV 4 vals4M (sv4M k) = 4 + k := by decide
    exact h k h2 h1
  · have h : ∀ p, p < 4 → 1 ≤ p → p + 1 < 4 → zoneV 4 vals4M (zi4M p) = p := by decide
    exact h p (by omega) h1 h2
  · have hzl : z < vals4M.length := zoneV_small hz (by omega)
    have h : ∀ z, z < vals4M.length → zoneV 4 vals4M z = 0 → z = 0 ∨ z = 7 := by decide
    exact h z hzl hz
  · have hzl : z < vals4M.length := zoneV_small hz (by omega)
    have h : ∀ z, z < vals4M.length → zoneV 4 vals4M z = 4 - 1 → z = 3 ∨ z = 5 := by decide
    exact h z hzl hz
  · have h : ∀ c ∈ chain4M.clauses, bk4M c < 4 ∧ ClIn (BlkN 4 (zoneV 4 vals4M) (bk4M c)) c := by decide
    exact h c hc
  · have h : ∀ c ∈ chain4M.clauses, 1 ≤ bk4M c → bk4M c + 1 < 4 → c.l1.v ≠ c.l2.v ∧ c.l1.v ≠ c.l3.v ∧
        c.l2.v ≠ c.l3.v := by decide
    exact h c hc h1 h2

/-- La construcción Lean da la salida de `preprocess_chain.jl`. -/
theorem preCnfM_chain4M : preCnfM chain4M 4 (zoneV 4 vals4M) sv4M zi4M 0 3 bk4M = chain4MP := by rfl

end GPathB

namespace MachineOn

open GPathB

/-- **`chain4m_cross` se decide con la máquina sobre su preprocesada**, por la construcción general. -/
theorem spineVerdictOn_pre_chain4M : SpineVerdictOn chain4MP ↔ Satisfiable chain4M :=
  preCnfM_chain4M ▸ spineVerdictOn_preM_iff chainInM_chain4M

end MachineOn

end AbsSatBingo.Model
