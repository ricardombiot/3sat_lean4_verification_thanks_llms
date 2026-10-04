-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainPreGen.lean
import AbsSatBingo.Model.ForbidOnChainPre

/-!
# El preproceso, en general: toda cadena se renumera a `ChainOrdN`

**`ChainIn φ n zone sv zi e0a e0b eLa eLb cl`**: `φ` es una cadena de `n` bloques (`n` cualquiera), `cl p` es la cláusula
del bloque `p` (y toda cláusula de `φ` es una de ellas), la del bloque de en medio `p` tiene exactamente sus dos
separadores y su variable de dentro `zi p` (distintas), y las de dentro de los bloques de los extremos son a lo sumo
`e0a, e0b` y `eLa, eLb`.

La construcción (`preCnf`), la de `test_3sat/preprocess_chain.jl`:

* **`fPre`**: las del bloque `0` a `0, 1`; el separador `i` a `2i`; la de dentro del bloque de en medio `p` a `2p + 1`;
  las del último bloque a `2n - 1, 2n`. **`gPre`**, la inversa.
* **`preCl`**: en cada cláusula de en medio, (separador izquierdo, la de dentro, separador derecho), con sus signos.
* **`zoneO`**, la zona de la cadena nueva. **El truco**: `zoneO (fPre z) = zone z` en toda variable de la cadena, así que
  la pertenencia de las cláusulas a sus bloques pasa de `φ` a `preCnf` reescribiendo.

Resultado: **`renaming_pre`**, **`chainOrd_pre`**, **`bounded_pre`**, y **`spineVerdictOn_pre_iff`**: la espina sobre la
preprocesada decide toda cadena de la clase, de cualquier longitud.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- **Una cadena de entrada.** -/
structure ChainIn (φ : Cnf) (n : Nat) (zone sv zi : Nat → Nat) (e0a e0b eLa eLb : Nat) (cl : Nat → Clause) :
    Prop where
  D    : ChainN φ n zone
  hsv  : ∀ k, 1 ≤ k → k < n → zone (sv k) = n + k
  hzi  : ∀ p, 1 ≤ p → p + 1 < n → zone (zi p) = p
  u0   : ∀ z, zone z = 0 → z = e0a ∨ z = e0b
  uL   : ∀ z, zone z = n - 1 → z = eLa ∨ z = eLb
  hcl  : ∀ p, p < n → cl p ∈ φ.clauses ∧ ClIn (BlkN n zone p) (cl p)
  cov  : ∀ c ∈ φ.clauses, ∃ p, p < n ∧ c = cl p
  mid  : ∀ p, 1 ≤ p → p + 1 < n → ClVar (cl p) (sv p) ∧ ClVar (cl p) (zi p) ∧ ClVar (cl p) (sv (p + 1))
  dist : ∀ p, 1 ≤ p → p + 1 < n → (cl p).l1.v ≠ (cl p).l2.v ∧ (cl p).l1.v ≠ (cl p).l3.v ∧ (cl p).l2.v ≠ (cl p).l3.v

/-! ## La construcción -/

section Def

variable (n : Nat) (zone sv zi : Nat → Nat) (e0a e0b eLa eLb : Nat) (cl : Nat → Clause)

/-- La numeración nueva. -/
def fPre (z : Nat) : Nat :=
  if zone z = 0 then (if z = e0a then 0 else 1)
  else if zone z = n - 1 then (if z = eLa then 2 * n - 1 else 2 * n)
  else if zone z < n then 2 * zone z + 1
  else if n + 1 ≤ zone z ∧ zone z < 2 * n then 2 * (zone z - n)
  else 2 * n + 1 + z

/-- Su inversa. -/
def gPre (w : Nat) : Nat :=
  if w = 0 then e0a else if w = 1 then e0b else if w = 2 * n - 1 then eLa else if w = 2 * n then eLb
  else if w % 2 = 0 then sv (w / 2) else zi ((w - 1) / 2)

/-- El literal de `c` con la variable `v`. -/
def litOf (c : Clause) (v : Nat) : Lit := if c.l1.v = v then c.l1 else if c.l2.v = v then c.l2 else c.l3

/-- Renombrar un literal. -/
def renL (f : Nat → Nat) (l : Lit) : Lit := ⟨f l.v, l.pos⟩

/-- La cláusula nueva del bloque `p`. -/
def preCl (p : Nat) : Clause :=
  if 1 ≤ p ∧ p + 1 < n then
    ⟨renL (fPre n zone e0a eLa) (litOf (cl p) (sv p)), renL (fPre n zone e0a eLa) (litOf (cl p) (zi p)),
      renL (fPre n zone e0a eLa) (litOf (cl p) (sv (p + 1)))⟩
  else ⟨renL (fPre n zone e0a eLa) (cl p).l1, renL (fPre n zone e0a eLa) (cl p).l2, renL (fPre n zone e0a eLa) (cl p).l3⟩

/-- **La fórmula preprocesada.** -/
def preCnf : Cnf := ⟨2 * n + 1, (List.range n).map (preCl n zone sv zi e0a eLa cl)⟩

/-- La zona de la cadena nueva. -/
def zoneO (w : Nat) : Nat :=
  if w ≤ 1 then 0 else if w ≤ 2 * n - 2 then (if w % 2 = 0 then n + w / 2 else (w - 1) / 2)
  else if w ≤ 2 * n then n - 1 else 2 * n

def svO (k : Nat) : Nat := 2 * k

end Def

/-! ## Lo que hace la numeración -/

section Num

variable {n : Nat} {zone sv zi : Nat → Nat} {e0a e0b eLa eLb : Nat} {cl : Nat → Clause}

/-- Una variable de la cadena: de dentro de un bloque o un separador. -/
def InChainZ (n : Nat) (zone : Nat → Nat) (z : Nat) : Prop := zone z < n ∨ (n + 1 ≤ zone z ∧ zone z < 2 * n)

theorem inChainZ_of_blk {p z : Nat} (hp : p < n) (h : BlkN n zone p z) : InChainZ n zone z := by
  unfold InChainZ; rcases h with h | ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem zoneO_cases (n w : Nat) :
    (w ≤ 1 ∧ zoneO n w = 0) ∨ (2 ≤ w ∧ w ≤ 2 * n - 2 ∧ w % 2 = 0 ∧ zoneO n w = n + w / 2) ∨
    (2 ≤ w ∧ w ≤ 2 * n - 2 ∧ w % 2 = 1 ∧ zoneO n w = (w - 1) / 2) ∨
    (2 * n - 2 < w ∧ 2 ≤ w ∧ w ≤ 2 * n ∧ zoneO n w = n - 1) ∨ (2 * n < w ∧ 2 ≤ w ∧ zoneO n w = 2 * n) := by
  unfold zoneO
  by_cases h1 : w ≤ 1
  · exact Or.inl ⟨h1, if_pos h1⟩
  rw [if_neg h1]
  by_cases h2 : w ≤ 2 * n - 2
  · rw [if_pos h2]
    by_cases h3 : w % 2 = 0
    · exact Or.inr (Or.inl ⟨by omega, h2, h3, if_pos h3⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2, by omega, if_neg h3⟩))
  rw [if_neg h2]
  by_cases h4 : w ≤ 2 * n
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, h4, if_pos h4⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega, if_neg h4⟩)))

/-- Los valores de la zona nueva. -/
theorem zoneO_lo {w : Nat} (h : w ≤ 1) : zoneO n w = 0 := by unfold zoneO; rw [if_pos h]
theorem zoneO_top (two : 2 ≤ n) {w : Nat} (h1 : 2 * n - 1 ≤ w) (h2 : w ≤ 2 * n) : zoneO n w = n - 1 := by
  unfold zoneO; rw [if_neg (by omega), if_neg (by omega), if_pos h2]
theorem zoneO_odd {p : Nat} (h1 : 1 ≤ p) (h2 : p + 1 < n) : zoneO n (2 * p + 1) = p := by
  unfold zoneO; rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]; omega
theorem zoneO_even {i : Nat} (h1 : 1 ≤ i) (h2 : i < n) : zoneO n (2 * i) = n + i := by
  unfold zoneO; rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]; omega

theorem fPre_zone (C : ChainIn φ n zone sv zi e0a e0b eLa eLb cl) {z : Nat} (hz : InChainZ n zone z) :
    zoneO n (fPre n zone e0a eLa z) = zone z := by
  have two := C.D.two
  unfold InChainZ at hz
  unfold fPre
  by_cases h0 : zone z = 0
  · rw [if_pos h0, h0]; split <;> exact zoneO_lo (by omega)
  rw [if_neg h0]
  by_cases hL : zone z = n - 1
  · rw [if_pos hL, hL]; split <;> exact zoneO_top two (by omega) (by omega)
  rw [if_neg hL]
  by_cases hm : zone z < n
  · rw [if_pos hm]; exact zoneO_odd (by omega) (by omega)
  rw [if_neg hm, if_pos (by omega), zoneO_even (by omega) (by omega)]; omega

theorem gfPre (C : ChainIn φ n zone sv zi e0a e0b eLa eLb cl) {z : Nat} (hz : InChainZ n zone z) :
    gPre n sv zi e0a e0b eLa eLb (fPre n zone e0a eLa z) = z := by
  have two := C.D.two
  unfold InChainZ at hz
  unfold fPre
  by_cases h0 : zone z = 0
  · rw [if_pos h0]
    by_cases ea : z = e0a
    · rw [if_pos ea]; unfold gPre; rw [if_pos rfl]; exact ea.symm
    · rw [if_neg ea]; unfold gPre; rw [if_neg (by omega), if_pos rfl]
      rcases C.u0 z h0 with e | e
      · exact absurd e ea
      · exact e.symm
  rw [if_neg h0]
  by_cases hL : zone z = n - 1
  · rw [if_pos hL]
    by_cases ea : z = eLa
    · rw [if_pos ea]; unfold gPre; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]; exact ea.symm
    · rw [if_neg ea]; unfold gPre
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
      rcases C.uL z hL with e | e
      · exact absurd e ea
      · exact e.symm
  rw [if_neg hL]
  by_cases hm : zone z < n
  · rw [if_pos hm]; unfold gPre
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show (2 * zone z + 1 - 1) / 2 = zone z by omega]
    exact (C.D.cardM (zone z) (by omega) (by omega) z (zi (zone z)) rfl (C.hzi _ (by omega) (by omega))).symm
  rw [if_neg hm, if_pos (by omega)]; unfold gPre
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 2 * (zone z - n) / 2 = zone z - n by omega]
  exact (C.D.sep1 (zone z - n) (by omega) (by omega) z _ (by omega) (C.hsv _ (by omega) (by omega))).symm

theorem fPre_lt (C : ChainIn φ n zone sv zi e0a e0b eLa eLb cl) {z : Nat} (hz : InChainZ n zone z) :
    fPre n zone e0a eLa z < 2 * n + 1 := by
  have two := C.D.two
  unfold InChainZ at hz
  unfold fPre
  split
  · split <;> omega
  split
  · split <;> omega
  split
  · omega
  rw [if_pos (by omega)]; omega

/-- Lo que hay en la zona nueva `p` de en medio: `2p + 1`. -/
theorem zoneO_mid {w p : Nat} (h1 : 1 ≤ p) (h2 : p + 1 < n) (h : zoneO n w = p) : w = 2 * p + 1 := by
  rcases zoneO_cases n w with ⟨a, e⟩ | ⟨a, b, c, e⟩ | ⟨a, b, c, e⟩ | ⟨a, b, c, e⟩ | ⟨a, b, e⟩ <;> omega

theorem litOf_v {c : Clause} {v : Nat} (h : ClVar c v) : (litOf c v).v = v := by
  unfold litOf
  split
  · assumption
  split
  · assumption
  rcases h with e | e | e
  · omega
  · omega
  · exact e.symm

theorem litOf_mem (c : Clause) (v : Nat) : litOf c v ∈ clLits c := by
  unfold litOf clLits
  split
  · simp
  split <;> simp

theorem litOf_self {c : Clause} (d12 : c.l1.v ≠ c.l2.v) (d13 : c.l1.v ≠ c.l3.v) (d23 : c.l2.v ≠ c.l3.v)
    {l : Lit} (hl : l ∈ clLits c) : litOf c l.v = l := by
  unfold clLits at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  unfold litOf
  rcases hl with rfl | rfl | rfl
  · rw [if_pos rfl]
  · rw [if_neg (fun e => d12 e), if_pos rfl]
  · rw [if_neg (fun e => d13 e), if_neg (fun e => d23 e)]

theorem clLits_var {c : Clause} {l : Lit} (hl : l ∈ clLits c) : ClVar c l.v := by
  unfold clLits at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- Las variables de la cláusula nueva del bloque `p`: imágenes de las de `cl p`. -/
theorem preCl_vars (C : ChainIn φ n zone sv zi e0a e0b eLa eLb cl) {p : Nat} {w : Nat}
    (hw : ClVar (preCl n zone sv zi e0a eLa cl p) w) : ∃ z, ClVar (cl p) z ∧ w = fPre n zone e0a eLa z := by
  unfold preCl at hw
  split at hw
  · rename_i hm
    obtain ⟨a, b, c⟩ := C.mid p hm.1 hm.2
    rcases hw with e | e | e
    · exact ⟨_, a, by rw [e]; simp only [renL, litOf_v a]⟩
    · exact ⟨_, b, by rw [e]; simp only [renL, litOf_v b]⟩
    · exact ⟨_, c, by rw [e]; simp only [renL, litOf_v c]⟩
  · rcases hw with e | e | e
    · exact ⟨_, Or.inl rfl, by rw [e]; rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), by rw [e]; rfl⟩
    · exact ⟨_, Or.inr (Or.inr rfl), by rw [e]; rfl⟩

end Num

/-! ## Los tres resultados -/

section Main

variable {n : Nat} {zone sv zi : Nat → Nat} {e0a e0b eLa eLb : Nat} {cl : Nat → Clause}

theorem mem_preCnf {c' : Clause} (h : c' ∈ (preCnf n zone sv zi e0a eLa cl).clauses) :
    ∃ p, p < n ∧ c' = preCl n zone sv zi e0a eLa cl p := by
  unfold preCnf at h
  obtain ⟨p, hp, e⟩ := List.mem_map.mp h
  exact ⟨p, List.mem_range.mp hp, e.symm⟩

/-- **El renombrado.** -/
theorem renaming_pre (C : ChainIn φ n zone sv zi e0a e0b eLa eLb cl) :
    Renaming φ (preCnf n zone sv zi e0a eLa cl) (fPre n zone e0a eLa) (gPre n sv zi e0a e0b eLa eLb) := by
  have inz : ∀ {p}, p < n → ∀ {l}, l ∈ clLits (cl p) → InChainZ n zone l.v := fun {_} hp {_} hl =>
    inChainZ_of_blk hp (clIn_var (C.hcl _ hp).2 (clLits_var hl))
  refine ⟨fun c hc l hl => ?_, fun c hc => ?_, fun c' hc' => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := C.cov c hc
    exact gfPre C (inz hp hl)
  · obtain ⟨p, hp, rfl⟩ := C.cov c hc
    refine ⟨preCl n zone sv zi e0a eLa cl p, List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩, fun l' hl' => ?_⟩
    unfold preCl at hl'
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
  · obtain ⟨p, hp, rfl⟩ := mem_preCnf hc'
    refine ⟨cl p, (C.hcl p hp).1, fun l hl => ?_⟩
    unfold preCl
    split
    · rename_i hm
      obtain ⟨d12, d13, d23⟩ := C.dist p hm.1 hm.2
      have hs := litOf_self d12 d13 d23 hl
      -- la variable de `l` es una de las tres
      have hv : l.v = sv p ∨ l.v = zi p ∨ l.v = sv (p + 1) := by
        have hB := clIn_var (C.hcl p hp).2 (clLits_var hl)
        rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩
        · exact Or.inr (Or.inl (C.D.cardM p hm.1 hm.2 _ _ h (C.hzi p hm.1 hm.2)))
        · exact Or.inl (C.D.sep1 p hm.1 (by omega) _ _ h (C.hsv p hm.1 (by omega)))
        · exact Or.inr (Or.inr (C.D.sep1 (p + 1) (by omega) hm.2 _ _ (by omega) (C.hsv _ (by omega) hm.2)))
      rcases hv with e | e | e
      · exact ⟨renL (fPre n zone e0a eLa) (litOf (cl p) (sv p)), by simp [clLits], by rw [← e, hs]; rfl, by rw [← e, hs]; rfl⟩
      · exact ⟨renL (fPre n zone e0a eLa) (litOf (cl p) (zi p)), by simp [clLits], by rw [← e, hs]; rfl, by rw [← e, hs]; rfl⟩
      · exact ⟨renL (fPre n zone e0a eLa) (litOf (cl p) (sv (p + 1))), by simp [clLits], by rw [← e, hs]; rfl, by rw [← e, hs]; rfl⟩
    · unfold clLits at hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact ⟨renL (fPre n zone e0a eLa) (cl p).l1, by simp [clLits], rfl, rfl⟩
      · exact ⟨renL (fPre n zone e0a eLa) (cl p).l2, by simp [clLits], rfl, rfl⟩
      · exact ⟨renL (fPre n zone e0a eLa) (cl p).l3, by simp [clLits], rfl, rfl⟩

/-- La preprocesada tiene sus variables en rango. -/
theorem bounded_pre (C : ChainIn φ n zone sv zi e0a e0b eLa eLb cl) :
    Bounded (preCnf n zone sv zi e0a eLa cl) := by
  intro c' hc'
  obtain ⟨p, hp, rfl⟩ := mem_preCnf hc'
  have bd : ∀ {w}, ClVar (preCl n zone sv zi e0a eLa cl p) w → w < 2 * n + 1 := fun hw => by
    obtain ⟨z, hz, rfl⟩ := preCl_vars C hw
    exact fPre_lt C (inChainZ_of_blk hp (clIn_var (C.hcl p hp).2 hz))
  exact ⟨bd (Or.inl rfl), bd (Or.inr (Or.inl rfl)), bd (Or.inr (Or.inr rfl))⟩

/-- **La preprocesada está en `ChainOrdN`.** -/
theorem chainOrd_pre (C : ChainIn φ n zone sv zi e0a e0b eLa eLb cl) :
    ChainOrdN (preCnf n zone sv zi e0a eLa cl) n (zoneO n) svO := by
  have two := C.D.two
  -- las cláusulas nuevas, en su bloque
  have blkO : ∀ p, p < n → ClIn (BlkN n (zoneO n) p) (preCl n zone sv zi e0a eLa cl p) := by
    intro p hp
    have t : ∀ {w}, ClVar (preCl n zone sv zi e0a eLa cl p) w → BlkN n (zoneO n) p w := fun hw => by
      obtain ⟨z, hz, rfl⟩ := preCl_vars C hw
      have hB := clIn_var (C.hcl p hp).2 hz
      unfold BlkN at hB ⊢
      rw [fPre_zone C (inChainZ_of_blk hp hB)]; exact hB
    exact ⟨t (Or.inl rfl), t (Or.inr (Or.inl rfl)), t (Or.inr (Or.inr rfl))⟩
  have getp : ∀ j c, (preCnf n zone sv zi e0a eLa cl).clauses[j]? = some c → j < n ∧
      c = preCl n zone sv zi e0a eLa cl j := by
    intro j c h
    unfold preCnf at h
    simp only [List.getElem?_map] at h
    by_cases hj : j < n
    · have e : (List.range n)[j]? = some j := by
        rw [List.getElem?_eq_getElem (by simp [hj])]; simp
      rw [e] at h; simp only [Option.map_some, Option.some.injEq] at h; exact ⟨hj, h.symm⟩
    · rw [List.getElem?_eq_none (by simp; omega)] at h; simp at h
  refine ⟨⟨two, fun w a b => ?_, fun i h1 h2 w w' hw hw' => ?_, fun y1 y2 y3 a b c d12 d13 d23 => ?_,
      fun y1 y2 y3 a b c d12 d13 d23 => ?_, fun j h1 h2 w w' hw hw' => ?_, fun c hc => ?_⟩,
    fun k h1 h2 => ?_, by simp [preCnf], fun j c hj => ?_, fun w p h1 h2 hz => ?_,
    fun j c hj w p h1 h2 hz hcv => ?_⟩
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
    obtain ⟨p, hp, rfl⟩ := mem_preCnf hc
    exact Or.inr ⟨p, hp, blkO p hp⟩
  · -- los separadores nuevos
    show zoneO n (2 * k) = n + k
    unfold zoneO; rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]; omega
  · obtain ⟨hjn, rfl⟩ := getp j c hj
    exact blkO j hjn
  · -- `NumLocal`
    have e := zoneO_mid h1 h2 hz
    subst e
    refine ⟨by omega, by show 2 * p + 1 + 1 < 2 * n + 1; omega, Or.inl ?_, Or.inr ?_⟩ <;> simp only [svO] <;> omega
  · -- `LitLocal`
    obtain ⟨hjn, rfl⟩ := getp j c hj
    have e := zoneO_mid h1 h2 hz
    subst e
    -- la cláusula es la del bloque `p`
    have hjp : j = p := by
      have hB := clIn_var (blkO j hjn) hcv
      rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    subst hjp
    obtain ⟨a, b, c⟩ := C.mid j h1 h2
    have fs : ∀ {k}, 1 ≤ k → k < n → fPre n zone e0a eLa (sv k) = 2 * k := fun h1 h2 => by
      unfold fPre; rw [C.hsv _ h1 h2, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      omega
    have fz : fPre n zone e0a eLa (zi j) = 2 * j + 1 := by
      unfold fPre; rw [C.hzi j h1 h2, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    unfold preCl; rw [if_pos ⟨h1, h2⟩]
    simp only [renL, litOf_v a, litOf_v b, litOf_v c, svO]
    exact ⟨fz, Or.inl (fs h1 (by omega)), Or.inr (fs (by omega) h2)⟩

end Main

namespace MachineOn

open GPathB Driver Machine

variable {n : Nat} {zone sv zi : Nat → Nat} {e0a e0b eLa eLb : Nat} {cl : Nat → Clause}

/-- **La espina sobre la preprocesada decide toda cadena de la clase, de cualquier longitud.** -/
theorem spineVerdictOn_pre_iff (C : ChainIn φ n zone sv zi e0a e0b eLa eLb cl) :
    SpineVerdictOn (preCnf n zone sv zi e0a eLa cl) ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_pre (renaming_pre C) (bounded_pre C) (chainOrd_pre C)

/-- **Y la máquina sobre la preprocesada es exacta.** -/
theorem machineExact_pre (C : ChainIn φ n zone sv zi e0a e0b eLa eLb cl) :
    MachineExact (preCnf n zone sv zi e0a eLa cl) :=
  machineExact_of_chainOrd (bounded_pre C) (chainOrd_pre C)

end MachineOn

end AbsSatBingo.Model

/-! ## `chain6_cross` está en la clase de entrada -/

namespace AbsSatBingo.Model

open AbsSatBin.Cnf

namespace GPathB

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 20000

/-- Las zonas de `chain6_cross`: `{x0, x2}`, `{x4}`, `{x5}`, `{x1}`, `{x3}`, `{x11, x12}`; separadores `x6 … x10`. -/
def vals6X : List Nat := [0, 3, 0, 4, 1, 2, 7, 8, 9, 10, 11, 5, 5]
def sv6X (k : Nat) : Nat := [0, 6, 7, 8, 9, 10].getD k 0
def zi6X (p : Nat) : Nat := [0, 4, 5, 1, 3, 0].getD p 0
def cl6X (p : Nat) : Clause := chain6X.clauses.getD p ⟨⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩⟩

theorem chainIn_chain6X : ChainIn chain6X 6 (zoneV 6 vals6X) sv6X zi6X 0 2 11 12 cl6X := by
  refine ⟨chainN_of_vals (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    fun k h1 h2 => ?_, fun p h1 h2 => ?_, fun z hz => ?_, fun z hz => ?_, fun p hp => ?_, fun c hc => ?_,
    fun p h1 h2 => ?_, fun p h1 h2 => ?_⟩
  · have h : ∀ k, k < 6 → 1 ≤ k → zoneV 6 vals6X (sv6X k) = 6 + k := by decide
    exact h k h2 h1
  · have h : ∀ p, p < 6 → 1 ≤ p → p + 1 < 6 → zoneV 6 vals6X (zi6X p) = p := by decide
    exact h p (by omega) h1 h2
  · have hzl : z < vals6X.length := zoneV_small hz (by omega)
    have h : ∀ z, z < vals6X.length → zoneV 6 vals6X z = 0 → z = 0 ∨ z = 2 := by decide
    exact h z hzl hz
  · have hzl : z < vals6X.length := zoneV_small hz (by omega)
    have h : ∀ z, z < vals6X.length → zoneV 6 vals6X z = 6 - 1 → z = 11 ∨ z = 12 := by decide
    exact h z hzl hz
  · have h : ∀ p, p < 6 → cl6X p ∈ chain6X.clauses ∧ ClIn (BlkN 6 (zoneV 6 vals6X) p) (cl6X p) := by decide
    exact h p hp
  · have h : ∀ c ∈ chain6X.clauses, ∃ p, p < 6 ∧ c = cl6X p := by decide
    exact h c hc
  · have h : ∀ p, p < 6 → 1 ≤ p → p + 1 < 6 →
        ClVar (cl6X p) (sv6X p) ∧ ClVar (cl6X p) (zi6X p) ∧ ClVar (cl6X p) (sv6X (p + 1)) := by decide
    exact h p (by omega) h1 h2
  · have h : ∀ p, p < 6 → 1 ≤ p → p + 1 < 6 → (cl6X p).l1.v ≠ (cl6X p).l2.v ∧ (cl6X p).l1.v ≠ (cl6X p).l3.v ∧
        (cl6X p).l2.v ≠ (cl6X p).l3.v := by decide
    exact h p (by omega) h1 h2

end GPathB

namespace MachineOn

open GPathB

/-- **`chain6_cross`, por la construcción general.** -/
theorem spineVerdictOn_pre_chain6X_gen :
    SpineVerdictOn (preCnf 6 (zoneV 6 vals6X) sv6X zi6X 0 11 cl6X) ↔ Satisfiable chain6X :=
  spineVerdictOn_pre_iff chainIn_chain6X

end MachineOn

end AbsSatBingo.Model
