-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnChainSide.lean
import AbsSatBingo.Model.ForbidOnChainN

/-!
# Un lado de la bisección

Al fijar el separador `v` (zona `n + m`) de una `ChainN`, el triángulo se cierra lado a lado. Aquí, el **lado
derecho**: los bloques `m … b-1`, con el extremo lejano libre (`b = n`, el final de la cadena) o **fijo** (`b < n`: todas
las ramas de `P0` leen igual el separador `b`, ya fijado por el lector). Sus separadores interiores son
`t_k` (zona `n + m + k`, `1 ≤ k < b - m`).

El caso lo decide el **primer separador leído** `t_r` del lado (`r = b - m` si no se lee ninguno):

* `r = 1` (`side_right1`): una sola fuente de `P` para el bloque `m`, que coincide con `a0` en `t_1`; lo demás, `a0`.
* `r = 2` (`side_right2`): las caras de una ventana que lee `t_1` (la del bloque `m`); dos fuentes, unidas en `t_1` por
  la ventana.
* `r = 3`, o `r = 4` con el extremo fijo (`side_right3`): las caras de una ventana que lee `t_1` y `t_2` (la del bloque
  `m + 1`); tres fuentes, la última para los bloques `m + 2` y `m + 3` si `r = 4`.

En los tres, las subtriangulaciones del testigo leen `t_1`: el lado baja a `r = 1`. Las caras llegan como **`SideCap`**:
lo que se usa de ellas (elegir una de `P0` en tres variables, una de `P` en una, y que todas leen igual lo que lee la
ventana). `sideCap_of_facesP` (las caras de `faces_Pw`) y `sideCap_of_facesX` (las de `faces_Pwx`, con un nodo que se
conserva) la dan.

La salida, **`SideOut`**: fuentes de `P0`, la del bloque `m` de `P`, unidas en los separadores del lado, y que
coinciden con `a0` en lo que leen las ventanas de cada bloque cerrado, salvo `v` (que se une al otro lado por `P`).

Con el extremo libre basta `r ≤ 3`: el lado puede tener hasta tres bloques. Con el extremo fijo, hasta cuatro.

**El lado izquierdo** es el derecho de la cadena al revés (`zoneRevN`, `chainN_rev`, `blkN_rev`, `fixedEnd_rev`).
**El pegado** (`glue_sides_tri`): las fuentes de los dos lados, `a0` fuera, unidas en `v` porque las dos del bloque de
`v` son de `P`, cierran el triángulo por `glueN_tri`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop} {σ : Int}

/-- **Lo que se usa de las caras de un testigo** del paso `lam`, para el triángulo de ventanas `i`, `j`, `l` y la rama
`a0`. -/
structure SideCap (φ : Cnf) (P0 P Q : Assign → Prop) (i j l lam : Int) (a0 : Assign) : Prop where
  q0  : ∀ c, Q c → P0 c
  win : ∀ c c', Q c → Q c' → ∀ z, ReadsAt φ lam z → c z = c' z
  p0  : ∀ {M : Nat → Prop}, No3 M → ∃ d, Q d ∧ Agr φ i j l M d a0
  pP  : ∀ {M : Nat → Prop}, Le1 M → ∃ d, P d ∧ Q d ∧ Agr φ i j l M d a0

/-- Las caras de `faces_Pw`. -/
theorem sideCap_of_facesP (hl : LocPair φ P0 P σ) {a0 c1 c2 c3 : Assign} {i j l lam : Int}
    (F : Faces φ (fun c => P c ∧ pidOfAssign φ c lam = pidOfAssign φ c1 lam) a0 c1 c2 c3 i j l) :
    SideCap φ P0 P (fun c => P c ∧ pidOfAssign φ c lam = pidOfAssign φ c1 lam) i j l lam a0 where
  q0 := fun c h => hl.sub c h.1
  win := fun _ _ h h' _ hz => agree_at h.2 h'.2 hz
  p0 := fun hM => F.pick hM
  pP := fun hM => by
    obtain ⟨d, hd, ag⟩ := F.pick (no3_of_le1 hM)
    exact ⟨d, hd.1, hd, ag⟩

/-- Las caras de `faces_Pwx`: solo las dos primeras son de `P`. -/
theorem sideCap_of_facesX {a0 c1 c2 c3 : Assign} {i j l lam : Int}
    (F : Faces φ (fun c => P0 c ∧ pidOfAssign φ c lam = pidOfAssign φ c1 lam) a0 c1 c2 c3 i j l) (q1 : P c1)
    (q2 : P c2) : SideCap φ P0 P (fun c => P0 c ∧ pidOfAssign φ c lam = pidOfAssign φ c1 lam) i j l lam a0 where
  q0 := fun _ h => h.1
  win := fun _ _ h h' _ hz => agree_at h.2 h'.2 hz
  p0 := fun hM => F.pick hM
  pP := fun hM => by
    obtain ⟨d, hP, hQ, ag, _⟩ := pick12 F q1 q2 hM
    exact ⟨d, hP, hQ, ag⟩

/-- **La salida de un lado**: los bloques `m … b-1`. -/
structure SideOut (φ : Cnf) (n : Nat) (zone : Nat → Nat) (P0 P : Assign → Prop) (i j l : Int) (a0 : Assign)
    (m b : Nat) (src : Nat → Assign) : Prop where
  p0   : ∀ p, m ≤ p → p < b → P0 (src p)
  pm   : P (src m)
  join : ∀ p, m + 1 ≤ p → p < b → ∀ z, zone z = n + p → src (p - 1) z = src p z
  agr  : ∀ p, m ≤ p → p < b → ∀ z, BlkN n zone p z → zone z ≠ n + m → InW φ i j l z → src p z = a0 z

section Right

variable {n : Nat} {zone : Nat → Nat} {m b : Nat} {i j l : Int} {a0 : Assign}

/-- El extremo lejano fijo: todas las ramas de `P0` leen igual el separador `b`. -/
def FixedEnd (n : Nat) (zone : Nat → Nat) (P0 : Assign → Prop) (b : Nat) : Prop :=
  b < n → ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + b → c z = c' z

/-- El último bloque del lado, sin el separador lejano: a lo sumo dos variables (el final de la cadena) o una (un
bloque de en medio, con el extremo fijo). -/
theorem no3_last (D : ChainN φ n zone) {p : Nat} (hp : 1 ≤ p) (hb : p < n) : No3 (fun z => zone z = p) := by
  by_cases h : p + 1 < n
  · exact no3_of_le1 (D.cardM p hp h)
  · have e : p = n - 1 := by omega
    rw [e]; exact D.cardL

/-- Un bloque de en medio y el separador de su derecha. -/
theorem no3_mid_sep (D : ChainN φ n zone) {p : Nat} (hp : 1 ≤ p) (hb : p + 1 < n) :
    No3 (fun z => zone z = p ∨ zone z = n + (p + 1)) :=
  no3_or (D.cardM p hp hb) (D.sep1 (p + 1) (by omega) hb)

/-- **`r = 1`**: el lado ya lee `t_1` (o no tiene separadores); una fuente `d` de `P` para el bloque `m`. -/
theorem side_right1 (hmb : m + 1 ≤ b) (hfix : FixedEnd n zone P0 b) (h0 : P0 a0) {d : Assign}
    (qd : P d) (qd0 : P0 d) (ag : Agr φ i j l (fun z => zone z = m ∨ (m + 1 < b ∧ zone z = n + (m + 1))) d a0)
    (hrd : m + 1 < b → ∀ z, zone z = n + (m + 1) → InW φ i j l z) :
    SideOut φ n zone P0 P i j l a0 m b (fun p => if p = m then d else a0) := by
  refine ⟨fun p _ _ => ?_, by simp only; exact qd, fun p a c z hz => ?_, fun p a c z hB hv hw => ?_⟩
  · by_cases e : p = m
    · rw [if_pos e]; exact qd0
    · rw [if_neg e]; exact h0
  · by_cases e : p = m + 1
    · subst e
      rw [if_pos (by omega), if_neg (by omega)]
      exact ag z (Or.inr ⟨by omega, hz⟩) (hrd (by omega) z hz)
    · rw [if_neg (by omega), if_neg (by omega)]
  · by_cases e : p = m
    · subst e
      rw [if_pos rfl]
      rcases hB with h | ⟨_, h⟩ | ⟨h1, h⟩
      · exact ag z (Or.inl h) hw
      · exact absurd h hv
      · by_cases hm1 : p + 1 < b
        · exact ag z (Or.inr ⟨hm1, by omega⟩) hw
        · exact hfix (by omega) d a0 qd0 h0 z (by omega)
    · rw [if_neg e]

/-- **`r = 2`**: las caras de una ventana que lee `t_1`. -/
theorem side_right2 (D : ChainN φ n zone) (hm : 1 ≤ m) (hmb : m + 2 ≤ b) (hbn : b ≤ n)
    (hfix : FixedEnd n zone P0 b) (h0 : P0 a0) {Q : Assign → Prop} {lam : Int} (C : SideCap φ P0 P Q i j l lam a0)
    (hl1 : ∀ z, zone z = n + (m + 1) → ReadsAt φ lam z)
    (hun : ∀ z, zone z = n + (m + 1) → ¬ InW φ i j l z)
    (hrd : m + 2 < b → ∀ z, zone z = n + (m + 2) → InW φ i j l z) :
    ∃ src, SideOut φ n zone P0 P i j l a0 m b src := by
  obtain ⟨d0, q0P, q0, ag0⟩ := C.pP (D.cardM m hm (by omega))
  have c1 : No3 (fun z => zone z = m + 1 ∨ (m + 2 < b ∧ zone z = n + (m + 2))) := by
    by_cases h : m + 2 < b
    · intro y1 y2 y3 b1 b2 b3
      exact no3_mid_sep D (p := m + 1) (by omega) (by omega) y1 y2 y3
        (b1.imp id (fun h => h.2)) (b2.imp id (fun h => h.2)) (b3.imp id (fun h => h.2))
    · intro y1 y2 y3 b1 b2 b3
      exact no3_last D (p := m + 1) (by omega) (by omega) y1 y2 y3
        (b1.resolve_right (fun h' => h h'.1)) (b2.resolve_right (fun h' => h h'.1))
        (b3.resolve_right (fun h' => h h'.1))
  obtain ⟨d1, q1, ag1⟩ := C.p0 c1
  refine ⟨fun p => if p = m then d0 else if p = m + 1 then d1 else a0,
    ⟨fun p _ _ => ?_, by simp only; exact q0P, fun p a c z hz => ?_, fun p a c z hB hv hw => ?_⟩⟩
  · by_cases e : p = m
    · rw [if_pos e]; exact C.q0 _ q0
    by_cases e' : p = m + 1
    · rw [if_neg e, if_pos e']; exact C.q0 _ q1
    · rw [if_neg e, if_neg e']; exact h0
  · by_cases e : p = m + 1
    · subst e
      rw [if_pos (by omega), if_neg (by omega), if_pos rfl]
      exact C.win _ _ q0 q1 z (hl1 z hz)
    by_cases e' : p = m + 2
    · subst e'
      rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]
      exact ag1 z (Or.inr ⟨by omega, hz⟩) (hrd (by omega) z hz)
    · rw [if_neg (by omega), if_neg (by omega), if_neg e, if_neg (by omega)]
  · by_cases e : p = m
    · subst e
      rw [if_pos rfl]
      rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩
      · exact ag0 z h hw
      · exact absurd h hv
      · exact absurd hw (hun z (by omega))
    by_cases e' : p = m + 1
    · subst e'
      rw [if_neg e, if_pos rfl]
      rcases hB with h | ⟨_, h⟩ | ⟨h1, h⟩
      · exact ag1 z (Or.inl h) hw
      · exact absurd hw (hun z (by omega))
      · by_cases hm2 : m + 2 < b
        · exact ag1 z (Or.inr ⟨hm2, by omega⟩) hw
        · exact hfix (by omega) d1 a0 (C.q0 _ q1) h0 z (by omega)
    · rw [if_neg e, if_neg e']

/-- **`r = 3`, o `r = 4` con el extremo fijo**: las caras de una ventana que lee `t_1` y `t_2`. -/
theorem side_right3 (D : ChainN φ n zone) (hm : 1 ≤ m) {r : Nat} (hr : r = 3 ∨ (r = 4 ∧ b = m + 4 ∧ b < n))
    (hmb : m + r ≤ b) (hbn : b ≤ n) (hfix : FixedEnd n zone P0 b) (h0 : P0 a0) {Q : Assign → Prop} {lam : Int}
    (C : SideCap φ P0 P Q i j l lam a0) (hl1 : ∀ z, zone z = n + (m + 1) → ReadsAt φ lam z)
    (hl2 : ∀ z, zone z = n + (m + 2) → ReadsAt φ lam z)
    (hun : ∀ k z, 1 ≤ k → k < r → zone z = n + (m + k) → ¬ InW φ i j l z)
    (hrd : m + r < b → ∀ z, zone z = n + (m + r) → InW φ i j l z) :
    ∃ src, SideOut φ n zone P0 P i j l a0 m b src := by
  obtain ⟨d0, q0P, q0, ag0⟩ := C.pP (D.cardM m hm (by omega))
  obtain ⟨d1, q1, ag1⟩ := C.p0 (no3_of_le1 (D.cardM (m + 1) (by omega) (by omega)))
  -- la tercera fuente: el bloque `m + 2` y el separador `t_3` (`r = 3`), o los bloques `m + 2` y `m + 3` (`r = 4`)
  let M2 : Nat → Prop := fun z => zone z = m + 2 ∨ (r = 3 ∧ m + 3 < b ∧ zone z = n + (m + 3)) ∨
    (r = 4 ∧ zone z = m + 3)
  have c2 : No3 M2 := by
    intro y1 y2 y3 b1 b2 b3
    rcases hr with rfl | ⟨rfl, hb4, hbn'⟩
    · have nr : ∀ {z}, ¬ (3 = 4 ∧ zone z = m + 3) := fun h => absurd h.1 (by omega)
      by_cases h : m + 3 < b
      · have im : ∀ {z}, M2 z → zone z = m + 2 ∨ zone z = n + (m + 2 + 1) := fun {z} hz => by
          rcases hz with e | ⟨_, _, e⟩ | e
          · exact Or.inl e
          · exact Or.inr e
          · exact absurd e nr
        exact no3_mid_sep D (p := m + 2) (by omega) (by omega) y1 y2 y3 (im b1) (im b2) (im b3)
      · have im : ∀ {z}, M2 z → zone z = m + 2 := fun {z} hz => by
          rcases hz with e | ⟨_, h', _⟩ | e
          · exact e
          · exact absurd h' h
          · exact absurd e nr
        exact no3_last D (p := m + 2) (by omega) (by omega) y1 y2 y3 (im b1) (im b2) (im b3)
    · have im : ∀ {z}, M2 z → zone z = m + 2 ∨ zone z = m + 3 := fun {z} hz => by
        rcases hz with e | ⟨h', _, _⟩ | ⟨_, e⟩
        · exact Or.inl e
        · omega
        · exact Or.inr e
      exact no3_or (D.cardM (m + 2) (by omega) (by omega)) (D.cardM (m + 3) (by omega) (by omega)) y1 y2 y3
        (im b1) (im b2) (im b3)
  obtain ⟨d2, q2, ag2⟩ := C.p0 c2
  have q0' := C.q0 _ q0; have q1' := C.q0 _ q1; have q2' := C.q0 _ q2
  refine ⟨fun p => if p = m then d0 else if p = m + 1 then d1 else if p = m + 2 ∨ (r = 4 ∧ p = m + 3) then d2
    else a0, ⟨fun p _ _ => ?_, by simp only; exact q0P, fun p a c z hz => ?_,
    fun p a c z hB hv hw => ?_⟩⟩
  · by_cases e : p = m
    · rw [if_pos e]; exact q0'
    by_cases e' : p = m + 1
    · rw [if_neg e, if_pos e']; exact q1'
    by_cases e'' : p = m + 2 ∨ (r = 4 ∧ p = m + 3)
    · rw [if_neg e, if_neg e', if_pos e'']; exact q2'
    · rw [if_neg e, if_neg e', if_neg e'']; exact h0
  · -- las uniones
    by_cases e : p = m + 1
    · subst e
      rw [if_pos (by omega), if_neg (by omega), if_pos rfl]
      exact C.win _ _ q0 q1 z (hl1 z hz)
    by_cases e' : p = m + 2
    · subst e'
      rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (Or.inl rfl)]
      exact C.win _ _ q1 q2 z (hl2 z hz)
    by_cases e3 : p = m + 3
    · subst e3
      rw [if_neg (by omega), if_neg (by omega), if_pos (Or.inl (by omega)), if_neg (by omega), if_neg (by omega)]
      rcases hr with rfl | ⟨rfl, _, _⟩
      · rw [if_neg (by omega)]
        exact ag2 z (Or.inr (Or.inl ⟨rfl, by omega, hz⟩)) (hrd (by omega) z hz)
      · rw [if_pos (Or.inr ⟨rfl, rfl⟩)]
    · have e4 : ¬ (p - 1 = m + 2 ∨ (r = 4 ∧ p - 1 = m + 3)) := by
        rintro (h | ⟨h1, h⟩)
        · omega
        · rcases hr with h' | ⟨_, hb, _⟩ <;> omega
      have e5 : ¬ (p = m + 2 ∨ (r = 4 ∧ p = m + 3)) := by omega
      rw [if_neg (show ¬ p - 1 = m by omega), if_neg (show ¬ p - 1 = m + 1 by omega), if_neg e4,
        if_neg (show ¬ p = m by omega), if_neg e, if_neg e5]
  · -- coincidir con `a0`
    by_cases e : p = m
    · subst e
      rw [if_pos rfl]
      rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩
      · exact ag0 z h hw
      · exact absurd h hv
      · exact absurd hw (hun 1 z (by omega) (by omega) (by omega))
    by_cases e' : p = m + 1
    · subst e'
      rw [if_neg e, if_pos rfl]
      rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩
      · exact ag1 z h hw
      · exact absurd hw (hun 1 z (by omega) (by omega) (by omega))
      · exact absurd hw (hun 2 z (by omega) (by omega) (by omega))
    by_cases e'' : p = m + 2 ∨ (r = 4 ∧ p = m + 3)
    · rw [if_neg e, if_neg e', if_pos e'']
      rcases e'' with rfl | ⟨rfl, rfl⟩
      · rcases hB with h | ⟨_, h⟩ | ⟨h1, h⟩
        · exact ag2 z (Or.inl h) hw
        · exact absurd hw (hun 2 z (by omega) (by omega) (by omega))
        · rcases hr with rfl | ⟨rfl, _, _⟩
          · by_cases hm3 : m + 3 < b
            · exact ag2 z (Or.inr (Or.inl ⟨rfl, hm3, by omega⟩)) hw
            · exact hfix (by omega) d2 a0 q2' h0 z (by omega)
          · exact absurd hw (hun 3 z (by omega) (by omega) (by omega))
      · rcases hr with h' | ⟨_, hb4, hbn'⟩
        · omega
        rcases hB with h | ⟨_, h⟩ | ⟨h1, h⟩
        · exact ag2 z (Or.inr (Or.inr ⟨rfl, h⟩)) hw
        · exact absurd hw (hun 3 z (by omega) (by omega) (by omega))
        · exact hfix hbn' d2 a0 q2' h0 z (by omega)
    · rw [if_neg e, if_neg e', if_neg e'']

end Right

/-! ## El lado izquierdo: la cadena al revés -/

/-- La zona de la cadena leída al revés: el bloque `j` pasa a `n - 1 - j`; el separador `i`, a `n - i`. -/
def zoneRevN (n : Nat) (zone : Nat → Nat) (z : Nat) : Nat :=
  if zone z < n then n - 1 - zone z else if n + 1 ≤ zone z ∧ zone z < 2 * n then 3 * n - zone z else zone z

section Rev

variable {n : Nat} {zone : Nat → Nat}

/-- Los tres casos de `zoneRevN`. -/
theorem zoneRevN_cases (n : Nat) (zone : Nat → Nat) (z : Nat) :
    (zone z < n ∧ zoneRevN n zone z = n - 1 - zone z) ∨
    (n + 1 ≤ zone z ∧ zone z < 2 * n ∧ zoneRevN n zone z = 3 * n - zone z) ∨
    (n ≤ zone z ∧ ¬ (n + 1 ≤ zone z ∧ zone z < 2 * n) ∧ zoneRevN n zone z = zone z) := by
  unfold zoneRevN
  by_cases h1 : zone z < n
  · exact Or.inl ⟨h1, if_pos h1⟩
  rw [if_neg h1]
  by_cases h2 : n + 1 ≤ zone z ∧ zone z < 2 * n
  · exact Or.inr (Or.inl ⟨h2.1, h2.2, if_pos h2⟩)
  · exact Or.inr (Or.inr ⟨by omega, h2, if_neg h2⟩)

theorem zoneRevN_blk {j : Nat} (hj : j < n) {z : Nat} : zoneRevN n zone z = j ↔ zone z = n - 1 - j := by
  rcases zoneRevN_cases n zone z with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ <;> rw [e] <;> omega

theorem zoneRevN_sep {i : Nat} (hi : 1 ≤ i) (hin : i < n) {z : Nat} :
    zoneRevN n zone z = n + i ↔ zone z = n + (n - i) := by
  rcases zoneRevN_cases n zone z with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ <;> rw [e] <;> omega

theorem outN_rev {z : Nat} : OutN n (zoneRevN n zone) z ↔ OutN n zone z := by
  unfold OutN
  rcases zoneRevN_cases n zone z with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ <;> rw [e] <;> omega

/-- El bloque cerrado `j`, al revés. -/
theorem blkN_rev {j z : Nat} (hj : j < n) (h : BlkN n zone j z) : BlkN n (zoneRevN n zone) (n - 1 - j) z := by
  rcases h with h | ⟨h1, h⟩ | ⟨h1, h⟩
  · exact Or.inl ((zoneRevN_blk (by omega)).mpr (by omega))
  · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
    rw [show n + (n - 1 - j) + 1 = n + (n - j) by omega]
    exact (zoneRevN_sep (by omega) (by omega)).mpr (by omega)
  · refine Or.inr (Or.inl ⟨by omega, ?_⟩)
    exact (zoneRevN_sep (by omega) (by omega)).mpr (by omega)

/-- **La cadena al revés es una cadena.** -/
theorem chainN_rev (D : ChainN φ n zone) : ChainN φ n (zoneRevN n zone) := by
  refine ⟨D.two, fun z a b => ?_, fun i a b z z' h h' => ?_, fun y1 y2 y3 a b c => ?_, fun y1 y2 y3 a b c => ?_,
    fun j a b z z' h h' => ?_, fun c hc => ?_⟩
  · rcases zoneRevN_cases n zone z with ⟨_, e⟩ | ⟨a', b', _⟩ | ⟨_, _, e⟩
    · omega
    · exact D.sepv z a' b'
    · omega
  · exact D.sep1 (n - i) (by omega) (by omega) z z' ((zoneRevN_sep a b).mp h) ((zoneRevN_sep a b).mp h')
  · have t := D.two
    have r := fun {y} (h : zoneRevN n zone y = 0) => (zoneRevN_blk (zone := zone) (by omega)).mp h
    exact D.cardL y1 y2 y3 (by have := r a; omega) (by have := r b; omega) (by have := r c; omega)
  · have t := D.two
    have r := fun {y} (h : zoneRevN n zone y = n - 1) => (zoneRevN_blk (zone := zone) (by omega)).mp h
    exact D.card0 y1 y2 y3 (by have := r a; omega) (by have := r b; omega) (by have := r c; omega)
  · exact D.cardM (n - 1 - j) (by omega) (by omega) z z' ((zoneRevN_blk (by omega)).mp h)
      ((zoneRevN_blk (by omega)).mp h')
  · rcases D.cl c hc with ⟨o1, o2, o3⟩ | ⟨j, hj, i1, i2, i3⟩
    · exact Or.inl ⟨outN_rev.mpr o1, outN_rev.mpr o2, outN_rev.mpr o3⟩
    · exact Or.inr ⟨n - 1 - j, by omega, blkN_rev hj i1, blkN_rev hj i2, blkN_rev hj i3⟩

/-- El extremo izquierdo fijo, como extremo derecho de la cadena al revés. -/
theorem fixedEnd_rev {P0 : Assign → Prop} {a : Nat} (ha : a < n)
    (h : 1 ≤ a → ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + a → c z = c' z) :
    FixedEnd n (zoneRevN n zone) P0 (n - a) := by
  intro hb c c' q q' z hz
  exact h (by omega) c c' q q' z ((zoneRevN_sep (by omega) (by omega)).mp hz |>.trans (by omega))

end Rev

/-! ## El pegado en `v` -/

section Glue

variable {n : Nat} {zone : Nat → Nat}

/-- **Pegar los dos lados en `v`** (zona `n + m`): el lado izquierdo (bloques `a … m-1`, de la cadena al revés), el
derecho (bloques `m … b-1`), y `a0` fuera; los extremos `a` y `b`, libres (`0`, `n`) o fijos. -/
theorem glue_sides_tri (hl : LocPair φ P0 P σ) (D : ChainN φ n zone) {v : Nat} (hv : stepVar φ σ = some v)
    {m a b : Nat} (hzv : zone v = n + m) (hm1 : 1 ≤ m) (ham : a < m) (hmb : m < b) (hbn : b ≤ n)
    (hfa : 1 ≤ a → ∀ c c', P0 c → P0 c' → ∀ z, zone z = n + a → c z = c' z) (hfb : FixedEnd n zone P0 b)
    {x u w : PathNodeId} {a0 : Assign} (h0 : P0 a0) (hx0 : pidOfAssign φ a0 x.id.step = x)
    (hu0 : pidOfAssign φ a0 u.id.step = u) (hw0 : pidOfAssign φ a0 w.id.step = w) {sL sR : Nat → Assign}
    (OL : SideOut φ n (zoneRevN n zone) P0 P x.id.step u.id.step w.id.step a0 (n - m) (n - a) sL)
    (OR : SideOut φ n zone P0 P x.id.step u.id.step w.id.step a0 m b sR)
    (hpv : InW φ x.id.step u.id.step w.id.step v → ∃ c, P c ∧ c v = a0 v) : TriOf φ P x u w := by
  have hmn : m < n := by omega
  have sv : ∀ {c c'}, P c → P c' → c v = c' v := fun q q' => hl.sameVar hv q q'
  -- `v` es el único separador `m`
  have only : ∀ z, zone z = n + m → z = v := fun z hz => D.sep1 m hm1 hmn z v hz hzv
  let src : Nat → Assign := fun p => if p < a then a0 else if p < m then sL (n - 1 - p) else if p < b then sR p
    else a0
  have sA : ∀ p, p < a → src p = a0 := fun p h => by simp only [src]; rw [if_pos h]
  have sLp : ∀ p, a ≤ p → p < m → src p = sL (n - 1 - p) := fun p h h' => by
    simp only [src]; rw [if_neg (by omega), if_pos h']
  have sRp : ∀ p, m ≤ p → p < b → src p = sR p := fun p h h' => by
    simp only [src]; rw [if_neg (by omega), if_neg (by omega), if_pos h']
  have sB : ∀ p, b ≤ p → src p = a0 := fun p h => by
    simp only [src]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- de `P0`
  have hs : ∀ j, j < n → P0 (src j) := by
    intro j hj
    by_cases h1 : j < a
    · rw [sA j h1]; exact h0
    by_cases h2 : j < m
    · rw [sLp j (by omega) h2]; exact OL.p0 _ (by omega) (by omega)
    by_cases h3 : j < b
    · rw [sRp j (by omega) h3]; exact OR.p0 _ (by omega) h3
    · rw [sB j (by omega)]; exact h0
  have pL : P (sL (n - m)) := OL.pm
  have pR : P (sR m) := OR.pm
  -- las uniones
  have hJ : JoinN n zone src := by
    intro q hq1 hqn z hz
    by_cases c1 : q < a
    · rw [sA _ (by omega), sA _ c1]
    by_cases c2 : q = a
    · subst c2
      rw [sA _ (by omega), sLp _ (by omega) ham]
      exact hfa hq1 a0 _ h0 (OL.p0 _ (by omega) (by omega)) z hz
    by_cases c3 : q < m
    · rw [sLp _ (by omega) (by omega), sLp _ (by omega) c3]
      have := OL.join (n - q) (by omega) (by omega) z ((zoneRevN_sep (i := n - q) (by omega) (by omega)).mpr (by omega))
      rw [show n - q - 1 = n - 1 - q by omega, show n - q = n - 1 - (q - 1) by omega] at this
      exact this.symm
    by_cases c4 : q = m
    · subst c4
      rw [sLp _ (by omega) (by omega), sRp _ (by omega) hmb, only z hz, show n - 1 - (q - 1) = n - q by omega]
      exact sv pL pR
    by_cases c5 : q < b
    · rw [sRp _ (by omega) (by omega), sRp _ (by omega) c5]
      exact OR.join q (by omega) c5 z hz
    by_cases c6 : q = b
    · subst c6
      rw [sRp _ (by omega) (by omega), sB _ (Nat.le_refl _)]
      exact hfb hqn _ a0 (OR.p0 _ (by omega) (by omega)) h0 z hz
    · rw [sB _ (by omega), sB _ (by omega)]
  -- de `P`, los bloques de `v`
  have hP : ∀ j, j < n → BlkN n zone j v → P (src j) := by
    intro j hj hB
    rcases hB with h | ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · have e : j = m := by omega
      subst e; rw [sRp _ (Nat.le_refl _) hmb]; exact pR
    · have e : j = m - 1 := by omega
      subst e; rw [sLp _ (by omega) (by omega), show n - 1 - (m - 1) = n - m by omega]; exact pL
  -- coincidir con `a0`
  have ha : ∀ p, p < n → Agr φ x.id.step u.id.step w.id.step (OwnN n zone p) (src p) a0 := by
    intro p hp z hz hw
    by_cases c1 : p < a
    · rw [sA _ c1]
    by_cases c2 : p < m
    · rw [sLp _ (by omega) c2]
      by_cases hzv' : zone z = n + m
      · rw [only z hzv']
        obtain ⟨c, qc, ec⟩ := hpv (by rw [← only z hzv']; exact hw)
        have q' : P (sL (n - 1 - p)) := by
          rcases hz with h | ⟨_, h⟩
          · omega
          · rw [show n - 1 - p = n - m by omega]; exact pL
        exact (sv q' qc).trans ec
      · have hB : BlkN n zone p z := by
          rcases hz with h | ⟨h1, h⟩
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h1, h⟩)
        refine OL.agr (n - 1 - p) (by omega) (by omega) z (blkN_rev hp hB) (fun e => hzv' ?_) hw
        have := (zoneRevN_sep (zone := zone) (by omega : 1 ≤ n - m) (by omega)).mp e
        omega
    by_cases c3 : p < b
    · rw [sRp _ (by omega) c3]
      have hB : BlkN n zone p z := by
        rcases hz with h | ⟨h1, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨h1, h⟩)
      refine OR.agr p (by omega) c3 z hB (fun e => ?_) hw
      rcases hz with h | ⟨_, h⟩ <;> omega
    · rw [sB _ (by omega)]
  exact glueN_tri hl D hv ⟨m, hmn, Or.inr (Or.inl ⟨hm1, hzv⟩)⟩ h0 hx0 hu0 hw0 hs hJ hP ha

end Glue

end GPathB

end AbsSatBingo.Model
