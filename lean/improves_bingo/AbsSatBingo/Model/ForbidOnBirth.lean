-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnBirth.lean
import AbsSatBingo.Model.ForbidOnHi

/-!
# La forma normal del nacimiento

Lo que queda abierto de `PrevCut` (`HPrevLo`) es una base muerta de una llegada que la entrada `a` ya tenía prohibida
y que ninguna cima de `a` sostiene entera. Aquí se demuestra **qué forma tiene** (`birth_pattern`), sin hipótesis:

* la cima `t` tiene **dos padres distintos** `pf`, `ph` en `a`;
* `pf` es vecino de los tres nodos de la base, sostiene las dos caras con un nodo `v` y tiene **escrito** el trío con
  la arista opuesta `u–w`;
* `ph` sostiene la cara `(u, w)`.

Sale de tres piezas:

* `arrOn_face_parent` (cada cara de `t` la sostiene un padre en `a`);
* **`holdsFace_down`**: una cara sostenida por una cima de una entrada baja a la entrada de la línea anterior que
  creó esa cima (la cima es de un solo lado de la unión, el join habría prohibido el triángulo, y `up_forbid` es
  completo). Da el color del padre de la cima, y aplicada dos veces el del abuelo;
* el palomar: los padres de `t` solo difieren en el color del abuelo, que es la clave de una entrada de dos líneas
  atrás, y una línea del mapa bin tiene como mucho dos entradas.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Driver Machine MachineOn

-- ============================================================
-- Tríos escritos y sin escribir
-- ============================================================

/-- Un trío del cierre simétrico está escrito, en el orden que se pida. -/
theorem listed_of_sym {g : GPathB} {a b r : PathNodeId} (h : Sym (TF g) a b r) :
    ∃ σ ∈ g.trios, trioIs a b r σ = true := by
  have get : ∀ {p q w}, TF g p q w → ∃ σ ∈ g.trios, trioIs p q w σ = true := by
    intro p q w hf
    have hd := hf.2
    unfold deadTrio at hd
    rw [Bool.and_eq_true] at hd
    exact List.any_eq_true.mp hd.2
  unfold Sym at h
  rcases h with h | h | h | h | h | h
  · exact get h
  · obtain ⟨σ, hσ, hti⟩ := get h; exact ⟨σ, hσ, trioIs_swap23 hti⟩
  · obtain ⟨σ, hσ, hti⟩ := get h; exact ⟨σ, hσ, trioIs_swap12 hti⟩
  · obtain ⟨σ, hσ, hti⟩ := get h; exact ⟨σ, hσ, trioIs_swap12 (trioIs_swap23 hti)⟩
  · obtain ⟨σ, hσ, hti⟩ := get h; exact ⟨σ, hσ, trioIs_swap23 (trioIs_swap12 hti)⟩
  · obtain ⟨σ, hσ, hti⟩ := get h; exact ⟨σ, hσ, trioIs_swap23 (trioIs_swap12 (trioIs_swap23 hti))⟩

/-- Un trío sin escribir no está prohibido, en ningún orden. -/
theorem not_sym_of_unlisted {g : GPathB} {p x y : PathNodeId} (hn : ∀ τ ∈ g.trios, trioIs p x y τ = false) :
    ¬ Sym (TF g) x y p := by
  intro hs
  obtain ⟨σ, hσ, hti⟩ := listed_of_sym (sym_perm hs (a := p) (b := x) (r := y) (by simp [perms]))
  rw [hn σ hσ] at hti
  cases hti

theorem unlisted_swap {g : GPathB} {p x y : PathNodeId} (hn : ∀ τ ∈ g.trios, trioIs p x y τ = false) :
    ∀ τ ∈ g.trios, trioIs p y x τ = false := by
  intro τ hτ
  cases hc : trioIs p y x τ
  · rfl
  · have := hn τ hτ
    rw [trioIs_swap23 hc] at this
    cases this

theorem pid_ext {p q : PathNodeId} (h1 : p.id = q.id) (h2 : p.parent_id = q.parent_id)
    (h3 : p.gparent_id = q.gparent_id) : p = q := by
  cases p; cases q; simp_all

-- ============================================================
-- Las cimas de una entrada vienen de una entrada de la línea anterior
-- ============================================================

/-- **El color del padre de una cima de una entrada** es la clave de una entrada de la línea anterior. -/
theorem top_parent_mem {φ : Cnf} {T : Int} (hT : 1 ≤ T) {prev : Line} (h : LInvTop φ T prev) (hbk : LineBk prev)
    {a : NodeId × GPathB} (ha : a ∈ advanceM .on φ prev) {p : PathNodeId} (hp : p ∈ a.2.alive)
    (hps : p.id.step = a.2.current_step - 1) : ∃ kv ∈ prev, p.parent_id = some kv.1 := by
  rcases entry_shapeOn (line_cases h.nodup h.keys) h.nodup ha with ⟨kv, hkv, hs, hae⟩ |
    ⟨k1, hk1, k2, hk2, _, hs1, hs2, hae⟩
  · rw [hae] at hp hps
    obtain ⟨f, _⟩ := arrOn_tops hT (h.on kv hkv) (hbk kv hkv).1 hs
    obtain ⟨b, hb, hpb⟩ := f p hp hps
    exact ⟨kv, hkv, by rw [hpb, hb]⟩
  · obtain ⟨e1, _⟩ := arrTop_facts hT h hk1 hs1
    obtain ⟨e2, _⟩ := arrTop_facts hT h hk2 hs2
    have hjoin : doJoinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1) = joinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1) := by
      unfold doJoinOn okJoin
      rw [if_pos (by simp [e1.1.step, e2.1.step, e1.1.mp, e2.1.mp, e1.1.valid, e2.1.valid])]
    obtain ⟨f1, _⟩ := arrOn_tops hT (h.on k1 hk1) (hbk k1 hk1).1 hs1
    obtain ⟨f2, _⟩ := arrOn_tops hT (h.on k2 hk2) (hbk k2 hk2).1 hs2
    rw [hae, hjoin] at hp hps
    rw [step_joinOn] at hps
    obtain ⟨T', hT'e⟩ := joinOn_eq (arrOn φ k1 a.1) (arrOn φ k2 a.1)
    rw [hT'e] at hp
    rcases (alive_join _ _ p).mp hp with hp1 | hp2
    · obtain ⟨b, hb, hpb⟩ := f1 p hp1 hps
      exact ⟨k1, hk1, by rw [hpb, hb]⟩
    · obtain ⟨b, hb, hpb⟩ := f2 p hp2 (by rw [← e1.1.step.trans e2.1.step.symm]; exact hps)
      exact ⟨k2, hk2, by rw [hpb, hb]⟩

/-- **Una cara sostenida por una cima de una entrada baja a la línea anterior.** Si la cima `p` de la entrada `a` es
vecina de `x` y de `y` (nodos de la línea anterior), `x–y` es arista y el trío `{p, x, y}` no está escrito, entonces
la entrada `kv` de la línea anterior que creó `p` (su clave es el color del padre de `p`) tiene una cima, padre de
`p`, que sostiene `(x, y)`. -/
theorem holdsFace_down {φ : Cnf} {T : Int} (hT : 1 ≤ T) {prev : Line} (h : LInvTop φ T prev) (hbk : LineBk prev)
    {a : NodeId × GPathB} (ha : a ∈ advanceM .on φ prev) {p x y : PathNodeId} (hp : p ∈ a.2.alive)
    (hps : p.id.step = a.2.current_step - 1) (hx : x.id.step < T) (hy : y.id.step < T) (nxy : x ≠ y)
    (hpx : a.2.Adj p x) (hpy : a.2.Adj p y) (hxy : a.2.Adj x y) (hn : ∀ τ ∈ a.2.trios, trioIs p x y τ = false) :
    ∃ kv ∈ prev, p.parent_id = some kv.1 ∧ HoldsFace kv.2 p x y := by
  have unl : ∀ {g : GPathB}, (∀ τ ∈ g.trios, trioIs p x y τ = false) → ¬ TF g p x y := by
    intro g hg hf
    have hd := hf.2
    unfold deadTrio at hd
    rw [Bool.and_eq_true] at hd
    obtain ⟨τ, hτ, hti⟩ := List.any_eq_true.mp hd.2
    rw [hg τ hτ] at hti
    cases hti
  rcases entry_shapeOn (line_cases h.nodup h.keys) h.nodup ha with ⟨kv, hkv, hs, hae⟩ |
    ⟨k1, hk1, k2, hk2, hne, hs1, hs2, hae⟩
  · rw [hae] at hp hps hpx hpy hxy hn
    obtain ⟨_, ia, _, _, _⟩ := arrTop_facts hT h hkv hs
    obtain ⟨f, _⟩ := arrOn_tops hT (h.on kv hkv) (hbk kv hkv).1 hs
    obtain ⟨b, hb, hpb⟩ := f p hp hps
    exact ⟨kv, hkv, by rw [hpb, hb], arrOn_face_parent (h.on kv hkv) (h.inv kv hkv) hs hp hps (ia.edges p x hpx).2
      (ia.edges p y hpy).2 hx hy nxy hpx hpy hxy (unl hn)⟩
  · obtain ⟨e1, i1, _, _, _⟩ := arrTop_facts hT h hk1 hs1
    obtain ⟨e2, i2, _, _, _⟩ := arrTop_facts hT h hk2 hs2
    have hjoin : doJoinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1) = joinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1) := by
      unfold doJoinOn okJoin
      rw [if_pos (by simp [e1.1.step, e2.1.step, e1.1.mp, e2.1.mp, e1.1.valid, e2.1.valid])]
    obtain ⟨f1, _⟩ := arrOn_tops hT (h.on k1 hk1) (hbk k1 hk1).1 hs1
    obtain ⟨f2, _⟩ := arrOn_tops hT (h.on k2 hk2) (hbk k2 hk2).1 hs2
    rw [hae, hjoin] at hp hps hpx hpy hxy hn
    have hcs12 : (arrOn φ k1 a.1).current_step = (arrOn φ k2 a.1).current_step := e1.1.step.trans e2.1.step.symm
    rw [step_joinOn] at hps
    have hps2 : p.id.step = (arrOn φ k2 a.1).current_step - 1 := by rw [← hcs12]; exact hps
    obtain ⟨T', hT'e⟩ := joinOn_eq (arrOn φ k1 a.1) (arrOn φ k2 a.1)
    have halive : p ∈ (arrOn φ k1 a.1).alive ∨ p ∈ (arrOn φ k2 a.1).alive := by
      rw [hT'e] at hp; exact (alive_join _ _ p).mp hp
    have hadj : ∀ x w, (joinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1)).Adj x w →
        (arrOn φ k1 a.1).Adj x w ∨ (arrOn φ k2 a.1).Adj x w := fun x w h => by
      rw [hT'e] at h; exact adj_join_cases h
    have hsep : p ∈ (arrOn φ k1 a.1).alive → p ∈ (arrOn φ k2 a.1).alive → False := by
      intro h1 h2
      obtain ⟨b1, hb1, hp1⟩ := f1 p h1 hps
      obtain ⟨b2, hb2, hp2⟩ := f2 p h2 hps2
      rw [hp1, hb1, hb2] at hp2
      exact hne (Option.some.inj hp2)
    have npx : p ≠ x := fun e => by rw [← e, hps, e1.1.step] at hx; omega
    have npy : p ≠ y := fun e => by rw [← e, hps, e1.1.step] at hy; omega
    have cutJ : SideForbids (arrOn φ k1 a.1) (TF (arrOn φ k1 a.1)) p x y →
        SideForbids (arrOn φ k2 a.1) (TF (arrOn φ k2 a.1)) p x y → False := fun c1 c2 =>
      unl hn (tF_joinOn_of_cut i1.edges i2.edges hpx hpy hxy npx npy nxy c1 c2)
    rcases halive with hp1 | hp2
    · have noO : ¬ ((arrOn φ k2 a.1).Adj p x ∧ (arrOn φ k2 a.1).Adj p y ∧ (arrOn φ k2 a.1).Adj x y) :=
        fun hh => hsep hp1 (i2.edges p x hh.1).1
      have spx := (hadj p x hpx).resolve_right (fun ho => hsep hp1 (i2.edges p x ho).1)
      have spy := (hadj p y hpy).resolve_right (fun ho => hsep hp1 (i2.edges p y ho).1)
      have sxy : (arrOn φ k1 a.1).Adj x y := by
        apply Classical.byContradiction
        intro hno
        exact cutJ (Or.inl fun hh => hno hh.2.2) (Or.inl noO)
      have hnS : ¬ TF (arrOn φ k1 a.1) p x y := fun hf => cutJ (Or.inr hf) (Or.inl noO)
      obtain ⟨b, hb, hpb⟩ := f1 p hp1 hps
      exact ⟨k1, hk1, by rw [hpb, hb], arrOn_face_parent (h.on k1 hk1) (h.inv k1 hk1) hs1 hp1 hps (i1.edges p x spx).2
        (i1.edges p y spy).2 hx hy nxy spx spy sxy hnS⟩
    · have noO : ¬ ((arrOn φ k1 a.1).Adj p x ∧ (arrOn φ k1 a.1).Adj p y ∧ (arrOn φ k1 a.1).Adj x y) :=
        fun hh => hsep (i1.edges p x hh.1).1 hp2
      have spx := (hadj p x hpx).resolve_left (fun ho => hsep (i1.edges p x ho).1 hp2)
      have spy := (hadj p y hpy).resolve_left (fun ho => hsep (i1.edges p y ho).1 hp2)
      have sxy : (arrOn φ k2 a.1).Adj x y := by
        apply Classical.byContradiction
        intro hno
        exact cutJ (Or.inl noO) (Or.inl fun hh => hno hh.2.2)
      have hnS : ¬ TF (arrOn φ k2 a.1) p x y := fun hf => cutJ (Or.inl noO) (Or.inr hf)
      obtain ⟨b, hb, hpb⟩ := f2 p hp2 hps2
      exact ⟨k2, hk2, by rw [hpb, hb], arrOn_face_parent (h.on k2 hk2) (h.inv k2 hk2) hs2 hp2 hps2
        (i2.edges p x spx).2 (i2.edges p y spy).2 hx hy nxy spx spy sxy hnS⟩

/-- **El color del abuelo de una cima que sostiene una cara** es la clave de una entrada de dos líneas atrás. -/
theorem holder_gparent_mem {φ : Cnf} {T : Int} (hT : 1 ≤ T) {L0 : Line} (h0 : LInvTop φ T L0) (hbk0 : LineBk L0)
    (h1 : LInvTop φ (T + 1) (advanceM .on φ L0)) (hbk1 : LineBk (advanceM .on φ L0))
    {a : NodeId × GPathB} (ha : a ∈ advanceM .on φ (advanceM .on φ L0)) {p x y : PathNodeId} (hp : p ∈ a.2.alive)
    (hps : p.id.step = a.2.current_step - 1) (hx : x.id.step < T + 1) (hy : y.id.step < T + 1) (nxy : x ≠ y)
    (hpx : a.2.Adj p x) (hpy : a.2.Adj p y) (hxy : a.2.Adj x y) (hn : ∀ τ ∈ a.2.trios, trioIs p x y τ = false) :
    ∃ E ∈ L0, p.gparent_id = some E.1 := by
  obtain ⟨kv, hkv, _, q, hq, hqs, hcq, _⟩ := holdsFace_down (by omega : (1 : Int) ≤ T + 1) h1 hbk1 ha hp hps hx hy nxy
    hpx hpy hxy hn
  obtain ⟨E, hE, hqp⟩ := top_parent_mem hT h0 hbk0 hkv hq hqs
  exact ⟨E, hE, by rw [hcq.2.1]; exact hqp⟩

-- ============================================================
-- La forma normal
-- ============================================================

/-- **La cima `p` de `g`, padre posible de `t`, sostiene la cara `(x, y)`.** -/
def HoldsBy (g : GPathB) (p t x y : PathNodeId) : Prop :=
  p ∈ g.alive ∧ p.id.step = g.current_step - 1 ∧ Compat p t ∧ g.Adj p x ∧ g.Adj p y ∧ g.Adj x y ∧
    ∀ τ ∈ g.trios, trioIs p x y τ = false

theorem holdsBy_swap {g : GPathB} {p t x y : PathNodeId} (h : HoldsBy g p t x y) : HoldsBy g p t y x :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.1, (adj_symm g x y).mp h.2.2.2.2.2.1, unlisted_swap h.2.2.2.2.2.2⟩

/-- **El nacimiento**: la cima `t` tiene en `g` dos padres distintos; `pf` sostiene las dos caras con `v` y tiene
escrito el trío con la arista opuesta `u–w`; `ph` sostiene `(u, w)`. -/
def BirthAt (g : GPathB) (t v u w : PathNodeId) : Prop :=
  ∃ pf ph, pf ≠ ph ∧ HoldsBy g pf t v u ∧ HoldsBy g pf t v w ∧ HoldsBy g ph t u w ∧
    ∃ τ ∈ g.trios, trioIs pf u w τ = true

/-- De tres entradas de una línea de como mucho dos, dos coinciden. -/
theorem pigeon3 {l : Line} (hl : l = [] ∨ (∃ a, l = [a]) ∨ (∃ a b, l = [a, b])) {E1 E2 E3 : NodeId × GPathB}
    (m1 : E1 ∈ l) (m2 : E2 ∈ l) (m3 : E3 ∈ l) : E1 = E2 ∨ E1 = E3 ∨ E2 = E3 := by
  rcases hl with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · exact absurd m1 List.not_mem_nil
  · rw [List.mem_singleton] at m1 m2
    exact Or.inl (m1.trans m2.symm)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at m1 m2 m3
    rcases m1 with rfl | rfl <;> rcases m2 with rfl | rfl <;> rcases m3 with rfl | rfl <;> simp

/-- El núcleo: con los papeles `(v, u, w)` ya repartidos. `hdead` construye la base muerta de `g` bajo `pf` si `pf`
sostuviera también `(u, w)`. -/
theorem birth_core {g : GPathB} {t v u w pf ph : PathNodeId} (h1 : HoldsBy g pf t v u) (h2 : HoldsBy g pf t v w)
    (h3 : HoldsBy g ph t u w) (hdead : (∀ τ ∈ g.trios, trioIs pf u w τ = false) → False) : BirthAt g t v u w := by
  have hl : ∃ τ ∈ g.trios, trioIs pf u w τ = true := by
    apply Classical.byContradiction
    intro hno
    apply hdead
    intro τ hτ
    cases hc : trioIs pf u w τ
    · rfl
    · exact absurd ⟨τ, hτ, hc⟩ hno
  refine ⟨pf, ph, ?_, h1, h2, h3, hl⟩
  intro e
  obtain ⟨τ, hτ, hti⟩ := hl
  rw [e, h3.2.2.2.2.2.2 τ hτ] at hti
  cases hti

/-- **La forma normal del nacimiento.** Una base muerta `(x, y, z)` de una llegada de la entrada `a`, de nodos de la
línea anterior, que `a` ya tiene prohibida y que ninguna cima de `a` sostiene entera, tiene la forma `BirthAt`, con
alguno de sus tres nodos en el papel de `v`. -/
theorem birth_pattern {φ : Cnf} {T : Int} (hT : 1 ≤ T) {L0 : Line} (h0 : LInvTop φ T L0) (hbk0 : LineBk L0)
    (h1 : LInvTop φ (T + 1) (advanceM .on φ L0)) (hbk1 : LineBk (advanceM .on φ L0))
    (h2 : LInvTop φ (T + 1 + 1) (advanceM .on φ (advanceM .on φ L0)))
    (hbk2 : LineBk (advanceM .on φ (advanceM .on φ L0)))
    {a : NodeId × GPathB} (ha : a ∈ advanceM .on φ (advanceM .on φ L0)) {d : NodeId} (hs : SendsOn φ a d)
    {t x y z : PathNodeId} (hd : DeadBase (arrOn φ a d) t x y z) (hx : x.id.step < T + 1) (hy : y.id.step < T + 1)
    (hz : z.id.step < T + 1) (hfa : TF a.2 x y z) (hni : ¬ ∃ p, DeadBase a.2 p x y z) :
    BirthAt a.2 t x y z ∨ BirthAt a.2 t y x z ∨ BirthAt a.2 t z x y := by
  have hent := h2.on a ha
  have hcsa : a.2.current_step = T + 1 + 1 := hent.1.step
  obtain ⟨fxy, fxz, fyz⟩ := deadBase_arr_parents (by omega : (1 : Int) ≤ T + 1 + 1) hent (h2.inv a ha)
    (hbk2 a ha).2.1 (hbk2 a ha).2.2 hs hd
  obtain ⟨_, _, _, _, _, nxy, nxz, nyz, _⟩ := hd
  -- un sostén de una cara, como `HoldsBy`
  have mk : ∀ {u w : PathNodeId}, u.id.step < T + 1 → w.id.step < T + 1 → HoldsFace a.2 t u w →
      ∃ p, HoldsBy a.2 p t u w := by
    intro u w hu hw ⟨p, hp, hps, hc, hpu, hpw, huw, hn⟩
    exact ⟨p, hp, hps, hc, hpu, hpw, huw, hn (fun e => by rw [← e, hps, hcsa] at hu; omega)
      (fun e => by rw [← e, hps, hcsa] at hw; omega)⟩
  obtain ⟨p1, k1⟩ := mk hx hy fxy
  obtain ⟨p2, k2⟩ := mk hx hz fxz
  obtain ⟨p3, k3⟩ := mk hy hz fyz
  -- el color del abuelo de cada sostén
  have gp : ∀ {p u w : PathNodeId}, u.id.step < T + 1 → w.id.step < T + 1 → u ≠ w → HoldsBy a.2 p t u w →
      ∃ E ∈ L0, p.gparent_id = some E.1 := fun hu hw nuw hk =>
    holder_gparent_mem hT h0 hbk0 h1 hbk1 ha hk.1 hk.2.1 hu hw nuw hk.2.2.2.1 hk.2.2.2.2.1 hk.2.2.2.2.2.1
      hk.2.2.2.2.2.2
  obtain ⟨E1, m1, g1⟩ := gp hx hy nxy k1
  obtain ⟨E2, m2, g2⟩ := gp hx hz nxz k2
  obtain ⟨E3, m3, g3⟩ := gp hy hz nyz k3
  -- dos sostenes con el mismo abuelo son el mismo nodo
  have same : ∀ {p q : PathNodeId} {u w u' w' : PathNodeId} {E E' : NodeId × GPathB}, HoldsBy a.2 p t u w →
      HoldsBy a.2 q t u' w' → p.gparent_id = some E.1 → q.gparent_id = some E'.1 → E = E' → p = q := by
    intro p q u w u' w' E E' hp hq gp' gq e
    refine pid_ext (Option.some.inj (hp.2.2.1.1.symm.trans hq.2.2.1.1)) (hp.2.2.1.2.1.symm.trans hq.2.2.1.2.1) ?_
    rw [gp', gq, e]
  -- lo que haría de `pf` una cima con las tres caras vivas
  have dead : ∀ {pf : PathNodeId}, HoldsBy a.2 pf t x y → HoldsBy a.2 pf t x z → HoldsBy a.2 pf t y z → False := by
    intro pf a1 a2 a3
    have ne : ∀ {q : PathNodeId}, q.id.step < T + 1 → q ≠ pf := fun hq e => by
      rw [e, a1.2.1, hcsa] at hq; omega
    exact hni ⟨pf, a1.1, a1.2.1, ne hx, ne hy, ne hz, nxy, nxz, nyz, a1.2.2.2.1, a1.2.2.2.2.1, a2.2.2.2.2.1,
      a1.2.2.2.2.2.1, a2.2.2.2.2.2.1, a3.2.2.2.2.2.1, not_sym_of_unlisted a1.2.2.2.2.2.2,
      not_sym_of_unlisted a2.2.2.2.2.2.2, not_sym_of_unlisted a3.2.2.2.2.2.2, hfa⟩
  rcases pigeon3 (line_cases h0.nodup h0.keys) m1 m2 m3 with e | e | e
  · -- los sostenes de (x, y) y (x, z) coinciden: v = x
    have e' := same k1 k2 g1 g2 e
    subst e'
    exact Or.inl (birth_core k1 k2 k3 (fun hn => dead k1 k2
      ⟨k1.1, k1.2.1, k1.2.2.1, k1.2.2.2.2.1, k2.2.2.2.2.1, k3.2.2.2.2.2.1, hn⟩))
  · -- los de (x, y) y (y, z): v = y
    have e' := same k1 k3 g1 g3 e
    subst e'
    exact Or.inr (Or.inl (birth_core (holdsBy_swap k1) k3 k2 (fun hn => dead k1
      ⟨k1.1, k1.2.1, k1.2.2.1, k1.2.2.2.1, k3.2.2.2.2.1, k2.2.2.2.2.2.1, hn⟩ k3)))
  · -- los de (x, z) y (y, z): v = z
    have e' := same k2 k3 g2 g3 e
    subst e'
    exact Or.inr (Or.inr (birth_core (holdsBy_swap k2) (holdsBy_swap k3) k1 (fun hn => dead
      ⟨k2.1, k2.2.1, k2.2.2.1, k2.2.2.2.1, k3.2.2.2.1, k1.2.2.2.2.2.1, hn⟩ k2 k3)))

end GPathB

end AbsSatBingo.Model
