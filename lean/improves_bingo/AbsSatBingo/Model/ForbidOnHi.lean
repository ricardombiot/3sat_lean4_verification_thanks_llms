-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnHi.lean
import AbsSatBingo.Model.ForbidOnInherit

/-!
# `PrevCut` dividida: la regla no prohíbe triángulos viejos, y el nacimiento bajo

Lo que queda de `PrevCut` tras la herencia (`HPrevNew`) se parte en dos hipótesis:

* **`HNoRule`** (una llegada sola): un triángulo viejo prohibido en la llegada `arrOn φ kv d` ya estaba prohibido en
  la entrada `kv`, si es una base muerta bajo una cima de la llegada o tiene un nodo en la cima de `kv`. En una
  llegada `up_forbid` solo escribe tríos con la cima nueva, así que dice que la regla del review (del filtro y del
  UP) no prohíbe esos triángulos. **Sin esa restricción es falsa**: en `v6_c26_i1` la regla prohíbe 16 triángulos
  viejos, todos bajos y con una cima de dos caras vivas (`probe_norule.jl`).
* **`HPrevLo`**: `PrevCut` para las bases de nacimiento (ninguna cima de la entrada sostiene las tres caras) cuyos
  nodos existían una línea más atrás. Sale de **`HPrevLo2`**, el mismo corte dos líneas atrás (`hPrevLo_of_two`,
  por `lineCut_advance`), que es como se ve en las medidas: sin tríos, por un nodo o una arista que falta.

Con `HNoRule` queda demostrado el caso en que la base tiene **un nodo `q` en la cima de la línea anterior**
(`prevCut_hi`), herede o nazca: las entradas de otra clave no tienen a `q`; y la de la clave de `q` tiene la base
prohibida, porque la base entera es del lado de `q` (las aristas de `q` lo son; la arista opuesta la sostiene un
padre de la cima, `arrOn_face_parent`, que es hijo de `q` por `AdjPar` y por tanto de ese lado, y el join habría
prohibido su cara) y `HNoRule` la baja a la entrada.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Driver Machine MachineOn

-- ============================================================
-- Lo viejo de una llegada es del remitente
-- ============================================================

/-- Una posesión entre nodos viejos de la llegada es del remitente. -/
theorem arrOn_adj_old {φ : Cnf} {T : Int} {kv : NodeId × GPathB} (hent : EntOn T kv.1 kv.2) {d : NodeId}
    (hs : SendsOn φ kv d) {p q : PathNodeId} (hp : p.id.step < T) (hq : q.id.step < T)
    (h : (arrOn φ kv d).Adj p q) : kv.2.Adj p q := by
  have hok := hent.1
  have hcsY : (kv.2.filterAllOn (reqOf φ d)).current_step = T := by rw [step_filterAllOn]; exact hok.step
  have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by
    rw [hcsY, sonsOfMap_step φ kv.1 d hs.1, hok.key]; omega
  have hvY := valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
  exact (shrinks_filterAllOn kv.2 (reqOf φ d)).1.adj _ _
    (adj_addNode_old (title := "") (forb := isProhibited φ) hdY (by rw [hcsY]; exact hp) (by rw [hcsY]; exact hq)
      ((sub_upOn_addNode hvY).adj _ _ h))

/-- Un nodo viejo vivo en la llegada está vivo en el remitente. -/
theorem arrOn_alive_old {φ : Cnf} {T : Int} {kv : NodeId × GPathB} (hent : EntOn T kv.1 kv.2) (hi : SInvB kv.2)
    {d : NodeId} (hs : SendsOn φ kv d) {q : PathNodeId} (hq : q.id.step < T) (h : q ∈ (arrOn φ kv d).alive) :
    q ∈ kv.2.alive := by
  have hok := hent.1
  have hcsY : (kv.2.filterAllOn (reqOf φ d)).current_step = T := by rw [step_filterAllOn]; exact hok.step
  have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by
    rw [hcsY, sonsOfMap_step φ kv.1 d hs.1, hok.key]; omega
  have hvY := valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
  have hiY := sInvB_filterAllOn hi (reqOf φ d)
  rcases alive_addNode_cases (title := "") (forb := isProhibited φ) hiY.docs hiY.below hdY
    ((sub_upOn_addNode hvY).alive q h) with ⟨hq1, _⟩ | ⟨_, hq2⟩
  · exact (shrinks_filterAllOn kv.2 (reqOf φ d)).1.alive q hq1
  · rw [hcsY] at hq2; omega

-- ============================================================
-- Las dos hipótesis
-- ============================================================

/-- **La regla no prohíbe ciertos triángulos viejos**: un triángulo de nodos viejos (por debajo del paso `T` de la
línea), prohibido en la llegada de una entrada de la línea, ya estaba prohibido en la entrada, si es una base muerta
bajo una cima de la llegada (sus tres caras con la cima sin prohibir) o tiene un nodo en la cima de la entrada. -/
def HNoRule (φ : Cnf) (line : Line) (T : Int) : Prop :=
  ∀ kv ∈ line, ∀ d, SendsOn φ kv d → ∀ x y z, x.id.step < T → y.id.step < T → z.id.step < T →
    (arrOn φ kv d).Adj x y → (arrOn φ kv d).Adj x z → (arrOn φ kv d).Adj y z →
    ((∃ t, DeadBase (arrOn φ kv d) t x y z) ∨ x.id.step = T - 1 ∨ y.id.step = T - 1 ∨ z.id.step = T - 1) →
    TF (arrOn φ kv d) x y z → TF kv.2 x y z

/-- **El nacimiento bajo**: `PrevCut` para las bases muertas de una llegada cuyos nodos existían una línea antes de
`prev` y que la entrada `a` no tenía muertas bajo ninguna cima suya (ningún padre sostiene las tres caras). -/
def HPrevLo (φ : Cnf) (prev : Line) (T : Int) : Prop :=
  ∀ a ∈ advanceM .on φ prev, ∀ d, SendsOn φ a d → ∀ t x y z, DeadBase (arrOn φ a d) t x y z →
    x.id.step < T - 1 → y.id.step < T - 1 → z.id.step < T - 1 → ¬ (∃ p, DeadBase a.2 p x y z) →
    ∀ e ∈ prev, SideForbids e.2 (TF e.2) x y z

/-- **El nacimiento bajo, dos líneas atrás**: la base de nacimiento de una llegada de una entrada de dos líneas después
de `L0` la cortan todas las entradas de `L0`. -/
def HPrevLo2 (φ : Cnf) (L0 : Line) (T : Int) : Prop :=
  ∀ a ∈ advanceM .on φ (advanceM .on φ L0), ∀ d, SendsOn φ a d → ∀ t x y z, DeadBase (arrOn φ a d) t x y z →
    x.id.step < T → y.id.step < T → z.id.step < T → ¬ (∃ p, DeadBase a.2 p x y z) →
    ∀ E ∈ L0, SideForbids E.2 (TF E.2) x y z

/-- El corte dos líneas atrás sube una línea (`lineCut_advance`). -/
theorem hPrevLo_of_two {φ : Cnf} {T : Int} (hT : 1 ≤ T) {L0 : Line} (h0 : LInvTop φ T L0)
    (h2 : HPrevLo2 φ L0 T) : HPrevLo φ (advanceM .on φ L0) (T + 1) := by
  intro a ha d hs t x y z hd hx hy hz hni
  exact lineCut_advance hT h0 hd.2.2.2.2.2.1 hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.1 (by omega) (by omega) (by omega)
    (h2 a ha d hs t x y z hd (by omega) (by omega) (by omega) hni)

-- ============================================================
-- Un triángulo de la unión con un nodo y un sostén de un solo lado
-- ============================================================

/-- **Un triángulo prohibido de `J` es un triángulo prohibido del lado `S`** si uno de sus nodos, `q`, no es del otro
lado `O`, y la arista opuesta `u–w` tiene en `J` una cima `p`, tampoco de `O`, vecina de los dos y con el trío
`{p, u, w}` sin escribir: las aristas de `q` son de `S`; la opuesta también, porque `J` habría prohibido su triángulo
con `p`; y `J` guardó el triángulo porque `S` lo cortaba. -/
theorem tri_side {J S O : GPathB} (hadj : ∀ x w, J.Adj x w → S.Adj x w ∨ O.Adj x w) (heO : EdgesAlive O)
    (hcut2 : ∀ {x y z}, J.Adj x y → J.Adj x z → J.Adj y z → x ≠ y → x ≠ z → y ≠ z → SideForbids S (TF S) x y z →
      SideForbids O (TF O) x y z → TF J x y z)
    (hinv : ∀ {x y z}, TF J x y z → ∃ τ : PathNodeId × PathNodeId × PathNodeId, trioIs x y z τ = true ∧
      SideForbids S (TF S) τ.1 τ.2.1 τ.2.2)
    {p q u w x y z : PathNodeId} (hperm : (x, y, z) ∈ perms q u w) (hf : TF J x y z) (hqO : q ∉ O.alive)
    (hpO : p ∉ O.alive) (nuw : u ≠ w) (npu : p ≠ u) (npw : p ≠ w) (hqu : J.Adj q u) (hqw : J.Adj q w)
    (hpu : J.Adj p u) (hpw : J.Adj p w) (huw : J.Adj u w) (hntr : ∀ τ ∈ J.trios, trioIs p u w τ = false) :
    S.Adj x y ∧ S.Adj x z ∧ S.Adj y z ∧ TF S x y z := by
  have ssymm : ∀ {y w}, S.Adj y w → S.Adj w y := fun h => (adj_symm S _ _).mp h
  have squ : S.Adj q u := (hadj q u hqu).resolve_right (fun ho => hqO (heO q u ho).1)
  have sqw : S.Adj q w := (hadj q w hqw).resolve_right (fun ho => hqO (heO q w ho).1)
  have suw : S.Adj u w := by
    apply Classical.byContradiction
    intro hno
    have hJ : TF J p u w := hcut2 hpu hpw huw npu npw nuw (Or.inl fun h => hno h.2.2)
      (Or.inl fun h => hpO (heO p u h.1).1)
    have hd := hJ.2
    unfold deadTrio at hd
    rw [Bool.and_eq_true] at hd
    obtain ⟨τ, hτ, hti⟩ := List.any_eq_true.mp hd.2
    rw [hntr τ hτ] at hti
    cases hti
  obtain ⟨sxy, sxz, syz⟩ := tri_of_perms (R := fun y w => S.Adj y w) ssymm squ sqw suw hperm
  obtain ⟨τ, hti, hsf⟩ := hinv hf
  have hp : τ ∈ perms x y z := (trioIs_iff_perms x y z τ).mp hti
  obtain ⟨a, b, c⟩ := τ
  obtain ⟨a1, a2, a3⟩ := tri_of_perms (R := fun y w => S.Adj y w) ssymm sxy sxz syz hp
  have hT : TF S a b c := hsf.resolve_left (fun hno => hno ⟨a1, a2, a3⟩)
  have hsym : Sym (TF S) x y z := sym_perm (Or.inl hT) hp
  exact ⟨sxy, sxz, syz, tF_of_sym_adj sxy hf.1 hsym⟩

-- ============================================================
-- La base con un nodo en la cima de la línea anterior
-- ============================================================

/-- **La entrada que tiene a `q` tiene la base prohibida.** `q` es un nodo de la base en la cima de `prev`; `u`, `w`
son los otros dos; la cara `(t, u, w)` la sostiene un padre de `t` en `a`, y otro padre de `t` es vecino de `q`. -/
theorem tF_sender_of_top {φ : Cnf} {T : Int} (hT : 1 ≤ T) {prev : Line} (h : LInvTop φ T prev) (hbk : LineBk prev)
    (h' : LInvTop φ (T + 1) (advanceM .on φ prev)) (hbk' : LineBk (advanceM .on φ prev)) (hR : HNoRule φ prev T)
    {a : NodeId × GPathB} (ha : a ∈ advanceM .on φ prev) {t q u w x y z : PathNodeId}
    (hperm : (x, y, z) ∈ perms q u w) (hf : TF a.2 x y z) (hx : x.id.step < T) (hy : y.id.step < T)
    (hz : z.id.step < T) (htop : x.id.step = T - 1 ∨ y.id.step = T - 1 ∨ z.id.step = T - 1)
    (hqs : q.id.step = T - 1) (hus : u.id.step < T) (hws : w.id.step < T) (nuw : u ≠ w)
    (hqu : a.2.Adj q u) (hqw : a.2.Adj q w) (huw : HoldsFace a.2 t u w)
    (hpq : ∃ p ∈ a.2.alive, p.id.step = a.2.current_step - 1 ∧ Compat p t ∧ a.2.Adj p q) :
    ∀ e ∈ prev, q ∈ e.2.alive → TF e.2 x y z := by
  intro e he hqe
  have hT' : (1 : Int) ≤ T + 1 := by omega
  have hcsa : a.2.current_step = T + 1 := (h'.on a ha).1.step
  -- la clave de toda entrada de `prev` que tiene a `q` es el id de `q`
  have keyq : ∀ kv ∈ prev, q ∈ kv.2.alive → q.id = kv.1 := by
    intro kv hkv hq
    obtain ⟨n, hn, hnid⟩ := (h.inv kv hkv).docs q hq
    have := (hbk kv hkv).1 n hn (by rw [hnid, (h.on kv hkv).1.step]; exact hqs)
    rw [hnid] at this
    exact this
  have same : ∀ kv ∈ prev, q ∈ kv.2.alive → kv = e := fun kv hkv hq =>
    eq_of_nodup_keys h.nodup hkv he ((keyq kv hkv hq).symm.trans (keyq e he hqe))
  -- el sostén de la cara opuesta es hijo de `q`
  obtain ⟨p, hpa, hps, hpt, hpu, hpw, huw', hntr⟩ := huw
  obtain ⟨p', _, hp's, hp't, hp'q⟩ := hpq
  have hcq : Compat q p' := (hbk' a ha).2.1 p' q hp'q (by rw [hp's, hcsa, hqs]; omega)
  have hpp : p.parent_id = some q.id := by rw [← hpt.2.1, hp't.2.1]; exact hcq.1
  have npu : p ≠ u := fun e' => by rw [← e', hps, hcsa] at hus; omega
  have npw : p ≠ w := fun e' => by rw [← e', hps, hcsa] at hws; omega
  have hntr' : ∀ τ ∈ a.2.trios, trioIs p u w τ = false := hntr npu npw
  have hqa : q ∈ a.2.alive := ((h'.inv a ha).edges q u hqu).1
  have hqT : q.id.step < T := by omega
  rcases entry_shapeOn (line_cases h.nodup h.keys) h.nodup ha with ⟨kv, hkv, hs, hae⟩ |
    ⟨k1, hk1, k2, hk2, hne, hs1, hs2, hae⟩
  · -- una sola llegada
    rw [hae] at hf hqu hqw huw' hqa
    have hent := h.on kv hkv
    have := same kv hkv (arrOn_alive_old hent (h.inv kv hkv) hs hqT hqa)
    subst this
    obtain ⟨sxy, sxz, syz⟩ := tri_of_perms (R := fun y w => (arrOn φ kv a.1).Adj y w)
      (fun h => (adj_symm _ _ _).mp h) hqu hqw huw' hperm
    exact hR kv hkv a.1 hs x y z hx hy hz sxy sxz syz (Or.inr htop) hf
  · -- la unión de dos llegadas
    obtain ⟨e1, i1, n1, _, _⟩ := arrTop_facts hT h hk1 hs1
    obtain ⟨e2, i2, n2, _, _⟩ := arrTop_facts hT h hk2 hs2
    have hjoin : doJoinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1) = joinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1) := by
      unfold doJoinOn okJoin
      rw [if_pos (by simp [e1.1.step, e2.1.step, e1.1.mp, e2.1.mp, e1.1.valid, e2.1.valid])]
    obtain ⟨f1, _⟩ := arrOn_tops hT (h.on k1 hk1) (hbk k1 hk1).1 hs1
    obtain ⟨f2, _⟩ := arrOn_tops hT (h.on k2 hk2) (hbk k2 hk2).1 hs2
    have ea2 : a.2 = joinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1) := by rw [hae, hjoin]
    rw [ea2] at hf hqu hqw hpu hpw huw' hntr' hqa hpa hps
    obtain ⟨T', hT'e⟩ := joinOn_eq (arrOn φ k1 a.1) (arrOn φ k2 a.1)
    have halive : ∀ r ∈ (joinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1)).alive,
        r ∈ (arrOn φ k1 a.1).alive ∨ r ∈ (arrOn φ k2 a.1).alive := fun r hr => by
      rw [hT'e] at hr; exact (alive_join _ _ r).mp hr
    have hadj : ∀ x w, (joinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1)).Adj x w →
        (arrOn φ k1 a.1).Adj x w ∨ (arrOn φ k2 a.1).Adj x w := fun x w h => by
      rw [hT'e] at h; exact adj_join_cases h
    have hcsJ : (joinOn (arrOn φ k1 a.1) (arrOn φ k2 a.1)).current_step = (arrOn φ k1 a.1).current_step :=
      step_joinOn _ _
    have hcs12 : (arrOn φ k1 a.1).current_step = (arrOn φ k2 a.1).current_step := e1.1.step.trans e2.1.step.symm
    -- `q` y `p` son de un solo lado: el de la entrada que tiene a `q`
    have q1 : q ∈ (arrOn φ k1 a.1).alive → k1 = e := fun hq =>
      same k1 hk1 (arrOn_alive_old (h.on k1 hk1) (h.inv k1 hk1) hs1 hqT hq)
    have q2 : q ∈ (arrOn φ k2 a.1).alive → k2 = e := fun hq =>
      same k2 hk2 (arrOn_alive_old (h.on k2 hk2) (h.inv k2 hk2) hs2 hqT hq)
    have p1 : p ∈ (arrOn φ k1 a.1).alive → q.id = k1.1 := fun hp => by
      obtain ⟨b, hb, hpb⟩ := f1 p hp (by rw [← hcsJ]; exact hps)
      rw [hpp, hb] at hpb
      exact Option.some.inj hpb
    have p2 : p ∈ (arrOn φ k2 a.1).alive → q.id = k2.1 := fun hp => by
      obtain ⟨b, hb, hpb⟩ := f2 p hp (by rw [← hcs12, ← hcsJ]; exact hps)
      rw [hpp, hb] at hpb
      exact Option.some.inj hpb
    rcases halive q hqa with hq | hq
    · have hk := q1 hq
      have hqO : q ∉ (arrOn φ k2 a.1).alive := fun hq' => hne (by rw [hk, q2 hq'])
      have hpO : p ∉ (arrOn φ k2 a.1).alive := fun hp' => hne (by rw [hk, ← keyq e he hqe, p2 hp'])
      obtain ⟨sxy, sxz, syz, hTF⟩ := tri_side (S := arrOn φ k1 a.1) (O := arrOn φ k2 a.1) hadj i2.edges
        (fun hxy hxz hyz nxy nxz nyz s1 s2 => tF_joinOn_of_cut i1.edges i2.edges hxy hxz hyz nxy nxz nyz s1 s2)
        (fun hf' => by
          obtain ⟨τ, c1, c2, _⟩ := tF_joinOn_inv e1.2.1 e2.2.1 i1.edges i2.edges hf'
          exact ⟨τ, c1, c2⟩) hperm hf hqO hpO nuw npu npw hqu hqw hpu hpw huw' hntr'
      rw [← hk]
      exact hR k1 hk1 a.1 hs1 x y z hx hy hz sxy sxz syz (Or.inr htop) hTF
    · have hk := q2 hq
      have hqO : q ∉ (arrOn φ k1 a.1).alive := fun hq' => hne (by rw [hk, q1 hq'])
      have hpO : p ∉ (arrOn φ k1 a.1).alive := fun hp' => hne (by rw [hk, ← keyq e he hqe, p1 hp'])
      obtain ⟨sxy, sxz, syz, hTF⟩ := tri_side (S := arrOn φ k2 a.1) (O := arrOn φ k1 a.1)
        (fun x w h => (hadj x w h).symm) i1.edges
        (fun hxy hxz hyz nxy nxz nyz s2 s1 => tF_joinOn_of_cut i1.edges i2.edges hxy hxz hyz nxy nxz nyz s1 s2)
        (fun hf' => by
          obtain ⟨τ, c1, _, c2⟩ := tF_joinOn_inv e1.2.1 e2.2.1 i1.edges i2.edges hf'
          exact ⟨τ, c1, c2⟩) hperm hf hqO hpO nuw npu npw hqu hqw hpu hpw huw' hntr'
      rw [← hk]
      exact hR k2 hk2 a.1 hs2 x y z hx hy hz sxy sxz syz (Or.inr htop) hTF

/-- **`PrevCut` para las bases con un nodo en la cima de la línea anterior**, bajo `HNoRule`: las entradas que no
tienen ese nodo cortan la base sin más, y la que lo tiene la tiene prohibida (`tF_sender_of_top`). -/
theorem prevCut_hi {φ : Cnf} {T : Int} (hT : 1 ≤ T) {prev : Line} (h : LInvTop φ T prev) (hbk : LineBk prev)
    (h' : LInvTop φ (T + 1) (advanceM .on φ prev)) (hbk' : LineBk (advanceM .on φ prev)) (hR : HNoRule φ prev T)
    (hR' : HNoRule φ (advanceM .on φ prev) (T + 1)) {a : NodeId × GPathB} (ha : a ∈ advanceM .on φ prev)
    {d : NodeId} (hs : SendsOn φ a d) {t x y z : PathNodeId} (hd : DeadBase (arrOn φ a d) t x y z)
    (hx : x.id.step < T) (hy : y.id.step < T) (hz : z.id.step < T)
    (hhi : ¬ (x.id.step < T - 1 ∧ y.id.step < T - 1 ∧ z.id.step < T - 1)) :
    ∀ e ∈ prev, SideForbids e.2 (TF e.2) x y z := by
  have hT' : (1 : Int) ≤ T + 1 := by omega
  have hent' := h'.on a ha
  obtain ⟨fxy, fxz, fyz⟩ := deadBase_arr_parents hT' hent' (h'.inv a ha) (hbk' a ha).2.1 (hbk' a ha).2.2 hs hd
  have hd0 := hd
  obtain ⟨_, _, _, _, _, nxy, nxz, nyz, _, _, _, hxy, hxz, hyz, _, _, _, hf⟩ := hd
  have axy : a.2.Adj x y := arrOn_adj_old hent' hs (by omega) (by omega) hxy
  have axz : a.2.Adj x z := arrOn_adj_old hent' hs (by omega) (by omega) hxz
  have ayz : a.2.Adj y z := arrOn_adj_old hent' hs (by omega) (by omega) hyz
  have asymm : ∀ {y w}, a.2.Adj y w → a.2.Adj w y := fun h => (adj_symm a.2 _ _).mp h
  have hfa : TF a.2 x y z := hR' a ha d hs x y z (by omega) (by omega) (by omega) hxy hxz hyz (Or.inl ⟨t, hd0⟩) hf
  have par : ∀ {u w}, HoldsFace a.2 t u w →
      (∃ p ∈ a.2.alive, p.id.step = a.2.current_step - 1 ∧ Compat p t ∧ a.2.Adj p u) ∧
      (∃ p ∈ a.2.alive, p.id.step = a.2.current_step - 1 ∧ Compat p t ∧ a.2.Adj p w) :=
    fun ⟨p, h1, h2, h3, h4, h5, _⟩ => ⟨⟨p, h1, h2, h3, h4⟩, ⟨p, h1, h2, h3, h5⟩⟩
  intro e he
  have edg := (h.inv e he).edges
  by_cases cx : x.id.step = T - 1
  · by_cases hq : x ∈ e.2.alive
    · exact Or.inr (tF_sender_of_top hT h hbk h' hbk' hR ha (q := x) (u := y) (w := z) (by simp [perms]) hfa hx hy
        hz (Or.inl cx) cx hy hz nyz axy axz fyz (par fxy).1 e he hq)
    · exact Or.inl fun hh => hq (edg x y hh.1).1
  · by_cases cy : y.id.step = T - 1
    · by_cases hq : y ∈ e.2.alive
      · exact Or.inr (tF_sender_of_top hT h hbk h' hbk' hR ha (q := y) (u := x) (w := z) (by simp [perms]) hfa hx hy
          hz (Or.inr (Or.inl cy)) cy hx hz nxz (asymm axy) ayz fxz (par fxy).2 e he hq)
      · exact Or.inl fun hh => hq (edg x y hh.1).2
    · have cz : z.id.step = T - 1 := by omega
      by_cases hq : z ∈ e.2.alive
      · exact Or.inr (tF_sender_of_top hT h hbk h' hbk' hR ha (q := z) (u := x) (w := y) (by simp [perms]) hfa hx hy
          hz (Or.inr (Or.inr cz)) cz hx hy nxy (asymm axz) (asymm ayz) fxy (par fxz).2 e he hq)
      · exact Or.inl fun hh => hq (edg x z hh.2.1).2

/-- **`HPrevNew` sale de `HNoRule` y del nacimiento bajo.** -/
theorem hPrevNew_of_lo {φ : Cnf} {T : Int} (hT : 1 ≤ T) {prev : Line} (h : LInvTop φ T prev) (hbk : LineBk prev)
    (h' : LInvTop φ (T + 1) (advanceM .on φ prev)) (hbk' : LineBk (advanceM .on φ prev)) (hR : HNoRule φ prev T)
    (hR' : HNoRule φ (advanceM .on φ prev) (T + 1)) (hlo : HPrevLo φ prev T) : HPrevNew φ prev T := by
  intro a ha d hs t x y z hd hx hy hz hni
  by_cases hl : x.id.step < T - 1 ∧ y.id.step < T - 1 ∧ z.id.step < T - 1
  · exact hlo a ha d hs t x y z hd hl.1 hl.2.1 hl.2.2 (fun ⟨p, hp⟩ => hni ⟨p, hp, hl.1, hl.2.1, hl.2.2⟩)
  · exact prevCut_hi hT h hbk h' hbk' hR hR' ha hs hd hx hy hz hl

-- ============================================================
-- La inducción de línea
-- ============================================================

/-- La inducción de línea con `HPrevNew` entregada por línea, a partir de los invariantes de esa línea, de la
siguiente y de la anterior. -/
theorem lInvNewC_steps {φ : Cnf} (H4 : ∀ n : Nat, HStar4On φ (stepsM .on φ n (initM .on φ)))
    (H0 : LInvTop φ 1 (initM .on φ) → LineBk (initM .on φ) →
      LInvTop φ (1 + 1) (advanceM .on φ (initM .on φ)) → LineBk (advanceM .on φ (initM .on φ)) →
      HPrevNew φ (initM .on φ) 1)
    (Hs : ∀ n : Nat, LInvTop φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) →
      LInvTop φ ((n : Int) + 1 + 1) (advanceM .on φ (stepsM .on φ n (initM .on φ))) →
      LineBk (advanceM .on φ (stepsM .on φ n (initM .on φ))) →
      LInvTop φ ((n : Int) + 1 + 1 + 1) (advanceM .on φ (advanceM .on φ (stepsM .on φ n (initM .on φ)))) →
      LineBk (advanceM .on φ (advanceM .on φ (stepsM .on φ n (initM .on φ)))) →
      HPrevNew φ (advanceM .on φ (stepsM .on φ n (initM .on φ))) ((n : Int) + 1 + 1)) :
    ∀ n : Nat, LInvTop φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) ∧ LineBk (stepsM .on φ n (initM .on φ)) ∧
      HSender4On φ (stepsM .on φ n (initM .on φ)) ∧ HPrevCut φ (stepsM .on φ n (initM .on φ)) ((n : Int) + 1) := by
  intro n
  induction n with
  | zero =>
    have hl := lInvTop_init φ
    have hbk := lineBk_init φ
    have hs : HSender4On φ (initM .on φ) := by
      intro a ha b hb hab
      rw [initM_eq, List.mem_singleton] at ha hb
      exact absurd (by rw [ha, hb]) hab
    have hT : (1 : Int) ≤ 1 := by omega
    have hl' := lInvTop_advance hT hl (hTopOn_of_cross4 hT hl hbk (hCross4On_of_sender hT hl hbk hs))
    exact ⟨hl, hbk, hs, hPrevCut_init hl' (H0 hl hbk hl' (lineBk_advance hT hl hbk))⟩
  | succ n ih =>
    obtain ⟨hl, hbk, hs, hpc⟩ := ih
    have hT : (1 : Int) ≤ (n : Int) + 1 := by omega
    have hT' : (1 : Int) ≤ (n : Int) + 1 + 1 := by omega
    have hl' := lInvTop_advance hT hl (hTopOn_of_cross4 hT hl hbk (hCross4On_of_sender hT hl hbk hs))
    have hbk' := lineBk_advance hT hl hbk
    have h4 := H4 (n + 1)
    have hcast : ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 := by push_cast; omega
    rw [stepsM_succ] at h4 ⊢
    rw [hcast]
    have hs' : HSender4On φ (advanceM .on φ (stepsM .on φ n (initM .on φ))) := by
      intro a ha b hb hab d hsa hsb
      exact ⟨crossCut_of_prevCut hT hl hl' hbk' hpc ha hb hab hsa,
        crossCut_of_prevCut hT hl hl' hbk' hpc hb ha (Ne.symm hab) hsb, h4 a ha b hb hab d hsa hsb⟩
    have hl'' := lInvTop_advance hT' hl' (hTopOn_of_cross4 hT' hl' hbk' (hCross4On_of_sender hT' hl' hbk' hs'))
    have hbk'' := lineBk_advance hT' hl' hbk'
    exact ⟨hl', hbk', hs', hPrevCut_succ hT hl hl' hbk' hpc (Hs n hl hl' hbk' hl'' hbk'')⟩

/-- **Las hipótesis divididas**: la regla no prohíbe las bases muertas ni los triángulos con un nodo en la cima de la
entrada, el nacimiento bajo, y el cierre a nivel cuatro en cada join. -/
def HypsLo4On (φ : Cnf) : Prop :=
  (∀ n : Nat, HNoRule φ (stepsM .on φ n (initM .on φ)) ((n : Int) + 1)) ∧
  (∀ n : Nat, HPrevLo φ (stepsM .on φ n (initM .on φ)) ((n : Int) + 1)) ∧
  (∀ n : Nat, HStar4On φ (stepsM .on φ n (initM .on φ)))

/-- Una hipótesis por línea, leída en la línea siguiente como `advanceM` de la anterior. -/
theorem at_succ {φ : Cnf} {P : Line → Int → Prop} (H : ∀ n : Nat, P (stepsM .on φ n (initM .on φ)) ((n : Int) + 1))
    (n : Nat) : P (advanceM .on φ (stepsM .on φ n (initM .on φ))) ((n : Int) + 1 + 1) := by
  have h := H (n + 1)
  have hcast : ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 := by push_cast; omega
  rw [stepsM_succ, hcast] at h
  exact h

theorem at_succ2 {φ : Cnf} {P : Line → Int → Prop}
    (H : ∀ n : Nat, P (stepsM .on φ n (initM .on φ)) ((n : Int) + 1)) (n : Nat) :
    P (advanceM .on φ (advanceM .on φ (stepsM .on φ n (initM .on φ)))) ((n : Int) + 1 + 1 + 1) := by
  have h := at_succ (P := P) H (n + 1)
  have hcast : ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 := by push_cast; omega
  rw [stepsM_succ, hcast] at h
  exact h

theorem hypsPrev4On_of_lo {φ : Cnf} (H : HypsLo4On φ) : HypsPrev4On φ := by
  have hs := lInvNewC_steps H.2.2
    (fun hl hbk hl' hbk' => hPrevNew_of_lo (by omega) hl hbk hl' hbk' (H.1 0)
      (at_succ (P := HNoRule φ) H.1 0) (H.2.1 0))
    (fun n _ hl' hbk' hl'' hbk'' => hPrevNew_of_lo (by omega) hl' hbk' hl'' hbk''
      (at_succ (P := HNoRule φ) H.1 n) (at_succ2 (P := HNoRule φ) H.1 n) (at_succ (P := HPrevLo φ) H.2.1 n))
  exact ⟨fun n => (hs n).2.2.2, H.2.2⟩

/-- **Las hipótesis con el nacimiento dos líneas atrás.** -/
def HypsTwo4On (φ : Cnf) : Prop :=
  (∀ n : Nat, HNoRule φ (stepsM .on φ n (initM .on φ)) ((n : Int) + 1)) ∧
  (∀ n : Nat, HPrevLo2 φ (stepsM .on φ n (initM .on φ)) ((n : Int) + 1)) ∧
  (∀ n : Nat, HStar4On φ (stepsM .on φ n (initM .on φ)))

theorem hypsPrev4On_of_two {φ : Cnf} (H : HypsTwo4On φ) : HypsPrev4On φ := by
  have hs := lInvNewC_steps H.2.2
    (fun hl hbk hl' hbk' => hPrevNew_of_lo (by omega) hl hbk hl' hbk' (H.1 0) (at_succ (P := HNoRule φ) H.1 0)
      (by
        -- en la primera línea no hay nodos por debajo del paso 0
        intro a ha d hsd t x y z hd hx _ _ _
        exfalso
        obtain ⟨_, ia, _, _, _⟩ := arrTop_facts (by omega : (1 : Int) ≤ 1 + 1) hl' ha hsd
        have hxal : x ∈ (arrOn φ a d).alive := (ia.edges t x hd.2.2.2.2.2.2.2.2.1).2
        obtain ⟨n, hn, hnid⟩ := ia.docs x hxal
        have := ia.zero n hn
        rw [hnid] at this
        omega))
    (fun n hl hl' hbk' hl'' hbk'' => hPrevNew_of_lo (by omega) hl' hbk' hl'' hbk''
      (at_succ (P := HNoRule φ) H.1 n) (at_succ2 (P := HNoRule φ) H.1 n)
      (hPrevLo_of_two (by omega) hl (H.2.1 n)))
  exact ⟨fun n => (hs n).2.2.2, H.2.2⟩

end GPathB

namespace MachineOn

open GPathB Driver

/-- **El veredicto con `PrevCut` dividida**: la espina `:on` decide la satisfacibilidad si

* **`HNoRule`**: una llegada no prohíbe un triángulo de nodos viejos que su entrada no tuviera prohibido, si es una
  base muerta bajo una cima de la llegada o tiene un nodo en la cima de la entrada;
* **`HPrevLo`**: `PrevCut` para las bases de nacimiento cuyos nodos existían una línea más atrás;
* **`Star4At`**: la estrella de una cima de la unión fijada cierra a nivel cuatro.

Las bases heredadas (`prevCut_inherit`) y las que tienen un nodo en la cima de la línea anterior (`prevCut_hi`) están
demostradas. -/
theorem spineVerdictOn_iff_of_lo4 {φ : Cnf} (hbd : Bounded φ) (H : HypsLo4On φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_prev4 hbd (hypsPrev4On_of_lo H)

/-- **El veredicto con el nacimiento dos líneas atrás**: como `spineVerdictOn_iff_of_lo4`, con el nacimiento bajo en la
forma en que se mide: la base la cortan todas las entradas de dos líneas antes de la entrada que envía la llegada. -/
theorem spineVerdictOn_iff_of_two4 {φ : Cnf} (hbd : Bounded φ) (H : HypsTwo4On φ) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_prev4 hbd (hypsPrev4On_of_two H)

end MachineOn

end AbsSatBingo.Model
