-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnPrefix.lean
import AbsSatBingo.Model.ForbidOnChain4X

/-!
# Las líneas solo ven el prefijo

La línea `T` de la máquina solo mira los pasos por debajo de `T + 1`. Por debajo del primer paso de la cláusula `j`,
la fórmula `φ` y su prefijo `prefixCnf φ j` (las `j` primeras cláusulas, las mismas variables) eligen los mismos nodos,
tienen las mismas ventanas y prohíben lo mismo. Entonces la condición de la línea para `φ` es la del prefijo:

* `sel_prefix`, `pid_prefix`, `isProhibited_prefix`, `validUpTo_prefix`, `solE_prefix`, `reqOf_prefix`,
  `mapNodes_prefix`, `sonsOfMap_prefix`;
* `phantomFree_transfer`: sin familias fantasma para el prefijo da lo mismo para `φ`, con las mismas familias;
* **`phantomAt_of_prefix`**: `PhantomAt (prefixCnf φ j) T → PhantomAt φ T` si `T + 1` no pasa del primer paso de la
  cláusula `j`.

Así las líneas de una cadena larga se reducen a las de sus prefijos, que son cadenas más cortas, salvo las de la
última cláusula.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

variable {φ : Cnf}

/-- Las `j` primeras cláusulas, con las mismas variables. -/
def prefixCnf (φ : Cnf) (j : Nat) : Cnf := ⟨φ.nVars, φ.clauses.take j⟩

section Prefix

variable {j : Nat}

theorem midFusion_prefix : midFusion (prefixCnf φ j) = midFusion φ := rfl

theorem fusionTop_prefix_le : fusionTop (prefixCnf φ j) ≤ fusionTop φ := by
  simp only [fusionTop, prefixCnf, List.length_take]; omega

theorem clauseOf_prefix {k : Int} (hlo : midFusion φ < k) (hk : k < fusionTop (prefixCnf φ j)) :
    clauseOf (prefixCnf φ j) k = clauseOf φ k := by
  have hidx : ((k - midFusion φ - 1) / 3).toNat < j := by
    simp only [fusionTop, prefixCnf, List.length_take, midFusion] at hk hlo ⊢; omega
  simp only [clauseOf, prefixCnf, midFusion]
  rw [List.getElem?_take_of_lt (by simpa [midFusion] using hidx)]

theorem sel_prefix {k : Int} (hk : k < fusionTop (prefixCnf φ j)) (a : Assign) :
    selOfAssign (prefixCnf φ j) a k = selOfAssign φ a k := by
  have hle := fusionTop_prefix_le (φ := φ) (j := j)
  unfold selOfAssign
  rw [midFusion_prefix]
  by_cases h0 : k ≤ 0
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0]
  by_cases h1 : k < midFusion φ
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  by_cases h2 : k = midFusion φ
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2, if_neg (by omega), if_neg (by omega),
    clauseOf_prefix (by omega) hk]

theorem pid_prefix {k : Int} (hk : k < fusionTop (prefixCnf φ j)) (a : Assign) :
    pidOfAssign (prefixCnf φ j) a k = pidOfAssign φ a k := by
  unfold pidOfAssign
  rw [sel_prefix hk, sel_prefix (by omega), sel_prefix (by omega)]

theorem isProhibited_prefix {w : PathNodeId} (hk : w.id.step < fusionTop (prefixCnf φ j)) :
    isProhibited (prefixCnf φ j) w = isProhibited φ w := by
  have hle := fusionTop_prefix_le (φ := φ) (j := j)
  unfold isProhibited isL3
  rw [midFusion_prefix]
  have e1 : decide (w.id.step < fusionTop (prefixCnf φ j)) = true := decide_eq_true hk
  have e2 : decide (w.id.step < fusionTop φ) = true := decide_eq_true (by omega)
  rw [e1, e2]

theorem validUpTo_prefix {T : Int} (hT : T ≤ fusionTop (prefixCnf φ j)) (a : Assign) :
    ValidUpTo (prefixCnf φ j) a T ↔ ValidUpTo φ a T := by
  constructor
  · intro h q hq
    have := h q hq
    rw [pid_prefix (by omega), isProhibited_prefix (by rw [pid_id, selOfAssign_step]; omega)] at this
    exact this
  · intro h q hq
    rw [pid_prefix (by omega), isProhibited_prefix (by rw [pid_id, selOfAssign_step]; omega)]
    exact h q hq

theorem solE_prefix {T : Int} (hT : T ≤ fusionTop (prefixCnf φ j)) (k : NodeId) (a : Assign) :
    SolE (prefixCnf φ j) T k a ↔ SolE φ T k a := by
  unfold SolE
  rw [validUpTo_prefix hT, sel_prefix (by omega)]

theorem reqOf_prefix {d : NodeId} (hd : d.step < fusionTop (prefixCnf φ j)) :
    reqOf (prefixCnf φ j) d = reqOf φ d := by
  have hle := fusionTop_prefix_le (φ := φ) (j := j)
  unfold reqOf
  rw [midFusion_prefix]
  by_cases h0 : d.step ≤ 0
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0]
  by_cases h1 : d.step < midFusion φ
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  by_cases h2 : d.step = midFusion φ
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2, if_neg (by omega), if_neg (by omega), clauseOf_prefix (by omega) hd]

theorem mapNodes_prefix {k : Int} (hk : k < fusionTop (prefixCnf φ j)) :
    mapNodes (prefixCnf φ j) k = mapNodes φ k := by
  have hle := fusionTop_prefix_le (φ := φ) (j := j)
  have hs1 : k < stepCount (prefixCnf φ j) := by
    simp only [stepCount, fusionTop] at hk ⊢; omega
  have hs2 : k < stepCount φ := by simp only [stepCount, fusionTop] at hle hk ⊢; omega
  unfold mapNodes
  rw [midFusion_prefix, if_neg (by omega : ¬ stepCount (prefixCnf φ j) ≤ k), if_neg (by omega : ¬ stepCount φ ≤ k),
    if_neg (by omega : ¬ fusionTop (prefixCnf φ j) ≤ k), if_neg (by omega : ¬ fusionTop φ ≤ k)]

theorem sonsOfMap_prefix {d : NodeId} (hd : d.step + 1 < fusionTop (prefixCnf φ j)) :
    sonsOfMap (prefixCnf φ j) d = sonsOfMap φ d := by
  unfold sonsOfMap
  rw [midFusion_prefix, mapNodes_prefix hd]

end Prefix

namespace GPathB

open Driver Machine MachineOn

variable {ψ : Cnf} {P0 P P0' P' : Assign → Prop} {N σ : Int}

/-- **Cambiar de fórmula**: si las dos eligen las mismas ventanas por debajo de `N`, sin familias fantasma pasa de una
a otra. -/
theorem phantomFree_transfer (hpid : ∀ a k, k < N → pidOfAssign ψ a k = pidOfAssign φ a k) (hσN : σ < N)
    (h : PhantomFree ψ P0 P N σ) : PhantomFree φ P0 P N σ := by
  intro R Tf hrefl hsymm hsw23 hsw12 hsteps hpair htrio hb2 hb3 hanch
  have st : ∀ {y w}, R y w → y.id.step < N := fun hyw => (hsteps _ _ hyw).2
  have st' : ∀ {y w}, R y w → w.id.step < N := fun hyw => (hsteps _ _ (hsymm _ _ hyw)).2
  obtain ⟨c2, c3⟩ := h R Tf hrefl hsymm hsw23 hsw12 hsteps hpair htrio
    (fun y w hyw => by
      obtain ⟨a, ha, h1, h2⟩ := hb2 y w hyw
      exact ⟨a, ha, by rw [hpid a _ (st hyw)]; exact h1, by rw [hpid a _ (st' hyw)]; exact h2⟩)
    (fun x u w hxu hxw huw n1 n2 n3 hn => by
      obtain ⟨a, ha, h1, h2, h3⟩ := hb3 x u w hxu hxw huw n1 n2 n3 hn
      exact ⟨a, ha, by rw [hpid a _ (st hxu)]; exact h1, by rw [hpid a _ (st' hxu)]; exact h2,
        by rw [hpid a _ (st' hxw)]; exact h3⟩)
    (fun a s ha hs hst hp => hanch a s ha hs hst (by rw [← hpid a σ hσN]; exact hp))
  refine ⟨fun y w hyw => ?_, fun x u w hxu hxw huw n1 n2 n3 hn => ?_⟩
  · obtain ⟨a, ha, h1, h2⟩ := c2 y w hyw
    exact ⟨a, ha, by rw [← hpid a _ (st hyw)]; exact h1, by rw [← hpid a _ (st' hyw)]; exact h2⟩
  · obtain ⟨a, ha, h1, h2, h3⟩ := c3 x u w hxu hxw huw n1 n2 n3 hn
    exact ⟨a, ha, by rw [← hpid a _ (st hxu)]; exact h1, by rw [← hpid a _ (st' hxu)]; exact h2,
      by rw [← hpid a _ (st' hxw)]; exact h3⟩

/-- Cambiar las familias por otras con las mismas ramas. -/
theorem phantomFree_congr (h : PhantomFree φ P0 P N σ) (h0 : ∀ a, P0 a ↔ P0' a) (h1 : ∀ a, P a ↔ P' a) :
    PhantomFree φ P0' P' N σ := by
  have e0 : P0 = P0' := funext fun a => propext (h0 a)
  have e1 : P = P' := funext fun a => propext (h1 a)
  subst e0; subst e1; exact h

/-- **Las líneas solo ven el prefijo**: la condición fuerte de la línea `T` para el prefijo da la de `φ`, si `T + 1` no
pasa del primer paso de la cláusula `j`. -/
theorem phantomAt_of_prefix (hb : Bounded φ) {j : Nat} {T : Int} (hT : T + 1 ≤ fusionTop (prefixCnf φ j))
    (h : PhantomAt (prefixCnf φ j) T) : PhantomAt φ T := by
  intro k d hk hd
  have hds : d.step = T := by
    have := sonsOfMap_step φ k d hd
    have hks := mapNodes_step φ (T - 1) k hk
    omega
  have hks := mapNodes_step φ (T - 1) k hk
  have hk' : k ∈ mapNodes (prefixCnf φ j) (T - 1) := by rw [mapNodes_prefix (by omega)]; exact hk
  have hd' : d ∈ sonsOfMap (prefixCnf φ j) k := by rw [sonsOfMap_prefix (by omega)]; exact hd
  obtain ⟨hF, hU⟩ := h k d hk' hd'
  have hreq : reqOf (prefixCnf φ j) d = reqOf φ d := reqOf_prefix (by omega)
  have hpid : ∀ (a : Assign) (q : Int), q < T + 1 → pidOfAssign (prefixCnf φ j) a q = pidOfAssign φ a q :=
    fun a q hq => pid_prefix (by omega) a
  refine ⟨fun r hr => ?_, ?_⟩
  · have hr' : r ∈ reqOf (prefixCnf φ j) d := by rw [hreq]; exact hr
    have hrT : r.step < T := by
      have := (reqOf_range hb r hr).2
      omega
    refine phantomFree_transfer (fun a q hq => hpid a q (by omega)) hrT
      (phantomFree_congr (hF r hr') (fun a => solE_prefix (by omega) k a) (fun a => ?_))
    rw [solE_prefix (by omega) k a, sel_prefix (by omega) a]
  · refine phantomFree_transfer hpid (by omega) (phantomFree_congr hU (fun a => ?_) (fun a => ?_))
    · rw [solE_prefix (by omega) k a, hreq]
      exact and_congr_right fun _ => forall_congr' fun r => imp_congr_right fun hr =>
        by rw [sel_prefix (by have := (reqOf_range hb r hr).2; omega) a]
    · rw [solE_prefix hT d a, sel_prefix (by omega) a]

end GPathB

end AbsSatBingo.Model
