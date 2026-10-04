-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnWeak.lean
import AbsSatBingo.Model.ForbidOnBlock

/-!
# Las llegadas solo deben ramas de la unión

`PhantomAt` pide, en el UP, que todo objeto de la llegada `k → d` sea de una rama **de esa llegada** (una solución
que elige `k` y `d`). La máquina no lo cumple siempre: en `scripts/cnf/chain6_cross.cnf` hay llegadas con triángulos
de nodos viejos que ninguna solución de la llegada recorre (`probe_exact3.jl`: `arr_t_out = 8`), y sin embargo las
entradas, los remitentes filtrados y el estado final salen exactos.

La inducción nunca usa tanto: una llegada solo se usa para formar la entrada `d` de la línea siguiente (sola o unida
a la otra llegada), y a la entrada le basta que sus objetos sean de ramas que eligen `d`. Los objetos con un nodo de
la fila nueva son siempre de ramas de la propia llegada (bajan a un padre); los de nodos viejos son los que pueden
deber su rama al otro remitente.

* **`snd3_upOnG`** (`ForbidOnHelly`): el UP conserva `Snd3` hacia cualquier familia que contenga las ramas de la
  llegada.
* **`PhantomAtW φ T`**: como `PhantomAt`, con la condición del UP hacia `SolE φ (T + 1) d`. Es más débil
  (`phantomAtW_of_phantomAt`, por `phantomFree_weaken`).
* Con ella valen el veredicto (`spineVerdictOn_iff_of_phantomW`), el lector (`reader_onW`) y la equivalencia
  (`machineExactW_iff`): `MachineExactW φ ↔ ∀ T ≥ 1, PhantomAtW φ T`, donde `MachineExactW` pide a las llegadas
  ramas de la entrada que van a formar.
* También la escalera de niveles (`hypsTriKeep_of_phantomAtW`, `hypsNodeKeep_of_phantomAtW`) y la equivalencia del
  lector (`readerExactW_iff`).
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin
open AbsSatBin.GraphPath.Model.GPathM (intRange shiftPid dedupPids mem_dedupPids)

variable {φ : Cnf}

/-- **Debilitar la familia de llegada**: si las ramas de `P0` que están en `P'` ya están en `P`, sin familias
fantasma hacia `P` da sin familias fantasma hacia `P' ⊇ P`. -/
theorem phantomFree_weaken {P0 P P' : Assign → Prop} {N σ : Int} (h : PhantomFree φ P0 P N σ)
    (hmono : ∀ a, P a → P' a) (hback : ∀ a, P0 a → P' a → P a) : PhantomFree φ P0 P' N σ := by
  intro R Tf h1 h2 h3 h4 h5 h6 h7 h8 h9 hanch
  obtain ⟨c2, c3⟩ := h R Tf h1 h2 h3 h4 h5 h6 h7 h8 h9
    (fun a s ha hs hst hp => hback a ha (hanch a s ha hs hst hp))
  refine ⟨fun y w hyw => ?_, fun x u w a1 a2 a3 n1 n2 n3 hn => ?_⟩
  · obtain ⟨a, ha, r⟩ := c2 y w hyw
    exact ⟨a, hmono a ha, r⟩
  · obtain ⟨a, ha, r⟩ := c3 x u w a1 a2 a3 n1 n2 n3 hn
    exact ⟨a, hmono a ha, r⟩

namespace GPathB

open Driver Machine MachineOn

/-- **`PhantomAtW φ T`**: como `PhantomAt`, pero en el UP los objetos de la llegada solo deben ser de ramas que
eligen `d` (las de la entrada que la llegada va a formar), no de ramas que además eligen `k`. -/
def PhantomAtW (φ : Cnf) (T : Int) : Prop :=
  ∀ k d : NodeId, k ∈ mapNodes φ (T - 1) → d ∈ sonsOfMap φ k →
    (∀ r ∈ reqOf φ d, PhantomFree φ (SolE φ T k) (fun a => SolE φ T k a ∧ selOfAssign φ a r.step = r) T r.step) ∧
    PhantomFree φ (fun a => SolE φ T k a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r) (SolE φ (T + 1) d) (T + 1) T

/-- La condición débil es más débil. -/
theorem phantomAtW_of_phantomAt {T : Int} (h : PhantomAt φ T) : PhantomAtW φ T := by
  intro k d hk hd
  obtain ⟨hF, hU⟩ := h k d hk hd
  exact ⟨hF, phantomFree_weaken hU (fun a ha => ha.1) (fun a h0 h1 => ⟨h1, h0.1.2⟩)⟩

/-- **El paso de la máquina bajo `PhantomAtW`.** -/
theorem lInvS3_advanceW (hb : Bounded φ) {T : Int} (hT : 1 ≤ T) {line : Line} (h : LInvS3 φ T line)
    (hcomp : CompLine φ T line) (hH : PhantomAtW φ T) : LInvS3 φ (T + 1) (advanceM .on φ line) := by
  have hlen := line_cases h.nodup h.keys
  have arr : ∀ kv ∈ line, ∀ d, SendsOn φ kv d →
      EntOn (T + 1) d (arrOn φ kv d) ∧ SInvB (arrOn φ kv d) ∧ NoDegT (arrOn φ kv d) ∧ DocsAlive (arrOn φ kv d) ∧
      Snd3 φ (SolE φ (T + 1) d) (arrOn φ kv d) ∧ d ∈ mapNodes φ T := by
    intro kv hkv d hs
    have hent := h.on kv hkv
    have hok := hent.1
    have hd : d.step = kv.2.current_step := by rw [sonsOfMap_step φ kv.1 d hs.1, hok.key, hok.step]; omega
    have hi := h.inv kv hkv
    have hcsY : (kv.2.filterAllOn (reqOf φ d)).current_step = T := by rw [step_filterAllOn]; exact hok.step
    have hdY : d.step = (kv.2.filterAllOn (reqOf φ d)).current_step := by rw [step_filterAllOn]; exact hd
    have hvY : (kv.2.filterAllOn (reqOf φ d)).isValid = true :=
      valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2
    have hiY := sInvB_filterAllOn hi (reqOf φ d)
    have hdaY := docsAlive_filterAllOn (h.docs kv hkv) (reqOf φ d) hvY
    have hdm : d ∈ mapNodes φ T := by
      have hk' : kv.1 ∈ mapNodes φ kv.1.step := by rw [hok.key]; exact h.keys kv hkv
      have := sonsOfMap_subset φ kv.1 hk' d hs.1
      rw [hok.key, show T - 1 + 1 = T by omega] at this
      exact this
    obtain ⟨hF, hU⟩ := hH kv.1 d (h.keys kv hkv) hs.1
    have sY := snd3_filter hi hent.2.1 (h.ndt kv hkv) hok.step hok.valid (reqOf_length_le_one φ d)
      (fun r hr => by have := reqOf_range hb r hr; rw [hd, hok.step] at this; exact this) hF
      (h.snd kv hkv) (hcomp kv hkv) hvY
    refine ⟨entOn_upFilteringOn hent hs.1 hs.2,
      sInvB_upOn hiY hdY (by rw [hd, hok.step]; omega),
      noDegT_upOn (noSelf_filterAllOn hent.2.1 _) (noDegT_filterAllOn hent.2.1 (h.ndt kv hkv) _),
      docsAlive_upOn hdaY hvY hs.2,
      snd3_upOnG (fun a ha => ha.1) hb hiY (noSelf_filterAllOn hent.2.1 _)
        (noDegT_filterAllOn hent.2.1 (h.ndt kv hkv) _) hcsY hT hvY hdaY hs.1 hdm hU sY (comp_filter (hcomp kv hkv)) hs.2,
      hdm⟩
  have ent : ∀ E ∈ advanceM .on φ line, SInvB E.2 ∧ NoDegT E.2 ∧ DocsAlive E.2 ∧
      Snd3 φ (SolE φ (T + 1) E.1) E.2 ∧ E.1 ∈ mapNodes φ T := by
    intro E hE
    rcases entry_shapeOn hlen h.nodup hE with ⟨kv, hkv, hs, he⟩ | ⟨a, ha, b, hb', _, hsa, hsb, he⟩
    · obtain ⟨_, hi, hn, hda, hp, hm⟩ := arr kv hkv E.1 hs
      rw [he]; exact ⟨hi, hn, hda, hp, hm⟩
    · obtain ⟨ea, ia, _, da, pa, hm⟩ := arr a ha E.1 hsa
      obtain ⟨eb, ib, _, db, pb, _⟩ := arr b hb' E.1 hsb
      have hcs : (arrOn φ a E.1).current_step = (arrOn φ b E.1).current_step := ea.1.step.trans eb.1.step.symm
      have hjoin : doJoinOn (arrOn φ a E.1) (arrOn φ b E.1) = joinOn (arrOn φ a E.1) (arrOn φ b E.1) := by
        unfold doJoinOn okJoin
        rw [if_pos (by simp [ea.1.step, eb.1.step, ea.1.mp, eb.1.mp, ea.1.valid, eb.1.valid])]
      rw [he, hjoin]
      exact ⟨sInvB_joinOn ia ib hcs, noDegT_joinOn ea.2.1 eb.2.1 ia.edges ib.edges, docsAlive_joinOn da db,
        snd3_joinOn pa pb ia.edges ib.edges, hm⟩
  exact ⟨lineOn_advance h.on, advanceOn_nodup φ line,
    fun E hE => by rw [show T + 1 - 1 = T by omega]; exact (ent E hE).2.2.2.2,
    fun E hE => (ent E hE).1, fun E hE => (ent E hE).2.1, fun E hE => (ent E hE).2.2.1,
    fun E hE => (ent E hE).2.2.2.1⟩

/-- **La inducción**: sin familias fantasma hasta la línea, el invariante de triángulos vale en ella. -/
theorem lInvS3_stepsW (hb : Bounded φ) : ∀ n : Nat, (∀ T : Int, 1 ≤ T → T ≤ n → PhantomAtW φ T) →
    LInvS3 φ ((n : Int) + 1) (stepsM .on φ n (initM .on φ)) := by
  intro n
  induction n with
  | zero => intro _; exact lInvS3_init φ
  | succ n ih =>
    intro hm
    have hl := ih (fun T h1 hT => hm T h1 (by push_cast; omega))
    rw [stepsM_succ]
    have := lInvS3_advanceW hb (by omega) hl (compLine_steps hb (lInvS_of_s3 hl)) (hm _ (by omega) (by push_cast; omega))
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

/-- **Sin familias fantasma, toda entrada de la máquina cumple los tres niveles.** -/
theorem levels_steps3W (hb : Bounded φ) (n : Nat) (hm : ∀ T : Int, 1 ≤ T → T ≤ n → PhantomAtW φ T) :
    ∀ kv ∈ stepsM .on φ n (initM .on φ), TopCT kv.2 ∧ TopEdge kv.2 ∧ TopTri kv.2 := by
  intro kv hkv
  have hl := lInvS3_stepsW hb n hm
  obtain ⟨h2, h3⟩ := levels_of_snd3 (hl.snd kv hkv) (compLine_steps hb (lInvS_of_s3 hl) kv hkv)
  exact ⟨topCT_of_topEdge h2, h2, h3⟩

/-- **La máquina es exacta, con las llegadas hacia la unión**: cada entrada y cada remitente filtrado válido tienen
sus parejas de vecinos y sus triángulos sin prohibir en ramas de sus soluciones; cada llegada válida, en ramas de las
soluciones de la **entrada que va a formar** (las que eligen `d`, vengan del remitente que vengan). -/
def MachineExactW (φ : Cnf) : Prop :=
  ∀ n : Nat, ∀ kv ∈ stepsM .on φ n (initM .on φ),
    Snd3 φ (SolE φ ((n : Int) + 1) kv.1) kv.2 ∧
    ∀ d ∈ sonsOfMap φ kv.1,
      ((kv.2.filterAllOn (reqOf φ d)).isValid = true →
        Snd3 φ (fun a => SolE φ ((n : Int) + 1) kv.1 a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r)
          (kv.2.filterAllOn (reqOf φ d))) ∧
      ((arrOn φ kv d).isValid = true →
        Snd3 φ (SolE φ ((n : Int) + 1 + 1) d) (arrOn φ kv d))

/-- **La equivalencia, con la condición débil.** El lado derecho solo habla de las soluciones de los prefijos de `φ`. -/
theorem machineExactW_iff (hb : Bounded φ) : MachineExactW φ ↔ ∀ T : Int, 1 ≤ T → PhantomAtW φ T := by
  constructor
  · -- exacta ⟹ sin familias fantasma
    intro hM T hT k d hk hd
    obtain ⟨n, rfl⟩ : ∃ n : Nat, T = (n : Int) + 1 := ⟨(T - 1).toNat, by omega⟩
    have hk' : k ∈ mapNodes φ n := by rw [show (n : Int) + 1 - 1 = n by omega] at hk; exact hk
    have base := lInvBase_steps φ n
    by_cases hent : ∃ kv ∈ stepsM .on φ n (initM .on φ), kv.1 = k
    · obtain ⟨kv, hkv, rfl⟩ := hent
      have hE := base.on kv hkv
      have hok := hE.1
      have hi := base.inv kv hkv
      have comp := compLine_base hb n kv hkv
      obtain ⟨_, hops⟩ := hM n kv hkv
      obtain ⟨hY, hA⟩ := hops d hd
      refine ⟨fun r hr => ?_, ?_⟩
      · have hreq : reqOf φ d = [r] := by
          have hlen := reqOf_length_le_one φ d
          cases hq : reqOf φ d with
          | nil => rw [hq] at hr; cases hr
          | cons x xs =>
            rw [hq] at hlen hr
            have hxs : xs = [] := by
              cases xs with
              | nil => rfl
              | cons _ _ => simp at hlen
            subst hxs
            rw [List.mem_singleton] at hr
            rw [hr]
        rw [hreq] at hY
        exact phantomFree_of_exact_filter hE.2.1 (base.ndt kv hkv) hok.step comp
          (fun hv => snd3_mono (hY hv) (fun a ha => ⟨ha.1, ha.2 r (List.mem_singleton_self _)⟩))
      · by_cases hvY : (kv.2.filterAllOn (reqOf φ d)).isValid = true
        · have hds : d.step = (n : Int) + 1 := by rw [sonsOfMap_step φ kv.1 d hd, hok.key]; omega
          exact phantomFree_of_exact_up (title := "") (sInvB_filterAllOn hi _) (noSelf_filterAllOn hE.2.1 _)
            (noDegT_filterAllOn hE.2.1 (base.ndt kv hkv) _) (tb_filterAllOn hE.2.2 _)
            ((step_filterAllOn kv.2 _).trans hok.step) (by omega) hvY hds (comp_filter comp)
            (fun a ha => ⟨ha.1, by have := ha.2; rw [show (n : Int) + 1 + 1 - 1 = (n : Int) + 1 by omega] at this; exact this⟩)
            hA
        · exact phantomFree_of_empty (fun a ha => hvY (isValid_of_carried (comp_filter comp a ha).1))
    · -- ninguna entrada con esa clave: ninguna solución del prefijo la elige
      have hempty : ∀ a, ¬ SolE φ ((n : Int) + 1) k a := by
        intro a ha
        have hn : (n : Int) < stepCount φ := by
          by_cases hc : stepCount φ ≤ (n : Int)
          · unfold mapNodes at hk'
            rw [if_neg (by omega), if_pos hc] at hk'
            exact absurd hk' List.not_mem_nil
          · omega
        obtain ⟨_, g, hf, _⟩ := comp_line hb a n hn ha.1
        have hkey : selOfAssign φ a n = k := by
          have := ha.2; rw [show (n : Int) + 1 - 1 = n by omega] at this; exact this
        exact hent ⟨_, List.mem_of_find?_eq_some hf, hkey⟩
      exact ⟨fun r _ => phantomFree_of_empty hempty, phantomFree_of_empty (fun a ha => hempty a ha.1)⟩
  · -- sin familias fantasma ⟹ exacta
    intro H n kv hkv
    have hl := lInvS3_stepsW hb n (fun T h1 _ => H T h1)
    refine ⟨hl.snd kv hkv, fun d hd => ?_⟩
    have hent := hl.on kv hkv
    have hok := hent.1
    have hi := hl.inv kv hkv
    have hcomp := compLine_steps hb (lInvS_of_s3 hl) kv hkv
    have hdk : d.step = kv.2.current_step := by rw [sonsOfMap_step φ kv.1 d hd, hok.key, hok.step]; omega
    have hdm : d ∈ mapNodes φ ((n : Int) + 1) := by
      have hk' : kv.1 ∈ mapNodes φ kv.1.step := by rw [hok.key]; exact hl.keys kv hkv
      have := sonsOfMap_subset φ kv.1 hk' d hd
      rw [hok.key, show (n : Int) + 1 - 1 + 1 = (n : Int) + 1 by omega] at this
      exact this
    obtain ⟨hF, hU⟩ := H ((n : Int) + 1) (by omega) kv.1 d (hl.keys kv hkv) hd
    have sY : (kv.2.filterAllOn (reqOf φ d)).isValid = true →
        Snd3 φ (fun a => SolE φ ((n : Int) + 1) kv.1 a ∧ ∀ r ∈ reqOf φ d, selOfAssign φ a r.step = r)
          (kv.2.filterAllOn (reqOf φ d)) := fun hvY =>
      snd3_filter hi hent.2.1 (hl.ndt kv hkv) hok.step hok.valid (reqOf_length_le_one φ d)
        (fun r hr => by have := reqOf_range hb r hr; rw [hdk, hok.step] at this; exact this) hF
        (hl.snd kv hkv) hcomp hvY
    refine ⟨sY, fun hvA => ?_⟩
    have hvY : (kv.2.filterAllOn (reqOf φ d)).isValid = true :=
      valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hvA
    exact snd3_upOnG (fun a ha => ha.1) hb (sInvB_filterAllOn hi _) (noSelf_filterAllOn hent.2.1 _)
      (noDegT_filterAllOn hent.2.1 (hl.ndt kv hkv) _) ((step_filterAllOn kv.2 _).trans hok.step) (by omega) hvY
      (docsAlive_filterAllOn (hl.docs kv hkv) (reqOf φ d) hvY) hd hdm hU (sY hvY) (comp_filter hcomp) hvA


/-- **Con la condición débil, el filtro de cada llegada conserva `TopTri`.** -/
theorem hypsTriKeep_of_phantomAtW (hb : Bounded φ) (H : ∀ T : Int, 1 ≤ T → PhantomAtW φ T) : HypsTriKeep φ := by
  intro n kv hkv d hs _ _
  obtain ⟨hsY, _⟩ := ((machineExactW_iff hb).mpr H n kv hkv).2 d hs.1
  have hS := hsY (valid_of_upOn (d := d) (title := "") (forb := isProhibited φ) hs.2)
  have comp := comp_filter (reqs := reqOf φ d) (compLine_base hb n kv hkv)
  intro t _ hts u w htu htw huw ntu ntw nuw hn
  obtain ⟨a, hP, h1, h2, h3⟩ := hS.2 t u w htu htw huw ntu ntw nuw hn
  exact ⟨_, comp a hP, by rw [← hts]; exact h1, h2, h3⟩

/-- Y con la escalera, también las aristas y los nodos de cima: las hipótesis de niveles son consecuencias. -/
theorem hypsNodeKeep_of_phantomAtW (hb : Bounded φ) (H : ∀ T : Int, 1 ≤ T → PhantomAtW φ T) : HypsNodeKeep φ :=
  hypsNodeKeep_of_edgeKeep (hypsEdgeKeep_of_triKeep (hypsTriKeep_of_phantomAtW hb H))

end GPathB

namespace MachineOn

open GPathB Driver Machine

/-- **La espina `:on` decide toda fórmula que cumple la condición débil.** -/
theorem spineVerdictOn_iff_of_phantomW (hbd : Bounded φ) (H : ∀ T : Int, 1 ≤ T → PhantomAtW φ T) :
    SpineVerdictOn φ ↔ Satisfiable φ :=
  spineVerdictOn_iff_of_finalTopCT hbd
    (fun kv hkv => (levels_steps3W hbd (stepCount φ - 1).toNat (fun T h1 _ => H T h1) kv hkv).1)

/-- **El lector no se atasca.** En la máquina `:on`, sin familias fantasma en sus líneas (`PhantomAtW`) ni en la
lectura (`HRead`), cualquier lectura de un estado final —cualquier sucesión de elecciones de nodos vivos, revisando
tras cada una— deja un estado válido que lleva la rama de una asignación que satisface `φ` y coincide con todas las
elecciones. -/
theorem reader_onW (hbd : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T)
    (HR : ∀ k, HRead φ (stepCount φ) (SolE φ (stepCount φ) k)) {kv : NodeId × GPathB} (hkv : kv ∈ runM .on φ)
    {R : List NodeId} {g' : GPathB} (hr : Reading kv.2 R g') :
    g'.isValid = true ∧ ∃ a, Sat a φ ∧ (∀ r ∈ R, selOfAssign φ a r.step = r) ∧ CT g' (pidOfAssign φ a) := by
  have hpos := stepCount_pos φ
  have hn : (((stepCount φ - 1).toNat : Nat) : Int) + 1 = stepCount φ := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  have hl := lInvS3_stepsW hbd (stepCount φ - 1).toNat (fun T h1 _ => HA T h1)
  have hcomp := compLine_steps hbd (lInvS_of_s3 hl)
  rw [hn] at hl hcomp
  have hkv' : kv ∈ stepsM .on φ (stepCount φ - 1).toNat (initM .on φ) := hkv
  have hent := hl.on kv hkv'
  have h0 : RInv φ (stepCount φ) (Pinned φ (SolE φ (stepCount φ) kv.1) []) kv.2 :=
    rInv_congr (P := SolE φ (stepCount φ) kv.1)
      ⟨hl.inv kv hkv', hent.2.1, hl.ndt kv hkv', hent.1.step, hent.1.valid, hl.snd kv hkv', hcomp kv hkv'⟩
      (fun a => ⟨fun ha => ⟨ha, fun r hr => absurd hr List.not_mem_nil⟩, fun ha => ha.1⟩)
  have hfin := reading_inv (HR kv.1) hr [] (fun x hx => absurd hx List.not_mem_nil) h0
  rw [List.nil_append] at hfin
  refine ⟨hfin.valid, ?_⟩
  obtain ⟨q, hq, _⟩ := exists_alive_at hfin.valid (k := 0) (Int.le_refl 0) (by rw [hfin.step]; exact hpos)
  obtain ⟨a, ha, _, _⟩ := hfin.snd.1 q q (adj_refl _ _ hq)
  exact ⟨a, sat_of_validUpTo ha.1.1, ha.2, hfin.comp a ha⟩

/-- **El lector es exacto exactamente cuando la lectura no tiene familias fantasma**, con la condición débil en las líneas. -/
theorem readerExactW_iff (hb : Bounded φ) (HA : ∀ T : Int, 1 ≤ T → PhantomAtW φ T) :
    ReaderExact φ ↔ ∀ k, HRead φ (stepCount φ) (SolE φ (stepCount φ) k) := by
  have hpos := stepCount_pos φ
  have hn : (((stepCount φ - 1).toNat : Nat) : Int) + 1 = stepCount φ := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  have base := lInvBase_steps φ (stepCount φ - 1).toNat
  have hcomp := compLine_base hb (stepCount φ - 1).toNat
  rw [hn] at base hcomp
  -- el invariante del estado final, con su exactitud dada
  have start : ∀ kv ∈ runM .on φ, Snd3 φ (Pinned φ (SolE φ (stepCount φ) kv.1) []) kv.2 →
      RInv φ (stepCount φ) (Pinned φ (SolE φ (stepCount φ) kv.1) []) kv.2 := by
    intro kv hkv hs
    have hent := base.on kv hkv
    exact ⟨base.inv kv hkv, hent.2.1, base.ndt kv hkv, hent.1.step, hent.1.valid, hs,
      fun a ha => hcomp kv hkv a ha.1⟩
  constructor
  · intro hRE k R r hR hr1 hrT
    by_cases hent : ∃ kv ∈ runM .on φ, kv.1 = k
    · obtain ⟨kv, hkv, rfl⟩ := hent
      have h0 := start kv hkv (hRE kv hkv [] kv.2 (Reading.nil _))
      rcases reach (T := stepCount φ) (hRE kv hkv) R hR [] kv.2 (Reading.nil _) h0 with hemp | ⟨g, hread, hinv⟩
      · rw [List.nil_append] at hemp
        exact phantomFree_of_empty hemp
      · rw [List.nil_append] at hread hinv
        refine phantomFree_of_exact_filter hinv.ns hinv.ndt hinv.step hinv.comp (fun hv => ?_)
        -- el estado filtrado es válido: hay un nodo vivo del color, y la lectura sigue
        have hcsY : (g.filterAllOn [r]).current_step = stepCount φ := (step_filterAllOn g _).trans hinv.step
        obtain ⟨q, hqY, hqs⟩ := exists_alive_at hv (k := r.step) (by omega) (by rw [hcsY]; exact hrT)
        have hs1 : Sub (g.filterAllOn [r]) ([r].foldl filterRequire g) := (shrinks_reviewOn _).1
        have hqid : q.id = r :=
          pinned_foldl [r] g hinv.inv.docs (isValid_of_sub hs1 hv) q (hs1.alive q hqY) (List.mem_singleton_self _) hqs
        have hqg : q ∈ g.alive := (shrinks_filterAllOn g [r]).1.alive q hqY
        have hread' := reading_snoc hread hqg (by rw [hqid]; exact hr1)
        rw [hqid] at hread'
        exact snd3_mono (hRE kv hkv _ _ hread') (fun a ha =>
          ⟨⟨ha.1, fun x hx => ha.2 x (List.mem_append_left _ hx)⟩,
            ha.2 r (List.mem_append_right _ (List.mem_singleton_self _))⟩)
    · -- ninguna entrada final con esa clave: ninguna solución la elige
      refine phantomFree_of_empty (fun a ha => hent ?_)
      have hv : ValidUpTo φ a (((stepCount φ - 1).toNat : Nat) + 1 : Int) := by rw [hn]; exact ha.1.1
      obtain ⟨_, g, hf, _⟩ := comp_line hb a (stepCount φ - 1).toNat (by omega) hv
      refine ⟨_, List.mem_of_find?_eq_some hf, ?_⟩
      have e : (((stepCount φ - 1).toNat : Nat) : Int) = stepCount φ - 1 := by omega
      show selOfAssign φ a ((stepCount φ - 1).toNat : Nat) = k
      rw [e]; exact ha.1.2
  · intro HR kv hkv R g' hr
    have hl := lInvS3_stepsW hb (stepCount φ - 1).toNat (fun T h1 _ => HA T h1)
    rw [hn] at hl
    have h0 := start kv hkv (snd3_mono (hl.snd kv hkv) (fun a ha => ⟨ha, fun r hr => absurd hr List.not_mem_nil⟩))
    have hfin := reading_inv (HR kv.1) hr [] (fun x hx => absurd hx List.not_mem_nil) h0
    rw [List.nil_append] at hfin
    exact hfin.snd

end MachineOn

end AbsSatBingo.Model
