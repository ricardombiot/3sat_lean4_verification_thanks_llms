-- lean/improves_bingo/AbsSatBingo/Model/LineInduction.lean
import AbsSatBingo.Model.DriverFam

/-!
# La inducción sobre los pasos de la máquina, bajo `PinFree`

La contabilidad de cada entrada de la línea (`EntOk`) y su paso por `advance`; el invariante de la línea (`LineInv`:
`LineOk`, `EntOk`, `TopExact`, claves únicas y `LTUf`) y su paso (`lineInv_advance`, con `PinFreeF` en la línea
siguiente); el caso base (`lineInv_init`); y el veredicto del lector bajo `PinFree` como única hipótesis.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin

namespace GPathB

open Driver Machine

/-- La contabilidad de un estado. -/
def BK (g : GPathB) : Prop := NodupIds g ∧ EdgesAlive g ∧ LinksStep g ∧ AboveZero g

/-- La contabilidad de una entrada: la del estado y los documentos de su cima con la clave. -/
def EntOk (kv : NodeId × GPathB) : Prop := BK kv.2 ∧ TopDocsId kv.2 kv.1

theorem topDocsId_of_shrinks {h g : GPathB} {k : NodeId} (hs : Shrinks h g) (hg : TopDocsId g k) : TopDocsId h k := by
  intro n hn h1
  obtain ⟨m, hm, hid, _, _⟩ := hs.1.nodes n hn
  rw [← hid]
  exact hg m hm (by rw [hid, ← hs.1.step]; exact h1)

theorem topDocsId_join {e g : GPathB} {k : NodeId} (he : TopDocsId e k) (hg : TopDocsId g k)
    (hcs : e.current_step = g.current_step) : TopDocsId (join e g) k := by
  intro n hn h1
  have hj : (join e g).current_step = e.current_step := rfl
  rcases List.mem_append.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    revert h1
    generalize g.node? m.id = x
    cases x with
    | none => intro h1; exact he m hm (by rw [← hj]; exact h1)
    | some m' => intro h1; exact he m hm (by rw [← hj]; exact h1)
  · exact hg n (List.mem_filter.mp hn).1 (by rw [← hcs, ← hj]; exact h1)

theorem bk_filterAll {g : GPathB} (h : BK g) (R : List NodeId) : BK (g.filterAll R) :=
  ⟨revPrims_filterAll revPrims_nodupIds _ _ h.1, revPrims_filterAll revPrims_edgesAlive _ _ h.2.1,
   revPrims_filterAll revPrims_linksStep _ _ h.2.2.1, revPrims_filterAll revPrims_aboveZero _ _ h.2.2.2⟩

/-- **La llegada conserva la contabilidad**, con la clave del destino. -/
theorem entOk_upFiltering {φ : Cnf} {T : Int} (hT : 0 ≤ T) {kv : NodeId × GPathB} (hok : StateOk T kv.1 kv.2)
    (he : EntOk kv)
    {d : NodeId} (hd : d ∈ sonsOfMap φ kv.1)
    (hv : (kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)).isValid = true) :
    EntOk (d, kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ)) := by
  obtain ⟨_, heq⟩ := upFiltering_eq_arrival (kv := kv) hv
  show EntOk (d, kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ))
  rw [heq]
  unfold arrival
  let f := kv.2.filterAll (reqOf φ d)
  have hbf : BK f := bk_filterAll he.1 _
  have hfs : f.current_step = T := (shrinks_filterAll _ _).1.step.trans hok.step
  have hds : d.step = f.current_step := by rw [hfs, sonsOfMap_step φ kv.1 d hd, hok.key]; omega
  have hb : Below f := below_of_shrinks (shrinks_filterAll _ _) hok.below
  have hnd := nodupIds_addNode (title := "") (forb := isProhibited φ) hbf.1 hb hds
  refine ⟨⟨revPrims_review revPrims_nodupIds _ hnd, revPrims_review revPrims_edgesAlive _ (edgesAlive_addNode hbf.2.1),
    revPrims_review revPrims_linksStep _ (linksStep_addNode hbf.2.2.1 hds),
    revPrims_review revPrims_aboveZero _ (aboveZero_addNode hbf.2.2.2 (by rw [hds, hfs]; exact hT))⟩, ?_⟩
  exact topDocsId_of_shrinks (shrinks_review _) (topDocsId_addNode hb)

/-- **El join de dos estados de la misma clave conserva la contabilidad.** -/
theorem entOk_doJoin {key : NodeId} {e g : GPathB} (he : EntOk (key, e)) (hg : EntOk (key, g)) :
    EntOk (key, doJoin e g) := by
  refine ⟨⟨nodupIds_doJoin he.1.1 hg.1.1, edgesAlive_doJoin he.1.2.1 hg.1.2.1, ?_, ?_⟩, ?_⟩
  · unfold doJoin; split
    · exact linksStep_join he.1.2.2.1 hg.1.2.2.1
    · exact he.1.2.2.1
  · unfold doJoin; split
    · exact aboveZero_join he.1.2.2.2 hg.1.2.2.2
    · exact he.1.2.2.2
  · show TopDocsId (doJoin e g) key
    unfold doJoin; split
    · rename_i hok
      unfold okJoin at hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      exact topDocsId_join he.2 hg.2 hok.1.1.1
    · exact he.2

theorem entOk_insert {line : Line} {key : NodeId} {g : GPathB} (hl : ∀ kv ∈ line, EntOk kv) (hg : EntOk (key, g)) :
    ∀ kv ∈ Driver.insert line key g, EntOk kv := by
  unfold Driver.insert
  split
  · rename_i key' e hfind
    have hkey : key' = key := by simpa using List.find?_some hfind
    subst hkey
    have he := hl _ (List.mem_of_find?_eq_some hfind)
    intro kv hkv
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    split
    · exact entOk_doJoin he hg
    · exact hl kv0 hkv0
  · intro kv hkv
    rcases List.mem_append.mp hkv with h | h
    · exact hl kv h
    · rw [List.mem_singleton] at h; subst h; exact hg

/-- **`advance` conserva la contabilidad de las entradas.** -/
theorem advance_entOk {φ : Cnf} {T : Int} (hT : 0 ≤ T) {line : Line} (hl : LineOk T line)
    (he : ∀ kv ∈ line, EntOk kv) :
    ∀ kv ∈ advance φ line, EntOk kv := by
  unfold advance
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, EntOk kv) line ?_ [] (fun _ h => absurd h List.not_mem_nil)
  intro next kv hkv hn
  unfold sendAll
  refine foldl_pres _ (fun next : Line => ∀ kv ∈ next, EntOk kv) _ ?_ next hn
  intro y d hd hy
  unfold sendTo
  dsimp only
  split
  · rename_i hv
    exact entOk_insert hy (entOk_upFiltering hT (hl kv hkv) (he kv hkv) hd hv)
  · exact hy

-- ============================================================
-- El invariante de la línea y su paso
-- ============================================================

/-- Los hijos de una clave del paso `T - 1`. -/
def SonT (φ : Cnf) (T : Int) (k d : NodeId) : Prop := d ∈ sonsOfMap φ k ∧ k.step = T - 1

/-- **El invariante de la línea** del paso `T`. -/
def LineInv (T : Int) (line : Line) : Prop :=
  LineOk T line ∧ (∀ kv ∈ line, EntOk kv ∧ TopExact kv.2) ∧ (line.map (·.1)).Nodup ∧ LTUf (· ∈ line) T

theorem upFiltering_of_valid {φ : Cnf} {kv : NodeId × GPathB} {d : NodeId}
    (hf : (kv.2.filterAll (reqOf φ d)).isValid = true) :
    kv.2.upFiltering (reqOf φ d) d "" (isProhibited φ) = arrival (reqOf φ) "" (isProhibited φ) kv d := by
  unfold upFiltering up; rw [if_pos hf]; rfl

/-- **El paso de la máquina**: con `PinFreeF` en la línea siguiente, el invariante pasa de un paso al siguiente. -/
theorem lineInv_advance {φ : Cnf} {T : Int} (hT : 1 ≤ T) {line : Line} (h : LineInv T line)
    (hpf : PinFreeF (reqOf φ) (· ∈ advance φ line) (T + 1)) : LineInv (T + 1) (advance φ line) := by
  obtain ⟨hl, hent, hnd, hih⟩ := h
  have hl' := lineOk_advance (φ := φ) hl
  have hent' := advance_entOk (φ := φ) (by omega) hl (fun kv h' => (hent kv h').1)
  have hsnd : ∀ kv, kv ∈ line → SenderOk T kv := by
    intro kv hkv
    obtain ⟨⟨hbk, htid⟩, htop⟩ := hent kv hkv
    exact ⟨(hl kv hkv).docs, hbk.1, (hl kv hkv).below, hbk.2.2.1, htop, (hl kv hkv).step, htid⟩
  have hson : ∀ k d, SonT φ T k d → d.step = T := by
    rintro k d ⟨hd, hk⟩; rw [sonsOfMap_step φ k d hd, hk]; omega
  have hcov : Covers (famOf (· ∈ advance φ line)) (Arrivals (reqOf φ) "" (isProhibited φ) (· ∈ line) (SonT φ T)) := by
    rintro g ⟨kv, hkv, rfl⟩
    refine covers_trans (advance_covers φ line kv hkv) (covers_of_sub ?_) _ rfl
    rintro a ⟨kv0, d, hkv0, hd, hv, rfl⟩
    exact ⟨kv0, d, hkv0, ⟨hd, (hl kv0 hkv0).key⟩, hv, rfl⟩
  have hupC : LineUpC (reqOf φ) "" (isProhibited φ) (· ∈ line) (· ∈ advance φ line) (SonT φ T) := by
    intro kv d hkv hd hf S hc
    rw [← upFiltering_of_valid hf] at hc
    exact mem_of_has (advance_lineUpC hl hkv hd.1 (isValid_of_carried hc) hc)
  have hkeys : ∀ a b, a ∈ advance φ line → b ∈ advance φ line → a.1 = b.1 → a = b :=
    fun a b ha hb hab => eq_of_nodup_keys (advance_nodup φ line) ha hb hab
  have hentc : ∀ kv, kv ∈ advance φ line → kv.2.current_step = T + 1 ∧ AliveDocs kv.2 ∧ TopDocsId kv.2 kv.1 :=
    fun kv hkv => ⟨(hl' kv hkv).step, (hl' kv hkv).docs, (hent' kv hkv).2⟩
  have htop := topExact_next (reqOf φ) "" (isProhibited φ) hT hsnd hson hcov hupC hpf hih hkeys hentc
  refine ⟨hl', fun kv hkv => ⟨hent' kv hkv, htop kv hkv⟩, advance_nodup φ line, ?_⟩
  exact ltuf_stepC (reqOf φ) "" (isProhibited φ) hT hsnd hson hcov hupC hpf hih (fun kv hkv => (hl' kv hkv).step)

-- ============================================================
-- El caso base
-- ============================================================

/-- **El caso base**: la línea inicial (la semilla) cumple el invariante; `LTUf` es trivial con un solo estado. -/
theorem lineInv_init (φ : Cnf) : LineInv 1 (init φ) := by
  have hl := (init_inv φ (fun _ => false)).1
  have hk := FinalTop.kInv_initSeed
  let d : NodeId := ⟨0, 0⟩
  let seed := initSeed d ""
  have hmem : (d, seed) ∈ init φ := by rw [init_eq]; exact List.mem_singleton_self _
  have hstep : seed.current_step = 1 := (hl _ hmem).step
  have htid : TopDocsId seed d := by
    have hup : seed = (GPathB.empty.addNode d "" (fun _ => false)).review := by
      show up GPathB.empty d "" (fun _ => false) = _
      unfold up; rw [if_pos (show GPathB.empty.isValid = true by rfl)]
    rw [hup]
    exact topDocsId_of_shrinks (shrinks_review _) (topDocsId_addNode (fun n hn => absurd hn List.not_mem_nil))
  refine ⟨hl, ?_, ?_, ?_⟩
  · rw [init_eq]
    intro kv hkv
    rw [List.mem_singleton] at hkv; subst hkv
    exact ⟨⟨⟨hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1⟩, htid⟩, hk.1⟩
  · rw [init_eq]; exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  · intro Q p hps hker
    have hcov : Covers (famOf (· ∈ init φ)) (· = seed) := by
      refine covers_of_sub ?_
      rintro g ⟨kv, hkv, rfl⟩
      rw [init_eq, List.mem_singleton] at hkv; subst hkv; rfl
    have hker' : FamKernel (· = seed) seed.current_step Q p p := by rw [hstep]; exact famKernel_covers hcov hker
    have hks := kernel_of_famKernel hker'
    refine ⟨(d, seed), hmem, ?_, hks⟩
    obtain ⟨V, R, hst, _, hr⟩ := hks
    obtain ⟨n, hn, hnid⟩ := (hl _ hmem).docs p (hst.alive (hst.dom hr).1)
    rw [← hnid]; exact (htid n hn (by rw [hnid, hstep]; exact hps)).symm

-- ============================================================
-- La máquina entera y el veredicto del lector
-- ============================================================

theorem steps_succ (φ : Cnf) : ∀ (n : Nat) (L : Line), steps φ (n + 1) L = advance φ (steps φ n L) := by
  intro n
  induction n with
  | zero => intro L; rfl
  | succ n ih => intro L; show steps φ (n + 1) (advance φ L) = advance φ (steps φ (n + 1) L); rw [ih]; rfl

/-- **La única hipótesis**: en cada línea de la máquina (tras cada paso), fijar por los requisitos de la fila de una
cima no la mata en la unión de la línea. -/
def HypsPin (φ : Cnf) : Prop :=
  ∀ n : Nat, PinFreeF (reqOf φ) (· ∈ steps φ (n + 1) (init φ)) ((n : Int) + 2)

theorem lineInv_steps {φ : Cnf} (H : HypsPin φ) : ∀ n : Nat, LineInv ((n : Int) + 1) (steps φ n (init φ)) := by
  intro n
  induction n with
  | zero => exact lineInv_init φ
  | succ n ih =>
    rw [steps_succ]
    have hpf := H n
    rw [steps_succ] at hpf
    have := lineInv_advance (φ := φ) (by omega) ih (by rw [show (n : Int) + 1 + 1 = (n : Int) + 2 by omega]; exact hpf)
    rw [show ((n + 1 : Nat) : Int) + 1 = (n : Int) + 1 + 1 by push_cast; omega]
    exact this

theorem vInv_visited_top {g₀ : GPathB} (hk : TopExact g₀) (hnd : NodupIds g₀) (hea : EdgesAlive g₀)
    (hd : AliveDocs g₀) : ∀ h, Visited g₀ h → FinalTop.VInv h := by
  intro h hvis
  induction hvis with
  | start =>
    show FinalTop.VInv (review { g₀ with dirty := true })
    rw [FinalTop.review_eq_filterAll]
    exact FinalTop.vInv_filterAll (h := { g₀ with dirty := true }) ⟨topExact_dirty hk true, hnd, hea, hd⟩ []
  | pin q _ ih => exact FinalTop.vInv_filterAll ih [q.id]

/-- **El veredicto del lector es la satisfacibilidad bajo `PinFree` como única hipótesis.** -/
theorem readerVerdict_iff_of_pinFree {φ : Cnf} (hbd : Bounded φ) (H : HypsPin φ) :
    readerVerdict φ = true ↔ Satisfiable φ := by
  apply Decode.readerVerdict_iff_of_noZombie hbd
  intro kv hkv h hvis
  have hpos := stepCount_pos φ
  have hinv := lineInv_steps H (stepCount φ - 1).toNat
  have hrun : run φ = steps φ (stepCount φ - 1).toNat (init φ) := rfl
  rw [← hrun, show ((stepCount φ - 1).toNat : Int) + 1 = stepCount φ by rw [Int.toNat_of_nonneg (by omega)]; omega]
    at hinv
  obtain ⟨hl, hent, _, _⟩ := hinv
  have hok := hl kv hkv
  obtain ⟨⟨hbk, _⟩, htop⟩ := hent kv hkv
  have hv := vInv_visited_top htop hbk.1 hbk.2.1 hok.docs h hvis
  have hcs : 2 ≤ kv.2.current_step := by rw [hok.step]; unfold stepCount; omega
  have hc := Final.cInv_visited hok.docs hbk.1 hok.below hbk.2.2.2 hcs h hvis
  exact fun hval => noZombie_of_topExact hv.1 (hc.2.2.2.2.2 hval) (by have := hc.2.2.2.2.1; omega) hval

end GPathB

end AbsSatBingo.Model
