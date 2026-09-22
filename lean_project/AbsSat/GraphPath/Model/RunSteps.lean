-- lean_project/AbsSat/GraphPath/Model/RunSteps.lean
import AbsSat.GraphPath.Model.RunInhabited

/-!
# Reducing the send step of the construction route

`RunInhabited` leaves one step: pinning and reviewing keeps every entry towards the literal steps on a
path (`FilterSoundAt`). This module takes it apart, as v144 did for full exactness:

* **`soundAt_of_embedded`**, **`soundAt_review`** (no hypothesis) — the invariant moves across a double
  embedding, and the review with no pin keeps it (no path is lost).
* **`filterSoundAt_of_steps`** — a send is its steps (`WeakPairs.full_seq`), so the invariant follows from
  one weak requirement at a time (`WeakStepSoundAt`) and one pin at a time (`PinStepSoundAt`).
* **`pinStep_of_pairs`** — for one pin, the entries towards the pinned step are proved (the node level):
  what is left is **`PinPairSoundAt`**, the entries towards the *other* literal steps.
-/

namespace AbsSat.GraphPath.Model.RunSteps

open AbsSat.Utils.Alias
open AbsSat.Cnf
open AbsSat.GraphMap.CnfMap
open AbsSat.GraphMap.CnfMapImproves (weakReqOfCnf)
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.AggressiveReview
open AbsSat.GraphPath.Model.PureDriverImproves (filterWeak filterWeakAll)
open AbsSat.GraphPath.Model.ReaderAgg
open AbsSat.GraphPath.Model.EmbeddedSupport (Mem Embedded)
open AbsSat.GraphPath.Model.ReaderAggRun (MInv)
open AbsSat.GraphPath.Model.BranchCompat (pinOneByOne)
open AbsSat.GraphPath.Model.BranchRun (isValid_of_embedded)
open AbsSat.GraphPath.Model.Exactness (Realizes)
open AbsSat.GraphPath.Model.RunInhabited (SoundAt LitStep FilterSoundAt soundAt_review reqOfCnf_lit)
open AbsSat.GraphPath.Model.WeakPairs (weakOneByOne full_seq readable_weakOneByOne readableAgg_weakStep
  pruned_weakOneByOne)
open AbsSat.GraphPath.Model.SeqPin (chainSound_of_embedded pruned_pinOneByOne)

-- ============================================================
-- Moving the invariant
-- ============================================================

theorem soundAt_of_embedded (L : Int → Prop) {A S : GPathM} (eAS : Embedded A S) (eSA : Embedded S A)
    (adA : AdjacentOwners.Adj A) (hsA : Sons.SMP A) (ht : SoundAt L S) : SoundAt L A := by
  intro x n hx hx0 hx1 q hq0 hq1 hL hqn
  obtain ⟨n', hn', ho, _⟩ := eAS.node x n hx
  have hqm : Mem A q := by
    have hg := adA.ctx.ownGow x n hx q hqn hq0 hq1
    obtain ⟨m, hm, hid⟩ := adA.ctx.gn q hg
    exact ⟨m, by rw [← hid]; exact node?_of_mem adA.rc.nodup m hm⟩
  obtain ⟨sel, hsc, h1, h2⟩ := ht x n' hn' hx0 (by rw [← eAS.step]; exact hx1) q hq0
    (by rw [← eAS.step]; exact hq1) hL (ho q hqn hqm)
  exact ⟨sel, chainSound_of_embedded eSA hsA sel hsc, h1, h2⟩

-- ============================================================
-- The send, one step at a time
-- ============================================================

variable (φ : Cnf)

/-- One pin at a literal step, on a valid reader's state, keeps the invariant. -/
def PinStepSoundAt : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → SoundAt (LitStep φ) g →
    ∀ r : NodeId, LitStep φ r.step → isValid (filterAllAgg g [r]) = true →
      SoundAt (LitStep φ) (filterAllAgg g [r])

/-- One weak requirement, on a valid reader's state, keeps the invariant. -/
def WeakStepSoundAt : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → SoundAt (LitStep φ) g →
    ∀ e : Int × List NodeId, isValid (filterAllAgg (filterWeak g e) []) = true →
      SoundAt (LitStep φ) (filterAllAgg (filterWeak g e) [])

theorem soundAt_pinOneByOne (hP : PinStepSoundAt φ) : ∀ (rs : List NodeId) (h : GPathM),
    (∀ r ∈ rs, LitStep φ r.step) → ReadableAgg h → isValid h = true → SoundAt (LitStep φ) h →
      isValid (pinOneByOne h rs) = true → SoundAt (LitStep φ) (pinOneByOne h rs) := by
  intro rs
  induction rs with
  | nil => intro h _ _ _ ht _; exact ht
  | cons q rest ih =>
    intro h hl hR hv ht hvS
    have hR' := ReadableAgg_filterAllAgg h hR [q]
    have hv' : isValid (filterAllAgg h [q]) = true :=
      isValid_of_embedded (Hereditary.embedded_of_pruned_self (pruned_pinOneByOne rest _)
        (RCtx_of_readableAgg _ hR').nodup) hvS
    exact ih _ (fun r hr => hl r (List.mem_cons_of_mem _ hr)) hR' hv'
      (hP h hR hv ht q (hl q List.mem_cons_self) hv') hvS

theorem soundAt_weakOneByOne (hW : WeakStepSoundAt φ) : ∀ (ws : List (Int × List NodeId)) (h : GPathM),
    ReadableAgg h → isValid h = true → SoundAt (LitStep φ) h → isValid (weakOneByOne h ws) = true →
      SoundAt (LitStep φ) (weakOneByOne h ws) := by
  intro ws
  induction ws with
  | nil => intro h _ _ ht _; exact ht
  | cons e rest ih =>
    intro h hR hv ht hvS
    have hR' := readableAgg_weakStep h (RCtx_of_readableAgg h hR) e
    have hv' : isValid (filterAllAgg (filterWeak h e) []) = true :=
      isValid_of_embedded (Hereditary.embedded_of_pruned_self (pruned_weakOneByOne rest _)
        (RCtx_of_readableAgg _ hR').nodup) hvS
    exact ih _ hR' hv' (hW h hR hv ht e hv') hvS

/-- **The send step from its single steps.** -/
theorem filterSoundAt_of_steps (hwf : WF φ) (hW : WeakStepSoundAt φ) (hP : PinStepSoundAt φ) :
    FilterSoundAt φ := by
  intro k kv _ hm ht d _ hv
  have hlit : ∀ r ∈ reqOfCnf φ d, LitStep φ r.step := fun r hr => Or.inl (reqOfCnf_lit φ hwf d r hr)
  generalize weakReqOfCnf φ d = ws at hv ⊢
  generalize reqOfCnf φ d = rq at hv hlit ⊢
  obtain ⟨hvT, eAT, eTA, adA, hsA⟩ := full_seq kv.2 hm.rctx hm.smp hm.pms hm.sn ws rq hv
  have hR0 : ReadableAgg (filterAllAgg kv.2 []) := ⟨kv.2, [], hm.rctx, rfl⟩
  have hR1 := readable_weakOneByOne ws _ hR0
  have hv1 : isValid (weakOneByOne (filterAllAgg kv.2 []) ws) = true :=
    isValid_of_embedded (Hereditary.embedded_of_pruned_self (pruned_pinOneByOne rq _)
      (RCtx_of_readableAgg _ hR1).nodup) hvT
  have hv0 : isValid (filterAllAgg kv.2 []) = true :=
    isValid_of_embedded (Hereditary.embedded_of_pruned_self (pruned_weakOneByOne ws _)
      (RCtx_of_readableAgg _ hR0).nodup) hv1
  have ht0 := soundAt_review _ kv.2 hm.rctx.nodup ht
  have ht1 := soundAt_weakOneByOne φ hW ws _ hR0 hv0 ht0 hv1
  have htT := soundAt_pinOneByOne φ hP rq _ hlit hR1 hv1 ht1 hvT
  exact soundAt_of_embedded _ eAT eTA adA hsA htT

-- ============================================================
-- One pin: the pinned step is free
-- ============================================================

/-- **What is left of one pin**: the entries towards the literal steps other than the pinned one. -/
def PinPairSoundAt : Prop :=
  ∀ g : GPathM, ReadableAgg g → isValid g = true → SoundAt (LitStep φ) g →
    ∀ r : NodeId, LitStep φ r.step → isValid (filterAllAgg g [r]) = true →
      ∀ x n, (filterAllAgg g [r]).node? x = some n → 0 ≤ x.id.step →
        x.id.step < (filterAllAgg g [r]).current_step →
        ∀ q, 0 ≤ q.id.step → q.id.step < (filterAllAgg g [r]).current_step → LitStep φ q.id.step →
          q.id.step ≠ r.step → q ∈ n.owners → Realizes (filterAllAgg g [r]) x q

/-- **One pin, towards the pinned step.** An owner at the pinned step carries the pin; the entry was on a
path before the pin, and that path passes the pin, so it survives. -/
theorem pinStep_of_pairs (h : PinPairSoundAt φ) : PinStepSoundAt φ := by
  intro g hR hv ht r hr hvr x n hx hx0 hx1 q hq0 hq1 hL hqn
  by_cases hqr : q.id.step = r.step
  · have hRr := ReadableAgg_filterAllAgg g hR [r]
    have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
    have rcg := RCtx_of_readableAgg g hR
    have hpr := pruned_filterAllAgg g [r]
    have hcs := hpr.step_eq
    obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
    have hxid := node?_id_eq _ x n hx
    have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
    have hqg := ctxR.ownGow x n hx q hqn hq0 hq1
    have hqid : q.id = r := ReaderComplete.pin_id g r q hqg hqr
    obtain ⟨sel, hsc, hsx, hsq⟩ := ht x n₀ hx₀ hx0 (by rw [← hcs]; exact hx1) q hq0
      (by rw [← hcs]; exact hq1) hL (hown q hqn)
    refine ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => ?_), hsx, hsq⟩
    rw [List.mem_singleton.mp hreq, ← hqr, hsq, hqid]
  · exact h g hR hv ht r hr hvr x n hx hx0 hx1 q hq0 hq1 hL hqr hqn

/-- **One pin: every node still standing is on a chain that passes the pin.** No extra hypothesis
beyond the induction's own: a live node owns something at the pinned step, what it owns carries the
pin (`ReaderComplete.pin_id`), the pinned step is a literal step, so `SoundAt g` hands over a chain
of `g` through `x` and it — and that chain passes the pin, so it is a chain of the pinned state.

So a pin never creates a dead end, and `PinPairSoundAt` is exactly the *second* demand: that the
chain can be made to pick a given second entry as well. -/
theorem realizes_pin_at (g : GPathM) (hR : ReadableAgg g)
    (r : NodeId) (hr0 : 0 ≤ r.step)
    (hvr : isValid (filterAllAgg g [r]) = true)
    (hrs : r.step < (filterAllAgg g [r]).current_step)
    (x : PathNodeId) (n : PNodeM) (hx : (filterAllAgg g [r]).node? x = some n)
    (_hx0 : 0 ≤ x.id.step) (_hx1 : x.id.step < (filterAllAgg g [r]).current_step)
    (ht : ∀ n₀, g.node? x = some n₀ → ∀ w, w.id.step = r.step → w ∈ n₀.owners → Realizes g x w) :
    ∃ w ∈ n.owners, w.id = r ∧ Realizes (filterAllAgg g [r]) x w := by
  have hRr := ReadableAgg_filterAllAgg g hR [r]
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
  have rcg := RCtx_of_readableAgg g hR
  have hpr := pruned_filterAllAgg g [r]
  have hcs := hpr.step_eq
  -- a live node owns something at the pinned step, and the pin fixes what
  have hok := owners_ok_of_isValidNode _ n (ctxR.nodeval x n hx)
  simp only [List.all_eq_true] at hok
  have hent := hok r.step (mem_intRange hr0 (by omega))
  obtain ⟨w, hw, hws⟩ := List.any_eq_true.mp hent
  have hwstep : w.id.step = r.step := eq_of_beq hws
  have hwid : w.id = r :=
    ReaderComplete.pin_id g r w (ctxR.ownGow x n hx w hw (by omega) (by omega)) hwstep
  -- pull `x` back to `g` and realize the pair there
  obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
  have hxid := node?_id_eq _ x n hx
  have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
  obtain ⟨sel, hsc, hsx, hsw⟩ := ht n₀ hx₀ w hwstep (hown w hw)
  refine ⟨w, hw, hwid, sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => ?_), hsx, hsw⟩
  rw [List.mem_singleton.mp hreq, ← hwstep, hsw, hwid]

/-- **La variante que solo pide —y solo entrega— la cadena.**

`realizes_pin_at` pide `Realizes g x w`, que es una frase sobre **dos** nodos. Pero quien la consume
(el lector) tira la pata de `x`: solo usa que el estado pinchado tenga alguna cadena. Así que basta
con que el owner al paso pinchado esté en **alguna** cadena — un enunciado sobre **un** nodo.

Es el cruce de la frontera 2-vs-3 en la dirección buena, y es lo único que hacía falta. -/
theorem chain_pin_at (g : GPathM) (hR : ReadableAgg g)
    (r : NodeId) (hr0 : 0 ≤ r.step)
    (hvr : isValid (filterAllAgg g [r]) = true)
    (hrs : r.step < (filterAllAgg g [r]).current_step)
    (x : PathNodeId) (n : PNodeM) (hx : (filterAllAgg g [r]).node? x = some n)
    (_hx0 : 0 ≤ x.id.step) (_hx1 : x.id.step < (filterAllAgg g [r]).current_step)
    (ht : ∀ n₀, g.node? x = some n₀ → ∀ w, w.id.step = r.step → w ∈ n₀.owners →
      ∃ sel, ChainSound g sel ∧ sel w.id.step = w) :
    ∃ sel, ChainSound (filterAllAgg g [r]) sel := by
  have hRr := ReadableAgg_filterAllAgg g hR [r]
  have ctxR := Reader.Ctx_of_readable _ (readable_of_readableAgg _ hRr) hvr
  have rcg := RCtx_of_readableAgg g hR
  have hpr := pruned_filterAllAgg g [r]
  have hcs := hpr.step_eq
  -- un nodo vivo posee algo en el paso pinchado, y el pin fija qué
  have hok := owners_ok_of_isValidNode _ n (ctxR.nodeval x n hx)
  simp only [List.all_eq_true] at hok
  have hent := hok r.step (mem_intRange hr0 (by omega))
  obtain ⟨w, hw, hws⟩ := List.any_eq_true.mp hent
  have hwstep : w.id.step = r.step := eq_of_beq hws
  have hwid : w.id = r :=
    ReaderComplete.pin_id g r w (ctxR.ownGow x n hx w hw (by omega) (by omega)) hwstep
  obtain ⟨n₀, hn₀, hid, hown, _⟩ := hpr.nodes_derived n (List.mem_of_find?_eq_some hx)
  have hxid := node?_id_eq _ x n hx
  have hx₀ : g.node? x = some n₀ := by rw [← hxid, hid]; exact node?_of_mem rcg.nodup n₀ hn₀
  obtain ⟨sel, hsc, hsw⟩ := ht n₀ hx₀ w hwstep (hown w hw)
  exact ⟨sel, ChainSound_filterAllAgg g [r] sel hsc (fun req hreq _ _ => by
    rw [List.mem_singleton.mp hreq, ← hwstep, hsw, hwid])⟩

/-- info: 'AbsSat.GraphPath.Model.RunSteps.chain_pin_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_pin_at

/-- **Con un invariante de entradas global.** El pin solo necesita que las entradas del nodo que se
mira sean realizables. -/
theorem realizes_pin_gen (L : Int → Prop) (g : GPathM) (hR : ReadableAgg g) (ht : SoundAt L g)
    (r : NodeId) (hr : L r.step) (hr0 : 0 ≤ r.step)
    (hvr : isValid (filterAllAgg g [r]) = true)
    (hrs : r.step < (filterAllAgg g [r]).current_step)
    (x : PathNodeId) (n : PNodeM) (hx : (filterAllAgg g [r]).node? x = some n)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < (filterAllAgg g [r]).current_step) :
    ∃ w ∈ n.owners, w.id = r ∧ Realizes (filterAllAgg g [r]) x w := by
  have hcs := (pruned_filterAllAgg g [r]).step_eq
  refine realizes_pin_at g hR r hr0 hvr hrs x n hx hx0 hx1 (fun n₀ hx₀ w hwr hwn => ?_)
  exact ht x n₀ hx₀ hx0 (by rw [← hcs]; exact hx1) w (by rw [hwr]; exact hr0)
    (by rw [hwr, ← hcs]; exact hrs) (by rw [hwr]; exact hr) hwn

/-- **Con el bloque literal**, que es la instancia que usa la corrida de la máquina. -/
theorem realizes_pin (g : GPathM) (hR : ReadableAgg g) (ht : SoundAt (LitStep φ) g)
    (r : NodeId) (hr : LitStep φ r.step) (hr0 : 0 ≤ r.step)
    (hvr : isValid (filterAllAgg g [r]) = true)
    (hrs : r.step < (filterAllAgg g [r]).current_step)
    (x : PathNodeId) (n : PNodeM) (hx : (filterAllAgg g [r]).node? x = some n)
    (hx0 : 0 ≤ x.id.step) (hx1 : x.id.step < (filterAllAgg g [r]).current_step) :
    ∃ w ∈ n.owners, w.id = r ∧ Realizes (filterAllAgg g [r]) x w :=
  realizes_pin_gen (LitStep φ) g hR ht r hr hr0 hvr hrs x n hx hx0 hx1

/-- info: 'AbsSat.GraphPath.Model.RunSteps.realizes_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms realizes_pin

/-- **The verdict by construction, from its single steps.** -/
theorem sat_of_steps (hwf : WF φ) (hW : WeakStepSoundAt φ) (hP : PinPairSoundAt φ)
    (kv : NodeId × GPathM) (hkv : kv ∈ PureDriverImproves.pureRunW φ)
    (hv : isValid (filterAllAgg kv.2 []) = true) : Satisfiable φ :=
  RunInhabited.sat_of_soundAt φ hwf (filterSoundAt_of_steps φ hwf hW (pinStep_of_pairs φ hP)) kv hkv hv

/-- info: 'AbsSat.GraphPath.Model.RunSteps.sat_of_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sat_of_steps

end AbsSat.GraphPath.Model.RunSteps
