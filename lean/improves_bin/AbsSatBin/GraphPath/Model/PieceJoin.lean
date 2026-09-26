-- lean/improves_bin/AbsSatBin/GraphPath/Model/PieceJoin.lean
import AbsSatBin.GraphPath.Model.StateGrow

/-!
# The join, per state: pieces grow into their destination, and `PieceLocal`

A state of line `n+1` is the join of the pieces `upF X d` of the states `X` of line `n` sent to its key `d`.

* **`piece_grown`**: every valid piece grows into the state of its destination (`Grown`): the join only
  adds. So a certificate of a piece is a certificate of the joined state.
* **`PieceLocal n`**: every clique with witnesses of a state of line `n+1` is a clique with witnesses of one
  of its pieces. Measured in Julia (`julia/improves_bin/test_3sat/probes/piecelocal_probe.jl`): 3.5 M cliques
  of size 1–3 with witnesses in joined states, all inside one piece. It is the join rule of the machine —
  the union of valid sets does not create new ones — and `StateGrow.top_one_source` is its first part (the
  table of a node of the new step comes from one source).
* **`mapCert_join`**: with `PieceLocal`, `MapCert` of every piece gives `MapCert` of every state of the line.
-/

namespace AbsSatBin.GraphPath.Model.PieceJoin

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphPath.Model
open AbsSatBin.GraphPath.Model.GPathM
open AbsSatBin.GraphPath.Model.PureDriver
open AbsSatBin.GraphPath.Model.LineSem
open AbsSatBin.GraphPath.Model.CliqueTri (Clique)
open AbsSatBin.GraphPath.Model.MapCert (MapCert WitR CertR)

variable (φ : Cnf)

-- ============================================================
-- A piece grows into its destination
-- ============================================================

/-- The line has, at key `d`, a state that `G` grows into. -/
def GrownAt (d : NodeId) (G : GPathM) (line : PureLine) : Prop := ∃ h, (d, h) ∈ line ∧ Grown G h

theorem insertPure_of_mem (line : PureLine) (hnd : (line.map (·.1)).Nodup) (key : NodeId) (e g : GPathM)
    (he : (key, e) ∈ line) : (key, doJoin e g) ∈ insertPure line key g := by
  unfold insertPure
  cases hf : line.find? (fun kv => kv.1 == key) with
  | none =>
    exact absurd (beq_iff_eq.mpr rfl) (List.find?_eq_none.mp hf (key, e) he)
  | some kv =>
    have hmem : kv ∈ line := List.mem_of_find?_eq_some hf
    have hkey : kv.1 = key :=
      eq_of_beq (List.find?_some (p := fun x : NodeId × GPathM => x.1 == key) hf)
    have hkv : kv = (key, e) := key_inj line hnd kv hmem (key, e) he hkey
    have : (key, doJoin e g)
        = (fun x : NodeId × GPathM => if x.1 == key then (key, doJoin kv.2 g) else x) kv := by
      simp only; rw [if_pos (by rw [hkey]; exact beq_iff_eq.mpr rfl), hkv]
    rw [this]
    exact List.mem_map_of_mem hmem

theorem grownAt_insertPure (k : Int) (line : PureLine) (hl : LineOk φ k line) (key : NodeId) (g' : GPathM)
    (hg' : StateOk φ k (key, g')) (d : NodeId) (G : GPathM) (h : GrownAt d G line) :
    GrownAt d G (insertPure line key g') := by
  obtain ⟨h0, hm, hgr⟩ := h
  by_cases hk : d = key
  · subst hk
    refine ⟨doJoin h0 g', insertPure_of_mem line hl.1 d h0 g' hm, hgr.trans ?_⟩
    have hok := okJoin_of_stateOk φ k d h0 g' (hl.2 _ hm) hg'
    simp only [doJoin, hok, if_pos]
    exact grown_join_left h0 g'
  · exact ⟨h0, mem_insertPure_of_ne line key d g' h0 hk hm, hgr⟩

theorem grownAt_insertPure_new (k : Int) (line : PureLine) (hl : LineOk φ k line) (d : NodeId) (G : GPathM)
    (hG : StateOk φ k (d, G)) : GrownAt d G (insertPure line d G) := by
  cases hf : line.find? (fun x => x.1 == d) with
  | some kv =>
    have hmem : kv ∈ line := List.mem_of_find?_eq_some hf
    have hkey : kv.1 = d := eq_of_beq (List.find?_some (p := fun x : NodeId × GPathM => x.1 == d) hf)
    have he : (d, kv.2) ∈ line := by rw [← hkey]; exact hmem
    refine ⟨doJoin kv.2 G, insertPure_of_mem line hl.1 d kv.2 G he, ?_⟩
    have hok := okJoin_of_stateOk φ k d kv.2 G (hl.2 _ he) hG
    simp only [doJoin, hok, if_pos]
    exact grown_join_right kv.2 G hok
  | none =>
    refine ⟨G, ?_, Grown.refl G⟩
    unfold insertPure; rw [hf]
    exact List.mem_append_right _ List.mem_cons_self

section
variable (k : Int) (kv : NodeId × GPathM) (hkv : StateOk φ k kv)
include hkv

theorem grownAt_sendAll_keep (d : NodeId) (G : GPathM) :
    ∀ acc, LineOk φ (k + 1) acc → GrownAt d G acc → GrownAt d G (sendAll φ kv acc) := by
  simp only [sendAll]
  have : ∀ (l : List NodeId), (∀ d' ∈ l, d' ∈ sonsOfMap φ kv.1) →
      ∀ acc, LineOk φ (k + 1) acc → GrownAt d G acc → GrownAt d G (l.foldl (sendTo φ kv.2) acc) := by
    intro l
    induction l with
    | nil => intro _ acc _ h; exact h
    | cons x xs ih =>
      intro hx acc hl h
      simp only [List.foldl_cons]
      refine ih (fun d' hd => hx d' (List.mem_cons_of_mem _ hd)) _
        (LineOk_sendTo φ k kv hkv x (hx x List.mem_cons_self) acc hl) ?_
      simp only [sendTo]
      split
      · next hval =>
        exact grownAt_insertPure φ (k + 1) acc hl x _ (StateOk_sent φ k kv hkv x (hx x List.mem_cons_self) hval) d G h
      · exact h
  exact this _ (fun _ hd => hd)

theorem grownAt_sendAll_new (d : NodeId) (hd : d ∈ sonsOfMap φ kv.1)
    (hv : isValid (upF φ kv.2 d) = true) :
    ∀ acc, LineOk φ (k + 1) acc → GrownAt d (upF φ kv.2 d) (sendAll φ kv acc) := by
  simp only [sendAll]
  have : ∀ (l : List NodeId), (∀ d' ∈ l, d' ∈ sonsOfMap φ kv.1) → d ∈ l →
      ∀ acc, LineOk φ (k + 1) acc → GrownAt d (upF φ kv.2 d) (l.foldl (sendTo φ kv.2) acc) := by
    intro l
    induction l with
    | nil => intro _ h; exact absurd h List.not_mem_nil
    | cons x xs ih =>
      intro hx hdl acc hl
      simp only [List.foldl_cons]
      have hl' := LineOk_sendTo φ k kv hkv x (hx x List.mem_cons_self) acc hl
      rcases List.mem_cons.mp hdl with e | hdl'
      · subst e
        have hsend : sendTo φ kv.2 acc d = insertPure acc d (upF φ kv.2 d) := by
          simp only [sendTo]; rw [if_pos hv]
        have hbase : GrownAt d (upF φ kv.2 d) (sendTo φ kv.2 acc d) := by
          rw [hsend]
          exact grownAt_insertPure_new φ (k + 1) acc hl d _ (StateOk_sent φ k kv hkv d hd hv)
        -- the rest of the fold keeps it
        have keep : ∀ (l' : List NodeId), (∀ d' ∈ l', d' ∈ sonsOfMap φ kv.1) →
            ∀ acc', LineOk φ (k + 1) acc' → GrownAt d (upF φ kv.2 d) acc' →
              GrownAt d (upF φ kv.2 d) (l'.foldl (sendTo φ kv.2) acc') := by
          intro l'
          induction l' with
          | nil => intro _ acc' _ h; exact h
          | cons y ys ih' =>
            intro hy acc' hl'' h
            simp only [List.foldl_cons]
            refine ih' (fun d' hd' => hy d' (List.mem_cons_of_mem _ hd')) _
              (LineOk_sendTo φ k kv hkv y (hy y List.mem_cons_self) acc' hl'') ?_
            simp only [sendTo]
            split
            · next hval =>
              exact grownAt_insertPure φ (k + 1) acc' hl'' y _
                (StateOk_sent φ k kv hkv y (hy y List.mem_cons_self) hval) d _ h
            · exact h
        exact keep xs (fun d' hd' => hx d' (List.mem_cons_of_mem _ hd')) _ hl' hbase
      · exact ih (fun d' hd' => hx d' (List.mem_cons_of_mem _ hd')) hdl' _ hl'
  exact this _ (fun _ hd => hd) hd
end

/-- **Every valid piece grows into the state of its destination.** -/
theorem piece_grown (n : Nat) (kv : NodeId × GPathM) (hkv : kv ∈ line φ n) (d : NodeId)
    (hd : d ∈ sonsOfMap φ kv.1) (hv : isValid (upF φ kv.2 d) = true) :
    ∃ h, (d, h) ∈ line φ (n + 1) ∧ Grown (upF φ kv.2 d) h := by
  rw [line_succ]
  simp only [pureAdvance]
  have hall : ∀ x ∈ line φ n, StateOk φ n x := (lineOk φ n).2
  have main : ∀ (l : PureLine), (∀ x ∈ l, StateOk φ n x) → kv ∈ l →
      ∀ acc, LineOk φ ((n : Int) + 1) acc →
        GrownAt d (upF φ kv.2 d) (l.foldl (fun next x => sendAll φ x next) acc) := by
    intro l
    induction l with
    | nil => intro _ h; exact absurd h List.not_mem_nil
    | cons x xs ih =>
      intro hx hkl acc hl
      simp only [List.foldl_cons]
      have hl' := LineOk_sendAll φ n x (hx x List.mem_cons_self) acc hl
      rcases List.mem_cons.mp hkl with e | hkl'
      · subst e
        have hbase := grownAt_sendAll_new φ n kv (hx kv List.mem_cons_self) d hd hv acc hl
        have keep : ∀ (l' : PureLine), (∀ y ∈ l', StateOk φ n y) →
            ∀ acc', LineOk φ ((n : Int) + 1) acc' → GrownAt d (upF φ kv.2 d) acc' →
              GrownAt d (upF φ kv.2 d) (l'.foldl (fun next y => sendAll φ y next) acc') := by
          intro l'
          induction l' with
          | nil => intro _ acc' _ h; exact h
          | cons y ys ih' =>
            intro hy acc' hl'' h
            simp only [List.foldl_cons]
            exact ih' (fun z hz => hy z (List.mem_cons_of_mem _ hz)) _
              (LineOk_sendAll φ n y (hy y List.mem_cons_self) acc' hl'')
              (grownAt_sendAll_keep φ n y (hy y List.mem_cons_self) d _ acc' hl'' h)
        exact keep xs (fun z hz => hx z (List.mem_cons_of_mem _ hz)) _ hl' hbase
      · exact ih (fun z hz => hx z (List.mem_cons_of_mem _ hz)) hkl' _ hl'
  exact main _ hall hkv [] ⟨by simp, by intro x hx; exact absurd hx List.not_mem_nil⟩

-- ============================================================
-- `PieceLocal` and the join
-- ============================================================

/-- **`PieceLocal n`**: every clique with witnesses of a state of line `n+1` is one of a single piece. -/
def PieceLocal (n : Nat) : Prop :=
  ∀ kv' ∈ line φ (n + 1), ∀ Q R, Clique kv'.2 Q → WitR kv'.2 Q R →
    ∃ kv ∈ line φ n, kv'.1 ∈ sonsOfMap φ kv.1 ∧ isValid (upF φ kv.2 kv'.1) = true ∧
      Clique (upF φ kv.2 kv'.1) Q ∧ WitR (upF φ kv.2 kv'.1) Q R

/-- **The join keeps `MapCert`** when cliques with witnesses live in one piece. -/
theorem mapCert_join (n : Nat) (hPL : PieceLocal φ n)
    (hP : ∀ kv ∈ line φ n, ∀ d ∈ sonsOfMap φ kv.1, isValid (upF φ kv.2 d) = true → MapCert (upF φ kv.2 d)) :
    ∀ kv' ∈ line φ (n + 1), MapCert kv'.2 := by
  intro kv' hkv' Q R hQ hW
  obtain ⟨kv, hkv, hd, hv, hQP, hWP⟩ := hPL kv' hkv' Q R hQ hW
  obtain ⟨sel, hs, hon, hR⟩ := hP kv hkv kv'.1 hd hv Q R hQP hWP
  obtain ⟨h, hmem, hgr⟩ := piece_grown φ n kv hkv kv'.1 hd hv
  have he : (kv'.1, h) = kv' := key_inj _ (lineOk φ (n + 1)).1 _ hmem kv' hkv' rfl
  rw [← he]
  refine ⟨sel, ChainSound_of_grown hgr sel hs, hon, fun m hm h0 h1 => hR m hm h0 ?_⟩
  have := hgr.step_eq; simp only at h1; omega

/-- info: 'AbsSatBin.GraphPath.Model.PieceJoin.piece_grown' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms piece_grown

/-- info: 'AbsSatBin.GraphPath.Model.PieceJoin.mapCert_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapCert_join

end AbsSatBin.GraphPath.Model.PieceJoin
