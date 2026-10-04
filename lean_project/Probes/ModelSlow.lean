import AbsSat.GraphPath.Model.MirrorTest
import AbsSat.GraphMap.ImportCnf

/-! # `model-slow`: why the model became slow with the review mirror

On one cnf, runs the model's machine (`MirrorTest` loop, base `review`) and, for every send, reviews
the same state with the model's `reviewNode` (mirror) and with a local copy without the mirror
(`reviewNodeA`, the pre-2026-09-24 one): rounds of `reviewFuel`, time, and whether the two results are
the same state. The line followed is the mirrored one.

    lake exe model-slow <file.cnf>
-/

open AbsSat.Utils.Alias
open AbsSat.GraphMap.GraphMap
open AbsSat.GraphPath.Model
open AbsSat.GraphPath.Model.GPathM
open AbsSat.GraphPath.Model.MirrorTest

def reviewNodeA (g : GPathM) (nb : PNodeM → List PathNodeId) (id : PathNodeId) : GPathM :=
  match g.node? id with
  | none => g
  | some d =>
    if isValidNode g d then
      let uni := unionOwnersOf g (nb d)
      let d := relink (intersectOwners d.owners uni) d
      let g := unlinkIncompatible
        (updateAt g id (fun n => { n with owners := intersectOwners n.owners uni })) id
      if isValidNode g d then g else removeNode g id
    else removeNode g id

def stepsA (g : GPathM) (nb : PNodeM → List PathNodeId) : List Int → GPathM
  | [] => g
  | k :: ks =>
    if isValid g then stepsA (((g.line k).map (·.id)).foldl (fun g id => reviewNodeA g nb id) g) nb ks
    else g

def reviewPassA (g : GPathM) : GPathM :=
  let h := cleanInvalid₂ g
  let p := stepsA h (·.parents) (intRange 1 (h.current_step - 1))
  stepsA p (·.sons) (intRange 0 (p.current_step - 2)).reverse

/-- The pass before the pair rule (plan pair_mode): mirror on, plain two-phase clean. -/
def reviewPassNP (g : GPathM) : GPathM := reviewSons (reviewParents (cleanInvalid₂ g))

/-- `reviewFuel`, counting rounds, with a given pass. -/
def reviewCount (pass : GPathM → GPathM) (g : GPathM) : GPathM × Nat := Id.run do
  let mut g := g
  let mut n := 0
  let mut fuel := measure g + 1
  while fuel > 0 do
    fuel := fuel - 1
    if !isValid g then fuel := 0
    else
      let g' := pass g
      n := n + 1
      if measure g' < measure g then g := g' else
        g := g'
        fuel := 0
  return (g, n)

def sameState (g h : GPathM) : Bool :=
  let setEq (a b : List PathNodeId) := a.all (b.contains ·) && b.all (a.contains ·)
  isValid g == isValid h && (!isValid g ||
    (setEq g.gowners h.gowners && g.nodes.length == h.nodes.length &&
     g.nodes.all (fun n => match h.node? n.id with
       | some m => setEq n.owners m.owners && setEq n.parents m.parents && setEq n.sons m.sons
       | none => false)))

def main (args : List String) : IO Unit := do
  let path := args.headD "x.cnf"
  let gmap ← AbsSat.GraphMap.ImportCnf.load_import! path
  let mut line := mirrorInit gmap
  let mut totM := 0; let mut totA := 0; let mut tM := 0; let mut tA := 0
  let mut sends := 0; let mut diff := 0
  let mut tC := 0; let mut tP := 0; let mut tPF := 0
  for step in [0:(gmap.step - 1).toNat] do
    let mut next : MirrorLine := []
    let mut stepM := 0; let mut stepA := 0; let mut maxNodes := 0
    for (origin, g) in line do
      match get_node gmap origin with
      | none => pure ()
      | some mn =>
        for destine in mn.sons.toList do
          match get_node gmap destine with
          | none => pure ()
          | some dn =>
            let F := dn.requires.toList.foldl filterRequire g
            maxNodes := max maxNodes F.nodes.length
            let t0 ← IO.monoMsNow
            let (rA, nA) ← IO.lazyPure (fun _ => reviewCount reviewPassNP F)
            let t1 ← IO.monoMsNow
            let (rM, nM) ← IO.lazyPure (fun _ => reviewCount reviewPass F)
            let t2 ← IO.monoMsNow
            let t3 ← IO.monoMsNow
            let c ← IO.lazyPure (fun _ => cleanInvalid₂ F)
            let _ ← IO.lazyPure (fun _ => measure c)
            let t4 ← IO.monoMsNow
            let pc ← IO.lazyPure (fun _ => pairSweep c)
            let _ ← IO.lazyPure (fun _ => measure pc)
            let t5 ← IO.monoMsNow
            let cp ← IO.lazyPure (fun _ => cleanPair F)
            let _ ← IO.lazyPure (fun _ => measure cp)
            let t6 ← IO.monoMsNow
            tC := tC + (t4 - t3); tP := tP + (t5 - t4); tPF := tPF + (t6 - t5)
            sends := sends + 1
            totA := totA + nA; totM := totM + nM
            stepA := stepA + nA; stepM := stepM + nM
            tA := tA + (t1 - t0); tM := tM + (t2 - t1)
            if !sameState rA rM then diff := diff + 1
            let g' := up rM destine dn.title
            if isValid g' then next := insertGPath next destine g'
    IO.println s!"paso {step}: gpaths {line.length}, max nodos {maxNodes}, vueltas sin regla {stepA}, con regla {stepM}, tiempo acumulado {tA}/{tM} ms; una limpieza {tC}, una pairSweep {tP}, un cleanPair {tPF}"
    (← IO.getStdout).flush
    line := next
  IO.println s!"envios {sends}; vueltas sin/con regla {totA}/{totM}; tiempo {tA}/{tM} ms; estados distintos {diff}"
