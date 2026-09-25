-- lean/improves_bin/AbsSatBin.lean  (generado por scripts/gen_root.sh)
import AbsSatBin.Cnf.Dimacs
import AbsSatBin.Cnf.Formula
import AbsSatBin.GraphMap.CnfMapBin
import AbsSatBin.GraphMap.CnfSelBin
import AbsSatBin.GraphMap.MapBinDump
import AbsSatBin.GraphPath.Model.AddNode
import AbsSatBin.GraphPath.Model.AggressiveReview
import AbsSatBin.GraphPath.Model.ArcConsistency
import AbsSatBin.GraphPath.Model.Bridge
import AbsSatBin.GraphPath.Model.Candidates
import AbsSatBin.GraphPath.Model.Certificate
import AbsSatBin.GraphPath.Model.Certifies
import AbsSatBin.GraphPath.Model.CleanInvalid
import AbsSatBin.GraphPath.Model.CleanTwoPhase
import AbsSatBin.GraphPath.Model.CnfChain
import AbsSatBin.GraphPath.Model.Coherence
import AbsSatBin.GraphPath.Model.Conservation
import AbsSatBin.GraphPath.Model.Decision
import AbsSatBin.GraphPath.Model.Denot
import AbsSatBin.GraphPath.Model.DriverBin
import AbsSatBin.GraphPath.Model.Extendable
import AbsSatBin.GraphPath.Model.Filter
import AbsSatBin.GraphPath.Model.Fuel
import AbsSatBin.GraphPath.Model.GPathM
import AbsSatBin.GraphPath.Model.GownersNodes
import AbsSatBin.GraphPath.Model.Join
import AbsSatBin.GraphPath.Model.JoinSound
import AbsSatBin.GraphPath.Model.L6
import AbsSatBin.GraphPath.Model.L6Search
import AbsSatBin.GraphPath.Model.L6Up
import AbsSatBin.GraphPath.Model.L7
import AbsSatBin.GraphPath.Model.MapChain
import AbsSatBin.GraphPath.Model.MapReachable
import AbsSatBin.GraphPath.Model.NoDeadEnd
import AbsSatBin.GraphPath.Model.NodeIds
import AbsSatBin.GraphPath.Model.NodeInvariant
import AbsSatBin.GraphPath.Model.OtherBitSem
import AbsSatBin.GraphPath.Model.OwnersInvariants
import AbsSatBin.GraphPath.Model.Ownership
import AbsSatBin.GraphPath.Model.PairInactive
import AbsSatBin.GraphPath.Model.ParentId
import AbsSatBin.GraphPath.Model.Parents
import AbsSatBin.GraphPath.Model.PathExists
import AbsSatBin.GraphPath.Model.PickInduction
import AbsSatBin.GraphPath.Model.PinChainBin
import AbsSatBin.GraphPath.Model.Pinned
import AbsSatBin.GraphPath.Model.Pruned
import AbsSatBin.GraphPath.Model.PureDriver
import AbsSatBin.GraphPath.Model.Reachable
import AbsSatBin.GraphPath.Model.Reader
import AbsSatBin.GraphPath.Model.ReaderAgg
import AbsSatBin.GraphPath.Model.ReaderExec
import AbsSatBin.GraphPath.Model.ReaderPrefix
import AbsSatBin.GraphPath.Model.Review
import AbsSatBin.GraphPath.Model.SelfOwn
import AbsSatBin.GraphPath.Model.SkipReview
import AbsSatBin.GraphPath.Model.Sons
import AbsSatBin.GraphPath.Model.Survive
import AbsSatBin.GraphPath.Model.SymMachine
import AbsSatBin.GraphPath.Model.Threaded
import AbsSatBin.GraphPath.Model.Up
import AbsSatBin.GraphPath.Model.Verdict
import AbsSatBin.SatMachine.PureProofs
import AbsSatBin.SatMachine.PureSatMachine
import AbsSatBin.Utils.Alias

/-! # `AbsSatBin` — the machine over the binary map

Lean mirror of `julia/improves_bin`: the `bin` map (three 2-node steps per clause, prohibited
window `(0,0,0)`) and the UP that skips it. Modules arrive from `lean_project` one at a time,
as the migration needs them; see `README.md` for the ledger of what came from where.
-/
