-- lean/improves_bin/AbsSatBin.lean  (generado por scripts/gen_root.sh)
import AbsSatBin.Cnf.Dimacs
import AbsSatBin.Cnf.Formula
import AbsSatBin.GraphMap.CnfMapBin
import AbsSatBin.GraphMap.MapBinDump
import AbsSatBin.GraphPath.Model.AddNode
import AbsSatBin.GraphPath.Model.Certificate
import AbsSatBin.GraphPath.Model.CleanInvalid
import AbsSatBin.GraphPath.Model.Coherence
import AbsSatBin.GraphPath.Model.Denot
import AbsSatBin.GraphPath.Model.DriverBin
import AbsSatBin.GraphPath.Model.Extendable
import AbsSatBin.GraphPath.Model.Filter
import AbsSatBin.GraphPath.Model.Fuel
import AbsSatBin.GraphPath.Model.GPathM
import AbsSatBin.GraphPath.Model.Join
import AbsSatBin.GraphPath.Model.L6
import AbsSatBin.GraphPath.Model.L6Search
import AbsSatBin.GraphPath.Model.L6Up
import AbsSatBin.GraphPath.Model.OwnersInvariants
import AbsSatBin.GraphPath.Model.Pruned
import AbsSatBin.GraphPath.Model.Reachable
import AbsSatBin.GraphPath.Model.Review
import AbsSatBin.GraphPath.Model.Up
import AbsSatBin.GraphPath.Model.Verdict
import AbsSatBin.Utils.Alias

/-! # `AbsSatBin` — the machine over the binary map

Lean mirror of `julia/improves_bin`: the `bin` map (three 2-node steps per clause, prohibited
window `(0,0,0)`) and the UP that skips it. Modules arrive from `lean_project` one at a time,
as the migration needs them; see `README.md` for the ledger of what came from where.
-/
