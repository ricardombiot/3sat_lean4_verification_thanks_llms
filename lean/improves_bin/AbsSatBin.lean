-- lean/improves_bin/AbsSatBin.lean
import AbsSatBin.Utils.Alias
import AbsSatBin.Cnf.Formula
import AbsSatBin.Cnf.Dimacs
import AbsSatBin.GraphMap.CnfMapBin
import AbsSatBin.GraphMap.MapBinDump

/-! # `AbsSatBin` — the machine over the binary map

Lean mirror of `julia/improves_bin`: the `bin` map (three 2-node steps per clause, prohibited
window `(0,0,0)`) and the UP that skips it. Modules arrive from `lean_project` one at a time,
as the migration needs them; see `README.md` for the ledger of what came from where.
-/
