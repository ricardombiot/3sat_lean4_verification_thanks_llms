#!/bin/bash
# Side-by-side execution of Lean 4 and Julia on same test CNF

set -e

JULIA_BIN="/Users/ricardo/.julia/juliaup/julia-1.13.0+0.aarch64.apple.darwin14/Julia-1.13.app/Contents/Resources/julia/bin/julia"
TEST_CNF="${1:-simple_test.cnf}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "╔════════════════════════════════════════════════════════╗"
echo "║  LEAN 4 vs JULIA: Side-by-Side Execution Comparison   ║"
echo "╚════════════════════════════════════════════════════════╝"
echo ""
echo "Test file: $TEST_CNF"
echo ""

# Check file exists
if [ ! -f "$SCRIPT_DIR/lean_project/$TEST_CNF" ]; then
    echo "❌ Error: $SCRIPT_DIR/lean_project/$TEST_CNF not found"
    exit 1
fi

# Lean 4 execution
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "▶️  LEAN 4 EXECUTION"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
cd "$SCRIPT_DIR/lean_project"
lake exe stepbystep-cnf 2>&1 | grep -v "^ℹ\|^info:" || true
cd "$SCRIPT_DIR"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "▶️  JULIA EXECUTION"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
$JULIA_BIN StepByStep.jl 2>&1 || true

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✅ Comparison complete. See LEAN_VS_JULIA_COMPARISON.md"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
