#!/usr/bin/env bash
# Continuous agentic fuzzing with LLM-guided grammar refinement
#
# This script runs the fuzzer in a loop:
# 1. Fuzz for N executions
# 2. Analyze successes with Claude Opus
# 3. Auto-apply top suggestions
# 4. Rebuild fuzzer
# 5. Repeat until Ctrl+C

set -e

# Configuration
REFINE_INTERVAL=${REFINE_INTERVAL:-100}
DEPTH=${DEPTH:-10}
AUTO_APPLY=${AUTO_APPLY:-3}
GENERATOR_DIR="$(cd "$(dirname "$0")/../generator" && pwd)"
SCAFFOLD_DIR="$(cd "$(dirname "$0")/../scaffold" && pwd)"

# Colors for pretty printing
BLUE='\033[1;34m'
GREEN='\033[1;32m'
YELLOW='\033[1;33m'
CYAN='\033[1;36m'
MAGENTA='\033[1;35m'
NC='\033[0m' # No Color

# Pretty print a phase transition
print_phase() {
    local phase=$1
    local icon=$2
    echo ""
    echo -e "${CYAN}╔════════════════════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${CYAN}║${NC}  ${icon} ${BLUE}${phase}${NC}"
    echo -e "${CYAN}╚════════════════════════════════════════════════════════════════════════════╝${NC}"
    echo ""
}

print_generation() {
    local gen=$1
    echo ""
    echo -e "${MAGENTA}┌────────────────────────────────────────────────────────────────────────────┐${NC}"
    echo -e "${MAGENTA}│${NC}  🧬 ${YELLOW}GENERATION ${gen}${NC}"
    echo -e "${MAGENTA}└────────────────────────────────────────────────────────────────────────────┘${NC}"
    echo ""
}

# Check API key
if [ -z "$ANTHROPIC_API_KEY" ]; then
    echo -e "${YELLOW}⚠️  ANTHROPIC_API_KEY not set${NC}"
    echo "   Continuous refinement requires an Anthropic API key."
    echo "   Set it with: export ANTHROPIC_API_KEY=sk-ant-..."
    echo ""
    echo "   Running fuzzer without refinement..."
    cd "$GENERATOR_DIR"
    cargo +nightly run --release --bin main -- --depth "$DEPTH"
    exit 0
fi

# Banner
echo -e "${BLUE}╔════════════════════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║${NC}  🤖 ${GREEN}CONTINUOUS AGENTIC FUZZING${NC}                                           ${BLUE}║${NC}"
echo -e "${BLUE}╠════════════════════════════════════════════════════════════════════════════╣${NC}"
echo -e "${BLUE}║${NC}  Refine interval: ${YELLOW}${REFINE_INTERVAL}${NC} executions                                      ${BLUE}║${NC}"
echo -e "${BLUE}║${NC}  Auto-apply: Top ${YELLOW}${AUTO_APPLY}${NC} suggestions                                        ${BLUE}║${NC}"
echo -e "${BLUE}║${NC}  Depth: ${YELLOW}${DEPTH}${NC}                                                              ${BLUE}║${NC}"
echo -e "${BLUE}║${NC}  Model: ${YELLOW}claude-opus-4-6${NC}                                                  ${BLUE}║${NC}"
echo -e "${BLUE}╠════════════════════════════════════════════════════════════════════════════╣${NC}"
echo -e "${BLUE}║${NC}  Press ${YELLOW}Ctrl+C${NC} to stop                                                      ${BLUE}║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════════════════════════════════╝${NC}"
echo ""

# Track generation
GENERATION=0

# Cleanup on exit
cleanup() {
    echo ""
    print_phase "🛑 STOPPING FUZZER" "🛑"
    echo -e "${GREEN}Completed ${GENERATION} refinement cycles${NC}"
    exit 0
}
trap cleanup INT TERM

# Main loop
while true; do
    GENERATION=$((GENERATION + 1))
    print_generation "$GENERATION"

    # Phase 1: Fuzz
    print_phase "PHASE 1: FUZZING (${REFINE_INTERVAL} executions)" "🔬"
    cd "$GENERATOR_DIR"

    # Count existing solutions
    BEFORE_COUNT=$(find solutions -name "result_*.lean" 2>/dev/null | wc -l | tr -d ' ')

    # Run fuzzer with timeout to limit executions
    # Estimate: ~2 exec/sec, so N executions ≈ N/2 seconds
    TIMEOUT=$((REFINE_INTERVAL / 2))
    echo -e "${CYAN}Running fuzzer for ~${TIMEOUT}s (targeting ${REFINE_INTERVAL} executions)...${NC}"

    timeout "${TIMEOUT}s" cargo +nightly run --release --bin main -- --depth "$DEPTH" 2>&1 | \
        grep -E "(NEW CATEGORY|🎯|!!!|executions:)" || true

    # Count new solutions
    AFTER_COUNT=$(find solutions -name "result_*.lean" 2>/dev/null | wc -l | tr -d ' ')
    NEW_SUCCESSES=$((AFTER_COUNT - BEFORE_COUNT))

    echo ""
    echo -e "${GREEN}✓ Fuzzing phase complete${NC}"
    echo -e "  New successes: ${YELLOW}${NEW_SUCCESSES}${NC}"
    echo -e "  Total solutions: ${YELLOW}${AFTER_COUNT}${NC}"

    # Phase 2: Analyze
    SUCCESS_DIR="$GENERATOR_DIR/solutions/lake_pass_comp_fail_safe_fail"
    if [ -d "$SUCCESS_DIR" ] && [ "$(ls -A "$SUCCESS_DIR" 2>/dev/null)" ]; then
        print_phase "PHASE 2: LLM ANALYSIS" "🧠"
        cd "$SCAFFOLD_DIR"

        echo -e "${CYAN}Analyzing successful prefixes with Claude Opus...${NC}"

        uv run scaffold refine-grammar \
            "$SUCCESS_DIR" \
            --output "../artifacts/grammar_suggestions_gen${GENERATION}.json" \
            --auto-apply "$AUTO_APPLY" 2>&1 | \
            grep -E "(Loading|Loaded|Analyzing|applying|Applied|HOT PATTERNS|SUGGESTED)" || true

        echo ""
        echo -e "${GREEN}✓ Analysis phase complete${NC}"

        # Phase 3: Rebuild
        print_phase "PHASE 3: REBUILDING FUZZER" "⚙️"
        cd "$GENERATOR_DIR"

        echo -e "${CYAN}Rebuilding fuzzer with improved grammar...${NC}"
        cargo build --release --bin main 2>&1 | tail -3

        echo ""
        echo -e "${GREEN}✓ Rebuild complete - fuzzer has evolved!${NC}"

    else
        echo -e "${YELLOW}⚠️  No successes yet, skipping refinement for this generation${NC}"
    fi

    # Brief pause before next generation
    sleep 2
done
