# LLM-Guided Grammar Refinement

Use Claude Opus to analyze successful fuzzer outputs and suggest grammar improvements.

## The Problem

With a **0.5% compile rate** (16 successes out of 3,227 executions), coverage-guided fuzzing struggles with sparse positive signal. Traditional fuzzing learns from thousands of executions, but we have very few successes to learn from.

## The Solution

Instead of statistical coverage tracking, use LLM analysis:

1. **Collect successes**: Run fuzzer, gather the ~16 prefixes that compiled
2. **Analyze with Opus**: Feed successes + grammar to Claude Opus 4
3. **Get suggestions**: Receive structured suggestions for grammar improvements
4. **Review & apply**: Manually review and apply approved changes

## Why This Works Better

| Coverage-Guided | LLM-Guided |
|----------------|-----------|
| Learns from 3,211 failures | Learns from 16 successes |
| Noisy signal (99.5% failures) | High signal (100% successes) |
| Requires dense feedback | Works with sparse data |
| Statistical patterns only | Semantic understanding |
| Can't explain "why" | Provides reasoning |

## Usage

### 1. Run Fuzzer and Collect Successes

```bash
cd generator
cargo +nightly run --release --bin main -- --depth 10

# Successful prefixes are saved to:
# solutions/lake_pass_comp_fail_safe_fail/result_*.lean
```

### 2. Analyze with LLM

```bash
cd scaffold
export ANTHROPIC_API_KEY="sk-ant-..."

uv run scaffold refine-grammar \
    ../generator/solutions/lake_pass_comp_fail_safe_fail/ \
    --output ../artifacts/grammar_suggestions.json
```

This will:
- Load all successful `.lean` files from the directory
- Extract current grammar rules from `generator/src/grammar.rs`
- Send to Claude Opus 4-6 for analysis
- Save structured suggestions to JSON
- Print summary to console

### 3. Review Suggestions

```bash
cat ../artifacts/grammar_suggestions.json | jq
```

Output format:
```json
{
  "analysis": "Brief analysis of patterns...",
  "hot_patterns": [
    "Pattern that appears in successes",
    "Another effective pattern"
  ],
  "cold_rules": [
    "RULE_NAME_1",
    "RULE_NAME_2"
  ],
  "suggested_rules": [
    {
      "nonterminal": "NEW_RULE",
      "expansion": "{SOMETHING} pattern here",
      "reason": "Why this would help",
      "priority": 8
    }
  ],
  "priority_changes": [
    "Most important change to make",
    "Second priority change"
  ]
}
```

### 4. Apply Approved Changes

Review the suggestions and manually apply approved changes to `generator/src/grammar.rs`:

```rust
// Example: Add suggested rule
("NEW_RULE", "{PATTERN} that {WORKS}"),
```

### 5. Test Improvements

```bash
cd generator
cargo build --release --bin main
cargo +nightly run --release --bin main -- --depth 10

# Monitor if success rate improves!
```

## Example Session

```bash
$ uv run scaffold refine-grammar ../generator/solutions/lake_pass_comp_fail_safe_fail/

Loading successful prefixes from ../generator/solutions/lake_pass_comp_fail_safe_fail/...
✓ Loaded 16 successful prefixes
Loading grammar from ../generator/src/grammar.rs...
✓ Loaded grammar (45821 chars)

Analyzing with Claude Opus (model: claude-opus-4-6, ~3211 failures)...
This may take 30-60 seconds...

================================================================================
📊 GRAMMAR ANALYSIS SUMMARY
================================================================================

The successful prefixes show consistent use of @[simp] attributes combined with
simple False propositions. The fuzzer discovered that simp_all can leverage
marked simp lemmas to attempt False proofs.

🔥 HOT PATTERNS (what works):
  1. @[simp] theorem <name> : False := sorry
  2. Simple imports (Lean, Lean.Meta) without heavy dependencies
  3. set_option declarations (relaxedAutoImplicit, maxHeartbeats)
  4. Basic inductive types without complex positivity requirements

❄️  COLD RULES (candidates for removal):
  - DERIVING
  - INSTANCE_DECL
  - MUTUAL_BLOCK

💡 SUGGESTED NEW RULES (5):
  1. [9/10] SIMP_THEOREM
     → @[simp] theorem {ID} : {SIMPLE_PROP} := sorry
     Reason: 80% of successes use @[simp] + False/conjunction props

  2. [8/10] MINIMAL_IMPORTS
     → import {LEAN_MODULE}
     Reason: Successes use minimal imports (Lean, Lean.Meta, Lean.Elab)

  ...

🎯 PRIORITY CHANGES:
  1. Add SIMP_THEOREM rule targeting @[simp] False declarations
  2. Remove DERIVING (never compiles, 15+ uses with 0 successes)
  3. Simplify INDUCTIVE_DECL to avoid positivity failures

================================================================================

✓ Saved analysis to ../artifacts/grammar_suggestions.json

✅ Analysis complete! Review suggestions in ../artifacts/grammar_suggestions.json

Next steps:
  1. Review the suggestions in the JSON file
  2. Manually apply approved changes to generator/src/grammar.rs
  3. Run fuzzer again to test improvements
```

## Configuration

All configuration via CLI options:

- `--limit`: Max successes to analyze (default: 50, to avoid token limits)
- `--grammar-path`: Path to grammar.rs (default: auto-detected from monorepo)
- `--output`: Where to save JSON (default: `artifacts/grammar_suggestions.json`)
- `--api-key`: Anthropic API key (or use `ANTHROPIC_API_KEY` env var)

## Cost Estimate

Using Claude Opus 4-6:
- Input: ~50KB (grammar + 16 success examples)
- Output: ~2KB (structured suggestions)
- Cost: ~$0.15 per analysis
- Time: 30-60 seconds

## Iterative Refinement

Run this after each fuzzing campaign to continuously improve the grammar:

```bash
# Campaign 1
fuzz → 0.5% success → analyze → apply changes → rebuild

# Campaign 2
fuzz → 1.2% success → analyze → apply changes → rebuild

# Campaign 3
fuzz → 2.8% success → analyze → apply changes → rebuild
...
```

## Tips

1. **Start with high-priority suggestions**: Apply the top 2-3 first
2. **Test incrementally**: Don't apply all suggestions at once
3. **Track success rate**: Monitor if changes actually improve compilation rate
4. **Use varied depths**: Run fuzzer at different depths (5, 10, 15, 20) to collect diverse successes
5. **Batch analysis**: Collect successes from multiple runs before analyzing (more data = better suggestions)
