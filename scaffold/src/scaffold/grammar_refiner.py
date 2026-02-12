"""LLM-guided grammar refinement for fuzzing.

Analyzes successful fuzzer outputs to identify effective grammar patterns
and suggest improvements using Claude Opus.
"""

import json
from pathlib import Path
from typing import Any

import anthropic
from pydantic import BaseModel


class RuleSuggestion(BaseModel):
    """A suggested grammar rule addition or modification."""

    nonterminal: str
    expansion: str
    reason: str
    priority: int = 5  # 1-10, higher = more important


class GrammarAnalysis(BaseModel):
    """LLM analysis of grammar effectiveness."""

    analysis: str
    hot_patterns: list[str]
    cold_rules: list[str]
    suggested_rules: list[RuleSuggestion]
    priority_changes: list[str]


def load_successful_prefixes(success_dir: Path, limit: int = 50) -> list[str]:
    """Load successful Lean prefixes from solutions directory.

    Args:
        success_dir: Directory containing result_*.lean files
        limit: Maximum number of successes to load (to avoid token limits)

    Returns:
        List of Lean code strings that successfully compiled
    """
    lean_files = sorted(success_dir.glob("result_*.lean"))[:limit]
    prefixes = []

    for file in lean_files:
        try:
            code = file.read_text()
            prefixes.append(code)
        except Exception as e:
            print(f"Warning: Could not read {file}: {e}")

    return prefixes


def load_grammar_rules(grammar_path: Path) -> str:
    """Extract grammar rules from grammar.rs file.

    Args:
        grammar_path: Path to generator/src/grammar.rs

    Returns:
        String representation of grammar rules for LLM analysis
    """
    content = grammar_path.read_text()

    # Extract the rules_raw() function body
    start = content.find("fn rules_raw()") or content.find("fn prefix_rules_raw()")
    if start == -1:
        msg = "Could not find rules_raw() or prefix_rules_raw() in grammar.rs"
        raise ValueError(msg)

    # Find the vec![ ... ] block
    vec_start = content.find("vec![", start)
    if vec_start == -1:
        msg = "Could not find vec![ in grammar function"
        raise ValueError(msg)

    # Find matching closing bracket (simple heuristic - count brackets)
    depth = 0
    i = vec_start
    while i < len(content):
        if content[i] == "[":
            depth += 1
        elif content[i] == "]":
            depth -= 1
            if depth == 0:
                break
        i += 1

    if depth != 0:
        msg = "Could not find matching ] for vec!["
        raise ValueError(msg)

    rules_block = content[vec_start : i + 1]
    return rules_block


def analyze_with_llm(
    successes: list[str],
    grammar: str,
    failed_count: int,
    api_key: str | None = None,
    model: str = "claude-opus-4-6",
) -> GrammarAnalysis:
    """Ask Claude Opus to analyze successful patterns and suggest improvements.

    Args:
        successes: List of Lean code that successfully compiled
        grammar: Current grammar rules as string
        failed_count: Number of failed executions for context
        api_key: Anthropic API key (or use ANTHROPIC_API_KEY env var)
        model: Model to use for analysis

    Returns:
        Structured analysis with suggestions
    """
    client = anthropic.Anthropic(api_key=api_key)

    success_rate = len(successes) / (len(successes) + failed_count) * 100
    examples = "\n\n".join(
        f"--- Success Example {i+1} ---\n{code}" for i, code in enumerate(successes[:20])
    )

    prompt = f"""You are helping improve a grammar-based fuzzer for Lean 4 that targets soundness bugs.

CURRENT GRAMMAR (Lean 4 CFG rules):
{grammar}

SUCCESSFUL PREFIXES ({len(successes)} compiled and passed tests, {success_rate:.1f}% success rate):
{examples}

FAILED CASES: {failed_count} ({100-success_rate:.1f}% failure rate)

CONTEXT:
- We're fuzzing Lean 4's kernel for soundness bugs
- Target areas: universe levels, inductive types, termination checking, type classes
- Prefixes are declarations only (theorems use `sorry` placeholder)
- Golden suffixes are appended later: `theorem soundness_check : False := by <tactic>`

TASK:
Analyze the successful prefixes to identify patterns that work and suggest grammar improvements.

1. What patterns appear in successes? (e.g., specific attribute combinations, declaration types, imports)
2. Which grammar rules seem effective vs underused/broken?
3. What's missing from the grammar that could improve success rate?
4. Suggest specific new rules or modifications

Focus on:
- Rules that exercise the kernel deeply (universe polymorphism, complex inductives)
- Combinations that create "interesting" environments for False proofs
- Removing or fixing rules that likely never compile

Respond with valid JSON matching this schema:
{{
  "analysis": "Brief analysis of success patterns and grammar effectiveness",
  "hot_patterns": ["Pattern 1 that works", "Pattern 2 that works", ...],
  "cold_rules": ["RULE_NAME_1", "RULE_NAME_2"],
  "suggested_rules": [
    {{
      "nonterminal": "NONTERMINAL_NAME",
      "expansion": "{{NONTERMINAL}} or literal text",
      "reason": "Why this rule would help",
      "priority": 8
    }}
  ],
  "priority_changes": ["Most important change 1", "Most important change 2", ...]
}}

Provide 5-10 high-quality suggestions prioritized by expected impact."""

    response = client.messages.create(
        model=model, max_tokens=8000, messages=[{"role": "user", "content": prompt}]
    )

    # Extract JSON from response (may be wrapped in markdown code blocks)
    content = response.content[0].text
    if "```json" in content:
        content = content.split("```json")[1].split("```")[0].strip()
    elif "```" in content:
        content = content.split("```")[1].split("```")[0].strip()

    result = json.loads(content)
    return GrammarAnalysis(**result)


def save_analysis(analysis: GrammarAnalysis, output_path: Path) -> None:
    """Save analysis results to JSON file.

    Args:
        analysis: Grammar analysis from LLM
        output_path: Where to save JSON output
    """
    output_path.write_text(analysis.model_dump_json(indent=2))
    print(f"✓ Saved analysis to {output_path}")


def print_analysis_summary(analysis: GrammarAnalysis) -> None:
    """Pretty-print analysis summary to console.

    Args:
        analysis: Grammar analysis to display
    """
    print("\n" + "=" * 80)
    print("📊 GRAMMAR ANALYSIS SUMMARY")
    print("=" * 80)

    print(f"\n{analysis.analysis}\n")

    print("🔥 HOT PATTERNS (what works):")
    for i, pattern in enumerate(analysis.hot_patterns, 1):
        print(f"  {i}. {pattern}")

    if analysis.cold_rules:
        print("\n❄️  COLD RULES (candidates for removal):")
        for rule in analysis.cold_rules[:10]:
            print(f"  - {rule}")

    print(f"\n💡 SUGGESTED NEW RULES ({len(analysis.suggested_rules)}):")
    for i, suggestion in enumerate(
        sorted(analysis.suggested_rules, key=lambda x: x.priority, reverse=True)[:5], 1
    ):
        print(f"  {i}. [{suggestion.priority}/10] {suggestion.nonterminal}")
        print(f"     → {suggestion.expansion}")
        print(f"     Reason: {suggestion.reason}\n")

    print("🎯 PRIORITY CHANGES:")
    for i, change in enumerate(analysis.priority_changes, 1):
        print(f"  {i}. {change}")

    print("\n" + "=" * 80)


def apply_suggestions(
    analysis: GrammarAnalysis, grammar_path: Path, top_n: int = 3
) -> list[str]:
    """Apply top N suggestions to grammar file.

    Args:
        analysis: Grammar analysis with suggestions
        grammar_path: Path to grammar.rs to modify
        top_n: Number of top-priority suggestions to apply

    Returns:
        List of changes made (for logging)
    """
    if not analysis.suggested_rules:
        return []

    # Sort by priority and take top N
    top_suggestions = sorted(
        analysis.suggested_rules, key=lambda x: x.priority, reverse=True
    )[:top_n]

    content = grammar_path.read_text()
    changes = []

    # Find the prefix_rules_raw() function to add rules
    marker = "fn prefix_rules_raw() -> Vec<(&'static str, &'static str)> {"
    if marker not in content:
        msg = "Could not find prefix_rules_raw() function in grammar.rs"
        raise ValueError(msg)

    # Find the vec![ opening
    vec_start = content.find("vec![", content.find(marker))
    if vec_start == -1:
        msg = "Could not find vec![ in prefix_rules_raw()"
        raise ValueError(msg)

    # Add new rules after the vec![ line
    insertion_point = content.find("\n", vec_start) + 1

    new_rules = []
    for suggestion in top_suggestions:
        # Escape the expansion properly for Rust strings
        expansion = suggestion.expansion.replace('"', '\\"')
        rule = f'        ("{suggestion.nonterminal}", "{expansion}"),  // Auto-added: {suggestion.reason[:60]}'
        new_rules.append(rule)
        changes.append(f"Added {suggestion.nonterminal}: {suggestion.expansion[:50]}...")

    # Insert the new rules
    new_content = (
        content[:insertion_point]
        + "\n        // === AUTO-GENERATED RULES (LLM suggestions) ===\n"
        + "\n".join(new_rules)
        + "\n        // === END AUTO-GENERATED RULES ===\n\n"
        + content[insertion_point:]
    )

    # Write back
    grammar_path.write_text(new_content)

    return changes
