"""Campaign summary report generation from diagnostic JSONL logs."""

import json
from collections import Counter, defaultdict
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any

from rich.console import Console
from rich.table import Table as RichTable

from scaffold.models import DiagnosticRecord, ErrorCategory, Verdict


def generate_campaign_summary(log_path: Path) -> str:
    """Generate a markdown summary from a diagnostic JSONL log.

    Args:
        log_path: Path to the .jsonl diagnostic log file

    Returns:
        Markdown-formatted campaign summary
    """
    records = _load_records(log_path)
    if not records:
        return "# Campaign Summary\n\nNo records found."

    total = len(records)
    unique_prefixes = len(set(r.prefix_hash for r in records))

    # Time range
    start_time = min(r.timestamp for r in records)
    end_time = max(r.timestamp for r in records)
    duration = end_time - start_time

    # Verdict distribution
    verdict_counts = Counter(r.verdict for r in records)

    # Error category histogram
    error_counts: Counter[ErrorCategory] = Counter()
    for record in records:
        error_counts.update(record.error_categories)

    # Suffix breakdown
    suffix_stats = _analyze_suffixes(records)

    # Build summary
    lines = [
        f"# Campaign Summary",
        f"",
        f"**Session:** `{records[0].session_id}`",
        f"**Started:** {start_time.strftime('%Y-%m-%d %H:%M:%S UTC')}",
        f"**Ended:** {end_time.strftime('%Y-%m-%d %H:%M:%S UTC')}",
        f"**Duration:** {_format_duration(duration)}",
        f"",
        f"## Overview",
        f"",
        f"- **Total executions:** {total:,}",
        f"- **Unique prefixes:** {unique_prefixes:,}",
        f"- **Executions per minute:** {total / max(duration.total_seconds() / 60, 1):.1f}",
        f"",
        f"## Verdict Distribution",
        f"",
    ]

    for verdict in [Verdict.GOLDEN, Verdict.BUILD_FAILED, Verdict.TIMEOUT, Verdict.FALSE_POSITIVE]:
        count = verdict_counts[verdict]
        if count > 0:
            pct = (count / total) * 100
            icon = "🎯" if verdict == Verdict.GOLDEN else ""
            lines.append(f"- **{verdict.value}:** {count:,} ({pct:.1f}%) {icon}")

    if verdict_counts[Verdict.GOLDEN] > 0:
        lines.extend([
            f"",
            f"### 🎯 Golden Signals!",
            f"",
            f"Found {verdict_counts[Verdict.GOLDEN]} potential soundness bug(s)!",
            f"Check `artifacts/golden-signals/` for details.",
        ])

    # Error categories (top 10)
    if error_counts:
        lines.extend([
            f"",
            f"## Error Categories (Top 10)",
            f"",
        ])
        for category, count in error_counts.most_common(10):
            pct = (count / total) * 100
            lines.append(f"- **{category.value}:** {count:,} ({pct:.1f}%)")

    # Suffix breakdown with rich table
    if suffix_stats:
        lines.extend([
            f"",
            f"## Golden Suffix Performance",
            f"",
        ])

        # Create rich table for pretty formatting
        console = Console(record=True, force_terminal=False)
        table = RichTable(show_header=True, header_style="bold")
        table.add_column("Suffix", style="cyan")
        table.add_column("Tests", justify="right")
        table.add_column("Build Success", justify="right")
        table.add_column("Avg Errors", justify="right")

        for suffix_name, stats in sorted(suffix_stats.items()):
            success_rate = (stats['build_success'] / stats['count']) * 100 if stats['count'] > 0 else 0
            avg_errors = stats['total_errors'] / stats['count'] if stats['count'] > 0 else 0

            table.add_row(
                suffix_name,
                str(stats['count']),
                f"{success_rate:.0f}%",
                f"{avg_errors:.1f}",
            )

        # Render table as text and add to markdown
        with console.capture() as capture:
            console.print(table)
        lines.extend([
            "```",
            capture.get(),
            "```",
        ])

    return "\n".join(lines)


def _load_records(log_path: Path) -> list[DiagnosticRecord]:
    """Load all records from a JSONL file."""
    records = []
    with open(log_path) as f:
        for line in f:
            if line.strip():
                data = json.loads(line)
                records.append(DiagnosticRecord(**data))
    return records


def _analyze_suffixes(records: list[DiagnosticRecord]) -> dict[str, dict[str, Any]]:
    """Analyze per-suffix statistics."""
    suffix_stats: dict[str, dict[str, Any]] = defaultdict(lambda: {
        'count': 0,
        'build_success': 0,
        'total_errors': 0,
    })

    for record in records:
        suffix = record.suffix_name
        suffix_stats[suffix]['count'] += 1
        if record.verdict != Verdict.BUILD_FAILED:
            suffix_stats[suffix]['build_success'] += 1
        suffix_stats[suffix]['total_errors'] += len(record.error_categories)

    return dict(suffix_stats)


def _format_duration(delta: timedelta) -> str:
    """Format timedelta as human-readable string."""
    hours, remainder = divmod(delta.total_seconds(), 3600)
    minutes, seconds = divmod(remainder, 60)

    parts = []
    if hours >= 1:
        parts.append(f"{int(hours)}h")
    if minutes >= 1:
        parts.append(f"{int(minutes)}m")
    if seconds >= 1 or not parts:
        parts.append(f"{int(seconds)}s")

    return " ".join(parts)
