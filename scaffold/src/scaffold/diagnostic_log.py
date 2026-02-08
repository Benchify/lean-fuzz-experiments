"""Append-only JSONL logger for build diagnostics.

One instance per fuzz session. Each record is a single line in the log file.
"""

import hashlib
import logging
from datetime import UTC, datetime
from pathlib import Path

from scaffold.diagnostics import summary_categories
from scaffold.executor import MONOREPO
from scaffold.models import DiagnosticRecord, OracleResult

logger = logging.getLogger(__name__)

_DEFAULT_LOG_DIR = MONOREPO / "artifacts" / "diagnostics"


class DiagnosticLogger:
    """Append-only JSONL logger for diagnostic records."""

    def __init__(
        self,
        session_id: str | None = None,
        log_dir: Path | None = None,
    ) -> None:
        """Initialize the logger.

        Args:
            session_id: Unique session identifier. Defaults to timestamp + PID.
            log_dir: Directory for log files. Defaults to artifacts/diagnostics/.
        """
        import os

        if session_id is None:
            ts = datetime.now(tz=UTC).strftime("%Y%m%d_%H%M%S")
            session_id = f"{ts}_{os.getpid()}"

        self.session_id = session_id
        self.log_dir = log_dir or _DEFAULT_LOG_DIR
        self.log_dir.mkdir(parents=True, exist_ok=True)
        self.log_path = self.log_dir / f"{self.session_id}.jsonl"

    def log(self, prefix: str, result: OracleResult) -> None:
        """Append a diagnostic record for one prefix+suffix result.

        Args:
            prefix: The fuzzer-generated prefix code.
            result: Oracle result from testing that prefix.
        """
        prefix_hash = hashlib.sha256(prefix.encode()).hexdigest()[:12]
        categories = summary_categories(result.diagnostics)

        record = DiagnosticRecord(
            timestamp=datetime.now(tz=UTC),
            session_id=self.session_id,
            prefix_hash=prefix_hash,
            suffix_name=result.suffix_name,
            verdict=result.verdict,
            exit_code=result.exit_code,
            error_categories=categories,
            diagnostics=result.diagnostics,
            raw_stderr=result.raw_stderr,
            prefix_snippet=prefix[:500],
        )

        with open(self.log_path, "a") as f:
            f.write(record.model_dump_json() + "\n")
