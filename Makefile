# Lean 4 Soundness Fuzzer Makefile

# Configuration
JOBS ?= 4
DEPTH ?= 15

.PHONY: run build test clean help

# Default target: run parallel fuzzing
run: build
	@echo "[*] Starting $(JOBS) parallel fuzzer instances (depth=$(DEPTH))"
	@echo "[*] Press Ctrl+C to stop"
	@cd generator && \
	for i in $$(seq 1 $(JOBS)); do \
		RUST_LOG=warn cargo +nightly run --release --bin main -- --depth $(DEPTH) & \
	done; \
	trap 'kill $$(jobs -p) 2>/dev/null' EXIT; \
	wait

# Build the fuzzer
build:
	@cd generator && cargo +nightly build --release --bin main

# Run tests
test:
	@cd generator && cargo +nightly test

# Clean build artifacts
clean:
	@cd generator && cargo clean
	@rm -rf generator/solutions/type*

# Show usage
help:
	@echo "Lean 4 Soundness Fuzzer"
	@echo ""
	@echo "Targets:"
	@echo "  make run         - Run fuzzer with $(JOBS) parallel workers (default)"
	@echo "  make build       - Build the fuzzer"
	@echo "  make test        - Run tests"
	@echo "  make clean       - Clean build artifacts"
	@echo ""
	@echo "Configuration:"
	@echo "  JOBS=N           - Number of parallel workers (default: 4)"
	@echo "  DEPTH=N          - Tree depth for generation (default: 15)"
	@echo ""
	@echo "Examples:"
	@echo "  make run                    # Run with defaults (4 workers, depth 15)"
	@echo "  make run JOBS=8             # Run with 8 workers"
	@echo "  make run JOBS=2 DEPTH=10    # Run with 2 workers, depth 10"
