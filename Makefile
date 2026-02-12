# Lean 4 Soundness Fuzzer Makefile

# Configuration
JOBS ?= 1
DEPTH ?= 15
REFINE_INTERVAL ?= 100
AUTO_APPLY ?= 3

.PHONY: run run-continuous build test clean help deps

# Lean version (must match across all tools for .olean compatibility)
LEAN_VERSION ?= v4.27.0

# Specific commits for each tool at v4.27.0 (most recent before 4.28 bump)
COMPARATOR_REF ?= 6c40ab4
LEAN4EXPORT_REF ?= 56030ca
SAFEVERIFY_REF ?= dbe482f

# Default target: run parallel fuzzing
run: build
	@echo "[*] Starting $(JOBS) parallel fuzzer workers (depth=$(DEPTH))"
	@echo "[*] Workers share corpus via LibAFL LLMP"
	@echo "[*] Press Ctrl+C to stop (will save reports)"
	@cd generator && \
	for i in $$(seq 1 $(JOBS)); do \
		echo "[*] Starting worker $$i/$(JOBS)..."; \
		RUST_LOG=warn ./target/release/main --depth $(DEPTH) & \
		sleep 0.2; \
	done; \
	wait

# Run continuous agentic fuzzing with LLM-guided grammar refinement
run-continuous: build
	@echo "[*] Starting continuous agentic fuzzing"
	@echo "[*] Refine interval: $(REFINE_INTERVAL) executions"
	@echo "[*] Auto-apply: Top $(AUTO_APPLY) suggestions"
	@echo "[*] Depth: $(DEPTH)"
	@echo "[*] Press Ctrl+C to stop"
	@REFINE_INTERVAL=$(REFINE_INTERVAL) \
	 DEPTH=$(DEPTH) \
	 AUTO_APPLY=$(AUTO_APPLY) \
	 ./scripts/continuous_fuzz.sh

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

# Install all dependencies with version pinning
deps:
	@echo "[*] Installing dependencies for Lean $(LEAN_VERSION)"
	@mkdir -p ../
	@# Clone and build lean4export
	@if [ ! -d "../lean4export" ]; then \
		echo "[*] Cloning lean4export..."; \
		cd .. && git clone https://github.com/leanprover/lean4export.git; \
	fi
	@echo "[*] Building lean4export at $(LEAN4EXPORT_REF) ($(LEAN_VERSION))..."
	@cd ../lean4export && \
		git fetch && git checkout $(LEAN4EXPORT_REF) && \
		lake build
	@# Clone and build comparator
	@if [ ! -d "../comparator" ]; then \
		echo "[*] Cloning comparator..."; \
		cd .. && git clone https://github.com/leanprover/comparator.git; \
	fi
	@echo "[*] Building comparator at $(COMPARATOR_REF) ($(LEAN_VERSION))..."
	@cd ../comparator && \
		git fetch && git checkout $(COMPARATOR_REF) && \
		lake build
	@# Clone and build safeverify
	@if [ ! -d "../safeverify" ]; then \
		echo "[*] Cloning safeverify..."; \
		cd .. && git clone https://github.com/gasstationmanager/safeverify.git; \
	fi
	@echo "[*] Building safeverify at $(SAFEVERIFY_REF) ($(LEAN_VERSION))..."
	@cd ../safeverify && \
		git fetch && git checkout $(SAFEVERIFY_REF) && \
		lake build safe_verify:exe
	@# Clone lean4 source (optional)
	@if [ ! -d "lean4" ]; then \
		echo "[*] Cloning lean4 source..."; \
		git clone https://github.com/leanprover/lean4.git lean4; \
	fi
	@# Create .env
	@if [ ! -f ".env" ]; then \
		echo "[*] Creating .env..."; \
		cp .env.example .env; \
		sed -i.bak 's|./../../../|../|g' .env && rm .env.bak; \
	fi
	@echo ""
	@echo "[*] ✅ Dependencies installed!"
	@echo "[*] Verifying binaries..."
	@[ -f "../lean4export/.lake/build/bin/lean4export" ] && echo "  ✓ lean4export" || echo "  ✗ lean4export FAILED"
	@[ -f "../comparator/.lake/build/bin/comparator" ] && echo "  ✓ comparator" || echo "  ✗ comparator FAILED"
	@[ -f "../safeverify/.lake/build/bin/safe_verify" ] && echo "  ✓ safeverify" || echo "  ✗ safeverify FAILED"
	@echo ""
	@echo "Run 'make run' to start fuzzing!"

# Show usage
help:
	@echo "Lean 4 Soundness Fuzzer"
	@echo ""
	@echo "Targets:"
	@echo "  make deps           - Install all dependencies (comparator, safeverify, etc.)"
	@echo "  make run            - Run fuzzer with $(JOBS) parallel workers"
	@echo "  make run-continuous - Run continuous agentic fuzzing with LLM refinement"
	@echo "  make build          - Build the fuzzer"
	@echo "  make test           - Run tests"
	@echo "  make clean          - Clean build artifacts"
	@echo ""
	@echo "Configuration:"
	@echo "  LEAN_VERSION=v      - Lean version for all tools (default: $(LEAN_VERSION))"
	@echo "  JOBS=N              - Number of parallel workers (default: $(JOBS))"
	@echo "  DEPTH=N             - Tree depth for generation (default: $(DEPTH))"
	@echo "  REFINE_INTERVAL=N   - Executions between refinements (default: $(REFINE_INTERVAL))"
	@echo "  AUTO_APPLY=N        - Auto-apply top N suggestions (default: $(AUTO_APPLY))"
	@echo ""
	@echo "Examples:"
	@echo "  make deps                                    # One-time setup"
	@echo "  make run                                     # Run with defaults"
	@echo "  make run JOBS=8                              # 8 parallel workers"
	@echo "  export ANTHROPIC_API_KEY=sk-ant-..."
	@echo "  make run-continuous REFINE_INTERVAL=100     # Continuous refinement"
