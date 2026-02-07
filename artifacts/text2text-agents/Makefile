.PHONY: all clean fuzz help

# Default target
all: help

help:
	@echo "Lean 4 Security Audit - Test Harness"
	@echo ""
	@echo "Available targets:"
	@echo "  make test-soundness    - Run soundness bug tests"
	@echo "  make test-parser       - Run parser fuzzing tests"
	@echo "  make test-resource     - Run resource exhaustion tests"
	@echo "  make test-serialize    - Run serialization tests"
	@echo "  make test-all          - Run all test suites"
	@echo "  make case-N            - Run specific case (e.g., make case-1)"
	@echo "  make fuzz              - Run fuzzing campaigns"
	@echo "  make clean             - Clean generated artifacts"

test-all: test-soundness test-parser test-resource test-serialize

test-soundness:
	@echo "Running soundness tests..."
	@for case in cases/soundness-*; do \
		if [ -d "$$case" ]; then \
			echo "Testing $$case..."; \
			make -C "$$case" test 2>&1 || true; \
		fi \
	done

test-parser:
	@echo "Running parser tests..."
	@for case in cases/parser-*; do \
		if [ -d "$$case" ]; then \
			echo "Testing $$case..."; \
			make -C "$$case" test 2>&1 || true; \
		fi \
	done

test-resource:
	@echo "Running resource exhaustion tests..."
	@for case in cases/resource-*; do \
		if [ -d "$$case" ]; then \
			echo "Testing $$case..."; \
			make -C "$$case" test 2>&1 || true; \
		fi \
	done

test-serialize:
	@echo "Running serialization tests..."
	@for case in cases/serialize-*; do \
		if [ -d "$$case" ]; then \
			echo "Testing $$case..."; \
			make -C "$$case" test 2>&1 || true; \
		fi \
	done

case-%:
	@if [ -d "cases/case-$*" ]; then \
		make -C "cases/case-$*" test; \
	else \
		echo "Case $* not found"; \
		exit 1; \
	fi

fuzz:
	@echo "Running fuzzing campaigns..."
	@cd fuzz-harnesses && ./run-fuzz.sh

clean:
	@echo "Cleaning artifacts..."
	@find cases -name "*.olean" -delete
	@find cases -name "*.c" -delete
	@find cases -name "*.out" -delete
	@rm -rf fuzz-harnesses/corpus fuzz-harnesses/crashes