.PHONY: test clean

test:
	@echo "Differential testing: VM vs Kernel..."
	@lean test.lean 2>&1 | tee output.txt
	@echo "Checking for discrepancies..."
	@if grep -q "error" output.txt; then \
		echo "Found errors - investigate discrepancies"; \
	fi

clean:
	rm -f *.olean *.c *.out output.txt