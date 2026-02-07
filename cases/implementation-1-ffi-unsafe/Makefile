.PHONY: test clean

test:
	@echo "Testing FFI and unsafe code..."
	@lean test.lean --trust=0 2>&1 | tee output.txt
	@if grep -q "unsafe" output.txt; then \
		echo "Unsafe code detected - verify it cannot affect soundness"; \
	fi

clean:
	rm -f *.olean *.c *.out output.txt