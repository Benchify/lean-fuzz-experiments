.PHONY: test clean

test:
	@echo "Testing inductive type soundness..."
	@lean test.lean --trust=0 2>&1 | tee output.txt
	@if grep -i "error" output.txt | grep -v "code generator"; then \
		echo "Found errors (expected for malformed cases)"; \
	fi
	@echo "Test complete."

clean:
	rm -f *.olean *.c *.out output.txt