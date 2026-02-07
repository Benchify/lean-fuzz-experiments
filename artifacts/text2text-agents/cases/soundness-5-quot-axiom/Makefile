.PHONY: test clean

test:
	@echo "Testing quotient types and axiom soundness..."
	@lean test.lean --trust=0 2>&1 | tee output.txt
	@echo "Checking axiom usage..."
	@lean test.lean --trust=0 2>&1 | grep -i "axiom" || echo "No additional axioms detected"

clean:
	rm -f *.olean *.c *.out output.txt