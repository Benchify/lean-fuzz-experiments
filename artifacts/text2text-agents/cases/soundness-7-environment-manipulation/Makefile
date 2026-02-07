.PHONY: test clean

test:
	@echo "Testing environment manipulation..."
	@lean test.lean --trust=0 2>&1 | tee output.txt
	@if grep -i "axiom" output.txt | grep -i "dangerous"; then \
		echo "⚠️  Detected dangerous axiom - verify it's properly tracked"; \
	fi

clean:
	rm -f *.olean *.c *.out output.txt