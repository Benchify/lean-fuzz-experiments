.PHONY: test clean

test:
	@echo "Testing typeclass elaboration soundness..."
	@lean test.lean --trust=0 2>&1 | tee output.txt

clean:
	rm -f *.olean *.c *.out output.txt