.PHONY: test clean

test:
	@echo "Testing native code generation..."
	@lean test.lean 2>&1 | tee output.txt
	@echo "Compiling to executable..."
	@lean --c=test.c test.lean 2>&1 | tee -a output.txt || true

clean:
	rm -f *.olean *.c *.out *.o output.txt