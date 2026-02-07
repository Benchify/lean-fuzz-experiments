.PHONY: test clean

test:
	@echo "Testing recursive definition soundness..."
	@lean test.lean --trust=0 2>&1 | tee output.txt
	@echo "Test completed. Check output.txt for results."

clean:
	rm -f *.olean *.c *.out output.txt