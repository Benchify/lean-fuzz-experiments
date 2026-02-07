.PHONY: test clean

test:
	@echo "Testing stack overflow resilience..."
	@lean test.lean -s 1024 2>&1 | tee output.txt
	@echo "Testing with minimal stack..."
	@lean test.lean -s 256 2>&1 | tee -a output.txt || true
	@echo "Test complete. Check for crashes."

clean:
	rm -f *.olean *.c *.out output.txt