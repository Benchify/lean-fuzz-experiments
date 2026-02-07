.PHONY: test clean

test:
	@python3 test.py 2>&1 | tee output.txt

clean:
	rm -f *.lean *.olean* *.c *.out output.txt test_import.lean