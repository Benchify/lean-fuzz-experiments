.PHONY: test clean

test:
	@./fuzz-input.sh 2>&1 | tee output.txt

clean:
	rm -f *.lean *.olean *.c *.out output.txt