.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap -R . Pset5

rocq:
	$(ROCQ) Pset5Sig.v
	$(ROCQ) Pset5.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .*.cache *.vok *.vos