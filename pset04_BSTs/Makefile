.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap -R . Pset4

coq:
	$(ROCQ) Pset4Sig.v
	$(ROCQ) Pset4.v

clean:
	rm -f *.vo* .*.aux *.cache *.glob