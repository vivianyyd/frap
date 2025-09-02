.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap

rocq:
	$(ROCQ) Pset1Signature.v
	$(ROCQ) Pset1Implementation.v

clean:
	rm -f *.vo *.glob
