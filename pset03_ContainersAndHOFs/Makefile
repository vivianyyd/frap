.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap -R . Pset3

rocq:
	$(ROCQ) Pset3Sig.v
	$(ROCQ) Pset3.v

clean:
	rm -f *.vo *.glob .*.aux *.aux .lia.cache .nia.cache *.vok *.vos