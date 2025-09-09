.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap

rocq:
	$(ROCQ) Pset2Sig.v
	$(ROCQ) Pset2.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .lia.cache .nia.cache *.vok *.vos
