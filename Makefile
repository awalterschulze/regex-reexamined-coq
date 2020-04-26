build:
	coqc orb_simple.v

	coqc comparable.v
	coqc sort.v
	coqc dup.v
	coqc compare_nat.v
	coqc reorder.v

	coqc regex.v
	coqc size.v
	coqc nullable.v
	coqc compare_regex.v
	coqc reduce_orb.v

	coqc matches_pred.v
	coqc derive_def.v
	coqc setoid.v
	coqc derive.v
	coqc smart_or.v
	coqc smart.v
	coqc simplified.v
	coqc simple.v

	coqc main.v

clean:
	( rm *.vo \
	; rm *.glob \
	; rm .*.aux \
	; rm *.vok \
	; rm *.vos \
	|| true)
