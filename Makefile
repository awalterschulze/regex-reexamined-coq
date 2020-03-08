build:
	coqc comparable.v
	coqc regex.v
	coqc nullable.v
	coqc derive.v
	coqc compare_regex.v
	coqc smart.v
	coqc simplified.v
	coqc main.v

clean:
	(rm *.vo || true && rm *.glob || true && rm .*.aux || true)