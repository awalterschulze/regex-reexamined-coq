build:
	coqc comparable.v
	coqc regex.v
	coqc compare_regex.v
	coqc main.v

clean:
	(rm *.vo || true && rm *.glob || true && rm .*.aux || true)