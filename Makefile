build:
	coqc comparable.v
	coqc regex.v

clean:
	(rm *.vo || true && rm *.glob || true && rm .*.aux || true)