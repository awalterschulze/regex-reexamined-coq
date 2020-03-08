build:
	coqc comparable.v
	coqc main.v

clean:
	(rm *.vo || true && rm *.glob || true && rm .*.aux || true)