SML = mosmlc

qtl: main.sml
	$(SML) -o $@ -toplevel $<

run: qtl
	cat prog | ./qtl