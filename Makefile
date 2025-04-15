SML = mosmlc

qtl: main.sml
	    $(SML) -o $@ $<

run: qtl
		cat prog | ./qtl