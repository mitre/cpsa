# Makefile rules for CPSA

# Suggested CPSA flags include a memory use limit:
# CPSAFLAGS = +RTS -M512m -N -RTS

# Analyze protocols for shapes
%.txt:		%.scm
	$(CPSATIME) cpsa4 $(CPSAFLAGS) -o $@ $<

# Preprocess by transforming defprot forms into defprotocol
%.scm:		%.prot
	cpsa4prot $(CPSAPROTFLAGS) -o $@ $<

# Analyze protocols for shapes, but don't fail when CPSA does
%.txt:		%.lsp
	-$(CPSATIME) cpsa4 $(CPSAFLAGS) -o $@ $<

# Use .text for intermediat analyses with lemmas that will get deleted
%.text:		%.scm 
	$(CPSATIME) cpsa4 $(CPSAFLAGS) -o $@ $<

# Extract shapes
%_shapes.txt:	%.txt
	cpsa4shapes $(SHAPESFLAGS) -o $@ $<

# Extract shape analysis sentences
%_sas.text:	%.txt
	cpsa4sas $(SASFLAGS) -o $@ $<

# Visualize output using the expanded format (default)
%.xhtml:	%.txt
	cpsa4graph $(GRAPHFLAGS) -o $@ $<

# Visualize output using the compact format
%.svg:		%.txt
	cpsa4graph -c -o $@ $<

# Visualize output using the LaTeX format
%.tex:		%.txt
	cpsa4graph -l -m 62 -o $@ $<

# Generate a Prolog database from a CPSA output file
%.pl:		%.txt
	cpsa4db $(DBFLAGS) $< | cpsa4dbprolog | sort > $@

# Generate a json version of source file
%.json:		%.scm
	cpsa4pp -jo $@ $<

# Generate defgoals from deflemmas
%_lemmas.json: 	%.json 
	python cpsa4lemmas.py $<

# Generate scm from json 
%_lemmas_src.scm: %_lemmas.json 
	cpsa4json -o $@ $<

# Generate goalsat file 
%_goalsat.txt: 	%_lemmas_src.text
	cpsa4goalsat -o $@ $<

# Generate json with lemmas as rules 
%_lemmas_as_rules.json:	%.json %_goalsat.txt 
	python cpsa4lemmas.py $^

# Generate the final scm file with verified lemmas as rules
%_lemmas_final.scm:	%_lemmas_as_rules.json
	cpsa4json -o $@ $<

.PRECIOUS:	%.txt %_shapes.txt %_lemmas_final.scm 
