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

.PRECIOUS:	%.txt %_shapes.txt
