.PHONY: all build clean examples test

all: | clean clean-examples compile examples

#------------------------------------------------------------------------------#
# Main
O = ./mlightdp.o
compile: | clean
  # compile source
	@ocamlbuild -use-ocamlfind -use-menhir -I src/ src/main.native
	@mv main.native ${O}

  # create bash script
	@echo '#!/usr/bin/env bash' > mlightdp
	@echo '' >> mlightdp
	@echo 'MLIGHTDP="'${O}'"' >> mlightdp
	@echo '' >> mlightdp
	@echo 'if [[ ! -e "$$MLIGHTDP" ]]; then\n    echo "Error: MLightDP executable not found at $$MLIGHTDP."\n    exit 1\nfi' >> mlightdp
	@echo '' >> mlightdp
	@echo '"$$MLIGHTDP" "$$@"' >> mlightdp

	@chmod +x mlightdp


examples:
	@echo "Compile Example: Gap Sparse Vector"
	@./mlightdp examples/gap_sparse_vector.mldp
	@echo "Compile Example: Helloise"
	@./mlightdp examples/helloise.mldp
	@echo "Compile Example: Numerical Sparse Vector"
	@./mlightdp examples/numerical_sparse_vector.mldp
	@echo "Compile Example: Partial Sum"
	@./mlightdp examples/partial_sum.mldp
	@echo "Compile Example: Smart Sum"
	@./mlightdp examples/smart_sum.mldp
	@echo "Compile Example: Sparse Vector"
	@./mlightdp examples/sparse_vector.mldp
	@echo "Compile Example: Sum"
	@./mlightdp examples/sum.mldp

#------------------------------------------------------------------------------#
# Clean
clean:
	@rm -rf ./_build
	@rm -f mlightdp
	@rm -f ${O}
	@rm -f ./*.native
	@rm -f ./*.byte
	@rm -f src/parser.mli
	@rm -f src/parser.ml

clean-examples:
	@rm -f ./examples/**.dfy

#------------------------------------------------------------------------------#
# Unit testing
test-parser:
	@echo "Unit Test: Parser"
	@ocamlbuild -use-ocamlfind -use-menhir -pkg oUnit -I src/ test/parser_test.native
	@./parser_test.native

test-semant:
	@echo "Unit Test: Semantic Analysis"
	@ocamlbuild -use-ocamlfind -use-menhir -pkg oUnit -I src/ test/semant_test.native
	@./semant_test.native

test: | clean test-parser test-semant

test-menhir: | clean
	@menhir --explain src/parser.mly
