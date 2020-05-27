.PHONY: all build clean examples test

all: | clean clean-examples compile examples

clean:
	@rm -rf ./_build
	@rm -f ./*.native
	@rm -f ./*.byte
	@rm -f src/parser.mli
	@rm -f src/parser.ml

clean-examples:
	@rm -f ./examples/**.dfy

#------------------------------------------------------------------------------#
# Main
compile:
	@ocamlbuild -use-ocamlfind -use-menhir -I src/ src/main.native

I = "examples/sparse_vector.mldp"
run:
	@./main.native ${I}

examples:
	@echo "Compile Example: Gap Sparse Vector"
	@./main.native examples/gap_sparse_vector.mldp
	@echo "Compile Example: Helloise"
	@./main.native examples/helloise.mldp
	@echo "Compile Example: Numerical Sparse Vector"
	@./main.native examples/numerical_sparse_vector.mldp
	@echo "Compile Example: Partial Sum"
	@./main.native examples/partial_sum.mldp
	@echo "Compile Example: Smart Sum"
	@./main.native examples/smart_sum.mldp
	@echo "Compile Example: Sparse Vector"
	@./main.native examples/sparse_vector.mldp

#------------------------------------------------------------------------------#
# Unit testing
test-parser:
	@echo "Parser:"
	@ocamlbuild -use-ocamlfind -use-menhir -pkg oUnit -I src/ test/parser_test.native
	@./parser_test.native

test-semant:
	@echo "Semantic Analysis:"
	@ocamlbuild -use-ocamlfind -use-menhir -pkg oUnit -I src/ test/semant_test.native
	@./semant_test.native

test: | clean test-parser test-semant

test-menhir: | clean
	@menhir --explain src/parser.mly
