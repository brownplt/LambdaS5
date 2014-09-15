.PHONY = clean builddir debug

INCLUDES = analyses/cfg,analyses/cps,analyses/sym,analyses/ses,js,exprjs,ljs,util,experimental,test,optimization

OCAMLBUILD = ocamlbuild -build-dir ../obj -libs unix,str,graph -lflags -I,../lib -Is $(INCLUDES) -cflags -annot -cflags -I,../lib -Is $(INCLUDES) 

debug: builddir
	@rm -f s5.d.byte
	$(OCAMLBUILD) s5.d.byte
	@ln -s ../obj/s5.d.byte


clean:
	rm -rf ../obj

builddir:
	@mkdir ../obj 2> /dev/null || true

test: debug
	$(OCAMLBUILD) regexp_tests.d.byte
	$(OCAMLBUILD) gc_tests.d.byte

compare: debug
	$(OCAMLBUILD) sym_compare.d.byte

######## for optimization ##########
# since all include path of ocamlbuild should be relative to current directory,
# ../ is forbidden in -Is. The simplest way to make and run optimization test is writing
# targets in this top-level makefile
TEST_SRC = $(wildcard optimization/test/*.ml)
TEST_BYTE = $(addprefix ../obj/,$(subst .ml,.d.byte,$(TEST_SRC)))
OPT_BUILD = ocamlbuild -build-dir ../obj -Is util,ljs,js,exprjs,optimization -use-ocamlfind -pkgs ounit,unix,str -lflags -I,../lib 

opt: debug $(TEST_BYTE)

$(TEST_BYTE): ../obj/%.d.byte: %.ml
	$(OPT_BUILD) $<

opttest: opt
	#$(foreach p,$(TEST_BYTE),$(p) -no-output-file -no-cache-filename;)
	for p in $(TEST_BYTE); do  \
		echo "Running $$p"; \
		$$p -no-output-file -no-cache-filename; \
	done
