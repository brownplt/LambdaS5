.PHONY = clean builddir debug

INCLUDES = analyses/cfg,analyses/cps,analyses/sym,analyses/ses,analyses/opt,js,exprjs,ljs,util,experimental,test

OCAMLBUILD = ocamlbuild -build-dir ../obj -libs unix,str,graph,oUnit -lflags -I,../lib -Is $(INCLUDES) -cflags -annot -cflags -I,../lib -Is $(INCLUDES)

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
