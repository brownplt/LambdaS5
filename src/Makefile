.PHONY = clean builddir debug

INCLUDES = analyses/cfg,analyses/cps,js,exprjs,ljs,util,experimental

OCAMLBUILD = ocamlbuild -build-dir ../obj -libs unix,str,graph -lflags -I,../lib -Is $(INCLUDES) -cflags -I,../lib -Is $(INCLUDES)

debug: builddir
	@rm -f s5.d.byte
	$(OCAMLBUILD) s5.d.byte
	@ln -s ../obj/s5.d.byte


clean:
	rm -rf ../obj

builddir:
	@mkdir ../obj 2> /dev/null || true


