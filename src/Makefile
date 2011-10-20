.PHONY = clean builddir debug

OCAMLBUILD = ocamlbuild -build-dir ../obj -libs unix,str,graph -lflags -I,../lib -cflags -I,../lib

debug: builddir
	@rm -f s5.d.byte
	$(OCAMLBUILD) s5.d.byte
	@ln -s ../obj/s5.d.byte


clean:
	rm -rf ../obj

builddir:
	@mkdir ../obj 2> /dev/null || true


