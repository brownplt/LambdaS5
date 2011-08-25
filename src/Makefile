.PHONY = clean builddir debug

OCAMLBUILD = ocamlbuild-3.12.1 -build-dir ../obj -lib unix

debug: builddir
	@rm -f s5.d.byte
	$(OCAMLBUILD) s5.d.byte
	@ln -s ../obj/s5.d.byte


clean:
	rm -rf ../obj

builddir:
	@mkdir ../obj 2> /dev/null || true


