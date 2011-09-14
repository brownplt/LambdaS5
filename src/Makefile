.PHONY = clean builddir debug

OCAMLBUILD = ocamlbuild -build-dir ../obj -lib unix -lib str

debug: builddir
	@rm -f s5.d.byte
	$(OCAMLBUILD) s5.d.byte
	@ln -s ../obj/s5.d.byte


clean:
	rm -rf ../obj

builddir:
	@mkdir ../obj 2> /dev/null || true


