# base is the src directory
BASE := ..
DIRS = $(addprefix $(BASE)/, util ljs js exprjs optimization)

comma := ,
INCLUDES = $(subst $(eval) ,$(comma),$(DIRS))

OCAMLBUILD = ocamlbuild -build-dir $(BASE)/../obj/ -cflags -Is $(INCLUDES) -use-ocamlfind -pkgs ounit,unix,str -lflags -I $(BASE)/../lib/ 

all:
	$(OCAMLBUILD) -I test/constant_test.d.byte
