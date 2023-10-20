#.DELETE_ON_ERROR:

# Islaris dune locks some build directory and prevents parallel builds
.NOTPARALLEL:

SOURCES:=$(wildcard *.c)
OPTIMIZATION:=0 1 2
ISLARIS-REPO:=../islaris
ISLARIS-CN:=$(ISLARIS-REPO)/fromCN

ISLARIS-BASES:=$(foreach s, $(SOURCES), $(foreach o, $(OPTIMIZATION), $(ISLARIS-CN)/$(basename $s)/O$o))

PARENT_NAME=$(notdir $(patsubst %/,%, $(dir $(base))))
STEM_PARENT_NAME=$(notdir $(*D))

TARGETS:=$(foreach base, $(ISLARIS-BASES), $(addprefix $(base)/,\
	html \
	instructions \
	dune \
	$(PARENT_NAME).elf \
	$(PARENT_NAME).v \
	$(PARENT_NAME).dump \
	$(PARENT_NAME).cleaned.dump \
	))

CC:=clang
# -Wa,-L passes -L to the assembler to keep local symbols in the symbol table (typically start with .L)
#CFLAGS:=-target aarch64v8-none-elf -static -gdwarf-4 -std=c11 -Wall -Wa,-L -Wl,-e,main -ffreestanding -nostdlib
CFLAGS:=-target aarch64v8-none-elf -gdwarf-4 -std=c11 -Wall -Wa,-L -Wl,-e,main -ffreestanding -nostdlib
OBJDUMP:=aarch64-linux-gnu-objdump
READ-DWARF:=read-dwarf
CN:=cn

SILENT:=$(findstring s,$(word 1, $(MAKEFLAGS)))
PIPE_TO_NULL_IF_SILENT:=$(if $(SILENT),> /dev/null 2> /dev/null)

define pp
	printf "`tput setaf 6`$1:`tput sgr0` $2\n"
endef

all: $(TARGETS)
.PHONY: all

# Rule without receipt adds prerequisites to all targets at once
$(TARGETS): | $(ISLARIS-BASES)


$(ISLARIS-BASES):
	mkdir -p $@


clean:
	rm -rf $(ISLARIS-CN)
.PHONY: clean


%.dump: %.elf
	@$(call pp,objdump,generating dump)
	$(OBJDUMP) -d $< > $@


%.cleaned.dump: %.dump
	@$(call pp,tail,removing unparsable header of dump for islaris)
	tail -n +7 $< > $@


$(ISLARIS-REPO)/%/dune: template.dune
	@$(call pp,sed,generating dune file)
	sed 's/@@COQDIR@@/$(subst /,.,$*)/' $< > $@


.SECONDEXPANSION:

%.v: %.elf %.dump $$(*D)/dune
	$(info $@)
	@$(call pp,cn,verifying $<)
	$(CN) check $(*F).c $(PIPE_TO_NULL_IF_SILENT)
	@$(call pp,cn,generating assembler spec and proof)
	$(CN) bin $*.elf $*.dump $(subst /,.,$(subst $(ISLARIS-REPO)/,,$(*D))).instructions $@ $(*F).c $(PIPE_TO_NULL_IF_SILENT)
	@$(call pp,islaris,checking automatically generated proof)
	$(MAKE) -C $(ISLARIS-REPO)


%.elf: $$(*F).c
	$(call pp,cc,compiling $<)
	$(CC) $(CFLAGS) -$(STEM_PARENT_NAME) -o $@ $<


%/html: $(addprefix %/$$(STEM_PARENT_NAME), .elf .dump)
	@$(call pp,read-dwarf,generating html output)
	mkdir -p $@
	$(READ-DWARF) rd --html --elf=$*/$(STEM_PARENT_NAME).elf --objdump-d=$*/$(STEM_PARENT_NAME).dump --comp-dir=. --out-dir=$@ $(PIPE_TO_NULL_IF_SILENT)


%/instructions: %/$$(STEM_PARENT_NAME).cleaned.dump
	@$(call pp,islaris,generating assembly instruction traces)
	cd $(ISLARIS-REPO) && PATH=$$PWD/bin:$$PATH dune exec --\
		islaris $(realpath $<) -j $(shell nproc) -o $(abspath $@) --coqdir=$(subst /,.,$(subst $(ISLARIS-REPO)/,,$@)) $(PIPE_TO_NULL_IF_SILENT)
	@$(call pp,islaris,compiling coq isla traces)
	$(MAKE) -C $(ISLARIS-REPO)
	@find $@ -type f -name "*.isla" | wc -l | xargs -I '{}' $(call pp,islaris,found {} instructions)