# Pancake programs, compiled with the original CakeML compiler (`cake --pancake`).
#   make            # build/count, the milestone-0 program
#   make test       # run it

CAKE_VERSION = v3479
CAKE_SHA256  = e110bfcba19d6524ee4748608a67a275647445a048928cf623c2c9a973e31c9a
CAKE_URL     = https://github.com/CakeML/cakeml/releases/download/$(CAKE_VERSION)/cake-x64-64.tar.gz
CC     ?= cc
# Linear-scan register allocation and a moderate heap: the default allocator and large heaps
# make the checker's compile take hours (about 11 min this way).
CAKEFLAGS ?= --reg_alg=4
CAKEHEAP  ?= 4000
CFLAGS ?= -O2
B       = build

all: $(B)/count

# The checker: ../scripts/Emit.lean prints the verified program to checker.pnk.
checker.pnk:
	cd .. && lake env lean scripts/Emit.lean

checker: $(B)/checker

$(B)/checker: $(B)/checker.S ffi_checker.c
	$(CC) $(CFLAGS) -o $@ $< ffi_checker.c

$(B):
	mkdir -p $(B)

$(B)/cake-x64-64.tar.gz: | $(B)
	curl -fsSL -o $@.tmp $(CAKE_URL)
	echo "$(CAKE_SHA256)  $@.tmp" | sha256sum -c -
	mv $@.tmp $@

$(B)/cake: $(B)/cake-x64-64.tar.gz
	tar -xzf $< -C $(B)
	$(MAKE) -C $(B)/cake-x64-64 cake
	cp $(B)/cake-x64-64/cake $@

$(B)/%.S: %.pnk $(B)/cake
	CML_HEAP_SIZE=$(CAKEHEAP) $(B)/cake --pancake $(CAKEFLAGS) < $< > $@.tmp
	mv $@.tmp $@

$(B)/%: $(B)/%.S ffi.c
	$(CC) $(CFLAGS) -o $@ $< ffi.c

test: $(B)/count
	printf hello | $(B)/count > $(B)/count.out
	echo 15 | cmp - $(B)/count.out && echo "count: ok"

.PHONY: all test
