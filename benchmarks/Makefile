default: all

dll:
	$(MAKE) -C dll

sll:
	$(MAKE) -C sll

ints:
	$(MAKE) -C ints

sll-bounds:
	$(MAKE) -C sll-bounds

tree:
	$(MAKE) -C tree


clean:
	$(MAKE) -C dll clean
	$(MAKE) -C sll clean
	$(MAKE) -C ints clean
	$(MAKE) -C sll-bounds clean
	$(MAKE) -C tree clean

all: dll ints sll sll-bounds tree

.PHONY: all default dll ints sll sll-bounds tree clean
