CC := coqc

SRC := $(shell find ./ -type f -name '*.v')
OBJ := $(patsubst %.v, %.vo, $(SRC))

%.vo: %.v
	$(CC) $<

all: $(OBJ)

clean:
	find ./ -type f -name '*.vo' -delete
	find ./ -type f -name '*.glob' -delete
	find ./ -type f -name '*~' -delete
