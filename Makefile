
TARGET?=@install

all:
	@dune build $(TARGET)

clean:
	@dune clean

test:
	@dune runtest -f --no-buffer

watch:
	@dune build $(TARGET) -w
