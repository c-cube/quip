
TARGET?=@install

all:
	@dune build $(TARGET)

clean:
	@dune clean

watch:
	@dune build $(TARGET) -w
