PACKAGE=svncterm
VERSION=1.2

all: svncterm

glyphs.h: genfont
	./genfont > glyphs.h

genfont: genfont.c
	cc -g -O2 -o $@ genfont.c -Wall -lz

svncterm: svncterm.c
	cc -O2 -g -o $@ svncterm.c -Wall -Wno-deprecated-declarations -lvncserver -lpthread -lz -ljpeg -lutil -lgnutls -I/usr/local/include -L/usr/local/lib

clean:
	rm -rf genfont svncterm svncterm.1 *.core
