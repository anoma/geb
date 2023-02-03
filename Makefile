all:
	make clean || true
	ros run --load "geb.asd" --eval "(progn (load \"geb.asd\") (make-system))"

install:
	make clean || true
	make all
	mkdir -p '${HOME}/.local/bin/'
	mv "./build/geb.image" '${HOME}/.local/bin/'

clean:
	rm "./build/geb.image"

uninstall:
	rm '${HOME}/.local/bin/geb.image'
