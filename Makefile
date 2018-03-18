
test: main.native mini-c
	./mini-c --debug test.c

main.native: *.ml*
	ocamlbuild $@

mini-c:
	ln -s main.native $@

clean:
	rm _build -rf
	rm main.native
	rm mini-c