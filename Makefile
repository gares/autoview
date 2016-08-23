COQC=coqc
SRC=$(wildcard *v)

all: jscoq udoc $(SRC:%.v=%.html)

jscoq:
	git clone https://github.com/ejgallego/jscoq-builds.git --depth 1 jscoq
	cd jscoq && git checkout c219bd7e4b207846a607ce5a19513412d826ce7a


udoc: udoc.patch
	rm -rf udoc
	git clone https://github.com/ejgallego/udoc.git
	cd udoc && patch -p1 < ../udoc.patch
	cd udoc && git checkout 11fa04a621e8f8bc156430da4f0d3c10d8585ab3
	cd udoc && make # requires ocaml 4.02

%.html : %.v Makefile
	-$(COQC) $* # if not working, no links but html still ok
	./udoc/udoc.byte $< -o $@
	sed -i 's?^ *<title.*?<title>$*</title>?' $@
	sed -i 's?^ *<h1>$*</h1>??' $@
	sed -i '/<\/title>/a\<link rel="stylesheet" href="local.css" />' $@

ex2 : # to get nice fonts for lesson2 and exercise2
	./sedfont exercise2.html
	./sedfont lesson2.html
run:
	python3 -m http.server 8000
