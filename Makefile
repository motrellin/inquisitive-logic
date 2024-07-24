# Makefile for a Coq-Project including Coq-Equations
# Copyright (C) 2024  Max Ole Elliger, Philip Kaludercic
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

# Configuration

#TODO Change the following lines for configuration.
COMPONENTS := theories:InqLog

COQDOC_FLAGS = --utf8

all: coqdoc

define GENCoqDoc
BEGIN { RS="[[:space:]]"; FS=":" }			\
{							\
    dirname = $$1;					\
    cmd = "coqdep -f _CoqProject -sort " dirname;	\
    while ((cmd | getline) > 0) {			\
        if ($$0 ~ "^" dirname && !seen[$$0]) {		\
	    print $$0;					\
            seen[$$0] = 1;				\
        }						\
    }							\
    close(cmd);						\
}
endef

html: Makefile.coq
	VFILES="$(shell echo $(COMPONENTS) | awk '$(GENCoqDoc)')" $(MAKE) -e -f Makefile.coq html

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: Makefile.coq
	$(MAKE) -f $< cleanall
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -f .Makefile.coq.d
	rm -f _CoqProject

define GENCoqPr
BEGIN { RS="[[:space:]]"; FS=":" }			\
{							\
    dirname = $$1;					\
    libname = $$2;					\
    print "-R " dirname " " libname;			\
    system("find " dirname " -name \"*.v\"");		\
}							\
END { print "-docroot ." }
endef

define GENDirList
BEGIN { RS="[[:space:]]"; FS=":" }			\
{ print $$1; }
endef

_CoqProject: Makefile $(shell echo $(COMPONENTS) | awk '$(GENDirList)')
	echo $(COMPONENTS) | awk '$(GENCoqPr)' > $@

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

.PHONY: all html clean

COQMAKEFILE := Makefile # Do not change!
include coqdocjs/Makefile.doc
