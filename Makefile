# Copyright (C) 2015, University of British Columbia
# Written by Yan Peng (July 12th 2017)
#

.PHONY: all clean

ACL2 := /Users/penny/bin/acl2
ACL2_BOOKS := /Users/penny/Software/acl2/books
BUILD_DIR := /Users/penny/Software/acl2/books/build

JOBS ?= 1

all: top

top:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_BOOKS) asp

clean:
	$(BUILD_DIR)/clean.pl
