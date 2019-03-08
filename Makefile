# Copyright (C) 2018, University of British Columbia
# Written by Yan Peng (Oct 2018)
#
# License: A 3-clause BSD license.
# See the LICENSE file distributed with this software
#

.PHONY: all clean

ACL2 := /Users/penny/Software/acl2/saved_acl2
ACL2_BOOKS := $(dir ${ACL2})books
BUILD_DIR := ${ACL2_BOOKS}/build

JOBS ?= 3

all: top

top: test refine ring

ring:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_BOOKS) asp-ring

refine:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_BOOKS) refinement

test:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_BOOKS) rational2str

clean:
	$(BUILD_DIR)/clean.pl
