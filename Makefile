# Copyright (C) 2015, University of British Columbia
# Written by Yan Peng (July 12th 2017)
#

.PHONY: all clean

ACL2 := /Users/penny/Software/acl2/saved_acl2
ACL2_BOOKS := $(dir ${ACL2})books
BUILD_DIR := ${ACL2_BOOKS}/build

JOBS ?= 3

all: top

top: env asp test

refine:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_BOOKS) refinement

test:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_BOOKS) rational2str

env:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_BOOKS) env

asp:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_BOOKS) asp

clean:
	$(BUILD_DIR)/clean.pl
