#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#############################################################################

.PHONY: clean go

# Set ARCH to "x86" or "arm" as appropriate; this is literally the
# directory name in which the libs2nbignum.a file should be found.
# If this block fails to do it automatically, replace with manual
# setting: ARCH=x86 or ARCH=arm as appropriate

ARCH=unknown_architecture

UNAME_RESULT=$(shell uname -m)

ifeq ($(UNAME_RESULT),x86_64)
ARCH=x86
endif

ifeq ($(UNAME_RESULT),aarch64)
ARCH=arm
endif

ifeq ($(UNAME_RESULT),arm64)
ARCH=arm
endif

# Benchmarking progfram

benchmark: benchmark.c ../include/s2n-bignum.h ../tests/mul_mod_128kplustwo.c ../tests/mul_mod_128kplustwo.h ../tests/bignum_9words.S ../$(ARCH)/libs2nbignum.a
	gcc -O3 -o benchmark benchmark.c ../tests/mul_mod_128kplustwo.c ../tests/bignum_9words.S -L../$(ARCH) -ls2nbignum -lm -I../include

go: benchmark ; ./benchmark

clean: ; rm -f benchmark
