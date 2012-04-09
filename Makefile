# Frama-C installation directories
FRAMAC_SHARE := $(shell frama-c.byte -print-path)
FRAMAC_LIBDIR := $(shell frama-c.byte -print-libpath)
PLUGIN_NAME := Loop_counter
PLUGIN_CMO := loop_counter
include $(FRAMAC_SHARE)/Makefile.dynamic

constraint:
	frama-c -contraint main.c
	dot temp.dot -Tpng > constraint.png
