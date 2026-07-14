# SLOW_MODULES +=
# VERIFIED_MODULES =
# 	end_of_verified_modules

# VERIFIED_OR_SLOW_MODULES = $(sort $(SLOW_MODULES) $(VERIFIED_MODULES))
# ADMIT_MODULES = $(filter-out ${VERIFIED_OR_SLOW_MODULES}, $(wildcard *.fst)) $(filter-out ${VERIFIED_OR_SLOW_MODULES}, $(wildcard *.fsti))
FSTAR_INCLUDE_DIRS_EXTRA += ../secrets

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
