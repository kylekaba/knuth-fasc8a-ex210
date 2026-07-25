CXX ?= g++
CXXFLAGS ?= -O3 -std=c++17 -DNDEBUG
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
BREW_GXX := $(lastword $(sort $(wildcard /opt/homebrew/bin/g++-[0-9]* /usr/local/bin/g++-[0-9]*)))
ifneq ($(BREW_GXX),)
ifeq ($(origin CXX),default)
CXX := $(BREW_GXX)
endif
OMPFLAGS ?= -fopenmp
else
LIBOMP_PREFIX := $(shell brew --prefix libomp 2>/dev/null)
ifneq ($(LIBOMP_PREFIX),)
OMPFLAGS ?= -Xpreprocessor -fopenmp -I$(LIBOMP_PREFIX)/include -L$(LIBOMP_PREFIX)/lib -lomp
else
OMPFLAGS ?=
endif
endif
else
OMPFLAGS ?= -fopenmp
endif
BIN := build/bin
DATA := data
REGEN := build/regenerated

PROGRAMS := transfer_generator extract_blocks sanity_counts bruteforce_5x4 \
            closed_factor verify_visible wiedemann_ext verify_rank_cert pade_witness

.PHONY: all clean sanity visible-check visible-checkpoints rank-check rank-checkpoint-verify verify regen-check certs-regenerate pade-witnesses hashes

all: $(addprefix $(BIN)/,$(PROGRAMS))

$(BIN):
	mkdir -p $@

$(BIN)/transfer_generator: src/transfer_generator.cpp | $(BIN)
	$(CXX) $(CXXFLAGS) $< -o $@

$(BIN)/extract_blocks: src/extract_blocks.cpp src/transfer_generator.cpp | $(BIN)
	$(CXX) $(CXXFLAGS) $< -o $@

$(BIN)/sanity_counts: src/sanity_counts.cpp src/transfer_generator.cpp | $(BIN)
	$(CXX) $(CXXFLAGS) $< -o $@

$(BIN)/bruteforce_5x4: src/bruteforce_5x4.cpp | $(BIN)
	$(CXX) $(CXXFLAGS) $< -o $@

$(BIN)/closed_factor: src/closed_factor.cpp | $(BIN)
	$(CXX) $(CXXFLAGS) $< -o $@

$(BIN)/verify_visible: src/verify_visible.cpp | $(BIN)
	$(CXX) $(CXXFLAGS) $< -o $@

$(BIN)/wiedemann_ext: src/wiedemann_ext.cpp | $(BIN)
	$(CXX) $(CXXFLAGS) $< -o $@

$(BIN)/verify_rank_cert: src/verify_rank_cert.cpp | $(BIN)
	$(CXX) $(CXXFLAGS) $(OMPFLAGS) $< -o $@

$(BIN)/pade_witness: src/pade_witness.cpp | $(BIN)
	$(CXX) $(CXXFLAGS) $< -o $@

sanity: all
	$(BIN)/bruteforce_5x4
	$(BIN)/sanity_counts $(DATA)

visible-check: $(BIN)/verify_visible
	$(BIN)/verify_visible $(DATA)

visible-checkpoints: $(BIN)/verify_visible
	$(BIN)/verify_visible $(DATA) $(DATA)/certs/visible76.khc1

rank-check: all
	$(BIN)/verify_rank_cert $(DATA)/blocks/Trel_plus.kmc $(DATA)/certs/Trel_plus_border.kwc2 $(DATA)/certs/Trel_plus_eigen50.vec
	$(BIN)/verify_rank_cert $(DATA)/blocks/Trel_minus.kmc $(DATA)/certs/Trel_minus_shift50.kwc2 -
	$(BIN)/verify_rank_cert $(DATA)/blocks/U1_plus.kmc $(DATA)/certs/U1_plus_shift50.kwc2 -
	$(BIN)/verify_rank_cert $(DATA)/blocks/U1_minus.kmc $(DATA)/certs/U1_minus_shift50.kwc2 -
	$(BIN)/verify_rank_cert $(DATA)/blocks/U2_plus.kmc $(DATA)/certs/U2_plus_shift50.kwc2 -
	$(BIN)/verify_rank_cert $(DATA)/blocks/U2_minus.kmc $(DATA)/certs/U2_minus_shift50.kwc2 -

$(REGEN)/Trel_plus_border.krc1: $(BIN)/verify_rank_cert \
    $(DATA)/blocks/Trel_plus.kmc $(DATA)/certs/Trel_plus_border.kwc2 \
    $(DATA)/certs/Trel_plus_eigen50.vec $(DATA)/certs/Trel_plus_border.krc1
	mkdir -p $(REGEN)
	$(BIN)/verify_rank_cert $(DATA)/blocks/Trel_plus.kmc $(DATA)/certs/Trel_plus_border.kwc2 $(DATA)/certs/Trel_plus_eigen50.vec $@

rank-checkpoint-verify: $(REGEN)/Trel_plus_border.krc1
	cmp $(DATA)/certs/Trel_plus_border.krc1 $<

verify: sanity visible-check rank-check

regen-check: all
	rm -rf $(REGEN)
	mkdir -p $(REGEN)
	$(BIN)/transfer_generator $(REGEN)
	$(BIN)/extract_blocks $(REGEN)
	cmp $(DATA)/T5.bin $(REGEN)/T5.bin
	cmp $(DATA)/U5.bin $(REGEN)/U5.bin
	cmp $(DATA)/W5.bin $(REGEN)/W5.bin
	for f in $(DATA)/blocks/*; do cmp "$$f" "$(REGEN)/blocks/$$(basename $$f)"; done
	@echo "REGENERATION IS BYTE-FOR-BYTE IDENTICAL"

certs-regenerate: all
	mkdir -p $(DATA)/certs
	$(BIN)/closed_factor $(DATA) 9000 0
	$(MAKE) visible-checkpoints
	$(BIN)/wiedemann_ext $(DATA)/blocks/Trel_plus.kmc border 1 $(DATA)/certs/Trel_plus_border.kwc2 $(DATA)/certs/Trel_plus_eigen50.vec
	$(BIN)/wiedemann_ext $(DATA)/blocks/Trel_minus.kmc normal 1 $(DATA)/certs/Trel_minus_shift50.kwc2
	$(BIN)/wiedemann_ext $(DATA)/blocks/U1_plus.kmc normal 1 $(DATA)/certs/U1_plus_shift50.kwc2
	$(BIN)/wiedemann_ext $(DATA)/blocks/U1_minus.kmc normal 1 $(DATA)/certs/U1_minus_shift50.kwc2
	$(BIN)/wiedemann_ext $(DATA)/blocks/U2_plus.kmc normal 1 $(DATA)/certs/U2_plus_shift50.kwc2
	$(BIN)/wiedemann_ext $(DATA)/blocks/U2_minus.kmc normal 1 $(DATA)/certs/U2_minus_shift50.kwc2
	$(BIN)/verify_rank_cert $(DATA)/blocks/Trel_plus.kmc $(DATA)/certs/Trel_plus_border.kwc2 $(DATA)/certs/Trel_plus_eigen50.vec $(DATA)/certs/Trel_plus_border.krc1
	$(MAKE) pade-witnesses

pade-witnesses: $(BIN)/pade_witness
	$(BIN)/pade_witness $(DATA)/certs/Trel_plus_border.kwc2 $(DATA)/certs/Trel_plus_border.kpw1
	$(BIN)/pade_witness $(DATA)/certs/Trel_minus_shift50.kwc2 $(DATA)/certs/Trel_minus_shift50.kpw1
	$(BIN)/pade_witness $(DATA)/certs/U1_plus_shift50.kwc2 $(DATA)/certs/U1_plus_shift50.kpw1
	$(BIN)/pade_witness $(DATA)/certs/U1_minus_shift50.kwc2 $(DATA)/certs/U1_minus_shift50.kpw1
	$(BIN)/pade_witness $(DATA)/certs/U2_plus_shift50.kwc2 $(DATA)/certs/U2_plus_shift50.kpw1
	$(BIN)/pade_witness $(DATA)/certs/U2_minus_shift50.kwc2 $(DATA)/certs/U2_minus_shift50.kpw1

hashes:
	sha256sum -c SHA256SUMS

clean:
	rm -rf build
