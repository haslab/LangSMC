FIND := find
MAKE := make

NAME_OPT := -name
ECO := "*.eco"
TYPE_OPT := -type f
DELETE_OPT := -delete

MAKE_OPT := -C

CLEAN := clean

EC_PATH := $(CURDIR)/easycrypt
PROOF_PATH := $(CURDIR)/proof


.PHONY: easycrypt clean-easycrypt
.PHONY: check-proof clean-proof

# --------------------------------------------------------------------
# Build EasyCrypt
easycrypt:
	$(MAKE) $(MAKE_OPT) easycrypt/
# Clean EasyCrypt
clean-easycrypt:
	$(MAKE) $(CLEAN) $(MAKE_OPT) easycrypt/

# --------------------------------------------------------------------
# check proof
check-proof:
	$(MAKE) check $(MAKE_OPT) proof/

clean-proof:
	$(FIND) proof/ $(NAME_OPT) $(ECO) $(TYPE_OPT) $(DELETE_OPT)

# --------------------------------------------------------------------
clean: clean-easycrypt clean-proof
