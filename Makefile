PYTHON ?= python3

.PHONY: check check-crush

check:
	$(PYTHON) scripts/check.py

check-crush:
	$(PYTHON) scripts/check.py --with-crush
