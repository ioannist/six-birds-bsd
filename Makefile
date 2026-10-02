LATEXMK = latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build

APPARATUS_DIR = paper/apparatus
CLOSURE_DIR = paper/closure

PAPER_AUX_EXTS = aux log bbl blg toc out synctex.gz fdb_latexmk fls

.PHONY: help \
	paper-build-apparatus paper-build-closure paper-build \
	paper-preflight-apparatus paper-preflight-closure paper-preflight \
	paper-clean-apparatus paper-clean-closure paper-clean \
	audit-check audit-regenerate audit-regenerate-full \
	validate verify-lean test \
	public-audit

.NOTPARALLEL:

help:
	@echo "Paper targets:"
	@echo "  paper-build-apparatus     Build the apparatus paper PDF at $(APPARATUS_DIR)/build/main.pdf"
	@echo "  paper-build-closure       Build the closure paper PDF at $(CLOSURE_DIR)/build/main.pdf"
	@echo "  paper-build               Build both paper PDFs"
	@echo "  paper-preflight-apparatus Build, lint, and log-check the apparatus paper"
	@echo "  paper-preflight-closure   Build, lint, and log-check the closure paper"
	@echo "  paper-preflight           Preflight both papers and run registry/Lean validators"
	@echo "  paper-clean-apparatus     Remove apparatus paper build artifacts"
	@echo "  paper-clean-closure       Remove closure paper build artifacts"
	@echo "  paper-clean               Remove build artifacts for both papers"
	@echo ""
	@echo "Foundations-audit targets (artifact mode must match check_lean.py's invocation):"
	@echo "  audit-check           Verify committed audit artifacts (--check --skip-validation)"
	@echo "  audit-regenerate      Regenerate audit artifacts in the safe mode (--skip-validation)"
	@echo "  audit-regenerate-full Regenerate WITH upstream-validator side effects (no flags); use only if you intend to commit a validation_status=passed artifact shape and update check_lean.py to match"
	@echo ""
	@echo "Validator orchestration:"
	@echo "  validate              Run the static validator chain (NO Lean build; self-sufficient from a fresh checkout)"
	@echo "  verify-lean           Build Lean (SixBirdsBSD + vendored Foundations) and run the live axiom-closure probe; needs a Lean toolchain"
	@echo "  test                  Run pytest on the validator unit tests"
	@echo "  public-audit          Check the tracked tree for private/operator artifacts"
	@echo ""
	@echo "  help                  Show this target list"

paper-build-apparatus:
	cd $(APPARATUS_DIR) && $(LATEXMK) main.tex

paper-build-closure:
	cd $(CLOSURE_DIR) && $(LATEXMK) main.tex

paper-build: paper-build-apparatus paper-build-closure

# Release preflight log check. Undefined references/citations, cleveref
# artifacts, and layout warnings are all fatal for the public manuscripts.
define preflight_log_check
	@log="$(1)/build/main.log"; \
	test -f "$$log" || { echo "error: missing build log $$log"; exit 1; }; \
	if grep -nE 'Overfull|Underfull|Float too large' "$$log"; then \
	  echo "error: $(2) paper build log contains layout warnings"; \
	  exit 1; \
	fi; \
	if grep -nE 'undefined references|undefined citations|Reference .* undefined|Citation .* undefined|There were undefined|Cref Cref|\\\\Cref.*\\\\Cref' "$$log"; then \
	  echo "error: $(2) paper build log contains undefined-reference/citation or cleveref-artifact warnings"; \
	  exit 1; \
	fi
endef

paper-preflight-apparatus: paper-build-apparatus
	scripts/paper_lint.sh $(APPARATUS_DIR)
	$(call preflight_log_check,$(APPARATUS_DIR),apparatus)

paper-preflight-closure: paper-build-closure
	scripts/paper_lint.sh $(CLOSURE_DIR)
	$(call preflight_log_check,$(CLOSURE_DIR),closure)

paper-preflight: paper-preflight-apparatus paper-preflight-closure
	python3 scripts/check_statements_of_record.py --check
	python3 scripts/check_manifests.py --check --skip-probe
	python3 scripts/check_lean.py --skip-build

paper-clean-apparatus:
	rm -rf $(APPARATUS_DIR)/build
	@for ext in $(PAPER_AUX_EXTS); do rm -f "$(APPARATUS_DIR)"/*.$$ext; done

paper-clean-closure:
	rm -rf $(CLOSURE_DIR)/build
	@for ext in $(PAPER_AUX_EXTS); do rm -f "$(CLOSURE_DIR)"/*.$$ext; done

paper-clean: paper-clean-apparatus paper-clean-closure

audit-check:
	python3 scripts/audit_foundations_dependencies.py --check --skip-validation

audit-regenerate:
	python3 scripts/audit_foundations_dependencies.py --skip-validation

audit-regenerate-full:
	@echo "WARNING: this regenerates with validation_status=passed; check_lean.py will then"
	@echo "flag the artifacts as stale unless its --skip-validation invocation is also changed."
	python3 scripts/audit_foundations_dependencies.py

# validate is the STATIC validator chain: it runs from a fresh committed
# checkout with no Lean build (the manifest probe is skipped — see verify-lean).
# Axiom-closure / forbidden-token guarantees are verified here against the
# committed Lean source + foundations-audit artifacts; verify-lean re-confirms
# them live by building.
validate:
	scripts/check_public_hygiene.sh
	python3 scripts/check_lean.py --skip-build
	python3 scripts/check_manifests.py --check --skip-probe
	python3 scripts/check_statements_of_record.py --check
	python3 scripts/audit_foundations_dependencies.py --check --skip-validation
	python3 scripts/check_foundations_provenance.py --check
	python3 scripts/check_semantic_alignment.py --check
	python3 scripts/check_supplementary_statement_audit.py --check
	python3 scripts/check_support_prime_data.py --check

# verify-lean is the build-dependent gate: it builds the Lean project (incl. the
# vendored Foundations libraries) and runs the live `lake env lean` axiom-closure
# probe over every manifest declaration. Requires a Lean toolchain + the vendored
# deps; not reproducible from a source-only checkout, so it is NOT part of validate.
verify-lean:
	cd lean && lake build
	cd lean && lake build SixBirdsBSD.Verification.Regression
	python3 scripts/check_manifests.py --check

test:
	python3 -m pytest scripts/test_check_manifests.py scripts/test_check_semantic_alignment.py scripts/test_check_supplementary_statement_audit.py

public-audit:
	scripts/check_public_hygiene.sh
