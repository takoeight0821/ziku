# Makefile for Ziku project
# Provides parallel test execution for faster development cycles

.PHONY: build test test-parallel test-fast clean-results help

RESULTS_DIR := .test-results

# Test categories (grouped by typical execution time)
# Fast tests: parser, infer, truncate, big-step
# Medium tests: ir-eval, ir-eval-big-step, emit-translate
# Slow tests: scheme-only, consistency, big-step-consistency, emit-scheme, io
FAST_CATEGORIES := parser infer truncate big-step
MEDIUM_CATEGORIES := ir-eval ir-eval-big-step emit-translate
SLOW_CATEGORIES := scheme-only consistency big-step-consistency emit-scheme io
ALL_CATEGORIES := $(FAST_CATEGORIES) $(MEDIUM_CATEGORIES) $(SLOW_CATEGORIES)

# Default target
help:
	@echo "Ziku Test Runner"
	@echo ""
	@echo "Usage:"
	@echo "  make build           Build the project"
	@echo "  make test            Run all tests sequentially"
	@echo "  make test-parallel   Run all tests in parallel (recommended)"
	@echo "  make test-fast       Run only fast tests (parser, infer, truncate, big-step)"
	@echo "  make test-medium     Run fast + medium tests"
	@echo "  make clean-results   Clean test result files"
	@echo ""
	@echo "Parallel execution:"
	@echo "  make -j4 test-parallel   Run with 4 parallel jobs"
	@echo "  make -j8 test-parallel   Run with 8 parallel jobs"
	@echo ""
	@echo "Categories:"
	@echo "  Fast:   $(FAST_CATEGORIES)"
	@echo "  Medium: $(MEDIUM_CATEGORIES)"
	@echo "  Slow:   $(SLOW_CATEGORIES)"

# Build the project
build:
	lake build

# Run all tests sequentially (original behavior)
test:
	lake test

# Run all tests in parallel with result aggregation
test-parallel: clean-results $(addprefix test-category-,$(ALL_CATEGORIES))
	@./scripts/aggregate-test-results.sh $(RESULTS_DIR)

# Run only fast tests (for quick feedback during development)
test-fast: clean-results $(addprefix test-category-,$(FAST_CATEGORIES))
	@./scripts/aggregate-test-results.sh $(RESULTS_DIR)

# Run fast + medium tests
test-medium: clean-results $(addprefix test-category-,$(FAST_CATEGORIES)) $(addprefix test-category-,$(MEDIUM_CATEGORIES))
	@./scripts/aggregate-test-results.sh $(RESULTS_DIR)

# Generic rule for running a single category
test-category-%:
	@mkdir -p $(RESULTS_DIR)
	@echo "Running $* tests..."
	@lake test -- $* --report $(RESULTS_DIR)/$*.json || true

# Clean test results
clean-results:
	@rm -rf $(RESULTS_DIR)

# Docker variants
.PHONY: docker-build docker-test docker-test-parallel

docker-build:
	docker run --rm -v "$(PWD):/workspace" -w /workspace ziku nix develop --command lake build

docker-test:
	docker run --rm -v "$(PWD):/workspace" -w /workspace ziku nix develop --command lake test

docker-test-parallel: clean-results
	@mkdir -p $(RESULTS_DIR)
	@for cat in $(ALL_CATEGORIES); do \
		echo "Running $$cat tests..."; \
		docker run --rm -v "$(PWD):/workspace" -w /workspace ziku \
			nix develop --command lake test -- $$cat --report $(RESULTS_DIR)/$$cat.json || true; \
	done
	@./scripts/aggregate-test-results.sh $(RESULTS_DIR)
