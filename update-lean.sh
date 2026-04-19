#!/bin/bash
set -e

PROJECTS=("nf-validate" "parse-strat" "seq-embed")

echo "Starting Lean & Mathlib update process for all projects..."

for proj in "${PROJECTS[@]}"; do
    echo "========================================"
    echo "Updating project: $proj"
    echo "========================================"
    
    cd "$proj"
    
    echo "1. Running lake update..."
    lake update
    
    echo "2. Syncing lean-toolchain to Mathlib's explicit version..."
    if [ -f ".lake/packages/mathlib/lean-toolchain" ]; then
        cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain
        echo "Toolchain perfectly synced."
    else
        echo "Warning: .lake/packages/mathlib/lean-toolchain not found. Skipping toolchain sync."
    fi
    
    echo "3. Fetching Mathlib cache..."
    lake exe cache get
    
    echo "4. Building project..."
    if [ "$proj" == "nf-validate" ]; then
        # For nf-validate, build both the default executable and the library target containing proofs
        lake build
        lake build NfValidate
    else
        lake build
    fi
    
    cd ..
    echo "Finished $proj."
    echo ""
done

echo "All projects updated and built successfully!"
