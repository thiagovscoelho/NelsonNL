#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v lean >/dev/null 2>&1; then
    printf '%s\n' 'Lean verification NOT performed: lean executable not found.' >&2
    exit 127
fi
lean --version
lean NLPrimitive.lean
lean NLDefined.lean
python3 check_finite_models.py
