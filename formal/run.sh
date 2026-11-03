#!/usr/bin/env bash

if ! cd "$(dirname "${BASH_SOURCE[0]}")/lean"; then
    echo "error: failed to enter Lean workspace" >&2
    exit 1
fi

if ! command -v lake >/dev/null 2>&1 && [ -f "${HOME}/.elan/env" ]; then
    # shellcheck source=/dev/null
    . "${HOME}/.elan/env"
fi
if ! lake build; then
    echo "error: Lean build failed" >&2
    exit 1
fi
if ! lake env lean Check.lean; then
    echo "error: Lean axiom audit failed" >&2
    exit 1
fi
