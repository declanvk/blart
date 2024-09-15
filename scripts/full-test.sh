#!/usr/bin/env bash

set -o errexit # make script exit when a command fails
set -o nounset # make script exit when using undeclared variables
set -o pipefail # make script exit when command fails in a pipe
set -o xtrace # print a trace of all commands executed by script

if [ "$#" -ne 1 ]; then
    >&2 echo "Illegal number of parameters [$#]"
    >&2 echo "usage: full-test.sh <toolchain>"
    exit 1
fi

TOOLCHAIN="${1}"
TOOLCHAIN_ARG="+${TOOLCHAIN}"


if [ "${TOOLCHAIN}" = "nightly" ]; then
    TOOLCHAIN_EXTRA_ARGS="--features nightly"
else
    TOOLCHAIN_EXTRA_ARGS=""
fi

cargo "${TOOLCHAIN_ARG}" fmt -- --check
cargo "${TOOLCHAIN_ARG}" build  $TOOLCHAIN_EXTRA_ARGS --all-targets

# --all-targets does not include the doctests
cargo "${TOOLCHAIN_ARG}" test   $TOOLCHAIN_EXTRA_ARGS --lib --bins --examples --tests
# check in release just in case
cargo "${TOOLCHAIN_ARG}" test   $TOOLCHAIN_EXTRA_ARGS --lib --bins --examples --tests --release
# We test benchmarks in release, otherwise they are too slow
cargo "${TOOLCHAIN_ARG}" test   $TOOLCHAIN_EXTRA_ARGS --benches --release
cargo "${TOOLCHAIN_ARG}" test   $TOOLCHAIN_EXTRA_ARGS --doc

cargo "${TOOLCHAIN_ARG}" clippy $TOOLCHAIN_EXTRA_ARGS --all-targets 
cargo "${TOOLCHAIN_ARG}" doc    $TOOLCHAIN_EXTRA_ARGS --no-deps --document-private-items

if [ "${TOOLCHAIN}" = "nightly" ]; then
    # Test with and without the toolchain-specific features
    # Also don't test benchmarks, since those load from disk
    cargo "${TOOLCHAIN_ARG}" miri test --lib --bins --examples --tests $TOOLCHAIN_EXTRA_ARGS
    cargo "${TOOLCHAIN_ARG}" miri test --lib --bins --examples --tests
fi
