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
    declare -a TOOLCHAIN_EXTRA_ARGS=("" "--all-features")
else
    declare -a TOOLCHAIN_EXTRA_ARGS=("" "--features allocator-api2")
fi

for extra_args in "${TOOLCHAIN_EXTRA_ARGS[@]}"
do
    cargo "${TOOLCHAIN_ARG}" fmt -- --check
    cargo "${TOOLCHAIN_ARG}" build  $extra_args --all-targets

    # --all-targets does not include the doctests
    cargo "${TOOLCHAIN_ARG}" test   $extra_args --lib --bins --examples --tests
    # check in release just in case
    cargo "${TOOLCHAIN_ARG}" test   $extra_args --lib --bins --examples --tests --release
    # We test benchmarks in release, otherwise they are too slow
    cargo "${TOOLCHAIN_ARG}" test   $extra_args --benches --release
    cargo "${TOOLCHAIN_ARG}" test   $extra_args --doc

    cargo "${TOOLCHAIN_ARG}" clippy $extra_args --all-targets 
    cargo "${TOOLCHAIN_ARG}" doc    $extra_args --no-deps --document-private-items

    if [ "${TOOLCHAIN}" = "nightly" ]; then
        cargo "${TOOLCHAIN_ARG}" miri test --lib --bins --examples --tests $extra_args
    fi
done

