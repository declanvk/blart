#!/usr/bin/env bash

set -o errexit # make script exit when a command fails
set -o nounset # make script exit when using undeclared variables
set -o pipefail # make script exit when command fails in a pipe
set -o xtrace # print a trace of all commands executed by script

if [ "$#" -ne 1 ]; then
    >&2 echo "Illegal number of parameters [$#]"
    >&2 echo "usage: ${0} <toolchain>"
    exit 1
fi

MAYBE_RESOLVED="${1}"

if [[ "${MAYBE_RESOLVED}" == "msrv" ]]; then
    MAYBE_RESOLVED="$(cargo metadata --no-deps --format-version 1 \
        | jq -r '.packages | map(select(.name == "blart"))[0].rust_version')"
fi

echo "${MAYBE_RESOLVED}"