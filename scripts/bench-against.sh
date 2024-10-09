#!/usr/bin/env bash

set -o errexit # make script exit when a command fails
set -o nounset # make script exit when using undeclared variables
set -o pipefail # make script exit when command fails in a pipe

git switch --quiet --detach "$1"

BASELINE_NAME="$(git rev-parse --short HEAD)"

# Create the baseline benchmark and don't output the summary
cargo bench --quiet --bench iai_callgrind -- --save-baseline="${BASELINE_NAME}" > /dev/null

# Using '-' will switch back to the previous branch or git checkout
git switch --quiet -

# Run the benchmark again with comparison to baseline
cargo bench --quiet --bench iai_callgrind -- --baseline="${BASELINE_NAME}"