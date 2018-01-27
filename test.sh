#!/bin/bash
# Runs all tests.
set -e
rm -Rf .tox
./pep8.sh
unset TESTNAME; tox
