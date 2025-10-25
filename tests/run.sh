#!/bin/bash
YOSYS=yosys
TESTSDIR="$(dirname "${BASH_SOURCE[0]}")"
PLUGIN="$(realpath "$TESTSDIR/../build/slang.so")"
code=0
NOCOLOR='\033[0m'
RED='\033[0;31m'
GREEN='\033[0;32m'
BOLD='\033[1m'

for testcase in "$TESTSDIR"/*/*.ys "$TESTSDIR"/*/*.tcl;
do
	TEXT=$testcase;
	base=$(basename "$testcase")
	dir=$(dirname "$testcase")
	echo -n "${TEXT}... ";
	if ! (cd "$dir" && exec "$YOSYS" -m "$PLUGIN" "$base" >/dev/null 2>&1); then
		echo -e "${RED}FAIL${NOCOLOR}";
		echo -e "Testcase ${BOLD}${testcase}${NOCOLOR} failed";
		(cd "$dir" && exec "$YOSYS" -g -Q -m "$PLUGIN" "$base");
		echo;
		code=1;
	else
		echo -e "${GREEN}OK${NOCOLOR}";
	fi
done;
exit $code
