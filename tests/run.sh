#!/bin/bash
YOSYS=yosys
TESTSDIR="$(dirname "${BASH_SOURCE[0]}")"
PLUGIN="$(realpath "$TESTSDIR/../build/slang.so")"
code=0
for testcase in "$TESTSDIR"/*/*.ys;
do
	TEXT=$testcase;
	base=$(basename "$testcase")
	dir=$(dirname "$testcase")
	echo -n "${TEXT}... ";
	if ! (cd "$dir" && exec "$YOSYS" -m "$PLUGIN" -s "$base" 1>/dev/null 2>&1); then
		echo -e "\e[31mFAIL\e[0m";
		echo -e "Testcase \e[1m${testcase}\e[0m failed";
		(cd "$dir" && exec "$YOSYS" -g -Q -m "$PLUGIN" -s "$base");
		echo;
		code=1;
	else
		echo -e "\e[32mOK\e[0m";
	fi
done;
exit $code
