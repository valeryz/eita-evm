#!/usr/bin/env bash
# compare-batteries.sh — diff two run-battery.sh logs per leaf directory.
#   scripts/compare-batteries.sh <log-a> <log-b>
# Prints the directories whose pass/fail/skip counts differ, then the totals.
set -uo pipefail
a="$1"; b="$2"
join -j1 <(grep -E '^  \S+ +pass=' "$a" | awk '{print $1, $2, $3, $4}' | sort) \
         <(grep -E '^  \S+ +pass=' "$b" | awk '{print $1, $2, $3, $4}' | sort) |
  awk '$2 != $5 || $3 != $6 || $4 != $7 { printf "  %-55s A: %s %s %s   B: %s %s %s\n", $1, $2, $3, $4, $5, $6, $7 }'
echo "A: $(grep '^TOTAL' "$a" | sed 's/  (.*//')"
echo "B: $(grep '^TOTAL' "$b" | sed 's/  (.*//')"
