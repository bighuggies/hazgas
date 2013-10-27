#!/usr/bin/env python
#encoding: utf-8

import subprocess
import re
import os
import sys

i = 0
passed = 0

NEVER_CLAIM = "\tnever claim         \t+ "

has_more_claims = True

print("\033[37m\033[1mPerforming verification...\033[0m\n")

while True:
    p = subprocess.Popen(["./pan", "-N{0}".format(i), "-n"] + sys.argv[1:],
                         stdout=subprocess.PIPE, stderr=open(os.devnull, "w"))

    claim = None
    error = []

    for line in p.stdout:
        line = line.strip("\r\n")

        if "non-existing claim" in line:
            has_more_claims = False
            p.kill()
            break

        if "assertion violated" in line or line.startswith("error:"):
            error.append(line)

        if line[:len(NEVER_CLAIM)] == NEVER_CLAIM:
            claim = line[len(NEVER_CLAIM) + 1:len(line) - 1]

    if claim is None:
        break

    if not has_more_claims:
        break

    passed += not error

    print("{0} {1}\033[0m".format("\033[32m✔" if not error else "\033[31m✗", claim))

    if error:
        print("\n".join("    " + e for e in error) + "\n")

    i += 1

print("""
\033[37m\033[1mVerification completed.\033[0m

    {0} claims in total, of which:
    \033[32m{1} passed.\033[0m \
""".format(i, passed))

if passed < i:
    print("    \033[31m{0} failed.\033[0m".format(i - passed))

print("")
