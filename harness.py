#!/usr/bin/env python
#encoding: utf-8

import subprocess
import re

i = 0
passed = 0

NEVER_CLAIM = "\tnever claim         \t+ "

has_more_claims = True

print("\033[37m\033[1mPerforming verification...\033[0m\n")

while True:
    p = subprocess.Popen(["./pan", "-N{0}".format(i), "-n"],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    o, _ = p.communicate()

    claim = "??"
    holds = True

    for line in o.split("\n"):
        if "non-existing claim" in line:
            has_more_claims = False
            break

        if "assertion violated" in line:
            holds = False

        if line[:len(NEVER_CLAIM)] == NEVER_CLAIM:
            claim = line[len(NEVER_CLAIM) + 1:len(line) - 1]

    if not has_more_claims:
        break

    passed += holds

    print("{0} {1}\033[0m".format("\033[32m✔" if holds else "\033[31m✗", claim))

    i += 1

print("\nVerification completed: {0} claims in total, {1} claims passed".format(i, passed))
