#!/usr/bin/env python3

# Print the last skeleton label
# John D. Ramsdell -- October 2021

# The input is expected on standard input
# Use cpsapp -j to translate the source file into JSON.
#
# cpsa4pp -j file | ./lastlabel.py

import sys
import json
import cpsajson

def main():
    if len(sys.argv) != 1:      # Ensure no argument is supplied
        print("Print the last skeleton label")
        print("Expects JSON translation of CPSA output on standard input")
        print("cpsa4pp -j file | ./lastlabel.py")
        print()
        print("Usage: " + sys.argv[0])
        sys.exit(1)
    xs = cpsajson.load(sys.stdin)

    label = 0                   # Skeleton number
    for x in xs:
        if x[0] == "defskeleton":
            for item in x:
                if type(item) is list and item[0] == "label":
                    label = item[1]
    print(label)

if __name__ == "__main__":
    main()
