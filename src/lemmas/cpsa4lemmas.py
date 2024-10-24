#!/usr/bin/env python3

# Skeleton split
# Paul D. Rowe -- October 2024

# Extracts the lemmas of protocols in a CPSA source file,
# writing a new file containing only the protocols with 
# the lemmas removed, and each lemma stated as a defgoal.

# All other defgoals and defskeletons of the source file 
# are dropped. 

# If the source file is root.json, the result is written
# to root_lemmas.json. 

import sys
import os.path
import json

# Read a file containing a sequence of json objects produced by cpsa's
# pretty printer.  Assumes each object is terminated by a blank line.
def load(f):
    xs = []                     # List of objects read
    buf = ""
    while True:
        l = f.readline()
        if l == "":             # End of file
            if len(buf) > 0:    # Extract JSON object from buf
                xs.append(json.loads(buf))
            return xs
        elif l == "\n":         # Blank line
            if len(buf) > 0:    # Extract JSON object from buf
                xs.append(json.loads(buf))
                buf = ""
        else:
            buf += l            # Append line to buf

def readfile(fname):
    (root, ext) = os.path.splitext(fname)
    f = open(fname, 'r')
    xs = load(f)
    f.close()
    return root, ext, xs

def main():
    if len(sys.argv) < 2 or len(sys.argv) > 3: # Ensure one or two files 
        print("Usage: " + sys.argv[0] + " source_file [goalsat_file]")
        sys.exit(1)

    # Read in the first file
    fname = sys.argv[1]
    root, ext, xs = readfile(fname)

    # One file indicates we are extracting deflemmas into 
    # defgoals in their own file.
    if len(sys.argv) == 2:
        pd = []                     # Protocol list
        h = []                      # Herald form
        ms = []                     # macro list
        ls = []                     # lemma list
        for x in xs:
            if x[0] == "herald":
                h = x               # Store herald
            elif x[0] == "defprotocol":
                pd.append(x)        # Store protocol
            elif x[0] == "defmacro":
                ms.append(x)
        for p in pd: # p is a defprotocol item
            for item, i in zip(p, range(len(p))): # search for deflemma and indx in p
                if item[0] == "deflemma":
                    item[1] = p[1]
                    ls.append(item) # add i to list of lemmas
                    p[i] = "" # replace deflemma item with empty string
        for l in ls:
            l[0] = "defgoal" # change deflemma to defgoal
        f = open(root + "_lemmas" + ext, 'w')
        if h:
            json.dump(h, f)
        for m in ms:
            json.dump(m, f)
        for p in pd:
            json.dump(p, f)
        for l in ls:
            json.dump(l, f)
        f.close()
        
    if len(sys.argv) == 3:
        pd = []                     # Protocol list
        h = []                      # Herald form
        ms = []                     # Macros
        gd = []                     # Goal and Skeleton list
        gsats = []
        for x in xs:
            if x[0] == "herald":
                h = x               # Store herald
            elif x[0] == "defmacro":
                ms.append(x)
            elif x[0] == "defprotocol":
                pd.append(x)        # Store protocol
            elif x[0] == "defskeleton" or x[0] == "defgoal":
                gd.append(x)        # Store skeleton or goal
        
        fname = sys.argv[2]
        f = open(fname, 'r')
        contents = f.read().splitlines() ## contents is entire file as a string 
        for g in contents:
            gsats.append(g.split()) ## gsats should be a list of lists
        f.close()

        i = 0
        unsats = 0
        for p in pd: # p is a defprotocol item
            for item, j in zip(p, range(len(p))): # search for deflemma and indx in p
                if item[0] == "deflemma":
                    if len(gsats[i]) == 1: # i'th goal is achieved
                        item[0] = "defrule"
                        item.append("(comment Verified Lemma)")
                    else: # goal is not achieved. Delete it
                        p[j] = ""
                        unsats = unsats + 1
                        #item.append("(comment Counterexample to lemma found)")
                        #unsats.append(item)
                    i = i + 1 # increment counter for each deflemma found
        
        f = open(root + "_lemmas_as_rules" + ext, 'w')
        if h:
            if unsats > 0:
                h.append("(comment Deleted at least one false lemma)")
            json.dump(h, f)
        elif unsats > 0:
            h = ["(herald lemma-verification (comment Deleted at least one false lemma))"]
            json.dump(h, f)
        for m in ms:
            json.dump(m, f)
        for p in pd:
            json.dump(p, f)
        for g in gd:
            json.dump(g, f)
        f.close()
        

if __name__ == "__main__":
    main()
