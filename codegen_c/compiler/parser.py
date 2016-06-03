#!/usr/bin/env python
import codecs
import json
import argparse
import re
import os
from string import Template
from library import *
from bmType import bmType,bmRoot
from bmTerm import bmTerm 
from bmProgram import bmProgram,getBmProgram

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--debug", action='store_true')
    parser.add_argument("files", metavar="F", type=str, nargs='+', help="All JSON files")
    args = parser.parse_args()
    if GAP in args.files[0]:
        setProblem(GAP)
    elif PAREN in args.files[0]:
        setProblem(PAREN)
    elif ACCORDION in args.files[0]:
        setProblem(ACCORDION)
    elif LCS in args.files[0]:
        setProblem(LCS)
    elif BITONIC in args.files[0]:
        setProblem(BITONIC)
    elif KNAPSACK in args.files[0]:
        setProblem(KNAPSACK)
    else:
        Assert(False, "problem name not expected/defined")
    (pdict,prgs) = getBmProgram(args.files)
    #For each loop,rec pair - take superset from rec and put it in loop
    
    unionSS = {}
    if getProblem() in  [ACCORDION,BITONIC]:
        for name in pdict:
            addSS(pdict[name]["rec"].superset,unionSS)
        for name in pdict:
            pdict[name]["rec"].superset = unionSS
            pdict[name]["loop"].superset = unionSS
    else:
        for name in pdict:
            #print "PRG: ", name, pdict[name]["rec"].superset
            if getProblem() == "Gap":
                if u"J0" not in pdict[name]["rec"].superset:
                    pdict[name]["rec"].superset[u"J0"] = u"J"
                if u"J1" not in pdict[name]["rec"].superset:
                    pdict[name]["rec"].superset[u"J1"] = u"J"
                if u"K0" not in pdict[name]["rec"].superset:
                    pdict[name]["rec"].superset[u"K0"] = u"K"
                if u"K1" not in pdict[name]["rec"].superset:
                    pdict[name]["rec"].superset[u"K1"] = u"K"
            pdict[name]["loop"].superset = pdict[name]["rec"].superset
        
    if args.debug:
        for prg in prgs:
            print prg.text.encode('utf-8')
            print prg.__str__().encode('utf-8')
     
    for prg in prgs:
        prg.printCode()
        


if __name__ == "__main__": main()
