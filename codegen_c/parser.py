#!/usr/bin/env python
import codecs
import json
import argparse
import re

def Assert(cond,msg):
    if not cond:
        print "ERROR: " + msg
        raise Exception(msg)
        sys.exit(1)

def parseJsons(files):
    prgs = dict()
    for fname in files:
        f = codecs.open(fname,"r","utf-8")
        x = f.read()
        ljsons = x.split("\n\n")
        for j in ljsons:
            if len(j) >= 2:
                form = json.loads(j)
                if form['program'] not in prgs:
                    prgs[form['program']] = dict()
                prgs[form['program']][form['style']] = form
    return prgs

"""
>>> prgs["A[J]"].keys()
[u'rec', u'loop']
>>> prgs["A[J]"]["rec"].keys()
[u'text', u'style', u'program', u'term']
>>> prgs["A[J]"]["rec"]["term"].keys()
[u'root', u'$', u'subtrees']
>>> prgs.keys()
[u'B[J0,J1]', u'A[J]']
"""

bmTypes = []
bmTerms = []


class bmRoot(object):
    '''
        literal: string
        kind: (set,?,variable)
        ns: (numeric or None)
    '''
    def __init__(self,root):
        for k in root.keys():
            Assert(k in ['literal','$','kind','ns'],"root has more keys than accounted for: " + str(root))
        self.literal = root['literal']
        Assert(root['$'] == 'Identifier',"$ value not Identifier in " + str(root))
        self.kind = root['kind']
        if 'ns' in root:
            self.ns = str(root['ns'])
        else:
            self.ns = None
    def __str__(self):
        retStr = self.literal 
        if self.kind != u'?':
            retStr+= u"[" + self.kind
            if(self.ns is None):
                return retStr + u"]"
            else:
                return retStr + u"," + self.ns  + u"]"
        else:
            return retStr    
class bmType(bmRoot):
    '''
        subtrees = list of bmType objects (size = 0 or 2) 
        
        2 Type(\mult,?)
        2 Type(->,?)
        2 Type(\cap,?)
        0 Type(J,set)
        0 Type(J_0,set)
        0 Type(K_0,set)
        0 Type(N,set)
        0 Type(R,set)
        0 Type(<,variable)

    '''
    def __init__(self,typ):
        global bmTypes
        
        for k in typ.keys():
            Assert(k in ['root','$','subtrees'],"typ has more keys than accounted for: " + str(typ.keys()))
        #self.root = bmRootType(typ['root'])
        
        bmRoot.__init__(self,typ['root'])
        
        #first char of sets is a caps
        if self.kind == 'set':
            Assert(self.literal[0].isupper(),"First char of set in TypeTree must be caps") 
        Assert(self.ns is None, "ns value is always None in rootType nodes")
        
        Assert(typ['$'] == 'Tree',"$ value != identifier in bmType: " + typ['$'])
        self.subtrees = []
        
        for subtree in typ['subtrees']:
            self.subtrees.append(bmType(subtree))
        
        Assert(len(self.subtrees) in [0,2],"type has only 0-ary or 2-ary nodes")
        
        bmTypes.append(self)
    def __str__(self):
        if len(self.subtrees) == 0:
            return bmRoot.__str__(self)
        else:
            return self.subtrees[0].__str__() + u" " + bmRoot.__str__(self) + u" " + self.subtrees[1].__str__()
        
class bmTerm(bmRoot):
    '''
        type: inferred type of the expression (bmType object)
        subtrees: list of bmTerms size 0, 1 or 2
            0 Term(+,?)
            0 Term(A[J0],variable)
            0 Term(A[J1],variable)
            0 Term(A,variable)
            0 Term(B[J0,J1],variable)
            0 Term(B[K0,K2],variable)
            0 Term(B[K0,K3],variable)
            0 Term(B[K1,K2],variable)
            0 Term(B[K1,K3],variable)
            0 Term(B,variable)
            0 Term(C[K0,K1,K2],variable)
            0 Term(C[K0,K1,K3],variable)
            0 Term(C[K0,K2,K3],variable)
            0 Term(C[K1,K2,K3],variable)
            0 Term(cons,?)
            0 Term(f,variable)
            0 Term(item,variable)
            0 Term(i,variable)
            0 Term(j,variable)
            0 Term(k,variable)
            0 Term(let,?)
            0 Term(min,?)
            0 Term(nil,?)
            0 Term(?,variable)
            0 Term(w,variable)
            0 Term(\theta,variable)
            0 Term(\psi,variable)
            1 Term(fix,?)
            1 Term(program,?)
            2 Term(:,?)
            2 Term(/,?)
            2 Term(@,?)
            2 Term(\lambdamap,?)

        RTODO: guards (inferred guards!)
    '''
    def __init__(self,trm):
        global bmTerms        
        
        for k in trm.keys():
            Assert(k in ['root','$','type','subtrees','guards'],"trm has \
            more keys than accounted for: " + str(trm.keys()))
        Assert('root' in trm and 'subtrees' in trm, "root and subtrees \
        should be in trm used for initialization")
        Assert(trm['$'] == 'Tree',"$ value not Identifier in " + str(trm["$"]))
        
        bmRoot.__init__(self,trm['root'])
        Assert(self.ns is None or self.ns.isdigit(), "ns is either empty or a valid number")
        if 'type' in trm:
            self.type = bmType(trm['type']) 
            #print json.dumps(self.type,sort_keys=True,indent=2)
        else:
            self.type = None
        
        self.subtrees = []
        for i in trm['subtrees']:
            self.subtrees.append(bmTerm(i))
        
        #print len(self.subtrees),self.__str__()
        
        self.guards = None #TODO: Add guards in JSON
        bmTerms.append(self)
    def __str__(self):
        rootWithType = bmRoot.__str__(self) 
        if self.type is not None:
            rootWithType += u"{" + self.type.__str__() + u"}"
        if len(self.subtrees) == 0:
            return rootWithType
        elif len(self.subtrees) == 2:
            return self.subtrees[0].__str__() + u" " + rootWithType + u" " + self.subtrees[1].__str__()
        else:
            return rootWithType + u" " + self.subtrees[0].__str__()
class bmProgram(object):
    '''
        name: program name for recursion
        params: named arguments to the program
        term: root bmTerm of the program
    '''
    def __init__(self,prg):
        #parse prg to get the components
        Assert("program" in prg and "term" in prg, "program and/or term not available in prg ")
        prg_name = filter(None,re.split('\[|,|\]',prg["program"]))
        self.name = prg_name[0]
        self.params = prg_name[1:]
        self.term = bmTerm(prg["term"])
        self.impl = prg['style'] 
        if "text" in prg:
            self.text = prg["text"]
        else:
            self.text = ""
    def __str__(self):
        retStr = self.name + u"[" 
        retStr += u','.join(self.params)  + u"] " + self.impl+ u": \n"
        retStr += self.term.__str__() 
        return retStr

def getBmProgram(filenames):
    a = []
    prgs = parseJsons(filenames)
    #print prgs.keys()
    for prg in prgs:
        #print prg
        for impl in prgs[prg]:
            #print prg,impl
            a.append(bmProgram(prgs[prg][impl]))
    return a        

def findUniqueVals(l,keys):
    s = set()
    for obj in l:
        noneFound = False
        for key in keys:
            if getattr(obj,key) is None:
                noneFound = True
                break
        if(noneFound):
            continue
        s.add(u'|'.join([getattr(obj,key) for key in keys]))
    print keys,s

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("files", metavar="F",type=str,nargs='+', help="All JSON files")
    args = parser.parse_args()
    prgs = getBmProgram(args.files)
    '''
    findUniqueVals(bmRoots,['literal'])
    findUniqueVals(bmRoots,['literal','ns'])
    findUniqueVals(bmRoots,['kind'])
    findUniqueVals(bmRoots,['literal','kind'])
    findUniqueVals(bmTerms,['literal','kind'])
    findUniqueVals(bmTerms,['literal'])
    '''
    
    for prg in prgs:
        print prg.__str__()
        


if __name__ == "__main__": main()
