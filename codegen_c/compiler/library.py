#!/usr/bin/env python
import codecs
import json
import argparse
import re
import os
from string import Template

LPDEBUG = False
VALIDFNAMES = [u'A', u'B', u'C', u'D']  # RTODO: generate automatically based on input files
DEBUG = False
GUARD = u'|!'
SPACE = u' '
PNAME = None
keepTempInMin = True
noLoopGuardOptim = False


def areDisjoint(I,J,superset):
    if topSuperset(I,superset,[]) != topSuperset(J,superset,[]) or I==J:
        return ""
    else:
        if I not in superset or J not in superset:
            return ""
        elif superset[I] == superset[J]:
            if I <J:
                return "x<y"
            else:
                return "y<x"
        else:
            leftEval = areDisjoint(superset[I],J,superset)
            if leftEval != "":
                return leftEval
            rightEval = areDisjoint(I,superset[J],superset)
            if rightEval != "":
                return rightEval
            return ""
            
            
def isLeft(M,K,superset):
    Assert(superset[M] == K,"Must be a subset-superset pair M \in K")
    extraSubsets = filter(lambda (J0,J): J0 != M and J == K,superset.iteritems())
    #print "eSubs:",extraSubsets, M, K, superset
    Assert(len(extraSubsets) == 1, K + " should have exactly 2 partitions!")
    return M < Mp

def isSubset(M,K,superset):
    if M in superset and superset[M] == K:
        return True
    elif M not in superset:
        return False
    else:
        return isSubset(superset[M],K,superset)
def topSuperset(M,superset,params):
    if M not in superset or M in params:
        return M
    else:
        return topSuperset(superset[M],superset,params)
            
def getDecl(name, newparams, intv, impl):
    if type(intv) is str or type(intv) is unicode:
        return "func" + name + "_" + impl + "(" + ",".join([intv + x for x in newparams]) + ")"
    else:
        return "func" + name + "_" + impl + "(" + ",".join([intv(x) for x in newparams]) + ")"
def isSet(string):
    return string != 'U' and (string[0]).isupper() and len(string) <= 2 and (string[0] not in VALIDFNAMES)
     
def Assert(cond, msg):
    if not cond:
        print (u"ERROR: " + msg).encode('utf-8')
        import pdb 
        pdb.set_trace()
        
        raise Exception(msg)
        sys.exit(1)
bmProg = {}
INT = u"int"
INTERVAL = u"interval"
def defineIntervalCall(I):
    return u"PARAM("+I+u")"
def defineIntervalStmt(I):
    return u"DEFINTERVALSTMT("+I+u")"
def defineIntervalFunc(I):
    return u"DEFINTERVALFUNC("+I+u")"
def defineBegin(I):
    return u"DEFBEGIN("+I+u")"
def defineEnd(I):
    return u"DEFEND("+I+u")"
def defineInSet(i,I):
    return u"INSET(" + i + u"," + I + u")"
APPLY = u'@'
FIX = u'fix'
MIN = u'min'
MAX = u'max'

AND = u'\u2227'
PSI = u"\u03C8"
PLUS = u'+'
SLASH = u'/'
THETA = u"\u03B8"
MAPSTO = u"\u21A6"
MINUS = u'-'
QMARK = u'?'
OMAX=u'\u2a01'

LT=u"<"
DELTA=u'\u03b4'
NEG = u'\u00ac'
STMTEND=[u"}",u";"]
PARLEVEL = u"PARLEVEL"
MULT = u'\u00d7'
INTERSECT=u'\u2229'

def refineLP(loopEndPoints,v,newlow,newhigh):
    finallow = "max(" + loopEndPoints[v][0] + "," + newlow + ")" if newlow != loopEndPoints[v][0] else newlow
    finalhigh = "min(" + loopEndPoints[v][1] + "," + newhigh + ")" if newhigh != loopEndPoints[v][1] else newhigh 
    loopEndPoints[v] = (finallow,finalhigh)
    

def addParLims(s,pd):
    return u"\nPARBOO/* "+PARLEVEL+u" "+ unicode(pd) +u" */ " +s + "PARBOO" 

def endStmt(s):
    if s != u"" and s[-1] not in STMTEND and (not (s[-1]==u"\n" and s[-2] in STMTEND)):
        return s + u";"
    else:
        return s
SUBNUMS = {u"\u2080":0,
           u"\u2081":1,
           u"\u2082":2,
           u"\u2083":3,
           u"\u2084":4,
           u"\u2085":5,
           u"\u2086":6,
           u"w'":u"w_prime"}
VARS = [u'i', u'j', u'k', QMARK, PSI, THETA, u'p',u'q']




def sanitizeSubs(string):
    for c in SUBNUMS:
        string = string.replace(c, unicode(SUBNUMS[c]))
    return string

def parseJsons(files):
    prgs = dict()
    for fname in files:
        f = codecs.open(fname, u"r", u"utf-8")
        x = f.read()
        x = sanitizeSubs(x)
        Assert(u'\u2080' not in x, u"Can't have subscripted unicode letter")
        #print "OS",os.name
        if os.name == 'nt':
            ljsons = x.split(u"\n\n")
        else:
            ljsons = x.split(u"\n\n")
        for j in ljsons:
            if len(j) >= 2 and u"vbox" not in j:  # Ignore jsons with no program and extreneous key "vbox"  
                form = json.loads(j)
                Assert(u'program' in form, u"'program' key not present in " + unicode(form.keys()))
                if form[u'program'] not in prgs:
                    prgs[form[u'program']] = dict()
                prgs[form[u'program']][form[u'style']] = form
    return prgs
    
def arrayAccessStr(prg,funct, largs):
    #return funct + u'[' + u']['.join(largs) + u']'
    return u"D" + prg.preDist() + funct + u'(' + u','.join(largs) + u')'
def arrayAccess(prg,funct, largs, ctx):
    for x in largs:
        x.setCode(ctx)
    #return funct + u'[' + u']['.join([x.code for x in largs]) + u']'
    return u"D" + prg.preDist() + funct + u'(' + u','.join([x.code for x in largs]) + u')'
    
def funCall(funct, largs, ctx):
    for x in largs:
        x.setCode(ctx)
    return funct + u'(' + u','.join([x.code for x in largs]) + u')'

def opInfix(funct, largs, ctx):
    for x in largs:
        x.setCode(ctx)
    return funct.join([x.code for x in largs])

def getAllFVsets(code,fvSets):
    for i in range(len(code)):
        for DEFSTR in ["DEFBEGIN(","DEFEND("]:
            if code[i:i+len(DEFSTR)] == DEFSTR:
                z = code[i+len(DEFSTR):].find(")")
                K = code[i+len(DEFSTR):i+len(DEFSTR)+z]
                fvSets.add(K)
                Assert(isSet(K),"Must be a set: "+ K)
        if code[i:i+6] == "INSET(":
            z1 = code[i+6:].find(",")
            z2 = code[i+6:].find(")")
            K = code[i+7+z1:i+6+z2]
            fvSets.add(K)
            Assert(isSet(K),"Must be a set: "+ K)
    

bmTypes = []
bmTerms = []

def isRecCall(nm):
    return nm[0] in VALIDFNAMES and nm[1] == u'[' and nm[len(nm) - 1] == u']'

def getReadSet(trm):
    if trm.literal == PSI:
        return [trm.type.arrType()]
    elif trm.type is None:
        return []
    else:
        retSet = []
        for i in trm.subtrees:
            tmpSet = getReadSet(i)
            for (a, b) in tmpSet:
                if (a, b) not in retSet:
                    retSet.append((a, b))
        return retSet
    
def refineTypes(trm, readSet, freeVars={}):
    # Whenever we see a theta, we refine
    # for each component
    # varname,ns -> go up and update the type of freevar nodes
    # print "refineTypes: ",trm.literal
    if trm.literal == MAPSTO and trm.subtrees[0].type is not None and isSet(trm.subtrees[0].type.literal):
        freeVars[(trm.subtrees[0].literal, trm.subtrees[0].ns)] = (trm.subtrees[0])
    elif trm.literal == APPLY and trm.funct.literal == THETA:
        Assert(len(trm.largs) == 2, "Only 2 args supported for theta: " + trm.__str__())
        lv = trm.largs[0]
        rv = trm.largs[1]
        if lv.literal == APPLY or rv.literal == APPLY:
            return
        Assert((lv.literal, lv.ns) in freeVars, "lvar of Theta not in freeVars!")
        lfv = freeVars[(lv.literal, lv.ns)]
        Assert((rv.literal, rv.ns) in freeVars, "rvar of Theta not in freeVars!")
        rfv = freeVars[(rv.literal, rv.ns)]
        # force lv/rv constraints from readSet 
        for (a, b) in readSet:
            if lfv.type.literal == a and rfv.type.literal == b:
                continue
            elif lfv.type.literal != a and rfv.type.literal != b:
                continue
            elif lfv.type.literal == a and rfv.type.literal != b:
                chfv = rfv
                updateType = b
            elif lfv.type.literal != a and rfv.type.literal == b:
                chfv = lfv
                updateType = a
            
            if chfv.type.isUnion() and chfv.type.inUnion(updateType):
                continue
            elif updateType[0] == chfv.type.literal:
                chfv.type.literal = updateType
                # b was a subset of actual set there, refine the type!
            elif chfv.type.isDistinctSet(updateType):
                # make union
                chfv.type.makeUnion(updateType)
            else:
                print  trm.__str__() 
                print "L:", lfv.__str__()
                print "R:", rfv.__str__()
                Assert(False, "Set type expansion Not supported: " + a + "," + b)       
        return
    for i in trm.subtrees:
        refineTypes(i, readSet, freeVars)


def getComponents(trm,comps):
    if isComponent(trm):
        if trm not in comps:
            comps.append(trm)
    else:
        
        Assert(trm.literal in [AND,NEG],"only AND/NEG allowed in guards around basic blocks for now: " + trm.__str__())
        for x in trm.subtrees:
            getComponents(x,comps)        


        
def getUsedVarsInGuards(trm,uvars):
    if hasattr(trm, "guards"):
        getUsedVars(trm.guards,uvars)
    for x in trm.subtrees:
        getUsedVarsInGuards(x,uvars)
        
def getUsedVars(trm,uvars):
    if len(trm.subtrees) == 0:
        if trm.literal in VARS and trm.literal not in uvars:
            uvars.append(trm.literal)
    else:
        searchSet = trm.subtrees
        if trm.literal == APPLY:
            Assert(hasattr(trm,"funct"),u"funct should be built in this apply node")
            searchSet = trm.largs
        for x in searchSet:
            getUsedVars(x,uvars)
       
def getGuardComponents(trm,comps):
    if hasattr(trm, "guards"):
        getComponents(trm.guards,comps)
    for x in trm.subtrees:
        getGuardComponents(x,comps)

def isComponent(trm):
    if isSet(trm.literal) and len(trm.subtrees) == 1:
        return True
    if trm.literal == LT and len(trm.subtrees) == 2 and trm.subtrees[0].isPlus() and isComponent(trm.subtrees[0]) and len(trm.subtrees[1].subtrees) == 0:
        return True
    if trm.literal == APPLY or trm.literal == NEG :
        return True
    if len(trm.subtrees) == 0 or trm.literal == AND:
        return False
    isComp = True
    for x in trm.subtrees:
        if len(x.subtrees) != 0:
            return False
    return True
 
def eqGuards(g1,g2):
    ng1 =  len(g1.subtrees)
    ng2 =  len(g2.subtrees)
    if g1.literal == g2.literal and ng1 == 0 and ng2 == 0:
        return True
    if g1.literal != g2.literal or ng1 != ng2:
        return False
    for i in range(ng1):
        if not eqGuards(g1.subtrees[i], g2.subtrees[i]):
            return False
    return True

def addSS(ss2,ss):
    for k in ss2: 
        if k in ss:
            Assert(ss[k] == ss2[k],"information overwritten: " + k + ","  + ss[k] + "," + ss2[k])
        ss[k] = ss2[k]
        
def findUniqueVals(l, keys):
    s = set()
    for obj in l:
        noneFound = False
        for key in keys:
            if getattr(obj, key) is None:
                noneFound = True
                break
        if(noneFound):
            continue
        s.add(u'|'.join([getattr(obj, key) for key in keys]))
    print keys, s

def setProblem(s):
    global problem
    problem = s

def getProblem():
    global problem
    return problem