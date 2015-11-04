#!/usr/bin/env python
import codecs
import json
import argparse
import re
from string import Template
VALIDFNAMES = [u'A', u'B', u'C']  # TODO: generate automatically based on input files
DEBUG = False

SPACE = u' '
PNAME = None
def getDecl(name, newparams, intv, impl):
    return "func" + name + "_" + impl + "(" + ",".join([intv + x for x in newparams]) + ")"
    
def isSet(string):
    return string != 'U' and (string[0]).isupper() and len(string) <= 2 and (string[0] not in VALIDFNAMES)
     
def Assert(cond, msg):
    if not cond:
        print u"ERROR: " + msg
        raise Exception(msg)
        sys.exit(1)
bmProg = {}
INT = u"int"
INTERVAL = u"interval"
APPLY = u'@'
FIX = u'fix'
MIN = u'min'
PSI = u"\u03C8"
SLASH = u'/'
THETA = u"\u03B8"
MAPSTO = u"\u21A6"
QMARK = u'?'
SUBNUMS = {u"\u2080":0,
           u"\u2081":1,
           u"\u2082":2,
           u"\u2083":3,
           u"\u2084":4,
           u"\u2085":5,
           u"\u2086":6}
VARS = [u'i', u'j', u'k', QMARK, PSI, THETA]



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
        ljsons = x.split(u"\n\n")
        for j in ljsons:
            if len(j) >= 2 and u"vbox" not in j:  # Ignore jsons with no program and extreneous key "vbox"  
                form = json.loads(j)
                Assert(u'program' in form, u"'program' key not present in " + unicode(form.keys()))
                if form[u'program'] not in prgs:
                    prgs[form[u'program']] = dict()
                prgs[form[u'program']][form[u'style']] = form
    return prgs

def arrayAccessStr(funct, largs):
    return funct + u'[' + u']['.join(largs) + u']'
            
def arrayAccess(funct, largs):
    for x in largs:
        x.setCode(False)
    return funct + u'[' + u']['.join([x.code for x in largs]) + u']'

def funCall(funct, largs):
    for x in largs:
        x.setCode(False)
    return funct + u'(' + u','.join([x.code for x in largs]) + u')'

def opInfix(funct, largs):
    for x in largs:
        x.setCode(False)
    return funct.join([x.code for x in largs])

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




class bmRoot(object):
    '''
        literal: string
        kind: (set,?,variable)
        ns: (numeric or None)
    '''
    def __init__(self, root):
        for k in root.keys():
            Assert(k in [u'type', u'literal', u'$', u'kind', u'ns'], "root has more keys than accounted for: " + str(root))
        self.literal = root[u'literal']
        # if self.literal[0] in VALIDFNAMES:
        #    print "LIT: ", self.literal
        if self.literal == u"":
            self.literal = u"B"
        # Assert(self.literal != u"",u"Empty literal found!")
        Assert(root[u'$'] == u'Identifier', u"$ value not Identifier in " + str(root))
        self.kind = root[u'kind']
        if u'ns' in root:
            self.ns = str(root[u'ns'])
        else:
            self.ns = None
    
    def __str__(self):
        retStr = self.literal 
        return retStr

class bmType(bmRoot):
    '''
        subtrees = list of bmType objects (size = 0 or 2) 
    '''
    def __init__(self, typ):
        global bmTypes
        
        for k in typ.keys():
            Assert(k in [u'root', u'_id', u'$', u'subtrees'], u"typ has more keys than accounted for: " + str(typ.keys()))
        # self.root = bmRootType(typ[u'root'])
        
        bmRoot.__init__(self, typ[u'root'])
        
        # first char of sets is a caps
        if self.kind == 'set':
            Assert(self.literal[0].isupper(), "First char of set in TypeTree must be caps: " + self.literal) 
        Assert(self.ns is None, "ns value is always None in rootType nodes")
        
        Assert(typ[u'$'] == 'Tree', "$ value != identifier in bmType: " + typ[u'$'])
        self.subtrees = []
        
        for subtree in typ[u'subtrees']:
            self.subtrees.append(bmType(subtree))
        
        Assert(len(self.subtrees) in [0, 2], "type has only 0-ary or 2-ary nodes")
        
        bmTypes.append(self)
    def __str__(self):
        if self.isUnion():
            return self.subtrees[0] + bmRoot.__str__(self) + self.subtrees[1]
        elif len(self.subtrees) == 0:
            return bmRoot.__str__(self)
        else:
            return u"(" + self.subtrees[0].__str__() + u" " + bmRoot.__str__(self) + u" " + self.subtrees[1].__str__() + u")"
    def isDistinctSet(self, b):
        Assert(self.kind == u'set', u"Only set kind types can be asked this")
        return b[0] == self.literal[0] and b[1:] != self.literal[1:]
    def makeUnion(self, b):
        Assert(self.kind == u'set' and len(self.subtrees) == 0, u'set to be turned into union')
        self.subtrees.append(self.literal)
        self.subtrees.append(b)
        self.literal = u"U"
    def inUnion(self, a):
        Assert(self.isUnion(), "Should be a union type")
        return (a in self.subtrees)
    def isUnion(self):
        return self.literal == u"U"
    def getSet(self):
        Assert(isSet(self.literal) or self.literal == u"U", u"Should be set or union")
        if isSet(self.literal):
            return self.literal
        elif self.literal == u"U":
            return self.subtrees[0] + u"," + self.subtrees[1]
    def arrType(self):
        Assert(self.literal == u"->" and len(self.subtrees) == 2 and self.subtrees[1].literal == "->", u"this should be MAPSTO: " + self.literal)
        return self.subtrees[0].literal, self.subtrees[1].subtrees[0].literal
        
class bmTerm(bmRoot):
    u'''
        type: inferred type of the expression (bmType object)
        subtrees: list of bmTerms size 0, 1 or 2
        id - unique identifier
        tempMade - was a temporary value made for this node and can be used as code?
        guards - a guarding term
    '''
    def __init__(self, trm, parent, prg):
        global bmTerms   
        self.prg = prg
        self.id = len(bmTerms)
        self.tempMade = False
        self.parent = parent
        bmTerms.append(self)     
        for k in trm.keys():
            Assert(k in [u'_id', u'root', u'$', u'type', u'subtrees'], u"trm has more keys than accounted for: " + str(trm.keys()))
        Assert(u'root' in trm and u'subtrees' in trm, u"root and subtrees \
        should be in trm used for initialization")
        Assert(trm[u'$'] == 'Tree', "$ value not Identifier in " + str(trm["$"]))
        if trm[u'root'][u'literal'] == ":":
            # just treat it as subtrees[1]
            self.__init__(trm[u'subtrees'][1], parent, prg)
            return
        bmRoot.__init__(self, trm[u'root'])

        Assert(self.ns is None or self.ns.isdigit(), "ns is either empty or a valid number")
        if u'type' in trm:
            self.type = bmType(trm[u'type']) 
        else:
            self.type = None
        
        self.subtrees = []
        for i in trm[u'subtrees']:
            if i[u'root'][u'literal'] == '|!':
                # guarded expression
                self.subtrees.append(bmTerm(i[u'subtrees'][0], self, prg))
                self.subtrees[len(self.subtrees) - 1].guards = bmTerm(i[u'subtrees'][1], None, prg)
                continue
            self.subtrees.append(bmTerm(i, self, prg))
        
        # Integer terms
        if self.literal == 0 or self.literal == 1:
            self.kind = "const"
            self.literal = str(self.literal)
        elif isRecCall(self.literal):
            
            prg_name = filter(None, re.split('\[|,|\]', self.literal))
            name = prg_name[0]
            newparams = prg_name[1:]
            # Move superset data structure to bmProgram and 
            # maintain the link to bmProg in each term to access it
            # update it during init phase
            # Or just do this computation in the pbmProg ds
        for p in self.subtrees:
            if (p.literal == QMARK):
                # print self.literal, u'\u21A6'
                Assert(self.literal == MAPSTO, u"'?' not to left of ->, " + self.literal)
            for c in p.subtrees:
                if c.literal == '+':
                    Assert(p.literal == u'@' and self.literal == u'@', u"'+' evaluation they are always left of (@)left of (@) isn't valid!")
        
    def strTemp(self):
        self.tempMade = True
        return u"t" + unicode(self.id)
    
    
    def isConsNode(self):
        return self.literal == u'@' and hasattr(self, "funct") and self.funct.literal == u'cons'
    
    def getGuards(self):
        # get all guard expressions in the subtree
        if hasattr(self, "guards"):
            if hasattr(self.guards, "code"):
                return ""  # guard used already
            self.guards.setCode(False)
            # print self.subtrees[1].code
            # print self.__str__()
            return self.guards.code
        else:
            guardList = []
            for i in self.subtrees:
                gi = i.getGuards()
                if gi != u"":
                    guardList.append(gi)
            if len(guardList) == 0:
                return u""
            else:
                return u" && ".join(guardList)
    def printUp(self):
        t = self
        ctr = 0
        while t.parent is not None:
            print '\t'.join('' for x in range(ctr)), t.parent.literal, t.parent.type.__str__()
            t = t.parent
            ctr = ctr + 1
    
    def setConsArgs(self):
        Assert(self.isConsNode(), "Must be a cons apply node here")
        retList = []
        for arg in self.largs:
            if arg.isConsNode():
                arg.setConsArgs()
                retList.extend(arg.consargs)
            elif arg.literal == u'nil':
                continue
            else:
                retList.append(arg)
        self.consargs = retList 
    def getApplyCode(self):
        Assert(self.literal == u'@' and hasattr(self, "funct"), "All set for this @ node")
        op = self.funct.literal
        if op in [PSI, THETA]:
            return arrayAccess(u"dist", self.largs)
        elif op in [u'w']:
            return funCall(op, self.largs)
        elif op == MIN:
            Assert(len(self.largs) == 1, "min is unary!")
            child = self.largs[0]
            if child.literal == MAPSTO:
                # minimize over a range denoted by free variables
                rs = self.buildForLoop(child.fvranges, child.boundExpr, self.getGuards(), MIN, self.strTemp())
                return rs 
            elif child.isConsNode():
                # minimize over a list in consargs
                Assert(len(child.consargs) == 2 , "Min should be Binaryyyy")
                for x in child.consargs:
                    x.setCode(False)
                return u"min(" + u",".join(x.code for x in child.consargs) + u")"
            else:
                Assert(False, u"min should have only MAPSTO or cons as children: " + child.literal)
        elif op == u"cons":
            Assert(len(self.largs) == 2 , "cons is always binary")
            # print len(self.consargs),self.consargs
            return u','.join([arg.string(False) for arg in self.consargs])
        elif op == u'+':
            Assert(len(self.largs) == 2 , "+ is always binary")
            return opInfix(op, self.largs)
        elif self.funct.literal == MAPSTO and self.funct.subtrees[0].literal == PSI:
            Assert(len(self.largs) == 1, "MAPSTO with multiple freevars not expected")
            # thing on the "right" happens first from a procedural standpoint
            self.largs[0].setCode(False)
            self.funct.boundExpr.setCode(False)
            rs = self.largs[0].code
            # print "L0str: ",self.largs[0].__str__(), rs
            if(rs != u"" and rs[-1] != u";"):
                rs += u";"
            if rs != u"" and self.funct.boundExpr.code != u"":
                # print "boundE: ",self.funct.boundExpr.code
                rs += u"\n" + self.funct.boundExpr.code
                if self.funct.boundExpr.code[-1] != u";":
                    rs += u";"
            return rs
        elif self.funct.literal == SLASH:
            Assert(len(self.largs) == 1, "largs must be size 1")
            self.funct.setCode(False)
            rs = self.funct.code
            if self.largs[0].literal != PSI:
                self.largs[0].setCode(False)
                rs += ";" + self.largs[0].code
            return rs
        elif hasattr(self.funct, u"code") and len(self.largs) == 1 and self.largs[0].literal == PSI:
                return self.funct.code
        else:
            Assert(False, u"Apply term not handled: " + self.__str__())

    def setFunAndArgs(self):
        if hasattr(self, "funct"):
            return
        Assert(self.literal == u'@', "Can't get function when its not apply node")
        if self.subtrees[0].literal != u'@':
            retv = (self.subtrees[0], [self.subtrees[1]])
        else:
            self.subtrees[0].setFunAndArgs()
            funct = self.subtrees[0].funct
            largs = list(self.subtrees[0].largs)
            largs.append(self.subtrees[1])
            retv = (funct, largs)
        self.funct = retv[0]
        self.largs = retv[1]
    def setFreeVarsAndExpr(self):
        if hasattr(self, u"fvranges"):
            return
        Assert(self.literal == MAPSTO, u"Can't get free vars when its not apply node")
        Assert(self.subtrees[0].literal in VARS, u"LHS of MAPSTO must be a free var name: " + self.subtrees[0].literal)
        fv = (self.subtrees[0].literal, self.subtrees[0].type)
        if self.subtrees[1].literal != MAPSTO:
            retv = ([fv], self.subtrees[1])
        else:
            self.subtrees[1].setFreeVarsAndExpr()
            fvranges = list(self.subtrees[1].fvranges)
            boundExpr = self.subtrees[1].boundExpr
            fvranges.insert(0, fv)
            retv = (fvranges, boundExpr)
        self.fvranges = retv[0]
        self.boundExpr = retv[1] 
    def getFVRangeStr(self):
        Assert(self.literal == MAPSTO, "Must be MAPSTO node")
        rs = u""
        for v, r in self.fvranges:
            if v in VARS and v not in [PSI, THETA]:
                rs += u"[" + v + u" in " + r.__str__() + u"]"
        return rs
    def getCode(self):
        Assert(hasattr(self, "code"), "setCode must have been called by now")
        if self.tempMade:
            return self.strTemp()
        else:
            return self.code
    def getTempDefs(self, temps):
        if self.tempMade:
            temps[self.id] = self.preCode
        for x in self.subtrees:
            if x.literal != SLASH: 
                x.getTempDefs(temps)
    def getTempDefsStr(self):
        temps = {}
        rs = u""
        self.getTempDefs(temps)
        for k in sorted(temps.keys()):
            rs += temps[k] + u"\n"
        return rs            
    def buildForLoop(self, fvranges, boundExpr, guardExpr, mode, tmpVar=""):
        # compute the tmpVar using evalExpr in a loop
        # constraining the loopVar using both loopType and guardExpr
        rs = u""
        lsargs = []
        boundExpr.setCode(False)
        if mode == MIN:
            rs += u"\nTYPE " + tmpVar + u"= MAXVAL;\n"
        fvrUp = filter(lambda (v, r): v not in [THETA, QMARK], fvranges)
        forDiag = False
        if len(fvrUp) == 2 and isSet(fvrUp[0][1].literal) and isSet(fvrUp[1][1].literal):
            # i,j - in two sets
            v0 = fvrUp[0][0]
            v1 = fvrUp[1][0]
            r0 = fvrUp[0][1]
            r1 = fvrUp[1][1]
            rs += self.prg.forPre() + u"(" + v0 + u"," + v1 + u"," + r0.getSet() + u"," + r1.getSet() + u",\n"
            forDiag = True
            lsargs =[v0,v1]
        else:
            for v, r in fvrUp:
                Assert(v in VARS and v not in [PSI, THETA], u"Can't have PSI/THETA inside MAPSTO")
                Assert(r.literal != MAPSTO, u"this variable must be INT SET/UNION type")
                Assert(isSet(r.literal) or r.literal == u'U', u"No other loopVarTypes supported: " + r.__str__())
                if r.literal == u"U":
                    rs += u"FORUNION(" + v + u"," + r.getSet() + u",\n"
                else:
                    rs += self.prg.forPre() + u"(" + v + u"," + r.getSet() + u"){\n"
                lsargs.append(v)
        
        
        # add any temporary definitions
        if mode != MIN:
            tdfs = self.getTempDefsStr()
            # Assert(tdfs = u"",u"Temp def shouldn be empty: " + tdfs)
            rs += tdfs
        
        if guardExpr != u"":
            rs += u"if (" + guardExpr + u"){\n"
        
        if mode == MIN:
            rs += tmpVar + u" = min(" + tmpVar + u"," + boundExpr.code + u");\n"
        elif mode == THETA or mode == u"default":
            rs += arrayAccessStr(u"dist", lsargs) + u" = " + boundExpr.code + u";\n"
        else:
            Assert(False, u"mode not defined: " + mode)
        
        if guardExpr != u"":
            rs += u"}\n"
        
        if forDiag:
            rs += u")\n"
        else:
            for v, r in fvrUp:
                if v in [QMARK, THETA]:
                    continue
                if r.literal == u"U":
                    rs += u")\n"
                else:
                    rs += u"}\n"
        
        return rs
    
    def setCode(self, typed=True):
        if hasattr(self, "code"):
            return
        rootWithType = bmRoot.__str__(self) 
        if self.type is not None and typed:
            rootWithType += u"{" + self.type.__str__() + u"}"
        
        if self.literal == MAPSTO:
            if self.parent is not None and self.parent.literal in [SLASH, FIX]:
                # This is array recomputation
                rs = self.buildForLoop(self.fvranges, self.boundExpr, "", u"default")
            elif self.subtrees[0].literal == PSI:
                self.subtrees[1].setCode(False)
                rs = self.subtrees[1].code
            else:
                # print self.parent.__str__()
                print self.__str__()
                Assert(False, "Why here?")
                
                rs = u""
                rs += self.getFVRangeStr()
                self.boundExpr.setCode(False)
                rs += self.getTempDefsStr()
                rs += self.boundExpr.code 
            self.code = rs
        elif self.literal == '@':
            self.code = self.getApplyCode()
        elif self.literal == FIX:
            # TODO: Get "read set": {J0xJ0, J0xJ1, J1xJ1}
            Assert(len(self.subtrees) == 1, "fix should be unary")
            # x = self.getGuards()
            self.subtrees[0].setCode(False)
            self.code = self.subtrees[0].code
            # print self.type.readset, x, self.__str__()
            # Assert(False,u"fix not implemented yet")
        elif self.literal in [u'<', u'>', u'==', u'!=', u'&', u'|']:
            # binary infix operators
            Assert(len(self.subtrees) == 2, "binary infix operators")
            op = self.literal
            if op == u'&':
                op = u' && '
            self.code = opInfix(op, self.subtrees)
        elif isSet(self.literal):
             # guard computation
             Assert(len(self.subtrees) == 1 and len(self.subtrees[0].subtrees) == 0, "IN SET guard")
             self.code = u"INSET(" + self.subtrees[0].literal + u"," + self.literal + u")"
        elif self.literal == u"|!":
            # guarded expression
            # subtrees[1] is the condition
            # Assert(False,"False")
            Assert(len(self.subtrees) == 2, "guarded expression should have 2 children")
            # print self.__str__()
            retStr = u""
            guarding = (not hasattr(self.subtrees[1], "code"))
            if guarding:
                self.subtrees[1].setCode(False)
                retStr = u"if(" + self.subtrees[1].code + u"){\n"
            self.subtrees[0].setCode(False)
            retStr += self.subtrees[0].code 
            if guarding:
                retStr += u"\n}\n"
            self.code = retStr
        elif self.literal == SLASH:
            # print "SLASH: ",self.parent.parent.literal,self.parent.parent.type.__str__(),self.type.arrType(),self.subtrees[0].type.arrType(),self.subtrees[1].type.arrType()
            # self.setSlashRelationships()
            cmds = []
            for x in self.subtrees:
                x.setCode(False)
                if x.literal == PSI or (x.literal == MAPSTO and x.subtrees[0].literal == QMARK and x.subtrees[1].literal == PSI):
                    continue;
                elif x.literal == SLASH or (x.literal != PSI and x.code != u""):
                    cmds.append(x.code)
                else:
                    Assert(False, "Not accessible: " + x.literal)
            # print cmds
            if len(cmds) == 1:
                self.code = cmds[0]
            elif len(cmds) == 2:
                self.code = cmds[0] + u";" + cmds[1]
            else:
                self.code = u""
        elif len(self.subtrees) == 0:
            self.code = rootWithType
        elif len(self.subtrees) == 2:
            Assert(False, "Case not taken care of: " + self.getDebug())
            self.subtrees[0].setCode(False)
            self.subtrees[1].setCode(False)
            self.code = u"(" + self.subtrees[0].code + u" " + rootWithType + u" " + self.subtrees[1].code + u")"
        elif len(self.subtrees) == 1:
            self.subtrees[0].setCode(False)
            self.code = rootWithType + u" " + self.subtrees[0].code
        else:
            Assert(False, "subtrees can only be 0,1,2 sized!")

        if self.tempMade:
            self.preCode = self.code
            self.code = self.strTemp()
        
        
        
    def getDebug(self):
        if DEBUG:
            if self.parent and self.parent.literal == u'@':
                return  u','.join([unicode(self.id), self.literal, self.parent.literal, self.parent.funct.literal, unicode(len(self.parent.largs))])
        return self.literal + u":" + self.type.__str__()
    def __str__(self, ctr=0, typed=True):
        spacings = u''.join([SPACE for i in range(ctr)])
        if typed:
            rootstr = self.literal + u' | ' + self.type.__str__() + u' | '
        else:
            rootstr = self.literal
        if len(self.subtrees) == 0:
            return spacings + rootstr + u'\n'
           
        retStr = spacings + u'{\n'
        retStr += spacings + SPACE
        if hasattr(self, "guards"):
            retStr += "GUARD " + self.guards.__str__(ctr + 1, False) + spacings + SPACE
        if hasattr(self, 'funct') and self.funct.literal != MAPSTO:
            retStr += self.funct.literal + u' | ' + self.funct.type.__str__() + u' | \n'
            if self.isConsNode():
                for i in self.consargs:
                    retStr += i.__str__(ctr=ctr + 1, typed=typed)
            else:
                for i in self.largs:
                    retStr += i.__str__(ctr=ctr + 1, typed=typed)
        elif hasattr(self, 'fvranges') and self.literal == MAPSTO:
            # get fvranges, boundExpr, largs
            retStr += u"[|"
            for v, r in self.fvranges:
                retStr += v + u":" + r.__str__() + u"|" 
            retStr += u"] : " + self.type.__str__() + u"\n"
            retStr += self.boundExpr.__str__(ctr=ctr + 1, typed=typed)
            # for i in self.largs:
            #    retStr += i.__str__(ctr=ctr+2,typed=typed)
        else:
            retStr += rootstr + u'\n'
            for i in self.subtrees:
                retStr += i.__str__(ctr=ctr + 1, typed=typed)
        return retStr + spacings + u'}\n'
        
        
        
class bmProgram(object):
    '''
        name: program name for recursion
        params: named arguments to the program
        term: root bmTerm of the program
    '''
    def __init__(self, prg):
        # parse prg to get the components
        global bmProg
        global PNAME
        Assert("program" in prg and "term" in prg, "program and/or term not available in prg ")
        prg_name = filter(None, re.split('\[|,|\]', prg["program"]))
        self.name = prg_name[0]
        bmProg[self.name] = self
        PNAME = self.name 
        self.params = prg_name[1:]
        Assert(prg["term"]["root"]["literal"] == "program", "'program' literal not found in root of first term")
        Assert(len(prg["term"]["subtrees"]) == 1, "'program' should have one central root term")
        self.impl = prg[u'style'] 
        if "text" in prg:
            self.text = prg["text"]
        else:
            self.text = ""
        self.term = bmTerm(prg["term"]["subtrees"][0], None, self)
        self.superset = {}
        self.addStateVars(self.term)
        self.computeSupersets(self.term)
        if DEBUG:
            print self.name, self.impl, "superset: ", self.superset
        self.addStateVarsSecond(self.term)
        
            
    def addStateVars(self, trm):
        if trm.literal == MAPSTO:
            trm.setFreeVarsAndExpr()
        elif trm.literal == u'@':
            trm.setFunAndArgs()
            Assert(hasattr(trm, "funct"), "No funct!")
        for child in trm.subtrees:
            self.addStateVars(child)
    
    def addStateVarsSecond(self, trm):
        if trm.isConsNode():
            trm.setConsArgs()
        elif trm.literal == u'fix':
            readSet = getReadSet(trm)
            # print "ReadSet: ",readSet
            refineTypes(trm, readSet) 
        for child in trm.subtrees:
            self.addStateVarsSecond(child)
    def forPre(self):
        if not hasattr(self, "forCtr"):
            self.forCtr = 0
        self.forCtr += 1
        return u"FOR_" + self.name + u"_" + self.impl + u"_" + str(self.forCtr)
        
    def tempDefCode(self):
        # go over the superset entries and divide the supersets equally!
        # collect supersets
        lefts = {}
        retStr = u""
        for i in sorted(self.superset.keys()):
            if self.superset[i] not in lefts:
                lefts[self.superset[i]] = []
            lefts[self.superset[i]].append(i)
        for K in lefts:
            n = len(lefts[K])
            Assert(n == 2, "Must divide the set by 2")
            L0 = lefts[K][0]
            retStr += INTERVAL + u" " + L0 + u" = {" + K + u".begin,(" + K + u".end + " + K + u".begin)/2};\n"
            # retStr += L0+u".begin = "+K+u".begin;\n"
            # retStr += L0+u".end = ("+K+u".end + "+K+u".begin)/2;\n"
            L1 = lefts[K][1]
            retStr += INTERVAL + u" " + L1 + u" = {" + L0 + u".end," + K + u".end};\n"
            # retStr += L1+u".begin = "+L0+u".end;\n"
            # retStr += L1+u".end = "+K+u".end;\n"
        return retStr    
    def setSupersetRelationships(self, newparams):
        Assert(len(self.params) == len(newparams), u"Params and newparams aren't same!: ")
        for i in range(len(self.params)):
            if newparams[i] in self.superset:
                Assert(self.superset[newparams[i]] == self.params[i], "Can't have a different superset!")
            else:
                self.superset[newparams[i]] = self.params[i]    
    def computeSupersets(self, curtrm):
        
        if isRecCall(curtrm.literal):
            prg_name = filter(None, re.split('\[|,|\]', curtrm.literal))
            name = prg_name[0]
            newparams = prg_name[1:]
            if name == self.name:
                self.setSupersetRelationships(newparams)
            # set the code for these terms!
            curtrm.code = getDecl(name, newparams, "", "rec")
        else:
            for i in curtrm.subtrees:
                self.computeSupersets(i)
    def getBaseCase(self):
        Assert(self.impl == u"rec", u"Should be recursive!")
        retStr = u"if (BASE_CONSTRAINT_" + self.name + u"(" + u",".join(self.params) + u")){\n"
        retStr += getDecl(self.name, self.params, u"", impl=u"loop") + u";\n"
        retStr += u"return;\n"
        retStr += u"}"
        return retStr 
    def printCode(self):
        # print "#define FOR_FORWARD(i,s,e) for(int i=s;i<e;i++)"
        # print "#define FOR_BACKWARD(i,s,e) for(int i=e-1;i>=s;i--)"
        self.term.setCode(False)
        intv = INTERVAL + u" "
        print u"void " + getDecl(self.name, self.params, intv, self.impl) + u"{"
        if self.impl == u"rec":
            print self.getBaseCase()
        print self.tempDefCode()
        print self.term.code
        print u"}"
    def __str__(self):
        retStr = self.name + u"[" 
        retStr += u','.join(self.params) + u"] " + self.impl + u": \n"
        retStr += self.term.__str__() 
        return retStr

def getBmProgram(filenames):
    a = []
    prgs = parseJsons(filenames)
    # print prgs.keys()
    for prg in prgs:
        # print prg
        implList = []
        if u'loop' in prgs[prg]:
            implList.append(u'loop')
        if u'rec' in prgs[prg]:
            implList.append(u'rec')
        
        for impl in implList:
            # print prg,impl
            a.append(bmProgram(prgs[prg][impl]))
    return a        

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

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--debug", action='store_true')
    parser.add_argument("files", metavar="F", type=str, nargs='+', help="All JSON files")
    args = parser.parse_args()
    prgs = getBmProgram(args.files)
    
    if args.debug:
        for prg in prgs:
            print prg.text
            print prg.__str__()
     
    for prg in prgs:
        superset = {}
        # print "PANEM: ",PNAME
        # print prg.text
        prg.printCode()
        
    
       
    # print superset
    
    # printSlashes() 
      


if __name__ == "__main__": main()
