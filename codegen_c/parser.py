#!/usr/bin/env python
import codecs
import json
import argparse
import re
from string import Template
DEBUG = True
superset = {}
SPACE = u' '



     
def Assert(cond,msg):
    if not cond:
        print u"ERROR: " + msg
        raise Exception(msg)
        sys.exit(1)
bmProg = {}
INT = u"int"
PSI = u"\u03C8"
THETA = u"\u03B8"
MAPSTO = u"\u21A6"
SUBNUMS = {u"\u2080":0,
           u"\u2081":1,
           u"\u2082":2,
           u"\u2083":3,
           u"\u2084":4,
           u"\u2085":5,
           u"\u2086":6}
VARS = [u'i',u'j',u'k',u'?',PSI, THETA]

def tempDefCode():
    #go over the superset entries and divide the supersets equally!
    #collect supersets
    lefts = {}
    retStr = u""
    for i in sorted(superset.keys()):
        retStr += INT+u" "+i+u"_start;\n"
        retStr += INT+u" "+i+u"_end;\n"

        if superset[i] not in lefts:
            lefts[superset[i]] = []
        lefts[superset[i]].append(i)
    for K in lefts:
        n = len(lefts[K])
        Assert(n == 2,"Must divide the set by 2")
        L0 = lefts[K][0]
        retStr += L0+u"_start = "+K+u"_start;\n"
        retStr += L0+u"_end = ("+K+u"_end -"+u"_start)/2;\n"
        L1 = lefts[K][1]
        retStr += L1+u"_start = "+L0+u"_end;\n"
        retStr += L1+u"_end = "+K+u"_end;\n"
    return retStr

def sanitizeSubs(string):
    for c in SUBNUMS:
        string = string.replace(c,unicode(SUBNUMS[c]))
    return string
def parseJsons(files):
    prgs = dict()
    for fname in files:
        f = codecs.open(fname,u"r",u"utf-8")
        x = f.read()
        x = sanitizeSubs(x)
        Assert(u'\u2080' not in x,u"Can't have subscripted unicode letter")
        ljsons = x.split(u"\n\n")
        for j in ljsons:
            if len(j) >= 2 and u"vbox" not in j: #Ignore jsons with no program and extreneous key "vbox"  
                form = json.loads(j)
                Assert(u'program' in form,u"'program' key not present in " + unicode(form.keys()))
                if form[u'program'] not in prgs:
                    prgs[form[u'program']] = dict()
                prgs[form[u'program']][form[u'style']] = form
    return prgs



def arrayAccessStr(funct,largs):
    return funct + u'[u' + u'][u'.join(largs) + u']'
            
def arrayAccess(funct,largs):
    for x in largs:
        x.setCode(False)
    return funct + u'[u' + u'][u'.join([x.code for x in largs]) + u']'
def funCall(funct,largs):
    for x in largs:
        x.setCode(False)
    return funct + u'(' + u','.join([x.code for x in largs]) + u')'
def opInfix(funct,largs):
    for x in largs:
        x.setCode(False)
    return funct.join([x.code for x in largs])

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
            Assert(k in [u'literal','$','kind','ns'],"root has more keys than accounted for: " + str(root))
        self.literal = root[u'literal']
        Assert(root[u'$'] == 'Identifier',"$ value not Identifier in " + str(root))
        self.kind = root[u'kind']
        if 'ns' in root:
            self.ns = str(root[u'ns'])
        else:
            self.ns = None
    def __str__(self):
        retStr = self.literal 
        return retStr
        '''if self.kind != u'?':
            retStr+= u"[" + self.kind
            if(self.ns is None):
                return retStr + u"]"
            else:
                return retStr + u"," + self.ns  + u"]"
        else:
            return retStr   
        ''' 
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
            Assert(k in [u'root','$','subtrees'],"typ has more keys than accounted for: " + str(typ.keys()))
        #self.root = bmRootType(typ[u'root'])
        
        bmRoot.__init__(self,typ[u'root'])
        
        #first char of sets is a caps
        if self.kind == 'set':
            Assert(self.literal[0].isupper(),"First char of set in TypeTree must be caps") 
        Assert(self.ns is None, "ns value is always None in rootType nodes")
        
        Assert(typ[u'$'] == 'Tree',"$ value != identifier in bmType: " + typ[u'$'])
        self.subtrees = []
        
        for subtree in typ[u'subtrees']:
            self.subtrees.append(bmType(subtree))
        
        Assert(len(self.subtrees) in [0,2],"type has only 0-ary or 2-ary nodes")
        
        bmTypes.append(self)
    def __str__(self):
        if len(self.subtrees) == 0:
            return bmRoot.__str__(self)
        else:
            return u"(" +self.subtrees[0].__str__() + u" " + bmRoot.__str__(self) + u" " + self.subtrees[1].__str__() + u")"
    
    def arrType(self):
        Assert(self.literal == "->" and len(self.subtrees) == 2 and self.subtrees[1].literal == "->",u"this should be MAPSTO: " + self.literal)
        return self.subtrees[0].literal,self.subtrees[1].subtrees[0].literal
        
class bmTerm(bmRoot):
    u'''
        type: inferred type of the expression (bmType object)
        subtrees: list of bmTerms size 0, 1 or 2
        RTODO: guards (inferred guards!)
    '''
    def __init__(self,trm,parent):
        global bmTerms   
        self.guards = None #TODO: Add guards in JSON
        self.id = len(bmTerms)
        self.tempMade = False
        self.parent = parent
        bmTerms.append(self)     
        for k in trm.keys():
            Assert(k in [u'root',u'$',u'type',u'subtrees',u'guards'],u"trm has \
            more keys than accounted for: " + str(trm.keys()))
        Assert(u'root' in trm and u'subtrees' in trm, u"root and subtrees \
        should be in trm used for initialization")
        Assert(trm[u'$'] == 'Tree',"$ value not Identifier in " + str(trm["$"]))
        if trm[u'root'][u'literal'] == ":":
            #just treat it as subtrees[1]
            self.__init__(trm[u'subtrees'][1],parent)
            return
        
        bmRoot.__init__(self,trm[u'root'])
        Assert(self.ns is None or self.ns.isdigit(), "ns is either empty or a valid number")
        if 'type' in trm:
            self.type = bmType(trm[u'type']) 
            #print json.dumps(self.type,sort_keys=True,indent=2)
        else:
            self.type = None
        
        self.subtrees = []
        for i in trm[u'subtrees']:
            self.subtrees.append(bmTerm(i,self))

        for p in self.subtrees:
            if (p.literal == u'?'):
                #print self.literal, u'\u21A6'
                Assert(self.literal == MAPSTO,u"'?' not to left of ->, "+ self.literal)
            for c in p.subtrees:
                if c.literal == '+':
                    Assert(p.literal == u'@' and self.literal==u'@', u"'+' evaluation they are always left of (@)left of (@) isn't valid!")
        
    def strTemp(self):
        self.tempMade = True
        return u"t" + unicode(self.id)
    def addStateVars(self):
        if self.literal == MAPSTO:
            self.setFreeVarsAndExpr()
        elif self.literal == u'@':
            self.setFunAndArgs()
        #elif self.literal == u"/":
        #    self.setSlashArgs()
        for child in self.subtrees:
            child.addStateVars()
    def addStateVarsSecond(self):
        if self.isConsNode():
            self.setConsArgs()
        #if self.isSlashApplyNode():
        #    self.setSlashApplyArgs()
        for child in self.subtrees:
            child.addStateVarsSecond()
    def isConsNode(self):
        return self.literal == u'@' and hasattr(self,"funct") and self.funct.literal ==u'cons'
    
    '''def setSlashArgs(self):
        Assert(self.literal == u"/","Should be Slash node")
        retList = []
        for child in self.subtrees:
            if child.literal == u"/":
                child.setSlashArgs()
                retList.extend(child.slashargs)
            else:
                retList.append(child)
            #Assert(child.literal != u"/","/ compose with @")
        self.slashargs = retList
        #print "SLASH: ",len(retList),','.join([x.literal for x in retList])
    def isSlashApplyNode(self):
        return self.literal == u'@' and hasattr(self,"funct") and self.funct.literal ==u'/'
    '''
    def printUp(self):
        t=self
        ctr = 0
        while t.parent is not None:
            print '\t'.join('' for x in range(ctr)),t.parent.literal,t.parent.type.__str__()
            t=t.parent
            ctr = ctr+1
    '''def setSlashApplyArgs(self):
        Assert(self.isSlashApplyNode(),u"Must be a / apply node here")
        #take all largs of "/ apply" nodes and put them in slashargs
        retList = list(self.funct.slashargs)       
        for arg in self.largs:
            if arg.isSlashApplyNode():
                arg.setSlashApplyArgs()
                retList.extend(arg.slashargs)
            elif arg.literal == u"/":
                retList.append(arg.slashargs)
            else:
                retList.append(arg)
        self.slashargs = retList 
    '''
    def setSupersetRelationships(self,name,newparams):
        prg = bmProg[name]
        params = prg.params
        Assert(len(params) == len(newparams), u"Params and newparams aren't same!: ")
        for i in range(len(params)):
            if newparams[i] in superset:
                Assert(superset[newparams[i]] == params[i],"Can't have a different superset!")
            else:
                superset[newparams[i]] = params[i]    
    def setConsArgs(self):
        Assert(self.isConsNode(),"Must be a cons apply node here")
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
        Assert(self.literal == u'@' and hasattr(self,"funct"),"All set for this @ node")
        op = self.funct.literal
        if op in [PSI]:
            return arrayAccess(u"dist", self.largs)
        elif op in [u'w']:
            return funCall(op, self.largs)
            '''elif op == u'/':
                #Assert(hasattr(self,"slashargs"),u"slashargs missing: " + unicode(bmTerms.index(self)))
                cmds = []
                for x in self.subtrees:
                    x.setCode(False)
                    if x.literal != PSI:
                        cmds.append(x.code)
                return  u";".join(cmds) + u";\n"
            '''
        elif op == u'min':
            Assert(len(self.largs) == 1, "min is unary!")
            child = self.largs[0]
            if child.literal == MAPSTO:
                #minimize over a range denoted by free variables
                child.boundExpr.setCode(False)
                rs = u"\nTYPE " + self.strTemp() + u"= MAXVAL;\n"
                for v,r in child.fvranges:
                    Assert(v in VARS and v not in [PSI,THETA],u"Can't have PSI, THETA inside min")
                    Assert(r.literal != MAPSTO,u"this variable must be INT SET type")
                    rs += u"FOR("+v+u","+r.literal+u"_start,"+r.literal+u"_end){\n"
                rs += self.strTemp() + u" = min(" + self.strTemp() +u"," + child.boundExpr.code + u");\n"
                
                for v,r in child.fvranges:
                    rs+=u"}\n"
                     
                return rs 
            elif child.isConsNode():
                #minimize over a list in consargs
                Assert(len(child.consargs) == 2 ,"Min should be Binaryyyy")
                for x in child.consargs:
                    x.setCode(False)
                return u"min("+ u",".join(x.code for x in child.consargs) +u")"
            else:
                Assert(False,u"min should have only MAPSTO or cons as children: " + child.literal )
        elif op == u"cons":
            Assert(len(self.largs) == 2 ,"cons is always binary")
            #print len(self.consargs),self.consargs
            return u','.join([arg.string(False) for arg in self.consargs])
        elif op == u'+':
            Assert(len(self.largs) == 2 ,"+ is always binary")
            return opInfix(op,self.largs)
        elif self.funct.literal == MAPSTO and self.funct.subtrees[0].literal == PSI:
            Assert(len(self.largs) == 1,"MAPSTO with multiple freevars not expected")
            #thing on the "right" happens first from a procedural standpoint
            self.largs[0].setCode(False)
            self.funct.boundExpr.setCode(False)
            rs = self.largs[0].code
            if(rs != u"" and rs[-1] != u";"):
                rs +=u";"
            if rs != u"" and self.funct.boundExpr.code != u"":
                #print "boundE: ",self.funct.boundExpr.code
                rs+=u"\n" + self.funct.boundExpr.code
                if self.funct.boundExpr.code[-1] != u";":
                    rs+=u";"
            return rs
        else:
            for pname in bmProg:
                if self.funct.literal.startswith(pname):
                    #recursive call to the function
                    prg_name = filter(None,re.split('\[|,|\]',self.funct.literal))
                    name = prg_name[0]
                    Assert(name == pname,"function call name != pname")
                    newparams = prg_name[1:]
                    
                    #Make sure subset relationships are enforced
                    self.setSupersetRelationships(name,newparams)
                    return bmProg[name].getDecl(newparams,"") 
            Assert(False,"Can't be here")
            print self.funct.literal,self.largs[0].literal
            if self.funct.literal == MAPSTO:
                Assert(self.funct.subtrees[0].literal == PSI,"LOL")
                if self.largs[0].literal == u'/':
                    print u"SPL/: ",u','.join([x.literal for x in self.largs[0].slashargs])
                elif self.largs[0].literal == u'@':
                    print u"SPL@: ",self.largs[0].funct.literal,u'|',u','.join([x.literal for x in self.largs[0].largs])
                else:
                    Assert(False,"LOL1")
            #self.printUp()
            return funCall(self.funct.__str__(), self.largs)
        
    def setFunAndArgs(self):
        if hasattr(self, "funct"):
            return
        Assert(self.literal == u'@',"Can't get function when its not apply node")
        if self.subtrees[0].literal != u'@':
            retv = (self.subtrees[0],[self.subtrees[1]])
        else:
            self.subtrees[0].setFunAndArgs()
            funct = self.subtrees[0].funct
            largs = list(self.subtrees[0].largs)
            largs.append(self.subtrees[1])
            retv = (funct,largs)
        self.funct = retv[0]
        self.largs = retv[1]
    def setFreeVarsAndExpr(self):
        if hasattr(self, "fvranges"):
            return
        Assert(self.literal == MAPSTO,"Can't get free vars when its not apply node")
        Assert(self.subtrees[0].literal in VARS, u"LHS of MAPSTO must be a free var name: " + self.subtrees[0].literal)
        fv = (self.subtrees[0].literal,self.subtrees[0].type)
        if self.subtrees[1].literal != MAPSTO:
            retv = ([fv],self.subtrees[1])
        else:
            self.subtrees[1].setFreeVarsAndExpr()
            fvranges = list(self.subtrees[1].fvranges)
            boundExpr = self.subtrees[1].boundExpr
            fvranges.insert(0,fv)
            retv = (fvranges,boundExpr)
        self.fvranges = retv[0]
        self.boundExpr = retv[1] 
    def getFVRangeStr(self):
        Assert(self.literal == MAPSTO,"Must be MAPSTO node")
        rs = u""
        for v,r in self.fvranges:
            if v in VARS and v not in [PSI,THETA]:
                rs += u"[" + v + u" in " + r.__str__() + u"]"
        return rs
    def getCode(self):
        Assert(hasattr(self,"code"),"setCode must have been called by now")
        if self.tempMade:
            return self.strTemp()
        else:
            return self.code
    def getTempDefs(self,temps):
        if self.tempMade:
            temps[self.id] = self.preCode
        for x in self.subtrees:
            if x.literal != u'/': 
                x.getTempDefs(temps)
    def getTempDefsStr(self):
        temps = {}
        rs = u""
        self.getTempDefs(temps)
        for k in sorted(temps.keys()):
            rs+=temps[k] + u"\n"
        return rs
    '''def setSlashRelationships(self):
        global supersetX
        global supersetY
        Assert(self.literal == u"/","Slash needed")
        (X,Y) = self.type.arrType()
        (X1,Y1) = self.subtrees[0].type.arrType()
        (X2,Y2) = self.subtrees[1].type.arrType()
        addToSlash(X, X1,supersetX)
        addToSlash(X, X2,supersetX)
        addToSlash(Y, Y1,supersetY)
        addToSlash(Y, Y2,supersetY)
    '''
    
    def setCode(self,typed = True):
        
        if hasattr(self,"code"):
            return
        rootWithType = bmRoot.__str__(self) 
        if self.type is not None and typed:
            rootWithType += u"{" + self.type.__str__() + u"}"
        
        if self.literal == MAPSTO:
            if self.parent is not None and self.parent.literal == u'/':
                #This is array recomputation
                #print self.parent.id,self.parent.literal
                rs = u""
                lsargs =[]
                for v,r in self.fvranges:
                    if v in ["?"]:
                        continue
                    Assert(v in VARS and v not in [PSI],u"Can't have PSI, THETA inside min")
                    Assert(r.literal != MAPSTO,u"this variable must be INT SET type")
                    rs += u"FOR("+v+u","+r.literal+u"_start,"+r.literal+u"_end){\n"
                    lsargs.append(v)
                self.boundExpr.setCode(False)
                #add any temporary definitions
                rs += self.getTempDefsStr()
                rs += arrayAccessStr("dist", lsargs) + u" = " + self.boundExpr.code + u";\n"
                
                for v,r in self.fvranges:
                    rs+=u"}\n"
            else:
                rs = u""
                rs += self.getFVRangeStr()
                self.boundExpr.setCode(False)
                rs += self.getTempDefsStr()
                rs +=  self.boundExpr.code 
            self.code = rs
        elif self.literal == '@':
            self.code = self.getApplyCode()
        elif self.literal == '/':
            #print "SLASH: ",self.parent.parent.literal,self.parent.parent.type.__str__(),self.type.arrType(),self.subtrees[0].type.arrType(),self.subtrees[1].type.arrType()
            #self.setSlashRelationships()
            cmds = []
            for x in self.subtrees:
                x.setCode(False)
                if x.literal != PSI and x.code !=u"":
                    cmds.append(x.code)
            #print cmds
            if len(cmds) == 1:
                self.code = cmds[0]
            elif len(cmds) == 2:
                self.code == cmds[0] + u";" + cmds[1]
            else:
                self.code = u""
        elif len(self.subtrees) == 0:
            self.code = rootWithType
        elif len(self.subtrees) == 2:
            Assert(False,"Case not taken care of: " + self.getDebug())
            self.subtrees[0].setCode(False)
            self.subtrees[1].setCode(False)
            self.code = u"(" + self.subtrees[0].code + u" " + rootWithType + u" " + self.subtrees[1].code + u")"
        elif len(self.subtrees) == 1:
            self.subtrees[0].setCode(False)
            self.code = rootWithType + u" " + self.subtrees[0].code
        else:
            Assert(False,"subtrees can only be 0,1,2 sized!")

        if self.tempMade:
            self.preCode = self.code
            self.code = self.strTemp()
        
    def getDebug(self):
        if DEBUG:
            if self.parent and self.parent.literal == u'@':
                return  u','.join([unicode(self.id), self.literal,self.parent.literal,self.parent.funct.literal, unicode(len(self.parent.largs))])
        return ""
    def __str__(self,ctr =0,  typed = True):
        spacings = u''.join([SPACE for i in range(ctr)])
        rootstr = self.literal + u' | ' + self.type.__str__() + u' | '
        if len(self.subtrees) == 0:
            return spacings + rootstr + u'\n'
           
        retStr = spacings + u'{\n'
        retStr += spacings + SPACE
        if hasattr(self,'funct') and self.funct.literal != MAPSTO:
            retStr += self.funct.literal + u' | ' + self.funct.type.__str__() + u' | \n'
            if self.isConsNode():
                for i in self.consargs:
                    retStr += i.__str__(ctr=ctr+1,typed=typed)
            else:
                for i in self.largs:
                    retStr += i.__str__(ctr=ctr+1,typed=typed)
        elif hasattr(self,'fvranges') and self.literal == MAPSTO:
            #get fvranges, boundExpr, largs
            retStr += u"[|"
            for v,r in self.fvranges:
                retStr += v + u":" + r.__str__() + u"|" 
            retStr += u"]\n"
            retStr += self.boundExpr.__str__(ctr=ctr+1,typed=typed)
            #for i in self.largs:
            #    retStr += i.__str__(ctr=ctr+2,typed=typed)
        else:
            retStr += rootstr + u'\n'
            for i in self.subtrees:
                retStr += i.__str__(ctr=ctr+1,typed=typed)
        return retStr + spacings + u'}\n'
        
        
        
class bmProgram(object):
    '''
        name: program name for recursion
        params: named arguments to the program
        term: root bmTerm of the program
    '''
    def __init__(self,prg):
        #parse prg to get the components
        global bmProg
        Assert("program" in prg and "term" in prg, "program and/or term not available in prg ")
        prg_name = filter(None,re.split('\[|,|\]',prg["program"]))
        self.name = prg_name[0]
        bmProg[self.name] = self
        
        self.params = prg_name[1:]
        Assert(prg["term"]["root"]["literal"] == "program", "'program' literal not found in root of first term")
        Assert(len(prg["term"]["subtrees"]) == 1, "'program' should have one central root term")
        
        self.term = bmTerm(prg["term"]["subtrees"][0],None)
        self.term.addStateVars()
        self.term.addStateVarsSecond()
        
        self.impl = prg[u'style'] 
        if "text" in prg:
            self.text = prg["text"]
        else:
            self.text = ""
    def getDecl(self,newparams,intv,impl=None):
        if not impl:
            impl = self.impl
        return "func" + self.name + "_" + impl + "(" + ",".join([intv + x+"_start,"+intv+x+"_end" for x in newparams]) + ")"
    
    def getBaseCase(self):
        Assert(self.impl == u"rec",u"Should be recursive!")
        retStr = u"if (BASE_CONSTRAINT(" + ",".join([x+"_start,"+x+"_end" for x in self.params]) +u")){\n"
        retStr += self.getDecl(self.params,u"",impl=u"loop") + u";\n"
        retStr += u"return;\n"
        retStr += u"}"
        return retStr 
    def printCode(self):
        print "//DEFINITIONS and HEADERS"
        #print "#define FOR_FORWARD(i,s,e) for(int i=s;i<e;i++)"
        #print "#define FOR_BACKWARD(i,s,e) for(int i=e-1;i>=s;i--)"
        self.term.setCode(False)
        intv = INT + u" "
        print u"void " + self.getDecl(self.params,intv) + u"{"
        if self.impl == u"rec":
            print self.getBaseCase()
        print tempDefCode()
        print self.term.code
        print "}"
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
    
    
    for prg in prgs:
        print prg.text
        prg.printCode()
        
    #print superset
    #for prg in prgs:
    #    print prg.__str__()
    #printSlashes() 
      


if __name__ == "__main__": main()
