import codecs
import json
import argparse
import re
import os
from string import Template
from library import *
from bmType import bmRoot,bmType


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
        if trm[u'root'][u'literal'] == ":" and trm["subtrees"][0]["root"]["literal"] ==u"bazinga":
            Assert(len(trm["subtrees"][0]["subtrees"]) == 1,"Bazinga can have only one node")
            self.pardep = trm["subtrees"][0]["subtrees"][0]["root"]["literal"]
            #print (prg.name + "," + trm[u'root'][u'literal'] +"," + ( "1" if (trm["subtrees"][1]["root"]["literal"] == MAPSTO) else "0") +","+ unicode(self.pardep)).encode("utf-8")
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
            if i[u'root'][u'literal'] == GUARD:
                # guarded expression
                self.subtrees.append(bmTerm(i[u'subtrees'][0], self, prg))
                self.subtrees[len(self.subtrees) - 1].guards = bmTerm(i[u'subtrees'][1], self.subtrees[len(self.subtrees) - 1], prg)
                continue
            self.subtrees.append(bmTerm(i, self, prg))
        
        # Integer terms
        if self.literal == 0 or self.literal == 1:
            self.kind = "const"
            self.literal = str(self.literal)

        for p in self.subtrees:
            if (p.literal == QMARK):
                # print self.literal, u'\u21A6'
                Assert(self.literal == MAPSTO, u"'?' not to left of ->, " + self.literal)
            for c in p.subtrees:
                if c.literal == PLUS:
                    Assert(p.literal == u'@' and self.literal == u'@', u"PLUS evaluation they are always left of (@)left of (@) isn't valid!")
        
    def strTemp(self,ctx):
        self.tempMade = True
        if "use_tmp" in ctx:
            return ctx["use_tmp"]
        return u"t" + unicode(self.id)
    
    
    def isConsNode(self):
        return self.literal == u'@' and hasattr(self, "funct") and self.funct.literal == u'cons'
    
    def getGuards(self,fvranges,ctx):
        # get all guard expressions right on this node
        Assert(False, "obsolete function")
        if hasattr(self, "guards"):
            comps = []
            getComponents(self.guards, comps)
            #see if each component is necessary or reducndant by fvranges
            realComps = []
            #print "comps: ", [comp.__str__() for comp in comps]
            for g in comps:
                if len(g.subtrees)== 1 and isSet(g.literal):
                    var = g.subtrees[0].literal
                    range = filter(lambda (v,r): v==var and r.literal == g.literal,fvranges)
                    if len(range) == 0:
                        #necessary comp
                        realComps.append(g)
                else:
                    realComps.append(g)
            
            for g in realComps:
                if not hasattr(g, "code"):
                    g.setCode(ctx)
            return u" && ".join([g.code for g in realComps])
        else:
            return u""
    def getAllGuards(self,fvranges,ctx):
        # get all guard expressions in the subtree
        if hasattr(self, "guards"):
            return self.getGuards(fvranges,ctx)
        else:
            guardList = []
            for i in self.subtrees:
                gi = i.getAllGuards(fvranges,ctx)
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
    def getApplyCode(self,ctx):
        Assert(self.literal == u'@' and hasattr(self, "funct"), "All set for this @ node")
        
        op = self.funct.literal
        if hasattr(self,u"guards"):
            #Assert(self.guards.literal != LT,"Caught you: " + self.__str__() + str(ctx))
            Assert(op in [OMAX,MIN,MAX,PLUS],"Only OMAX, APPLY can have guards: " + op)
        if op in [PSI, THETA]:
            return arrayAccess(self.prg,u"dist", self.largs,ctx)
        elif op == MINUS:
            Assert(len(self.largs) == 2,u"MINUS is binary! ")
            for t in self.largs:
                t.setCode(ctx)
            return u"(" + self.largs[0].code + u"-" + self.largs[1].code + u")" 
        elif op in [u"w",u"w_prime",u"w'",u"S"]:
            return funCall(op, self.largs, ctx)
        elif op in [MIN,MAX]:
            Assert(len(self.largs) == 1, u"min is unary!")
            child = self.largs[0]
            
            if child.literal == MAPSTO:
                # minimize over a range denoted by free variables
                if (not keepTempInMin) and "minevar" in ctx and ctx["minevar"]:
                    tmpVar = ""
                else:
                    tmpVar = self.strTemp(ctx)
                oldCommonGuards = []
                if "common_guards" in ctx:
                    oldCommonGuards = ctx["common_guards"]
                loopEndPoints = self.processGuards(child.fvranges,child.boundExpr,ctx)
                rs = self.buildForLoop(child.fvranges, child.boundExpr, op, tmpVar,ctx,loopEndPoints)
                ctx["common_guards"] = oldCommonGuards
                #if hasattr(self,"pardep"):
                #    print "FORPAR-MINMAX: ", self.pardep
                return rs 
            elif child.isConsNode():
                if "common_guards" in ctx:
                    for g in ctx["common_guards"]:
                        if hasattr(child, "guardCompStrs") and g in child.guardCompStrs:
                            child.guardCompStrs.remove(g)
                            print "REMOVING GUARD: " + g
                # minimize over a list in consargs
                #Assert(not hasattr(self, "guards"),"no guards here for cons node!")
                Assert(len(child.consargs) in [2,3,4] , "Min should be Binary or Ternary or Quarternary")
                psiargs = filter(lambda x: x.literal == APPLY and x.funct.literal in [THETA,PSI],child.consargs)
                minargs = filter(lambda x: x.literal == APPLY and x.funct.literal ==op,child.consargs)
                if not psiargs or not minargs:
                    #usual min 
                    for c in child.consargs:
                        c.setCode(ctx)
                    return reduce(lambda a,b: op+"(" + a + "," + b + ")" if a != b else a,map(lambda x: x.code,child.consargs))        
                elif len(psiargs) == 1:
                    #find all sub-mins and set minEvar to true for them
                    for c in child.consargs:
                        if c not in psiargs and c not in minargs:
                            c.setCode(ctx)
                    for c in minargs:
                        ctx["minevar"] = True
                        c.setCode(ctx)
                        Assert(ctx["minevar"] == False,"Should be falsed by now")
                    argsExceptPsi = filter(lambda x: x.literal != APPLY or x.funct.literal not in [PSI,THETA],child.consargs)
                    argsCodeExceptPsi = map(lambda x: x.code, argsExceptPsi)
                    return reduce(lambda a,b: op+"(" + a + "," + b + ")" if a != b else a,argsCodeExceptPsi)
                else:
                    Assert(False,"can't have more than one psi in a min expression")
            else:
                Assert(False, u"min should have only MAPSTO or cons as children: " + child.literal)
        elif op == PLUS:
            Assert(len(self.largs) == 2 , "+ is always binary")
            return opInfix(op, self.largs, ctx)
        elif op == MAPSTO and self.funct.subtrees[0].literal == PSI:
            Assert(len(self.largs) == 1, "MAPSTO with multiple freevars not expected")
            # thing on the "right" happens first from a procedural standpoint
            self.largs[0].setCode(ctx)
            self.funct.boundExpr.setCode(ctx)
            rs = self.largs[0].code
            #print "L0str: ", rs
            rs=endStmt(rs)
            if rs != u"" and self.funct.boundExpr.code != u"":
                # print "boundE: ",self.funct.boundExpr.code
                rs += u"\n" + self.funct.boundExpr.code
                rs=endStmt(rs)
            return rs
        elif op == SLASH:
            Assert(len(self.largs) == 1, "largs must be size 1")
            self.funct.setCode(ctx)
            rs = self.funct.code
            if self.largs[0].literal != PSI:
                self.largs[0].setCode(ctx)
                rs = endStmt(rs)
                rs += self.largs[0].code
            return rs
        elif op == OMAX:
            #guard?expr:UNDEF
            Assert(len(self.largs) == 2,"Only two children allowed for max: " + self.__str__())
            self.largs[0].setCode(ctx)
            self.largs[1].setCode(ctx)
            exprCode = u"OMAX(" + self.largs[0].code + u"," + self.largs[1].code + u")"
            return exprCode
        elif hasattr(self.funct, u"code") and len(self.largs) == 1 and self.largs[0].literal == PSI:
            self.funct.setCode(ctx)
            return self.funct.code
        elif op == DELTA:
            Assert(len(self.largs) in [2,3],"must have two arguments")
            for x in self.largs:
                x.setCode(ctx)
            return u"DELTA(" + u",".join([x.code for x in self.largs]) + u")"     
        else:
            for arg in self.largs:
                print u"LARGi:",arg.__str__().encode('utf-8') 
            if hasattr(self,"guards"):
                print u"GUARD:",self.guards.__str__()
            Assert(False, u"Apply term not handled:  " + self.funct.__str__())

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
    def isMinMax(self):
        return self.literal == APPLY and self.funct.literal in [MIN,MAX]
        
    def getCommonGuards(self,comps):
        if "" not in comps:
            comps[""] = 0
        
        if self.literal == SLASH or self.isConsNode():
            iterateOver = self.subtrees
            if self.isConsNode():
                iterateOver = self.consargs
                #print "cons", len(iterateOver), [x.literal if x.literal != APPLY else x.funct.literal for x in iterateOver]
            
            for x in iterateOver:
                if (x.literal == APPLY and x.funct.literal in [PSI,THETA]) or (self.isConsNode() and x.literal in [PSI,THETA]):
                    continue
                elif x.literal == SLASH or x.isConsNode():
                    x.getCommonGuards(comps)
                else:
                    #print x.__str__()
                    comps[""] += 1
                    if hasattr(x, "guards"):
                        for g in x.guardCompStrs:
                            if g not in comps:
                                comps[g] =0
                            comps[g] += 1
                        
                    
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
    def initLoopEndPoints(self,vars,vtypes,loopEndPoints):
        for v in vars:
            if vtypes[v].literal != u"U" and isSet(vtypes[v].literal):
                loopEndPoints[v] = (defineBegin(vtypes[v].literal),defineEnd(vtypes[v].literal))
            elif vtypes[v].literal == u"U":
                s0 = vtypes[v].subtrees[0]
                s1 = vtypes[v].subtrees[1]
                loopEndPoints[v] = ((defineBegin(s0),defineEnd(s0)),(defineBegin(s1),defineEnd(s1)))
    def refineLoopGuards(self,vars,vtypes,loopEndPoints,vars_modif):    
        #initLoopEndPoints(vars,vtypes,loopEndPoints)
        if noLoopGuardOptim:
            return
        if hasattr(self, "guardCompStrs"):
            toRemove = []
            for g in self.guardCompStrs:
                if g[0:6] == "INSET(":
                    [exp,se] = g[6:-1].split(',')
                    exp = filter(lambda a: a!=')' and a != '(' and a != ' ',exp)
                    se = filter(lambda a: a!=')' and a != '(' and a != ' ',se)
                    if exp in vars and vtypes[exp].literal != u"U" and isSet(vtypes[exp].literal):
                        #see if this se set is a subset of range of this var
                        if isSubset(se,vtypes[exp].literal,self.prg.superset) :
                            #print exp, se, vtypes[exp].literal # refineLP
                            if loopEndPoints[exp][0] == defineBegin(vtypes[exp].literal) and loopEndPoints[exp][1] == defineEnd(vtypes[exp].literal):
                                loopEndPoints[exp] = (defineBegin(se),defineEnd(se))
                            else:
                                refineLP(loopEndPoints,exp,defineBegin(se),defineEnd(se))
                            toRemove.append(g) 
                    if exp.find(PLUS) > 0:
                        [x,c] = exp.split(PLUS)
                        Assert(c=="1","Only constant 1 supported for now: expression i+1 or j+1")
                        #print "guard->loop: ", x, vtypes[x].literal,exp, se, self.prg.superset
                        if x in vars and vtypes[x].literal != u"U" and isSet(vtypes[x].literal):
                            #x+1 \in se and (we know) x in sx
                            sx = vtypes[x].literal
                            if se != sx and sx != u"U" and isSet(sx):
                                refineLP(loopEndPoints,x,defineBegin(se)+u"-1",defineEnd(se)+u"-1")
                                toRemove.append(g)
                                '''
                                se_sup = self.prg.superset[se]
                                sx_sup = self.prg.superset[sx]
                                if (se_sup == sx_sup and sx < se):
                                    #x+1 \in se, x \in sx and se is after sx as an interval
                                    #x has to be end of sx
                                    loopEndPoints[x] = (loopEndPoints[x][1]+u"-1",None)
                                    toRemove.append(g) 
                                elif (se_sup == sx_sup and se < sx):
                                    #x+1 \in se, x \in sx and se is before sx as an interval
                                    #x has to be empty
                                    loopEndPoints[x] = (None,None)
                                    toRemove.append(g) 
                                if (sx_sup in self.prg.superset and self.prg.superset[sx_sup] == se_sup):
                                    # x : sx < sx_sup < J and x+1 : se < J 
                                    if se > sx_sup:
                                        #sx_sup = [ sx? | sx?] _ se
                                        if not isLeft(sx,sx_sup,self.prg.superset):
                                            loopEndPoints[x] = (loopEndPoints[x][1]+u"-1",None)
                                            
                                        else:
                                            loopEndPoints[x] = (None,None)
                                    else:
                                        #empty set
                                        loopEndPoints[x] = (None,None)
                                    toRemove.append(g)
                                '''
                            if se == sx:
                                #x+1 and x both are in sx so x ranges from [sx.begin,sx.end-1)
                                if loopEndPoints[x][1] == defineEnd(sx):
                                    loopEndPoints[x] = (loopEndPoints[x][0],defineEnd(sx)+u"-1")
                                else:
                                    refineLP(loopEndPoints,x,defineBegin(sx),defineEnd(sx)+u"-1")
                                toRemove.append(g)
                        #if not g in toRemove:
                        #    print "NOT RESOLVED."
                    if exp.find("-") > 0:
                        [x,c] = exp.split("-")
                        Assert(c=="1","Only constant 1 supported for now: expression i-1 or j-1")
                        #print "guard->loop: ", x, vtypes[x].literal,exp, se, self.prg.superset
                        if x in vars and vtypes[x].literal != u"U" and isSet(vtypes[x].literal):
                            sx = vtypes[x].literal 
                            #x-1 in se and x in sx
                            if se != sx and sx != u"U" and isSet(sx):
                                refineLP(loopEndPoints,x,defineBegin(sx)+u"+1",defineEnd(sx))
                                toRemove.append(g)
                                '''
                                se_sup = self.prg.superset[se]
                                sx_sup = self.prg.superset[sx]
                                if (se_sup == sx_sup and se < sx):
                                    #x-1 \in se, x \in sx and se is before sx as an interval
                                    #x has to be start of se
                                    loopEndPoints[x] = (loopEndPoints[x][0],None)
                                    toRemove.append(g) 
                                elif (se_sup == sx_sup and se > sx):
                                    #x-1 \in se, x \in sx and se is after sx as an interval
                                    #x has to be empty
                                    loopEndPoints[x] = (None,None)
                                    toRemove.append(g) 
                                if (sx_sup in self.prg.superset and self.prg.superset[sx_sup] == se_sup):
                                    # x : sx < sx_sup < J and x-1 : se < J 
                                    if se < sx_sup:
                                        #se _ sx_sup = [ sx? | sx?] 
                                        #print "sx,sx_sup: ",sx,sx_sup,self.prg.superset, isLeft(sx,sx_sup,self.prg.superset)
                                        if isLeft(sx,sx_sup,self.prg.superset):
                                            loopEndPoints[x] = (loopEndPoints[x][0],None)
                                        else:
                                            loopEndPoints[x] = (None,None)
                                    else:
                                        #empty set
                                        loopEndPoints[x] = (None,None)
                                    toRemove.append(g)
                                '''
                            if se == sx:
                                #x-1 and x both are in sx so x ranges from [sx.begin+1,sx.end)
                                if loopEndPoints[x][0] == defineBegin(sx):
                                    loopEndPoints[x] = (defineBegin(sx)+u"+1",loopEndPoints[x][1])
                                else:
                                    refineLP(loopEndPoints,x,defineBegin(sx)+u"+1",defineEnd(sx))
                                toRemove.append(g)
                        if not g in toRemove:
                            print "NOT RESOLVED."
                if g.find(LT) > 0:
                    pos = g.find(LT)
                    x=g[:pos]
                    y=g[pos+1:]
                    #print "GUARD ANALYSIS: ",self.prg.name, self.prg.impl, x,"<",y, vars
                    if "+" in x and y in vars:
                        posplus = x.find("+")
                        j=x[:posplus]
                        c=x[posplus+1:]
                        Assert(c=="1","Only 1 supported for x: j+1")
                        #j+1 < y
                        
                        if j in vars:
                            sj = vtypes[j].literal
                            sy = vtypes[y].literal
                            jLoopsBeforey = vars.index(j) < vars.index(y) 
                            print "//FOUND var + 1 LT var : ",j,sj,y,sy,jLoopsBeforey, areDisjoint(sj,sy,self.prg.superset)
                            if sj==sy and sj != u"U" and jLoopsBeforey:
                                #change y appropriately to j+2
                                if loopEndPoints[y][0] == defineBegin(sy):
                                    loopEndPoints[y] = (j+ "+2",loopEndPoints[y][1])
                                else:
                                    refineLP(loopEndPoints,y,j+ "+2",loopEndPoints[y][1])
                                toRemove.append(g)
                            if sj != sy and areDisjoint(sj,sy,self.prg.superset) == "y<x" :
                                loopEndPoints[y] = (None,None)
                                toRemove.append(g)
                            if sj != sy and areDisjoint(sj,sy,self.prg.superset) == "x<y" :
                                refineLP(loopEndPoints,y,j+ "+2",loopEndPoints[y][1])
                                toRemove.append(g)
                            #if sj != sy and areDisjoint(sj,sy,self.prg.superset) == "x<y" and xLoopsBeforey:
                                
                    if x in vars and y in vars :
                        sx = vtypes[x].literal
                        sy = vtypes[y].literal
                        xLoopsBeforey = vars.index(x) < vars.index(y)
                        #print "GUARD ANALYSIS: ", x,"<",y, vars,sx,sy
                        if getProblem() == "Paren":
                            if sy == u"U" and sx != u"U" and isSet(sx):
                                sy0 = vtypes[y].subtrees[0]
                                sy1 = vtypes[y].subtrees[1]
                                ly = loopEndPoints[y]
                                if sy0 == sx and xLoopsBeforey:
                                    #first y-loop can start from x+1
                                    loopEndPoints[y] =((x+u"+1",ly[0][1]),ly[1])
                                    toRemove.append(g) 
                                if sy1 == sx and xLoopsBeforey:
                                    #second y-loop can start from x+1
                                    loopEndPoints[y] =(ly[0],(x+u"+1",ly[1][1]))
                                    toRemove.append(g) 
                            if sx == u"U" and sy != u"U" and isSet(sy):
                                sx0 = vtypes[x].subtrees[0]
                                sx1 = vtypes[x].subtrees[1]
                                lx = loopEndPoints[x]
                                if sx0 == sy and not xLoopsBeforey:
                                    #first x-loop can end at y
                                    loopEndPoints[x] =((lx[0][0],y),lx[1])
                                    toRemove.append(g) 
                                if sx1 == sy and not xLoopsBeforey:
                                    #second x-loop can end at y
                                    loopEndPoints[x] =(lx[0],(lx[1][0],y))
                                    toRemove.append(g) 
                                
                        if sx == sy and xLoopsBeforey: 
                            #you can run y-loop from x+1 to end
                            if loopEndPoints[y][0] == defineBegin(sy):
                                loopEndPoints[y] = (x+ u"+1",loopEndPoints[y][1])
                            else:
                                refineLP(loopEndPoints,y,x+ u"+1",loopEndPoints[y][1])
                            toRemove.append(g) 
                        if sx == sy and not xLoopsBeforey: 
                            #you can run x-loop from begin to y
                            #Assert(False,"not supported x<y with y looping before x")
                            if loopEndPoints[x][1] == defineEnd(sx):
                                loopEndPoints[x] = (loopEndPoints[x][0],y)
                            else:
                                refineLP(loopEndPoints,x,loopEndPoints[x][0],y)
                            toRemove.append(g) 
                        if sx != sy and areDisjoint(sx,sy,self.prg.superset) == "x<y":
                            toRemove.append(g) #trivially satisfied!
                        if sx != sy and areDisjoint(sx,sy,self.prg.superset) == "y<x":
                            loopEndPoints[x] = (None,None)
                            loopEndPoints[y] = (None,None)
                            toRemove.append(g) #Useless loop!
                    if g not in toRemove:
                        import pdb
                        pdb.set_trace()
            #print "EP:",loopEndPoints
            for g in toRemove:
                self.guardCompStrs.remove(g)
    def processGuards(self,fvranges,boundExpr,ctx):
        # constraining the loopVar using both loopType and guardExpr
        #Use guardComponents and freeVariables to find best bounds and guards
        #(0) Bring guards up in this special Min -> Min case:
        if boundExpr.isMinMax() and len(boundExpr.largs) == 1 and boundExpr.largs[0].isConsNode() and len(boundExpr.largs[0].consargs) == 2 and boundExpr.largs[0].consargs[0].literal == APPLY and boundExpr.largs[0].consargs[0].funct.literal in [PSI,THETA] and boundExpr.largs[0].consargs[1].isMinMax():
            #move guards from boundExpr.largs[0].consargs[1] to boundExpr if they don't involve the inner literal
            innerLoop = boundExpr.largs[0].consargs[1]
            if len(innerLoop.largs) == 1 and innerLoop.largs[0].literal == MAPSTO and len(innerLoop.largs[0].fvranges) ==1:  
                innerLit = innerLoop.largs[0].fvranges[0][0]
                innerBE = innerLoop.largs[0].boundExpr
                for g in innerBE.guardCompStrs:
                    if innerLit not in g:
                        #move this g up and remove from here
                        Assert(hasattr(boundExpr,"guardCompStrs"),"Must have existing guards?")
                        boundExpr.addToGuardCompStrs(g)
                        innerBE.guardCompStrs.remove(g)
                
        #(1) eliminate guards implied by fvranges and ctx["fvranges"]
        if "elim_guards" not in ctx:
            ctx["elim_guards"] =[]
        fvrUp = filter(lambda (v, r): v not in [THETA, QMARK], fvranges)
        vars_modif = map(lambda (v,r): v,fvrUp)
        vtypes = {}
        fvrAnalysis = list(filter(lambda (v, r): v not in [THETA, QMARK, PSI], ctx['fvr']))
        fvrAnalysis.extend(filter(lambda (v,r): (v,r) not in fvrAnalysis ,fvrUp))
        for (v,r) in fvrAnalysis:
            vtypes[v] = r
        vars = map(lambda (v,r): v,fvrAnalysis)
        for (v,r) in fvrUp:
            if isSet(r.literal):
                inSetvr = defineInSet(v,r.literal)
                Assert(inSetvr not in ctx["elim_guards"], "can't have this INSET already in elim_guards")
                ctx["elim_guards"].append(inSetvr)
        
        #(2) take common guards of all SLASH expressions and pull it up to loop, Generalized for MIN expressions too
        compDict = {}
        commomcomps = []
        if boundExpr.isMinMax():
            Assert(len(boundExpr.largs) == 1, "minsubtree should be unary: " + boundExpr.__str__()) 
            if boundExpr.largs[0].isConsNode():
                boundExpr.largs[0].getCommonGuards(compDict)
            #print "MINcomps: ",compDict, boundExpr.largs[0].__str__().encode('utf-8')
        else:
            boundExpr.getCommonGuards(compDict)
        
        #print "compDict: ",compDict
        if "" in compDict and compDict[""] > 0:
            for g in compDict:
                if g != "":
                    if compDict[g] == compDict[""] and g not in commomcomps:
                        commomcomps.append(g)
        for g in commomcomps:
            boundExpr.addToGuardCompStrs(g)
        
        ctx["common_guards"] = commomcomps
        loopEndPoints = {}
        
        
        boundExpr.initLoopEndPoints(vars,vtypes,loopEndPoints)
        if LPDEBUG and hasattr(boundExpr,"guardCompStrs"):
            print "BEFORE LP:",vars_modif,filter(lambda g: "elim_guards" not in ctx or (g not in ctx["elim_guards"]),boundExpr.guardCompStrs),[v+" in ("+ unicode(loopEndPoints[v][0]) + "," + unicode(loopEndPoints[v][1]) + ")"  for v in vars]
        boundExpr.refineLoopGuards(vars,vtypes,loopEndPoints,vars_modif)
        if  LPDEBUG and  hasattr(boundExpr,"guardCompStrs"):
            print "AFTER LP:",vars_modif,filter(lambda g: "elim_guards" not in ctx or (g not in ctx["elim_guards"]),boundExpr.guardCompStrs),[v+" in ("+ unicode(loopEndPoints[v][0]) + "," + unicode(loopEndPoints[v][1]) + ")"  for v in vars]
        return loopEndPoints
        
    def buildForLoop(self, fvranges, boundExpr, mode, tmpVar,ctx, loopEndPoints):
        # compute the tmpVar using evalExpr in a loop
        
        minEvar = mode in [MIN,MAX] and "minevar" in ctx and ctx["minevar"]
        if minEvar:
            ctx["minevar"] = False
        
        fvrUp = filter(lambda (v, r): v not in [THETA, QMARK], fvranges)
        vars_modif = map(lambda (v,r): v,fvrUp)
        vtypes = {}
        fvrAnalysis = list(filter(lambda (v, r): v not in [THETA, QMARK, PSI], ctx['fvr']))
        fvrAnalysis.extend(filter(lambda (v,r): (v,r) not in fvrAnalysis ,fvrUp))
        for (v,r) in fvrAnalysis:
            vtypes[v] = r
        vars = map(lambda (v,r): v,fvrAnalysis)
        
        
        #print "loopEndPoints: ", loopEndPoints
        rs = u""
        lsargs = []
        ctx["noguards"] = True
        guardedNode = None
        tVar = None
        guardLocal = None
        if boundExpr.isMinMax() and boundExpr.largs[0].isConsNode() and len(boundExpr.largs[0].consargs) >= 2:
            guardedNodeList = (filter(lambda c: hasattr(c,"guardCompStrs"),boundExpr.largs[0].consargs))
            #print "GNL: ",guardedNodeList
            if len(guardedNodeList) == 1:
                guardedNode = guardedNodeList[0]
                if "common_guards" in ctx:
                    for g in ctx["common_guards"]:
                        if g in guardedNode.guardCompStrs:
                            guardedNode.guardCompStrs.remove(g)
                if len(guardedNode.guardCompStrs) == 0:
                    guardedNode = None
                else:
                    guardLocal = guardedNode.getGuardExpr()
                    guardedNode.guardCompStrs = []
                    #single guarded node!
                    tVar = guardedNode.strTemp(ctx)
                    ctx["use_tmp"] = tVar
                #print "GN:",guardedNode.guardCompStrs, tmpVar
        boundExpr.setCode(ctx)
        '''
        if ("loop_bounds" not in ctx) or (len(ctx["loop_bounds"]) == 0) :
            ctx["loop_bounds"] = {}
            for v in loopEndPoints:
                if v not in vars_modif:
                    ctx["loop_bounds"][v] = loopEndPoints[v]
        else:
            for v in vars_modif:
                toRemove = []
                if v in ctx["loop_bounds"]:
                    if boundExpr.isMinMax() and len(boundExpr.largs) == 1 and boundExpr.largs[0].isConsNode() and len(boundExpr.largs[0].consargs) == 2 and boundExpr.largs[0].consargs[0].literal == APPLY and boundExpr.largs[0].consargs[0].funct.literal in [PSI,THETA] and boundExpr.largs[0].consargs[1].isMinMax():
                        mainlow = defineBegin(vtypes[v].literal)
                        mainhigh = defineEnd(vtypes[v].literal)   
                        newlow = ctx["loop_bounds"][v][0]
                        newhigh = ctx["loop_bounds"][v][1]                        
                        Assert(newlow == mainlow and newhigh ==mainhigh,"Don't need to process this because the relevant guards were lifted up")
                        toRemove.append(v)
                    else:
                        Assert(False,"remove guards(!) on this literal: " + v)
                    
                for v in toRemove:
                    del ctx["loop_bounds"][v]
        '''
        if guardedNode and tVar and guardLocal:
            loclsargs = [v for (v,r) in filter(lambda (v, r): v not in [THETA, QMARK, PSI], ctx['fvr'])]
            initVar = arrayAccessStr(self.prg,u"dist", loclsargs)
            guardedNode.preCode = u"TYPE " + tVar + " = " + initVar + ";\nif("+guardLocal+"){\n" + tVar + " = "+mode+"(" + tVar + "," + guardedNode.preCode +");\n}\n"
            del ctx["use_tmp"]
        
        
        for (v,r) in fvrUp:
            if isSet(r.literal):
                ctx["elim_guards"].remove(defineInSet(v,r.literal))
        
        inlineUnion = len(fvrUp) == 1 and fvrUp[0][1].literal == u"U" and isSet(fvrUp[0][1].subtrees[0]) and isSet(fvrUp[0][1].subtrees[1]) and mode in [MIN,MAX]
        Assert("noguards" not in ctx, "must have been deleted")
        #guardExpr = boundExpr.getGuards(fvranges,ctx)
        guardExpr = u""
        if hasattr(boundExpr, "guardCompStrs"):
            guardExpr = boundExpr.getGuardExpr()
        
        if mode == MIN and not minEvar:
            rs += u"\nTYPE " + tmpVar + u"= MAXVAL;\n"
        elif mode == MAX and not minEvar:
            rs += u"\nTYPE " + tmpVar + u"= MINVAL;\n"
        elif mode in [MIN,MAX] and minEvar and keepTempInMin and not "use_tmp" in ctx:
            ls = [v for (v,r) in filter(lambda (v, r): v not in [THETA, QMARK, PSI], ctx['fvr'])]
            rs += u"\nTYPE " + tmpVar + u"= "+arrayAccessStr(self.prg,u"dist", ls)+";\n"
        forDiag = False
        if inlineUnion:
            v = fvrUp[0][0]
            loopBounds1 = loopEndPoints[v][0][0] + u"," + loopEndPoints[v][0][1]
            loopBounds2 = loopEndPoints[v][1][0] + u"," + loopEndPoints[v][1][1]
            rs += self.prg.forPre() + u"(" + v + u"," + loopBounds1 + u"){\n"
            
            if guardExpr != u"":
                rs += u"if (" + guardExpr + u"){\n"
            rs += tmpVar + u" = "+mode+"(" + tmpVar + u"," + boundExpr.code + u");\n"
            if guardExpr != u"":
                rs += u"}\n"
            rs +=u"\n}\n"
            
            rs += self.prg.forPre() + u"(" + v + u"," + loopBounds2 + u"){\n"
            
            if guardExpr != u"":
                rs += u"if (" + guardExpr + u"){\n"
            rs += tmpVar + u" = "+mode+"(" + tmpVar + u"," + boundExpr.code + u");\n"
            if guardExpr != u"":
                rs += u"}\n"
            rs +=u"\n}\n"
            return rs
            
        ignoreLoop = {}
        for v, r in fvrUp:
            letStmt = False
            ignoreLoop[v] = False
            Assert(v in VARS and v not in [PSI, THETA], u"Can't have PSI/THETA inside MAPSTO")
            Assert(r.literal != MAPSTO, u"this variable must be INT SET/UNION type")
            Assert(isSet(r.literal) or r.literal == u'U', u"No other loopVarTypes supported: " + r.__str__())
            if v in loopEndPoints and r.literal != u"U":
                if loopEndPoints[v][0] is None and loopEndPoints[v][1] is None:
                    ignoreLoop[v] = True
                elif loopEndPoints[v][1] is None:
                    letStmt = True
                    loopBounds = loopEndPoints[v][0]
                else:
                    loopBounds = loopEndPoints[v][0] + u"," + loopEndPoints[v][1]
            elif v in loopEndPoints and r.literal == u"U":
                loopBounds = loopEndPoints[v][0][0] + u"," + loopEndPoints[v][0][1]+u","+loopEndPoints[v][1][0] + u"," + loopEndPoints[v][1][1]
            else:
                loopBounds = r.getSetEnds()
            if r.literal == u"U":
                rs += u"FORUNION(" + v + u"," + loopBounds + u",\n"
            elif ignoreLoop[v]:
                return u"NOP;" #loop doesn't do anything
                rs += u"IGNORE("
            elif letStmt:
                rs += u"{\nLET(" + v + u"," + loopBounds + u");\n"
            else:
                rs += self.prg.forPre() + u"(" + v + u"," + loopBounds + u"){\n"
            lsargs.append(v)
        
        
        if guardExpr != u"":
            rs += u"if (" + guardExpr + u"){\n"
        
        # add any temporary definitions
        if mode not in  [MIN,MAX]:
            tdfs = self.getTempDefsStr()
            # Assert(tdfs = u"",u"Temp def shouldn be empty: " + tdfs)
            rs += tdfs
        
        
        if "fix" in ctx and ctx["fix"] and "slashes" in ctx:
            eVar = u""
            del ctx["slashes"]
        elif minEvar and not keepTempInMin:
            lsargs = [v for (v,r) in filter(lambda (v, r): v not in [THETA, QMARK, PSI], ctx['fvr'])]
            tmpVar = arrayAccessStr(self.prg,u"dist", lsargs)
        elif boundExpr.isMinMax() and "minevar" in ctx:
            if keepTempInMin:
                eVar = arrayAccessStr(self.prg,u"dist", lsargs) + u" = "
            else:
                eVar = ""
        else:
            eVar = arrayAccessStr(self.prg,u"dist", lsargs) + u" = "
            
        if mode in [MIN,MAX]:
            rs += tmpVar + u" = "+mode+"(" + tmpVar + u"," + boundExpr.code + u")"
        elif (mode == FIX or mode == SLASH):
            if eVar != u"":
                rs += eVar  + boundExpr.code
        else:
            Assert(False, u"mode not defined: " + mode)
        rs=endStmt(rs) + u"\n"
        if guardExpr != u"":
            rs += u"}\n"
       
        if forDiag:
            rs += u")\n"
        else:
            for v, r in fvrUp:
                if v in [QMARK, THETA]:
                    continue
                if ignoreLoop[v]:
                    rs += u")\n"
                elif r.literal == u"U":
                    rs += u")\n"
                else:
                    rs += u"}\n"
        
        return rs
    def addToGuardCompStrs(self,s):
        if hasattr(self, "guardCompStrs"):
            self.guardCompStrs.append(s)
        elif not hasattr(self, "guards") and not hasattr(self, "guardCompStrs"):
            self.guardCompStrs = [s]
        else:
            Assert(False, "can't have guards but not guardCompStrs: " + self.__str__())
    def getGuardExpr(self):
        Assert(hasattr(self, "guardCompStrs"), "Must have guardCompStrs")
        return u" && ".join(self.guardCompStrs)
    
                
    def setCode(self, ctx):
        if hasattr(self, "code"):
            if isRecCall(self.literal) and "curpardep" in ctx:
                Assert(ctx["curpardep"] != -1, "Can't have two recursive calls under same bazinga!")
                self.code = addParLims(self.code,ctx["curpardep"]) 
                ctx["curpardep"] = -1
            return
        if hasattr(self,"pardep"):
            Assert("curpardep" not in ctx, "Can't have a bazinga inside a parent bazinga!")
            ctx["curpardep"] = self.pardep
            #print (u"PAR: " + unicode(self.pardep) + u" " + self.literal + u" " +self.parent.literal).encode("utf-8")
        if hasattr(self,u"guards"):
            Assert(hasattr(self.guards, "code"),"guards should have code already")
            Assert(hasattr(self, "guardCompStrs"),"guardCompStrs should have initialized already")
            if "elim_guards" in ctx:
                for eg in ctx["elim_guards"]:
                    if eg in self.guardCompStrs:
                        self.guardCompStrs.remove(eg)
            self.guards.setCode(ctx)
            
        guardsAllowed = "noguards" not in ctx
        if not guardsAllowed:
            del ctx["noguards"]
        fvsSeen =  ("fvr" in ctx) and len(filter(lambda (v,r): isSet(r.literal) or r.literal==u"U",ctx["fvr"])) >= 2
        
        
        rootWithType = bmRoot.__str__(self) 
        if self.literal == MAPSTO:
            if "fvr" not in ctx:
                ctx["fvr"] = []
            for (v,r) in self.fvranges:
                if (v,r) not in ctx["fvr"]:
                    ctx["fvr"].append((v,r))
            if self.parent is not None and self.parent.literal in [SLASH, FIX]:
                # This is array recomputation
                #if "curpardep" in ctx:
                #    print "FORPAR-/FIX: ", ctx["curpardep"]
                oldCommonGuards = []
                if "common_guards" in ctx:
                    oldCommonGuards = ctx["common_guards"]
                loopEndPoints = self.processGuards(self.fvranges,self.boundExpr,ctx)
                rs = self.buildForLoop(self.fvranges, self.boundExpr, self.parent.literal,"",ctx,loopEndPoints)
                if self.prg.impl == "rec" and (hasattr(self,"pardep") or (len(self.subtrees) == 2 and hasattr(self.subtrees[1],"pardep"))):
                    fvSets = set()
                    getAllFVsets(rs,fvSets)
                    rs = self.prg.addFunction(fvSets,rs)
                    
                ctx["common_guards"] = oldCommonGuards
                if len(self.subtrees) == 2 and hasattr(self.subtrees[1],"pardep"):
                    pdep = self.subtrees[1].pardep
                    rs = addParLims(rs,pdep)
                if hasattr(self,"pardep"):
                    pdep = self.pardep
                    rs = addParLims(rs,pdep)
            elif self.subtrees[0].literal == PSI:
                self.subtrees[1].setCode(ctx)
                rs = self.subtrees[1].code
            else:
                # print self.parent.__str__()
                print self.__str__()
                Assert(False, "Why here?")
                
                rs = u""
                rs += self.getFVRangeStr()
                self.boundExpr.setCode(ctx)
                rs += self.getTempDefsStr()
                rs += self.boundExpr.code 
            for (v,r) in self.fvranges:
                Assert ((v,r)  in ctx["fvr"],u" not found in ctx: " + v + u"," + r.__str__())
                ctx["fvr"].remove((v,r))
            self.code = rs
        elif self.literal == APPLY:
            
            self.code = self.getApplyCode(ctx)
            if hasattr(self,u"guards") and guardsAllowed and self.getGuardExpr() != u"":
                if self.parent is not None and self.parent.literal == SLASH and "evar" in ctx and ctx["evar"] != u"":
                    self.code = u"if(" + self.getGuardExpr() + u"){\n" + ctx["evar"] + u"=" + self.code +u";}\n"
                else:
                    self.code = u"((" + self.getGuardExpr() + u")?(" + self.code +u"):UNDEF)"
            
        elif self.literal == FIX:
            # TODO: Get "read set": {J0xJ0, J0xJ1, J1xJ1}
            Assert(len(self.subtrees) == 1, "fix should be unary")
            # x = self.getGuards()
            ctx["fix"] = True
            self.subtrees[0].setCode(ctx)
            ctx["fix"] =False
            self.code = self.subtrees[0].code
            # print self.type.readset, x, self.__str__()
            # Assert(False,u"fix not implemented yet")
        elif self.literal in [LT, u'>', u'==', u'!=', AND, u'|']:
            # binary infix operators
            Assert(len(self.subtrees) == 2, "binary infix operators")
            op = self.literal
            if op == AND: 
                op = u' && '
            self.code = opInfix(op, self.subtrees, ctx)
        elif isSet(self.literal):
             # guard computation
             Assert(len(self.subtrees) == 1, "IN SET guard: " + self.__str__())
             self.subtrees[0].setCode(ctx)
             self.code = defineInSet(self.subtrees[0].code,self.literal)
        elif self.literal == GUARD:
            # guarded expression
            # subtrees[1] is the condition
            # Assert(False,"False")
            Assert(len(self.subtrees) == 2, "guarded expression should have 2 children")
            # print self.__str__()
            retStr = u""
            guarding = (not hasattr(self.subtrees[1], "code"))
            if guarding:
                self.subtrees[1].setCode(ctx)
                retStr = u"if(" + self.subtrees[1].code + u"){\n"
            self.subtrees[0].setCode(ctx)
            retStr += self.subtrees[0].code 
            if guarding:
                retStr += u"\n}\n"
            self.code = retStr
        elif self.literal == SLASH and fvsSeen:
            rootSlash = (("slash" not in ctx) or not ctx["slash"]) 
            if rootSlash:
                #First slash seen from the top that is inside when 
                #i,j are present as free variables
                ctx["slash"] = True
                fvrs = filter(lambda (v,r): isSet(r.literal) or r.literal==u"U",ctx["fvr"]) 
                fvstrs = [v for (v,r) in fvrs]
                #remove "slash" the moment you get into the SLASH
                ctx["evar"] = arrayAccessStr(self.prg,"dist", fvstrs)
                ctx["slashes"] = []
            
            for x in self.subtrees:                
                if x.literal != SLASH:
                    if "common_guards" in ctx:
                        for g in ctx["common_guards"]:
                            if hasattr(x, "guards") and g in x.guardCompStrs:
                                x.guardCompStrs.remove(g)
                                #print "REMOVING GUARD: " + g
                x.setCode(ctx)
                if x.literal != SLASH:
                    if rootSlash and x.code == ctx["evar"]:
                        #irrelevant slash, turn into Guard
                        Assert(x == self.subtrees[0],"Must be first child of the SLASH")
                        self.addToGuardCompStrs(u"IS_UNDEF("+ctx["evar"]+u")")
                        continue       
                    else:                           
                        ctx["slashes"].append(x)
                #else this is a lower level "/" inside i -> j ->
            if not rootSlash:
                self.code = u"NONE"
            else:
                #compose all the Slash codes
                self.code = u""
                #Assert(len(ctx["slashes"]) == 2, "Only two slash divisions supported based on guards for now")
                for x in ctx["slashes"]:
                    self.code += x.code
                    self.code = endStmt(self.code)
                #self.code += ctx["evar"] +  u" = " + reduce(lambda a,b: u"GETDEF("+a+u","+b+u")",[x.code for x in ctx["slashes"]]) + u""
                ctx["slashes"] = []
                del ctx["evar"]
                del ctx["slash"]
        elif self.literal == SLASH and not fvsSeen:
            cmds = []
            for x in self.subtrees:                
                x.setCode(ctx)
                if x.literal == PSI or (x.literal == MAPSTO and x.subtrees[0].literal == QMARK and x.subtrees[1].literal == PSI):
                    continue;
                elif x.literal == SLASH or (x.literal != PSI and x.code != u""):
                    cmds.append(x.code)
                else:
                    Assert(False, "Not accessible: " + x.literal)
            # print cmds
            cmds = filter(lambda x: x != "",cmds)
            if len(cmds) == 1:
                self.code = cmds[0]
            elif len(cmds) ==2:
                self.code = endStmt(cmds[0]) + cmds[1]
            else:
                self.code = u""
        elif len(self.subtrees) == 1 and self.literal == NEG:
            self.subtrees[0].setCode(ctx)
            self.code =  u"(!"+self.subtrees[0].code+u")"
        elif len(self.subtrees) == 0:
            Assert(self.literal in VARS or (self.literal).isdigit(), "should be a variable or number! : " + self.__str__())
            self.code = rootWithType
        elif len(self.subtrees) == 2:
            Assert(False, "Case not taken care of: " + self.getDebug())
            self.subtrees[0].setCode(ctx)
            self.subtrees[1].setCode(ctx)
            self.code = u"(" + self.subtrees[0].code + u" " + rootWithType + u" " + self.subtrees[1].code + u")"
        elif len(self.subtrees) == 1:
            Assert(False, "Case not taken care of: " + self.getDebug())
            self.subtrees[0].setCode(ctx)
            self.code = rootWithType + u" " + self.subtrees[0].code
        else:
            Assert(False, "subtrees can only be 0,1,2 sized!")

        if self.tempMade:
            self.preCode = self.code
            self.code = self.strTemp(ctx)
        
        if self.parent is not None and hasattr(self.parent, "guards") and  self.parent.guards == self:
            comps = []
            getComponents(self, comps)
            self.parent.guardCompStrs = [g.code for g in comps]
        
        if hasattr(self,"pardep"):
            Assert("curpardep" in ctx, "Can't have been removed by another bazinga!")
            del ctx["curpardep"]
            #self.code = u"YYXX[" + unicode(self.pardep) + u"]{" +self.code + u"}\n" 
        if hasattr(self,"guards"):
            self.code = self.code + "/* " + self.guards.code + " */"
            
        
    def isPlus(self):
        return self.literal == APPLY and self.funct.literal == PLUS
        
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
        if hasattr(self, 'funct') and self.funct.literal != MAPSTO and self.funct.literal != SLASH:
            if len(self.funct.subtrees)!=0:
                print self.funct.literal, len(self.funct.subtrees)
                Assert(False,"funct should not have children")
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
        if hasattr(self,"pardep"):
            retStr = "PAR[" + unicode(self.pardep) + "]{" + retStr + "}"
        return retStr + spacings + u'}\n'
        
       