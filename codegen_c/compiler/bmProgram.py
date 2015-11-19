import codecs
import json
import argparse
import re
import os
from string import Template
from library import *
from bmType import bmRoot,bmType
from bmTerm import bmTerm

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
        self.recCallMap = {}
        self.computeSupersets(self.term)
        if DEBUG:
            print self.name, self.impl, "superset: ", self.superset
        self.addStateVarsSecond(self.term)
        self.newFuncs = []
        
            
    def preDist(self):
        if self.impl == "loop":
            return self.name + "L"
        else:
            return ""
            
    def addStateVars(self, trm):
        if trm.literal == MAPSTO:
            trm.setFreeVarsAndExpr()
        elif trm.literal == u'@':
            trm.setFunAndArgs()
            Assert(hasattr(trm, "funct"), "No funct!")
        for child in trm.subtrees:
            self.addStateVars(child)
        if hasattr(trm, "guards"):
            self.addStateVars(trm.guards)
    
    def addStateVarsSecond(self, trm):
        if trm.isConsNode():
            trm.setConsArgs()
        elif trm.literal == u'fix':
            readSet = getReadSet(trm)
            # print "ReadSet: ",readSet
            refineTypes(trm, readSet) 
        for child in trm.subtrees:
            self.addStateVarsSecond(child)
        if hasattr(trm, "guards"):
            trm.guards.setCode({})
            
    
    def forPre(self):
        if not hasattr(self, "forCtr"):
            self.forCtr = 0
        self.forCtr += 1
        #return u"#pragma ivdep\nFOR_" + self.name + u"_" + self.impl + u"_" + str(self.forCtr)
        return u"FOR_" + self.name + u"_" + self.impl + u"_" + str(self.forCtr)
    def tempDefCode(self):
        # go over the superset entries and divide the supersets equally!
        # collect supersets
        if self.impl == u"loop":
            return u""
        lefts = {}
        retStr = u""
        for i in sorted(self.superset.keys()):
            #print "SS: ", self.superset
            if i in self.params or self.superset[i] not in self.params:
                #print "IGNORING: ",i, self.superset[i]
                continue
            if self.superset[i] not in lefts:
                lefts[self.superset[i]] = []
            lefts[self.superset[i]].append(i)
        for K in lefts:
            n = len(lefts[K])
            Assert(n == 2, "Must divide the set by 2")
            L0 = lefts[K][0]
            #retStr += defineIntervalStmt(L0) + u" = {" + K + u".begin,(" + K + u".end + " + K + u".begin)/2};\n"
            retStr += defineIntervalStmt(L0)+u";\n"
            retStr += defineBegin(L0) +u" = "+defineBegin(K)+u";\n"
            retStr += defineEnd(L0)+u" = ("+defineEnd(K)+u" + "+defineBegin(K)+u")/2;\n"
            L1 = lefts[K][1]
            #retStr += defineIntervalStmt(L1) + u" = {" + L0 + u".end," + K + u".end};\n"
            retStr += defineIntervalStmt(L1)+u";\n"
            retStr += defineBegin(L1) +u" = "+defineEnd(L0)+u";\n"
            retStr += defineEnd(L1)+u" = "+defineEnd(K)+u";\n"
            
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
            curtrm.code = getDecl(name, newparams, defineIntervalCall, "rec")
        else:
            for i in curtrm.subtrees:
                self.computeSupersets(i)
    def getBaseCase(self):
        Assert(self.impl == u"rec", u"Should be recursive!")
        retStr = u"if (BASE_CONSTRAINT_" + self.name + u"(" + u",".join(self.params) + u")){\n"
        retStr += getDecl(self.name, self.params, defineIntervalCall, impl=u"loop") + u";\n"
        retStr += u"return;\n"
        retStr += u"}"
        return retStr 
    def addFunction(self,fvSets,code):
        listFVS = list(fvSets)
        fname = "func" + self.name + "_" + str(len(self.newFuncs)+1)
        newFunc = "void "+ fname + "(" + ",".join([defineIntervalFunc(x) for x in listFVS]) + "){\n"
        newFunc += code
        newFunc += "}\n"
        self.newFuncs.append(newFunc)
        fdecl = fname + "("+ ",".join([defineIntervalCall(x) for x in listFVS])+")"
        return fdecl
    def postProcessPar(self,code):
        #get each line of code and look for comment 
        lines = code.split("PARBOO")
        ctr = 0
        parlevs = []
        parlines = []
        for line in lines:
            if PARLEVEL in line:
                words = line.split(" ")
                parlines.append(ctr)
                parlevs.append((ctr,int(words[words.index(PARLEVEL) + 1])))
            ctr += 1
        #parlevs has line number , parallel dependency levels
        sortedlevels = sorted(parlevs,key=lambda x:x[1])
        #print "SORTED LEVELS",sortedlevels
        parCounts = {}
        for (lnum,lvl) in sortedlevels:
            if lvl not in parCounts:
                parCounts[lvl] = [lnum]
            else:
                parCounts[lvl].append(lnum)
        
       
        ctr = 0
        parctr = 0
        output = []
        for line in lines:
            if ctr not in parlines:
                if len(output) > 0 and "cilk_sync;" in output[-1] and line.strip() == ";":
                    1
                elif line.strip() == ";":
                    output[-1] = output[-1] +";"
                else:
                    output.append(line)
            else:
                lnum = sortedlevels[parctr][0]
                lvl = sortedlevels[parctr][1]
                added_code = lines[lnum]
                if len(parCounts[lvl]) >= 2 and parCounts[lvl][-1] == lnum:
                    #for last one add cilk_sync
                    added_code = added_code + ";\ncilk_sync;"
                elif len(parCounts[lvl]) >= 2 and parCounts[lvl][-1] != lnum:
                    Assert(lnum in parCounts[lvl], "Must be accounted for in parCounts")
                    #add cilk_spawn before it 
                    added_code = "cilk_spawn " + added_code
                output.append(added_code)
                parctr += 1
            ctr+=1
        code = u"\n".join(output)
        return code
    def printCode(self):
        # print "#define FOR_FORWARD(i,s,e) for(int i=s;i<e;i++)"
        # print "#define FOR_BACKWARD(i,s,e) for(int i=e-1;i>=s;i--)"
        ctx = {}
        self.term.setCode(ctx)
        intv = defineIntervalFunc
        print "\n".join(self.newFuncs) 
        print u"void " + getDecl(self.name, self.params, intv, self.impl) + u"{"
        if hasattr(self,"co_set") and self.impl == u"loop":
            #copy optimization active!
            print "__declspec(align(ALIGNMENT)) TYPE V[B * B];"
            print "copy_dist_part(V,PARAM("+self.co_set[0]+"),PARAM("+self.co_set[1]+"));"
        if self.impl == u"rec":
            print self.getBaseCase()
        print self.tempDefCode()
        print self.postProcessPar(self.term.code)
        #print self.term.code
        print u"}"
    def __str__(self):
        retStr = self.name + u"[" 
        retStr += u','.join(self.params) + u"] " + self.impl + u": \n"
        retStr += self.term.__str__() 
        return retStr

        
def getBmProgram(filenames):
    a = []
    pdict = {}
    prgs = parseJsons(filenames)
    # print prgs.keys()
    for prg in sorted(prgs.keys(),reverse=True):
        # print prg
        pdict[prg] ={}
        implList = []
        if u'loop' in prgs[prg]:
            implList.append(u'loop')
        if u'rec' in prgs[prg]:
            implList.append(u'rec')
        
        for impl in implList:
            # print prg,impl
            cur_bmprog = bmProgram(prgs[prg][impl])
            pdict[prg][impl] = cur_bmprog
            a.append(cur_bmprog)
    return (pdict,a)        
