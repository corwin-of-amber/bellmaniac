import codecs
import json
import argparse
import re
import os
from string import Template
from library import *

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
            Assert(self.literal[0].isupper() or self.literal[0]==BOTTOM, "First char of set in TypeTree must be caps or BOTTOM: " + self.literal) 
        if self.literal[0] == BOTTOM:
            self.ns = None
        if self.literal != LT :
            Assert(self.ns is None, "ns value is always None in rootType nodes: lit=" + self.literal + ", ns=" + unicode(self.ns))
        
        Assert(typ[u'$'] == 'Tree', "$ value != identifier in bmType: " + typ[u'$'])
        self.subtrees = []
        
        if self.literal == u'->' and typ[u'subtrees'][0][u'root'][u'literal'] == INTERSECT:
            Assert(typ[u'subtrees'][0][u'subtrees'][1][u'root'][u'literal'] == u'<' and typ[u'subtrees'][0][u'subtrees'][0][u'root'][u'literal'] == MULT, "Must be intersection of X and <")
            mult_node = bmType(typ[u'subtrees'][0][u'subtrees'][0])
            mult_node.literal = u'->'
            R_node = bmType(typ[u'subtrees'][1])
            Assert(len(R_node.subtrees) == 0,"R node should not have children")
            
            R_lit = R_node.literal 
            mn_s0_lit = mult_node.subtrees[0].literal
            mn_s1_lit = mult_node.subtrees[1].literal
            
            R_node.literal = mn_s0_lit
            mult_node.subtrees[0].literal = mn_s1_lit
            mult_node.subtrees[1].literal = R_lit
            
            self.subtrees.append(R_node)
            self.subtrees.append(mult_node)
            
            Assert(len(self.subtrees[1].subtrees) == 2,"Two children of mult_node")
            
        else:
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
    def getSetEnds(self):
        Assert(isSet(self.literal) or self.literal == u"U", u"Should be set or union")
        if isSet(self.literal):
            return u",".join([defineBegin(self.literal), defineEnd(self.literal)])
        elif self.literal == u"U":
            return u",".join([defineBegin(self.subtrees[0]), defineEnd(self.subtrees[0]), defineBegin(self.subtrees[1]), defineEnd(self.subtrees[1]) ])
    
    def arrType(self):
        Assert(self.literal == u"->" and len(self.subtrees) == 2 and self.subtrees[1].literal == "->", u"these should be MAPSTO: " + self.literal + "," + self.subtrees[1].literal )
        return self.subtrees[0].literal, self.subtrees[1].subtrees[0].literal
        