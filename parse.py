import pdb
import sys
import copy

# NOTE __.... are reserved sorts, fxn names, constant names etc
# __sort (is a predefined sort), __nosort (has no sort defined; such as product of keyword), __keyword (is a keyword), __null (type ()), __new (getting defined rn)
# We do not support ite's where t&e do not share a type

# TODO keywords are not nearly complete; but likely sufficient

s = 8
A = 512



class Token:
    def __init__ (self, s):
        self.ogs = str(s)
        self.s = str(s)
    def __repr__(self):
        return self.s

    def assignSorts(self, sorts, keywords, prestate):
        if self.s in prestate.keys():
            self.sort = prestate[self.s]
            if self.sort[0] == []:
                self.sort = self.sort[1]
            #assert(self.soft in sorts)  Can assert all parts of self.sort is in sorts; but no reason to
        elif self.s in keywords:
            self.sort = "__keyword"
        elif self.s in sorts:
            self.sort = "__sort"
        elif isinstance(self.s, str) and self.s.isnumeric(): # As we are in a QF_UFLIA extension
            self.sort = "Int"
        else:
            self.sort = "__new" # Is almost certainly a new definition
            #pdb.set_trace()
            pass

    def toSMTLIB(self):
        if self.s == "=p": # Due to Core SMTLIB
            return "="
        return self.s

    def findAllTermsSatisfying(self, lamb,letExplore=True,useList=False):
        ret = list() if useList else set()
        if lamb(self):
            if useList:
                ret.append(self)
            else:
                ret.add(self)
        return ret

    def regenss(self):
        return self.s


class LevelPart:
    def __init__(self, s, level):
        self.ogs = s
        self.s = s
        self.slps = []
        self.level = level

        buffer = ""
        atPlusLevel = 0
        for ch in s:
            buffer = buffer + ch
            if ch=="(":
                if buffer.strip() != "(" and atPlusLevel==0:
                    self.slps.extend([Token(tok) for tok in buffer[:-1].strip().split()])
                    buffer = "("
                atPlusLevel += 1
            elif ch==")":
                atPlusLevel -= 1
                if atPlusLevel == 0:
                    buffer = buffer.strip()
                    self.slps.append(LevelPart(buffer[1:-1], level+1))
                    buffer = ""
        if buffer.strip() != "":
            buffer = buffer.strip()
            self.slps.extend([Token(tok) for tok in buffer.split()])

    def __repr__(self):
        return "LevelPart at Level "+str(self.level)+" with the following "+str(len(self.slps))+" sub level parts:\n\n\t"+("\n\t".join([slp.s for slp in self.slps]))

    # No support for defined or parameterized sorts; Assumes all have arity 0
    def getSorts(self, partialSorts):
        if len(self.slps)>0 and isinstance(self.slps[0],Token) and self.slps[0].s == "declare-sort":
            partialSorts.add(self.slps[1].s)
        for slp in self.slps:
            if isinstance(slp, LevelPart):
                slp.getSorts(partialSorts)

    # No support for defined sorts; stick to uninterpreted functions
    def setStates(self, preState, sorts, keywords):
        self.prestate = preState
        state = copy.deepcopy(preState)
        
        if len(self.slps)>0 and isinstance(self.slps[0],Token) and self.slps[0].s == "declare-fun":
            assert(len(self.slps)==4)
            state[self.slps[1].s] = ([inpSort.s for inpSort in self.slps[2].slps], self.slps[3].s)
        elif len(self.slps)>0 and isinstance(self.slps[0],Token) and self.slps[0].s == "declare-const":
            assert(len(self.slps)==3)
            state[self.slps[1].s] = ([], self.slps[2].s)
        elif len(self.slps)>0 and isinstance(self.slps[0],Token) and self.slps[0].s == "let":
            assert(len(self.slps)==3)
            postLetState = copy.deepcopy(state)
            for let in self.slps[1].slps:
                assert(len(let.slps)==2)
                let.slps[1].setStates(postLetState, sorts, keywords)
                let.slps[1].assignSorts(sorts, keywords)
                postLetState[let.slps[0].s] = let.slps[1].sort
                let.sort = "__nosort"
            self.slps[1].sort = "__nosort"
            postLetState = self.slps[1].setStates(postLetState, sorts, keywords)
            self.postLetState = postLetState
            if isinstance(self.slps[2],LevelPart):
                self.slps[2].setStates(postLetState, sorts, keywords)
        else:
            for slp in self.slps:
                if isinstance(slp, LevelPart):
                    state = slp.setStates(state, sorts, keywords)
        return state 

    def assignSorts(self, sorts, keywords):
        if "sort" in dir(self):
            return # No need for redundancy
        if "prestate" not in dir(self):
            self.sort = "__nosort"
            return 
        if len(self.slps)>0 and isinstance(self.slps[0],Token) and self.slps[0].s in ["set-info", "set-logic", "check-sat", "exit"]:
            self.sort = "__nosort"
            return
        for slp in self.slps:
            if isinstance(slp, Token) :
                #try:
                slp.assignSorts(sorts, keywords, self.prestate)
                #except:
                #    pdb.set_trace()
                #    pass
            else:
                slp.assignSorts(sorts, keywords)
        if len(self.slps)>0 and isinstance(self.slps[0],Token) and self.slps[0].s in self.prestate.keys():
            self.sort = self.prestate[self.slps[0].s][1]  # Note how we DO NOT assert the sorts of the first element; we ostensibly could tho

            #try: 
            assert(self.sort in sorts)
            #except:
            #    pdb.set_trace()
            #    pass
        elif len(self.slps)==0:
            self.sort = "__nullsort"
        elif len(self.slps)>0 and isinstance(self.slps[0],Token) and self.slps[0].s in ["declare-fun", "declare-const","assert","get-assignment","set-option","get-model"]:
            self.sort = "__nosort"
        elif len(self.slps)>0 and isinstance(self.slps[0],Token) and self.slps[0].s == "let":
            assert(len(self.slps)==3)
            self.sort = self.slps[2].sort
        elif len(self.slps)>0 and isinstance(self.slps[0],Token) and self.slps[0].s == "ite":
            assert(len(self.slps)==4)
            assert(self.slps[2].sort == self.slps[3].sort)
            self.sort = self.slps[2].sort
        elif len(self.slps)==2 and isinstance(self.slps[0],Token) and self.slps[0].s not in sorts and self.slps[0].s not in keywords: # Should likely be a (newname expr) form thing
            self.sort = "__nosort"
        elif all([slp.sort=="__nosort" for slp in self.slps]):
            self.sort = "__nosort"
        else:
            pdb.set_trace()
            pass

    def toSMTLIB(self):
        if self.level > 0:
            return "("+" ".join([slp.toSMTLIB() for slp in self.slps])+")"
        else: 
            return "\n".join([slp.toSMTLIB() for slp in self.slps])

    def findAllTermsSatisfying(self, lamb, letExplore=True, useList=False):
        ret = list() if useList else set()
        if (not letExplore) and len(self.slps)>0 and self.slps[0].s=="let":
            return ret
        for slp in self.slps:
            #if (not letExplore) and isinstance(slp, LevelPart) and len(slp.slps)>0 and slp.slps[0].s=="let":
            #    continue
            if useList:
                ret += slp.findAllTermsSatisfying(lamb,letExplore=letExplore,useList=True)
            else:
                ret |= slp.findAllTermsSatisfying(lamb, letExplore=letExplore)
        if lamb(self):
            if useList:
                ret.append(self)
            else:
                ret.add(self)
        return ret

    def firstDeclare(self):
        i = 0
        for j in self.slps:
            if isinstance(j,LevelPart):
                if j.slps[0].s in ["declare-fun","declare-const","assert","declare-sort","define-fun","define-const","check-sat"]: #Includes unsupported defines too; assumes if one of these used we're done setting stuff
                    return i
            i += 1
        return i

    def setLogic(self, logic):
        for i,j in enumerate(self.slps):
            if isinstance(j,LevelPart):
                if j.slps[0].s == "set-logic":
                    break
        self.slps[i].slps[1] = Token(logic)

    def regenss(self):
        slpss = list()
        for slp in self.slps:
            if isinstance(slp, Token):
                slpss.append(slp.regenss())
            else:
                slpss.append("("+slp.regenss()+")")

        if self.level > 0:
            self.s = " ".join(slpss)
        else: 
            self.s = "\n".join(slpss)
        return self.s

# INSTANTIATORS
# BASES
def a1(op,t1):
    T1 = t1.s if isinstance(t1,Token) else ("("+t1.s+")")
    return LevelPart(op+" "+T1,1)
def a2(op,t1,t2):
    T1 = t1.s if isinstance(t1,Token) else ("("+t1.s+")")
    T2 = t2.s if isinstance(t2,Token) else ("("+t2.s+")")
    return LevelPart(op+" "+T1+" "+T2,1)
def a3(op,t1,t2,t3):
    T1 = t1.s if isinstance(t1,Token) else ("("+t1.s+")")
    T2 = t2.s if isinstance(t2,Token) else ("("+t2.s+")")
    T3 = t3.s if isinstance(t3,Token) else ("("+t3.s+")")
    return LevelPart(op+" "+T1+" "+T2+" "+T3,1)
# BASICS
def AND(term1,term2):
    return a2("and",term1,term2)#LevelPart("and ("+term1.s+") ("+term2.s+")",1)
def OR(term1,term2):
    return a2("or",term1,term2)#LevelPart("or ("+term1.s+") ("+term2.s+")",1)
def IMPL(term1,term2):
    return a2("=>",term1,term2)#LevelPart("=> ("+term1.s+") ("+term2.s+")",1)
def BLOCK(term1):
    return a1("Block",term1)#LevelPart("Block ("+term1.s+")",1)
def ALIGN(term1):
    return a1("Align",term1)#LevelPart("Align ("+term1.s+")",1)
def OFFSET(term1):
    return a1("Offset",term1)#LevelPart("Offset ("+term1.s+")",1)
def BASE(term1):
    return a1("Base",term1)#LevelPart("Offset ("+term1.s+")",1)
def CREATE(term1,term2):
    return a2("Create",term1,term2)#LevelPart("Create ("+term1.s+") ("+term2.s+")",1)
#def ADDRESS(term1):
#    return a1("Address",term1)#LevelPart("Address ("+term1.s+")",1)
def MINP(term1,term2):
    return a2("-p",term1,term2)#LevelPart("-p ("+term1.s+") ("+term2.s+")",1)
def EQP(term1,term2):
    return a2("=p",term1,term2)#LevelPart("=p ("+term1.s+") ("+term2.s+")",1)
def EQZ(term1,term2):
    return a2("=",term1,term2)#LevelPart("= ("+term1.s+") ("+term2.s+")",1)
def LEQ(term1,term2):
    return a2("<=",term1,term2)#LevelPart("<= ("+term1.s+") ("+term2.s+")",1)
def LEQP(term1,term2):
    return a2("<=p",term1,term2)#LevelPart("<=p ("+term1.s+") ("+term2.s+")",1)
def ADD(term1,term2):
    return a2("+",term1,term2)#LevelPart("+ ("+term1.s+") ("+term2.s+")",1)
def ADDP(term1,term2):
    return a2("+p",term1,term2)#LevelPart("+p ("+term1.s+") ("+term2.s+")",1)
def PROD(term1,term2):
    return a2("*",term1,term2)#LevelPart("* ("+term1.s+") ("+term2.s+")",1)
def NEG(term1):
    return a1("-",term1)#LevelPart("- ("+term1.s+")",1)
def NOT(term1):
    return a1("not",term1)#LevelPart("not ("+term1.s+")",1)
def QUOT(term1):
    return a1("quot",term1)#LevelPart("quot ("+term1.s+")",1)
def IFF(term1, term2):
    return AND(IMPL(term1,term2),IMPL(term2,term1))
#SHORTHANDS
def ADDRESS(term1):
    return ADD(BASE(BLOCK(term1)),OFFSET(term1))
def DB(term1,term2):
    return EQZ(ALIGN(term1),ALIGN(term2))
def DELTA(term1,term2):
    return EQZ(BLOCK(term1),BLOCK(term2))
def DELTA0(term1,term2):
    def neq0(t):
        return NOT(EQZ(t,Token("0")))
    return AND(DELTA(term1,term2),AND(neq0(ADDRESS(term1)),neq0(ADDRESS(term2))))
def LT(term1,term2):
    return AND(NOT(EQZ(term1,term2)), LEQ(term1,term2))
def MIN(term1,term2):
    return ADD(term1,NEG(term2))
def RANGE(term1,term2):
    return AND(LT(Token("0"), ADD(ADDRESS(term1),PROD(Token(s),term2))),LEQ(ADD(ADDRESS(term1),PROD(Token(s),term2)),Token(A)))
# OPTIM SHORTHANDS
def DELTAPLUS(term1,term2):
    return EQZ(term1.slps[1], term2.slps[1])
def DELTA0PLUS(term1,term2):
    return DELTAPLUS(term1,term2)
def RANGEPLUS(term1,term2):
    return AND(LT(Token("0"), ADD(term1.slps[2],PROD(Token(s),term2))),LEQ(ADD(term1.slps[2],PROD(Token(s),term2)),Token(A)))
#COMMANDS
def DECLARE_FUN(symbol, in_sorts, out_sort):
    return a3("declare-fun",Token(symbol),LevelPart(" ".join(in_sorts),1),Token(out_sort))
def DECLARE_CONST(symbol,sort):
    return a2("declare-const",Token(symbol),Token(sort))
def DECLARE_SORT(symbol,arity):
    return a2("declare-sort",Token(symbol),Token(str(arity)))
def ASSERT(assertion):
    return a1("assert",assertion)

# think about uninterpreted quot
# think about this s,A token constants

def gatherListWithAnds(l):# NOTE this lies about level; should not use level hereafter except 0/1 check
    if len(l)==0:
        return Token("true")
    runner = l[0]
    for i in range(1, len(l)):
        runner = AND(runner, l[i])
    return runner

def Ap(term):
    return EQP(CREATE(BLOCK(term),ADDRESS(term)),term)
def Applus(term):
    if (isinstance(term,LevelPart)and(len(term.slps)>0)and(term.slps[0].s=="Create+")):
        return Token("true")
    return Ap(term)


def Amod(term):
    return AND(LEQ(Token("0"),ALIGN(term)), LEQ(ALIGN(term),ADD(Token(s),NEG(Token("1")))))

def Ain(term):
    p = term
    return AND(LEQ(Token("0"),ADDRESS(p)),LEQ(ADDRESS(p),Token(A)))
def Ainplus(term):
    if (isinstance(term,LevelPart)and(len(term.slps)>0)and(term.slps[0].s=="Create+")):
        return Token("true")
    return Ain(term)

def Ao(term):
    return EQZ(OFFSET(term),ADD(PROD(Token(s),QUOT(term)),ALIGN(term))) 

def Aleq(term):
    p = term.slps[1]
    q = term.slps[2]
    return IMPL(DELTA0(p,q),IFF(LEQP(p,q),LEQ(OFFSET(p),OFFSET(q))))

def Amin(term):
    p = term.slps[1]
    q = term.slps[2]
    return IMPL(AND(DELTA0(p,q),DB(p,q)),EQZ(PROD(Token(s),MINP(p,q)),MIN(OFFSET(p),OFFSET(q))))
def Aminplus(term):
    p = term.slps[1]
    q = term.slps[2]
    if (isinstance(p,LevelPart)and(len(p.slps)>0)and(p.slps[0].s=="Create+")) and (isinstance(q,LevelPart)and(len(q.slps)>0)and(q.slps[0].s=="Create+")):
        return IMPL(AND(DELTA0PLUS(p,q),DB(p,q)),EQZ(PROD(Token(s),MINP(p,q)),MIN(OFFSET(p),OFFSET(q))))
    return Amin(term)


def Aplus(term):
    p = term.slps[1]
    i = term.slps[2]
    return IMPL(AND(NOT(EQZ(ADDRESS(p),Token("0"))),RANGE(p,i)),EQZ(OFFSET(ADDP(p,i)),ADD(OFFSET(p),PROD(Token(s),i))))
def Aplusplus(term):
    p = term.slps[1]
    i = term.slps[2]
    if (isinstance(p,LevelPart)and(len(p.slps)>0)and(p.slps[0].s=="Create+")):
        return IMPL(RANGEPLUS(p,i),EQZ(OFFSET(ADDP(p,i)),ADD(OFFSET(p),PROD(Token(s),i))))
    return Aplus(term)


def Adelt(term):
    p = term.slps[1]
    i = term.slps[2]
    return IMPL(AND(NOT(EQZ(ADDRESS(p),Token("0"))),RANGE(p,i)),DELTA(ADDP(p,i),p))
def Adeltplus(term):
    p = term.slps[1]
    i = term.slps[2]
    if (isinstance(p,LevelPart)and(len(p.slps)>0)and(p.slps[0].s=="Create+")):
        return IMPL(RANGEPLUS(p,i),DELTAPLUS(ADDP(p,i),p))
    return Adelt(term)

def Aa(term):
    l = term.slps[1]
    a = term.slps[2]
    return IMPL(AND(LEQ(Token("0"),a),LEQ(a,Token(A))),EQP(ADDRESS(CREATE(l,a)),a)) 

def Ab(term):
    l = term.slps[1]
    a = term.slps[2]
    return IMPL(AND(LEQ(Token("0"),a),LEQ(a,Token(A))),EQP(BLOCK(CREATE(l,a)),l)) 



def Aaplus(term):
    l = term.slps[1]
    a = term.slps[2]
    return EQP(ADD(BASE(l),OFFSET(CREATE(l,a))),a) 

def Abplus(term):
    l = term.slps[1]
    a = term.slps[2]
    return EQP(BLOCK(CREATE(l,a)),l) 


def convertFile(filename,_s,_A): # is a path
    # Set globals
    global s, A
    s = _s
    A = _A



    # Readlines of file
    with open(filename) as f:
        lines = list()
        line = f.readline()
        while line:
            lines.append(line)
            line = f.readline()
    clines = " ".join(lines)

    # Generate a basic parse tree over lines
    parseTree = LevelPart(clines, 0)

    # Gather sorts used
    sorts = set(["Bool","Int","Pointer"])
    parseTree.getSorts(sorts)

    # set A and s, if set-info'd
    sDecls = parseTree.findAllTermsSatisfying(lambda t: isinstance(t,LevelPart)and(len(t.slps)==3)and t.slps[0].s=="set-info" and t.slps[1].s==":s",letExplore=True)
    ADecls = parseTree.findAllTermsSatisfying(lambda t: isinstance(t,LevelPart)and(len(t.slps)==3)and t.slps[0].s=="set-info" and t.slps[1].s==":A",letExplore=True)
    if len(sDecls)==1:
        s = int(list(sDecls)[0].slps[2].s)
    if len(ADecls)==1:
        A = int(list(sDecls)[0].slps[2].s)



    keywords = set(["declare-fun", "declare-const","assert", "let", "ite", "check-sat", "get-assignment","exit","set-option","get-model"])

    # Make each expression gather its state
    functions = dict()
    # Bool/Core
    functions["true"] = ([],"Bool")
    functions["false"] = ([],"Bool")
    functions["not"] = (["Bool"], "Bool")
    functions["=>"] = (["Bool","Bool"],"Bool")
    functions["and"] = (["Bool","Bool"],"Bool")
    functions["or"] = (["Bool","Bool"],"Bool") # Convenience extension
    functions["xor"] = (["Bool","Bool"],"Bool") # Convenience extension
    # NOTE ite handled as keyword
    # NOTE = not included parametrically
    # NOTE distinct not included
    # QF_UFLIA ones
    #functions[-] = (["Int"],"Int")   problem: cannot handle two - symbols; add one for subtr; Actually subtr is not necessarily a part of QF_UFLIA
    functions["+"] = (["Int","Int"],"Int")
    functions["-"] = (["Int"],"Int") # Is negation
    functions["*"] = (["Int","Int"],"Int") # It is the user's responsibility to ensure one of these is a constant
    functions["<="] = (["Int","Int"],"Int")
    functions["<"] = (["Int","Int"],"Int") # Convenience extension
    functions[">="] = (["Int","Int"],"Int") # Convenience extension
    functions[">"] = (["Int","Int"],"Int") # Convenience extension
    functions["="] = (["Int","Int"],"Int") # Convenience extension
    # BPA ones
    functions["Block"] = (["Pointer"], "Int")
    functions["Offset"] = (["Pointer"], "Int")
    functions["Base"] = (["Int"], "Int")
    functions["Align"] = (["Pointer"], "Int")
    functions["+p"] = (["Pointer","Int"],"Pointer") # ASSERT 
    functions["-p"] = (["Pointer","Pointer"],"Int") # ASSERT
    functions["<=p"] = (["Pointer","Pointer"],"Bool")
    functions["Create"] = (["Int","Int"],"Pointer") #Is (.,.)
    #functions["Address"] = (["Pointer"], "Int") # Is composite, Base(Block(.))+Offset(.) # NOTE commented out as it should not be used by user
    functions["=p"] = (["Pointer","Pointer"],"Bool")  # From Core
    final_fxns = parseTree.setStates(functions, sorts, keywords)

    # assign each expression a type based on its prestate and its elements' states
    parseTree.assignSorts(sorts, keywords)
    #pdb.set_trace()

    # The transformation transform formula to formula; should only affect assertions; thus
    allAsserts = parseTree.findAllTermsSatisfying(lambda t: isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="assert" or t.slps[0].s=="let"),letExplore=True,useList=True)
    for asrt in allAsserts:
        #pdb.set_trace()
        asrtt = asrt.slps[1] if asrt.slps[0].s=="assert" else asrt.slps[2]
        if asrt.slps[0].s=="let":
            def eq(setter):
                if setter.slps[1].sort == "Pointer":
                    return EQP(setter.slps[0],setter.slps[1])
                return EQZ(setter.slps[0],setter.slps[1]) # Sometimes uses the wrong type (= for Pointer) but that should be alright
            asrtt = gatherListWithAnds([asrtt] + [eq(setter) for setter in asrt.slps[1].slps])
            asrtt.setStates(asrt.slps[2].prestate, sorts, keywords)
            asrtt.assignSorts(sorts, keywords)
            asrtt.regenss()
        # find all instances of certain terms in formulas
        allPointers = asrtt.findAllTermsSatisfying(lambda t : ("sort"in dir(t))and(t.sort=="Pointer"),letExplore=False)
        allLEQPs = asrtt.findAllTermsSatisfying(lambda t : (isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="<=p")),letExplore=False)
        allSUMPs = asrtt.findAllTermsSatisfying(lambda t : (isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="+p")),letExplore=False)
        allMINPs = asrtt.findAllTermsSatisfying(lambda t : (isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="-p")),letExplore=False)
        allCREATEs = asrtt.findAllTermsSatisfying(lambda t : (isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="Create")),letExplore=False)
       
        # Instantiate all axioms
        F = asrtt
        Fp = gatherListWithAnds([Ap(term) for term in allPointers])
        Fmod = gatherListWithAnds([Amod(term) for term in allPointers])
        Fin = gatherListWithAnds([Ain(term) for term in allPointers])
        Fo = gatherListWithAnds([Ao(term) for term in allPointers])
        Fdelt = gatherListWithAnds([Adelt(term) for term in allSUMPs])
        Fplus = gatherListWithAnds([Aplus(term) for term in allSUMPs])
        Fmin = gatherListWithAnds([Amin(term) for term in allMINPs])
        Fleq = gatherListWithAnds([Aleq(term) for term in allLEQPs])
        Fa = gatherListWithAnds([Aa(term) for term in allCREATEs])
        Fb = gatherListWithAnds([Ab(term) for term in allCREATEs])

        # Combine axiom deployments and replace original assertion
        recon = gatherListWithAnds([F,Fp,Fmod,Fin,Fo,Fdelt,Fplus,Fmin,Fleq,Fa,Fb])
        if (asrt.slps[0].s=="assert"):
            asrt.slps[1] = recon
        if (asrt.slps[0].s=="let"):
            asrt.slps[2] = recon

        parseTree.regenss()

    # We Must Introduce uninterpreted function quot: Pointer->Int, and the integers s and A
    index = parseTree.firstDeclare()
    parseTree.slps = parseTree.slps[:index] + [
        DECLARE_SORT("Pointer",0),
        DECLARE_FUN("Block",["Pointer"], "Int"),
        DECLARE_FUN("Offset",["Pointer"], "Int"),
        DECLARE_FUN("Base",["Int"], "Int"),
        DECLARE_FUN("Align",["Pointer"], "Int"),
        DECLARE_FUN("+p",["Pointer","Int"],"Pointer"),
        DECLARE_FUN("-p",["Pointer","Pointer"],"Int"),
        DECLARE_FUN("<=p",["Pointer","Pointer"],"Bool"),
        DECLARE_FUN("Create",["Int","Int"],"Pointer"),
        DECLARE_FUN("quot",["Pointer"],"Int"),
        #DECLARE_CONST("s","Int"),
        #DECLARE_CONST("A","Int")
        ] + parseTree.slps[index:]

    # Change Logic BPA+ -> QF_UFLIA
    parseTree.setLogic("QF_UFLIA")

    # convert back into smtlib based on endpoints' values
    smtlib = parseTree.toSMTLIB()

    return smtlib


def convertFilePlus(filename,_s,_A): # is a path
    # Set globals
    global s, A
    s = _s
    A = _A

    # Readlines of file
    with open(filename) as f:
        lines = list()
        line = f.readline()
        while line:
            lines.append(line)
            line = f.readline()
    clines = " ".join(lines)

    # Generate a basic parse tree over lines
    parseTree = LevelPart(clines, 0)

# set A and s, if set-info'd
    sDecls = parseTree.findAllTermsSatisfying(lambda t: isinstance(t,LevelPart)and(len(t.slps)==3)and t.slps[0].s=="set-info" and t.slps[1].s==":s",letExplore=True)
    ADecls = parseTree.findAllTermsSatisfying(lambda t: isinstance(t,LevelPart)and(len(t.slps)==3)and t.slps[0].s=="set-info" and t.slps[1].s==":A",letExplore=True)
    if len(sDecls)==1:
        s = int(list(sDecls)[0].slps[2].s)
    if len(ADecls)==1:
        A = int(list(sDecls)[0].slps[2].s)

    # Gather sorts used
    sorts = set(["Bool","Int","Pointer","Int+"])
    parseTree.getSorts(sorts)

    keywords = set(["declare-fun", "declare-const","assert", "let", "ite", "check-sat", "get-assignment","exit","set-option","get-model"])

    # Make each expression gather its state
    functions = dict()
    # Bool/Core
    functions["true"] = ([],"Bool")
    functions["false"] = ([],"Bool")
    functions["not"] = (["Bool"], "Bool")
    functions["=>"] = (["Bool","Bool"],"Bool")
    functions["and"] = (["Bool","Bool"],"Bool")
    functions["or"] = (["Bool","Bool"],"Bool") # Convenience extension
    functions["xor"] = (["Bool","Bool"],"Bool") # Convenience extension
    # NOTE ite handled as keyword
    # NOTE = not included parametrically
    # NOTE distinct not included
    # QF_UFLIA ones
    #functions[-] = (["Int"],"Int")   problem: cannot handle two - symbols; add one for subtr; Actually subtr is not necessarily a part of QF_UFLIA
    functions["+"] = (["Int","Int"],"Int")
    functions["-"] = (["Int"],"Int") # Is negation
    functions["*"] = (["Int","Int"],"Int") # It is the user's responsibility to ensure one of these is a constant
    functions["<="] = (["Int","Int"],"Int")
    functions["<"] = (["Int","Int"],"Int") # Convenience extension
    functions[">="] = (["Int","Int"],"Int") # Convenience extension
    functions[">"] = (["Int","Int"],"Int") # Convenience extension
    functions["="] = (["Int","Int"],"Int") # Convenience extension
    # BPA ones
    functions["Block"] = (["Pointer"], "Int")
    functions["Offset"] = (["Pointer"], "Int")
    functions["Base"] = (["Int"], "Int")
    functions["Align"] = (["Pointer"], "Int")
    functions["+p"] = (["Pointer","Int"],"Pointer") # ASSERT 
    functions["-p"] = (["Pointer","Pointer"],"Int") # ASSERT
    functions["<=p"] = (["Pointer","Pointer"],"Bool")
    functions["Create"] = (["Int","Int"],"Pointer") #Is (.,.)
    #functions["Address"] = (["Pointer"], "Int") # Is composite, Base(Block(.))+Offset(.) # NOTE commented out as it should not be used by user
    functions["=p"] = (["Pointer","Pointer"],"Bool")  # From Core
    # BPA+ ones
    functions["Create+"] = (["Int","Int+"],"Pointer")
    functions["Reduce"] = (["Int+"],"Int")
    # NOTE do not use Int+ = Int+, no real reason just not implemented
    final_fxns = parseTree.setStates(functions, sorts, keywords)

    # assign each expression a type based on its prestate and its elements' states
    parseTree.assignSorts(sorts, keywords)

    # The transformation transform formula to formula; should only affect assertions; thus
    allAsserts = parseTree.findAllTermsSatisfying(lambda t: isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="assert" or t.slps[0].s=="let"),letExplore=True,useList=True)
    for asrt in allAsserts:
        #pdb.set_trace()
        asrtt = asrt.slps[1] if asrt.slps[0].s=="assert" else asrt.slps[2]
        if asrt.slps[0].s=="let":
            def eq(setter):
                if setter.slps[1].sort == "Pointer":
                    return EQP(setter.slps[0],setter.slps[1])
                return EQZ(setter.slps[0],setter.slps[1]) # Sometimes uses the wrong type (= for Pointer) but that should be alright
            asrtt = gatherListWithAnds([asrtt] + [eq(setter) for setter in asrt.slps[1].slps])
            asrtt.setStates(asrt.slps[2].prestate, sorts, keywords)
            asrtt.assignSorts(sorts, keywords)
            asrtt.regenss()
        # find all instances of certain terms in formulas
        allPointers = asrtt.findAllTermsSatisfying(lambda t : ("sort"in dir(t))and(t.sort=="Pointer"),letExplore=False)
        allLEQPs = asrtt.findAllTermsSatisfying(lambda t : (isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="<=p")),letExplore=False)
        allSUMPs = asrtt.findAllTermsSatisfying(lambda t : (isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="+p")),letExplore=False)
        allMINPs = asrtt.findAllTermsSatisfying(lambda t : (isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="-p")),letExplore=False)
        allCREATEs = asrtt.findAllTermsSatisfying(lambda t : (isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="Create")),letExplore=False)
        allCREATEpluss = asrtt.findAllTermsSatisfying(lambda t : (isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="Create+")),letExplore=False)

       
        # Instantiate all axioms
        F = asrtt
        Fp = gatherListWithAnds([Applus(term) for term in allPointers])
        Fmod = gatherListWithAnds([Amod(term) for term in allPointers])
        Fin = gatherListWithAnds([Ainplus(term) for term in allPointers])
        Fo = gatherListWithAnds([Ao(term) for term in allPointers])
        Fdelt = gatherListWithAnds([Adeltplus(term) for term in allSUMPs])
        Fplus = gatherListWithAnds([Aplusplus(term) for term in allSUMPs])
        Fmin = gatherListWithAnds([Aminplus(term) for term in allMINPs])
        Fleq = gatherListWithAnds([Aleq(term) for term in allLEQPs])
        Fa = gatherListWithAnds([Aa(term) for term in allCREATEs])
        Fb = gatherListWithAnds([Ab(term) for term in allCREATEs])
        Faplus = gatherListWithAnds([Aaplus(term) for term in allCREATEpluss])
        Fbplus = gatherListWithAnds([Abplus(term) for term in allCREATEpluss])

        # Combine axiom deployments and replace original assertion
        recon = gatherListWithAnds([F,Fp,Fmod,Fin,Fo,Fdelt,Fplus,Fmin,Fleq,Fa,Fb,Faplus,Fbplus])
        if (asrt.slps[0].s=="assert"):
            asrt.slps[1] = recon
        if (asrt.slps[0].s=="let"):
            asrt.slps[2] = recon

        parseTree.regenss()


    # NOTE that the recon trees are very simplistic and lack features like sorts; the whole pipeline should be reran over the output if sorts etc. are redesired
    
    # remove all reduce calls
    allReduces = parseTree.findAllTermsSatisfying(lambda t: isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="Reduce"),letExplore=True,useList=True)
    for reduc in allReduces:
        reduc.s = reduc.slps[1].s
        if isinstance(reduc.slps[1],LevelPart):
            reduc.slps = reduc.slps[1].slps
        else:
            reduc.toSMTLIB= reduc.slps[1].toSMTLIB
            #self.mark_reduc = True
    # Make all Create+ calls create calls
    allCreatePs = parseTree.findAllTermsSatisfying(lambda t: isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="Create+"),letExplore=True)
    for createP in allCreatePs:
        createP.slps[0].s="Create"

    #add restrictions on all Int+ values, convert them
    allIntPs = parseTree.findAllTermsSatisfying(lambda t: isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[-1].s=="Int+"),letExplore=True) #Can only be declare-fun and declare-const as lets can only base values on existing values and Int+ is not the result of any function
    intprests = {}
    for intPDecl in allIntPs:
        #pdb.set_trace()
        intPDecl.slps[-1].s = "Int"
        intp = intPDecl.slps[1]
        intprests[intPDecl] = ASSERT(AND(LEQ(Token(1),intp), LEQ(intp,Token(s))))
    # Insert the restrictions in order, bear in mind how all are in top level
    for intPDecl in intprests.keys():
        for i,slp in enumerate(parseTree.slps):
            if slp==intPDecl:
                break
        parseTree.slps = parseTree.slps[:i+1] +[intprests[intPDecl]]+ parseTree.slps[i+1:]

        
 
    # We Must Introduce uninterpreted function quot: Pointer->Int, and the integers s and A
    index = parseTree.firstDeclare()
    parseTree.slps = parseTree.slps[:index] + [
        DECLARE_SORT("Pointer",0),
        DECLARE_FUN("Block",["Pointer"], "Int"),
        DECLARE_FUN("Offset",["Pointer"], "Int"),
        DECLARE_FUN("Base",["Int"], "Int"),
        DECLARE_FUN("Align",["Pointer"], "Int"),
        DECLARE_FUN("+p",["Pointer","Int"],"Pointer"),
        DECLARE_FUN("-p",["Pointer","Pointer"],"Int"),
        DECLARE_FUN("<=p",["Pointer","Pointer"],"Bool"),
        DECLARE_FUN("Create",["Int","Int"],"Pointer"),
        DECLARE_FUN("quot",["Pointer"],"Int"),
        #DECLARE_CONST("s","Int"),
        #DECLARE_CONST("A","Int")
        ]  +parseTree.slps[index:]

   
        
    # Change Logic BPA+ -> QF_UFLIA
    parseTree.setLogic("QF_UFLIA")

    # convert back into smtlib based on endpoints' values
    smtlib = parseTree.toSMTLIB()

    return smtlib

def convertFileTo(infile,_s,_A,outfile=None):
    output = convertFile(infile,_s,_A)
    if outfile != None:
        with open(outfile,"w") as f:
            f.write(output)
    return output

def convertFileToPlus(infile,_s,_A,outfile=None):
    output = convertFilePlus(infile,_s,_A)
    if outfile != None:
        with open(outfile,"w") as f:
            f.write(output)
    return output

if __name__ == "__main__":
    print(sys.argv)
    if len(sys.argv) == 3:
        output = convertFileTo(sys.argv[1],8,512,sys.argv[2])
    elif len(sys.argv) == 5:
        output = convertFileTo(sys.argv[1],sys.argv[3],sys.argv[4],sys.argv[2])
    elif len(sys.argv) == 2:
        output = convertFile(sys.argv[1],8,512)
    elif len(sys.argv) == 4:
        output = convertFileToPlus(sys.argv[1],8,512,sys.argv[2])
    elif len(sys.argv) == 6:
        output = convertFileToPlus(sys.argv[1],sys.argv[3],sys.argv[4],sys.argv[2])

    print(output)
