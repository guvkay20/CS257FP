import pdb
import sys
import copy

# NOTE __.... are reserved sorts, fxn names, constant names etc
# __sort (is a predefined sort), __nosort (has no sort defined; such as product of keyword), __keyword (is a keyword), __null (type ()), __new (getting defined rn)
# We do not support ite's where t&e do not share a type

# TODO keywords are not nearly complete; but likely sufficient

class Token:
    def __init__ (self, s):
        self.s = s
    def __repr__(self):
        return self.s

    def assignSorts(self, sorts, keywords, prestate):
        if self.s in prestate.keys():
            self.sort = prestate[self.s]
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

    def findAllTermsSatisfying(self, lamb):
        ret = set()
        if lamb(self):
            ret.add(self)
        return ret



class LevelPart:
    def __init__(self, s, level):
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
        elif len(self.slps)>0 and isinstance(self.slps[0],Token) and self.slps[0].s in ["declare-fun", "assert"]:
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

    def findAllTermsSatisfying(self, lamb):
        ret = set()
        if lamb(self):
            ret.add(self)
        for slp in self.slps:
            ret |= slp.findAllTermsSatisfying(lamb)
        return ret

    def firstDeclare(self):
        i = 0
        for j in self.slps:
            if isinstance(j,LevelPart):
                if j.slps[0].s in ["declare-fun","declare-const","assert","declare-sort","define-fun","define-const","check-sat"]: #Includes unsupported defines too; assumes if one of these used we're done setting stuff
                    return i
            i += 1
        return i


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
def CREATE(term1,term2):
    return a2("Create",term1,term2)#LevelPart("Create ("+term1.s+") ("+term2.s+")",1)
def ADDRESS(term1):
    return a1("Address",term1)#LevelPart("Address ("+term1.s+")",1)
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
    return a1("NOT",term1)#LevelPart("not ("+term1.s+")",1)
def QUOT(term1):
    return a1("quot",term1)#LevelPart("quot ("+term1.s+")",1)
def IFF(term1, term2):
    return AND(IMPL(term1,term2),IMPL(term2,term1))
#SHORTHANDS
def DB(term1,term2):
    return EQZ(ALIGN(term1),ALIGN(term2))
def DELTA(term1,term2):
    return EQZ(BLOCK(term1),BLOCK(term2))
def DELTA0(term1,term2):
    def neq0(t):
        return NOT(EQZ(t,Token("0")))
    return AND(DELTA(term1,term2),AND(neq0(term1),neq1(term2)))
#COMMANDS
def DECLARE_FUN(symbol, in_sorts, out_sort):
    return a3("declare-fun",Token(symbol),LevelPart(" ".join(in_sorts),1),Token(out_sort))
def DECLARE_CONST(symbol,sort):
    return a2("declare-const",Token(symbol),Token(sort))

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

def Amod(term):
    return AND(LEQ(0,ALIGN(term)), LEQ(ALIGN(term),ADD(Token("s"),NEG(Token("1")))))

def Ain(term):
    return AND(LEQ(Token("0"),ADDRESS(p)),LEQ(ADDRESS(p),Token("A")))

def Ao(term):
    return EQZ(OFFSET(term),ADD(PROD(Token("s"),QUOT(term)),ALIGN(term))) 

def Aleq(term):
    p = term.slps[1]
    q = term.slps[2]
    return IMPL(DELTA0(p,q),IFF(LEQP(p,q),LEQ(OFFSET(p),OFFSET(q))))

def Amin(term):
    p = term.slps[1]
    q = term.slps[2]
    return IMPL(AND(DELTA0(p,q),DB(p,q)),EQZ(PROD(Token("s"),MINP(p,q)),MIN(OFFSET(p),OFFSET(q))))

def Aplus(term):
    p = term.slps[1]
    i = term.slps[2]
    return IMPL(AND(NOT(EQZ(ADDRESS(p),Token("0"))),RANGE(p,i)),EQZ(OFFSET(ADDP(p,i)),ADD(OFFSET(p),PROD(Token("s"),i))))

def Adelt(term):
    p = term.slps[1]
    i = term.slps[2]
    return IMPL(AND(NOT(EQZ(ADDRESS(p),Token("0"))),RANGE(p,i)),DELTA(ADDP(p,i),p))

def Aa(term):
    l = term.slps[1]
    a = term.slps[2]
    return IMPL(AND(LEQ(token("0"),a),LEQ(a,token("A"))),EQP(ADDRESS(CREATE(l,a)),a)) 

def Ab(term):
    l = term.slps[1]
    a = term.slps[2]
    return IMPL(AND(LEQ(token("0"),a),LEQ(a,token("A"))),EQP(BLOCK(CREATE(l,a)),l)) 

if __name__ == "__main__":
    # Readlines of file
    filename = sys.argv[1]
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

    keywords = set(["declare-fun", "assert", "let", "ite", "check-sat", "exit"])

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
    functions["Base"] = (["Pointer"], "Int")
    functions["Align"] = (["Pointer"], "Int")
    functions["+p"] = (["Pointer","Int"],"Pointer") # ASSERT 
    functions["-p"] = (["Pointer","Pointer"],"Int") # ASSERT
    functions["<=p"] = (["Pointer","Pointer"],"Bool")
    functions["Create"] = (["Int","Int"],"Pointer") #Is (.,.)
    functions["Address"] = (["Pointer"], "Int") # Is composite, Base(Block(.))+Offset(.)
    functions["=p"] = (["Pointer","Pointer"],"Bool")  # From Core
    final_fxns = parseTree.setStates(functions, sorts, keywords)

    # assign each expression a type based on its prestate and its elements' states
    parseTree.assignSorts(sorts, keywords)

    # The transformation transform formula to formula; should only affect assertions; thus
    allAsserts = parseTree.findAllTermsSatisfying(lambda t: isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="assert"))
    for asrt in allAsserts:
        # find all instances of certain terms in formulas
        allPointers = asrt.findAllTermsSatisfying(lambda t : ("sort"in dir(t))and(t.sort=="Pointer"))
        allLEQPs = asrt.findAllTermsSatisfying(lambda t : ("sort"in dir(t))and isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="<=p"))
        allSUMPs = asrt.findAllTermsSatisfying(lambda t : ("sort"in dir(t))and isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="+p"))
        allMINPs = asrt.findAllTermsSatisfying(lambda t : ("sort"in dir(t))and isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="-p"))
        allCREATEs = asrt.findAllTermsSatisfying(lambda t : ("sort"in dir(t))and isinstance(t,LevelPart)and(len(t.slps)>0)and(t.slps[0].s=="Create"))
       
        # Instantiate all axioms
        F = asrt.slps[1]
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
        asrt.slps[1] = recon
    # We Must Introduce uninterpreted function quot: Pointer->Int, and the integers s and A
    index = parseTree.firstDeclare()
    parseTree.slps = parseTree.slps[:index] + [
        DECLARE_FUN("quot",["Pointer"],"Int"),
        DECLARE_CONST("s","Int"),
        DECLARE_CONST("A","Int")
        ] + parseTree.slps[index:]

    # NOTE that the recon trees are very simplistic and lack features like sorts; the whole pipeline should be reran over the output if sorts etc. are redesired

    # convert back into smtlib based on endpoints' values
    smtlib = parseTree.toSMTLIB()
    
    pdb.set_trace()
