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
        return self.s

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
    final_fxns = parseTree.setStates(functions, sorts, keywords)

    # assign each expression a type based on its prestate and its elements' states
    parseTree.assignSorts(sorts, keywords)

    # TODO implement the transformations here; but do this last

    # convert back into smtlib based on endpoints' values
    smtlib = parseTree.toSMTLIB()
    
    pdb.set_trace()
