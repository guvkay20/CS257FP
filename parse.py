import pdb
import sys

class Token:
    def __init__ (self, s):
        self.s = s
    def __repr__(self):
        return self.s

class LevelPart:
    def __init__(self, s, level):
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

    #def __repr__(self):
    #    return "LevelPart at Level "+str(self.level)" with the following Sub-Leve

if __name__ == "__main__":
    filename = sys.argv[1]
    
    with open(filename) as f:
        lines = list()
        line = f.readline()
        while line:
            lines.append(line)
            line = f.readline()

    clines = " ".join(lines)

    pdb.set_trace()
    parseTree = LevelPart(clines, 0)


    pdb.set_trace()
