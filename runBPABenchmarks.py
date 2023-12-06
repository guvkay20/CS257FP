import sys
import os
from parse import convertFileTo
import subprocess
import pdb
import time

def getMarksList(marksRootDir="benchmarks/BPA/"):
    marks = list()
    for root,dirs,files in os.walk(marksRootDir):
        for f in files:
            if f[-5:]==".smt2":
                fpath = root+"/"+f
                marks.append(fpath)
    return marks

def convertAndRunMarks(marks):
    times = list()
    ttimes = list()
    tttimes = list()

    for mark in marks:
        tic = time.perf_counter()
        convertFileTo(mark,8,512,"tmp.smt2")
        x=subprocess.run(["Z3/z3/build/z3","-smt2","-st","tmp.smt2"], capture_output=True)
        toc = time.perf_counter()
        outs = str(x.stdout)
        assigns = outs.split("\\n")
        assigns = [assign.strip("()").split() for assign in assigns]
        assigns = {z[0]:z[1] for z in assigns if len(z)==2}
        _time = float(assigns[":time"])
        _ttime = float(assigns[":total-time"])
        times.append(_time)
        ttimes.append(_ttime)
        tttimes.append(toc-tic)
    avg_time = sum(times)/len(times)
    avg_ttime = sum(ttimes)/len(ttimes)
    avg_tttime = sum(tttimes)/len(tttimes)
    pdb.set_trace()

convertAndRunMarks(getMarksList())
