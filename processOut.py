import json
import numpy as np
import pdb

res = json.load(open("results.json"))
res = (res['unoptimized results'],res['optimized results'])
res = (res[0]['raw results'],res[1]['raw results'])
res = (np.array(res[0]).T,np.array(res[1]).T)
diffs = res[1] - res[0]
def save(arr,name):
    np.savetxt(name,arr,delimiter=',')
save(res[0],"results/unoptimized.csv")
save(res[1],"results/optimized.csv")
save(diffs,"results/differences.csv")

with open("results/unoptimized.csv") as a:
    with open("results/optimized.csv") as b:
        with open("results/differences.csv") as c:
            with open("results/merged.csv","w") as f:
                f.write("BPA Solve Time,BPA Z3 Total Time,BPA Total Time,BPA Z3 Memory Use,,BPA+ Solve Time,BPA+ Z3 Total Time,BPA+ Total Time,BPA+ Z3 Memory Use,,Solve Time Difference,Z3 Total Time Difference,Total Time Difference,Z3 Memory Use Difference\n")
                for i in range(diffs.shape[0]):
                    f.write(a.readline()[:-1]+", ,"+b.readline()[:-1]+", ,"+c.readline())

pdb.set_trace()
