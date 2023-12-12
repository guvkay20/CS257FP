python3 parse.py $1 tmp.smt2 8 512 "junk"
../z3/build/z3 -smt2 -st tmp.smt2
