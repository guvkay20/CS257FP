# CS257 Final Project

This repository contains the program files used for CS257 Final Project of Kaya Guvendi and Ethan Bogle.

benchmarks/ directory contains the two theories' benchmarks.

BPA.smt and BPA+.smt define the syntax of their respective theories.

convertAndRun.sh and convertAndRunPlus.sh are Bash files that can be called to translate a BPA/BPA+ SMT-LIB file into QF\_UFLIA in SMT-LIB and solve them with Z3. Do note that Z3 executable's path must be provided within, explaining why separate "Ethan" variants are maintained. Call with path to target file as argument.

parse.py performs translations from BPA/BPA+ into QF\_UFLIA. Several calling options exist, refer to the file.

runBPABenchmarks.py runs the benchmarks as described in the paper, recording results into results.json. Call without arguments.

processOut.py transforms results.json's result into a series of csv files in results. Call without arguments.
