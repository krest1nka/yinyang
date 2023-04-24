For fuzzing:

-s <path to temp folder to dump mutants> -l <path for log files> -L 1000000 -i 100 -b <path to bug folder> "z3 model_validate=true;z3 model_validate=true" <absolute path to the seeds>

For delta debugging: 

**It is important to alter s.py path in script.sh**

picireny --input phi1.smt2 --test script.sh -g SMTLIBv2.g4 --start start