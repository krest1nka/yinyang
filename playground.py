import os
import subprocess
import sys
import signal
import inspect
from pathlib import Path

import z3

from ASTtoAPI import ASTtoAPI

path = Path(__file__)
rootpath = str(path.parent.absolute().parent)
sys.path.append(rootpath)

current_dir = os.getcwd()

from yinyang.src.base.Driver import run_checks, create_scratch_folder, create_log_folder, create_bug_folder, get_seeds, \
    check_opfuzz
from yinyang.src.base.Error import raise_runtime_error
from yinyang.src.base.ArgumentParser import build_opfuzz_parser
from yinyang.src.base.Exitcodes import OK_BUGS, OK_NOBUGS
from yinyang.src.base.Exitcodes import ERR_USAGE, ERR_INTERNAL

from yinyang.src.core.Fuzzer import Fuzzer

from yinyang.config.OpfuzzHelptext import (
    usage,
    header,
    short_description,
    long_description,
    options,
)

# parse arguments from command line
parser = build_opfuzz_parser(current_dir, usage)
args = parser.parse_args()

temp_seeds = []
for path in args.PATH_TO_SEEDS:
    if not os.path.exists(path):
        print('error: folder/file "%s" does not exist' % (path),
              flush=True)
        exit(ERR_USAGE)
    if os.path.isfile(path):
        temp_seeds.append(path)
    elif os.path.isdir(path):
        for subdir, dirs, files in os.walk(path):
            for filename in files:
                filepath = subdir + os.sep + filename
                if filepath.endswith(".smt2"):
                    temp_seeds.append(filepath)
    else:
        print("error: %s is neither a file nor a directory", flush=True)
        exit(ERR_USAGE)
args.PATH_TO_SEEDS = temp_seeds


fuzzer = Fuzzer(args, "krest1nka")
fuzzer.run()
mutants = fuzzer.get_mutants()

#check API and CLI outputs

print("API output:")

solver = ASTtoAPI.get_solver(mutants[0])
print(solver.check())
if str(solver.check()) == "sat":
    print(solver.model())


echo_cli = subprocess.Popen(['echo', str(mutants[0])], stdout=subprocess.PIPE)
z3_cli = subprocess.Popen(['z3', '-in'], stdin=echo_cli.stdout, stdout=subprocess.PIPE)
echo_cli.stdout.close()
output = z3_cli.communicate()[0]

print("CLI output:")
print(output)
cli_result = ""
if "unsat" in str(output):
    cli_result = "unsat"
elif "sat" in str(output):
    cli_result = "sat"

print(cli_result == str(solver.check()))





