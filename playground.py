import os
import subprocess
import sys
import signal
import inspect
from pathlib import Path

import z3

from ASTtoAPI import ASTtoAPI, ASTtoAPIException

path = Path(__file__)
rootpath = str(path.parent.absolute().parent)
sys.path.append(rootpath)

current_dir = os.getcwd()

from yinyang.src.base.ArgumentParser import build_opfuzz_parser
from yinyang.src.base.Exitcodes import ERR_USAGE

from yinyang.src.core.Fuzzer import Fuzzer

from yinyang.config.OpfuzzHelptext import (
    usage
)

# parse arguments from command line
parser = build_opfuzz_parser(current_dir, usage)
args = parser.parse_args()

temp_seeds = []
for path in args.PATH_TO_SEEDS:
    if not os.path.exists(path):
        print('error: folder/file "%s" does not exist' % path,
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
#
# # check API and CLI outputs
#
# logs = open(args.scratchfolder + "/logs.txt", "a")
#
# for mutant in mutants:
#     echo_cli = subprocess.Popen(['echo', str(mutant)], stdout=subprocess.PIPE)
#     z3_cli = subprocess.Popen(['z3', '-in'], stdin=echo_cli.stdout, stdout=subprocess.PIPE)
#     echo_cli.stdout.close()
#     output = z3_cli.communicate()[0]
#     cli_result = ""
#     if "unsat" in str(output):
#         cli_result = "unsat"
#     elif "sat" in str(output):
#         cli_result = "sat"
#
#     try:
#         solver = ASTtoAPI.get_solver(mutant)
#         api_result = str(solver.check())
#     except ASTtoAPIException as error:
#         logs.write(str(error) + "\n")
#         continue
#
#     if cli_result != api_result:
#         logs.write("----------------------------\n")
#         logs.write(mutant)
#         logs.write("\nAPI: " + api_result + "\nCLI: " + cli_result + "\n")
#         logs.write("----------------------------\n")
