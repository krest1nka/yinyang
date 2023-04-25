import sys
import subprocess
import tempfile

from ASTtoAPI import ASTtoAPI, ASTtoAPIException
from yinyang.src.parsing.Parse import parse_file

args = sys.argv
file = open(args[1] + "/mutant.smt2", "w")
file.write(args[2])
file.close()
mutant = parse_file(args[1] + "/mutant.smt2")
mutant = mutant[0]

logs = open(args[1] + "/logs.txt", "a")
elogs = open(args[1] + "/elogs.txt", "a")

try:
    solver = ASTtoAPI.get_solver(mutant)
    api_result = str(solver.check())
    print(api_result)
except ASTtoAPIException as error:
    logs.write("----------------------------\n")
    logs.write(str(mutant))
    logs.write("\n" + str(error) + "\n")
    logs.write("----------------------------\n")
    print("exception")
except Exception as e:
    elogs.write("----------------------------\n")
    elogs.write(str(mutant))
    elogs.write("\n" + str(e) + "\n")
    elogs.write("----------------------------\n")
    print("exception")