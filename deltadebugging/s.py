import sys
import subprocess

sys.path.append("/Users/kristina/Desktop/yinyang/")


from ASTtoAPI import ASTtoAPI
from yinyang.src.parsing.Parse import parse_file

args = sys.argv
seed = parse_file(args[1])
print(seed[0])
# CLI output
echo_cli = subprocess.Popen(['echo', str(seed[0])], stdout=subprocess.PIPE)
z3_cli = subprocess.Popen(['z3', '-in'], stdin=echo_cli.stdout, stdout=subprocess.PIPE)
echo_cli.stdout.close()
output = z3_cli.communicate()[0]
if str(output) == "b''":
    exit(1)
cli_result = ""
if "unsat" in str(output):
    cli_result = "unsat"
elif "sat" in str(output):
    cli_result = "sat"

# API output
solver = ASTtoAPI.get_solver(seed[0])
api_result = str(solver.check())

# Check if outcomes differ
if (cli_result == "sat" and api_result == "unsat") or (cli_result == "unsat" and api_result == "sat"):
    exit(0)
exit(1)
