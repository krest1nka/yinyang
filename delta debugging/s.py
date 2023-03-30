import sys
import subprocess

from yinyang.src.parsing.Parse import parse_file
from ASTtoAPI import ASTtoAPI

args = sys.argv
seed = parse_file(args[1])

# CLI output
echo_cli = subprocess.Popen(['echo', str(seed)], stdout=subprocess.PIPE)
z3_cli = subprocess.Popen(['z3', '-in'], stdin=echo_cli.stdout, stdout=subprocess.PIPE)
echo_cli.stdout.close()
output = z3_cli.communicate()[0]
cli_result = ""
if "unsat" in str(output):
    cli_result = "unsat"
elif "sat" in str(output):
    cli_result = "sat"

# API output
solver = ASTtoAPI.get_solver(seed)
api_result = str(solver.check())

# Check if outcomes differ
if cli_result != api_result:
    exit(0)
exit(1)
