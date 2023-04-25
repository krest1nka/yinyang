import os
import subprocess
import sys

args = sys.argv

for bug in os.listdir(args[1]):
    result = subprocess.run(['picireny', '--input', bug, '--test', 'script', '-g', 'SMTLIBv2.g4', '--start', 'start'],
                            stdout=subprocess.PIPE)
    print(result.stdout.decode('utf-8'))
