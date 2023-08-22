import os
import subprocess
import sys
import threading
import concurrent.futures

args = sys.argv

for bug in os.listdir(args[1]):
    try:
        subprocess.run(['picireny', '--input', args[1] + '/' + bug, '--test',
                        '/Users/kristina/Desktop/yinyang/deltadebugging/script.sh', '-g',
                        '/Users/kristina/Desktop/yinyang/deltadebugging/SMTLIBv2.g4', '--start', 'start'],
                       stdout=subprocess.PIPE, timeout=900)
    except Exception as e:
        print(e)

# for thread in threads:
#     thread.join(600)

# threads = []
# for bug in os.listdir(args[1]):
#     thread = threading.Thread(target=run_subprocess, args=(bug,))
#     threads.append(thread)
#     thread.start()
#
# for thread in threads:
#     thread.join(600)

