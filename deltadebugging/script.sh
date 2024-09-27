#!/bin/bash

# execute the Python script and save the exit code
python3 /Users/kristina/Desktop/yinyang/deltadebugging/s.py $1
exit_code=$?

# exit the Bash script with the same exit code as the Python script
exit $exit_code