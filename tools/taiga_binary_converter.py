#
#  Copyright © 2017 Eric Matthews,  Lesley Shannon
# 
#  Licensed under the Apache License, Version 2.0 (the "License");
#  you may not use this file except in compliance with the License.
#  You may obtain a copy of the License at
# 
#  http://www.apache.org/licenses/LICENSE-2.0
# 
#  Unless required by applicable law or agreed to in writing, software
#  distributed under the License is distributed on an "AS IS" BASIS,
#  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#  See the License for the specific language governing permissions and
#  limitations under the License.
# 
#  Initial code developed under the supervision of Dr. Lesley Shannon,
#  Reconfigurable Computing Lab, Simon Fraser University.
# 
#  Author(s):
#             Eric Matthews <ematthew@sfu.ca>
#

import argparse
import re
import sys
import subprocess
import tempfile

def stringByteSwap(s):
    pairs = [s[i:i+2] for i in range(0, len(s), 2)]
    return ''.join(pairs[::-1])

parser = argparse.ArgumentParser(description='Converts binary into init files for simulation and BRAMs')

#objdump prefix
parser.add_argument('toolPrefix', help='the prefix for objdump')

#base adder required
parser.add_argument('baseAddr', help='the base address')
#ram size required
parser.add_argument('ramSize', help='the ram size')

# input file required
parser.add_argument('inputFile', help='The executable')

# output file names
parser.add_argument('outputFile', help='The ram init file')
parser.add_argument('simFile', help='The sim data file')

parser.add_argument('--quiet', '-q', help='Suppresses diagnostic output ', action="store_true")

args = parser.parse_args()

# open input file
subprocess.run([args.toolPrefix + 'objdump', '-Dzs', args.inputFile], stdout=open(args.inputFile + '.dumpDzs', "w"))
subprocess.run([args.toolPrefix + 'objdump', '-d', args.inputFile], stdout=open(args.inputFile + '.dumpd', "w"))


try:
    program_input = open(args.inputFile + '.dumpDzs', 'r')
    opcode_input = open(args.inputFile + '.dumpd', 'r')
except IOError:
    print('Could not open files: ', args.inputFile + '.dumpDzs ', args.inputFile + '.dumpd')
    sys.exit()

    program_output = args.inputFile + '.bin'
    sim_output = args.inputFile + '.sim'
    
if (args.outputFile) :
    program_output = args.outputFile
if (args.simFile) :
    sim_output = args.simFile
    

# open output file
try:
    program_output = open(program_output, 'w')
    sim_output = open(sim_output, 'w')
except IOError:
    print('Could not create files: ', program_output, sim_output)
    sys.exit()
    
print('array size ', int(int(args.ramSize)/4))

ramData = ['00000000'] * int((int(args.ramSize)/4));

lineRegex = re.compile(r'\s+')
instLineRegex = re.compile(r'\s+|:\s+')
dataLineRegex = re.compile(r' [a-f0-9]{8}\s+')

hexRegex = re.compile(r'[a-f0-9]{8}')

#parses the block output format
for line in program_input:
    lineContents = lineRegex.split(line)

    if (dataLineRegex.match(line) != None) :
        index = int((int(lineContents[1],16) - int(args.baseAddr,16))/4)

        for entry in lineContents[2:]: #skip address
            if (hexRegex.match(entry)) :
                ramData[index] = stringByteSwap(entry)
                index+=1

program_output.write('\n'.join(str(line) for line in ramData))

#overwrite instruction entries with instruction info
#<ins hex> <opcode> <instruction details>...
for line in opcode_input:
    lineContents = instLineRegex.split(line)
    if (hexRegex.match(lineContents[0])) :
        index = int((int(lineContents[0],16) - int(args.baseAddr,16))/4)
    
        for entry in lineContents[1:]: #skip address
                ramData[index] = lineContents[1] + ' ' + ' '.join(lineContents[2:])

sim_output.write(' --\n'.join(str(line) for line in ramData))
sim_output.write(' --')

print('Done')
    
    
