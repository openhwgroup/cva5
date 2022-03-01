#
#  Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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
print(args.inputFile)
subprocess.run([args.toolPrefix + 'objcopy', '--gap-fill=0x00', '-O',  'binary', args.inputFile, args.inputFile + '.rawbinary'])
subprocess.run([args.toolPrefix + 'objdump', '-fd', '--prefix-addresses', args.inputFile], stdout=open(args.inputFile + '.dissasembled', "w"))


try:
    program_input = open(args.inputFile + '.rawbinary', 'rb')
    opcode_input = open(args.inputFile + '.dissasembled', 'r')
except IOError:
    print('Could not open files: ', args.inputFile + '.raw ', args.inputFile + '.dissasembled')
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

#Initialize with zero
ramData = ['00000000'] * int((int(args.ramSize)/4));

instLineRegex = re.compile(r'\s+')
isInstLine = re.compile(r'[a-f0-9]{8}\s+<\S+') #pattern hexaddress <function name and offset> instruction
#parses the block output format
addressRegex = re.compile(r'0x[a-f0-9]{8}')
hexRegex = re.compile(r'[a-f0-9]{8}')

#Find start address and lowest address in dissasembly file
index = 0
lowestAddress = sys.maxsize
for line in opcode_input:
	if (isInstLine.match(line)) :
		addressMatch = hexRegex.match(line)
		if (int(addressMatch[0],16) < lowestAddress) :
			lowestAddress = int(addressMatch[0],16)
			index = int(lowestAddress/4) -  int(int(args.baseAddr,16)/4)
	if (line.find('start address') != -1) :
		addressMatch = addressRegex.search(line)
		print('start address: ', addressMatch[0])
		
#Reads binary 4 bytes at a time and converts to Verilog readmemh format
word = program_input.read(4)
while word != b"":
	ramData[index] = stringByteSwap(word.hex())
	index+=1
	word = program_input.read(4)
		
program_output.write('\n'.join(str(line) for line in ramData))

#append instruction details to data
opcode_input.seek(0)
for line in opcode_input:
    if (isInstLine.match(line)) :
        lineContents = list(filter(None, instLineRegex.split(line))) #split line and remove empty strings
        index = int((int(lineContents[0],16) - int(args.baseAddr,16))/4)
        ramData[index] +=  ' ' + ' '.join(lineContents[1:])

sim_output.write(' --\n'.join(str(line) for line in ramData))
sim_output.write(' --')

print('Done')
    
    
