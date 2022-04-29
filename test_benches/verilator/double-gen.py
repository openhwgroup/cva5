import quantumrandom as qr
import sys

output = sys.argv[1];
test_num = sys.argv[2];
precision = sys.argv[3];

file = open(output, 'w')

if(precision == 'D'):
    for i in range(int(test_num)):
        inputs = qr.get_data(data_type='hex16', array_length=2, block_size=8)
        content = inputs[0] + " " + inputs[1] + "\n"
        file.write(content)
elif(precision == S):
    for i in range(int(test_num)):
        inputs = qr.get_data(data_type='hex16', array_length=2, block_size=4)
        content = inputs[0] + " " + inputs[1] + "\n"
        file.write(content)
else:
    sys.exit(-1)

file.close()



