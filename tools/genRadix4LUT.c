//This file is used to generate the table to look up the quotient digit for radix 4 fractional division

#include <stdio.h> //The binary print specifier 'b' is a new C23 feature
#include <limits.h>

int main() {

    //Table contents from "Digital Arithmetic" by Ercegovac and Lang
    int radix4Table[6][8] = {
        {INT_MIN, INT_MIN, INT_MIN, INT_MIN, INT_MIN, INT_MIN, INT_MIN, INT_MIN},
        {-13, -15, -16, -18, -20, -20, -22, -24},
        {-4, -6, -6, -6, -8, -8, -8, -8},
        {4, 4, 4, 4, 6, 6, 8, 8},
        {12, 14, 15, 16, 18, 20, 20, 24},
        {INT_MAX, INT_MAX, INT_MAX, INT_MAX, INT_MAX, INT_MAX, INT_MAX, INT_MAX}
    };

    char encodingTable[5][8] = {"NEG_TWO", "NEG_ONE", "ZERO", "POS_ONE", "POS_TWO"};

    for (int d = 0; d < 8; d++) {
        for (int combined = -44; combined <= 42; combined++) {
            for (int i = 0; i < 5; i++) {
                if (combined >= radix4Table[i][d] && combined < radix4Table[i+1][d]) {
                    printf("10'b%03b%07b: q = %s;\n", d, combined & 0x7F, encodingTable[i]);
                    break;
                }
            }
        }
    }
    
    return 0;
}