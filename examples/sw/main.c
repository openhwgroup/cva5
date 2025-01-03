/*
 * Copyright © 2024 Chris Keilbart
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

#include <stdio.h>
#include <stdatomic.h>

//Needed to "sleep" for the correct duration
#define MHZ 100
static void usleep(unsigned usecs) {
    unsigned int counter = usecs * MHZ;
    counter /= 2; //Two instructions per loop body; decrement and compare
    do {
        atomic_thread_fence(memory_order_relaxed); //This prevents the loop from being optimized away but doesn't do anything
    } while (counter-- > 0); //Assumes that a tight add and branch loop can be sustained at 1 IPC
}

//Example program to run on CVA5, assumes running at 100 MHz
//The accompanying mem.mif file is the corresponding executable in hexadecimal format
//It was compiled targetting RV32IM with a 4KB memory size, and a uart_putc function supporting the AXI UART Lite AMD IP

int main(void) {

    while(1) {
        puts("Hello World!");
        usleep(1000*1000);
    }

    return 0;
}
