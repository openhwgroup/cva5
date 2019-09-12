/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
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
 *             Eric Matthews <ematthew@sfu.ca>
 */

#ifndef SIMMEM_H
#define SIMMEM_H
#include <stdlib.h>
#include <iostream>
#include <fstream>

class SimMem {
public:
  SimMem(std::ifstream& program, uint32_t mem_size);
  ~SimMem();
  void write (uint32_t addr, uint32_t data, uint32_t be);
  uint32_t read (uint32_t addr);
private:
  uint32_t mem_size;
  uint32_t *memory;
  uint32_t address_mask;
};
#endif
