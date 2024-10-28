/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

function get_stack_adj_base(rlist : bits(5)) -> int = {
  if(xlen == 32) then
    match(rlist) {
        0b00100 => 16,
        0b00101 => 16,
        0b00110 => 16,
        0b00111 => 16,
        0b01000 => 32,
        0b01001 => 32,
        0b01010 => 32,
        0b01011 => 32,
        0b01100 => 48,
        0b01101 => 48,
        0b01110 => 48,
        0b01111 => 64,
        _ => internal_error(__FILE__, __LINE__, "Unsupported rlist: " ^ bits_str(rlist))
    }
  else {
    match(rlist) {
        0b00100 => 16,
        0b00101 => 16,
        0b00110 => 32,
        0b00111 => 32,
        0b01000 => 48,
        0b01001 => 48,
        0b01010 => 64,
        0b01011 => 64,
        0b01100 => 80,
        0b01101 => 80,
        0b01110 => 96,
        0b01111 => 112,
        _ => internal_error(__FILE__, __LINE__, "Unsupported rlist: " ^ bits_str(rlist))
    }
  }
}

mapping reg_list : bits(5) <-> string = {
  0b00000     <-> "",
  0b00001     <-> "",
  0b00010     <-> "",
  0b00011     <-> "",
  0b00100     <-> "ra",
  0b00101     <-> "ra, s0",
  0b00110     <-> "ra, s0-s1",
  0b00111     <-> "ra, s0-s2",
  0b01000     <-> "ra, s0-s3",
  0b01001     <-> "ra, s0-s4",
  0b01010     <-> "ra, s0-s5",
  0b01011     <-> "ra, s0-s6",
  0b01100     <-> "ra, s0-s7",
  0b01101     <-> "ra, s0-s8",
  0b01110     <-> "ra, s0-s9",
  0b01111     <-> "ra, s0-s11",
}

mapping rlist_to_int : bits(5) <-> int = {
  0b00000     <-> 0,
  0b00001     <-> 1,
  0b00010     <-> 2,
  0b00011     <-> 3,
  0b00100     <-> 4,
  0b00101     <-> 5,
  0b00110     <-> 6,
  0b00111     <-> 7,
  0b01000     <-> 8,
  0b01001     <-> 9,
  0b01010     <-> 10,
  0b01011     <-> 11,
  0b01100     <-> 12,
  0b01101     <-> 13,
  0b01110     <-> 14,
  0b01111     <-> 15,
}

mapping spimm_to_int : bits(2) <-> int = {
  0b00     <-> 0,
  0b01     <-> 1,
  0b10     <-> 2,
  0b11     <-> 3,
}

function zcmp_regmask(rlist : bits(5)) -> bits(32) = {
  //assert(rlist <= unsigned(15) & rlist >= unsigned(4), "Invalid rlist for zcmp_regmask");

  var mask : bits(32) = zeros();

  if(unsigned(rlist) >= unsigned(0b100)) then {
    mask = mask | zero_extend(0b10)
  };

  let rlist_num = rlist_to_int(rlist);

  foreach (i from 5 to rlist_num) {
    if(i >= 5) then {
      if( (i - 5) < 2 ) then
        mask = mask | zero_extend(0b1 << 8 + (i - 5))
      else {
        mask = mask | zero_extend(0b1 << 16 + (i - 7))
      };
    };
  };

  if(rlist == zero_extend(0xf)) then
    mask = mask | zero_extend(0b1 << 27);

  mask
}

enum clause extension = Ext_Zcmp
function clause extensionEnabled(Ext_Zcmp) = extensionEnabled(Ext_Zca) & extensionEnabled(Ext_Zcd) == false & (xlen == 32 | xlen == 64)

union clause ast = CM_PUSH : (bits(5), bits(2))

mapping clause encdec_compressed = CM_PUSH(rlist, spimm)   if extensionEnabled(Ext_Zcmp)
  <-> 0b001 @ 0b11000 @ rlist : bits(5) @ spimm : bits(2) @ 0b10    if extensionEnabled(Ext_Zcmp)

function clause execute (CM_PUSH(rlist, spimm)) = {
  let addr = X(sp);
  let stack_adj_base = to_bits(xlen, get_stack_adj_base(rlist));
  let spimm_int = spimm_to_int(spimm);
  let stack_adj = stack_adj_base + spimm_int;
  let new_sp = addr - zero_extend(stack_adj);
  foreach (i from 0 to 31) {
    if ((zcmp_regmask(rlist) & zero_extend(0b1 << i)) != zeros()) then {
        match ext_data_get_addr(sp, zeros(), Write(Data), xlen / 8) {
          Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); RETIRE_FAIL },
          Ext_DataAddr_OK(vaddr) =>
            if   check_misaligned(vaddr, width)
            then { handle_mem_exception(vaddr, E_SAMO_Addr_Align()); RETIRE_FAIL }
            else match translateAddr(vaddr, Write(Data)) {
              TR_Failure(e, _)    => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
              TR_Address(paddr, _) => {
                let eares = mem_write_ea(paddr, width_bytes, aq, rl, false);
                match (eares) {
                  MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
                  MemValue(_) => {
                    let reg_val = X(zero_extend(i));
                    match mem_write_value(paddr, width_bytes, rs2_val[width_bytes * 8 - 1 .. 0], aq, rl, false) {
                      MemValue(true)  => RETIRE_SUCCESS,
                      MemValue(false) => internal_error(__FILE__, __LINE__, "store got false from mem_write_value"),
                      MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL }
                    }
                  }
                }
              }
            }

        }
    }
  };

  X(sp) = new_sp;
  RETIRE_SUCCESS
}

mapping clause assembly = CM_PUSH(rlist, spimm)
  <-> "cm.push" ^ spc() ^ reg_list(rlist) ^ sep()
