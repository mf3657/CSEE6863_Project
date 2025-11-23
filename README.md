# CSEE 6863 HARDWARE VERIFICATION PROJECT

8 bit RISC Processor Verification Project
Hardware group #1

	- Michael John Flynn: mf3657
	- Felipe Andrade: fga2116

The goal of this project is to verify the functionality, and shortcomings, of an open source 8-bit microprocessor created by NayanaBannur, aswell as refactor and clean up the verilog.

Original Repo can be found [here!](https://github.com/NayanaBannur/8-bit-RISC-Processor)

## Methodology

The 8 bit microprocessor includes a RISC architecture with 5 pipeline stages and a basic instruction set including 18 instructions, with an 8x8-bit register file. The 5 pipeline stages include instruction fetch, instruction decode, execution, memory access, and store results.

To undertake this project we will utilise Cadence JasperGold verify the funcitonality of the core using various asserts and properties.

---

## <span style="color: seagreen;">Processor Breakdown</span>


### Module Breakdown

```bash
processor_top
    |-instr_and_data_mem # the in and out, basically the bus
                         # holds 1024 instruction lines (16 bit instructions)
                         # holds 256 8bit values
    |-register_file # 8x8bit memory
    |-processor_core # The whole damn thing
```

### Instruction Decoding
```bash
ALU_OPERATIONS (ADD, SUB, AND, OR, ...)
15         11 10      8 7    6 5     4 3    2 1       0
+------------+---------+------+-------+------+--------+
|   opcode   | res_reg | XXX  | op2_r | XXX  | op1_r  |
+------------+---------+------+-------+------+--------+
opcode → ALU operation
res_reg → destination register
op2_r → second operand register
op1_r → first operand register
X = unused/don’t care


LOAD_INSTRUCTION
15         11 10      8 7                                  0
+------------+---------+-----------------------------------+
|   opcode   | res_reg |         immediate addr            |
+------------+---------+-----------------------------------+
load from instruction[7:0] into register instruction[10:8]


STORE_INSTRUCTION
15         11 10                                  3 2       0
+------------+-------------------------------------+--------+
|   opcode   |       store memory address          | op1_r  |
+------------+-------------------------------------+--------+
store register op1_r -> memory address [10:3]
no destination register


BRANCH_INSTRUCTION
15         11 10                                       0
+------------+-----------------------------------------+
|   opcode   |              branch target              |
+------------+-----------------------------------------+
branch_addr is 10 bits -> 1024-entry address space

```
```verilog
	always@(instruction)
		begin
		    // ------------ Opcode ------------
            opcode       <= instruction[15:11];

            // ------------ Register fields ------------
            op1_addr     <= instruction[2:0];
            op2_addr     <= instruction[6:4];
            res_addr     <= instruction[10:8];

            // ------------ Memory Addresses ------------
            ld_mem_addr  <= instruction[7:0];     // LOAD only
            st_mem_addr  <= instruction[10:3];    // STORE only

            // ------------ Branch Target ------------
            branch_addr  <= instruction[9:0];
		end
```

### Using memory data

- passed from instr_and_data_mem as *datamem_rd_data* and assigned to *datamem_wr_data* when *load_mem_data* is high.
- *datamem_wr_data* is used as follows when certain bypasses are enabled:
```verilog
// line ~383
assign op1_data = bypass_op1_dcd_stage  ? datamem_wr_data : op1_rd_data;
assign op2_data = bypass_op2_dcd_stage  ? datamem_wr_data : op2_rd_data;

// line ~470
assign operand1 = bypass_op1_ex_stage  ? datamem_wr_data : op1_data_reg;
assign operand2 = bypass_op2_ex_stage  ? datamem_wr_data : op2_data_reg;
```
- datamem_wr_data is also used to store values in the memory in the instr_and_data_mem module at the data_wr_addr index.

### processor_core signals
#### Inputs

- **clk, rest:**
  - self explanatory
- **<span style="color: green;">[7:0]</span> op1_rd_data, op2_rd_data:** 
  - assigned to op1/2_data unless bypass_op1/2_dcd_stage is high
  - comes from rd_data1 and rd_data2 within module register_file i.e. the 8x8bit memory
- **<span style="color: green;">[7:0]</span> datamem_rd_data:**
  - assigned to datamem_wr_data when load_mem_data is high
  - comes from module instr_and_data_mem
- **<span style="color: green;">[15:0]</span> instr_mem_out:**
  - what?

#### Outputs

- **<span style="color: green;">[2:0]</span> op1_addr, op2_addr:**
  - assigned as rd_addr1/2 within the register_file 8 bit memory module.
  - Used to access the 8*8bit reg_file for reading two 8 words.
- **<span style="color: green;">[9:0]</span> prog_ctr:**
  - used to fetch instructions from the instr_and_data_mem module
  - set as follows in the processor core
    ```verilog
      always @(posedge clk)
	    if (reset == 1'b1)
	       prog_ctr <= #1 10'b1;
	    else
	       begin
	    	if (branch_taken_reg == 1) //update in store res stage
	    		begin                             
	    		prog_ctr <= #1 nxt_prog_ctr_r2;
	    		set_invalidate_instruction <= #1 1'b1;
	    		end
	    	else
	    		begin
	    		prog_ctr <= #1 prog_ctr + 1'b1;
	    		set_invalidate_instruction <= #1 1'b0;
	    		end

	       end
    ```
- **<span style="color: green;">[7:0]</span> datamem_wr_data:**
  - *datamem_rd_data* assigned to *datamem_wr_data* when *load_mem_data* is high, else *data_out_reg* (*data_out*).
    ```verilog
      assign datamem_wr_data = load_mem_data ? datamem_rd_data : data_out_reg;
      //where
      assign data_out = (add_op_true_reg || store_true_reg) ? alu_data_out :
       (lgcl_or_bitwse_T_reg ? logical_data_out : shift_data_out);
    ```
  - Essentially takes in data from memory or takes the alu, logical, or shift data.
  - to be used as described above in #[Using Memory Data] 
- **<span style="color: green;">[7:0]</span> data_rd_addr:**
  - Used to address the data_mem (256 words) from instr_and_data_mem.
  - Set with reg *ld_mem_addr_reg* which is set by *ld_mem_addr* set by instruction<span style="color: green;">[7:0]</span> as described above in #[Instruction Decoding]
- **<span style="color: green;">[7:0]</span> data_wr_addr:**
  - Used to store datamem_wr_data into memory in the instr_and_data_mem module
    ```verilog
    data_wr_addr <= #1 store_true_reg ? st_mem_addr_reg : ld_mem_addr_reg; 
    ```
- **<span style="color: green;">[7:0]</span> operation_result:**
  - Essentially an internal *data_out* or *data_out_reg* that's accesible by the processor_top module.
- **<span style="color: green;">[2:0]</span> destination_reg_addr:**
  - Used in the setting of bypass logic for the decode and execute units.
  - Set with res_addr_reg.
  - wr_addr in the 8x8bit register.
- **store_to_mem:**
  - Used to store words in 256 byte memory in instr_and_data_mem.
  - Set in processor_core as follows:
    ```verilog
    assign  store_to_mem = (store_to_mem_ex && !invalidate_instr);
    // where
    store_to_mem_ex <= #1 store_true_reg;
    //where
    store_true_reg <= #1 store_true;
    //where
    case(opcode)
        ........
    // OP_STORE:
			5'h09:	store_true <= 1'b1;
        ........
    endcase
    ```
- **reg_wr_en:**
  - Used in the setting of bypass logic for the decode and execute units. Similar to *destination_reg_addr*.
  - wr_en in 8x8bit register.
  - Set in processor core as follows:
    ```verilog
    assign reg_wr_en_ex <= #1 write_to_regfile_reg;
    // where
    reg_wr_en_ex <= #1 write_to_regfile_reg;
    // where
    write_to_regfile_reg <= #1 write_to_regfile;
    // where
    case (opcode)
    /* many many opcodes set */ write_to_regfile /* which is, by default, */ 1'b0
