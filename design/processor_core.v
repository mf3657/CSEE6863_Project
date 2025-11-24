module processor_core (clk, reset, 
					   op1_rd_data, op2_rd_data, 
					   instr_mem_out,
					   op1_addr, op2_addr,
					   prog_ctr, store_to_mem, 
					   reg_wr_en, 
					   data_rd_addr, data_wr_addr, 
					   datamem_rd_data, datamem_wr_data, 
					   operation_result, 
					   destination_reg_addr);               

//***************************
//	INPUTS
//****************************
	input wire	clk, reset;

	input wire [7:0]  op1_rd_data, op2_rd_data;
	input wire [7:0]  datamem_rd_data;
	input wire [15:0] instr_mem_out;

//***************************
//	OUTPUTS (and associated)
//****************************
	output reg [2:0] op1_addr, op2_addr;
           reg [2:0] op1_addr_reg , op2_addr_reg;

	output reg [9:0] prog_ctr;
           reg [9:0] branch_addr, nxt_prog_ctr;

	output reg [7:0] data_rd_addr, data_wr_addr;
	output reg [7:0] operation_result;
    
	output reg [2:0] destination_reg_addr;

    output wire [7:0] datamem_wr_data;
           wire [7:0] data_out;
	
    output wire  store_to_mem, reg_wr_en;
	       wire	 invalidate_instr;

//**********************************
//	INTERNAL SIGNALS AND REGISTERS
//**********************************
	wire [7:0] operand1, operand2;
	wire [7:0] op1_data, op2_data, branch_taken;
	wire		carry_out,save_carry_flag;
	wire		gt_flag_ex, lt_flag_ex, eq_flag_ex;
	wire		gt_flag_true, lt_flag_true, eq_flag_true;
	wire		carry_flag_true;

	reg [9:0] branch_addr,prog_ctr,nxt_prog_ctr;
	reg [9:0] nxt_prog_ctr_reg, nxt_prog_ctr_r2;
	reg [7:0] op1_data_reg, op2_data_reg; 
	reg [15:0] instruction;
	reg [4:0] opcode;
	reg [7:0] ld_mem_addr;
	reg [7:0] logical_data_out;
	reg [7:0] data_in1,data_in2;
	reg [7:0] ld_mem_addr_reg;
	reg [7:0] alu_data_out,shift_data_out;
	reg [7:0] data_out_reg, res_addr, res_addr_reg;
	reg [7:0] st_mem_addr, st_mem_addr_reg;
	reg		add_op_true, carry_in, en_op2_complement;
	reg		and_op_true, or_op_true, not_op_true;
	reg	    jump_true, shift_left_true,store_to_mem_ex ;
	reg		add_op_true_reg, carry_in_reg;
	reg		en_op2_complement_reg,jump_true_reg;       
	reg		and_op_true_reg,or_op_true_reg,not_op_true_reg;
	reg		shift_left_true_reg;
	reg		set_invalidate_instruction;
	reg		carry_flag, save_carry_flag_reg;
	reg		lgcl_or_bitwse_T;
	reg		lgcl_or_bitwse_T_reg;
	reg		load_true, store_true;
	reg		write_to_regfile, write_to_regfile_reg;
	reg		store_true_reg, load_true_reg;
	reg		alu_carry_out, shift_carry_out;
	reg		load_mem_data;
	reg		bypass_op1_ex_stage, bypass_op2_ex_stage;
	reg		bypass_op1_dcd_stage, bypass_op2_dcd_stage; 
	reg		and_bitwise_true_reg, branch_taken_reg;
	reg		and_bitwise_true, or_bitwise_true_reg;
	reg		or_bitwise_true, not_bitwsie_true_reg;
	reg		not_bitwise_true, not_bitwise_true_reg;
	reg		invalidate_fetch_instr;
	reg		invalidate_decode_instr_r1;
	reg		invalidate_fetch_instr_r2;
	reg		invalidate_decode_instr,reg_wr_en_ex;
	reg		invalidate_fetch_instr_r1;
	reg		invalidate_execute_instr,carry_flag_ex;
	reg		gt_flag_ex_reg, gt_flag;
	reg		lt_flag_ex_reg, lt_flag, unconditional_jump;
	reg		eq_flag_ex_reg, eq_flag, unconditional_jump_reg;
	reg		compare_true, compare_true_reg, compare_true_r2;
	reg		jump_gt, jump_lt, jump_eq, jump_carry;
	reg		jump_gt_reg, jump_lt_reg, jump_eq_reg;
	reg		jump_carry_reg;




//****************************************
//   RESET INITIALIZATION
//****************************************

//keep instruction and program counter at zero during reset
//Disable register and memory writes during reset
	always @(reset)
	    if (reset == 1'b1)                          
		    begin
		        prog_ctr <= 10'b0;
		        instruction <= 16'b0;
		    end

//****************************************
//	INSTRUCTION FETCH PIPELINE REGISTERS
//****************************************
                                                   
	always @(posedge clk)
		if (reset == 1'b1)
		    begin
		        instruction <= 16'b0;
		        invalidate_fetch_instr <= 1'b0;
		    end
		else
		    begin
		        instruction <= #1 instr_mem_out;
		        if (branch_taken_reg == 1'b1)
			        invalidate_fetch_instr <= #1 1'b1;
		        else
			        invalidate_fetch_instr <= #1 1'b0;
		    end

                                             
//***************************
//	INSTRUCTION DECODE LOGIC
//****************************

/*
The instruction word is 16 bits wide. During the Decode (ID)
pipeline stage, the instruction is split into several fields. 
Each field may be interpreted differently depending on the 
instruction type (ALU, LOAD, STORE, BRANCH). The decode logic
extracts all fields unconditionally, simplifying later pipeline
stages, which can ignore fields that are not relevant to the
current instruction.


ALU OPERATIONS (ADD, SUB, AND, OR, ...)
15         11 10      8 7    6 5     4 3    2 1       0
+------------+---------+------+-------+------+--------+
|   opcode   | res_reg | XXX  | op2_r | XXX  | op1_r  |
+------------+---------+------+-------+------+--------+
opcode → ALU operation
res_reg → destination register
op2_r → second operand register
op1_r → first operand register
X = unused/don’t care


LOAD INSTRUCTION
15         11 10      8 7                                  0
+------------+---------+-----------------------------------+
|   opcode   | res_reg |         immediate addr            |
+------------+---------+-----------------------------------+
load from instruction[7:0] into register instruction[10:8]


STORE INSTRUCTION
15         11 10                                  3 2       0
+------------+-------------------------------------+--------+
|   opcode   |       store memory address          | op1_r  |
+------------+-------------------------------------+--------+
store register op1_r -> memory address [10:3]
no destination register


BRANCH INSTRUCTION
15         11 10                                       0
+------------+-----------------------------------------+
|   opcode   |              branch target              |
+------------+-----------------------------------------+
branch_addr is 10 bits -> 1024-entry address space

*/

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

//--------------------------------------------------------
// Default all control signals (no operation)
//--------------------------------------------------------
/*
The control unit is implemented as a combinational opcode 
decoder. Given the 5-bit opcode extracted during the 
instruction decode stage, it generates ALU control signals, 
memory access enables, branch and jump controls, and the 
register file write-enable flag.

All control signals are defaulted to zero (NOP behaviour). 
The case statement assigns the minimum required set of 
signals for each opcode. This implements a classic 
hardwired control-path microarchitecture.
*/

	always@ (opcode or branch_addr)        
begin
		add_op_true <= 1'b0;
		and_op_true <= 1'b0;
		or_op_true  <= 1'b0;
		not_op_true <= 1'b0; 
		carry_in	<= 1'b0;
		en_op2_complement  <= 1'b0;
		jump_true	<= 1'b0;
		compare_true <= 1'b0;
		shift_left_true <= 1'b0;
		lgcl_or_bitwse_T <= 1'b0;
		load_true <= 1'b0;
		store_true <= 1'b0;
		write_to_regfile <= 1'b0;
		unconditional_jump <= 1'b0;
		jump_gt <= 1'b0;
		jump_lt <= 1'b0;
		jump_eq <= 1'b0;
		jump_carry <= 1'b0;

		case (opcode)
		//	OP_NOP:  
		//	5'h00:   	;		
		
		//	OP_ADD:	begin
			5'h01:	begin
					write_to_regfile <= 1'b1;
					add_op_true <= 1'b1;
					end
	
		//	OP_SUB:	begin
			5'h02:	begin
					add_op_true <= 1'b1;	
					carry_in	<= 1'b1;
					en_op2_complement <= 1'b1;
					write_to_regfile <= 1'b1;
				   	end

		//	OP_AND:	begin
			5'h03:	begin
					and_op_true <= 1'b1;
					lgcl_or_bitwse_T <= 1'b1;
					write_to_regfile <= 1'b1;     
					end

		//	OP_OR:	begin
			5'h04:	begin
					or_op_true <= 1'b1;
					lgcl_or_bitwse_T <= 1'b1;
					write_to_regfile <= 1'b1;
					end

		//	OP_NOT:	begin
			5'h05:	begin
					not_op_true <= 1'b1;
					lgcl_or_bitwse_T <= 1'b1;
					write_to_regfile <= 1'b1;
					end

		//	OP_SHL	begin                  
			5'h06:	begin
					shift_left_true <= 1'b1;
					write_to_regfile <= 1'b1;
					end

		//	OP_JMP:	begin
			5'h07:	begin
					nxt_prog_ctr <= branch_addr;
					jump_true	<= 1'b1;
					unconditional_jump <= 1'b1;
					end

		//	OP_LOAD:	begin
			5'h08:	begin
					load_true <= 1'b1;
					write_to_regfile <= 1'b1;
					end                      
                                                      
		//	OP_STORE:	store_true <= 1'b1;
			5'h09:	store_true <= 1'b1;

		//	OP_ANDBIT:	begin
			5'h0a:	begin
					and_bitwise_true <= 1'b1;
					lgcl_or_bitwse_T <= 1'b1;
					write_to_regfile <= 1'b1; 
			   		end

		//	OP_ORBIT:	begin
			5'h0b:	begin
					or_bitwise_true <= 1'b1;
					lgcl_or_bitwse_T <= 1'b1;
					write_to_regfile <= 1'b1;
					end

		//	OP_NOTBIT:	begin
			5'h0c:	begin
					not_bitwise_true <= 1'b1;
					lgcl_or_bitwse_T <= 1'b1;
					write_to_regfile <= 1'b1;
					end
 
		//	OP_COMPARE: begin
			5'h0d:	begin
					add_op_true <= 1'b1;
					compare_true <= 1'b1;	
					carry_in	<= 1'b1;   //subtract
					en_op2_complement <= 1'b1;
				   	end

		//	OP_JMPGT:	begin
			5'h0e:	begin
					nxt_prog_ctr <= branch_addr;
					jump_true	<= 1'b1;
					jump_gt <= 1'b1;
					end

		//	OP_JMPLT:	begin
			5'h0f:	begin
					nxt_prog_ctr <= branch_addr;
					jump_true	<= 1'b1;
					jump_lt <= 1'b1;
					end
		//	OP_JMPEQ:	begin
			5'h10:	begin
					nxt_prog_ctr <= branch_addr;
					jump_true	<= 1'b1;
					jump_eq <= 1'b1;
					end

		//	OP_JMPC:	begin
			5'h11:	begin
					nxt_prog_ctr <= branch_addr;
					jump_true	<= 1'b1;
					jump_carry <= 1'b1;
					end

			default: 	;			//= NOP
			endcase
		end
	


//======================================================================
// Decode-Stage Bypass (Forwarding) Logic
// Detects RAW hazards where the instruction in Decode needs a register
// being written by an instruction ahead in the pipeline.
//
// If the previous instruction writes a register and that register equals
// either op1_addr or op2_addr, AND the instruction is not a LOAD
// (load results are not yet available), then bypass the data.
//
// This selects between:
//   - op?_rd_data       (normal regfile output)
//   - datamem_wr_data   (forwarded/bypassed result)
//
//======================================================================

//---------------------------
// Operand 1 bypass detector
//---------------------------
always @(op1_addr or destination_reg_addr or reg_wr_en or load_true)

	begin
	if ((op1_addr == destination_reg_addr) && (reg_wr_en == 1'b1) && (load_true == 1'b0))
		bypass_op1_dcd_stage <= 1'b1;
	else
		bypass_op1_dcd_stage <= 1'b0;
	end


//---------------------------
// Operand 2 bypass detector
//---------------------------
always @(op2_addr or destination_reg_addr or reg_wr_en or load_true)

	begin
	if ((op2_addr == destination_reg_addr) && (reg_wr_en == 1'b1) && (load_true == 1'b0))
		bypass_op2_dcd_stage <= 1'b1;
	else
		bypass_op2_dcd_stage <= 1'b0;
	end

    
//---------------------------
// Actual data selection
//---------------------------
assign op1_data = bypass_op1_dcd_stage  ? datamem_wr_data : op1_rd_data;
assign op2_data = bypass_op2_dcd_stage  ? datamem_wr_data : op2_rd_data;


//**********************************************************
//	INSTRUCTION DECODE AND OPERAND FETCH PIPELINE REGISTERS
//***********************************************************

	always @(posedge clk)
		begin
		    add_op_true_reg	<= #1	add_op_true;
		    or_op_true_reg	<= #1	or_op_true;
		    not_op_true_reg	<= #1	not_op_true;
		    and_bitwise_true_reg <= #1 and_bitwise_true; 
		    or_bitwise_true_reg <= #1 or_bitwise_true;
		    not_bitwise_true_reg <= #1 not_bitwise_true;  
		    and_op_true_reg	<= #1	and_op_true;
		    or_op_true_reg	<= #1	or_op_true;      
		    not_op_true_reg	<= #1	not_op_true;
		    carry_in_reg	<= #1  carry_in;
		    en_op2_complement_reg  <= #1 en_op2_complement;
		    nxt_prog_ctr_reg 	<= #1 nxt_prog_ctr;
		    jump_true_reg	<= #1 jump_true;
		    compare_true_reg <= #1 compare_true;
		    op1_data_reg	<= #1 op1_data ;
		    op2_data_reg	<= #1 op2_data ;
		    shift_left_true_reg <= #1 shift_left_true;
		    lgcl_or_bitwse_T_reg <= #1 lgcl_or_bitwse_T;
		    store_true_reg <= #1 store_true;
		    load_true_reg <= #1 load_true;
		    write_to_regfile_reg <= #1 write_to_regfile;
		    ld_mem_addr_reg <= #1 ld_mem_addr;
		    st_mem_addr_reg <= #1 st_mem_addr;
		    invalidate_fetch_instr_r1 <= #1 invalidate_fetch_instr;
		    jump_gt_reg <= #1 jump_gt;
		    jump_lt_reg <= #1 jump_lt;
		    jump_eq_reg <= #1 jump_eq;
		    jump_carry_reg <= #1 jump_carry;
		    unconditional_jump_reg <= #1 unconditional_jump;
		end

always @(posedge clk)
	if (reset == 1'b1)
		begin
		    op1_addr_reg <= 3'b000;
		    op2_addr_reg <= 3'b000;
		    res_addr_reg <= 3'b000;
		    invalidate_decode_instr <= 1'b0;
		end
	else
		begin 
		    op1_addr_reg <= #1 op1_addr;          
		    op2_addr_reg <= #1 op2_addr;
		    res_addr_reg <= #1 res_addr;                
		    if (branch_taken_reg == 1'b1)
		    	invalidate_decode_instr <= #1 1'b1;
		    else
		    	invalidate_decode_instr <= #1 1'b0;	
		end	




//*********************
//EXECUTION UNIT LOGIC
//*********************

//======================================================================
// EXECUTE-STAGE BYPASS LOGIC (Forwarding)
//----------------------------------------------------------------------
// Detects RAW hazards where the instruction in EX needs a register
// being written by a later pipeline stage (MEM/WB).
//
// Matches source registers (op1/op2) against the destination register
// of the previous instruction. If previous instruction writes a result
// AND is not a LOAD (data not available), bypass the new value.
//
//======================================================================
always @(op1_addr_reg or destination_reg_addr or reg_wr_en or op2_addr_reg or load_true_reg)

	begin
        // -------------------
        // OPERAND 1 BYPASS
        // -------------------
	    if ((op1_addr_reg == destination_reg_addr) && (reg_wr_en == 1'b1) && (load_true_reg == 1'b0))
	    	bypass_op1_ex_stage <= 1'b1;
	    else
	    	bypass_op1_ex_stage <= 1'b0;

        // -------------------
        // OPERAND 2 BYPASS
        // -------------------
	    if ((op2_addr_reg == destination_reg_addr) && (reg_wr_en == 1'b1) && (load_true_reg == 1'b0))
	    	bypass_op2_ex_stage <= 1'b1;
	    else
	    	bypass_op2_ex_stage <= 1'b0;
	end


// -------------------
// Select Operand Data
// -------------------
assign operand1 = bypass_op1_ex_stage  ? datamem_wr_data : op1_data_reg;
assign operand2 = bypass_op2_ex_stage  ? datamem_wr_data : op2_data_reg;

  
//======================================================================
// ALU INPUT PREPARATION
//----------------------------------------------------------------------
// - STORE instructions feed zero into operand2
// - SUB/COMPARE invert operand2 and add carry-in
// - Otherwise pass operand2 through as-is
//======================================================================

always @(operand1 or operand2 or en_op2_complement_reg or store_true_reg or add_op_true_reg or lgcl_or_bitwse_T_reg or shift_left_true_reg)

	begin
	    data_in1 <= operand1;      

	    if (store_true_reg == 1'b1)
	       data_in2 <= 8'b0;
	    else if (en_op2_complement_reg == 1)
	       data_in2 <= ~operand2;
	    else
	       data_in2 <= operand2;
	end

//======================================================================
// EXECUTION UNIT
// Performs arithmetic, logic, shift operations, compare flag generation,
// and branch condition evaluation.
//======================================================================

//----------------------------------------------------------------------
// ALU: ADD / SUB / STORE pass-through
//----------------------------------------------------------------------
// Two's complement subtraction is handled earlier by complementing
// operand2 and asserting carry_in_reg = 1.

always @(data_in1 or data_in2 or carry_in_reg)
		{alu_carry_out, alu_data_out} <= data_in1 + data_in2 + carry_in_reg;

//----------------------------------------------------------------------
// Compare instruction flag generation
// Only valid if compare_true_reg == 1
//----------------------------------------------------------------------

assign gt_flag_ex = ((compare_true_reg == 1'b1) &&
                     (alu_carry_out == 1'b1) &&
                     (alu_data_out != 8'b0));

assign lt_flag_ex = ((compare_true_reg == 1'b1) &&
                     (alu_carry_out == 1'b0) &&
                     (alu_data_out != 8'b0));

assign eq_flag_ex = ((compare_true_reg == 1'b1) &&
                     (alu_data_out == 8'b00000000));

//----------------------------------------------------------------------
// Shift-left operation
//----------------------------------------------------------------------

always @(data_in1)
	begin
	    shift_carry_out <= data_in1[7];             // bit shifted out
	    shift_data_out	<= {data_in1[6:0], 1'b0};   // logical shift left
	end 

//----------------------------------------------------------------------
// Logical / Bitwise operations
//----------------------------------------------------------------------                    

always @(and_op_true_reg or or_op_true_reg or not_op_true_reg or and_bitwise_true_reg or or_bitwise_true_reg or not_bitwise_true_reg or data_in1 or data_in2 )
    begin
        case (1'b1)

            and_op_true_reg:        logical_data_out = data_in1 && data_in2;
            or_op_true_reg:         logical_data_out = data_in1 || data_in2;
            not_op_true_reg:        logical_data_out = !data_in1;

            and_bitwise_true_reg:   logical_data_out = data_in1 & data_in2;
            or_bitwise_true_reg:    logical_data_out = data_in1 | data_in2;
            not_bitwise_true_reg:   logical_data_out = ~data_in1;

            default:                logical_data_out = ~data_in1;  // fallback
        endcase
    end


//----------------------------------------------------------------------
// Result MUX
// Select final data output for MEM stage
//----------------------------------------------------------------------
assign data_out = (add_op_true_reg || store_true_reg) ? alu_data_out :
                                                        (lgcl_or_bitwse_T_reg ? logical_data_out : shift_data_out);
                 
//----------------------------------------------------------------------
// Carry-out selection
//----------------------------------------------------------------------
assign carry_out = add_op_true_reg ? alu_carry_out : shift_carry_out;

//----------------------------------------------------------------------
// Carry flag writes (skip during compare)
//----------------------------------------------------------------------
assign save_carry_flag = (add_op_true_reg && !compare_true_reg) || shift_left_true_reg;	

//======================================================================
// BRANCH CONDITION LOGIC
// Combine EX-stage compare flags with stored flags
//======================================================================

assign gt_flag_true = 
		(((compare_true_r2 && !invalidate_instr) == 1'b1) &&
			gt_flag_ex_reg) || gt_flag;
assign lt_flag_true =
		(((compare_true_r2 && !invalidate_instr) == 1'b1) &&
			lt_flag_ex_reg) || lt_flag;	
assign eq_flag_true =
		(((compare_true_r2 && !invalidate_instr) == 1'b1) &&
			eq_flag_ex_reg) || eq_flag;
	
assign carry_flag_true =
		(((save_carry_flag_reg  && !invalidate_instr) == 1'b1)
		&& carry_flag_ex) || carry_flag ;

//----------------------------------------------------------------------
// Final branch decision
//----------------------------------------------------------------------
assign branch_taken =
       unconditional_jump_reg ||
      (gt_flag_true    && jump_gt_reg)    ||
      (lt_flag_true    && jump_lt_reg)    ||
      (eq_flag_true    && jump_eq_reg)    ||
      (carry_flag_true && jump_carry_reg);

                                              
//****************************************
// EXECUTION STAGE PIPELINE REGISTERS
//****************************************
                                                        
// Note that asynchronous read of memory ensures that no bypass
// is needed for STORE followed by LOAD

always @(posedge clk)
	begin
	    if (save_carry_flag == 1'b1)
	    	carry_flag_ex <= #1 carry_out;
        
        operation_result <= #1 data_out;
	    data_wr_addr <= #1 store_true_reg ? st_mem_addr_reg : ld_mem_addr_reg; 
	    data_rd_addr <= #1 ld_mem_addr_reg; 
	    data_out_reg <= #1 data_out;
	    load_mem_data <= #1 load_true_reg;
	    invalidate_fetch_instr_r2 <= #1 invalidate_fetch_instr_r1;
	    invalidate_decode_instr_r1 <= #1 invalidate_decode_instr; 
	    gt_flag_ex_reg <= #1 gt_flag_ex;
	    lt_flag_ex_reg <= #1 lt_flag_ex;
	    eq_flag_ex_reg <= #1 eq_flag_ex;
	    compare_true_r2 <= #1 compare_true_reg;       
	    nxt_prog_ctr_r2 <= #1 nxt_prog_ctr_reg;
	end
// data_wr_addr[10:8] is also the result wr addr
// and datamem wr data is also the wr data for register writes

//Disable register and memory writes during reset
always @(posedge clk)
	if (reset == 1'b1)
	    begin
		    store_to_mem_ex <= #1 1'b0;
		    reg_wr_en_ex <= #1 1'b0;
		    destination_reg_addr <= 3'b0;
		    branch_taken_reg <= 1'b0;
		    invalidate_execute_instr <= 1'b0;
		    save_carry_flag_reg <= 1'b0;
	    end
	else
	    begin
		    store_to_mem_ex <= #1 store_true_reg;
		    reg_wr_en_ex <= #1 write_to_regfile_reg;
		    destination_reg_addr <= #1 res_addr_reg;
		    branch_taken_reg <= #1 branch_taken;
		    save_carry_flag_reg <= #1 save_carry_flag; 
		    
            if (branch_taken_reg == 1'b1)
		    	invalidate_execute_instr <= #1 1'b1;
		    else
		    	invalidate_execute_instr <= #1 1'b0;
	    end


//****************************************
// STORE RESULTS STAGE LOGIC
//****************************************

//During LOAD instruction data is fetched from memory and
// written to the register here

assign datamem_wr_data = load_mem_data ? datamem_rd_data : data_out_reg;

assign invalidate_instr = (invalidate_fetch_instr_r2 ||
	invalidate_decode_instr_r1 || invalidate_execute_instr);

assign  store_to_mem = (store_to_mem_ex && !invalidate_instr);

assign reg_wr_en = (reg_wr_en_ex && !invalidate_instr);



//****************************************
// STORE RESULT STAGE PIPELINE REGISTERS
//****************************************
always @(posedge clk)
	begin                                
	if (reset == 1'b1)                     
		begin
		    carry_flag <= 1'b0;
		    gt_flag <= 1'b0;
		    lt_flag <= 1'b0;
		    eq_flag <= 1'b0;
		end
		
	else 
		begin
		    if ((save_carry_flag_reg && !invalidate_instr) == 1'b1)
	            carry_flag <= #1 carry_flag_ex;

		    if ((compare_true_r2 && !invalidate_instr) == 1'b1)
		    	begin
		    	    gt_flag <= #1 gt_flag_ex_reg;
		    	    lt_flag <= #1 lt_flag_ex_reg;
		    	    eq_flag <= #1 eq_flag_ex_reg;
		    	end
		end
	end


//****************************************
// PROGRAM COUNTER
//****************************************

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


//@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
//
// ASSERTIONS FOR PROCESSOR_CORE
//	- a_* = assert
//	- c_* = cover
//	- s_* = assume
//
//@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

localparam [4:0] OPC_NOP      = 5'h00;
localparam [4:0] OPC_ADD      = 5'h01;
localparam [4:0] OPC_SUB      = 5'h02;
localparam [4:0] OPC_AND      = 5'h03;
localparam [4:0] OPC_OR       = 5'h04;
localparam [4:0] OPC_NOT      = 5'h05;
localparam [4:0] OPC_SHIFT    = 5'h06;
localparam [4:0] OPC_JMP      = 5'h07;
localparam [4:0] OPC_LOAD     = 5'h08;
localparam [4:0] OPC_STORE    = 5'h09;
localparam [4:0] OPC_ANDBIT   = 5'h0a;
localparam [4:0] OPC_ORBIT    = 5'h0b;
localparam [4:0] OPC_NOTBIT   = 5'h0c;
localparam [4:0] OPC_COMPARE  = 5'h0d;
localparam [4:0] OPC_JMPGT    = 5'h0e;
localparam [4:0] OPC_JMPLT    = 5'h0f;
localparam [4:0] OPC_JMPEQ    = 5'h10;
localparam [4:0] OPC_JMPC     = 5'h11;
//-----------------------------------------------
// DECODE LOGIC ASSERTIONS
//-----------------------------------------------

//a_branch_addr_range: assert property (@(posedge clk)
//    opcode == OPCODE_BRANCH |-> branch_addr < 1024
//);

a_load_addr_range: assert property (@(posedge clk)
    opcode == OPC_LOAD |-> ld_mem_addr inside {[0:255]}
);

a_store_addr_range: assert property (@(posedge clk)
    opcode == OPC_STORE |-> st_mem_addr inside {[0:255]}
);


//-----------------------------------------------
// OPCODE ASSERTIONS
//-----------------------------------------------


// Ensure with assume assert that opcode follows the RISC protocol
s_valid_opcode: assume property ( @(posedge clk) 
								opcode inside {
									OPC_NOP,
									OPC_ADD,
									OPC_SUB,
									OPC_AND,
									OPC_OR,
									OPC_NOT,
									OPC_SHIFT,
									OPC_JMP,
									OPC_LOAD,
									OPC_STORE,
									OPC_ANDBIT,
									OPC_ORBIT,
									OPC_NOTBIT,
									OPC_COMPARE,
									OPC_JMPGT,
									OPC_JMPLT,
									OPC_JMPEQ,
									OPC_JMPC
								} );

//-----------------------------------------------
// PROGRAM COUNTER ASSERTIONS
//-----------------------------------------------
s_valid_pc : assume property (@(posedge clk) prog_ctr < 1024);



endmodule
