module instr_and_data_mem (clk, 
						   prog_ctr, instr_mem_out,
						   data_rd_addr, data_wr_addr,
						   datamem_rd_data, datamem_wr_data,
						   store_to_mem);

	input clk;
	input [9:0] prog_ctr;
	input [7:0] data_rd_addr, datamem_wr_data;
	input [7:0] data_wr_addr;
	input store_to_mem;  
                                     
	output [15:0] instr_mem_out;
	output [7:0] datamem_rd_data;

	reg [15:0]	instr_mem_out;              
	reg [7:0]	datamem_rd_data;



// instruction memory operations
	reg [15:0] instr_mem[0:1023];

	`ifdef FORMAL
    	// JasperGold chooses any instruction each cycle
    	(* anyconst *) reg [15:0] instr_sym;
		always @(posedge clk) restrict($stable(instr_sym));

    	always @(posedge clk)
    	    instr_mem_out <= #1 instr_sym;
	`else
    	// Regular RTL behavior
		initial
			$readmemh("../tb/program1.txt",instr_mem);
    	always @(posedge clk)
    	    instr_mem_out <= #1 instr_mem[prog_ctr];
	`endif


// data memory operations
	reg [7:0] data_mem[255:0];
	
	`ifdef FORMAL
		// JasperGold chooses any data value each cycle
	    (* anyconst *) reg [7:0] data_sym;
		always @(data_rd_addr) restrict($stable(data_sym));

	    always @(data_rd_addr) 
			datamem_rd_data <= data_sym;
	`else
		// Regular RTL behavior
		initial
			$readmemh("../data1.txt",data_mem);

	    always @(data_rd_addr) 
			datamem_rd_data <= data_mem[data_rd_addr];
	`endif


                                                      
// write to data memory in STORE instruction
	always @(posedge clk) begin
		if (store_to_mem == 1'b1) begin
			// On a STORE, read-after-write must return the written value
			assume(data_sym == datamem_wr_data);
			data_mem[data_wr_addr] <= datamem_wr_data;
		end
	end

//@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
//
// ASSERTIONS FOR INSTR_AND_DATA_MEM
//	- a_* = assert
//	- c_* = cover
//	- s_* = assume
//
//@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

//--------------------
// ASSERT PROPERTIES
//--------------------


//--------------------
// ASSUME PROPERTIES
//--------------------

// read after writes are fine, just not in the same damn cycle.
s_no_same_cycle_r_w: assume property (@(posedge clk) (!(store_to_mem && data_rd_addr == data_wr_addr));)

//--------------------
// COVER PROPERTIES
//--------------------



endmodule