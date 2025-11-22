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

	
// load program into memory 
	initial
	begin
	$readmemh("../tb/program1.txt",instr_mem);
	end

// read instructions from memory
	always @(posedge clk)
		instr_mem_out <=  #1 instr_mem[prog_ctr];


// data memory operations
	reg [7:0] data_mem[255:0];

// initialize data memory from file
	initial
	begin
	$readmemh("../data1.txt",data_mem);
	end
                                                     
// get data during LOAD instruction                 
	always @(data_rd_addr)
		datamem_rd_data <= data_mem[data_rd_addr]; 
                                                      
// write to data memory in STORE instruction
	always @(posedge clk)
		if (store_to_mem == 1'b1)
			data_mem[data_wr_addr] <= datamem_wr_data;

endmodule