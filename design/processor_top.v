module processor_top (clk, reset);

	input clk, reset;

	wire        clk, reset;
	wire 	    store_to_mem, reg_wr_en;
	wire [9:0]  prog_ctr;
	wire [15:0] instr_mem_out;
	wire [2:0]  op1_addr, op2_addr,destination_reg_addr;
	wire [7:0]  op1_rd_data, op2_rd_data, mem_data;
	wire [7:0]  data_rd_addr, data_wr_addr;
 	wire [7:0]  datamem_rd_data, datamem_wr_data;
	wire [7:0]  operation_result; 

 
	instr_and_data_mem  mem1(
							clk, 
							prog_ctr, instr_mem_out, 
							data_rd_addr, data_wr_addr, 
							datamem_rd_data, datamem_wr_data, 
							store_to_mem
							);

	processor_core 		proc1(
							clk, reset,
							op1_rd_data, op2_rd_data, 
							instr_mem_out,
							op1_addr, op2_addr,
							prog_ctr, store_to_mem, 
							reg_wr_en, 
							data_rd_addr, data_wr_addr, 
							datamem_rd_data, datamem_wr_data, 
							operation_result, 
							destination_reg_addr
							);

	register_file       regfile1(
							clk, reset, 
							.wr_data(datamem_wr_data), 
							.rd_data1(op1_rd_data), .rd_data2(op2_rd_data), 
							.rd_addr1(op1_addr), .rd_addr2(op2_addr), 
							.wr_addr(destination_reg_addr), 
							.wr_en(reg_wr_en)
							);

endmodule