module register_file (clk, reset, 
					  wr_data, 
					  rd_data1, rd_data2, 
					  rd_addr1, rd_addr2, 
					  wr_addr, 
					  wr_en);

	input clk, reset;
	input [7:0] wr_data;
	input [2:0] rd_addr1, rd_addr2, wr_addr;
	input		wr_en;
	output[7:0] rd_data1, rd_data2;

	reg [7:0] rd_data1, rd_data2;


//	register file
	reg [7:0] reg_file [7:0];
                                         	
	always @(rd_addr1 or rd_addr2 or reset or wr_en or wr_data)
		begin
		    rd_data1 <= reg_file[rd_addr1];
		    rd_data2 <= reg_file[rd_addr2];
		end

    always @(posedge clk)	
		begin
		    if (wr_en == 1)
		    	reg_file[wr_addr] <= #1 wr_data;
		end


//@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
//
// ASSERTIONS FOR REGISTER_FILE
//	- a_* = assert
//	- c_* = cover
//	- s_* = assume
//
//@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

//--------------------
// ASSERT PROPERTIES
//--------------------
// Ensures that after one clock cycle the wr_data is in fact stored correctly when wr_en is high
a_succesfull_write: assert property (@(posedge clk)
									 wr_en |-> ##1 (reg_file[wr_addr] == $past(wr_data)));
// Ensure stable memory when wr_en low
a_register_stability: assert property (@(posedge clk)
									 !wr_en ##1 !wr_en |-> (reg_file[wr_addr] == $past(reg_file[wr_addr])));
// Ensure wr_addr is stable during write
a_wr_addr_stable_during_write: assert property (@(posedge clk)
  												wr_en |-> $stable(wr_addr));
// Ensures actual values being wrote to registers
a_no_unkown_wr_data: assert property (@(posedge clk)
									  wr_en |-> !$isunknown(wr_data));

// Ensure correct reads from registers
a_read_port1_correct: assert property (@(posedge clk)
    									rd_data1 == reg_file[rd_addr1]);

a_read_port2_correct: assert property (@(posedge clk)
      									rd_data2 == reg_file[rd_addr2]);

//--------------------
// ASSUME PROPERTIES
//--------------------


										
//--------------------
// COVER PROPERTIES
//--------------------
// This is an interesting one as it will assert but we should pay attention to what happens to the read data when it does
c_read_write_same_addr: cover property (@(posedge clk)
										wr_en && (wr_addr == rd_addr1 || wr_addr == rd_addr2));


endmodule