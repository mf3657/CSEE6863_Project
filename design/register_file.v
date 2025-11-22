module register_file (clk, reset, 
					  wr_data, 
					  rd_data1, rd_data2, 
					  rd_addr1, rd_addr2, 
					  wr_addr, 
					  wr_en);

	input clk, reset;
	input [7:0] wr_data;
	input [2:0] rd_addr1, rd_addr2, wr_addr;
	input		 wr_en;
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

endmodule