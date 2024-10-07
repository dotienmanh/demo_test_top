`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/07/2024 02:49:09 PM
// Design Name: 
// Module Name: WB_top
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module WB_top(
    input  logic                     clk_i,
    input  logic                     rst_ni,
    
    input  logic [4:0]               rf_waddr_EX,         // From EX
    input  logic [31:0]              rf_wdata_EX,         // From EX
    input  logic                     rf_we_EX,            // From EX
  
    input  logic [31:0]              rf_wdata_lsu_i,        // From LSU
    input  logic                     rf_we_lsu_i,           // From LSU
    
    output logic [4:0]               rf_waddr_WB_o,
    output logic [31:0]              rf_wdata_WB_o,
    output logic                     rf_we_WB_o


    );
    logic [4:0]    rf_waddr_WB_r;
    logic [31:0]   rf_wdata_WB_r;
    logic          rf_we_WB_r;
    // EX/WB Pipeline
    always @(posedge clk_i or negedge rst_ni) begin
        if(rst_ni == 1'b0) begin
           rf_waddr_WB_r <=  5'b0;
           rf_wdata_WB_r <=  32'b0;
           rf_we_WB_r    <=  1'b0;
        end else begin
           rf_waddr_WB_r <= rf_waddr_EX;
           rf_wdata_WB_r <= rf_wdata_EX;
           rf_we_WB_r    <= rf_we_EX ;
        end
    end
    
    // 0 == RF write from EX
    // 1 == RF write from LSU
    logic [31:0] rf_wdata_wb_mux[2];
    logic [1:0]  rf_wdata_wb_mux_we;
    
    assign rf_wdata_wb_mux[0] = rf_wdata_WB_r;
    assign rf_wdata_wb_mux[1] = rf_wdata_lsu_i;
    
    assign rf_wdata_wb_mux_we[0] = rf_we_WB_r;      // NOT DONE YET
                                    //& wb_valid_q;
    assign rf_wdata_wb_mux_we[1] = rf_we_lsu_i;     // NOT DONE YET                            
    
    // RF write data can come from ID results (all RF writes that aren't because of loads will come
  // from here) or the LSU (RF writes for load data)
  assign rf_wdata_wb_o = ({32{rf_wdata_wb_mux_we[0]}} & rf_wdata_wb_mux[0]) |
                         ({32{rf_wdata_wb_mux_we[1]}} & rf_wdata_wb_mux[1]);
  assign rf_we_wb_o    = |rf_wdata_wb_mux_we;
  assign rf_waddr_WB_o = rf_waddr_WB_r;
endmodule
