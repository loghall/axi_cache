`include "props_pkg.sv" 

import propsPkg::*; 

module ram_props #(
    parameter integer MEM_ADDR_WIDTH = 7,
    parameter integer MEM_DATA_WIDTH = 32,
    parameter integer MEM_DATA_SIZE_BYTES = 4
                     
)
(  
    clk,
    reset_n, 
    i_addr, 
    i_wen, 
    i_ben,
    i_write_data,
    o_read_data  
);
    //------------------------------------------
    // 
    // Ports
    // 
    //------------------------------------------
    input wire clk; 
    input wire reset_n; 
    input wire [MEM_ADDR_WIDTH - 1 : 0] i_addr; 
    input wire i_wen;
    input wire [MEM_DATA_SIZE_BYTES - 1 : 0] i_ben;
    input wire [MEM_DATA_WIDTH - 1 : 0] i_write_data;
    input wire [MEM_DATA_WIDTH - 1 : 0] o_read_data; 

    //------------------------------------------
    // 
    // Internal/aux
    // 
    //------------------------------------------
    reg [MEM_ADDR_WIDTH - 1 : 0] arb_addr; 
    reg [MEM_DATA_WIDTH - 1 : 0] arb_data_1, arb_data_2;

    //------------------------------------------
    // 
    // Global assumes
    // 
    //------------------------------------------
    assume_arb_addr_constant : assume property( // arb_address is some constant, word aligned address
        implies_1cycle(
            clk, !reset_n,
            1,
            $stable(arb_addr) && ((arb_addr % 4) == 0)
        )
    );

    assume_word_aligned : assume property( // addresses are word aligned
        implies_1cycle(
            clk, !reset_n,
            1,
            i_addr % 4 == 0
        )
    );
    
    //------------------------------------------
    // 
    // Assert 
    // 
    //------------------------------------------
    assert_rdata : assert property( // verify that arb_data and output data agree 
        implies_1cycle(
            clk, !reset_n,
            arb_addr == i_addr,
            o_read_data == arb_data_1
        )
    );

    //------------------------------------------
    // 
    // Aux Code 
    // 
    //------------------------------------------

    // track what the value of arb_data should be in the memory. 
    always@(posedge clk) begin
        integer n; 

        if(!reset_n) begin
            arb_data_1 <= 0; 
            arb_data_2 <= 0; 
        end 
        else begin
            // writes are visible one cycle later, so this is required. 
            arb_data_1 <= arb_data_2;

            // if its a write, get the new data; must apply BEN
            if(i_wen && arb_addr == i_addr) begin 
                for(n = 0; n < MEM_DATA_SIZE_BYTES; n = n + 1) begin   
                    if(i_ben[n]) begin
                        arb_data_2[n * 8 + 7 -: 8] <= i_write_data[n * 8 + 7 -: 8]; 
                    end
                end 
            end
        end 
    end

endmodule

module Wrapper;

    bind ram ram_props bind1(
        .clk(clk), 
        .reset_n(reset_n),  
        .i_addr(i_addr), 
        .i_wen(i_wen),
        .i_ben(i_ben),
        .i_write_data(i_write_data),
        .o_read_data(o_read_data) 
    );

endmodule
