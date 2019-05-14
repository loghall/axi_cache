`include "props_pkg.sv" 

import propsPkg::*; 

module cache_way_props #(
    parameter integer CACHE_WAY_ADDR_WIDTH = 7,
    parameter integer CACHE_WAY_DATA_WIDTH = 32,
    parameter integer CACHE_WAY_DATA_SIZE_BYTES = 4,
    parameter integer CACHE_WAY_TAG_WIDTH = 4,
    parameter integer CACHE_WAY_TAG_SIZE_BYTES = 1               
)
(  
    clk,
    reset_n, 
    i_cache_way_addr,
    i_cache_way_wen, 
    i_cache_way_ben,
    i_cache_way_data,
    o_cache_way_data, 
    i_tag_wen, 
    i_tag_data,
    o_tag_data    
);
    //------------------------------------------
    // 
    // Ports
    // 
    //------------------------------------------
    input wire clk;
    input wire reset_n; 
 
    input wire [CACHE_WAY_ADDR_WIDTH - 1 : 0] i_cache_way_addr;

    input wire i_cache_way_wen; 
    input wire [CACHE_WAY_DATA_SIZE_BYTES - 1 : 0] i_cache_way_ben;
    input wire [CACHE_WAY_DATA_WIDTH - 1 : 0] i_cache_way_data;
    input wire [CACHE_WAY_DATA_WIDTH - 1 : 0] o_cache_way_data;

    input wire i_tag_wen; 
    input wire [CACHE_WAY_TAG_WIDTH - 1 : 0] i_tag_data;
    input wire [CACHE_WAY_TAG_WIDTH - 1 : 0] o_tag_data;   

    //------------------------------------------
    // 
    // Internal/aux
    // 
    //------------------------------------------
    reg [CACHE_WAY_ADDR_WIDTH - 1 : 0] arb_addr; 
    reg [CACHE_WAY_DATA_WIDTH - 1 : 0] arb_data_1, arb_data_2;
    reg [CACHE_WAY_TAG_WIDTH - 1 : 0] arb_tag_1, arb_tag_2; 

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
            i_cache_way_addr % 4 == 0
        )
    );


    //------------------------------------------
    // 
    // Helper functions
    // 
    //------------------------------------------
    
    //------------------------------------------
    // 
    // Assert 
    // 
    //------------------------------------------
    assert_rdata : assert property( // read data should always be correct
        implies_1cycle(
            clk, !reset_n,
            arb_addr == i_cache_way_addr,
            o_cache_way_data == arb_data_1
        )
    );
 
    assert_rtag : assert property( // read data should always be correct
        implies_1cycle(
            clk, !reset_n,
            arb_addr == i_cache_way_addr,
            o_tag_data == arb_tag_1
        )
    );
 
    //------------------------------------------
    // 
    // Aux Code 
    // 
    //------------------------------------------
    always@(posedge clk) begin
        if(!reset_n) begin
            arb_tag_1 <= 0; 
            arb_tag_2 <= 0; 
        end 
        else begin
            arb_tag_1 <= arb_tag_2; // update current tag for reads 
            if(i_tag_wen && arb_addr == i_cache_way_addr) begin
                arb_tag_2 <= i_tag_data; 
            end
        end 
    end
   
    always@(posedge clk) begin
        integer n; 

        if(!reset_n) begin
            arb_data_1 <= 0; 
            arb_data_2 <= 0; 
        end 
        else begin
            arb_data_1 <= arb_data_2; // update current data for reads
            if(i_cache_way_wen && arb_addr == i_cache_way_addr) begin 
                for(n = 0; n < CACHE_WAY_DATA_SIZE_BYTES; n = n + 1) begin   
                    if(i_cache_way_ben[n]) begin
                        arb_data_2[n * 8 + 7 -: 8] <= i_cache_way_data[n * 8 + 7 -: 8]; 
                    end
                end 
            end
        end 
    end

endmodule

module Wrapper;

    bind cache_way cache_way_props bind1(
        .clk(clk), 
        .reset_n(reset_n),  
        .i_cache_way_addr(i_cache_way_addr),
        .i_cache_way_wen(i_cache_way_wen), 
        .i_cache_way_ben(i_cache_way_ben),
        .i_cache_way_data(i_cache_way_data),
        .o_cache_way_data(o_cache_way_data), 
        .i_tag_wen(i_tag_wen), 
        .i_tag_data(i_tag_data),
        .o_tag_data(o_tag_data)    
    );

endmodule

