`include "props_pkg.sv" 

import propsPkg::*; 

module cache_4way_props #(
    parameter integer CACHE_ADDR_WIDTH = 7,
    parameter integer CACHE_DATA_WIDTH = 32,
    parameter integer CACHE_TAG_WIDTH = 4,
    parameter integer CACHE_DATA_SIZE_BYTES = 4,
    parameter integer CACHE_TAG_SIZE_BYTES = 1            
)
(  
    clk,
    reset_n, 
    i_way_select, 
    i_cache_addr,
    i_cache_wen, 
    i_cache_ben,
    i_cache_data,
    o_cache_data, 
    i_tag_wen, 
    i_tag_data,
    o_tag_data    
);
    //---------------------------------------------
    //
    // Local parameters
    //
    //---------------------------------------------   
    localparam integer CACHE_WAY_WIDTH = 2; 
    localparam integer NUM_CACHE_WAY = (1 << CACHE_WAY_WIDTH); 

    //------------------------------------------
    // 
    // Ports
    // 
    //------------------------------------------
    input wire clk;
    input wire reset_n; 
    
    input wire [NUM_CACHE_WAY - 1 : 0] i_way_select;
    input wire [CACHE_ADDR_WIDTH - 1 : 0] i_cache_addr;

    input wire i_cache_wen; 
    input wire [CACHE_DATA_SIZE_BYTES - 1 : 0] i_cache_ben;
    input wire [CACHE_DATA_WIDTH - 1 : 0] i_cache_data;
    input wire [CACHE_DATA_WIDTH - 1 : 0] o_cache_data [0 : NUM_CACHE_WAY - 1];

    input wire i_tag_wen; 
    input wire [CACHE_TAG_WIDTH - 1 : 0] i_tag_data;
    input wire [CACHE_TAG_WIDTH - 1 : 0] o_tag_data [0 : NUM_CACHE_WAY - 1];   

    //------------------------------------------
    // 
    // Internal/aux
    // 
    //------------------------------------------
    reg [CACHE_ADDR_WIDTH - 1 : 0] arb_addr; 
    reg [CACHE_DATA_WIDTH - 1 : 0] arb_data_1 [0 : NUM_CACHE_WAY - 1]; 
    reg [CACHE_DATA_WIDTH - 1 : 0] arb_data_2 [0 : NUM_CACHE_WAY - 1]; 
    reg [CACHE_TAG_WIDTH - 1 : 0] arb_tag_1 [0 : NUM_CACHE_WAY - 1]; 
    reg [CACHE_TAG_WIDTH - 1 : 0] arb_tag_2 [0 : NUM_CACHE_WAY - 1]; 

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
            i_cache_addr % 4 == 0
        )
    );

    assume_way_sel_onehot : assume property( // addresses are word aligned
        implies_1cycle(
            clk, !reset_n,
            1,
            $onehot(i_way_select)
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
    genvar m;
    for(m = 0; m < NUM_CACHE_WAY; m = m + 1) begin : gen_assert_tagdata
        assert_tagdata : assert property( // read data should always be correct
            implies_1cycle(
                clk, !reset_n,
                arb_addr == i_cache_addr,
                o_tag_data[m] == arb_tag_1[m]
            )
        );
    end 
    for(m = 0; m < NUM_CACHE_WAY; m = m + 1) begin : gen_assert_rdata
        assert_rdata : assert property( // read data should always be correct
            implies_1cycle(
                clk, !reset_n,
                arb_addr == i_cache_addr,
                o_cache_data[m] == arb_data_1[m]
            )
        );
    end 
 
    //------------------------------------------
    // 
    // Aux Code 
    // 
    //------------------------------------------
    generate  // tag tracker
        for(m = 0; m < NUM_CACHE_WAY; m = m + 1) begin : gen_aux_tagdata
            integer n; 
            always@(posedge clk) begin

                if(!reset_n) begin
                        arb_tag_1[m] <= 0;
                        arb_tag_2[m] <= 0; 
                end 
                else begin 
                    arb_tag_1[m] <= arb_tag_2[m]; 
                    if(i_tag_wen && i_way_select[m] && i_cache_addr == arb_addr) begin
                        arb_tag_2[m] <= i_tag_data; 
                    end
                end 
            end
        end
    endgenerate 
    generate  // data tracker 
        for(m = 0; m < NUM_CACHE_WAY; m = m + 1) begin : gen_aux_rdata
            integer n; 
            always@(posedge clk) begin

                if(!reset_n) begin
                        arb_data_1[m] <= 0;
                        arb_data_2[m] <= 0; 
                end 
                else begin 
                    arb_data_1[m] <= arb_data_2[m]; 
                    if(i_cache_wen && i_way_select[m] && i_cache_addr == arb_addr) begin
                        for(n = 0; n < CACHE_DATA_SIZE_BYTES; n = n + 1) begin   
                            if(i_cache_ben[n]) begin
                                arb_data_2[m][n * 8 + 7 -: 8] <= i_cache_data[n * 8 + 7 -: 8]; 
                            end
                        end 
                    end
                end 
            end
        end
    endgenerate 

   

endmodule

module Wrapper;

    bind cache_4way cache_4way_props bind1(
        .clk(clk), 
        .reset_n(reset_n), 
        .i_way_select(i_way_select),  
        .i_cache_addr(i_cache_addr),
        .i_cache_wen(i_cache_wen), 
        .i_cache_ben(i_cache_ben),
        .i_cache_data(i_cache_data),
        .o_cache_data(o_cache_data), 
        .i_tag_wen(i_tag_wen), 
        .i_tag_data(i_tag_data),
        .o_tag_data(o_tag_data)    
    );

endmodule
