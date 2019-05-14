module cache_4way # (
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

    //---------------------------------------------
    //
    // Port definition 
    //
    //---------------------------------------------
    input clk;
    input reset_n; 

    // same way select and address for cache and tag store
    input wire [NUM_CACHE_WAY - 1 : 0] i_way_select; 
    input wire [CACHE_ADDR_WIDTH - 1 : 0] i_cache_addr; 

    // data cache signals 
    input wire i_cache_wen; 
    input wire [CACHE_DATA_SIZE_BYTES - 1 : 0] i_cache_ben;
    input wire [CACHE_DATA_WIDTH - 1 : 0] i_cache_data;
    output reg [CACHE_DATA_WIDTH - 1 : 0] o_cache_data [0 : NUM_CACHE_WAY - 1]; 

    // tag store signals 
    input wire i_tag_wen; 
    input wire [CACHE_TAG_WIDTH - 1 : 0] i_tag_data;
    output reg [CACHE_TAG_WIDTH - 1 : 0] o_tag_data [0 : NUM_CACHE_WAY - 1];  

    // generate all the cache ways! yay verilog! 
    genvar i; 
    generate 
        for(i = 0; i < NUM_CACHE_WAY; i = i + 1) begin : gen_cache_way
            cache_way # (
                .CACHE_WAY_ADDR_WIDTH(CACHE_ADDR_WIDTH), 
                .CACHE_WAY_DATA_WIDTH(CACHE_DATA_WIDTH), 
                .CACHE_WAY_DATA_SIZE_BYTES(CACHE_DATA_SIZE_BYTES), 
                .CACHE_WAY_TAG_WIDTH(CACHE_TAG_WIDTH),
                .CACHE_WAY_TAG_SIZE_BYTES(CACHE_TAG_SIZE_BYTES)
            ) _cache_way (
                .clk(clk),
                .reset_n(reset_n),

                .i_cache_way_addr(i_cache_addr),
                .i_cache_way_wen(i_cache_wen && i_way_select[i]), // i_way_select acts as a chip select 
                .i_cache_way_ben(i_cache_ben),
                .i_cache_way_data(i_cache_data),
                .o_cache_way_data(o_cache_data[i]), 

                .i_tag_wen(i_tag_wen && i_way_select[i]), // i_way_select acts a chip select 
                .i_tag_data(i_tag_data),
                .o_tag_data(o_tag_data[i])  
            );
        end 
    endgenerate

endmodule

