module cache_way # (
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

    //---------------------------------------------
    //
    // Local params 
    //
    //---------------------------------------------

    // up cast the tag to the nearest byte to work with the rams
    localparam integer TAG_WIDTH_UPCAST = (8 * ( (CACHE_WAY_TAG_WIDTH / 8) + (CACHE_WAY_TAG_WIDTH % 8 != 0))); 

    //---------------------------------------------
    //
    // Port definition 
    //
    //---------------------------------------------
    
    // clk and reset (active low) 
    input clk;
    input reset_n; 
    
    // same addr for tag and data
    input wire [CACHE_WAY_ADDR_WIDTH - 1 : 0] i_cache_way_addr;  // input address

    // data store related signals
    input wire i_cache_way_wen; // only data write if wen is HIGH
    input wire [CACHE_WAY_DATA_SIZE_BYTES - 1 : 0] i_cache_way_ben; // byte enable
    input wire [CACHE_WAY_DATA_WIDTH - 1 : 0] i_cache_way_data; // input write data
    output wire [CACHE_WAY_DATA_WIDTH - 1 : 0] o_cache_way_data;  // output read data
    
    // tag store related signals
    input wire i_tag_wen; // only write tag if wen is HIGH
    input wire [CACHE_WAY_TAG_WIDTH - 1 : 0] i_tag_data; // input tag write data
    output wire [CACHE_WAY_TAG_WIDTH - 1 : 0] o_tag_data; // output tag read data 

    //---------------------------------------------
    //
    // Instantiation of cache and tag store RAMs
    //
    //---------------------------------------------
    
    ram # (
        .MEM_ADDR_WIDTH(CACHE_WAY_ADDR_WIDTH),
        .MEM_DATA_WIDTH(CACHE_WAY_DATA_WIDTH),
        .MEM_DATA_SIZE_BYTES(CACHE_WAY_DATA_SIZE_BYTES)
    ) 
    cache_way (
        .clk(clk),
        .reset_n(reset_n), 
        .i_addr(i_cache_way_addr), 
        .i_wen(i_cache_way_wen), 
        .i_ben(i_cache_way_ben),
        .i_write_data(i_cache_way_data),
        .o_read_data(o_cache_way_data)
    );

    ram # (
        .MEM_ADDR_WIDTH(CACHE_WAY_ADDR_WIDTH),
        .MEM_DATA_WIDTH(TAG_WIDTH_UPCAST),
        .MEM_DATA_SIZE_BYTES(CACHE_WAY_TAG_SIZE_BYTES)
    ) 
    tag_store (
        .clk(clk),
        .reset_n(reset_n), 
        .i_addr(i_cache_way_addr), 
        .i_wen(i_tag_wen), 
        .i_ben({CACHE_WAY_TAG_SIZE_BYTES{1'b1}}),
        .i_write_data(i_tag_data),
        .o_read_data(o_tag_data[CACHE_WAY_TAG_WIDTH - 1 : 0]) // may or may not be 8 bits, so we upcast! :)
    );

endmodule 
