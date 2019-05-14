module params; 
    function integer clogb2 (input integer bit_depth); 
        for(clogb2=0; bit_depth>0; clogb2=clogb2+1) begin 
            bit_depth = bit_depth >> 1; 
        end 
    endfunction
endmodule 



`define CACHE_PARAM(PARAM, WIDTH, IDX) \
    localparam integer PARAM``_LSB = IDX``; \
    localparam integer PARAM``_MSB = WIDTH`` - 1; \
    localparam integer PARAM``_NUM = (1 << WIDTH``);

`define CACHE_PARAM_POW2(PARAM) \
    localparam integer PARAM``_POW2 = (1 << clogb2(PARAM``));

`define CACHE_4WAY() \
    localparam integer CACHE_WAY_WIDTH = 2; \
    localparam integer NUM_CACHE_WAY = (1 << CACHE_WAY_WIDTH); \

`define STATES \
    localparam integer STATE_READY = 3'd0, \
                STATE_WAIT_MEM_RDY = 3'd1, \
                STATE_WAIT_MEM_ACK = 3'd2, \
                STATE_REQUEST_LOOKUP = 3'd3, \
                STATE_LOOKUP = 3'd4, \
                STATE_LINE_FILL = 3'd5;

// specific params for cache related structures
// macrod for bloating and to avoid redef all the time 
`define CONTROLLER_PARAMS(LINE_WIDTH, LINE_IDX, SET_WIDTH, SET_IDX, ADDR_WIDTH, DATA_WIDTH) \
    `LOG \
    `CACHE_PARAM(``CACHE_LINE, LINE_WIDTH``, 0) \
    `CACHE_PARAM(``CACHE_SET, SET_WIDTH``, 0) \
    localparam integer CACHE_TAG_WIDTH = ADDR_WIDTH`` - (CACHE_SET_NUM + CACHE_LINE_NUM); \
    `CACHE_PARAM(``CACHE_TAG, CACHE_TAG_WIDTH, 0) \
    localparam integer CACHE_DATA_SIZE_BYTES = (DATA_WIDTH`` >> 3); \
    localparam integer CACHE_DATA_SIZE_BYTES_WIDTH = clogb2(CACHE_DATA_SIZE_BYTES); \
    localparam integer CACHE_LINE_SIZE_DATA = CACHE_LINE_NUM / CACHE_DATA_SIZE_BYTES; \
    `CACHE_4WAY(2) \
    `STATES 
    
// for accesing tag store values
`define TAG_BITS TAG_WIDTH - 1 : 0
`define VALID_BIT TAG_WIDTH

// easy access to addresses with these macros
`define TAG_RANGE CACHE_TAG_MSB : CACHE_TAG_LSB
`define LINE_RANGE CACHE_LINE_MSB : CACHE_LINE_LSB
`define SET_RANGE CACHE_SET_MSB : CACHE_SET_LSB
