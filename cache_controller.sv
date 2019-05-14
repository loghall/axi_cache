`include "props_pkg.sv" 
`include "intf_props_pkg.sv"
`include "constants.v"

`define TAG TAG_MSB : TAG_LSB
`define LINE LINE_MSB : LINE_LSB
`define SET SET_MSB : SET_LSB 
`define CACHE_ADDR SET_MSB : 0 

import propsPkg::*; 
import intfPkg::*; 

module cache_props #(
    parameter integer ADDR_WIDTH = 10,
    parameter integer DATA_WIDTH = 32,
    parameter integer LINE_WIDTH = 4,
    parameter integer SET_WIDTH = 3,
    parameter integer WAY_WIDTH = 2,
    parameter integer TAG_WIDTH = 3,
    parameter integer DATA_SIZE_BYTES = 4, 
    parameter integer LINE_LSB = 0,
    parameter integer LINE_MSB = 3,
    parameter integer SET_LSB = 4,
    parameter integer SET_MSB = 6,
    parameter integer TAG_LSB = 7,
    parameter integer TAG_MSB = 9,
    parameter integer NUM_SETS = 8, 
    parameter integer NUM_WAYS = 4,
    parameter integer LINE_SIZE_BYTES = 16
)
(  
    // clk and reset
    clk, 
    reset_n, 
    
    // from CPU interface req signals
    i_req, 
    i_addr,
    i_wen, 
    i_ben,
    i_data, 
    o_data,
    o_rdy,

    // to memory CPU interface req signals 
    o_mem_req, 
    o_mem_addr,
    o_mem_wen, 
    o_mem_ben,
    o_mem_len,
    o_mem_data, 
    i_mem_rdy, 
    i_mem_valid,
    i_mem_data, 

    addr_way, 
    cache_addr,
    cache_wen, 
    cache_ben,
    cache_wdata,
    cache_rdata,   
    tag_wen, 
    tag_wdata, 
    tag_rdata,

    lookup_req,
    addr_tag,
    addr_set,
    addr_tag_store,
    lookup_valid,
    way_select,
    hit
);
    localparam integer CACHE_ADDR_WIDTH = (LINE_WIDTH + SET_WIDTH); 
      
    //------------------------------------------
    // 
    // ports
    // 
    //------------------------------------------
    // clk and reset (active low) 
    input wire clk;
    input wire reset_n; 
    input wire i_req;
    input wire [ADDR_WIDTH - 1 : 0] i_addr;
    input wire i_wen;
    input wire [DATA_SIZE_BYTES - 1 : 0] i_ben;
    input wire [DATA_WIDTH - 1 : 0] i_data;
    input wire [DATA_WIDTH - 1 : 0] o_data;
    input wire o_rdy;

    // to/from MEM cig
    input wire o_mem_req; 
    input wire [ADDR_WIDTH - 1 : 0] o_mem_addr;
    input wire o_mem_wen; 
    input wire [DATA_SIZE_BYTES - 1 : 0]  o_mem_ben;
    input wire [7 : 0] o_mem_len;
    input wire [DATA_WIDTH - 1 : 0] o_mem_data; 
    input wire i_mem_rdy; 
    input wire i_mem_valid;
    input wire [DATA_WIDTH - 1 : 0] i_mem_data; 

    // cache and signals 
    input wire [NUM_WAYS - 1 : 0] addr_way; 
    input wire [CACHE_ADDR_WIDTH - 1 : 0] cache_addr;
    input wire cache_wen; 
    input wire [DATA_SIZE_BYTES - 1 : 0] cache_ben;
    input wire [DATA_WIDTH - 1 : 0] cache_wdata; 
    input wire [DATA_WIDTH - 1 : 0] cache_rdata [0 : NUM_WAYS - 1];   
    input wire tag_wen; 
    input wire [TAG_WIDTH + 1 - 1 : 0] tag_wdata; 
    input wire [TAG_WIDTH + 1 - 1 : 0] tag_rdata [0 : NUM_WAYS - 1];  

    // cache 4 way signals
    input wire lookup_req, lookup_valid, hit;   
    input wire [TAG_WIDTH - 1: 0] addr_tag;  
    input wire [SET_WIDTH - 1: 0] addr_set; 
    input wire [TAG_WIDTH + 1 - 1 : 0] addr_tag_store [NUM_WAYS - 1 : 0];  
    input wire [NUM_WAYS - 1 : 0] way_select; 

    //------------------------------------------
    // 
    // Arb addr signals
    // 
    //------------------------------------------
    reg [ADDR_WIDTH - 1 : 0] arb_addr; 
    reg arb_addr_req, arb_cached, arb_cache_fill; 
    reg [TAG_WIDTH + 1 - 1 : 0] arb_set_tag [0 : NUM_WAYS - 1];  
    reg [TAG_WIDTH + 1 - 1 : 0] arb_set_tag_check [0 : NUM_WAYS - 1];  
    reg [NUM_WAYS - 1 : 0] arb_way;

    reg [DATA_WIDTH - 1 : 0] arb_data;
    reg [DATA_WIDTH - 1 : 0] arb_mem_wdata;
    reg [ADDR_WIDTH - 1 : 0] arb_mem_waddr;
    reg [DATA_SIZE_BYTES - 1 : 0] arb_mem_ben; 
    
    //------------------------------------------
    // 
    // Internals 
    // 
    //------------------------------------------
    reg [DATA_WIDTH - 1 : 0] i_data_r;
    reg [ADDR_WIDTH - 1 : 0] i_addr_r;
    reg [DATA_SIZE_BYTES - 1 : 0] i_ben_r; 
    reg [DATA_SIZE_BYTES - 1 : 0]  i_wen_r;
    integer mem_valid_ctr, j;

    wire [WAY_WIDTH - 1 : 0] addr_way_decoded; 

    //------------------------------------------
    // 
    // Global assumes/asserts for req/rdy interfacing 
    // 
    //------------------------------------------
    `REQ_PROP(clk, reset_n, i_req, o_rdy, assume, 0, i_req_assume)
    `REQ_PROP(clk, reset_n, o_mem_req, i_mem_rdy, assert, 0, o_mem_req_assert)
    `RDY_PROP(clk, reset_n, o_rdy, i_req, assert, !reset_n, o_rdy_assert)
    `RDY_PROP(clk, reset_n, i_mem_rdy, o_mem_req, assume, 0, i_mem_rdy_assume)
    `RDY_SIGNAL_PROP(clk, reset_n, o_rdy, o_data, assert, !reset_n, o_data_assert)
    `VALID_PROP(clk, reset_n, i_mem_rdy, i_mem_valid, o_mem_wen, o_mem_len, assume, 0, i_mem_valid_assume)
    `ADDR_ALIGN(clk, reset_n, i_addr, assume, 0, i_addr_assume)
    `ADDR_ALIGN(clk, reset_n, o_mem_addr, assert, !reset_n, o_mem_addr_assert);

    //------------------------------------------
    // 
    // Global assumes for arb addr 
    // 
    //------------------------------------------
    assume_arb_addr_constant : assume property( // some constant addr 
        implies_1cycle(
            clk, !reset_n,
            1,
            $stable(arb_addr) && ((arb_addr % 4) == 0)
        )
    );

    assume_correct_cache_read : assume property( // assume correct read if data in cache
        implies_1cycle(
            clk, !reset_n,
            cache_addr == arb_addr[`CACHE_ADDR] && arb_cached && !o_rdy,
            cache_rdata[addr_way_decoded] == arb_data
        )
    );

    assume_correct_cache_rdy_read : assume property( // assume correct read if data in cache
        implies_1cycle(
            clk, !reset_n,
            i_addr == arb_addr && arb_cached && o_rdy,
            cache_rdata[addr_way_decoded] == arb_data
        )
    );

    assume_mem_read_correct : assume property( // assume correct read from memory 
        implies_instant(
            clk, !reset_n,
            i_addr_r[`SET] == arb_addr[`SET] && i_mem_valid && mem_valid_ctr == arb_addr[`LINE],
            i_mem_data == arb_data 
        ) 
    );

    assume_lookup_valid_set : assume property( // assume lookup valid signal
        implies_1cycle(
            clk, !reset_n,
            lookup_req,
            $rose(lookup_valid)
        ) 
    );

    assume_lookup_falls : assume property( // assume valid falls 
        implies_1cycle(
            clk, !reset_n,
            lookup_valid,
            $fell(lookup_valid)
        ) 
    );

    //------------------------------------------
    // 
    // Global assumes for cache 4 way
    // 
    //------------------------------------------

    assume_way_select_onehot: assume property(
        implies_1cycle(
            clk, !reset_n,
            $rose(lookup_req),
            $onehot(way_select) == 1)
    );

    assume_arb_addr_hit: assume property(
        iff_instant(
            clk, !reset_n,
            1,
            $past($rose(lookup_req) && i_addr_r[`SET] == arb_addr[`SET] && i_addr_r[`TAG] == arb_addr[`TAG] && arb_cached, 1),
            hit
        )
    );

    assume_arb_addr_cache_hit: assume property(
        implies_1cycle(
            clk, !reset_n,
            $rose(lookup_req) && i_addr_r[`SET] == arb_addr[`SET] && i_addr_r[`TAG] == arb_addr[`TAG] && arb_cached,
            way_select[addr_way_decoded] == 1
        )
    );

    assume_lookup_req_low_valid: assume property(
        implies_instant(
            clk, !reset_n,
            $rose(lookup_valid),
            $past(lookup_req, 1) == 1
        )
    );

    //------------------------------------------
    // 
    // Global asserts for arb addr 
    // 
    //------------------------------------------
    assert_read_correct : assert property( // reads are always correct to this address
        implies_instant(
            clk, !reset_n,
            $rose(o_rdy) && i_addr_r == arb_addr && i_wen_r == 0,
            o_data == arb_data
        ) 
    );

    /*
    assert_write_thru : assert property( // write through for all writes 
        implies_instant(
            clk, !reset_n,
            $rose(o_rdy) && i_addr_r == arb_addr && i_wen_r == 1,
            arb_mem_waddr == arb_addr && arb_mem_ben == i_ben_r && arb_mem_wdata == i_data_r
        ) 
    );
    */

    /*
    assert_lookup_req_1cycle : assert property( // request only high for a single cycle
        implies_1cycle(
            clk, !reset_n,
            lookup_req,
            !lookup_req
        )
    );

    assert_lookup_req_wait : assert property( // assert lookup valid signal (note, assume this in cache controller)
        implies_instant(
            clk, !reset_n,
            $rose(lookup_req),
            !lookup_valid
        ) 
    );
    */

    /*
    genvar i; 
    for(i = 0; i < NUM_WAYS; i = i + 1) begin : gen_tag_update
        assert_tag_update : assert property( // assert tags updated correct
            implies_1cycle(
                clk, !reset_n,
                $rose(o_rdy) && arb_addr[`SET] == i_addr_r[`SET],
                arb_set_tag_check[i] == arb_set_tag[i]
            ) 
        );
    end 
    */

    //------------------------------------------
    // 
    // high level controller tracker 
    // 
    //------------------------------------------
    always@(posedge clk) begin
        if(!reset_n) begin
            i_addr_r <= 0;
            i_wen_r <= 0; 
            i_ben_r <= 0;
            i_data_r <= 0; 

            mem_valid_ctr <= 0; 
        end 
        else begin 
            if(i_req && o_rdy) begin
                i_addr_r <= i_addr;
                i_wen_r <= i_wen; 
                i_ben_r <= i_ben;
                i_data_r <= i_data; 
                
                mem_valid_ctr <= 0; 
            end
            else if(i_mem_valid) begin
                mem_valid_ctr <= mem_valid_ctr + 4; 
            end
        end
    end

    //------------------------------------------
    // 
    // aux code for arb addr  and bb assumptions
    // 
    //------------------------------------------
    assign addr_way_decoded =   (addr_way[0]) ? 0 : 
                                (addr_way[1]) ? 1 : 
                                (addr_way[2]) ? 2 : 
                                3; 
    // arb_addr logistics 
    always@(posedge clk) begin
        integer i; 
        if(!reset_n) begin
            arb_cached <= 0; 
            arb_way <= 0;
            arb_addr_req <= 0;
            
            for(i = 0; i < NUM_WAYS; i = i + 1) begin
                arb_set_tag[i] <= {{TAG_WIDTH{1'b0}}, 1'b0};
            end 
        end 
        else begin
            if(i_req && o_rdy && i_addr[`SET] == arb_addr[`SET]) begin
                arb_addr_req <= 1; 
            end 
            else if($rose(o_rdy) && arb_addr_req) begin
                arb_addr_req <= 0; 
                
                // update our tags 
                arb_set_tag[addr_way_decoded] <= {1'b1, i_addr_r[`TAG]}; 

                // now cached if same line 
                if(i_addr_r[`TAG] == arb_addr[`TAG]) begin
                    arb_cached <= 1; 
                    arb_way <= addr_way_decoded; 
                end 
                else if(addr_way_decoded == arb_way) begin // otherwise we may have gotten evicted 
                    arb_cached <= 0; 
                end 
            end  
        end 
    end

    // arb mem requests
    always@(posedge clk) begin
        if(!reset_n) begin
            arb_mem_waddr <= 0;
            arb_mem_wdata <= 0;
            arb_mem_ben <= 0; 
        end     
        else begin
            if(arb_addr_req && o_mem_req && i_addr_r == arb_addr && o_mem_wen) begin
                arb_mem_waddr <= o_mem_addr;
                arb_mem_wdata <= o_mem_data;
                arb_mem_ben <= o_mem_ben; 
            end 
        end 
    end 

    // arb value updates
    always@(posedge clk) begin
        integer n; 
        if(!reset_n) begin
            arb_data <= 0;
            arb_cache_fill <= 0;
            
        end 
        else begin
            if($rose(o_rdy) && arb_addr_req) begin
                arb_cache_fill <= 0;
                
                if(i_addr_r == arb_addr && i_wen_r) begin
                    for(n = 0; n < DATA_SIZE_BYTES; n = n + 1) begin   
                        if(i_ben_r[n]) begin
                            arb_data[n * 8 + 7 -: 8] <= i_data_r[n * 8 + 7 -: 8]; 
                        end
                    end 
                end
            end 
            else if(arb_addr_req && arb_addr[`TAG] == i_addr_r[`TAG] && o_mem_req && !o_mem_wen) begin
                arb_cache_fill <= 1; 
            end 
            else if(arb_cache_fill) begin
                if(i_mem_valid && mem_valid_ctr == arb_addr[`LINE]) begin 
                    arb_data <= i_mem_data; 
                end 
                else if (i_mem_rdy) begin  
                    arb_cache_fill <= 0; 
                end
            end
        end
    end

    //------------------------------------------
    // 
    // track all updates to arb_set tag store
    // 
    //------------------------------------------
    always@(posedge clk) begin
        if(!reset_n) begin
            for(j = 0; j < NUM_WAYS; j = j + 1) begin
                arb_set_tag_check[j] <= {{TAG_WIDTH{1'b0}}, 1'b0};
            end 
        end
        else begin
            if(tag_wen && cache_addr[`SET] == arb_addr[`SET]) begin
                arb_set_tag_check[addr_way_decoded] <= tag_wdata; 
            end
        end
    end 

endmodule

module Wrapper;

    bind cache_ctrl cache_props bind1(
        .clk(clk),
        .reset_n(reset_n),
        .i_req(i_req),
        .i_addr(i_addr),
        .i_wen(i_wen),
        .i_ben(i_ben),
        .i_data(i_data),
        .o_data(o_data),
        .o_rdy(o_rdy),
        .o_mem_req(o_mem_req),
        .o_mem_addr(o_mem_addr),
        .o_mem_wen(o_mem_wen),
        .o_mem_ben(o_mem_ben),
        .o_mem_len(o_mem_len),
        .o_mem_data(o_mem_data),
        .i_mem_rdy(i_mem_rdy),
        .i_mem_valid(i_mem_valid),
        .i_mem_data(i_mem_data),
        .addr_way(addr_way),
        .cache_addr(cache_addr),
        .cache_wen(cache_wen),
        .cache_ben(cache_ben),
        .cache_wdata(cache_wdata),
        .cache_rdata(cache_rdata),
        .tag_wen(tag_wen),
        .tag_wdata(tag_wdata),
        .tag_rdata(tag_rdata),
        .lookup_req(lookup_req),
        .addr_tag(addr_tag), 
        .addr_set(addr_set),
        .addr_tag_store(addr_tag_store), 
        .lookup_valid(lookup_valid), 
        .hit(hit),
        .way_select(way_select)
    );

endmodule
