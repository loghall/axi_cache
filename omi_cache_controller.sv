`include "props_pkg.sv" 
`include "intf_props_pkg.sv"
`include "constants.v"

import propsPkg::*; 
import intfPkg::*; 

module omi_props #(
    parameter integer ADDR_WIDTH = 10,
    parameter integer DATA_WIDTH = 32,
    parameter integer LINE_SIZE_BITS = 4,
    parameter integer SET_SIZE_BITS = 3
                     
)
(  
    // from CPU
    input wire clk, 
    input wire reset_n, 
    input wire i_cache_req, 
    input wire [ADDR_WIDTH - 1 : 0] i_cache_addr,
    input wire i_cache_wen, 
    input wire [ (DATA_WIDTH >> 3) - 1 : 0] i_cache_ben, 
    input wire [DATA_WIDTH - 1 : 0] i_cache_data, 
    input wire [7 : 0] i_cache_len,
    input wire o_cache_valid, 
    input wire [DATA_WIDTH - 1 : 0] o_cache_data,
    input wire o_cache_rdy,

    // to memory
    input wire o_mem_req, 
    input wire [ADDR_WIDTH - 1 : 0] o_mem_addr,
    input wire o_mem_wen, 
    input wire [ (DATA_WIDTH >> 3) - 1 : 0] o_mem_ben, 
    input wire [DATA_WIDTH - 1 : 0] o_mem_data, 
    input wire [7 : 0] o_mem_len,
    input wire i_mem_valid, 
    input wire [DATA_WIDTH - 1 : 0] i_mem_data,
    input wire i_mem_rdy,

    // internal registers that must remain stable during valid request
    input wire req,
    input wire rdy,
    input wire [ADDR_WIDTH - 1 : 0] addr,
    input wire wen,
    input wire [(DATA_WIDTH >> 3) - 1 : 0] iben,
    input wire [DATA_WIDTH - 1 : 0] data_out,
    input wire [2 : 0] state
);
    localparam integer STATE_READ_CACHE = 3'd3;

    reg [ADDR_WIDTH - 1 : 0] arb_addr;

    //------------------------------------------
    // Module Level Assumes As Noted in Specification
    //------------------------------------------
    `ADDR_ALIGN(clk, reset_n, i_cache_addr, assume, 0, i_cache_addr_assume)

    assume_arb_addr_constant : assume property(
        implies_1cycle(
            clk, !reset_n,
            1,
            $stable(arb_addr) && ((arb_addr % 4) == 0)
        )
    );

    // OMI Master signal assumes and asserts
    `REQ_PROP(clk, reset_n, i_cache_req, o_cache_rdy, assume, 0, assume_rdy)
    `REQ_SIGNAL_PROP(clk, reset_n, i_cache_req, i_cache_addr, assume, 0, assume_i_cache_addr)
    `REQ_SIGNAL_PROP(clk, reset_n, i_cache_req, i_cache_wen, assume, 0, assume_i_cache_wen)
    `REQ_SIGNAL_PROP(clk, reset_n, i_cache_req && i_cache_wen, i_cache_ben, assume, 0, assume_i_cache_ben)
    `REQ_SIGNAL_PROP(clk, reset_n, i_cache_req, i_cache_data, assume, 0, assume_i_cache_data)
    `REQ_SIGNAL_PROP(clk, reset_n, i_cache_req, i_cache_len, assume, 0, assume_i_cache_len)

    assume_i_cache_len_restrict: assume property(
        implies_instant(
            clk, !reset_n,
            1,
            i_cache_len <= 4
        )
    );


    // OMI Slave signal assumes and asserts
    `VALID_PROP(clk, reset_n, i_mem_rdy, i_mem_valid, o_mem_wen, o_mem_len, assume, 0, i_mem_valid_assume)

    assume_i_mem_low_when_req: assume property(
        implies_instant(
            clk, !reset_n,
            $fell(i_mem_rdy),
            $past(o_mem_req && i_mem_rdy, 1)
        )
    );

    //------------------------------------------
    // 
    // Global asserts for OMI MASTER
    // (from/to CPU)
    // 
    //------------------------------------------
    `REQ_PROP(clk, reset_n, i_cache_req, o_cache_rdy, assert, !reset_n, assert_ack_req)

    assert_data_0_invalid: assert property(
        implies_instant(
            clk, !reset_n,
            o_cache_valid == 0,
            o_cache_data == 0
        )
    );

    assert_data_0_until_req: assert property(
        implies_instant(
            clk, !reset_n,
            o_cache_rdy == 1,
            o_cache_data == 0
        )
    );

    assert_valid_0_when_rdy: assert property(
        implies_instant(
            clk, !reset_n,
            o_cache_rdy,
            !o_cache_valid
        )
    );

    /*
    assert_valid_thru_reads: assert property(
        implies_1cycle(
            clk, !reset_n,
            rdy && len_ctr < i_cache_len_r && !i_cache_wen_r && state == STATE_READ_CACHE,
            o_cache_valid
        )
    );
    */

    //------------------------------------------
    // 
    // Global asserts for OMI MASTER
    // (from/to CPU)
    // 
    //------------------------------------------
    `REQ_PROP(clk, reset_n, o_mem_req, i_mem_rdy, assert, !reset_n, assert_mem_req)
    `REQ_SIGNAL_PROP(clk, reset_n, o_mem_req, o_mem_addr, assert, !reset_n, assert_o_mem_addr)
    `REQ_SIGNAL_PROP(clk, reset_n, o_mem_req, o_mem_wen, assert, !reset_n, assert_o_mem_wen)
    `REQ_SIGNAL_PROP(clk, reset_n, o_mem_req && o_mem_wen, o_mem_ben, assert, !reset_n, assert_o_mem_ben)
    `REQ_SIGNAL_PROP(clk, reset_n, o_mem_req, o_mem_data, assert, !reset_n, assert_o_mem_data)
    `REQ_SIGNAL_PROP(clk, reset_n, o_mem_req, o_mem_len, assert, !reset_n, assert_o_mem_len)

    //------------------------------------------
    // 
    // Aux code
    // 
    //------------------------------------------
    integer len_ctr;
    reg [7 : 0] i_cache_len_r;
    reg i_cache_wen_r;

    always@(posedge clk) begin
        if(!reset_n) begin
            len_ctr <= 0;
        end
        else begin
            if(i_cache_req && o_cache_rdy) begin
                i_cache_len_r <= i_cache_len;
                len_ctr <= 0;
                i_cache_wen_r <= i_cache_wen;
            end
            else if(rdy && !i_cache_wen_r) begin
                len_ctr <= len_ctr + 1;
            end
        end
    end

endmodule

module Wrapper;

    bind cache omi_props bind1(
        .clk(clk),
        .reset_n(reset_n), 
        .i_cache_req(i_cache_req), 
        .i_cache_addr(i_cache_addr),
        .i_cache_wen(i_cache_wen), 
        .i_cache_ben(i_cache_ben),
        .i_cache_data(i_cache_data), 
        .i_cache_len(i_cache_len),
        .o_cache_valid(o_cache_valid),
        .o_cache_data(o_cache_data),
        .o_cache_rdy(o_cache_rdy),

        .o_mem_req(o_mem_req), 
        .o_mem_addr(o_mem_addr),
        .o_mem_wen(o_mem_wen), 
        .o_mem_ben(o_mem_ben),
        .o_mem_data(o_mem_data), 
        .o_mem_len(o_mem_len),

        .i_mem_valid(i_mem_valid),
        .i_mem_data(i_mem_data),
        .i_mem_rdy(i_mem_rdy),

        .req(req),
        .rdy(rdy),
        .addr(addr),
        .wen(wen),
        .iben(iben),
        .data_out(data_out),
        .state(state)

    );

endmodule

