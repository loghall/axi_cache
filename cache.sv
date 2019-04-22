`include "props_pkg.sv" 

import propsPkg::*; 

module cache_props(  
    input wire clk, 
    input wire reset_n, 
    input wire faux_rst,
    input wire [31 : 0] cpu_addr, 
    input wire [31 : 0] cpu_data_in, 
    input wire cpu_we,
    input wire cpu_re,  
    input wire [3 : 0] cpu_wstb,
    input wire [31 : 0] cpu_data_out,
    input wire [31 : 0] mem_addr,  
    input wire [31 : 0] mem_data_in, 
    input wire [3 : 0] mem_wstb,
    input wire mem_data_valid, 
    input wire mem_last,
    input wire miss, 

    input [7 : 0] data_cache [63 : 0][3 : 0][127 : 0], 
    input [16 : 0] tag_array [63 : 0][3 : 0], 
    input valid_bits [63 : 0][3 : 0], 
    input state
);
    // cache states 
    localparam READY = 1'b0, REPLACE = 1'b1; 

    // latch CPU signals 
    reg [31 : 0] latch_cpu_data_in;
    reg [31 : 0] latch_cpu_addr;  
    reg [16 : 0] latch_tag;  
    reg [5 : 0] latch_set_idx; 
    reg [1 : 0] latch_way_idx; 
    reg [6 : 0] latch_cpu_line_idx; 

    // latch mem signals 
    reg [31 : 0] latch_mem_data_in; 
    reg [31 : 0] latch_mem_addr;
    reg [6 : 0] latch_mem_line_idx;
    reg [4 : 0] counter; 
    reg rst_seen;

    wire req_now = cpu_re || cpu_we; 

    // generate set, way for current address (NOW); used to determine misses 
    wire [16 : 0] tag_now = cpu_addr[31 : 15]; 
    wire [5 : 0] set_idx_now = cpu_addr[14 : 9]; 
    wire [1 : 0] way_idx_now = cpu_addr[8 : 7];

    // generate miss information for current address (NOW) 
    wire tag_miss_now = tag_array[set_idx_now][way_idx_now] != tag_now; 
    wire valid_miss_now = valid_bits[set_idx_now][way_idx_now] == 1'b0; 
    wire miss_now = tag_miss_now || valid_miss_now; 
    
    // generate cache data using latched address information 
    wire [6 : 0] latch_line_idx = (state == REPLACE) ? latch_mem_line_idx : latch_cpu_line_idx; 
    wire [7 : 0] byte0 = data_cache[latch_set_idx][latch_way_idx][latch_line_idx];
    wire [7 : 0] byte1 = data_cache[latch_set_idx][latch_way_idx][latch_line_idx + 1];
    wire [7 : 0] byte2 = data_cache[latch_set_idx][latch_way_idx][latch_line_idx + 2];
    wire [7 : 0] byte3 = data_cache[latch_set_idx][latch_way_idx][latch_line_idx + 3];
    wire [31 : 0] cache_data = {byte3, byte2, byte1, byte0}; 

    genvar i, j, k, l; 

    ///////////////////////////////////////////////////////////
    //
    // ASSUMES
    //
    //////////////////////////////////////////////////////////

    // cpu addr aligned
    assume_cpu_aligned: assume property(iff_instant(
                                clk, faux_rst,
                                1, 
                                cpu_addr % 4, 
                                0
    )); 
    // mem addr aligned
    assume_mem_aligned: assume property(iff_instant(
                                clk, faux_rst,
                                1, 
                                mem_addr % 4, 
                                0
    )); 
    // no read/write at same time 
    assume_mutex_rw: assume property(iff_instant(
                                clk, faux_rst, 
                                1, 
                                cpu_we && cpu_re, 
                                0
    )); 
    // only r/w while ready
    assume_rw_only_in_ready: assume property(iff_instant(
                                clk, faux_rst,
                                $rose(cpu_we) || $rose(cpu_re), 
                                state, 
                                READY
    )); 
    // no r/w signal while handling miss 
    assume_no_rw_while_busy: assume property(iff_instant(
                                clk, faux_rst, 
                                state == REPLACE, 
                                cpu_we || cpu_re, 
                                0
    )); 
    // mem_wstb = '1111
    assume_const_mem_stb: assume property(iff_instant(
                                clk, faux_rst, 
                                1, 
                                mem_wstb, 
                                4'b1111
    )); 
    // 1 cycle we
    assume_we_only_1_cycle: assume property(implies_1cycle(
                                clk, faux_rst, 
                                cpu_we, 
                                !cpu_we
    )); 
    // 1 cycle re
    assume_re_only_1_cycle: assume property(implies_1cycle(
                                clk, faux_rst, 
                                cpu_re, 
                                !cpu_re
    )); 
    // mem_addr == cpu_addr if not handling miss
    assume_mem_addr_no_miss: assume property(iff_instant(
                                clk, faux_rst, 
                                state == READY, 
                                mem_addr, 
                                cpu_addr
    )); 
    // mem_last == 0 if not handling miss
    assume_mem_last_no_miss: assume property(iff_instant(
                                clk, faux_rst, 
                                state == READY, 
                                mem_last, 
                                0
    )); 
    // mem_data_valid == 0 if not handling miss
    assume_mem_valid_no_miss: assume property(iff_instant(
                                clk, faux_rst, 
                                state == READY, 
                                mem_data_valid, 
                                0
    )); 
    // mem_address increments by word size when filling cache line
    assume_inc_mem_addr: assume property(iff_1cycle(
                                clk, faux_rst, 
                                state == REPLACE && counter != 31 && mem_data_valid, 
                                latch_mem_addr + 4, 
                                mem_addr
    )); 
    // mem_address only changes after data valid
    assume_chg_mem_addr_on_valid: assume property(iff_instant(
                                clk, faux_rst, 
                                $changed(mem_addr), 
                                $past(mem_data_valid, 1),
                                1
    ));
    // mem last only asserted for last word
    assume_mem_last_set: assume property(iff_instant(
                                clk, faux_rst, 
                                state == REPLACE, 
                                counter == 31, 
                                mem_last
    )); 
    // 1 cycle mem last
    assume_mem_last_1_cycle: assume property(implies_1cycle(
                                clk, faux_rst, 
                                mem_last, 
                                !mem_last
    )); 
    // 1 cycle data_valid
    assume_mem_data_valid_1_cycle: assume property(implies_1cycle(
                                clk, faux_rst, 
                                mem_data_valid, 
                                !mem_data_valid
    )); 
    // if last, data must be valid
    assume_mem_last_implies_valid_1: assume property(implies_instant(
                                clk, faux_rst, 
                                mem_last,
                                mem_data_valid
    )); 
    // if data is not valid, it is not the last data 
    assume_mem_last_implies_valid_2: assume property(implies_instant(
                                clk, faux_rst, 
                                !mem_data_valid, 
                                !mem_last
    )); 
    //  cpu data assumes... 
    assume_cpu_data_in: assume property(iff_instant(
                                clk, faux_rst, 
                                1, 
                                cpu_data_in == 32'hAAAAAAAA || cpu_data_in == 32'h55555555 || cpu_data_in == 32'hFFFFFFFF || cpu_data_in == 32'h0, 
                                1
    ));
    // mem data assumes
    assume_mem_data_in: assume property(iff_instant(
                                clk, faux_rst, 
                                1,
                                (mem_data_in == 32'hAAAAAAAA || mem_data_in == 32'h55555555 || mem_data_in == 32'hFFFFFFFF || mem_data_in == 32'h0),
                                1
    ));
    // simulates actual operating scenario; when data is ready from mem (i.e. mem_data_in changed), make data valid
    assume_mem_data_valid_when_data: assume property(implies_instant(
                                clk, faux_rst, 
                                $changed(mem_data_in), 
                                $rose(mem_data_valid)
    ));
    // misc for jaspergold reset stuff; reset asserts automatically if it hasn't been triggered
    assume_force_reset: assume property(iff_instant(
                                clk, faux_rst, 
                                !rst_seen,
                                reset_n, 
                                0
    ));
    // misc for jasper gold reset stuff; reset stays high once its triggered
    assume_reset_deassert: assume property(@(posedge clk) rst_seen |-> reset_n == 1);
    
    //////////////////////////////////////////////////////////
    //
    // asserts !!!
    //
    //////////////////////////////////////////////////////////
    
    // -------------------- required state transitions --------------------
    // transition to replace on a miss 
    assert_rdy_to_rep: assert property(iff_1cycle(
                                clk, faux_rst, 
                                (state == READY) && req_now && miss_now, 
                                state, 
                                REPLACE
    )); 
    // transition to ready when done servicing miss 
    assert_rep_to_rdy: assert property(iff_1cycle(
                                clk, faux_rst, 
                                (state == REPLACE) && mem_last, 
                                state, 
                                READY
    )); 

    // -------------------- state transition checkers --------------------
    // if we did transition from rdy->rep, a miss and a request must have been asserted last cycle. 
    assert_rdy_to_rep_chk: assert property(iff_instant(
                                clk, faux_rst, 
                                (state == REPLACE) && $past(state == READY, 1), 
                                $past(miss_now && req_now, 1), 
                                1
    )); 
    // if we did transition from rep->rdy, mem_last must have been asserted last cycle.
    assert_rep_to_rdy_chk: assert property(iff_instant(
                                clk, faux_rst, 
                                (state == READY) && $past(state == REPLACE, 1), 
                                $past(mem_last, 1), 
                                1
    )); 

    // -------------------- r/w value checks --------------------
    // check cpu_data_out if no miss on read 
    assert_read_no_miss: assert property(iff_1cycle(
                                clk, faux_rst, 
                                (state == READY) && cpu_re && !miss_now, 
                                cache_data, 
                                cpu_data_out
    )); 
    // check cache data if no miss on write
    assert_write_no_miss: assert property(iff_1cycle(
                                clk, faux_rst, 
                                (state == READY) && cpu_we && !miss_now, 
                                cache_data, 
                                latch_cpu_data_in
    ));
    // check cache data if mem data valid 
    assert_cache_fill: assert property(iff_1cycle(
                                clk, faux_rst, 
                                (state == REPLACE) && mem_data_valid, 
                                cache_data, 
                                latch_mem_data_in
    )); 
    // assert tag updated correctly after replacement
    assert_tag_update: assert property(iff_1cycle(
                                clk, faux_rst, 
                                (state == REPLACE) && mem_last, 
                                tag_array[latch_set_idx][latch_way_idx], 
                                latch_tag
    )); 
    // assert valid updated correctly after replacement 
    assert_valid_update_valud: assert property(iff_1cycle(
                                clk, faux_rst, 
                                state == REPLACE && mem_last, 
                                valid_bits[latch_set_idx][latch_way_idx], 
                                1'b1
    ));

    // -------------------- signal checks --------------------
    // miss only high while in replace
    assert_miss_high: assert property(iff_instant(
                                clk, faux_rst, 
                                1, 
                                state == REPLACE, 
                                miss
    )); 

    // -------------------- hold value checks --------------------
    // assert tags only change when they should
    for(i = 0; i < 64; i = i + 1) begin: hold_value_tag1
        for(j = 0; j < 4; j = j + 1) begin: hold_value_tag2
            assert_tag_hold_value: assert property(iff_instant(
                                        clk, faux_rst, 
                                        $changed(tag_array[i][j]), 
                                        $past(i == latch_set_idx && j == latch_way_idx && state == REPLACE && mem_last, 1), 
                                        1
            ));
        end
    end
    // assert valids only change when they should 
    for(i = 0; i < 64; i = i + 1) begin: hold_value_valid1
        for(j = 0; j < 4; j = j + 1) begin: hold_value_valid2
            assert_valid_hold_value: assert property(iff_instant(
                                        clk, faux_rst, 
                                        $changed(valid_bits[i][j]), 
                                        $past((i == latch_set_idx && j == latch_way_idx && state == REPLACE && mem_last) || !reset_n, 1), 
                                        1
            ));
        end
    end
    // assert cache bytes only update when they should
    for(i = 0; i < 64; i = i + 1) begin: hold_value_cache1
        for(j = 0; j < 4; j = j + 1) begin: hold_value_cache2
            for(k = 0; k < 128; k = k + 1) begin: hold_value_cache3
                assert_cache_hold_value_hit: assert property(iff_instant(
                    clk, faux_rst, 
                    $changed(data_cache[i][j][k]), 
                    $past(state == READY && req_now && !miss_now && i == latch_set_idx && j == latch_way_idx && ({(k >> 2), 2'b00} == latch_cpu_line_idx) && cpu_wstb[k % 4] == 1, 1), 
                    1
                )); 
                assert_cache_hold_value_miss: assert property(iff_instant(
                    clk, faux_rst, 
                    $changed(data_cache[i][j][k]), 
                    $past(state == REPLACE && mem_data_valid && i == latch_set_idx && j == latch_way_idx && ({(k >> 2), 2'b00} == latch_mem_line_idx), 1), 
                    1
                )); 
            end
        end
    end
    
    // -------------------- reset_condition -------------------- 
    
    for(i = 0; i < 64; i = i + 1) begin: reset_valid_bits_outer
        for(j = 0; j < 4; j = j + 1) begin: reset_valid_bits_inner
            assert_reset_valid_bits: assert property(reset_cond(clk, !reset_n, valid_bits[i][j] == 1'b0)); 
        end
    end 
    
    // -------------------- misc --------------------
    p12: assert property(reset_cond(clk, !reset_n, state == READY));
    p13: assert property(reset_cond(clk, !reset_n, miss == 1'b0));

    
    //////////////////////////////////////////////////////////
    //
    // aux 
    //
    //////////////////////////////////////////////////////////
    always@(posedge clk) begin
        if(reset_n == 0) begin
            rst_seen <= 1; 
            latch_cpu_addr <= 0;
            latch_cpu_data_in <= 0; 
            latch_tag = 0; 
            latch_set_idx = 0; 
            latch_way_idx = 0;
            latch_cpu_line_idx = 0;
            latch_mem_addr <= 0; 
            latch_mem_data_in <= 0; 
            latch_mem_line_idx <= 0;
            counter <= 0; 
        end
        else begin 
            if (state == READY && req_now) begin // latch CPU data if valid request
                latch_cpu_addr <= cpu_addr;
                latch_cpu_data_in <= cpu_data_in; 
                latch_tag = cpu_addr[31 : 15]; 
                latch_set_idx = cpu_addr[14 : 9]; 
                latch_way_idx = cpu_addr[8 : 7];
                latch_cpu_line_idx = cpu_addr[6 : 0];
            end
            else if (state == REPLACE) begin // latch mem data while filling cache 
                if(mem_data_valid) begin
                    latch_mem_addr <= mem_addr; 
                    latch_mem_data_in <= mem_data_in; 
                    latch_mem_line_idx <= mem_addr[6:0];
                    counter <= counter + 5'b1;  
                end         
            end
        end 

    end
endmodule

module Wrapper;

bind cache cache_props bind1(
    .clk(clk), 
    .reset_n(reset_n), 
    .faux_rst(faux_rst),
    .cpu_addr(cpu_addr), 
    .cpu_data_in(cpu_data_in), 
    .cpu_we(cpu_we),
    .cpu_re(cpu_re),  
    .cpu_wstb(cpu_wstb),
    .cpu_data_out(cpu_data_out),
    .mem_addr(mem_addr),  
    .mem_data_in(mem_data_in), 
    .mem_wstb(mem_wstb),
    .mem_data_valid(mem_data_valid), 
    .mem_last(mem_last),
    .miss(miss), 

    .data_cache(cache.data_cache), 
    .tag_array(cache.tag_array), 
    .valid_bits(cache.valid_bits), 
    .state(cache.state)
);



endmodule

