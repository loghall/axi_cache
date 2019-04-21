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
    wire [16 : 0] tag = cpu_addr[31 : 15]; 
    wire [5 : 0] set_idx = cpu_addr[14 : 9]; 
    wire [1 : 0] way_idx = cpu_addr[8 : 7];
    wire [6 : 0] cpu_line_idx = cpu_addr[6 : 0];
    wire [6 : 0] mem_line_idx = mem_addr[6 : 0]; 
    wire [6 : 0] line_idx = (miss) ? mem_line_idx : cpu_line_idx; 
    
    wire [7 : 0] byte0 = data_cache[set_idx][way_idx][line_idx];
    wire [7 : 0] byte1 = data_cache[set_idx][way_idx][line_idx + 1];
    wire [7 : 0] byte2 = data_cache[set_idx][way_idx][line_idx + 2];
    wire [7 : 0] byte3 = data_cache[set_idx][way_idx][line_idx + 3];
    wire [31 : 0] cache_data = {byte3, byte2, byte1, byte0}; 

    reg [31 : 0] past_mem_addr;
    reg [4 : 0] counter; 
    reg rst_seen;

    localparam READY = 1'b0, REPLACE = 1'b1; 

	property iff_instant(pre, expression1, expression2); 
		@(posedge clk) disable iff(!reset_n)
			pre |-> expression1 == expression2; 
	endproperty 

    property iff_1cycle(pre, expression1, expression2); 
		@(posedge clk) disable iff(!reset_n)
			pre |-> ##1 expression1 == expression2; 
	endproperty  

	property implies_instant(expression1, expression2); 
		@(posedge clk) disable iff(!reset_n)
			expression1 |-> expression2; 
	endproperty 

    property implies_1cycle(expression1, expression2); 
		@(posedge clk) disable iff(!reset_n)
			expression1 |-> ##1 expression2; 
	endproperty 

    property reset_cond(reset_cond, expression1); 
		@(posedge clk) 
			reset_cond |-> ##1 expression1; 
	endproperty 


	property implies_past(expression_pre, expression_post);
		@(posedge clk) disable iff(!reset_n)
			expression_post |-> $past(expression_pre, 1); 
	endproperty 

    property past_implies(expression_pre, current_condition, expression_post);
		@(posedge clk) disable iff(!reset_n)
			$past(expression_pre, 1) && current_condition |-> expression_post; 
	endproperty 

    property signal_is_stable(stable_expression, signal);
        @(posedge clk) disable iff(!reset_n)
            stable_expression |-> $stable(signal); 
    endproperty

    property mem_addr_no_miss;
        @(posedge clk) disable iff(!reset_n)
            !miss |-> (mem_addr == cpu_addr) && (mem_data == 0);
    endproperty 
    
    property stable_1cycle(signal);
        @(posedge clk) disable iff(!reset_n)
            (cpu_re || cpu_we) |-> ##1 $stable(signal);
    endproperty

    property stable_during_miss(signal);
        @(posedge clk) disable iff(!reset_n)
            $past(miss, 1) && miss |-> $stable(signal);
    endproperty

    // cpu addr aligned
    assume_cpu_aligned: assume property(iff_instant(1, cpu_addr % 4, 0)); 
    // mem addr aligned
    assume_mem_aligned: assume property(iff_instant(1, mem_addr % 4, 0)); 
    // no read/write at same time 
    assume_mutex_rw: assume property(iff_instant(1, cpu_we && cpu_re, 0)); 
    // only r/w while ready
    assume_rw_only_in_ready: assume property(iff_instant($rose(cpu_we) || $rose(cpu_re), state, READY); 
    // no r/w signal while handling miss 
    assume_no_rw_while_busy: assume property(iff_instant(state == REPLACE, cpu_we || cpu_re, 0)); 
    // mem_wstb = '1111
    assume_const_mem_stb: assume property(iff_instant(1, mem_wstb, 4'b1111)); 
    // 1 cycle we
    assume_we_only_1_cycle: assume property(implies_1cycle(cpu_we, !cpu_we)); 
    // 1 cycle re
    assume_re_only_1_cycle: assume property(implies_1cycle(cpu_re, !cpu_re)); 
    // mem_addr == cpu_addr if not handling miss
    assume_mem_addr_no_miss: assume property(iff_instant(state == READY, mem_addr, cpu_addr)); 
    // mem_last == 0 if not handling miss
    assume_mem_last_no_miss: assume property(iff_instant(state == READY, mem_last, 0)); 
    // mem_data_valid == 0 if not handling miss
    assume_mem_valid_no_miss: assume property(iff_instant(state == READY, mem_data_valid, 0)); 
    // mem_address increments by word size when filling cache line
    assume_inc_mem_addr: assume property(iff_1cycle(state == REPLACE && counter != 31 && mem_data_valid, past_mem_addr + 4, mem_addr)); 
    // mem_address only changes after data valid
    assume_chg_mem_addr_on_valid: assume property(implies_past($changed(mem_addr), mem_data_valid);
    // mem last only asserted for last word
    assume_mem_last_set: assume property(iff_instant(state == REPLACE, counter == 31, mem_last)); 
    // 1 cycle mem last
    assume_mem_last_1_cycle: assume property(implies_1cycle(mem_last, !mem_last)); 
    // 1 cycle data_valid
    assume_mem_data_valid_1_cycle: assume property(implies_1cycle(mem_data_valid, !mem_data_valid)); 
    // if last, data must be valid
    assume_mem_last_implies_valid_1: assume property(implies_instant(mem_last, mem_data_valid)); 
    // if data is not valid, it is not the last data 
    assume_mem_last_implies_valid_2: assume property(implies_instant(!mem_data_valid, !mem_last)); 
    //  cpu data assumes... 
    assume_cpu_data_in: assume property(@(posedge clk) cpu_data_in == 32'hAAAAAAAA || cpu_data_in == 32'h55555555 || cpu_data_in == 32'hFFFFFFFF || cpu_data_in == 32'h0);
    // mem data assumes
    assume_mem_data_in: assume property(@(posedge clk) mem_data_in == 32'hAAAAAAAA || mem_data_in == 32'h55555555 || mem_data_in == 32'hFFFFFFFF || mem_data_in == 32'h0);
    // simulates actual operating scenario; when data is ready from mem (i.e. mem_data_in changed), make data valid
    mem_data_valid_when_data: assume property(implies_instant($changed(mem_data_in), $rose(mem_data_valid)));

    a28: assume property(@(posedge clk) !rst_seen |-> reset_n == 0);
    a29: assume property(@(posedge clk) rst_seen |-> reset_n == 1);
    
    // assertions 
    p1: assert property(iff_1cycle(cpu_re || cpu_we, tag_array[set_idx][way_idx] != tag || valid_bits[set_idx][way_idx] != 1'b1, $rose(miss))); // miss set correctly 
    p2: assert property(past_implies(cpu_re, !miss, cache_data == cpu_data_out)); // read data correct 
    p3: assert property(past_implies(cpu_we, !miss, cache_data == cpu_data_in)); // write data from cpu correct
    p4: assert property(past_implies(miss && mem_data_valid, 1, cache_data == mem_data_in)); // data from mem correctly in cache
    p5: assert property(iff_1cycle($fell(miss), tag_array[set_idx][way_idx], tag)); // tag updated correctly 
    p6: assert property(iff_1cycle($fell(miss), valid_bits[set_idx][way_idx], 1'b1)); // valid bits updated correctly 
    p7: assert property(iff_instant(1, $fell(miss), $fell(mem_last))); // mem_last and miss fall at same time. 
    p8: assert property(iff_1cycle((state == READY) && (cpu_re || cpu_we && (tag_array[set_idx][way_idx] != tag || valid_bits[set_idx][way_idx] != 1'b1)), state, REPLACE)); // update state correctly
    p9: assert property(iff_1cycle((state == READY) && (cpu_re || cpu_we && !(tag_array[set_idx][way_idx] != tag || valid_bits[set_idx][way_idx] != 1'b1)), state, READY)); // update state correctly 
    p10: assert property(iff_1cycle(state == REPLACE && mem_last, state, READY)); // update state correctly
    p11: assert property(iff_1cycle(state == REPLACE && !mem_last, state, REPLACE)); // update state correctly  
    p12: assert property(reset_cond(!reset_n, state == READY));
    p13: assert property(reset_cond(!reset_n, miss == 1'b0));

    genvar i, j; 
    for(i = 0; i < 64; i = i + 1) begin: valid_bits_outer
        for(j = 0; j < 4; j = j + 1) begin: valid_bits_inner
            p_bits: assert property(reset_cond(!reset_n, valid_bits[i][j] == 1'b0)); 
        end
    end 

    // aux code 
    always@(posedge clk) begin
        if (miss && mem_data_valid) begin
            past_mem_addr <= mem_addr; 
            counter <= counter + 5'b1;           
        end

    end

    always@(posedge clk) begin
        if(reset_n == 0) rst_seen <= 1;
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

