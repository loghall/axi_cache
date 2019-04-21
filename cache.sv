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

    // assume for verification; basically our master spec. 
    a1: assume property(iff_instant(1, cpu_addr % 4, 0)); // cpu addr aligned
    a2: assume property(iff_instant(1, mem_addr % 4, 0)); // mem_addr aligned
    a3: assume property(iff_instant(1, cpu_we && cpu_re, 0)); // no read/write at same time 
    a4: assume property(iff_instant(miss, cpu_we || cpu_re, 0)); // no asserting enables during transaction
    a5: assume property(iff_instant(1, mem_wstb, 4'b1111)); // mem_wstb = '1111
    a6: assume property(implies_1cycle(cpu_we, !cpu_we)); // 1 cycle we 
    a7: assume property(implies_1cycle(cpu_re, !cpu_re)); // 1 cycle re
    // a8: assume property(stable_1cycle(cpu_addr)); // addr stable for at least one cycle after enable
    // a9: assume property(stable_1cycle(cpu_data_in)); // data stable for at least one cycle after enable
    // a10: assume property(stable_1cycle(cpu_wstb)); // wstb stable for at least one cycle after enable
    // a11: assume property(stable_during_miss(cpu_addr)); // cpu addr stable during entire transaciton
    // a12: assume property(stable_during_miss(cpu_data_in)); // cpu data stable during entire transaction
    // a13: assume property(stable_during_miss(cpu_wstb)); // cpu data stable during entire transaction
    // a14: assume property(iff_instant(!miss, mem_addr, cpu_addr)); // mem_addr == cpu_addr if not handling miss
    // a15: assume property(iff_instant(!miss, mem_data_in, 0)); // mem_data_in == 0 if not handling miss
    // a16: assume property(iff_instant(!miss, mem_last, 0)); // mem_last == 0 if not handling miss
    // a17: assume property(iff_instant(!miss, mem_data_valid, 0)); // mem_data_valid == 0 if not handling miss
    // a18: assume property(iff_1cycle(miss && counter != 31 && mem_data_valid, past_mem_addr + 4, mem_addr)); // mem_address increments by word size when filling cache line
    // a19: assume property(iff_instant(miss, counter == 31, mem_last)); // mem last only asserted for last word
    // a20: assume property(implies_1cycle(mem_last, !mem_last)); // mem_last only asserted for one cycle 
    // a21: assume property(implies_1cycle(mem_data_valid, !mem_data_valid)); // mem data valid only asserted for 1 cycle 
    // a22: assume property(implies_instant(mem_last, mem_data_valid)); // mem last can only be high if mem valid is high
    // a23: assume property(implies_instant(!mem_data_valid, !mem_last)); // if mem valid is not high, mem last must not be high 
    // a24: assume property(@(posedge clk) cpu_data_in == 32'hAAAAAAAA || cpu_data_in == 32'h55555555);
    // a25: assume property(@(posedge clk) mem_data_in == 32'hAAAAAAAA || mem_data_in == 32'h55555555);
    // a26: assume property(implies_instant(miss && $changed(mem_data_in), $rose(mem_data_valid)));
    // a27: assume property(implies_past(miss && $changed(mem_addr), mem_data_valid));
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

