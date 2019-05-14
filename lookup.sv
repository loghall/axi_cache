`include "props_pkg.sv" 

import propsPkg::*; 

module lookup_props #(
    parameter integer ADDR_WIDTH = 10,
    parameter integer TAG_WIDTH = 3, 
    parameter integer SET_WIDTH = 3,
    parameter integer LINE_WIDTH = 4, 
    parameter integer NUM_WAYS = 4                 
)
(  
    clk,
    reset_n, 
    i_lookup_req, 
    i_addr_tag, 
    i_addr_set,
    i_addr_tag_store, 
    o_lookup_valid, 
    o_hit,
    o_way_select,

    history 
);
    //---------------------------------------------
    //
    //  Local Params
    //
    //---------------------------------------------
    localparam integer VALID = TAG_WIDTH;
    localparam integer NUM_SETS = (1 << SET_WIDTH); 

    //------------------------------------------
    // 
    // Ports
    // 
    //------------------------------------------
    input wire clk;
    input wire reset_n; 
    input wire i_lookup_req;
    input wire [TAG_WIDTH - 1 : 0] i_addr_tag;
    input wire [SET_WIDTH - 1 : 0] i_addr_set;
    input wire [TAG_WIDTH + 1 - 1 : 0] i_addr_tag_store [0 : NUM_WAYS - 1]; // tag store also keeps a valid bit (i.e. + 1)! 
    input wire o_lookup_valid; 
    input wire o_hit;
    input wire [NUM_WAYS - 1 : 0] o_way_select; 
    input wire [2 : 0] history [NUM_SETS - 1 : 0];

    //------------------------------------------
    // 
    // Internal/aux
    // 
    //------------------------------------------
    reg [ADDR_WIDTH - 1 : 0] arb_addr; 
    reg [NUM_WAYS - 1 : 0] arb_way;
    reg arb_hit; 
    
    wire [SET_WIDTH - 1 : 0] arb_set = arb_addr[SET_WIDTH + LINE_WIDTH - 1 : LINE_WIDTH]; 
    wire [TAG_WIDTH - 1 : 0] arb_tag = arb_addr[ADDR_WIDTH - 1 : SET_WIDTH + LINE_WIDTH];

    reg [NUM_WAYS - 1 : 0] was_hit, was_invalid, was_lru; 

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

    // request only high for a single cycle (note, this is asserted in cache_controller.sv)
    assume_req_1cycle : assume property( 
        implies_1cycle(
            clk, !reset_n,
            i_lookup_req,
            !i_lookup_req
        )
    );

    // request only rises when lookup_valid is low (note, this is asserted in cache_controller.sv)
    assume_req_wait : assume property(
        implies_instant(
            clk, !reset_n,
            $rose(i_lookup_req),
            !o_lookup_valid
        ) 
    );

    // ensure there are no duplicate tags that are valid (this isn't a valid execution state) 
    // (also implicitly asserted by cache_controller.sv)
    genvar i; 
    for(i = 0; i < NUM_WAYS; i = i + 1) begin : no_duplicate_tag
        no_duplicates : assume property ( 
            implies_instant (
                clk, !reset_n, 
                i_addr_tag_store[i][VALID],  
                i_addr_tag_store[i][TAG_WIDTH - 1 : 0] != i_addr_tag_store[(i + 1) % 4][TAG_WIDTH - 1 : 0] &&
                i_addr_tag_store[i][TAG_WIDTH - 1 : 0] != i_addr_tag_store[(i + 2) % 4][TAG_WIDTH - 1 : 0] &&
                i_addr_tag_store[i][TAG_WIDTH - 1 : 0] != i_addr_tag_store[(i + 3) % 4][TAG_WIDTH - 1 : 0] 
            )
        );
    end

    //------------------------------------------
    // 
    // Assert 
    // 
    //------------------------------------------
    
    // verify that appropriate conditions were met for each way selection; see the aux logic for more details 
    for(i = 0; i < NUM_WAYS; i = i + 1) begin : correct_way
        correct_way_select : assert property ( 
            implies_instant (
                clk, !reset_n, 
                $changed(arb_way) && arb_way[i], 
                was_hit[i] || (!was_hit[i] && was_invalid[i]) || (!was_hit[i] && !was_invalid[i] && was_lru[i])
            )
        );
    end

    // a single way must always be selected, no more no less
    onehot_way_select : assert property (
            implies_instant (
                clk, !reset_n, 
                $changed(arb_way), 
                $onehot(arb_way)
            )
    );

    // assert history array updated appropriately 
    assert_history_update1 : assert property(
        implies_instant(
            clk, !reset_n,
            $changed(history[arb_set]) && (history[arb_set] == 3'b011 || history[arb_set] == 3'b111),
            o_way_select[0] == 1'b1 
        ) 
    );

    assert_history_update2 : assert property(
        implies_instant(
            clk, !reset_n,
            $changed(history[arb_set]) && (history[arb_set] == 3'b101 || history[arb_set] == 3'b001),
            o_way_select[1] == 1'b1 
        ) 
    );

    assert_history_update3 : assert property(
        implies_instant(
            clk, !reset_n,
            $changed(history[arb_set]) && (history[arb_set] == 3'b110 || history[arb_set] == 3'b100),
            o_way_select[2] == 1'b1 
        ) 
    );

    assert_history_update4 : assert property(
        implies_instant(
            clk, !reset_n,
            $changed(history[arb_set]) && (history[arb_set] == 3'b000 || history[arb_set] == 3'b010),
            o_way_select[3] == 1'b1 
        ) 
    );

    // assert lookup valid signal rises 1 cycle after a request (note, this is assumed in cache_controller.sv)
    assert_lookup_valid_set : assert property(
        implies_1cycle(
            clk, !reset_n,
            i_lookup_req,
            $rose(o_lookup_valid)
        ) 
    );

    // assert lookup valid only high for one cycle (note, this is assumed in cache_controller.sv)
    assert_lookup_falls : assert property(
        implies_1cycle(
            clk, !reset_n,
            o_lookup_valid,
            $fell(o_lookup_valid)
        ) 
    );
  
    //------------------------------------------
    // 
    // Aux Code 
    // 
    //------------------------------------------

    // track past state so that way selection can be verified appropriately 
    always@(posedge clk) begin
        integer i; 

        // for each way, check if the arb_tag was a hit 1 cycle in the past
        for(i = 0; i < NUM_WAYS; i = i + 1) begin
            was_hit[i] <= $past(i_addr_tag_store[i][TAG_WIDTH - 1 : 0]) == arb_tag &&
                                        $past(i_addr_tag_store[i][VALID]) == 1;
            was_invalid[i] <= $past(i_addr_tag_store[i][VALID]) == 0; 
        end
        
        // for each way, check if selected for LRU 1 cycle in the past 
        was_lru[0] <= ($past(history[arb_set]) == 3'b100) || ($past(history[arb_set]) == 3'b000);
        was_lru[1] <= ($past(history[arb_set]) == 3'b110) || ($past(history[arb_set]) == 3'b010);
        was_lru[2] <= ($past(history[arb_set]) == 3'b001) || ($past(history[arb_set]) == 3'b011);
        was_lru[3] <= ($past(history[arb_set]) == 3'b101) || ($past(history[arb_set]) == 3'b111);                                       
    end 

    // track way selected for arb_addr
    always@(posedge clk) begin
        integer n; 

        if(!reset_n) begin
            arb_way <= 0; 
            arb_hit <= 0; 
        end 
        else begin
            // we know that way will be selected one cycle after a request, so use past. 
            if($past(i_lookup_req) && $past(i_addr_set == arb_set) && $past(i_addr_tag == arb_tag)) begin
                arb_way <= o_way_select; 
            end 
        end 
    end
    
endmodule

module Wrapper;

    bind lookup lookup_props bind1(
        .clk(clk),
        .reset_n(reset_n), 
        .i_lookup_req(i_lookup_req),
        .i_addr_tag(i_addr_tag), 
        .i_addr_set(i_addr_set),
        .i_addr_tag_store(i_addr_tag_store), 
        .o_hit(o_hit),
        .o_lookup_valid(o_lookup_valid),
        .o_way_select(o_way_select),
        .history(history)
    );

endmodule

