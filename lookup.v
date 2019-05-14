module lookup # (
    parameter integer ADDR_WIDTH = 10,
    parameter integer TAG_WIDTH = 3, 
    parameter integer SET_WIDTH = 3,
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
    o_way_select
);
    //---------------------------------------------
    //
    //  Local Params
    //
    //---------------------------------------------
    localparam integer VALID = TAG_WIDTH;
    localparam integer NUM_SETS = (1 << SET_WIDTH); 

    //---------------------------------------------
    //
    // Port definition 
    //
    //---------------------------------------------
    
    // clk, reset (active low)
    input wire clk;
    input wire reset_n; 

    // lookup request lines
    input wire i_lookup_req;
    input wire [TAG_WIDTH - 1 : 0] i_addr_tag;
    input wire [SET_WIDTH - 1 : 0] i_addr_set;
    input wire [TAG_WIDTH + 1 - 1 : 0] i_addr_tag_store [0 : NUM_WAYS - 1]; // tag store also keeps a valid bit (i.e. + 1)! 

    // lookup result lines
    output wire o_lookup_valid; 
    output wire o_hit;
    output wire [NUM_WAYS - 1 : 0] o_way_select; 

    //---------------------------------------------
    //
    // Internals 
    //
    //---------------------------------------------
    reg [2 : 0] history [NUM_SETS - 1 : 0]; 
    reg lookup_valid, lookup_hit, all_valid, hit;
    reg [NUM_WAYS - 1 : 0] lookup, invalid, lru, select, way_select; 

    integer i; 

    //---------------------------------------------
    //
    // Synchronous logic; respond to a lookup request  
    //
    //---------------------------------------------
    always @(posedge clk) begin
        if(!reset_n) begin
            lookup_valid <= 1'b0; 
            hit <= 1'b0;
            way_select <= {{NUM_WAYS - 1{1'b0}}, 1'b1};

            for(int i = 0; i < NUM_SETS; i = i + 1) begin
                history[i] <= 3'b000;
            end 
        end 
        else begin
            lookup_valid <= 1'b0; 
            if(i_lookup_req) begin
                // set outputs
                lookup_valid <= 1'b1; 
                hit <= lookup_hit; 
                way_select <= select; 
                
                // update LRU
                if(select[0]) begin 
                    history[i_addr_set][0] <= 1'b1; 
                    history[i_addr_set][1] <= 1'b1; 
                end
                else if(select[1]) begin
                    history[i_addr_set][0] <= 1'b1; 
                    history[i_addr_set][1] <= 1'b0; 
                end 
                else if(select[2]) begin
                    history[i_addr_set][0] <= 1'b0; 
                    history[i_addr_set][2] <= 1'b1; 
                end 
                else begin
                    history[i_addr_set][0] <= 1'b0; 
                    history[i_addr_set][2] <= 1'b0; 
                end 
            end 
        end 
    end

    //---------------------------------------------
    //
    // Output assignments
    //
    //---------------------------------------------
    assign o_lookup_valid = lookup_valid; 
    assign o_hit = hit;
    assign o_way_select = way_select; 

    //---------------------------------------------
    //
    // Way selection logic  
    //
    //---------------------------------------------
    assign lookup_hit = lookup != {NUM_WAYS{1'b0}};
    assign all_valid = invalid == {NUM_WAYS{1'b0}};
    assign select = (lookup_hit) ? lookup : 
                        (all_valid) ? lru :
                        invalid; 

    always@(*) begin
        integer i; 

        for(i = 0; i < NUM_WAYS; i = i + 1) begin
            lookup[i] <= 1'b0; 
            if(i_addr_tag_store[i][VALID] && i_addr_tag_store[i][TAG_WIDTH - 1 : 0] == i_addr_tag) begin
                lookup[i] <= 1'b1; 
            end
        end 
    end 
    
    always@(*) begin 
        integer i;
        
        invalid = {NUM_WAYS{1'b0}};
        for(i = 0; i < NUM_WAYS; i = i + 1) begin
            if(invalid == {NUM_WAYS{1'b0}} && !i_addr_tag_store[i][VALID]) begin
                invalid[i] = 1'b1; 
            end
        end
    end 
    
    always@(*) begin 
        lru = {NUM_WAYS{1'b0}}; 
        
        if(history[i_addr_set][0] == 0) begin
            if(history[i_addr_set][1] == 0) begin
                lru[0] = 1'b1;
            end 
            else begin 
                lru[1] = 1'b1; 
            end 
        end 
        else begin
            if(history[i_addr_set][2] == 0) begin
                lru[2] = 1'b1;
            end 
            else begin 
                lru[3] = 1'b1; 
            end 
        end
    end 
endmodule 
