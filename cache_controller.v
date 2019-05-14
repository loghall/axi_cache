`define TAG TAG_MSB : TAG_LSB
`define LINE LINE_MSB : LINE_LSB
`define SET SET_MSB : SET_LSB 
`define CACHE_ADDR SET_MSB : 0 

module cache_ctrl #(
    parameter integer ADDR_WIDTH = 10,
    parameter integer DATA_WIDTH = 32,
    parameter integer LINE_WIDTH = 4,
    parameter integer SET_WIDTH = 3,
    parameter integer WAY_WIDTH = 2 
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
    i_mem_data  
);
    
    //---------------------------------------------
    //
    // Local params 
    //
    //---------------------------------------------
    localparam integer  LINE_LSB = 0, 
                        LINE_MSB = LINE_LSB + LINE_WIDTH - 1,
                        LINE_SIZE_BYTES = (1 << LINE_WIDTH); 
    localparam integer  SET_LSB = LINE_MSB + 1,
                        SET_MSB = SET_LSB + SET_WIDTH - 1,
                        NUM_SETS = (1 << SET_WIDTH);
    localparam integer  NUM_WAYS = (1 << WAY_WIDTH); 
    localparam integer  TAG_WIDTH = (ADDR_WIDTH - SET_WIDTH - LINE_WIDTH),
                        TAG_MSB = ADDR_WIDTH - 1,
                        TAG_LSB = SET_MSB + 1; 
    localparam integer  DATA_SIZE_BYTES = (DATA_WIDTH / 8) + (DATA_WIDTH % 8 != 0); 
    localparam integer  TAG_SIZE_BYTES = (TAG_WIDTH / 8) + (TAG_WIDTH % 8 != 0); 
    localparam integer  CACHE_ADDR_WIDTH = (LINE_WIDTH + SET_WIDTH); 
    
    //---------------------------------------------
    //
    // Port definition 
    //
    //---------------------------------------------
    
    // clk and reset (active low) 
    input wire clk;
    input wire reset_n; 
    
    // to/from CPU sig
    input wire i_req;
    input wire [ADDR_WIDTH - 1 : 0] i_addr;
    input wire i_wen;
    input wire [DATA_SIZE_BYTES - 1 : 0] i_ben;
    input wire [DATA_WIDTH - 1 : 0] i_data;
    output wire [DATA_WIDTH - 1 : 0] o_data;
    output wire o_rdy;

    // to/from MEM cig
    output wire o_mem_req; 
    output wire [ADDR_WIDTH - 1 : 0] o_mem_addr;
    output wire o_mem_wen; 
    output wire [DATA_SIZE_BYTES - 1 : 0]  o_mem_ben;
    output wire [7 : 0] o_mem_len;
    output wire [DATA_WIDTH - 1 : 0] o_mem_data; 
    input wire i_mem_rdy; 
    input wire i_mem_valid;
    input wire [DATA_WIDTH - 1 : 0] i_mem_data;

    //---------------------------------------------
    //
    // internal signal definition
    //
    //---------------------------------------------
    localparam integer STATE_READY = 3'd0,
                       STATE_WAIT_MEM_RDY = 3'd1, 
                       STATE_WAIT_MEM_ACK = 3'd2, 
                       STATE_REQUEST_LOOKUP = 3'd3, 
                       STATE_LOOKUP = 3'd4, 
                       STATE_LINE_FILL = 3'd5;

    reg [2 : 0] state; 
    
    // to cpu output sigs
    reg [DATA_WIDTH - 1 : 0] rdata;
    reg rdy;  

    // to mem output sigs
    reg mem_req; 
    reg mem_wen; 
    reg [DATA_SIZE_BYTES - 1 : 0] mem_ben;
    reg [DATA_WIDTH - 1 : 0] mem_wdata; 
    reg [7 : 0] mem_len;
    reg [ADDR_WIDTH - 1 : 0] mem_addr;

    // latched request signals
    reg [ADDR_WIDTH - 1 : 0] i_addr_r; 
    reg i_wen_r; 
    reg [DATA_SIZE_BYTES - 1 : 0] i_ben_r; 
    reg [DATA_WIDTH - 1 : 0] i_data_r; 
    reg [DATA_WIDTH - 1 : 0] addr_rdata [0 : NUM_WAYS - 1];   

    // cache and tag req signals  
    reg [CACHE_ADDR_WIDTH - 1 : 0] cache_addr;
    reg cache_wen; 
    reg [DATA_SIZE_BYTES - 1 : 0] cache_ben;
    reg [DATA_WIDTH - 1 : 0] cache_wdata; 
    reg [DATA_WIDTH - 1 : 0] cache_rdata [0 : NUM_WAYS - 1];   
    reg tag_wen; 
    reg [TAG_WIDTH + 1 - 1 : 0] tag_wdata; 
    reg [TAG_WIDTH + 1 - 1 : 0] tag_rdata [0 : NUM_WAYS - 1];  

    // lookup signals 
    reg lookup_req, lookup_valid, hit;   
    reg [TAG_WIDTH - 1: 0] addr_tag;  
    reg [SET_WIDTH - 1: 0] addr_set; 
    reg [TAG_WIDTH + 1 - 1 : 0] addr_tag_store [NUM_WAYS - 1 : 0];  
    reg [NUM_WAYS - 1 : 0] way_select; 

    // other latched signals 
    reg addr_hit; 
    reg [NUM_WAYS - 1 : 0] addr_way; 
    wire [WAY_WIDTH - 1 : 0] addr_way_decoded; 
    integer read_data_ctr, i;

    //---------------------------------------------
    //
    // Controller logic
    //
    //---------------------------------------------
    always@(posedge clk) begin
        if(!reset_n) begin
            state <= STATE_READY; 
            
            rdy <= 1'b1; 
            rdata <= {DATA_WIDTH{1'b0}}; 

            mem_req <= 1'b0;
            mem_addr <= {ADDR_WIDTH{1'b0}};
            mem_wen <= 1'b0;
            mem_ben <= {DATA_SIZE_BYTES{1'b0}};
            mem_len <= 8'b0;
            mem_wdata <= {DATA_WIDTH{32'b0}};

            i_addr_r <= {ADDR_WIDTH{1'b0}}; 
            i_wen_r <= 1'b0; 
            i_ben_r <= {DATA_SIZE_BYTES{1'b0}};
            i_data_r <= {DATA_WIDTH{1'b0}}; 

            cache_addr <= {CACHE_ADDR_WIDTH{1'b0}};
            cache_wen <= 1'b0;
            cache_ben <= {DATA_SIZE_BYTES{1'b0}};
            cache_wdata <= {DATA_WIDTH{1'b0}};
            tag_wen <= 1'b0;
            tag_wdata <= {{TAG_WIDTH{1'b0}}, {1'b0}};

            lookup_req <= 1'b0; 
            addr_tag <= {TAG_WIDTH{1'b0}}; 
            addr_set <= {SET_WIDTH{1'b0}}; 
            for(i = 0; i < NUM_WAYS; i = i + 1) begin
                addr_tag_store[i] <= {1'b0, {TAG_WIDTH{1'b0}}};
                addr_rdata[i] <= {DATA_WIDTH{1'b0}};
            end
            addr_hit <= 1'b0; 
            addr_way <= {NUM_WAYS{1'b0}};
        end     
        else begin
            cache_wen <= 1'b0;
            tag_wen <= 1'b0; 
            lookup_req <= 0;

            case(state) 
                // ready to accept requests here 
                STATE_READY: begin
                    rdy <= 1'b1;

                    if(i_req && o_rdy) begin
                        // lower the ready flag
                        rdy <= 1'b0;
                        read_data_ctr <= 0;

                        // reset all mem signals 
                        mem_req <= 1'b0; 
                        mem_addr <= {ADDR_WIDTH{1'b0}};
                        mem_wen <= 1'b0;
                        mem_ben <= {DATA_SIZE_BYTES{1'b0}}; 
                        mem_len <= 8'b0; 
                        mem_wdata <= {DATA_WIDTH{1'b0}};

                        // reset the cache signals
                        cache_addr <= {CACHE_ADDR_WIDTH{1'b0}};
                        cache_wen <= 1'b0;
                        cache_ben <= {DATA_SIZE_BYTES{1'b0}};
                        cache_wdata <= {DATA_WIDTH{1'b0}}; 
                        tag_wen <= 1'b0;
                        tag_wdata <= {{TAG_WIDTH{1'b0}}, 1'b0}; 

                        // latch input signals 
                        i_addr_r <= i_addr; 
                        i_wen_r <= i_wen; 
                        i_ben_r <= i_ben;
                        i_data_r <= i_data; 

                        // go get lookup results 
                        state <= STATE_REQUEST_LOOKUP; 
                    end
                end
                STATE_REQUEST_LOOKUP : begin
                    lookup_req <= 1'b1; 
                    addr_tag <= i_addr_r[`TAG]; 
                    addr_set <= i_addr_r[`SET]; 
                    addr_tag_store <= tag_rdata; 

                    // also latch the read data just in case 
                    addr_rdata <= cache_rdata;  
                    state <= STATE_LOOKUP;
                end 
                STATE_LOOKUP : begin
                    if(lookup_valid) begin
                        addr_hit <= hit;
                        addr_way <= way_select; 
                        cache_addr <= i_addr_r[`CACHE_ADDR];  

                        if(hit && !i_wen_r) begin
                            rdata <= addr_rdata[addr_way_decoded]; 
                            state <= STATE_READY; 
                        end 
                        else begin 
                             // mem-op if not read/hit regardless 
                            mem_req <= i_mem_rdy; 
                            
                            if(i_wen_r) begin
                                // trigger cache write for hits and misses
                                cache_wen <= 1'b1;
                                cache_ben <= i_ben_r;
                                cache_wdata <= i_data_r; 

                                // set up for mem write-thru 
                                mem_addr <= i_addr_r; 
                                mem_wen <= 1'b1; 
                                mem_ben <= i_ben_r; 
                                mem_len <= 8'b1; 
                                mem_wdata <= i_data_r; 
                            end
                            else begin
                                // set up for mem cache line fill
                                mem_addr <= {i_addr_r[ADDR_WIDTH - 1 : LINE_MSB + 1], {LINE_WIDTH{1'b0}}}; 
                                mem_wen <= 1'b0;
                                mem_ben <= {DATA_SIZE_BYTES{1'b0}}; 
                                mem_len <= 8'd32; 
                                mem_wdata <= {DATA_WIDTH{1'b0}};
                            end 

                            state <= (i_mem_rdy) ? STATE_WAIT_MEM_ACK : STATE_WAIT_MEM_RDY;  
                        end 
                        // update tag array
                        tag_wen <= 1'b1;  
                        tag_wdata = {1'b1, i_addr_r[`TAG]};
                    end
                end
                STATE_WAIT_MEM_RDY : begin
                    // wait for mem to be ready before requesting 
                    if(i_mem_rdy) begin 
                        mem_req <= 1'b1;
                        state <= STATE_WAIT_MEM_ACK; 
                    end
                end
                STATE_WAIT_MEM_ACK : begin
                    // update if mem req acknowledged 
                    if(!i_mem_rdy) begin 
                        mem_req <= 1'b0; 
                        mem_wen <= 1'b0; 
                        
                        if(mem_wen) begin // handle writes
                            if(addr_hit) begin // write-thru acked, we're good. 
                                rdy <= 1'b1;
                                state <= STATE_READY;
                            end 
                            else begin // write misses require cacheline fill 
                                mem_req <= i_mem_rdy; 
                                mem_addr <= {i_addr_r[ADDR_WIDTH - 1 : LINE_MSB + 1], {LINE_WIDTH{1'b0}}}; 
                                mem_wen <= 1'b0;
                                mem_ben <= {DATA_SIZE_BYTES{1'b0}}; 
                                mem_len <= 8'd32; 
                                mem_wdata <= {DATA_WIDTH{1'b0}};

                                state <= (i_mem_rdy) ? STATE_WAIT_MEM_ACK : STATE_WAIT_MEM_RDY; 
                            end 
                        end
                        else begin // start the line fill for reads. 
                            cache_addr <= mem_addr[`CACHE_ADDR];
                            state <= STATE_LINE_FILL; 
                        end 
                    end 
                end
                STATE_LINE_FILL : begin
                    // fill the line words as they come in 
                    if(i_mem_valid) begin
                        cache_addr[`LINE] <= read_data_ctr; 
                        cache_wen <= 1'b1;
                        cache_ben <= {DATA_SIZE_BYTES{1'b1}};
                        cache_wdata <= i_mem_data; 

                        read_data_ctr <= read_data_ctr + DATA_SIZE_BYTES; 
                        
                        // latch our read data if read request
                        if(read_data_ctr == i_addr_r[`LINE] && i_wen_r == 1'b0) begin 
                            rdata <= i_mem_data; 
                        end 
                    end
                    else if(i_mem_rdy) begin // req complete, transition to ready
                        rdy <= 1'b1;
                        state <= STATE_READY; 
                    end  
                end  
            endcase
        end
    end

    //---------------------------------------------
    //
    // Output Assignments
    //
    //---------------------------------------------
   
    // request outputs
    assign o_rdy = rdy;
    assign o_data = rdata;

    // mem outputs
    assign o_mem_req = mem_req;
    assign o_mem_addr = mem_addr;
    assign o_mem_wen = mem_wen; 
    assign o_mem_ben = mem_ben;
    assign o_mem_len = mem_len;
    assign o_mem_data = mem_wdata; 
    assign addr_way_decoded =   (addr_way[0]) ? 0 : 
                                (addr_way[1]) ? 1 : 
                                (addr_way[2]) ? 2 : 
                                3; 
  
    //---------------------------------------------
    //
    // Cache instantiation
    //
    //---------------------------------------------
    cache_4way #(
        .CACHE_ADDR_WIDTH(ADDR_WIDTH),
        .CACHE_DATA_WIDTH(DATA_WIDTH),
        .CACHE_DATA_SIZE_BYTES(DATA_SIZE_BYTES),
        .CACHE_TAG_WIDTH(TAG_WIDTH + 1), // + 1 for valid bit
        .CACHE_TAG_SIZE_BYTES(TAG_SIZE_BYTES)
    ) cache (
        .clk(clk),
        .reset_n(reset_n),
        .i_way_select(addr_way),
        .i_cache_addr((o_rdy) ? i_addr : cache_addr),
        .i_cache_wen(cache_wen), 
        .i_cache_ben(cache_ben),
        .i_cache_data(cache_wdata),
        .o_cache_data(cache_rdata),
        .i_tag_wen(tag_wen),
        .i_tag(tag_wdata),
        .o_tag(tag_rdata)
    );

    //---------------------------------------------
    //
    // Lookup instantiation
    //
    //---------------------------------------------
    lookup # (
        .TAG_WIDTH(TAG_WIDTH), 
        .SET_WIDTH(SET_WIDTH),
        .NUM_WAYS(NUM_WAYS)
    ) cache_lookup (
        .clk(clk),
        .reset_n(reset_n), 
        .i_lookup_req(lookup_req), 
        .i_addr_tag(addr_tag), 
        .i_addr_set(addr_set),
        .i_addr_tag_store(addr_tag_store), 
        .o_lookup_valid(lookup_valid), 
        .o_hit(hit),
        .o_way_select(way_select)
    );

  
endmodule


