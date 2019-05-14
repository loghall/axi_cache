module cache #(
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
    output wire o_cache_valid, 
    output wire [DATA_WIDTH - 1 : 0] o_cache_data,
    output wire o_cache_rdy,

    // to memory
    output wire o_mem_req, 
    output wire [ADDR_WIDTH - 1 : 0] o_mem_addr,
    output wire o_mem_wen, 
    output wire [ (DATA_WIDTH >> 3) - 1 : 0] o_mem_ben, 
    output wire [DATA_WIDTH - 1 : 0] o_mem_data, 
    output wire [7 : 0] o_mem_len,
    output wire i_mem_valid, 
    output wire [DATA_WIDTH - 1 : 0] i_mem_data,
    output wire i_mem_rdy
);
    localparam integer BYTES_PER_WORD = (DATA_WIDTH >> 3);
    localparam integer STATE_READY = 3'd0,
                STATE_WAIT_ACK = 3'd1, 
                STATE_WAIT_RDY = 3'd2, 
                STATE_READ_CACHE = 3'd3, 
                STATE_WRITE_CACHE = 3'd4;
    
    
    integer read_ctr; 
    // latch all input data when i_cache_req is high
    reg req;
    reg [ADDR_WIDTH - 1 : 0] addr;
    reg wen; 
    reg [BYTES_PER_WORD - 1 : 0] iben;
    reg [DATA_WIDTH - 1 : 0] data_out; 
    reg [DATA_WIDTH - 1 : 0] data_in;
    reg rdy;

    reg [2 : 0] state;
    reg cache_rdy;
    reg cache_valid;
    reg [DATA_WIDTH - 1 : 0] cache_data;
    reg [7 : 0] i_cache_len_r;

    always@(posedge clk) begin
        if(!reset_n) begin
            state <= STATE_READY; 
            cache_rdy <= 1; 
        end
        else begin
            req <= 0; 
            cache_valid <= 0;
            
            case(state) 
                STATE_READY: begin
                    if(i_cache_req) begin
                        cache_rdy <= 0;
                        read_ctr <= 0; 
                        /*
                        i_cache_addr_r <= i_cache_addr;
                        i_cache_wen_r <= i_cache_wen;
                        i_cache_ben_r <= i_cache_ben;
                        i_cache_data_r <= i_cache_data;
                        */
                        // doesnt seem like we use the above
                        i_cache_len_r <= i_cache_len;

                        addr <= i_cache_addr; 
                        wen <= i_cache_wen;
                        if(i_cache_wen) begin
                            iben <= i_cache_ben;
                            data_out <= i_cache_data;
                        end

                        req <= (rdy) ? 1'b1 : 1'b0; 
                        state <= (rdy) ? STATE_WAIT_ACK : STATE_WAIT_RDY;
                    end
                end
                STATE_WAIT_RDY: begin
                    req <= 0;
                    state <= STATE_WAIT_RDY; 

                    if(rdy) begin
                        req <= 1;
                        state <= STATE_WAIT_ACK; 
                    end
                end
                STATE_WAIT_ACK: begin
                    req <= 1;
                    state <= STATE_WAIT_ACK;

                    if(!rdy) begin
                        req <= 0;
                        state <= (i_cache_wen) ? STATE_WRITE_CACHE : STATE_READ_CACHE; 
                    end 
                end
                STATE_READ_CACHE: begin
                    cache_valid <= 0; 
                    req <= 0;
                    state <= STATE_READ_CACHE;

                    if(read_ctr == i_cache_len_r) begin
                        cache_rdy <= 1; 
                        state <= STATE_READY; 
                    end
                    else if(rdy) begin
                        cache_data <= data_in; 
                        cache_valid <= 1; 

                            if(read_ctr != i_cache_len_r - 1) begin
                                addr <= addr + BYTES_PER_WORD; 
                                req <= 1; 
                                state <= STATE_WAIT_ACK; 
                            end 
                            else begin
                                state <= STATE_READ_CACHE; 
                            end

                        read_ctr <= read_ctr + 1; 
                    end
                end
                STATE_WRITE_CACHE: begin
                    state <= STATE_WRITE_CACHE;
                    
                    if(rdy) begin   
                        cache_rdy <= 1;
                        state <= STATE_READY; 
                    end 
                end
            endcase
        end
    end

    assign o_cache_valid = (!o_cache_rdy) && cache_valid;  
    assign o_cache_data = (o_cache_valid) ? cache_data : 0; 
    assign o_cache_rdy = cache_rdy; 

    cache_ctrl #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .LINE_WIDTH(LINE_SIZE_BITS),
        .SET_WIDTH(SET_SIZE_BITS)
    )
    (  
        .clk(clk), 
        .reset_n(reset_n), 

        .i_req(req), 
        .i_addr(addr),
        .i_wen(wen), 
        .i_ben(iben),
        .i_data(data_out), 
        .o_data(data_in),
        .o_rdy(rdy),

        .o_mem_req(o_mem_req), 
        .o_mem_addr(o_mem_addr),
        .o_mem_wen(o_mem_wen), 
        .o_mem_ben(o_mem_ben),
        .o_mem_data(o_mem_data), 
        .o_mem_len(o_mem_len),

        .i_mem_rdy(i_mem_rdy), 
        .i_mem_valid(i_mem_valid),
        .i_mem_data(i_mem_data)
    );
    
endmodule

