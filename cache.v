module cache #(
    parameter integer ADDR_WIDTH = 32,
    parameter integer DATA_WIDTH = 32,

    parameter integer LINE_SIZE_BITS = 7,
    parameter integer WAY_SIZE_BITS = 2,
    parameter integer SET_SIZE_BITS = 6
)
(  
    input wire clk, 
    input wire reset_n, 
    input wire faux_rst,
    input wire [ADDR_WIDTH - 1 : 0] cpu_addr, 
    input wire [DATA_WIDTH - 1 : 0] cpu_data_in, 
    input wire cpu_we,
    input wire cpu_re,  
    input wire [ (DATA_WIDTH >> 3) - 1 : 0] cpu_wstb,
    output reg [DATA_WIDTH - 1 : 0] cpu_data_out,
    input wire [ADDR_WIDTH - 1 : 0] mem_addr,  
    input wire [DATA_WIDTH - 1 : 0] mem_data_in, 
    input wire [ (DATA_WIDTH >> 3) - 1 : 0] mem_wstb,
    input wire mem_data_valid, 
    input wire mem_last,
    output reg miss
);
    // cache parameters; specifies number of sets, ways, bytes per line 
    // and other relevant information for indexing addresses correctly. 
    localparam LINE_LSB = 0; 
    localparam LINE_MSB = LINE_SIZE_BITS - 1; 
    localparam LINE_SIZE = (1 << LINE_SIZE_BITS);
    localparam WAY_LSB = LINE_MSB + 1; 
    localparam WAY_MSB = WAY_LSB + WAY_SIZE_BITS - 1;
    localparam WAY_SIZE = (1 << WAY_SIZE_BITS);  
    localparam SET_LSB = WAY_MSB + 1;
    localparam SET_MSB = SET_LSB + SET_SIZE_BITS - 1; 
    localparam SET_SIZE = (1 << SET_SIZE_BITS); 
    localparam TAG_SIZE_BITS = ADDR_WIDTH - SET_MSB - 1;
    localparam TAG_LSB = SET_MSB + 1;
    localparam TAG_MSB = TAG_LSB + TAG_SIZE_BITS - 1; 
    localparam BYTES_PER_WORD = (DATA_WIDTH) >> 3; 

    // valid array, tag array, and cache declaration
    reg valid_bits [SET_SIZE - 1 : 0][WAY_SIZE - 1 : 0]; 
    reg [TAG_SIZE_BITS - 1 : 0] tag_array [SET_SIZE - 1 : 0][WAY_SIZE - 1 : 0]; 
    reg [7 : 0] data_cache [SET_SIZE - 1 : 0][WAY_SIZE - 1 : 0][LINE_SIZE - 1 : 0]; 

    // derived from current cpu/mem address
    wire [TAG_SIZE_BITS - 1: 0] tag;
    wire [SET_SIZE_BITS - 1 : 0] set_idx;
    wire [WAY_SIZE_BITS - 1 : 0] way_idx; 
    wire [LINE_SIZE_BITS - 1 : 0] cpu_line_idx; 
    wire [LINE_SIZE_BITS - 1 : 0] mem_line_idx; 

    // cache states
    localparam READY = 1'b0, REPLACE = 1'b1;
    reg state; 
    
    integer i, j, k, l;
    // write cache line according to strobe bits set
    task write_cache;
        input [DATA_WIDTH - 1 : 0] data; 
        input [ (DATA_WIDTH >> 3) - 1 : 0] wstb; 
        input [LINE_SIZE_BITS - 1 : 0] line_idx; 
        begin
            for(i = 0; i < BYTES_PER_WORD; i = i + 1) begin
                if(wstb[i] == 1'b1) begin
                    data_cache[set_idx][way_idx][line_idx + i] <= data[i * 8 + 7 -: 8];
                end 
            end 
        end 
    endtask

    // read cache line 
    task read_cache;
        begin
            for(j = 0; j < BYTES_PER_WORD; j = j + 1) begin
                cpu_data_out[i * 8 + 7 -: 8] <= data_cache[set_idx][way_idx][cpu_line_idx + j];
            end
        end
    endtask

    task invalidate_cache; 
        for(k = 0; k < SET_SIZE; k = k + 1) begin
            for(l = 0; l < WAY_SIZE; l = l + 1) begin 
                valid_bits[k][l] = 1'b0; 
            end
        end
    endtask

    initial
    begin
        invalidate_cache();
        state <= READY;
        miss <= 0;
    end

    always @(posedge clk) 
    begin
        if(!reset_n) begin
            state <= READY; 
            miss <= 0; 
            invalidate_cache(); 
        end 
        else begin
            case(state) 
                READY: begin
                    miss <= 1'b1;
                    state <= REPLACE; 
                    if (cpu_re || cpu_we) begin
                        if(valid_bits[set_idx][way_idx] == 1'b1) begin
                            if(tag_array[set_idx][way_idx] == tag) begin
                                miss <= 1'b0;
                                state <= READY; 
                                if(cpu_re) begin
                                    read_cache();
                                end
                                else begin
                                    write_cache(cpu_data_in, cpu_wstb, cpu_line_idx);
                                end
                            end
                        end
                    end 
                    else begin
                        miss <= 1'b0;
                        state <= READY; 
                    end
                end
                REPLACE: begin 
                    if(mem_data_valid) begin
                        write_cache(mem_data_in, mem_wstb, mem_line_idx); 
                        if(mem_last) begin
                            valid_bits[set_idx][way_idx] <= 1'b1; // set valid
                            tag_array[set_idx][way_idx] <= tag; // update tag 
                            state <= READY;
                            miss <= 1'b0; 
                        end
                    end 
                    else begin
                        state <= REPLACE; 
                    end
                end
            endcase 
        end
    end

    // figure out set/tag/... for cpu addr
    assign tag = cpu_addr[TAG_MSB : TAG_LSB];
    assign set_idx = cpu_addr[SET_MSB : SET_LSB];
    assign way_idx = cpu_addr[WAY_MSB : WAY_LSB];
    assign cpu_line_idx = cpu_addr[LINE_MSB : LINE_LSB]; 

    // figure out set/tag/... for mem addr 
    assign mem_line_idx = mem_addr[LINE_MSB : LINE_LSB]; 

endmodule
