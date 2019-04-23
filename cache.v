module cache #(
    parameter integer C_ADDR_WIDTH = 16,
    parameter integer C_DATA_WIDTH = 32,

    parameter integer C_LINE_SIZE_BITS = 7,
    parameter integer C_WAY_SIZE_BITS = 2,
    parameter integer C_SET_SIZE_BITS = 6
)
(  
    input wire clk, 
    input wire reset_n, 
    input wire faux_rst,
    input wire [C_ADDR_WIDTH - 1 : 0] cpu_addr, 
    input wire [C_DATA_WIDTH - 1 : 0] cpu_data_in, 
    input wire cpu_we,
    input wire cpu_re,  
    input wire [ (C_DATA_WIDTH >> 3) - 1 : 0] cpu_wstb,
    output reg [C_DATA_WIDTH - 1 : 0] cpu_data_out,
    input wire [C_ADDR_WIDTH - 1 : 0] mem_addr,  
    input wire [C_DATA_WIDTH - 1 : 0] mem_data_in, 
    input wire [ (C_DATA_WIDTH >> 3) - 1 : 0] mem_wstb,
    input wire mem_data_valid, 
    input wire mem_last,
    output reg miss
);
    // cache parameters; specifies number of sets, ways, bytes per line 
    // and other relevant information for indexing addresses correctly. 
    localparam C_LINE_LSB = 0; 
    localparam C_LINE_MSB = C_LINE_SIZE_BITS - 1; 
    localparam C_LINE_SIZE = (1 << C_LINE_SIZE_BITS);
    localparam C_WAY_LSB = C_LINE_MSB + 1; 
    localparam C_WAY_MSB = C_WAY_LSB + C_WAY_SIZE_BITS - 1;
    localparam C_WAY_SIZE = (1 << C_WAY_SIZE_BITS);  
    localparam C_SET_LSB = C_WAY_MSB + 1;
    localparam C_SET_MSB = C_SET_LSB + C_SET_SIZE_BITS - 1; 
    localparam C_SET_SIZE = (1 << C_SET_SIZE_BITS); 
    localparam C_TAG_SIZE_BITS = C_ADDR_WIDTH - C_SET_MSB - 1;
    localparam C_TAG_LSB = C_SET_MSB + 1;
    localparam C_TAG_MSB = C_TAG_LSB + C_TAG_SIZE_BITS - 1; 
    localparam C_BYTES_PER_WORD = (C_DATA_WIDTH) >> 3; 

    // valid array, tag array, and cache declaration
    reg valid_bits [C_SET_SIZE - 1 : 0][C_WAY_SIZE - 1 : 0]; 
    reg [C_TAG_SIZE_BITS - 1 : 0] tag_array [C_SET_SIZE - 1 : 0][C_WAY_SIZE - 1 : 0]; 
    reg [7 : 0] data_cache [C_SET_SIZE - 1 : 0][C_WAY_SIZE - 1 : 0][C_LINE_SIZE - 1 : 0]; 

    // derived from current cpu/mem address
    wire [C_TAG_SIZE_BITS - 1: 0] tag;
    wire [C_SET_SIZE_BITS - 1 : 0] set_idx;
    wire [C_WAY_SIZE_BITS - 1 : 0] way_idx; 
    wire [C_LINE_SIZE_BITS - 1 : 0] cpu_line_idx; 
    wire [C_LINE_SIZE_BITS - 1 : 0] mem_line_idx; 

    // cache states
    localparam C_READY = 1'b0, C_REPLACE = 1'b1;
    reg state; 
    
    integer i, j, k, l;
    // write cache line according to strobe bits set
    task write_cache;
        input [C_DATA_WIDTH - 1 : 0] data; 
        input [ (C_DATA_WIDTH >> 3) - 1 : 0] wstb; 
        input [C_LINE_SIZE_BITS - 1 : 0] line_idx; 
        begin
            for(i = 0; i < C_BYTES_PER_WORD; i = i + 1) begin
                if(wstb[i] == 1'b1) begin
                    data_cache[set_idx][way_idx][line_idx + i] <= data[i * 8 + 7 -: 8];
                end 
            end 
        end 
    endtask

    // read cache line 
    task read_cache;
        begin
            for(j = 0; j < C_BYTES_PER_WORD; j = j + 1) begin
                cpu_data_out[i * 8 + 7 -: 8] <= data_cache[set_idx][way_idx][cpu_line_idx + j];
            end
        end
    endtask

    task invalidate_cache; 
        for(k = 0; k < C_SET_SIZE; k = k + 1) begin
            for(l = 0; l < C_WAY_SIZE; l = l + 1) begin 
                valid_bits[k][l] = 1'b0; 
            end
        end
    endtask

    initial
    begin
        invalidate_cache();
        state <= C_READY;
        miss <= 0;
    end

    always @(posedge clk) 
    begin
        if(!reset_n) begin
            state <= C_READY; 
            miss <= 0; 
            invalidate_cache(); 
        end 
        else begin
            case(state) 
                C_READY: begin
                    miss <= 1'b1;
                    state <= C_REPLACE; 
                    if (cpu_re || cpu_we) begin
                        if(valid_bits[set_idx][way_idx] == 1'b1) begin
                            if(tag_array[set_idx][way_idx] == tag) begin
                                miss <= 1'b0;
                                state <= C_READY; 
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
                        state <= C_READY; 
                    end
                end
                C_REPLACE: begin 
                    if(mem_data_valid) begin
                        write_cache(mem_data_in, mem_wstb, mem_line_idx); 
                        if(mem_last) begin
                            valid_bits[set_idx][way_idx] <= 1'b1; // set valid
                            tag_array[set_idx][way_idx] <= tag; // update tag 
                            state <= C_READY;
                            miss <= 1'b0; 
                        end
                    end 
                    else begin
                        state <= C_REPLACE; 
                    end
                end
            endcase 
        end
    end

    // figure out set/tag/... for cpu addr
    assign tag = cpu_addr[C_TAG_MSB : C_TAG_LSB];
    assign set_idx = cpu_addr[C_SET_MSB : C_SET_LSB];
    assign way_idx = cpu_addr[C_WAY_MSB : C_WAY_LSB];
    assign cpu_line_idx = cpu_addr[C_LINE_MSB : C_LINE_LSB]; 

    // figure out set/tag/... for mem addr 
    assign mem_line_idx = mem_addr[C_LINE_MSB : C_LINE_LSB]; 

endmodule
