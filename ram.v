module ram # (
    parameter integer MEM_ADDR_WIDTH = 7,
    parameter integer MEM_DATA_WIDTH = 32,
    parameter integer MEM_DATA_SIZE_BYTES = 4
)
(
    clk,
    reset_n, 
    i_addr, 
    i_wen, 
    i_ben,
    i_write_data,
    o_read_data  
);
    //---------------------------------------------
    //
    // Local params 
    //
    //---------------------------------------------
    localparam integer NUM_MEM_ADDR = (1 << MEM_ADDR_WIDTH); 

    //---------------------------------------------
    //
    // Port definition 
    //
    //---------------------------------------------
    input wire clk; 
    input wire reset_n; 
    input wire [MEM_ADDR_WIDTH - 1 : 0] i_addr; 
    input wire i_wen;
    input wire [MEM_DATA_SIZE_BYTES - 1 : 0] i_ben;
    input wire [MEM_DATA_WIDTH - 1 : 0] i_write_data;
    output wire [MEM_DATA_WIDTH - 1 : 0] o_read_data; 
    
    //---------------------------------------------
    //
    // internal signal definition
    //
    //---------------------------------------------

    // actual ram 
    reg [MEM_DATA_WIDTH - 1 : 0] mem [0 : NUM_MEM_ADDR - 1]; 

    // read data register 
    reg [MEM_DATA_WIDTH - 1 : 0] read_data; 
    
    // iterator; we are byte addressable bro 
    integer i; 

    always@(posedge clk) begin
        if(!reset_n) begin
            for(i = 0; i < NUM_MEM_ADDR; i = i + 1) begin
                mem[i] <= {MEM_DATA_WIDTH{1'b0}};
            end 
            read_data <= {MEM_DATA_WIDTH{1'b0}}; 
        end 
        else begin
            read_data <= mem[i_addr];
            if(i_wen) begin
                for(i = 0; i < MEM_DATA_SIZE_BYTES; i = i + 1) begin
                    if(i_ben[i]) begin   
                        mem[i_addr][i * 8 + 7 -: 8] <= i_write_data[i * 8 + 7 -: 8]; 
                    end
                end
            end 
        end 
    end
   
    assign o_read_data = read_data; 

endmodule
