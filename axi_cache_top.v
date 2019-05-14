module axi_cache #(
    parameter integer ADDR_WIDTH = 16,
    parameter integer DATA_WIDTH = 32,

    parameter integer LINE_SIZE_BITS = 6,
    parameter integer SET_SIZE_BITS = 7
)
(  
    input wire  s_axi_aclk,
    input wire  s_axi_aresetn,
    input wire [C_S_AXI_ID_WIDTH-1 : 0] s_axi_awid,
    input wire [C_S_AXI_ADDR_WIDTH-1 : 0] s_axi_awaddr,
    input wire [7 : 0] s_axi_awlen,
    input wire [2 : 0] s_axi_awsize,
    input wire [1 : 0] s_axi_awburst,
    input wire  s_axi_awlock,
    input wire [3 : 0] s_axi_awcache,
    input wire [2 : 0] s_axi_awprot,
    input wire [3 : 0] s_axi_awqos,
    input wire [3 : 0] s_axi_awregion,
    input wire [C_S_AXI_AWUSER_WIDTH-1 : 0] s_axi_awuser,
    input wire  s_axi_awvalid,
    output wire  s_axi_awready,
    input wire [C_S_AXI_DATA_WIDTH-1 : 0] s_axi_wdata,
    input wire [(C_S_AXI_DATA_WIDTH/8)-1 : 0] s_axi_wstrb,
    input wire  s_axi_wlast,
    input wire [C_S_AXI_WUSER_WIDTH-1 : 0] s_axi_wuser,
    input wire  s_axi_wvalid,
    output wire  s_axi_wready,
    output wire [C_S_AXI_ID_WIDTH-1 : 0] s_axi_bid,
    output wire [1 : 0] s_axi_bresp,
    output wire [C_S_AXI_BUSER_WIDTH-1 : 0] s_axi_buser,
    output wire  s_axi_bvalid,
    input wire  s_axi_bready,
    input wire [C_S_AXI_ID_WIDTH-1 : 0] s_axi_arid,
    input wire [C_S_AXI_ADDR_WIDTH-1 : 0] s_axi_araddr,
    input wire [7 : 0] s_axi_arlen,
    input wire [2 : 0] s_axi_arsize,
    input wire [1 : 0] s_axi_arburst,
    input wire  s_axi_arlock,
    input wire [3 : 0] s_axi_arcache,
    input wire [2 : 0] s_axi_arprot,
    input wire [3 : 0] s_axi_arqos,
    input wire [3 : 0] s_axi_arregion,
    input wire [C_S_AXI_ARUSER_WIDTH-1 : 0] s_axi_aruser,
    input wire  s_axi_arvalid,
    output wire  s_axi_arready,
    output wire [C_S_AXI_ID_WIDTH-1 : 0] s_axi_rid,
    output wire [C_S_AXI_DATA_WIDTH-1 : 0] s_axi_rdata,
    output wire [1 : 0] s_axi_rresp,
    output wire  s_axi_rlast,
    output wire [C_S_AXI_RUSER_WIDTH-1 : 0] s_axi_ruser,
    output wire  s_axi_rvalid,
    input wire  s_axi_rready
);
   
    wire [DATA_WIDTH - 1 : 0] cpu_to_cache_data; 
    wire [ADDR_WIDTH - 1 : 0] cpu_to_cache_addr;
    wire cpu_to_cache_req;
    wire cpu_to_cache_wen;
    wire [ADDR_WIDTH - 1 : 0] cpu_to_cache_addr;
    wire [DATA_WIDTH - 1 : 0] cpu_to_cache_data;
    wire [(DATA_WIDTH/8)-1 : 0] cpu_to_cache_wstrb;
    wire [DATA_WIDTH - 1 : 0] cache_to_cpu_data;

    axi_cpu_cache_intf #(
      .C_S_AXI_DATA_WIDTH(DATA_WIDTH),
      .C_S_AXI_ADDR_WIDTH(ADDR_WIDTH)
    )
        
    my_slave_intf (
      .s_axi_clk(s_axi_clk),
      .s_axi_aresetn(s_axi_aresetn),
      .s_axi_awid(s_axi_awid),
      .s_axi_awaddr(s_axi_awaddr),
      .s_axi_awlen(s_axi_awlen),
      .s_axi_awsize(s_axi_awsize),
      .s_axi_awburst(s_axi_awburst),
      .s_axi_awlock(s_axi_awlock),
      .s_axi_awcache(s_axi_awcache),
      .s_axi_awprot(s_axi_awprot),
      .s_axi_awqos(s_axi_awqos),
      .s_axi_awregion(s_axi_awregion),
      .s_axi_awuser(s_axi_awuser),
      .s_axi_awvalid(s_axi_awvalid),
      .s_axi_awready(s_axi_awready),
      .s_axi_wdata(s_axi_wdata),
      .s_axi_wstrb(s_axi_wstrb),
      .s_axi_wlast(s_axi_wlast),
      .s_axi_wuser(s_axi_wuser),
      .s_axi_wvalid(s_axi_wvalid),
      .s_axi_wready(s_axi_wready),
      .s_axi_bid(s_axi_bid),
      .s_axi_bresp(s_axi_bresp),
      .s_axi_buser(s_axi_buser),
      .s_axi_bvalid(s_axi_bvalid),
      .s_axi_bready(s_axi_bready),
      .s_axi_arid(s_axi_arid),
      .s_axi_araddr(s_axi_araddr),
      .s_axi_arlen(s_axi_arlen),
      .s_axi_arsize(s_axi_arsize),
      .s_axi_arburst(s_axi_arburst),
      .s_axi_arlock(s_axi_arlock),
      .s_axi_arcache(s_axi_arcache),
      .s_axi_arprot(s_axi_arprot),
      .s_axi_arqos(s_axi_arqos),
      .s_axi_arregion(s_axi_arregion),
      .s_axi_aruser(s_axi_aruser),
      .s_axi_arvalid(s_axi_arvalid),
      .s_axi_arready(s_axi_arready),
      .s_axi_rid(s_axi_rid),
      .s_axi_rdata(s_axi_rdata),
      .s_axi_rresp(s_axi_rresp),
      .s_axi_rlast(s_axi_rlast),
      .s_axi_ruser(s_axi_ruser),
      .s_axi_rvalid(s_axi_rvalid),
      .s_axi_rready(s_axi_rready),

      .cache_req_out(cpu_to_cache_req),
      .cache_wen(cpu_to_cache_wen),
      .cache_addr_out(cpu_to_cache_addr),
      .cache_data_out(cpu_to_cache_data),
      .cache_wstrb(cpu_to_cache_wstrb),
      .cache_data_in(cache_to_cpu_data)
    );
    cache #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .LINE_SIZE_BITS(LINE_SIZE_BITS),
        .SET_SIZE_BITS(SET_SIZE_BITS)) my_cache
    (
        .clk(s_axi_aclk),
        .reset_n(s_axi_aresetn), 
        .req_in(cpu_to_cache_req),
        .req_wen(cpu_to_cache_wen), 
        .req_addr_in(cpu_to_cache_addr),
        .req_data_in(cpu_to_cache_data),
        .req_byte_wstrb(cpu_to_cache_wstrb),
        .req_data_out(cache_to_cpu_data),
        
        .mem_req_out(0),
        .mem_wen(0),
        .mem_addr_out(0),
        .mem_data_out(0),
        .mem_byte_wstrb(0),
        .mem_req_len(0),
        .mem_req_size(0),
        .mem_rdy(0),
        .mem_data_in(0),
        .mem_data_valid(0),
        
        .cache_rdy(0)
    ); 

endmodule

