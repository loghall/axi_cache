// INITIALLY PROVIDED BY XILINX, WE MADE A FEW MODIFICATIONS BUT DID NOT GET TO
// TEST THEM!!!!!


`timescale 1 ns / 1 ps

    module myip3_v1_0_s00_axi #
    (
        // users to add parameters here

        // user parameters ends
        // do not modify the parameters beyond this line

        // width of id for for write address, write data, read address and read data
        parameter integer C_S_AXI_ID_WIDTH  = 1,

        // width of s_axi data bus
        parameter integer C_S_AXI_DATA_WIDTH    = 32,

        // width of s_axi address bus
        parameter integer C_S_AXI_ADDR_WIDTH    = 6,

        // width of optional user defined signal in write address channel
        parameter integer C_S_AXI_AWUSER_WIDTH  = 0,

        // width of optional user defined signal in read address channel
        parameter integer C_S_AXI_ARUSER_WIDTH  = 0,

        // width of optional user defined signal in write data channel
        parameter integer C_S_AXI_WUSER_WIDTH   = 0,

        // width of optional user defined signal in read data channel
        parameter integer C_S_AXI_RUSER_WIDTH   = 0,

        // width of optional user defined signal in write response channel
        parameter integer C_S_AXI_BUSER_WIDTH   = 0
    )
    (
        // users to add ports here

        // user ports ends
        // do not modify the ports beyond this line

        // global clock signal
        input wire  s_axi_aclk,

        // global reset signal. this signal is active low
        input wire  s_axi_aresetn,

        // write address id
        input wire [C_S_AXI_ID_WIDTH-1 : 0] s_axi_awid,

        // write address
        input wire [C_S_AXI_ADDR_WIDTH-1 : 0] s_axi_awaddr,

        // burst length. the burst length gives the exact number of transfers in a burst
        input wire [7 : 0] s_axi_awlen,

        // burst size. this signal indicates the size of each transfer in the burst
        input wire [2 : 0] s_axi_awsize,

        // burst type. the burst type and the size information, 
    // determine how the address for each transfer within the burst is calculated.
        input wire [1 : 0] s_axi_awburst,

        // lock type. provides additional information about the
    // atomic characteristics of the transfer.
        input wire  s_axi_awlock,

        // memory type. this signal indicates how transactions
    // are required to progress through a system.
        input wire [3 : 0] s_axi_awcache,

        // protection type. this signal indicates the privilege
    // and security level of the transaction, and whether
    // the transaction is a data access or an instruction access.
        input wire [2 : 0] s_axi_awprot,

        // quality of service, qos identifier sent for each
    // write transaction.
        input wire [3 : 0] s_axi_awqos,

        // region identifier. permits a single physical interface
    // on a slave to be used for multiple logical interfaces.
        input wire [3 : 0] s_axi_awregion,

        // optional user-defined signal in the write address channel.
        input wire [C_S_AXI_AWUSER_WIDTH-1 : 0] s_axi_awuser,

        // write address valid. this signal indicates that
    // the channel is signaling valid write address and
    // control information.
        input wire  s_axi_awvalid,

        // write address ready. this signal indicates that
    // the slave is ready to accept an address and associated
    // control signals.
        output wire  s_axi_awready,

        // write data
        input wire [C_S_AXI_DATA_WIDTH-1 : 0] s_axi_wdata,

        // write strobes. this signal indicates which byte
    // lanes hold valid data. there is one write strobe
    // bit for each eight bits of the write data bus.
        input wire [(C_S_AXI_DATA_WIDTH/8)-1 : 0] s_axi_wstrb,

        // write last. this signal indicates the last transfer
    // in a write burst.
        input wire  s_axi_wlast,

        // optional user-defined signal in the write data channel.
        input wire [C_S_AXI_WUSER_WIDTH-1 : 0] s_axi_wuser,

        // write valid. this signal indicates that valid write
    // data and strobes are available.
        input wire  s_axi_wvalid,

        // write ready. this signal indicates that the slave
    // can accept the write data.
        output wire  s_axi_wready,

        // response id tag. this signal is the id tag of the
    // write response.
        output wire [C_S_AXI_ID_WIDTH-1 : 0] s_axi_bid,

        // write response. this signal indicates the status
    // of the write transaction.
        output wire [1 : 0] s_axi_bresp,

        // optional user-defined signal in the write response channel.
        output wire [C_S_AXI_BUSER_WIDTH-1 : 0] s_axi_buser,

        // write response valid. this signal indicates that the
    // channel is signaling a valid write response.
        output wire  s_axi_bvalid,

        // response ready. this signal indicates that the master
    // can accept a write response.
        input wire  s_axi_bready,

        // read address id. this signal is the identification
    // tag for the read address group of signals.
        input wire [C_S_AXI_ID_WIDTH-1 : 0] s_axi_arid,

        // read address. this signal indicates the initial
    // address of a read burst transaction.
        input wire [C_S_AXI_ADDR_WIDTH-1 : 0] s_axi_araddr,

        // burst length. the burst length gives the exact number of transfers in a burst
        input wire [7 : 0] s_axi_arlen,

        // burst size. this signal indicates the size of each transfer in the burst
        input wire [2 : 0] s_axi_arsize,

        // burst type. the burst type and the size information, 
    // determine how the address for each transfer within the burst is calculated.
        input wire [1 : 0] s_axi_arburst,

        // lock type. provides additional information about the
    // atomic characteristics of the transfer.
        input wire  s_axi_arlock,

        // memory type. this signal indicates how transactions
    // are required to progress through a system.
        input wire [3 : 0] s_axi_arcache,

        // protection type. this signal indicates the privilege
    // and security level of the transaction, and whether
    // the transaction is a data access or an instruction access.
        input wire [2 : 0] s_axi_arprot,

        // quality of service, qos identifier sent for each
    // read transaction.
        input wire [3 : 0] s_axi_arqos,

        // region identifier. permits a single physical interface
    // on a slave to be used for multiple logical interfaces.
        input wire [3 : 0] s_axi_arregion,

        // optional user-defined signal in the read address channel.
        input wire [C_S_AXI_ARUSER_WIDTH-1 : 0] s_axi_aruser,

        // write address valid. this signal indicates that
    // the channel is signaling valid read address and
    // control information.
        input wire  s_axi_arvalid,

        // read address ready. this signal indicates that
    // the slave is ready to accept an address and associated
    // control signals.
        output wire  s_axi_arready,

        // read id tag. this signal is the identification tag
    // for the read data group of signals generated by the slave.
        output wire [C_S_AXI_ID_WIDTH-1 : 0] s_axi_rid,

        // read data
        output wire [C_S_AXI_DATA_WIDTH-1 : 0] s_axi_rdata,

        // read response. this signal indicates the status of
    // the read transfer.
        output wire [1 : 0] s_axi_rresp,

        // read last. this signal indicates the last transfer
    // in a read burst.
        output wire  s_axi_rlast,

        // optional user-defined signal in the read address channel.
        output wire [C_S_AXI_RUSER_WIDTH-1 : 0] s_axi_ruser,

        // read valid. this signal indicates that the channel
    // is signaling the required read data.
        output wire  s_axi_rvalid,

        // read ready. this signal indicates that the master can
    // accept the read data and response information.
        input wire  s_axi_rready, 

        // high for all cache requests
        output reg cache_req_out,
    
    // wen for corresponding request
    output reg cache_wen, 

        // addr to look up in cache
        output reg [C_S_AXI_ADDR_WIDTH - 1 : 0] cache_addr_out, 

        // data to the cache
        output reg [C_S_AXI_DATA_WIDTH - 1 : 0] cache_data_out,
    
    // w_strb for write data
    output reg [(C_S_AXI_DATA_WIDTH >> 3) - 1 : 0] cache_wstrb, 
    

        // data from the cache
    input reg [C_S_AXI_DATA_WIDTH - 1 : 0] cache_data_in,
    
    // is the cache ready to accept request?
    input reg cache_rdy
    );

    // axi4full signals
    reg [C_S_AXI_ADDR_WIDTH-1 : 0]  axi_awaddr;
    reg     axi_awready;
    reg     axi_wready;
    reg [1 : 0]     axi_bresp;
    reg [C_S_AXI_BUSER_WIDTH-1 : 0]     axi_buser;
    reg     axi_bvalid;
    reg [C_S_AXI_ADDR_WIDTH-1 : 0]  axi_araddr;
    reg     axi_arready;
    reg [C_S_AXI_DATA_WIDTH-1 : 0]  axi_rdata;
    reg [1 : 0]     axi_rresp;
    reg     axi_rlast;
    reg [C_S_AXI_RUSER_WIDTH-1 : 0]     axi_ruser;
    reg     axi_rvalid;

    // aw_wrap_en determines wrap boundary and enables wrapping
    wire aw_wrap_en;

    // ar_wrap_en determines wrap boundary and enables wrapping
    wire ar_wrap_en;

    // aw_wrap_size is the size of the write transfer, the
    // write address wraps to a lower address if upper address
    // limit is reached
    wire [31:0]  aw_wrap_size ; 

    // ar_wrap_size is the size of the read transfer, the
    // read address wraps to a lower address if upper address
    // limit is reached
    wire [31:0]  ar_wrap_size ; 

    // the axi_awv_awr_flag flag marks the presence of write address valid
    reg axi_awv_awr_flag;

    //the axi_arv_arr_flag flag marks the presence of read address valid
    reg axi_arv_arr_flag; 

    // the axi_awlen_cntr internal write address counter to keep track of beats in a burst transaction
    reg [7:0] axi_awlen_cntr;
    
    //the axi_arlen_cntr internal read address counter to keep track of beats in a burst transaction
    reg [7:0] axi_arlen_cntr;
    reg [1:0] axi_arburst;
    reg [1:0] axi_awburst;
    reg [7:0] axi_arlen;
    reg [7:0] axi_awlen;

    localparam integer C_ADDR_LSB = (C_S_AXI_DATA_WIDTH/32)+ 1;
    //----------------------------------------------
    //-- signals for user logic memory space example
    //------------------------------------------------
  localparam integer C_READY = 2'd0,
                                    C_WAIT_ACK = 2'd1,
                                    C_WAIT_RDY = 2'd2;
  reg servicing; 
    reg axi_wready_wlast; 
  reg [1 : 0] state;
  reg [C_S_AXI_DATA_WIDTH - 1 : 0] cache_data_in_r;

    // i/o connections assignments

    assign s_axi_awready    = axi_awready;
    assign s_axi_wready = axi_wready;
    assign s_axi_bresp  = axi_bresp;
    assign s_axi_buser  = axi_buser;
    assign s_axi_bvalid = axi_bvalid;
    assign s_axi_arready    = axi_arready;
    assign s_axi_rdata  = axi_rdata;
    assign s_axi_rresp  = axi_rresp;
    assign s_axi_rlast  = axi_rlast;
    assign s_axi_ruser  = axi_ruser;
    assign s_axi_rvalid = axi_rvalid;
    assign s_axi_bid = s_axi_awid;
    assign s_axi_rid = s_axi_arid;
    assign  aw_wrap_size = (C_S_AXI_DATA_WIDTH/8 * (axi_awlen)); 
    assign  ar_wrap_size = (C_S_AXI_DATA_WIDTH/8 * (axi_arlen)); 
    assign  aw_wrap_en = ((axi_awaddr & aw_wrap_size) == aw_wrap_size)? 1'b1: 1'b0;
    assign  ar_wrap_en = ((axi_araddr & ar_wrap_size) == ar_wrap_size)? 1'b1: 1'b0;

    // implement axi_awready generation
    // axi_awready is asserted for one s_axi_aclk clock cycle when both
    // s_axi_awvalid and s_axi_wvalid are asserted. axi_awready is
    // de-asserted when reset is low.
    always @( posedge s_axi_aclk )
    begin
      if ( s_axi_aresetn == 1'b0 )
        begin
          axi_awready <= 1'b0;
          axi_awv_awr_flag <= 1'b0;
        axi_wready_wlast <= 1'b0;
        end 
      else
        begin    
        axi_wready_wlast <= (axi_wready && axi_wlast) || axi_wready_wlast; 
          if (~axi_awready && s_axi_awvalid && ~axi_awv_awr_flag && ~axi_arv_arr_flag)
            begin
              // slave is ready to accept an address and
              // associated control signals
              axi_awready <= 1'b1;
              axi_awv_awr_flag  <= 1'b1; 
              // used for generation of bresp() and bvalid
            end
        else if (axi_wready_wlast && !servicing)          
            // preparing to accept next address after current write burst tx completion
            begin
              axi_awv_awr_flag  <= 1'b0;
            axi_wready_wlast <= 1'b0;
            end
          else        
            begin
              axi_awready <= 1'b0;
            end
        end 
    end    
    
    // implement axi_awaddr latching
    // this process is used to latch the address when both 
    // s_axi_awvalid and s_axi_wvalid are valid. 
    always @( posedge s_axi_aclk )
    begin
      if ( s_axi_aresetn == 1'b0 )
        begin
          axi_awaddr <= 0;
          axi_awlen_cntr <= 0;
          axi_awburst <= 0;
          axi_awlen <= 0;
        end 
      else
        begin    
          if (~axi_awready && s_axi_awvalid && ~axi_awv_awr_flag)
            begin
              // address latching 
              axi_awaddr <= s_axi_awaddr[C_S_AXI_ADDR_WIDTH - 1:0];  
              axi_awburst <= s_axi_awburst; 
              axi_awlen <= s_axi_awlen;     
              // start address of transfer
              axi_awlen_cntr <= 0;
            end   
          else if((axi_awlen_cntr <= axi_awlen) && axi_wready && s_axi_wvalid)        
            begin

              axi_awlen_cntr <= axi_awlen_cntr + 1;

              case (axi_awburst)
                2'b00: // fixed burst
                // the write address for all the beats in the transaction are fixed
                  begin
                    axi_awaddr <= axi_awaddr;          
                    //for awsize = 4 bytes (010)
                  end   
                2'b01: //incremental burst
                // the write address for all the beats in the transaction are increments by awsize
                  begin
                    axi_awaddr[C_S_AXI_ADDR_WIDTH - 1:C_ADDR_LSB] <= axi_awaddr[C_S_AXI_ADDR_WIDTH - 1:C_ADDR_LSB] + 1;
                    //awaddr aligned to 4 byte boundary
                    axi_awaddr[C_ADDR_LSB-1:0]  <= {C_ADDR_LSB{1'b0}};   
                    //for awsize = 4 bytes (010)
                  end   
                2'b10: //wrapping burst
                // the write address wraps when the address reaches wrap boundary 
                  if (aw_wrap_en)
                    begin
                      axi_awaddr <= (axi_awaddr - aw_wrap_size); 
                    end
                  else 
                    begin
                      axi_awaddr[C_S_AXI_ADDR_WIDTH - 1:C_ADDR_LSB] <= axi_awaddr[C_S_AXI_ADDR_WIDTH - 1:C_ADDR_LSB] + 1;
                      axi_awaddr[C_ADDR_LSB-1:0]  <= {C_ADDR_LSB{1'b0}}; 
                    end                      
                default: //reserved (incremental burst for example)
                  begin
                    axi_awaddr <= axi_awaddr[C_S_AXI_ADDR_WIDTH - 1:C_ADDR_LSB] + 1;
                    //for awsize = 4 bytes (010)
                  end
              endcase              
            end
        end 
    end   
    
    // implement axi_wready generation
    // axi_wready is asserted for one s_axi_aclk clock cycle when both
    // s_axi_awvalid and s_axi_wvalid are asserted. axi_wready is 
    // de-asserted when reset is low. 
    always @( posedge s_axi_aclk )
    begin
      if ( s_axi_aresetn == 1'b0 )
        begin
          axi_wready <= 1'b0;
        end 
      else
        begin    
        if ( ~axi_wready && s_axi_wvalid && axi_awv_awr_flag && !servicing)
            begin
              // slave can accept the write data
              axi_wready <= 1'b1;
            end
        else if ((s_axi_wlast && axi_wready) || servicing)
            begin
              axi_wready <= 1'b0;
            end
        end 
    end     
    
    // implement write response logic generation
    // the write response and response valid signals are asserted by the slave 
    // when axi_wready, s_axi_wvalid, axi_wready and s_axi_wvalid are asserted.  
    // this marks the acceptance of address and indicates the status of 
    // write transaction.
    always @( posedge s_axi_aclk )
    begin
      if ( s_axi_aresetn == 1'b0 )
        begin
          axi_bvalid <= 0;
          axi_bresp <= 2'b0;
          axi_buser <= 0;
        end 
      else
        begin   
        if (axi_awv_awr_flag && s_axi_wvalid && ~axi_bvalid && axi_wready_wlast && ~servicing)
            begin
              axi_bvalid <= 1'b1;
              axi_bresp  <= 2'b0; 
              // 'okay' response 
            end                   
          else
            begin
              if (s_axi_bready && axi_bvalid) 
              //check if bready is asserted while bvalid is high) 
              //(there is a possibility that bready is always asserted high)   
                begin
                  axi_bvalid <= 1'b0; 
                end  
            end
        end
     end   
    
    // implement axi_arready generation
    // axi_arready is asserted for one s_axi_aclk clock cycle when
    // s_axi_arvalid is asserted. axi_awready is 
    // de-asserted when reset (active low) is asserted. 
    // the read address is also latched when s_axi_arvalid is 
    // asserted. axi_araddr is reset to zero on reset assertion.
    always @( posedge s_axi_aclk )
    begin
      if ( s_axi_aresetn == 1'b0 )
        begin
          axi_arready <= 1'b0;
          axi_arv_arr_flag <= 1'b0;
        end 
      else
        begin    
          if (~axi_arready && s_axi_arvalid && ~axi_awv_awr_flag && ~axi_arv_arr_flag)
            begin
              axi_arready <= 1'b1;
              axi_arv_arr_flag <= 1'b1;
            end
          else if (axi_rvalid && s_axi_rready && axi_arlen_cntr == axi_arlen)
          // preparing to accept next address after current read completion
            begin
              axi_arv_arr_flag  <= 1'b0;
            end
          else        
            begin
              axi_arready <= 1'b0;
            end
        end 
    end  
    
    // implement axi_araddr latching
    //this process is used to latch the address when both 
    //s_axi_arvalid and s_axi_rvalid are valid. 
    always @( posedge s_axi_aclk )
    begin
      if ( s_axi_aresetn == 1'b0 )
        begin
          axi_araddr <= 0;
          axi_arlen_cntr <= 0;
          axi_arburst <= 0;
          axi_arlen <= 0;
          axi_rlast <= 1'b0;
          axi_ruser <= 0;
        end 
      else
        begin    
          if (~axi_arready && s_axi_arvalid && ~axi_arv_arr_flag)
            begin
              // address latching 
              axi_araddr <= s_axi_araddr[C_S_AXI_ADDR_WIDTH - 1:0]; 
              axi_arburst <= s_axi_arburst; 
              axi_arlen <= s_axi_arlen;     
              // start address of transfer
              axi_arlen_cntr <= 0;
              axi_rlast <= 1'b0;
            end   
          else if((axi_arlen_cntr <= axi_arlen) && axi_rvalid && s_axi_rready)        
            begin
             
              axi_arlen_cntr <= axi_arlen_cntr + 1;
              axi_rlast <= 1'b0;
            
              case (axi_arburst)
                2'b00: // fixed burst
                 // the read address for all the beats in the transaction are fixed
                  begin
                    axi_araddr       <= axi_araddr;        
                    //for arsize = 4 bytes (010)
                  end   
                2'b01: //incremental burst
                // the read address for all the beats in the transaction are increments by awsize
                  begin
                    axi_araddr[C_S_AXI_ADDR_WIDTH - 1:C_ADDR_LSB] <= axi_araddr[C_S_AXI_ADDR_WIDTH - 1:C_ADDR_LSB] + 1; 
                    //araddr aligned to 4 byte boundary
                    axi_araddr[C_ADDR_LSB-1:0]  <= {C_ADDR_LSB{1'b0}};   
                    //for awsize = 4 bytes (010)
                  end   
                2'b10: //wrapping burst
                // the read address wraps when the address reaches wrap boundary 
                  if (ar_wrap_en) 
                    begin
                      axi_araddr <= (axi_araddr - ar_wrap_size); 
                    end
                  else 
                    begin
                    axi_araddr[C_S_AXI_ADDR_WIDTH - 1:C_ADDR_LSB] <= axi_araddr[C_S_AXI_ADDR_WIDTH - 1:C_ADDR_LSB] + 1; 
                    //araddr aligned to 4 byte boundary
                    axi_araddr[C_ADDR_LSB-1:0]  <= {C_ADDR_LSB{1'b0}};   
                    end                      
                default: //reserved (incremental burst for example)
                  begin
                    axi_araddr <= axi_araddr[C_S_AXI_ADDR_WIDTH - 1:C_ADDR_LSB]+1;
                    //for arsize = 4 bytes (010)
                  end
              endcase              
            end
          else if((axi_arlen_cntr == axi_arlen) && ~axi_rlast && axi_arv_arr_flag )   
            begin
              axi_rlast <= 1'b1;
            end          
          else if (s_axi_rready)   
            begin
              axi_rlast <= 1'b0;
            end          
        end 
    end 
    
    // implement axi_arvalid generation
    // axi_rvalid is asserted for one s_axi_aclk clock cycle when both 
    // s_axi_arvalid and axi_arready are asserted. the slave registers 
    // data are available on the axi_rdata bus at this instance. the 
    // assertion of axi_rvalid marks the validity of read data on the 
    // bus and axi_rresp indicates the status of read transaction.axi_rvalid 
    // is deasserted on reset (active low). axi_rresp and axi_rdata are 
    // cleared to zero on reset (active low).  
    always @( posedge s_axi_aclk )
    begin
      if ( s_axi_aresetn == 1'b0 )
        begin
          axi_rvalid <= 0;
          axi_rresp  <= 0;
        end 
      else
        begin    
        if (axi_arv_arr_flag && ~axi_rvalid && !servicing)
            begin
              axi_rvalid <= 1'b1;
              axi_rresp  <= 2'b0; 
              // 'okay' response
            end   
        else if ((axi_rvalid && s_axi_rready) || servicing) 
            begin
              axi_rvalid <= 1'b0;
            end            
        end
    end    
    
  // forward requests to cache! 
  always @(posedge s_axi_clk) begin
    if(s_axi_aresetn == 1'b0) begin
      state <= C_READY;
      servicing <= 1'b0; 
      
      cache_req_out <= 1'b0;
      cache_wen <= 1'b0;
      cache_addr_out <= 0; 
      cache_data_out <= 0; 
      cache_wstrb <= 0;
      
      cache_data_in_r <= 0; 
    end
    else begin
      case(state)
        // ready to accept requests in this state. if read/write request
        // set cache signals appropriate and indicate servicing is occuring.
        // tranisiton to C_WAIT_ACK and wait for cache to acknowledge request
        C_READY: begin
          if(axi_wready && s_axi_wvalid)
            cache_req_out <= 1'b1;
            cache_addr_out <= axi_awaddr;
            cache_data_out <= s_axi_wdata;
            cache_wen <= 1'b1;
            cache_wstb <= s_axi_wstrb;

            servicing <= 1'b1;

            state <= C_WAIT_ACK; // reg to add
          end 
          else if(axi_arv_arr_flag) begin
            cache_req_out <= 1'b1;
            cache_addr_out <= axi_araddr;
            cache_wen <= 1'b0;

            servicing <= 1'b1;

            state <= C_WAIT_ACK; // reg to add
          end
          else begin
            state <= C_READY;
          end
        end
        // wait for acknowledgment from cache (deassert cache_rdy).
        // remain in this state until acknowledge received. 
        C_WAIT_ACK: begin
          if(!cache_rdy) begin
            cache_req_out <= 1'b0; 
            state <= C_WAIT_RDY;
          end 
          else begin
            state <= C_WAIT_ACK; 
          end
        end
        // now that request is acknowledged, wait for the request to finish.
        // set the servicing signal appropriately when cache request finished. 
        C_WAIT_RDY: begin
          if(cache_rdy) begin
            servicing <= 1'b0; 
            
            if(!cache_wen) begin
              cache_data_in_r <= cache_data_in; 
            end
            
            state <= C_READY;
          end 
          else begin
            state <= C_WAIT_RDY; 
          end
        end
      endcase
    end
  end
     
  // set output data correctly when axi_rvalid is asserted.
  // for rvalid to be asserted, the cache must have finished servicing
  // i.e. the correct read data 
  always @(*) begin
      if (axi_rvalid) 
        begin
          axi_rdata <= cache_data_in_r;
        end   
      else
        begin
          axi_rdata <= 32'h00000000;
        end       
    end
    
endmodule

