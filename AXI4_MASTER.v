
`timescale 1 ns / 1 ps

	module myip4_v1_0_m00_axi #
	(
		// users to add parameters here

		// user parameters ends
		// do not modify the parameters beyond this line

		// base address of targeted slave
		parameter  c_m_target_slave_base_addr	= 32'h40000000,

		// burst length. supports 1, 2, 4, 8, 16, 32, 64, 128, 256 burst lengths
		parameter integer c_m_axi_burst_len	= 16,

		// thread id width
		parameter integer c_m_axi_id_width	= 1,

		// width of address bus
		parameter integer c_m_axi_addr_width	= 32,

		// width of data bus
		parameter integer c_m_axi_data_width	= 32,

		// width of user write address bus
		parameter integer c_m_axi_awuser_width	= 0,

		// width of user read address bus
		parameter integer c_m_axi_aruser_width	= 0,

		// width of user write data bus
		parameter integer c_m_axi_wuser_width	= 0,

		// width of user read data bus
		parameter integer c_m_axi_ruser_width	= 0,

		// width of user response bus
		parameter integer c_m_axi_buser_width	= 0
	)
	(
		// users to add ports here

		// user ports ends
	

		// initiate axi transactions
		input wire  init_axi_txn,

		// asserts when transaction is complete
		output wire  txn_done,

		// asserts when error is detected
		output reg  error,

		// global clock signal.
		input wire  m_axi_aclk,

		// global reset singal. this signal is active low
		input wire  m_axi_aresetn,

		// master interface write address id
		output wire [c_m_axi_id_width-1 : 0] m_axi_awid,

		// master interface write address
		output wire [c_m_axi_addr_width-1 : 0] m_axi_awaddr,

		// burst length. the burst length gives the exact number of transfers in a burst
		output wire [7 : 0] m_axi_awlen,

		// burst size. this signal indicates the size of each transfer in the burst
		output wire [2 : 0] m_axi_awsize,

		// burst type. the burst type and the size information, 
    // determine how the address for each transfer within the burst is calculated.
		output wire [1 : 0] m_axi_awburst,

		// lock type. provides additional information about the
    // atomic characteristics of the transfer.
		output wire  m_axi_awlock,

		// memory type. this signal indicates how transactions
    // are required to progress through a system.
		output wire [3 : 0] m_axi_awcache,

		// protection type. this signal indicates the privilege
    // and security level of the transaction, and whether
    // the transaction is a data access or an instruction access.
		output wire [2 : 0] m_axi_awprot,

		// quality of service, qos identifier sent for each write transaction.
		output wire [3 : 0] m_axi_awqos,

		// optional user-defined signal in the write address channel.
		output wire [c_m_axi_awuser_width-1 : 0] m_axi_awuser,

		// write address valid. this signal indicates that
    // the channel is signaling valid write address and control information.
		output wire  m_axi_awvalid,

		// write address ready. this signal indicates that
    // the slave is ready to accept an address and associated control signals
		input wire  m_axi_awready,

		// master interface write data.
		output wire [c_m_axi_data_width-1 : 0] m_axi_wdata,

		// write strobes. this signal indicates which byte
    // lanes hold valid data. there is one write strobe
    // bit for each eight bits of the write data bus.
		output wire [c_m_axi_data_width/8-1 : 0] m_axi_wstrb,

		// write last. this signal indicates the last transfer in a write burst.
		output wire  m_axi_wlast,

		// optional user-defined signal in the write data channel.
		output wire [c_m_axi_wuser_width-1 : 0] m_axi_wuser,

		// write valid. this signal indicates that valid write
    // data and strobes are available
		output wire  m_axi_wvalid,

		// write ready. this signal indicates that the slave
    // can accept the write data.
		input wire  m_axi_wready,

		// master interface write response.
		input wire [c_m_axi_id_width-1 : 0] m_axi_bid,

		// write response. this signal indicates the status of the write transaction.
		input wire [1 : 0] m_axi_bresp,

		// optional user-defined signal in the write response channel
		input wire [c_m_axi_buser_width-1 : 0] m_axi_buser,

		// write response valid. this signal indicates that the
    // channel is signaling a valid write response.
		input wire  m_axi_bvalid,

		// response ready. this signal indicates that the master
    // can accept a write response.
		output wire  m_axi_bready,

		// master interface read address.
		output wire [c_m_axi_id_width-1 : 0] m_axi_arid,

		// read address. this signal indicates the initial
    // address of a read burst transaction.
		output wire [c_m_axi_addr_width-1 : 0] m_axi_araddr,

		// burst length. the burst length gives the exact number of transfers in a burst
		output wire [7 : 0] m_axi_arlen,

		// burst size. this signal indicates the size of each transfer in the burst
		output wire [2 : 0] m_axi_arsize,

		// burst type. the burst type and the size information, 
    // determine how the address for each transfer within the burst is calculated.
		output wire [1 : 0] m_axi_arburst,

		// lock type. provides additional information about the
    // atomic characteristics of the transfer.
		output wire  m_axi_arlock,

		// memory type. this signal indicates how transactions
    // are required to progress through a system.
		output wire [3 : 0] m_axi_arcache,

		// protection type. this signal indicates the privilege
    // and security level of the transaction, and whether
    // the transaction is a data access or an instruction access.
		output wire [2 : 0] m_axi_arprot,

		// quality of service, qos identifier sent for each read transaction
		output wire [3 : 0] m_axi_arqos,

		// optional user-defined signal in the read address channel.
		output wire [c_m_axi_aruser_width-1 : 0] m_axi_aruser,

		// write address valid. this signal indicates that
    // the channel is signaling valid read address and control information
		output wire  m_axi_arvalid,

		// read address ready. this signal indicates that
    // the slave is ready to accept an address and associated control signals
		input wire  m_axi_arready,

		// read id tag. this signal is the identification tag
    // for the read data group of signals generated by the slave.
		input wire [c_m_axi_id_width-1 : 0] m_axi_rid,

		// master read data
		input wire [c_m_axi_data_width-1 : 0] m_axi_rdata,

		// read response. this signal indicates the status of the read transfer
		input wire [1 : 0] m_axi_rresp,

		// read last. this signal indicates the last transfer in a read burst
		input wire  m_axi_rlast,

		// optional user-defined signal in the read address channel.
		input wire [c_m_axi_ruser_width-1 : 0] m_axi_ruser,

		// read valid. this signal indicates that the channel
    // is signaling the required read data.
		input wire  m_axi_rvalid,

		// read ready. this signal indicates that the master can
    // accept the read data and response information.
		output wire  m_axi_rready
	);


	// function called clogb2 that returns an integer which has the
	//value of the ceiling of the log base 2

	  // function called clogb2 that returns an integer which has the 
	  // value of the ceiling of the log base 2.                      
	  function integer clogb2 (input integer bit_depth);              
	  begin                                                           
	    for(clogb2=0; bit_depth>0; clogb2=clogb2+1)                   
	      bit_depth = bit_depth >> 1;                                 
	    end                                                           
	  endfunction                                                     

	// c_transactions_num is the width of the index counter for 
	// number of write or read transaction.
	 localparam integer c_transactions_num = clogb2(c_m_axi_burst_len-1);

	// burst length for transactions, in c_m_axi_data_widths.
	// non-2^n lengths will eventually cause bursts across 4k address boundaries.
	 localparam integer c_master_length	= 12;

	// total number of burst transfers is master length divided by burst length and burst size
	 localparam integer c_no_bursts_req = c_master_length-clogb2((c_m_axi_burst_len*c_m_axi_data_width/8)-1);

	// example state machine to initialize counter, initialize write transactions, 
	// initialize read transactions and comparison of read data with the 
	// written data words.
	parameter [1:0] idle = 2'b00, // this state initiates axi4lite transaction 
			// after the state machine changes state to init_write 
			// when there is 0 to 1 transition on init_axi_txn
		init_write   = 2'b01, // this state initializes write transaction,

			// once writes are done, the state machine 
			// changes state to init_read 
		init_read = 2'b10, // this state initializes read transaction

			// once reads are done, the state machine 
			// changes state to init_compare 

		init_compare = 2'b11; // this state issues the status of comparison 
			// of the written data with the read data	

	 reg [1:0] mst_exec_state;

	// axi4lite signals
	//axi4 internal temp signals
	reg [c_m_axi_addr_width-1 : 0] 	axi_awaddr;
	reg  	axi_awvalid;
	reg [c_m_axi_data_width-1 : 0] 	axi_wdata;
	reg  	axi_wlast;
	reg  	axi_wvalid;
	reg  	axi_bready;
	reg [c_m_axi_addr_width-1 : 0] 	axi_araddr;
	reg  	axi_arvalid;
	reg  	axi_rready;
	//write beat count in a burst
	reg [c_transactions_num : 0] 	write_index;

	//read beat count in a burst
	reg [c_transactions_num : 0] 	read_index;

	//size of c_m_axi_burst_len length burst in bytes
	wire [c_transactions_num+2 : 0] 	burst_size_bytes;

	//the burst counters are used to track the number of burst transfers of c_m_axi_burst_len burst length needed to transfer 2^c_master_length bytes of data.
	reg [c_no_bursts_req : 0] 	write_burst_counter;

	reg [c_no_bursts_req : 0] 	read_burst_counter;
	reg  	start_single_burst_write;
	reg  	start_single_burst_read;
	reg  	writes_done;
	reg  	reads_done;
	reg  	error_reg;
	reg  	compare_done;
	reg  	read_mismatch;
	reg  	burst_write_active;
	reg  	burst_read_active;
	reg [c_m_axi_data_width-1 : 0] 	expected_rdata;

	//interface response error flags
	wire  	write_resp_error;
	wire  	read_resp_error;
	wire  	wnext;
	wire  	rnext;
	reg  	init_txn_ff;
	reg  	init_txn_ff2;
	reg  	init_txn_edge;
	wire  	init_txn_pulse;


	// i/o connections assignments

	//i/o connections. write address (aw)
	assign m_axi_awid	= 'b0;

	//the axi address is a concatenation of the target base address + active offset range
	assign m_axi_awaddr	= c_m_target_slave_base_addr + axi_awaddr;

	//burst length is number of transaction beats, minus 1
	assign m_axi_awlen	= c_m_axi_burst_len - 1;

	//size should be c_m_axi_data_width, in 2^size bytes, otherwise narrow bursts are used
	assign m_axi_awsize	= clogb2((c_m_axi_data_width/8)-1);

	//incr burst type is usually used, except for keyhole bursts
	assign m_axi_awburst	= 2'b01;

	assign m_axi_awlock	= 1'b0;

	//update value to 4'b0011 if coherent accesses to be used via the zynq acp port. not allocated, modifiable, not bufferable. not bufferable since this example is meant to test memory, not intermediate cache. 
	assign m_axi_awcache	= 4'b0010;

	assign m_axi_awprot	= 3'h0;
	assign m_axi_awqos	= 4'h0;
	assign m_axi_awuser	= 'b1;
	assign m_axi_awvalid	= axi_awvalid;
	
	//write data(w)
	assign m_axi_wdata	= axi_wdata;

	//all bursts are complete and aligned in this example
	assign m_axi_wstrb	= {(c_m_axi_data_width/8){1'b1}};

	assign m_axi_wlast	= axi_wlast;
	assign m_axi_wuser	= 'b0;
	assign m_axi_wvalid	= axi_wvalid;
	
	//write response (b)
	assign m_axi_bready	= axi_bready;

	//read address (ar)
	assign m_axi_arid	= 'b0;
	
	assign m_axi_araddr	= c_m_target_slave_base_addr + axi_araddr;
	
	//burst length is number of transaction beats, minus 1
	assign m_axi_arlen	= c_m_axi_burst_len - 1;
	
	//size should be c_m_axi_data_width, in 2^n bytes, otherwise narrow bursts are used
	assign m_axi_arsize	= clogb2((c_m_axi_data_width/8)-1);
	
	//incr burst type is usually used, except for keyhole bursts
	assign m_axi_arburst	= 2'b01;
	
	assign m_axi_arlock	= 1'b0;
	
	//update value to 4'b0011 if coherent accesses to be used via the zynq acp port. not allocated, modifiable, not bufferable. not bufferable since this example is meant to test memory, not intermediate cache. 
	assign m_axi_arcache	= 4'b0010;
	
	assign m_axi_arprot	= 3'h0;
	assign m_axi_arqos	= 4'h0;
	assign m_axi_aruser	= 'b1;
	assign m_axi_arvalid	= axi_arvalid;
	
	//read and read response (r)
	assign m_axi_rready	= axi_rready;
	
	//example design i/o
	assign txn_done	= compare_done;
	
	//burst size in bytes
	assign burst_size_bytes	= c_m_axi_burst_len * c_m_axi_data_width/8;
	
	assign init_txn_pulse	= (!init_txn_ff2) && init_txn_ff;


	//generate a pulse to initiate axi transaction.
	always @(posedge m_axi_aclk)										      
	  begin                                                                        
	    // initiates axi transaction delay    
	    if (m_axi_aresetn == 0 )                                                   
	      begin                                                                    
	        init_txn_ff <= 1'b0;                                                   
	        init_txn_ff2 <= 1'b0;                                                   
	      end                                                                               
	    else                                                                       
	      begin  
	        init_txn_ff <= init_axi_txn;
	        init_txn_ff2 <= init_txn_ff;                                                                 
	      end                                                                      
	  end     


	//--------------------
	//write address channel
	//--------------------

	// the purpose of the write address channel is to request the address and 
	// command information for the entire transaction.  it is a single beat
	// of information.

	// the axi4 write address channel in this example will continue to initiate
	// write commands as fast as it is allowed by the slave/interconnect.
	// the address will be incremented on each accepted address transaction,
	// by burst_size_byte to point to the next address. 

	  always @(posedge m_axi_aclk)                                   
	  begin                                                                
	                                                                       
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1 )                                           
	      begin                                                            
	        axi_awvalid <= 1'b0;                                           
	      end                                                              
	    // if previously not valid , start next transaction                
	    else if (~axi_awvalid && start_single_burst_write)                 
	      begin                                                            
	        axi_awvalid <= 1'b1;                                           
	      end                                                              
	    /* once asserted, valids cannot be deasserted, so axi_awvalid      
	    must wait until transaction is accepted */                         
	    else if (m_axi_awready && axi_awvalid)                             
	      begin                                                            
	        axi_awvalid <= 1'b0;                                           
	      end                                                              
	    else                                                               
	      axi_awvalid <= axi_awvalid;                                      
	    end                                                                
	                                                                       
	                                                                       
	// next address after awready indicates previous address acceptance    
	  always @(posedge m_axi_aclk)                                         
	  begin                                                                
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1)                                            
	      begin                                                            
	        axi_awaddr <= 'b0;                                             
	      end                                                              
	    else if (m_axi_awready && axi_awvalid)                             
	      begin                                                            
	        axi_awaddr <= axi_awaddr + burst_size_bytes;                   
	      end                                                              
	    else                                                               
	      axi_awaddr <= axi_awaddr;                                        
	    end                                                                


	//--------------------
	//write data channel
	//--------------------

	//the write data will continually try to push write data across the interface.

	//the amount of data accepted will depend on the axi slave and the axi
	//interconnect settings, such as if there are fifos enabled in interconnect.

	//note that there is no explicit timing relationship to the write address channel.
	//the write channel has its own throttling flag, separate from the aw channel.

	//synchronization between the channels must be determined by the user.

	//the simpliest but lowest performance would be to only issue one address write
	//and write data burst at a time.

	//in this example they are kept in sync by using the same address increment
	//and burst sizes. then the aw and w channels have their transactions measured
	//with threshold counters as part of the user logic, to make sure neither 
	//channel gets too far ahead of each other.

	//forward movement occurs when the write channel is valid and ready

	  assign wnext = m_axi_wready & axi_wvalid;                                   
	                                                                                    
	// wvalid logic, similar to the axi_awvalid always block above                      
	  always @(posedge m_axi_aclk)                                                      
	  begin                                                                             
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1 )                                                        
	      begin                                                                         
	        axi_wvalid <= 1'b0;                                                         
	      end                                                                           
	    // if previously not valid, start next transaction                              
	    else if (~axi_wvalid && start_single_burst_write)                               
	      begin                                                                         
	        axi_wvalid <= 1'b1;                                                         
	      end                                                                           
	    /* if wready and too many writes, throttle wvalid                               
	    once asserted, valids cannot be deasserted, so wvalid                           
	    must wait until burst is complete with wlast */                                 
	    else if (wnext && axi_wlast)                                                    
	      axi_wvalid <= 1'b0;                                                           
	    else                                                                            
	      axi_wvalid <= axi_wvalid;                                                     
	  end                                                                               
	                                                                                    
	                                                                                    
	//wlast generation on the msb of a counter underflow                                
	// wvalid logic, similar to the axi_awvalid always block above                      
	  always @(posedge m_axi_aclk)                                                      
	  begin                                                                             
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1 )                                                        
	      begin                                                                         
	        axi_wlast <= 1'b0;                                                          
	      end                                                                           
	    // axi_wlast is asserted when the write index                                   
	    // count reaches the penultimate count to synchronize                           
	    // with the last write data when write_index is b1111                           
	    // else if (&(write_index[c_transactions_num-1:1])&& ~write_index[0] && wnext)  
	    else if (((write_index == c_m_axi_burst_len-2 && c_m_axi_burst_len >= 2) && wnext) || (c_m_axi_burst_len == 1 ))
	      begin                                                                         
	        axi_wlast <= 1'b1;                                                          
	      end                                                                           
	    // deassrt axi_wlast when the last write data has been                          
	    // accepted by the slave with a valid response                                  
	    else if (wnext)                                                                 
	      axi_wlast <= 1'b0;                                                            
	    else if (axi_wlast && c_m_axi_burst_len == 1)                                   
	      axi_wlast <= 1'b0;                                                            
	    else                                                                            
	      axi_wlast <= axi_wlast;                                                       
	  end                                                                               
	                                                                                    
	                                                                                    
	/* burst length counter. uses extra counter register bit to indicate terminal       
	 count to reduce decode logic */                                                    
	  always @(posedge m_axi_aclk)                                                      
	  begin                                                                             
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1 || start_single_burst_write == 1'b1)    
	      begin                                                                         
	        write_index <= 0;                                                           
	      end                                                                           
	    else if (wnext && (write_index != c_m_axi_burst_len-1))                         
	      begin                                                                         
	        write_index <= write_index + 1;                                             
	      end                                                                           
	    else                                                                            
	      write_index <= write_index;                                                   
	  end                                                                               
	                                                                                    
	                                                                                    
	/* write data generator                                                             
	 data pattern is only a simple incrementing count from 0 for each burst  */         
	  always @(posedge m_axi_aclk)                                                      
	  begin                                                                             
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1)                                                         
	      axi_wdata <= 'b1;                                                             
	    //else if (wnext && axi_wlast)                                                  
	    //  axi_wdata <= 'b0;                                                           
	    else if (wnext)                                                                 
	      axi_wdata <= axi_wdata + 1;                                                   
	    else                                                                            
	      axi_wdata <= axi_wdata;                                                       
	    end                                                                             


	//----------------------------
	//write response (b) channel
	//----------------------------

	//the write response channel provides feedback that the write has committed
	//to memory. bready will occur when all of the data and the write address
	//has arrived and been accepted by the slave.

	//the write issuance (number of outstanding write addresses) is started by 
	//the address write transfer, and is completed by a bready/bresp.

	//while negating bready will eventually throttle the awready signal, 
	//it is best not to throttle the whole data channel this way.

	//the bresp bit [1] is used indicate any errors from the interconnect or
	//slave for the entire write burst. this example will capture the error 
	//into the error output. 

	  always @(posedge m_axi_aclk)                                     
	  begin                                                                 
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1 )                                            
	      begin                                                             
	        axi_bready <= 1'b0;                                             
	      end                                                               
	    // accept/acknowledge bresp with axi_bready by the master           
	    // when m_axi_bvalid is asserted by slave                           
	    else if (m_axi_bvalid && ~axi_bready)                               
	      begin                                                             
	        axi_bready <= 1'b1;                                             
	      end                                                               
	    // deassert after one clock cycle                                   
	    else if (axi_bready)                                                
	      begin                                                             
	        axi_bready <= 1'b0;                                             
	      end                                                               
	    // retain the previous value                                        
	    else                                                                
	      axi_bready <= axi_bready;                                         
	  end                                                                   
	                                                                        
	                                                                        
	//flag any write response errors                                        
	  assign write_resp_error = axi_bready & m_axi_bvalid & m_axi_bresp[1]; 


	//----------------------------
	//read address channel
	//----------------------------

	//the read address channel (aw) provides a similar function to the
	//write address channel- to provide the tranfer qualifiers for the burst.

	//in this example, the read address increments in the same
	//manner as the write address channel.

	  always @(posedge m_axi_aclk)                                 
	  begin                                                              
	                                                                     
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1 )                                         
	      begin                                                          
	        axi_arvalid <= 1'b0;                                         
	      end                                                            
	    // if previously not valid , start next transaction              
	    else if (~axi_arvalid && start_single_burst_read)                
	      begin                                                          
	        axi_arvalid <= 1'b1;                                         
	      end                                                            
	    else if (m_axi_arready && axi_arvalid)                           
	      begin                                                          
	        axi_arvalid <= 1'b0;                                         
	      end                                                            
	    else                                                             
	      axi_arvalid <= axi_arvalid;                                    
	  end                                                                
	                                                                     
	                                                                     
	// next address after arready indicates previous address acceptance  
	  always @(posedge m_axi_aclk)                                       
	  begin                                                              
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1)                                          
	      begin                                                          
	        axi_araddr <= 'b0;                                           
	      end                                                            
	    else if (m_axi_arready && axi_arvalid)                           
	      begin                                                          
	        axi_araddr <= axi_araddr + burst_size_bytes;                 
	      end                                                            
	    else                                                             
	      axi_araddr <= axi_araddr;                                      
	  end                                                                


	//--------------------------------
	//read data (and response) channel
	//--------------------------------

	 // forward movement occurs when the channel is valid and ready   
	  assign rnext = m_axi_rvalid && axi_rready;                            
	                                                                        
	                                                                        
	// burst length counter. uses extra counter register bit to indicate    
	// terminal count to reduce decode logic                                
	  always @(posedge m_axi_aclk)                                          
	  begin                                                                 
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1 || start_single_burst_read)                  
	      begin                                                             
	        read_index <= 0;                                                
	      end                                                               
	    else if (rnext && (read_index != c_m_axi_burst_len-1))              
	      begin                                                             
	        read_index <= read_index + 1;                                   
	      end                                                               
	    else                                                                
	      read_index <= read_index;                                         
	  end                                                                   
	                                                                        
	                                                                        
	/*                                                                      
	 the read data channel returns the results of the read request          
	                                                                        
	 in this example the data checker is always able to accept              
	 more data, so no need to throttle the rready signal                    
	 */                                                                     
	  always @(posedge m_axi_aclk)                                          
	  begin                                                                 
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1 )                  
	      begin                                                             
	        axi_rready <= 1'b0;                                             
	      end                                                               
	    // accept/acknowledge rdata/rresp with axi_rready by the master     
	    // when m_axi_rvalid is asserted by slave                           
	    else if (m_axi_rvalid)                       
	      begin                                      
	         if (m_axi_rlast && axi_rready)          
	          begin                                  
	            axi_rready <= 1'b0;                  
	          end                                    
	         else                                    
	           begin                                 
	             axi_rready <= 1'b1;                 
	           end                                   
	      end                                        
	    // retain the previous value                 
	  end                                            
	                                                                        
	//check received read data against data generator                       
	  always @(posedge m_axi_aclk)                                          
	  begin                                                                 
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1)                   
	      begin                                                             
	        read_mismatch <= 1'b0;                                          
	      end                                                               
	    //only check data when rvalid is active                             
	    else if (rnext && (m_axi_rdata != expected_rdata))                  
	      begin                                                             
	        read_mismatch <= 1'b1;                                          
	      end                                                               
	    else                                                                
	      read_mismatch <= 1'b0;                                            
	  end                                                                   
	                                                                        
	//flag any read response errors                                         
	  assign read_resp_error = axi_rready & m_axi_rvalid & m_axi_rresp[1];  


	//----------------------------------------
	//example design read check data generator
	//-----------------------------------------

	//generate expected read data to check against actual read data

	  always @(posedge m_axi_aclk)                     
	  begin                                                  
		if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1)// || m_axi_rlast)             
			expected_rdata <= 'b1;                            
		else if (m_axi_rvalid && axi_rready)                  
			expected_rdata <= expected_rdata + 1;             
		else                                                  
			expected_rdata <= expected_rdata;                 
	  end                                                    


	//----------------------------------
	//example design error register
	//----------------------------------

	//register and hold any data mismatches, or read/write interface errors 

	  always @(posedge m_axi_aclk)                                 
	  begin                                                              
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1)                                          
	      begin                                                          
	        error_reg <= 1'b0;                                           
	      end                                                            
	    else if (read_mismatch || write_resp_error || read_resp_error)   
	      begin                                                          
	        error_reg <= 1'b1;                                           
	      end                                                            
	    else                                                             
	      error_reg <= error_reg;                                        
	  end                                                                


	//--------------------------------
	//example design throttling
	//--------------------------------

	// for maximum port throughput, this user example code will try to allow
	// each channel to run as independently and as quickly as possible.

	// however, there are times when the flow of data needs to be throtted by
	// the user application. this example application requires that data is
	// not read before it is written and that the write channels do not
	// advance beyond an arbitrary threshold (say to prevent an 
	// overrun of the current read address by the write address).

	// from axi4 specification, 13.13.1: "if a master requires ordering between 
	// read and write transactions, it must ensure that a response is received 
	// for the previous transaction before issuing the next transaction."

	// this example accomplishes this user application throttling through:
	// -reads wait for writes to fully complete
	// -address writes wait when not read + issued transaction counts pass 
	// a parameterized threshold
	// -writes wait when a not read + active data burst count pass 
	// a parameterized threshold

	 // write_burst_counter counter keeps track with the number of burst transaction initiated            
	 // against the number of burst transactions the master needs to initiate                                   
	  always @(posedge m_axi_aclk)                                                                              
	  begin                                                                                                     
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1 )                                                                                 
	      begin                                                                                                 
	        write_burst_counter <= 'b0;                                                                         
	      end                                                                                                   
	    else if (m_axi_awready && axi_awvalid)                                                                  
	      begin                                                                                                 
	        if (write_burst_counter[c_no_bursts_req] == 1'b0)                                                   
	          begin                                                                                             
	            write_burst_counter <= write_burst_counter + 1'b1;                                              
	            //write_burst_counter[c_no_bursts_req] <= 1'b1;                                                 
	          end                                                                                               
	      end                                                                                                   
	    else                                                                                                    
	      write_burst_counter <= write_burst_counter;                                                           
	  end                                                                                                       
	                                                                                                            
	 // read_burst_counter counter keeps track with the number of burst transaction initiated                   
	 // against the number of burst transactions the master needs to initiate                                   
	  always @(posedge m_axi_aclk)                                                                              
	  begin                                                                                                     
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1)                                                                                 
	      begin                                                                                                 
	        read_burst_counter <= 'b0;                                                                          
	      end                                                                                                   
	    else if (m_axi_arready && axi_arvalid)                                                                  
	      begin                                                                                                 
	        if (read_burst_counter[c_no_bursts_req] == 1'b0)                                                    
	          begin                                                                                             
	            read_burst_counter <= read_burst_counter + 1'b1;                                                
	            //read_burst_counter[c_no_bursts_req] <= 1'b1;                                                  
	          end                                                                                               
	      end                                                                                                   
	    else                                                                                                    
	      read_burst_counter <= read_burst_counter;                                                             
	  end                                                                                                       
	                                                                                                            
	                                                                                                            
	  //implement master command interface state machine                                                        
	                                                                                                            
	  always @ ( posedge m_axi_aclk)                                                                            
	  begin                                                                                                     
	    if (m_axi_aresetn == 1'b0 )                                                                             
	      begin                                                                                                 
	        // reset condition                                                                                  
	        // all the signals are assigned default values under reset condition                                
	        mst_exec_state      <= idle;                                                                
	        start_single_burst_write <= 1'b0;                                                                   
	        start_single_burst_read  <= 1'b0;                                                                   
	        compare_done      <= 1'b0;                                                                          
	        error <= 1'b0;   
	      end                                                                                                   
	    else                                                                                                    
	      begin                                                                                                 
	                                                                                                            
	        // state transition                                                                                 
	        case (mst_exec_state)                                                                               
	                                                                                                            
	          idle:                                                                                     
	            // this state is responsible to wait for user defined c_m_start_count                           
	            // number of clock cycles.                                                                      
	            if ( init_txn_pulse == 1'b1)                                                      
	              begin                                                                                         
	                mst_exec_state  <= init_write;                                                              
	                error <= 1'b0;
	                compare_done <= 1'b0;
	              end                                                                                           
	            else                                                                                            
	              begin                                                                                         
	                mst_exec_state  <= idle;                                                            
	              end                                                                                           
	                                                                                                            
	          init_write:                                                                                       
	            // this state is responsible to issue start_single_write pulse to                               
	            // initiate a write transaction. write transactions will be                                     
	            // issued until burst_write_active signal is asserted.                                          
	            // write controller                                                                             
	            if (writes_done)                                                                                
	              begin                                                                                         
	                mst_exec_state <= init_read;//                                                              
	              end                                                                                           
	            else                                                                                            
	              begin                                                                                         
	                mst_exec_state  <= init_write;                                                              
	                                                                                                            
	                if (~axi_awvalid && ~start_single_burst_write && ~burst_write_active)                       
	                  begin                                                                                     
	                    start_single_burst_write <= 1'b1;                                                       
	                  end                                                                                       
	                else                                                                                        
	                  begin                                                                                     
	                    start_single_burst_write <= 1'b0; //negate to generate a pulse                          
	                  end                                                                                       
	              end                                                                                           
	                                                                                                            
	          init_read:                                                                                        
	            // this state is responsible to issue start_single_read pulse to                                
	            // initiate a read transaction. read transactions will be                                       
	            // issued until burst_read_active signal is asserted.                                           
	            // read controller                                                                              
	            if (reads_done)                                                                                 
	              begin                                                                                         
	                mst_exec_state <= init_compare;                                                             
	              end                                                                                           
	            else                                                                                            
	              begin                                                                                         
	                mst_exec_state  <= init_read;                                                               
	                                                                                                            
	                if (~axi_arvalid && ~burst_read_active && ~start_single_burst_read)                         
	                  begin                                                                                     
	                    start_single_burst_read <= 1'b1;                                                        
	                  end                                                                                       
	               else                                                                                         
	                 begin                                                                                      
	                   start_single_burst_read <= 1'b0; //negate to generate a pulse                            
	                 end                                                                                        
	              end                                                                                           
	                                                                                                            
	          init_compare:                                                                                     
	            // this state is responsible to issue the state of comparison                                   
	            // of written data with the read data. if no error flags are set,                               
	            // compare_done signal will be asseted to indicate success.                                     
	            //if (~error_reg)                                                                               
	            begin                                                                                           
	              error <= error_reg;
	              mst_exec_state <= idle;                                                               
	              compare_done <= 1'b1;                                                                         
	            end                                                                                             
	          default :                                                                                         
	            begin                                                                                           
	              mst_exec_state  <= idle;                                                              
	            end                                                                                             
	        endcase                                                                                             
	      end                                                                                                   
	  end //master_execution_proc                                                                               
	                                                                                                            
	                                                                                                            
	  // burst_write_active signal is asserted when there is a burst write transaction                          
	  // is initiated by the assertion of start_single_burst_write. burst_write_active                          
	  // signal remains asserted until the burst write is accepted by the slave                                 
	  always @(posedge m_axi_aclk)                                                                              
	  begin                                                                                                     
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1)                                                                                 
	      burst_write_active <= 1'b0;                                                                           
	                                                                                                            
	    //the burst_write_active is asserted when a write burst transaction is initiated                        
	    else if (start_single_burst_write)                                                                      
	      burst_write_active <= 1'b1;                                                                           
	    else if (m_axi_bvalid && axi_bready)                                                                    
	      burst_write_active <= 0;                                                                              
	  end                                                                                                       
	                                                                                                            
	 // check for last write completion.                                                                        
	                                                                                                            
	 // this logic is to qualify the last write count with the final write                                      
	 // response. this demonstrates how to confirm that a write has been                                        
	 // committed.                                                                                              
	                                                                                                            
	  always @(posedge m_axi_aclk)                                                                              
	  begin                                                                                                     
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1)                                                                                 
	      writes_done <= 1'b0;                                                                                  
	                                                                                                            
	    //the writes_done should be associated with a bready response                                           
	    //else if (m_axi_bvalid && axi_bready && (write_burst_counter == {(c_no_bursts_req-1){1}}) && axi_wlast)
	    else if (m_axi_bvalid && (write_burst_counter[c_no_bursts_req]) && axi_bready)                          
	      writes_done <= 1'b1;                                                                                  
	    else                                                                                                    
	      writes_done <= writes_done;                                                                           
	    end                                                                                                     
	                                                                                                            
	  // burst_read_active signal is asserted when there is a burst write transaction                           
	  // is initiated by the assertion of start_single_burst_write. start_single_burst_read                     
	  // signal remains asserted until the burst read is accepted by the master                                 
	  always @(posedge m_axi_aclk)                                                                              
	  begin                                                                                                     
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1)                                                                                 
	      burst_read_active <= 1'b0;                                                                            
	                                                                                                            
	    //the burst_write_active is asserted when a write burst transaction is initiated                        
	    else if (start_single_burst_read)                                                                       
	      burst_read_active <= 1'b1;                                                                            
	    else if (m_axi_rvalid && axi_rready && m_axi_rlast)                                                     
	      burst_read_active <= 0;                                                                               
	    end                                                                                                     
	                                                                                                            
	                                                                                                            
	 // check for last read completion.                                                                         
	                                                                                                            
	 // this logic is to qualify the last read count with the final read                                        
	 // response. this demonstrates how to confirm that a read has been                                         
	 // committed.                                                                                              
	                                                                                                            
	  always @(posedge m_axi_aclk)                                                                              
	  begin                                                                                                     
	    if (m_axi_aresetn == 0 || init_txn_pulse == 1'b1)                                                                                 
	      reads_done <= 1'b0;                                                                                   
	                                                                                                            
	    //the reads_done should be associated with a rready response                                            
	    //else if (m_axi_bvalid && axi_bready && (write_burst_counter == {(c_no_bursts_req-1){1}}) && axi_wlast)
	    else if (m_axi_rvalid && axi_rready && (read_index == c_m_axi_burst_len-1) && (read_burst_counter[c_no_bursts_req]))
	      reads_done <= 1'b1;                                                                                   
	    else                                                                                                    
	      reads_done <= reads_done;                                                                             
	    end                                                                                                     

	// add user logic here

	// user logic ends

	endmodule
