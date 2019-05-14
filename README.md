# random verification stuff for a cache controller

Modules: 
- ram.v : basic read/write memory
- cache_way.v : includes data ram and tag ram
- cache_4way.v : instantiates 4 cache_ways; includes select logic
- lookup.v : hit/miss/replacement logic for 4 way set-associative cache
- cache_controller.v : functioning 4-way, set-associative writethrough cache using pseudo-LRU replacement
- omi_cache_controller.v : OMI (Our Memory Interface) compliant wrapper for cache controller
- axi_cache_slave.v : xilinx provided axi slave template with untested modifications :(
- axi_cache_master.v : xilinx provided axi master template with no modifications :( 

Notes: 
- We didn't get to finish the AXI implementations! These files are auto-generated Xilinx AXI IP. We do not claim we wrote these! 

Verification files:
- Each file listed above (other than the AXI files) has verification collateral:
  - .sv file containing relevant assumes and assertions.
  - .tcl source file for JasperGold.
- To run any of the verification files, source the .tcl file in JasperGold. 

Other relevant files:
- props_pkg.sv : contains parameterized properties for commonly used assertions/assumptions
- intf_props_pkg.sv : contains parameterized properties specifically dedicated to interface behavior
  - includes macros for each of verification with our design. 