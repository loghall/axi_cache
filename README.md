# axi_cache

Brief description of cache modules:
  ram.v: basic read/write memory
  cache_way.v: data_ram and tag_ram
  cache_4way.v: 4 cache_ways with way select signal
  lookup.v: hit/miss logic; replacement logic 
  cache_controller.v - high level cache functionality built with preceding modules 
  omi_cache_controller.v - OMI (Our Memory Interface) compliant wrapper for cache controller
  axi_cache_master.v - Sends cache/cpu requests to memory
  axi_cache_slave.v - Receives memory operations from the cpu

Verification files:
  Other than the axi_cache_master and axi_cache_slave verilog files, all other files have a corresponding SytemVerilog file
  To run verification
