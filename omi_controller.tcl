clear -all
analyze -sv omi_cache_controller.v
analyze -sv cache_controller.v
analyze -sv props_pkg.sv
analyze -sv intf_props_pkg.sv
analyze -sv omi_cache_controller.sv
elaborate -bbox_m {cache_4way} -bbox_m {lookup} -top cache
clock clk
reset -expression {!reset_n}
prove -bg -all

