clear -all
analyze -sv cache_controller.v
#analyze -v2k axi_cache_top.v
#analyze -sv props_pkg.sv
analyze -sv cache_controller.sv
elaborate -bbox_m {lookup} -bbox_m {cache_4way} -top cache_ctrl
clock clk
reset -expression {!reset_n}
prove -bg -all
