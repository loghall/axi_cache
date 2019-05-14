clear -all
analyze -sv cache_4way.v
analyze -v2k cache_way.v
analyze -v2k ram.v
analyze -sv props_pkg.sv
analyze -sv cache_4way.sv
elaborate -bbox_a 20000 -top cache_4way
clock clk
reset -expression {!reset_n}
#prove -bg -all


