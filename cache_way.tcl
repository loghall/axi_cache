clear -all
analyze -v2k cache_way.v
analyze -v2k ram.v
analyze -sv props_pkg.sv
analyze -sv cache_way.sv
elaborate -bbox_a 20000 -top cache_way
clock clk
reset -expression {!reset_n}
prove -bg -all

