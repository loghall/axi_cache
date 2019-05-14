clear -all
analyze -v2k ram.v
analyze -sv props_pkg.sv
analyze -sv ram.sv
elaborate -bbox_a 20000 -top ram
clock clk
reset -expression {!reset_n}
#prove -bg -all
