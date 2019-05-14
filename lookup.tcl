clear -all
analyze -sv lookup.v
analyze -sv props_pkg.sv
analyze -sv lookup.sv
elaborate -bbox_a 20000 -top lookup
clock clk
reset -expression {!reset_n}
prove -bg -all

