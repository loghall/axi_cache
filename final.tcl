clear -all
analyze -v2k cache.v
analyze -sv cache.sv
elaborate -top cache
clock clk
reset -expression {faux_rst}
prove -bg -all
