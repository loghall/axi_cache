package propsPkg;
	property iff_instant(clk, disable_cond, pre, expression1, expression2); 
		@(posedge clk) disable iff(disable_cond)
			pre |-> expression1 == expression2; 
	endproperty 

    property iff_1cycle(clk, disable_cond, pre, expression1, expression2); 
		@(posedge clk) disable iff(disable_cond)
			pre |-> ##1 expression1 == expression2; 
	endproperty  

	property implies_instant(clk, disable_cond, expression1, expression2); 
		@(posedge clk) disable iff(disable_cond)
			expression1 |-> expression2; 
	endproperty 

    property implies_1cycle(clk, disable_cond, expression1, expression2); 
		@(posedge clk) disable iff(disable_cond)
			expression1 |-> ##1 expression2; 
	endproperty 

endpackage 
