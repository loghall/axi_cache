package propsPkg;
	property iff_instant(clk, reset_n, pre, expression1, expression2); 
		@(posedge clk) disable iff(!reset_n)
			pre |-> expression1 == expression2; 
	endproperty 

    property iff_1cycle(clk, reset_n, pre, expression1, expression2); 
		@(posedge clk) disable iff(!reset_n)
			pre |-> ##1 expression1 == expression2; 
	endproperty  

	property implies_instant(clk, reset_n, expression1, expression2); 
		@(posedge clk) disable iff(!reset_n)
			expression1 |-> expression2; 
	endproperty 

    property implies_1cycle(clk, reset_n, expression1, expression2); 
		@(posedge clk) disable iff(!reset_n)
			expression1 |-> ##1 expression2; 
	endproperty 

    property reset_cond(clk, reset_cond, expression1); 
		@(posedge clk) 
			reset_cond |-> ##1 expression1; 
	endproperty 
endpackage 
