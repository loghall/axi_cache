`define REQ_SIGNAL_PROP(CLK, RESET_N, REQ, SIGNAL, PROPTYPE, DISABLE, ID) \
    ID``_stable_1: PROPTYPE`` property( \
        remain_stable(CLK``, DISABLE``, !$rose(REQ``) && REQ``, SIGNAL``) \
    );

`define RDY_SIGNAL_PROP(CLK, RESET_N, RDY, SIGNAL, PROPTYPE, DISABLE, ID) \
    ID``_stable_1: PROPTYPE`` property( \
        remain_stable(CLK``, DISABLE``, !$rose(RDY``) && RDY``, SIGNAL``) \
    ); 

`define REQ_PROP(CLK, RESET_N, REQ, SLV_RDY, PROPTYPE, DISABLE, ID) \
    ID``_fall_1: PROPTYPE`` property( \
        force_zero_1cycle(CLK``, DISABLE``, $fell(SLV_RDY``), REQ``) \
    ); \
    ID``_no_rise: PROPTYPE`` property( \
        force_value_1cycle(CLK``, DISABLE``, !SLV_RDY``, $rose(REQ``), 0) \
    ); 

`define RDY_PROP(CLK, RESET_N, RDY, REQ, PROPTYPE, DISABLE, ID) \
    ID``_stable_3: PROPTYPE`` property( \
        remain_stable_1cycle(CLK``, DISABLE``, RDY`` && !REQ``, RDY``) \
    ); \
    ID``_fall_2: PROPTYPE`` property( \
        force_zero_1cycle(CLK``, DISABLE``, $rose(REQ``), RDY``) \
    ); 

`define VALID_PROP(CLK, RESET_N, RDY, VALID, M_WEN, LEN, PROPTYPE, DISABLE, ID) \
    integer valid_ctr; \
    reg wen; \
    reg [7 : 0] req_len; \
    reg proc; \
    always@(posedge CLK``) begin \
        if(!RESET_N``) begin \
            valid_ctr <= 0; \
            req_len <= 0; \
            proc <= 0; \
        end \
        else begin \
            if(VALID``) begin \
                valid_ctr <= valid_ctr + 1; \
            end \
            else if($rose(RDY``)) begin \
                proc <= 0; \
            end \
            else if($fell(RDY``) && $past(!M_WEN``, 1)) begin \
                valid_ctr <= 0; \
                req_len <= LEN``;  \
                proc <= 1; \
            end \
        end \
    end \
    ID``_ctr: PROPTYPE`` property( \
            force_value_instant(CLK``, DISABLE``, $fell(proc), $past(valid_ctr), $past(req_len)) \
        ); \
    ID``_rdy_valid: PROPTYPE`` property( \
            force_zero_instant(CLK``, DISABLE``, RDY``, VALID``) \
        ); \
    ID``_wait_1cyc: PROPTYPE`` property( \
            force_zero_instant(CLK``, DISABLE``, $fell(RDY``), VALID``) \
        );

`define ADDR_ALIGN(CLK, RESET_N, ADDR, PROPTYPE, DISABLE, ID) \
    ID``_aligned: PROPTYPE`` property( \
        force_value_instant(CLK``, DISABLE``, 1, ADDR`` % 4, 0) \
    ); 

`define OMI_MASTER(CLK, RESET_N, REQ, RDY, ADDR, WEN, BEN, LEN, DATA, PROPTYPE, DISABLE, ID) \
    `REQ_PROP(CLK``, RESET_N``, REQ``, RDY``, PROPTYPE, 0, PROPTYPE``_ID) \
    `REQ_SIGNAL_PROP(CLK``, RESET_N``, REQ``, ADDR``, PROPTYPE``, DISABLE``, PROPTYPE``_ID``_addr) \
    `REQ_SIGNAL_PROP(CLK``, RESET_N``, REQ``, WEN``, PROPTYPE``, DISABLE``, PROPTYPE``_ID``_wen) \
    `REQ_SIGNAL_PROP(CLK``, RESET_N``, REQ`` && WEN``, BEN``, PROPTYPE``, PROPTYPE``_DISABLE``, ID``_ben) \
    `REQ_SIGNAL_PROP(CLK``, RESET_N``, REQ``, DATA``, PROPTYPE``, DISABLE``, PROPTYPE``_ID``_data) \
    `REQ_SIGNAL_PROP(CLK``, RESET_N``, REQ``, LEN``, PROPTYPE``, DISABLE``, PROPTYPE``_ID``_len) \
    `ADDR_ALIGN(CLK``, RESET_N``, I_ADDR``, PROPTYPE``, DISABLE``, PROPTYPE``_ID``_i_addr)


package intfPkg;
    /* Template 
        X: Y property(
            remain_stable_1cycle(clk, disable_cond, condition, signal)
        ); 
    */ 
    property remain_stable_1cycle(clk, disable_cond, condition, signal);
        @(posedge clk) disable iff(disable_cond) 
            condition |-> ##1 $stable(signal);
    endproperty 

     /* Template 
        X: Y property(
            force_zero_1cycle(clk, disable_cond, condition, signal)
        ); 
    */ 
    property force_zero_1cycle(clk, disable_cond, condition, signal);
        @(posedge clk) disable iff(disable_cond) 
            condition |-> ##1 signal == 0;
    endproperty

    /* Template 
        X: Y property(
            force_zero_instant(clk, disable_cond, condition, signal)
        ); 
    */ 
    property force_zero_instant(clk, disable_cond, condition, signal);
        @(posedge clk) disable iff(disable_cond) 
            condition |-> signal == 0;
    endproperty

    /* Template 
        X: Y property(
            force_value_instant(clk, disable_cond, condition, signal, value)
        ); 
    */
    property force_value_instant(clk, disable_cond, condition, signal, value);
        @(posedge clk) disable iff(disable_cond) 
            condition |-> signal == value;
    endproperty

    property force_value_1cycle(clk, disable_cond, condition, signal, value);
        @(posedge clk) disable iff(disable_cond) 
            condition |-> ##1 signal == value;
    endproperty

    /* Template 
        X: Y property(
            shall_rise_1cycle(clk, disable_cond, condition, signal)
        ); 
    */
    property shall_rise_1cycle(clk, disable_cond, condition, signal);
        @(posedge clk) disable iff(disable_cond) 
            condition |-> ##1 $rose(signal);
    endproperty

    property remain_stable(clk, disable_cond, condition, signal);
        @(posedge clk) disable iff(disable_cond) 
            condition |-> $stable(signal);
    endproperty 

endpackage 
