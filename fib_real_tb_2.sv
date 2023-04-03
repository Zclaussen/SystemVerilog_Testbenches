`timescale 1ns/10ps

// FIB TRANSACTION ITEM
class fib_item3 #(INPUT_WIDTH, OUTPUT_WIDTH);
    rand bit [INPUT_WIDTH-1:0] n;
    rand bit go;
    bit [OUTPUT_WIDTH-1:0] result;
    bit overflow;

    constraint c_go_dist {go dist{0 :/ 90, 1:/ 10};}
endclass

// FIB RANDOM TEST GENERATOR
class generator #(int NUM_TESTS, int INPUT_WIDTH, int OUTPUT_WIDTH);
    mailbox driver_mailbox;
    
    event driver_done_event;
    // event generator_done_event;

    task run();
        fib_item3 #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item;
        forever begin
            item = new;
            if(!item.randomize()) $display("Randomize Failed");
            driver_mailbox.put(item);
            @(driver_done_event);
        end
    endtask
endclass

interface fib_if #(parameter int INPUT_WIDTH, parameter int OUTPUT_WIDTH) (input logic clk);
    logic rst, go, done;
    logic [INPUT_WIDTH-1:0] n;
    logic [OUTPUT_WIDTH-1:0] result;
    logic overflow;
endinterface

class driver #(INPUT_WIDTH, OUTPUT_WIDTH);
    virtual fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) vif;

    mailbox driver_mailbox;
    mailbox scoreboard_data_mailbox;
    event driver_done_event;

    task run();
        logic is_first_test = 1'b1;
        logic is_active = 1'b0;
        $display("Time %0t [Driver]: Driver starting.", $time);

        forever begin
            fib_item3 #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item;

            //driver_mailbox.get(item);
            //$display("Time %0t [Driver]: Driving h%h test.", $time, item.n);
            
            while(vif.rst) begin
                @(posedge vif.clk);   
                is_first_test = 1'b1;
                is_active = 1'b0;  
            end

            driver_mailbox.get(item);

            vif.n <= item.n;
            vif.go <= item.go;

            @(posedge vif.clk);

            if(vif.done || is_first_test) is_active = 1'b0;

            if (!is_active && vif.go) begin            
                $display("Time %0t [Driver]: Sending start of test for n=h%h.", $time, item.n);
                scoreboard_data_mailbox.put(item);
                is_active = 1'b1;       
                is_first_test = 1'b0;
            end

            -> driver_done_event;                 
        end
    endtask
endclass

class monitor #(parameter int INPUT_WIDTH, parameter int OUTPUT_WIDTH);
    virtual fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) vif;
    mailbox scoreboard_result_mailbox;
    task run();
        $display("Time %0t [Monitor]: Monitor starting.", $time);
        forever begin
            fib_item3 #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item = new;
            @(posedge vif.clk iff (vif.done == 1'b0));      
            @(posedge vif.clk iff (vif.done == 1'b1));

            //item.n = vif.n;
            item.result = vif.result;
            item.overflow = vif.overflow;

            $display("Time %0t [Monitor]: Monitor detected result=%0d", $time, vif.result);
            scoreboard_result_mailbox.put(item);
        end
    endtask
endclass

class scoreboard #(parameter int INPUT_WIDTH, parameter int OUTPUT_WIDTH);
    mailbox scoreboard_result_mailbox;
    mailbox scoreboard_data_mailbox;
    int passed, failed, reference;

    function longint model(int n);
        longint 		    x, y, i, temp;
        x = 0;
        y = 1; 
        i = 3;
        if (n < 2) return 0;      
      
        while (i <= n) begin
	        temp = x+y;
	        x = y;
	        y = temp;
	        i ++;	 
        end
        return y;      
    endfunction

    /*function logic overflow_model(longint result);
      logic [OUTPUT_WIDTH-1:0] result_truncated;
      result_truncated = result;
      
      // If the truncated version is the same as the full version, there
      // was no overflow.
      return result_truncated != result;      
    endfunction */

    task run();
        passed = 0;
        failed = 0;
        for(int i = 0; i < 1000; i++) begin
            fib_item3 #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) in_item;
            fib_item3 #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) out_item;

            scoreboard_data_mailbox.get(in_item);
            $display("Time %0t [Scoreboard]: Received start of test for n=h%h.", $time, in_item.n);

            scoreboard_result_mailbox.get(out_item);
            $display("Time %0t [Scoreboard]: Received result=%0d for n=h%h.", $time, out_item.result, in_item.n);

            reference = model(in_item.n);
            if(out_item.result == reference) begin
                $display("Time %0t [Scoreboard] Test passed for input = h%h", $time, in_item.n);
                passed++;
            end
            else begin
                $display("Time %0t [Scoreboard] Test failed: result = %0d instead of %0d for input = h%h", $time, out_item.result, reference, in_item.n);
                failed ++;      
            end
        end
    endtask

    function void report_status();
        $display("Test status: %0d passed, %0d failed", passed, failed);
    endfunction
endclass

class env #(int NUM_TESTS, int INPUT_WIDTH, int OUTPUT_WIDTH);
    generator #(.NUM_TESTS(NUM_TESTS), .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) gen1;
    driver    #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) drv1;
    monitor   #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) monitor1;
    scoreboard #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) scoreboard1;

    virtual fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) vif;

    mailbox scoreboard_data_mailbox;
    mailbox scoreboard_result_mailbox;
    mailbox driver_mailbox;

    event   driver_done_event;

    function new();
        gen1 = new;
        drv1 = new;
        monitor1 = new;
        scoreboard1 = new;
        scoreboard_data_mailbox = new;
        scoreboard_result_mailbox = new;
        driver_mailbox = new;
    endfunction

    virtual task run();
        drv1.vif = vif;
        monitor1.vif = vif;

        gen1.driver_mailbox = driver_mailbox;
        drv1.driver_mailbox = driver_mailbox;

        drv1.scoreboard_data_mailbox = scoreboard_data_mailbox;
        scoreboard1.scoreboard_data_mailbox = scoreboard_data_mailbox;

        monitor1.scoreboard_result_mailbox = scoreboard_result_mailbox;
        scoreboard1.scoreboard_result_mailbox = scoreboard_result_mailbox;

        gen1.driver_done_event = driver_done_event;
        drv1.driver_done_event = driver_done_event;

        fork
            gen1.run();
            drv1.run();
            monitor1.run();
            scoreboard1.run();
        join_any

        scoreboard1.report_status();
    endtask
endclass

module fib_real_tb_2;
    localparam NUM_TESTS = 1000;
    localparam INPUT_WIDTH = 6;
    localparam OUTPUT_WIDTH = 64;

    logic clk;

    env #(.NUM_TESTS(NUM_TESTS), .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) _env = new;

    fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) _if (.clk(clk));
    fib #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) DUT (.clk(clk), .rst(_if.rst), .go(_if.go), .done(_if.done), .n(_if.n), .result(_if.result), .overflow(_if.overflow));

    covergroup cg @(posedge clk);
        //Overflow should be asserted at least 10 times
        cp_overflow: coverpoint _if.overflow {bins asserted={1'b1}; option.at_least = 10;}

        //2**INPUT_WIDTH values of n tested at least once
        cp_n: coverpoint _if.n {bins n_bins[] = {[0:2**INPUT_WIDTH-1]};}

        //Go should be asserted at least 100 times when the circuit is actively computing a value (i.e., go has been asserted previously and done = 0)
        cp_go_active: coverpoint {_if.go && !_if.done} {bins asserted={1'b1}; option.at_least = 100;}

        //While the circuit is actively computing a value (i.e. go has been asserted previously and done=0), the data input n should change at least 100 times
        //cp_n_active: coverpoint _if.n {bins n_bins[] = {[0:2**INPUT_WIDTH-1]}; option.at_least = 100; option.condition = {_if.done == 0};}

        
    endgroup

    initial begin : generate_clock
        clk = 1'b0;
        while(1) #5 clk = ~clk;
    end

    cg cg_inst;

    initial begin
        cg_inst = new();
        $timeformat(-9, 0, " ns");

        _env.vif = _if;

        _if.rst <= 1'b1;
        _if.go <= 1'b0;
        for(int i=0; i<5; i++) @(posedge clk);
        @(negedge clk);
        _if.rst <= 1'b0;
        @(posedge clk);

        _env.run();

        $display("Coverage = %0.2f %%", cg_inst.get_inst_coverage());
        disable generate_clock;
    end
    
    assert property (@(posedge clk) disable iff (_if.rst) _if.go && _if.done |=> !_if.done);
    assert property (@(posedge clk) disable iff (_if.rst) $fell(_if.done) |-> $past(_if.go,1));
endmodule