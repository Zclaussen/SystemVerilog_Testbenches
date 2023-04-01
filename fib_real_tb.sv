`timescale 1ns/10ps

// FIB TRANSACTION ITEM
class fib_item #(INPUT_WIDTH);
   rand bit [INPUT_WIDTH-1:0] n;
endclass

// FIB RANDOM TEST GENERATOR
class generator #(int NUM_TESTS, int INPUT_WIDTH);
    mailbox driver_mailbox;
    
    event driver_done_event;
    event generator_done_event;

    task run();
        fib_item #(INPUT_WIDTH) item = new;
        for(int i=0; i < NUM_TESTS; i++) begin
            if(!item.randomize()) $display("Randomize Failed");
            $display("Time %0t [Generator]: Generating input h%h for test %0d.", $time, item.n, i);
            driver_mailbox.put(item);
            @(driver_done_event);
        end

        $display("Time %0t [Generator]: Generator done.", $time);
        -> generator_done_event;
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
    event driver_done_event;

    task run();
        $display("Time %0t [Driver]: Driver starting.", $time);
        forever begin
            fib_item #(INPUT_WIDTH) item;
            driver_mailbox.get(item);
            $display("Time %0t [Driver]: Driving h%h test.", $time, item.n);
            
            vif.n <= item.n;
            vif.go <= 1'b1;
            @(posedge vif.clk);
            vif.go <= 1'b0;
            @(posedge vif.clk iff (vif.done == 1'b0));      
            @(posedge vif.clk iff (vif.done == 1'b1));
            -> driver_done_event;                 
        end
    endtask
endclass

class fib_item2 #(INPUT_WIDTH, OUTPUT_WIDTH);
    rand bit [INPUT_WIDTH-1:0] n;
    bit [OUTPUT_WIDTH-1:0] result;
    bit overflow;
endclass

class monitor #(parameter int INPUT_WIDTH, parameter int OUTPUT_WIDTH);
    virtual fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) vif;
    mailbox scoreboard_mailbox;
    task run();
        $display("Time %0t [Monitor]: Monitor starting.", $time);
        forever begin
            fib_item2 #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item = new;
            @(posedge vif.clk iff (vif.done == 1'b0));      
            @(posedge vif.clk iff (vif.done == 1'b1));

            item.n = vif.n;
            item.result = vif.result;
            item.overflow = vif.overflow;

            $display("Time %0t [Monitor]: Monitor detected result=%0d for n=h%h.", $time, vif.result, vif.n);
            scoreboard_mailbox.put(item);
        end
    endtask
endclass

class scoreboard #(parameter int INPUT_WIDTH, parameter int OUTPUT_WIDTH);
    mailbox scoreboard_mailbox;
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

    task run();
        passed = 0;
        failed = 0;
        forever begin
            fib_item2 #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item;
            scoreboard_mailbox.get(item);
            reference = model(item.n);
            if(item.result == reference) begin
                $display("Time %0t [Scoreboard] Test passed for input = h%h", $time, item.n);
                passed++;
            end
            else begin
                $display("Time %0t [Scoreboard] Test failed: result = %0h instead of %0h for input = h%h.", $time, item.result, reference, item.n);
                failed ++;      
            end
        end
    endtask

    function void report_status();
        $display("Test status: %0d passed, %0d failed", passed, failed);
    endfunction
endclass

class env #(int NUM_TESTS, int INPUT_WIDTH, int OUTPUT_WIDTH);
    generator #(.NUM_TESTS(NUM_TESTS), .INPUT_WIDTH(INPUT_WIDTH)) gen1;
    driver    #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) drv1;
    monitor   #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) monitor1;
    scoreboard #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) scoreboard1;

    virtual fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) vif;

    mailbox scoreboard_mailbox;
    mailbox driver_mailbox;

    event driver_done_event;
    event generator_done_event;

    function new();
        gen1 = new;
        drv1 = new;
        monitor1 = new;
        scoreboard1 = new;
        scoreboard_mailbox = new;
        driver_mailbox = new;
    endfunction

    virtual task run();
        drv1.vif = vif;
        monitor1.vif = vif;

        gen1.driver_mailbox = driver_mailbox;
        drv1.driver_mailbox = driver_mailbox;

        gen1.driver_done_event = driver_done_event;
        drv1.driver_done_event = driver_done_event;

        monitor1.scoreboard_mailbox = scoreboard_mailbox;
        scoreboard1.scoreboard_mailbox = scoreboard_mailbox;

        fork
            gen1.run();
            drv1.run();
            monitor1.run();
            scoreboard1.run();
        join_any

        scoreboard1.report_status();
    endtask
endclass

module fib_real_tb;
    localparam NUM_TESTS = 1000;
    localparam INPUT_WIDTH = 6;
    localparam OUTPUT_WIDTH = 63;

    logic clk;

    env #(.NUM_TESTS(NUM_TESTS), .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) _env = new;

    fib_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) _if (.clk(clk));
    fib #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) DUT (.clk(clk), .rst(_if.rst), .go(_if.go), .done(_if.done), .n(_if.n), .result(_if.result), .overflow(_if.overflow));

    initial begin : generate_clock
        clk = 1'b0;
        while(1) #5 clk = ~clk;
    end

    initial begin
        $timeformat(-9, 0, " ns");

        _env.vif = _if;

        _if.rst <= 1'b1;
        _if.go <= 1'b0;
        for(int i=0; i<5; i++) @(posedge clk);
        @(negedge clk);
        _if.rst <= 1'b0;
        @(posedge clk);

        _env.run();
        disable generate_clock;
    end
    
    assert property (@(posedge clk) disable iff (_if.rst) _if.go && _if.done |=> !_if.done);
    assert property (@(posedge clk) disable iff (_if.rst) $fell(_if.done) |-> $past(_if.go,1));
endmodule