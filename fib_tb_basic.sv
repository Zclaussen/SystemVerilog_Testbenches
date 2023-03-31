// Module: fib_tb_basic
// Description: A very bad testbench for the fib module. This testbench shows
// no errors despite there being many in the provided fib_bad module. Replace
// this testbench with your own.

module fib_tb_basic;

   localparam int INPUT_WIDTH = 6;
   localparam int OUTPUT_WIDTH = 32;
   
   logic 	  clk, rst, go, done, overflow;  
   logic [INPUT_WIDTH-1:0] n;
   logic [OUTPUT_WIDTH-1:0] result;
   longint 		    correct_result;
   logic 		    correct_overflow;   
   int 			    passed, failed;

   fib #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) DUT (.*);

   // Reference model for the correct result.
   function longint result_model(int n);
      longint 		    x, y, i, temp;
      x = 0;
      y = 1; 
      i = 3;
      if (n < 2)
	return 0;      
      
      while (i <= n) begin
	 temp = x+y;
	 x = y;
	 y = temp;
	 i ++;	 
      end
      return y;      
   endfunction

   // Reference model for the correct overflow.
   function logic overflow_model(longint result);
      logic [OUTPUT_WIDTH-1:0] result_truncated;
      result_truncated = result;
      
      // If the truncated version is the same as the full version, there
      // was no overflow.
      return result_truncated != result;      
   endfunction
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      $timeformat(-9, 0, " ns");

      passed = 0;
      failed = 0;      

      // Perform some number of tests.
      for (int i=0; i < 10; i++) begin
	 // Reset the DUT
	 rst = 1'b1;
	 go = 1'b0;
	 n = '0;
	 for (int i=0; i < 5; i++) @(posedge clk);	 
	 rst = 1'b0;

	 // Perform the test.
	 n = i;
	 go = 1'b1;
	 @(posedge clk);
	 go = 1'b0;	 
	 @(posedge done);

	 // Check the output.
	 correct_result = result_model(n);
	 correct_overflow = overflow_model(correct_result);
	 if (!correct_overflow) begin
	    if (result == correct_result) begin
	       //$display("Result test passed (time %0t)", $time);
	       passed ++;
	    end
	    else begin
	       $display("Result test failed (time %0t): result = %0d instead of %0d.", $time, result, correct_result);
	       failed ++;	    
	    end
	 end

	 if (overflow == correct_overflow) begin
	    //$display("Overflow test passed (time %0t)", $time);
	    passed ++;
	 end
	 else begin
	    $display("Overflow test failed (time %0t): overflow = %0b instead of %0b.", $time, overflow, correct_overflow);
	    failed ++;	    
	 end

	 @(posedge clk);
      end

      $display("Tests completed: %0d passed, %0d failed", passed, failed);      
      disable generate_clock;      
   end
endmodule