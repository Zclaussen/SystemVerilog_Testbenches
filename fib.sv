// Module: fib_bad
// Description: This module incorrect implements a Fibonacci calculator. It is
// up to you to expand on the provided testbench to discover and document all
// the errors in a report.
//

/*=============================================================================
 Parameter Descriptions
 INPUT_WIDTH : A positive integer representing the bit width of the n input 
 OUTPUT_WIDTH : A positive integer representing the bit width of the result 
 ===============================================================================
 ===============================================================================
 Interface Description (all control inputs are active high)
 --- INPUTS ---
 clk   : Clock
 rst   : Asynchronous reset
 go    : Assert to start the module for the current n input. Has no
         impact when the module is currently active (!done except after reset).
 n     : The nth Fibonacci number to calculate, starting at 1. A value of n=0
         produces a result = 0.
 
 --- OUTPUTS ---
 result : The calculated result. Is valid when done is asserted.
 done : Asserted when the result output is valid. Remains asserted indefinitely
        until go is asserted again, and then is cleared on the next cycle.
 ============================================================================ */

module fib_bad
  #(
    parameter int INPUT_WIDTH,
    parameter int OUTPUT_WIDTH
    )
   (
    input logic 		    clk,
    input logic 		    rst,
    input logic 		    go,
    input logic [INPUT_WIDTH-1:0]   n, 
    output logic [OUTPUT_WIDTH-1:0] result,
    output logic 		    overflow,
    output logic 		    done
   );

   typedef enum {START, COND, COMPUTE, OVERFLOW, DONE, RESTART} state_t;
   state_t state_r;   
   
   logic [$bits(n)-1:0] i_r;
   logic [$bits(result)-1:0] x_r;
   logic [$bits(result)-1:0] y_r;
   logic [$bits(result):0] full_add_r;   

   logic [$bits(result)-1:0] result_r;   
   logic 		     done_r, overflow_r;

   assign done = done_r;
   assign result = result_r;
   assign overflow = overflow_r;
         
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
	 state_r <= START;
	 result_r <= '0;
	 done_r <= 1'b0;
	 i_r <= '0;
	 x_r <= '0;
	 y_r <= '0;
	 overflow_r <= 1'b0;
	 full_add_r <= '0;	 
      end
      else begin
       
	 case (state_r)
	   START : begin
	      i_r <= 3;
	      x_r <= '0;
	      y_r <= 1;	   	      
	      if (go == 1'b1) state_r <= COND;	      
	   end
	   
	   COND : begin
	      done_r <= 1'b0;
	      
	      if (i_r <= n)
		state_r <= COMPUTE;
	      else
		state_r <= DONE;	   
	   end
	   
	   COMPUTE : begin	      
	      x_r <= y_r;
	      full_add_r <= x_r + y_r;
	      i_r <= i_r + 1'b1;
	      state_r <= OVERFLOW;	      
	   end

	   OVERFLOW : begin
	      if (full_add_r[OUTPUT_WIDTH]) overflow_r <= 1'b1;
	      y_r <= full_add_r;	      
	      state_r <= COND;						
	   end

	   DONE : begin
	      if (n < 2)
		result_r <= x_r;
	      else
		result_r <= y_r;
	      
	      done_r <= 1'b1;	      
	      state_r <= RESTART;	      	     
	   end

	   RESTART : begin
	      if (go == 1'b1) state_r <= COND; 
	   end
	 endcase

	 if (go == 1'b1)
	   state_r <= COND;	      	
      end
   end   
endmodule



// TODO: Create a fully functional fib entity. It is up to you to create a
// testbench that gives you confidence in its correctness. I will be using a
// very thorough testbench, so if your testbench is lacking, I will likely
// will find errors you did not see in your tests.

module fib_good
  #(
    parameter int INPUT_WIDTH,
    parameter int OUTPUT_WIDTH
    )
   (
    input logic 		    clk,
    input logic 		    rst,
    input logic 		    go,
    input logic [INPUT_WIDTH-1:0]   n, 
    output logic [OUTPUT_WIDTH-1:0] result,
    output logic 		    overflow,
    output logic 		    done
   );

   
endmodule


// Top-level module for synthesis and simulation, change the instantiated
// module to test different modules.

module fib
  #(
    parameter int INPUT_WIDTH=6,
    parameter int OUTPUT_WIDTH=32
    )
   (
    input logic 		    clk,
    input logic 		    rst,
    input logic 		    go,
    input logic [INPUT_WIDTH-1:0]   n, 
    output logic [OUTPUT_WIDTH-1:0] result,
    output logic 		    overflow,
    output logic 		    done
   );

   fib_bad #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) top (.*);
   //fib_good #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) top (.*);
   
endmodule