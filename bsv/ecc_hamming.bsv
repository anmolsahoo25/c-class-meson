/*
Copyright (c) 2018, IIT Madras All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted
provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice, this list of conditions
  and the following disclaimer.
* Redistributions in binary form must reproduce the above copyright notice, this list of
  conditions and the following disclaimer in the documentation and/or other materials provided
 with the distribution.
* Neither the name of IIT Madras  nor the names of its contributors may be used to endorse or
  promote products derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS
OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY
AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER
IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------

Author: Usha Kumari Krishnamurthy
Email id: usha.krishnamurthy@gmail.com
Details:

--------------------------------------------------------------------------------------------------
*/

package ecc_hamming; // Hamming codec for Error Detection and Correction

import Vector::*;
//import Randomizable ::*;
import LFSR::*;


  function Bit#(TAdd#(2,TLog#(databits))) ecc_hamming_encode (Bit#(databits) data_word_in)
  		provisos(Add#(databits, TAdd#(1,TLog#(databits)), encodedbits)
  		);
		let v_paritybits = valueOf(TAdd#(1,TLog#(databits)));

		Bit#(TAdd#(2,databits)) data_word = {2'b00,data_word_in};
		let v_encodedbits = valueOf(encodedbits);
		Bit#(TAdd#(2,encodedbits)) encoded_word = '0;
		Bit#(TAdd#(1,TLog#(databits))) parity_word_index = 1;
		Bit#(TAdd#(1,TLog#(databits))) parity_word = '0;
		Bit#(TLog#(databits)) parity_word_lsb = '0;
		Bit#(TAdd#(1,TLog#(databits))) j = '0;
		Bit#(TAdd#(1,TLog#(TLog#(databits)))) k = '0;
		Bit#(1) extra_parity_ded = 1'b0;

		/* Fill a temp register with word to be encoded and with parity word(initially zero)at 
			bit positions which are powers of 2 like 1,2,4,8 etc.*/

		//$display("Encodedbits is = %d", v_encodedbits);
		for(Integer i=0; i <= v_encodedbits ; i=i+1) begin
			if (fromInteger(i+1) == parity_word_index) begin
				encoded_word [i+1] = parity_word[k];
				parity_word_index = parity_word_index << 1;
				k = k + 1;  
			end
			else begin
				encoded_word [i+1] = data_word [j];
				j = j +1;
			end
		end
		
		/*Compute the encoded parity as follows:
			* for bit position 1 of parity bits XOR all bits in the temp register with 
				the position's binary index having a 1 in bit 1
			  viz. Parity bit 1 covers all the bits positions whose binary representation 
				includes a 1 in the least significant position (1, 3, 5, 7, 9, 11, etc).
			* Parity bit 2 covers all the bits positions whose binary representation includes 
				a 1 in the second position from the least significant bit (2, 3, 6, 7, 10, 11, etc).	
		*/
		for (Integer m=0; fromInteger(m) <= k; m=m+1) begin
			for (Integer n=0; n <= v_encodedbits; n=n+1) begin
				Bit#(TAdd#(1,TLog#(encodedbits))) index_into_enc= fromInteger(n+1);
				if (index_into_enc[m] == 1'b1) begin
					parity_word[m] = parity_word[m] ^ encoded_word[index_into_enc];
				end
			end 
		end

		/* Add an extra parity bit over the above to enable double error detection */
		extra_parity_ded = ((^data_word_in)^(^parity_word));

		return {extra_parity_ded,parity_word};
  endfunction

  function  Tuple3#(Bit#(databits),Bit#(TAdd#(1,TLog#(databits))), Bool) ecc_hamming_decode_correct 
            (Bit#(databits) data_word_in, Bit#(TAdd#(2,TLog#(databits))) 
            parity_word_in, Bit#(1) det_only)
            provisos(Add#(databits, TAdd#(1,TLog#(databits)), encodedbits));

		let data_word = {2'b00,data_word_in};

		let v_encodedbits = valueOf(encodedbits);
		let v_databits = valueOf(databits);
		let v_paritybits = valueOf(TAdd#(1,TLog#(databits)));
		Bit#(TAdd#(2,encodedbits)) encoded_word = '0;
		Bit#(TAdd#(1,TLog#(databits))) parity_word_index = 1;
		Bit#(TAdd#(1,TLog#(databits))) decoded_parity_word = '0;
		Bit#(TAdd#(1,TLog#(databits))) decoded_parity_word_lsb = '0;
		Bit#(TAdd#(1,TLog#(databits))) decoded_parity_word_correct = '0;
		Bit#(TAdd#(1,TLog#(databits))) j = '0;
		Bit#(TAdd#(1,TLog#(TLog#(databits)))) k = '0;
		Bit#(TAdd#(2,databits)) correct_data_word = '0;
		Bit#(1) extra_decoded_parity_ded = 1'b0; 
		Bool ecc_error_detect_only_trap = False;
		Bit#(TAdd#(2,TLog#(databits)))parity_word = {1'b0,parity_word_in[v_paritybits-1:0]};


		/* Do the same as encoder to recover the encoded parity word which when no error should all be zeroes */
		for(Integer i=0; i <= v_encodedbits ; i=i+1) begin
			if (fromInteger(i+1) == parity_word_index) begin
				encoded_word [i+1] = parity_word[k];
				parity_word_index = parity_word_index << 1;
				k = k + 1;  
			end
			else begin
				encoded_word [i+1] = data_word [j];
				j = j +1;
			end
		end

                for (Integer m=0; fromInteger(m) <= k; m=m+1) begin
                        for (Integer n=0; n <= v_encodedbits; n=n+1) begin
                                Bit#(TAdd#(1,TLog#(encodedbits))) index_into_enc= fromInteger(n+1);
                                if (index_into_enc[m] == 1'b1) begin
                                        decoded_parity_word[m] = decoded_parity_word[m] ^ encoded_word[index_into_enc];
                                end
                        end
                end
		decoded_parity_word_lsb = decoded_parity_word[v_paritybits-1:0];
		
		/* Compute the extra parity bit over the above to detect double error - 
			when det_only is set single errors are also not corrected but only detected */
		extra_decoded_parity_ded = ((^data_word_in)^(^parity_word_in)) & ~det_only;

		/* When decoded parity word is not zero it is the index of the bit position which has been errored so toggle it
			This is the single error case when not detect-only; the extra parity bit is for double error detection  */
		if (({extra_decoded_parity_ded,decoded_parity_word_lsb} != 0) && (extra_decoded_parity_ded == 1'b1)) begin
			parity_word_index = 1;
			j = '0;
			for(Integer i=0; i <= v_encodedbits; i=i+1) begin
				if (fromInteger(i+1) == decoded_parity_word) begin
					encoded_word[i+1] = ~encoded_word[i+1];
				end
				if (fromInteger(i+1) == parity_word_index) begin
					parity_word_index = parity_word_index << 1;
				end
				else begin
					correct_data_word [j] = encoded_word [i+1];
					j = j +1;
				end
			end
		end
		
		/* in case of double error detection take a trap */
		else if (({extra_decoded_parity_ded,decoded_parity_word_lsb} != 0) && (extra_decoded_parity_ded == 1'b0)) begin
			ecc_error_detect_only_trap = True;
		end
		else begin
			correct_data_word = data_word;
		end
		return tuple3 (correct_data_word[v_databits-1:0], decoded_parity_word, ecc_error_detect_only_trap);
  endfunction

/* --------- Synthesizable instances of the function ------------------------------//
  
  (*noinline*)
  function Bit#(TAdd#(2,TLog#(`DATABITS))) ecc_encode (Bit#(`DATABITS) data_word_in) =
    ecc_hamming_encode(data_word_in);
  
  (*noinline*)
  function Tuple3#(Bit#(`DATABITS ),Bit#(TAdd#(1,TLog#(`DATABITS ))), Bool) ecc_decode 
            (Bit#(`DATABITS) data_word_in, Bit#(TAdd#(2,TLog#(`DATABITS))) 
            parity_word_in, Bit#(1) det_only) = 
    ecc_hamming_decode_correct(data_word_in, parity_word_in, det_only);


module mkTbECCHammingVerfy (Empty);

    //Randomize#(Bit#(`DATABITS)) rand_data <- mkGenericRandomizer;
    Reg#(Bit#(TLog#((`DATABITS)))) count <- mkRegA(0);
    Reg#(Bool) rg_init <- mkRegA(True);
    LFSR#(Bit#(32)) lfsr1 <- mkLFSR_32 ;
    LFSR#(Bit#(32)) lfsr2 <- mkLFSR_32 ;

    rule rl_init_randomizers(rg_init);
	    rg_init <= False;
	    //rand_data.cntrl.init();	
	    lfsr1.seed('h99);
	    lfsr2.seed('h11);	
    endrule

    rule rl_encode_and_decode(!rg_init);
		  //let lv_rand_data <- rand_data.next;	
      //Bit#(`DATABITS) data_word = lv_rand_data;
      //Bit#(`DATABITS) data_word = 64'h0C0C0D0D0E0EF0F0;
      Bit#(`DATABITS) enc_data_word = '0;
      Bit#(TAdd#(2,TLog#(`DATABITS))) parity_word = '0;
      Bit#(`DATABITS) corrected_data = '0;
      Bit#(TAdd#(1,TLog#(`DATABITS))) decoded_parity = '0;
      Bool detect_trap = False;
		  count <= count + 1;
     	Bit#(`DATABITS) data_word = truncate({lfsr1.value,lfsr2.value});
      Bit#(`DATABITS) data_word_err = data_word;
			$display("Input Data Word ifor Encoding = %h", data_word );
      parity_word = ecc_encode (data_word);
      $display("Hamming encoded_word = %h, %b", enc_data_word, parity_word);
      //enc_data_word[33] = ~enc_data_word[33];
      data_word_err[count] = ~data_word_err[count];
			$display("Corrupted Data Word with injected Error = %h", data_word_err);
      {corrected_data,decoded_parity, detect_trap} = ecc_decode (data_word_err, parity_word, 1'b0);
      $display("Hamming decoded_word = %h, %b %b\n", corrected_data, decoded_parity, detect_trap);
			if (corrected_data != data_word)
				$display ("*************** Decoded Word Mismatch!!!! Not corrected properly");
                        enc_data_word[count] = ~enc_data_word[count];
			lfsr1.next;
			lfsr2.next;
		if (count == fromInteger(`DATABITS-1)) 
                	$finish(0);
    endrule

endmodule
*/
endpackage: ecc_hamming
