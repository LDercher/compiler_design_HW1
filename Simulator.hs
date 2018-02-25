module Simulator where

import Data.Bits
import Data.Array.IArray
import Data.Int
import Data.Word
import Machine
import X86

import Debug.Trace

--------------------------------------------------------------------------------
-- Simulator                                                                  --
--------------------------------------------------------------------------------

{-

Your task in this homework is to write a simulator for the core x86 instruction
set. At the high level, this will take the form of a function `step` which,
given a `Machine` value representing the current state of the machine, produces
a new `Machine` value representing the next state of the machine.

To do so, you will have to:

 1. Fetch the next instruction to execute (that is, the instruction pointed to
    by RIP), and increment the instruction pointer.

 2. Retrieve operands from memory, if necessary.

 3. Perform the instruction.

 4. Update memory and the flags with the results of the instruction, as
    appropriate.

You may find it helpful to structure your solution accordingly, defining helper
functions for moving Int64 values to and from memory, getting from or updating
operands, and performing individual operations.

You do not need to perform any error checking---you may assume that instructions
have the right number of operands, memory addresses are in range, and so forth.
You do not need to represent the more arcane restrictions of x86---such as the
limitation that at most one operand to may be indirect, or the limitations on
indirection in the `imul` instruction.

You may assume that the shift instructions (`shl`, `shr`, `sar`) never set the
overflow flag.  (In real x86, 1-bit shifts may set the overflow flag.)

Haskell provides functions `shiftL` and `shiftR` that do left and right
arithmetic shifts.  To get a right logical shift, it suffices to convert a
signed `Int64` value to it unsigned `Word64` equivalent, shift that value, and
then convert back to `Int64`.  The generic `fromIntegral` function can do both
conversions, so long as the result of the conversion is specified (in the
types).

getMemory :: Int64 -> Machine -> SByte
getMemory addr m = mem m ! addr

setMemory :: Int64 -> SByte -> Machine -> Machine
setMemory addr val m = m{ mem = mem m // [(addr, val)] }

getRegister :: Register -> Machine -> Int64
getRegister reg m = regs m ! reg

setRegister :: Register -> Int64 -> Machine -> Machine
setRegister reg val m = m{ regs = regs m // [(reg, val)] }

getOF, getZF, getSF :: Machine -> Bool
getOF m = overflow
    where (overflow, _, _) = flags m
getZF m = zero
    where (_, zero, _) = flags m
getSF m = sign
    where (_, _, sign) = flags m

setOF, setZF, setSF :: Bool -> Machine -> Machine
setOF b m = m{ flags = (b, zero, sign) }
    where (overflow, zero, sign) = flags m
setZF b m = m{ flags = (overflow, b, sign) }
    where (overflow, zero, sign) = flags m
setSF b m = m{ flags = (overflow, zero, b) }
    where (overflow, zero, sign) = flags m

clearFlags :: Machine -> Machine
clearFlags m = m{ flags = (False, False, False) }

getRIP :: Machine -> Int64
getRIP = rip

setRIP :: Int64 -> Machine -> Machine
setRIP val m = m{ rip = val }


-}


step :: Machine -> Machine
step M = M { mem = listArray (memoryFloor, memoryCeiling) (pad n0 ++ fs ++ pad n1 ++ ss ++ pad (n2+1) ) --get and set vals from mem
           , regs = listArray (RAX, R15) (repeat 0) -- get and set vals from regs
           , flags = (False, False, False) --set flags after op
           , rip = setRIP --do op at rip set rip to next inst
           }
            where n0 = lowerAddr - memoryFloor
                  fs = if textAddr < dataAddr then textSegment else dataSegment
                  n1 = (fromIntegral (upperAddress - lowerAddr)) - (fromIntegral (length fs))
                  ss = if textAddr < dataAddr then dataSegment else textSegment
                  n2 = (fromIntegral(memoryCeiling - upperAddress)) - (fromIntegral (length ss))
                  lowerAddr = min textAddr dataAddr
                  upperAddress = max textAddr dataAddr
                  pad n = take (fromIntegral n) (repeat (Byte 0))
{-

The `run` function loops your `step` function until the IP equals the pre-defined
halt value, returning the final machine state.

-}

run :: Machine -> Machine
run initial = until ((haltAddr ==) . getRIP) step initial

eval :: Machine -> Int64
eval initial = getRegister RAX (run initial)
