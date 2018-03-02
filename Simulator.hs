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

-}


step :: Machine -> Machine
step m= case (getMemory (getRIP m) m) of Inst (Movq, [src,dst]) -> storeOperand dst (readOperand src m) m
                                         Inst (Addq, [src,dst]) -> storeOperand res (readOperand dst m) m --update machine dst res off zf cf
                                                                                        where res = readOperand src m + readOperand dst m
                                         Inst (Subq, [src,dst]) -> storeOperand res (readOperand dst) m
                                                                                        where res = readOperand dst m - readOperand src m
                                         Inst (Imulq, [src,dst]) -> storeOperand res (readOperand dst) m
                                                                                        where res = readOperand src m * readOperand dst m
                                         Inst (Notq, [dst]) -> storeOperand (readOperand dst m)(not (readOperand dst m)) m
                                         Inst (Andq, [src,dst]) -> storeOperand res (readOperand dst) m
                                                                                        where res = readOperand src m && readOperand dst m
                                         Inst (Orq, [src,dst]) -> error "i"
                                         Inst (Xorq, [src,dst]) -> error "i"
                                         Inst (Shlq, [imm, dst]) -> error "i"
                                         Inst (Shrq, [imm,dst]) -> error "i"
                                         Inst (Sarq, [imm,dst]) -> error "i"
                                         Inst (Leaq, [src,dst]) -> error "i"
                                         Inst (Set condition, [dst]) -> storeOperand dst res m
                                                                                where res = (readOperand dst m) .&. 0xFF + if checkCond condition m then 1 else 0  --then storeOperand dst m else setRIP((getRIP m) + 4 ) m --get address out of dst
                                         Inst (Jmp, [src]) -> error "i"
                                         Inst (J condition, [dst]) -> if checkCond condition m then setRIP (readOperand dst m) m else setRIP((getRIP m) + 4 ) m
                                         Inst (Callq, [src]) -> error "i"
                                         Inst (Retq, []) -> error "i"
                                         otherwise -> error "i"

updateMachine:: Machine -> Operand Int64 -> Int64 -> Bool -> Bool -> Bool -> Machine
updateMachine m d r o z s = storeOperand d r m $ setOF o m $ setZF z m $ setSF s m $ setRIP((getRIP m) + 4 ) m

readOperand:: Operand Int64 -> Machine -> Int64
readOperand (Imm m) mchn = m
readOperand (Reg r) mchn  = getRegister r mchn
readOperand (IndImm i) mchn = accessAddr i mchn
readOperand (IndReg ir) mchn =  accessAddr (getRegister ir mchn) mchn
readOperand (IndBoth i r) mchn = accessAddr (i + (getRegister r mchn)) mchn

sbyteToWord8 :: SByte -> Word8
sbyteToWord8 (Byte s) = s

accessAddr:: Int64 -> Machine -> Int64
accessAddr a m = fromBytes $ map (\n -> sbyteToWord8 $ getMemory (n + a) m) [0..7]

checkCond:: Condition -> Machine -> Bool
checkCond c m = case c of Eq  -> getZF m
                          Neq -> not (getZF m)
                          Gt  -> ((not (getSF m)) && ((not(getZF m)) `xor` (getOF m)))
                          Ge  -> ((not(getSF m)) `xor` (getOF m))
                          Lt  -> ((not(getSF m)) `xor` (getOF m))
                          Le  -> (((getSF m) `xor` (getOF m)) || getZF m)

storeOperand:: Operand Int64 -> Int64 -> Machine -> Machine
storeOperand (Reg r) val m = setRegister r val m
storeOperand (IndImm i) val m = setMemIntToSybte i val m
storeOperand (IndReg ir) val m = setMemIntToSybte (accessAddr (getRegister ir m) m) val m
storeOperand (IndBoth i r) val m = setMemIntToSybte (accessAddr (i + (getRegister r m)) m) val m

setMemIntToSybte :: Int64 -> Int64 -> Machine -> Machine
setMemIntToSybte a s m = foldl (\m' (offset, byte) -> setMemory (offset+a) (Byte byte) m') m (zip [0..7] (fromQuad s))

--Imm imm                 -- $5
-- | Reg Register            -- %rax
-- | IndImm imm              -- (label)
-- | IndReg Register         -- (%rax)
-- | IndBoth Int64 Register  -- -4(%rax)









  {-M { mem = listArray (memoryFloor, memoryCeiling) (pad n0 ++ fs ++ pad n1 ++ ss ++ pad (n2+1) ) --get and set vals from mem
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


The `run` function loops your `step` function until the IP equals the pre-defined
halt value, returning the final machine state.

-}

run :: Machine -> Machine
run initial = until ((haltAddr ==) . getRIP) step initial

eval :: Machine -> Int64
eval initial = getRegister RAX (run initial)
