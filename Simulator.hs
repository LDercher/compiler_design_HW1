{-
author: Luke Dercher 
class: EECS 665
student_id: l446d901
-}



module Simulator where

import Data.Bits
import Data.Array.IArray
import Data.Int
import Data.Word
import Machine
import X86
import Loader
import Debug.Trace

--------------------------------------------------------------------------------
-- Simulator                                                                  --
--------------------------------------------------------------------------------

--Test w/ run $ load $ assemble $ <name_prog> note: try with small prog for debugging

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
step m= case (getMemory (getRIP m) m) of Inst (Movq, [src,dst]) -> updateMachine m dst (readOperand src m) False False False
                                         Inst (Addq, [src,dst]) -> updateMachine m dst res ((sameSign (readOperand src m) (readOperand dst m)) && (not (sameSign (readOperand src m) res))) (isZero res) (isNeg res)
                                                                                        where res = readOperand src m + readOperand dst m
                                         Inst (Incq, [src]) -> updateMachine m src res ((sameSign 1 (readOperand src m)) && (not (sameSign 1 res))) (isZero res) (isNeg res)
                                                                                        where res = 1 + readOperand src m                                               
                                         Inst (Subq, [src,dst]) -> updateMachine m dst res (((sameSign (-readOperand src m) (readOperand dst m)) && (not (sameSign (-readOperand src m) res))) || (readOperand src m) == minBound) (isZero res) (isNeg res)
                                                                                        where res = readOperand dst m - readOperand src m
                                         Inst (Decq, [src]) -> updateMachine m src res ((readOperand src m) == minBound) (isZero res) (isNeg res)
                                                                                        where res = readOperand src m - 1
                                         Inst (Cmpq, [src,dst]) -> setOF (((sameSign (-readOperand src m) (readOperand dst m)) && (not (sameSign (-readOperand src m) res))) || (readOperand src m) == minBound) $ setZF (isZero res) $ setSF (isNeg res) $ setRIP((getRIP m) + 4 ) $ m
                                                                                        where res = readOperand dst m - readOperand src m
                                         Inst (Imulq, [src,dst]) -> updateMachine m dst res (if ((res `div` (readOperand src m) )== (readOperand dst m)) then True else False) (isZero res) (isNeg res)
                                                                                        where res = readOperand src m * readOperand dst m
                                         Inst (Notq, [dst]) -> updateMachine m dst (complement (readOperand dst m)) (if ((readOperand dst m) == minBound) then True else False) False False
                                         Inst (Andq, [src,dst]) -> updateMachine m dst res False (isZero res) (isNeg res)
                                                                                        where res = readOperand src m .&. readOperand dst m
                                         Inst (Orq, [src,dst]) -> updateMachine m dst res False (isZero res) (isNeg res)
                                                                                        where res = readOperand src m .|. readOperand dst m
                                         Inst (Xorq, [src,dst]) -> updateMachine m dst res False (isZero res) (isNeg res)
                                                                                        where res = (readOperand src m .|. readOperand dst m) .&. (complement(readOperand src m .&. readOperand dst m))
                                         Inst (Shlq, [imm, dst]) -> updateMachine m dst res False (isZero res) (isNeg res)
                                                                                        where res = shiftL (fromIntegral(readOperand dst m)) (fromIntegral(readOperand imm m))
                                         Inst (Shrq, [imm,dst]) -> updateMachine m dst res False (isZero res) (isNeg res)
                                                                                        where res = shiftR (fromIntegral(readOperand dst m)) (fromIntegral(readOperand imm m))
                                         Inst (Sarq, [imm,dst]) -> updateMachine m dst res False (isZero res) (isNeg res)
                                                                                        where res = rotateR (fromIntegral(readOperand dst m)) (fromIntegral(readOperand imm m))
                                         Inst (Leaq, [src,dst]) -> updateMachine m dst (computeIndAddr src m) False False False
                                         Inst (Set condition, [dst]) -> storeOperand dst res $ setRIP((getRIP m) + 4 ) $ m
                                                                                where res = (readOperand dst m) .&. 0xFF + if checkCond condition m then 1 else 0
                                         Inst (Jmp, [src]) -> setRIP(readOperand src m) m
                                         Inst (J condition, [dst]) -> if checkCond condition m then setRIP (readOperand dst m) m else setRIP((getRIP m) + 4 ) m
                                         Inst (Pushq, [src]) -> setRegister RSP ((getRegister RSP m)-4) $ setMemory (getRegister RSP m) (getMemory (readOperand src m) m) $ setRIP((getRIP m) + 4 ) $ m
                                         Inst (Popq, [dst]) -> storeOperand dst (accessAddr (getRegister RSP m) m) $ setRegister RSP ((getRegister RSP m)+ 4) $ setRIP((getRIP m) + 4 ) $ m
                                         Inst (Callq, [src]) -> setRegister RSP ((getRegister RSP m)-8) $ setMemory (getRIP m) (getMemory (readOperand src m) m) $ setRIP(readOperand src m) $ m
                                         Inst (Retq, []) -> setRIP (accessAddr (getRegister RSP m) m)  $ setRegister RSP ((getRegister RSP m)+ 4) $ m
                                         otherwise -> error "bad instruction"

updateMachine:: Machine -> Operand Int64 -> Int64 -> Bool -> Bool -> Bool -> Machine
updateMachine m d r o z s = storeOperand d r $ setOF o $ setZF z $ setSF s $ setRIP((getRIP m) + 4 ) $ m

computeIndAddr:: Operand Int64 -> Machine -> Int64
computeIndAddr (Imm m) mchn = m
computeIndAddr (Reg r) mchn = getRegister r mchn
computeIndAddr (IndBoth i r) mchn = i + (getRegister r mchn)

sameSign:: Int64 -> Int64 -> Bool
sameSign l r = if (signum l == signum r) then True else False

isZero:: Int64 -> Bool
isZero i
      | (i == 0) = True
      | otherwise = False

isNeg:: Int64 -> Bool
isNeg i 
      | (i < 0) = True
      | otherwise = False

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


{-

The `run` function loops your `step` function until the IP equals the pre-defined
halt value, returning the final machine state.

-}

run :: Machine -> Machine
run initial = until ((haltAddr ==) . getRIP) step initial

eval :: Machine -> Int64
eval initial = getRegister RAX (run initial)

{- 
Helper funcs
-}

first:: (a,b,c) -> a
first (x,_,_) = x

second:: (a,b,c) -> b
second (_,y,_) = y

third:: (a,b,c) -> c
third (_,_,z) = z