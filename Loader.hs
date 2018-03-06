module Loader where

import Data.Array.IArray
import Data.Char
import Data.Int
import Data.List
import Data.Maybe

import Machine
import X86
import Text
import RunAsm

--------------------------------------------------------------------------------
-- Executable images                                                          --
--------------------------------------------------------------------------------

{-

An executable image is a half-way point between the source assembly language
program and the machine image.  You can think of it as a dramatic simplification
of the ELF or PE formats used in practice.

Our executable images contain:

  - The list of `SByte`s making up the executable code, called `textSegment`,
    along with the starting address for the text segment `textAddr`;

  - The list of `SByte`s making up the data, called `dataSegment`, along with
    the starting byte for the data segment `dataAddr`;

  - The starting address for execution (i.e., the initial RIP), called `start`.
    Note that this means that execution need not start at the lowest address in
    the code segment.
-}

data Executable = E { start, textAddr, dataAddr :: Int64
                    , textSegment, dataSegment :: [SByte] }

--------------------------------------------------------------------------------
-- Assembler                                                                  --
--------------------------------------------------------------------------------

{-

Your first task is to write an assembler (and linker); this is responsible for
taking a `Prog` value and producing an `Executable` value.  Conceptually, this
has three steps.

 - You need to transform the blocks of assembly code in the source program into
   a continuous stream of `SByte`s.  The interesting step here is that you need
   to turn textual labels in the source program into concrete integers in the
   executable image.

 - You need to transform the data blocks in the source program into a stream of
   `SByte`s.  Note that, following the slides, we want all labels in a generated
   program to be 4-byte aligned.  For the instruction stream, this will be easy,
   as we are assuming that all instructions are represented by 4-`SByte`
   sequences.  For data values, you will have to ensure that each label is on a
   4-byte boundary, inserting padding (0 bytes will do) if needed.

 - Finally, you will need to compute the start address.  Assume that programs
   will always start execution with the "main" label.

A couple of tips.

 - You may find Haskell's list-folding functions---`foldl` and `foldr`---
   particularly useful in implementing your assembler.

 - You do not need to handle errors gracefully---if the program refers to a
   label that does not exist, for example, your assembler can just crash.

 - While it is not mandatory, the sample solutions will always place the code
   segment below the data segment in memory.  If you do the same, you may find
   it easier to compare your results against the provided machine images.

-}


assemble :: Prog -> Executable
assemble p = E { start = fromJust (lookup "main" labels)
               , textAddr = memoryFloor
               , dataAddr = dataStart
               , textSegment = concatMap (sbytesFromInstr . patch labels . snd) codeBlocks
               , dataSegment = concatMap (sbytesFromData labels . snd) dataBlocks }
    where (codeBlocks, dataBlocks) = foldr partitioner ([], []) p
              where partitioner (label, _, Text instrs) (codeBlocks, dataBlocks) = ((label, instrs) : codeBlocks, dataBlocks)
                    partitioner (label, _, Data bytes) (codeBlocks, dataBlocks) = (codeBlocks, (label, bytes) : dataBlocks)
          (labels, dataStart) = (finalLabelMap, dataStart)
              where codeLabels (i, labels) (label, instrs) = (i + blockLen, (label, i) : labels)
                        where blockLen = 4 * genericLength instrs
                    (dataStart, codeLabelMap) = foldl codeLabels (memoryFloor, []) codeBlocks
                    dataLabels (i, labels) (label, dataBlock) = (i + blockLen, (label, i) : labels)
                        where blockLen | rem == 0 = quotient * 4
                                       | otherwise = (quotient + 1) * 4
                                  where (quotient, rem) = sum (map datumLength dataBlock) `divMod` 4
                              datumLength (String cs) = genericLength cs + 1
                              datumLength (Word _)    = 8
                    (_, finalLabelMap) = foldl dataLabels (dataStart, codeLabelMap) dataBlocks
          patch labels = map (\(op, operands) -> (op, map (patchOperand labels) operands))
          patchOperand labels (Imm (Label l))    = Imm (fromJust (lookup l labels))
          patchOperand _ (Imm (Literal i))       = Imm i
          patchOperand _ (Reg r)                 = Reg r
          patchOperand labels (IndImm (Label l)) = IndImm (fromJust (lookup l labels))
          patchOperand _ (IndImm (Literal i))    = IndImm i
          patchOperand _ (IndReg r)              = IndReg r
          patchOperand _ (IndBoth i r)           = IndBoth i r
          sbytesFromInstr = concatMap (\i -> [Inst i, More, More, More])

          sbytesFromData labels dataBlock = concatMap (padToFour . sbytesFromDatum labels) dataBlock
          sbytesFromDatum _ (String cs) = map (Byte . fromIntegral . ord) cs ++ replicate n (Byte 0)
              where n = 4 - (length cs `mod` 4)
          sbytesFromDatum labels (Word (Label l)) = map Byte $ fromQuad (fromJust (lookup l labels))
          sbytesFromDatum labels (Word (Literal i)) = map Byte $ fromQuad i

          padToFour bs = bs ++ (replicate z $ Byte 0)
              where z = length bs `mod` 4

--------------------------------------------------------------------------------
-- Loader                                                              --
--------------------------------------------------------------------------------

{-

Second, you will write a loader, which transforms and `Executable` program into
a machine image.  That is, you will have to produce a machine image with the
`textSegment` loaded into memory starting from `textAddr`, the `dataSegment`
loaded into memory starting from `dataAddr`, and with the registers set to begin
execution.

A few tips:

 - The Machine module defines a value `zeroMachine`, which is a machine image
   with everything set to 0.  You may find it helpful to build your machine
   image starting from `zeroMachine`.

 - The Haskell array update operator (//) can be used to do a number of updates
   at once.  So, for example, to update bytes i,..,i+3 to b1,..b4, you could do

       mem // [(i, b1), (i + 1, b2), (i + 2, b3), (i + 3, b4)]

 - Be sure to initialize both the instruction pointer and the stack pointer.

-}

load :: Executable -> Machine
load e = zeroMachine{ mem = dataInMemory
                    , regs = regs zeroMachine // [(RSP, memoryCeiling)]
                    , rip = start e }
    where initialMem = mem zeroMachine
          codeInMemory = initialMem // zip [textAddr e..] (textSegment e)
          dataInMemory = codeInMemory // zip [dataAddr e..] (dataSegment e)



--import System.Info (os)
firstArgToRDI = []
----    | os == "mingw32" = [movq ~%RCX ~%RDI]
 --   | otherwise = []



-- Write a function which returns (in RAX) the length of the input array
problem1 =
  [ global "function" $
    firstArgToRDI ++
    [ movq ~$5 ~%RAX
    , retq ] ]
   {- [ movq ~$0 ~%RAX ]
  , text "loop"
    [ cmpq ~$0 ~#RDI
    , j Eq ~$$"exit"
    , incq ~%RAX
    , addq ~$8 ~%RDI
    , jmp ~$$"loop" ]
  , text "exit"
    [ retq ] ] -}

-- Write a function which returns (in RAX) the largest number appearing in the
-- input array.
problem2 =
  [ global "function" $
    firstArgToRDI ++
    [ movq ~#RDI ~%RAX ]
  , text "loop"
    [ cmpq ~$0 ~#RDI
    , j Eq ~$$"exit"
    , cmpq ~%RAX ~#RDI
    , j Le ~$$"step"
    , movq ~#RDI ~%RAX ]
  , text "step"
    [ addq ~$8 ~%RDI
    , jmp ~$$"loop" ]
  , text "exit"
    [ retq ] ]

-- Write a function which returns the sum of the  values in the input array
problem3 =
 [ global "function" $
   firstArgToRDI ++
   [ movq ~$0 ~%RAX ]
 , text "loop"
   [ cmpq ~$0 ~#(0, RDI)
   , j Eq ~$$"exit"
   , addq ~#(0, RDI) ~%RAX
   , addq ~$8 ~%RDI
   , jmp ~$$"loop" ]
 , text "exit"
   [ retq ] ]

-- Write a function which returns *the index of* the largest number appearing in
-- the input array.  For example, if the input array is 4 -2 3 6 1 0, then your
-- function should return 3.
problem4 =
 [ global "function" $
   firstArgToRDI ++
   [ movq ~#RDI ~%RDX
   , movq ~$0 ~%RCX
   , movq ~$0 ~%RAX ]
 , text "loop"
   [ cmpq ~$0 ~#RDI
   , j Eq ~$$"exit"
   , cmpq ~%RDX ~#RDI
   , j Le ~$$"step"
   , movq ~#RDI ~%RDX
   , movq ~%RCX ~%RAX ]
 , text "step"
   [ addq ~$8 ~%RDI
   , incq ~%RCX
   , jmp ~$$"loop" ]
 , text "exit"
   [ retq ] ]

-- Write a function which reverses the elements in the input array.  Do not use
-- any additional storage (for example, on the stack).  This will require
-- somewhat more algorithmic sophistication than the previous examples.
problem5 =
 [ global "function" $
   firstArgToRDI ++
   [ movq ~%RDI ~%RSI ]
 , text "findLast"
   [ cmpq ~$0 ~#RSI
   , j Eq ~$$"found"
   , addq ~$8 ~%RSI
   , jmp ~$$"findLast" ]
 , text "found"
   [ subq ~$8 ~%RSI ]
 , text "swapLoop"
   [ cmpq ~%RSI ~%RDI
   , j Ge ~$$"exit"
   , movq ~#RDI ~%RAX
   , movq ~#RSI ~%RCX
   , movq ~%RAX ~#RSI
   , movq ~%RCX ~#RDI
   , addq ~$8 ~%RDI
   , subq ~$8 ~%RSI
   , jmp ~$$"swapLoop" ]
 , text "exit"
   [ retq ] ]

-- Write a function which sorts the input array; use no additional storage
-- (either explicitly or implicitly).  Your sort should run in n^2 time or less,
-- but you do not need to demonstrate any sophistication in your sorting
-- algorithm.
problem6 =
 [ global "function"
   firstArgToRDI
 , text "outer"
   [ cmpq ~$0 ~#RDI
   , j Eq ~$$"done"
   , movq ~%RDI ~%RSI ]
 , text "inner"
   [ addq ~$8 ~%RSI
   , cmpq ~$0 ~#RSI
   , j Eq ~$$"stepOuter"
   , movq ~#RDI ~%RAX
   , cmpq ~%RAX ~#RSI
   , j Ge ~$$"inner"
   , movq ~#RSI ~%RCX
   , movq ~%RCX ~#RDI
   , movq ~%RAX ~#RSI
   , jmp  ~$$"inner" ]
 , text "stepOuter"
   [ addq ~$8 ~%RDI
   , jmp ~$$"outer" ]
 , text "done"
   [ retq ] ]
