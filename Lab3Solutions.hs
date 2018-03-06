module Lab3 where

import X86
import Text
import RunAsm

{-

LAB 3: Assembly programming

DUE: Thursday, February 15, 11:59 PM

This laboratory will allow you to demonstrate facility with simple programming
in x86 assembly.  You will be asked to write a series of assembly functions
manipulating 0-terminated arrays of (64-bit signed) integers.  There are many
ways to write each of these functions; you should not worry about either
runtime, instruction, or register efficiency.

The runtime harness is similar to the in-class examples.  Each of your solutions
should provide a global label "function"; this will be called passing (a pointer
to) an array as its only argument.  The final element of the array will be a
'0'; there will not be any other '0's in the array, but you should not make any
other assumptions about array elements.

We have provided two ways of running your solutions.  `runAsmResult` will call
the provided assembly with several examples arrays, printing the returned value
in each case.  Use this function to run examples 1-3.  `runAsmArray` will call
the provided assembly with several example arrays, printing the arrays after the
function returns.  Use this function to run examples 4-5.  These are implemented
in runtimer.c and runtimea.c respectively, if you want to add your own test
cases.

These problems will be made significantly easier with the use of indirect
addressing.  As with the other features of x86 assembly, we have provided syntax
to help construct indirect references.  However, it is not quite as close the
the underlying assembly:

    movq ~#RDI ~%RAX          -- movq (%rdi), %rax
    movq ~#(4, RDI) ~%RAX     -- movq 4(%rdi), %rax

Also, these problems may bring you up against a limitation of the x86
instruction set we have not previously discussed: an individual x86 instruction
can operate on one indirect reference, but not two.  So, while you can do

    cmpq ~#RDI ~%RAX            -- cmpq %(rdi), %rax

or

    cmpq ~%RAX ~#RDI            -- cmpq %rax, %(rdi)

you cannot do

    cmpq ~#RSI ~#RDI            -- cmpq %(rsi), %(rdi)

Use temporary registers as necessary.

-}


--------------------------------------------------------------------------------
-- Win64 calling convention nonsense                                          --
-- Your solutions will NOT be tested on Win64, so you only need to include    --
-- this shim if you are using Windows yourself.                               --
import System.Info (os)
firstArgToRDI
    | os == "mingw32" = [movq ~%RCX ~%RDI]
    | otherwise = []
--------------------------------------------------------------------------------

-- Write a function which returns (in RAX) the length of the input array
problem1 =
  [ global "function" $
    firstArgToRDI ++
    [ movq ~$0 ~%RAX ]
  , text "loop"
    [ cmpq ~$0 ~#RDI
    , j Eq ~$$"exit"
    , incq ~%RAX
    , addq ~$8 ~%RDI
    , jmp ~$$"loop" ]
  , text "exit"
    [ retq ] ]

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
