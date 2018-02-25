module RunAsm where

import Text


import Control.Monad
import System.Directory
import System.Info (os)
import System.Process

remove f =
    do b <- doesFileExist f
       when b $ removeFile f

runAsm runtimeC asm =
    do remove "out.s"
       let windows = os == "mingw32"
       if windows then remove "out.exe" else remove "out"
       writeFile "out.s" (textOf asm)
       callProcess "gcc" ((if windows then ["-m64"] else []) ++
                         [runtimeC, "out.s", "-o", "out"])
       callProcess "./out" []

runAsmNoArgs asm = runAsm "runtime.c" asm
runAsmArgs asm   = runAsm "runtimef.c" asm
