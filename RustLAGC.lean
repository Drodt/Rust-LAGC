-- This module serves as the root of the `RustLAGC` library. Import modules here that should be built as part of the library.
-- import RustLAGC.While

import RustLAGC.Structures.Rust
import RustLAGC.Structures.Values
import RustLAGC.Structures.Traces
import RustLAGC.Eval

open SVal
open SymState
open SymTrace
open Event

#eval (update [].toAssocList' ("x", z 2)).toList
#eval (update [("z", sym), ("x", z 2)].toAssocList' ("z", z 2)).toList
#eval symb [("x", sym), ("y", b true)].toAssocList'

#check ε 
#check tS ε [("x", sym), ("y", b true)].toAssocList'
#check tE ε $ ev [] []
#check (ε.tS [("x",sym)].toAssocList').tE $ ev [] []
