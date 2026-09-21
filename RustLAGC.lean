-- This module serves as the root of the `RustLAGC` library. Import modules here that should be built as part of the library.
-- import RustLAGC.While

import RustLAGC.Structures.Rust
import RustLAGC.Structures.Value.Basic
import RustLAGC.Structures.State.Basic
import RustLAGC.Structures.Trace.Basic
import RustLAGC.Eval

open SVal
open SymState
open SymTrace

#eval (updateVar (SymState.mk []) "x" (val (Val.z 2))).toList
#eval (updateVar [("z", sym), ("x", (val (Val.z 2)))].toAssocList "z" (val (Val.z 2))).toList
#eval symb [("x", sym), ("y", (val (Val.b true)))].toAssocList

#check ε
#check ε ++ [TraceElem.state ([("x", sym), ("y", val (Val.b true))].toAssocList)]
