import Assay
import Examples.Forms.Uncompared

/--
info: theorems, run on the original functions:
  T1 shift_zero: 1000/1000 random inputs satisfy the hypotheses

mutant              T1   verdict
shift: 6:44: * ↦ +  ✗    killed
shift: 6:46: 2 ↦ 3  ·    untested
shift: 6:46: 2 ↦ 1  ·    untested
shift: 6:48: + ↦ -  ✗    killed

4 mutants: 2 killed, 0 holes, 2 untested, 0 equivalent, 0 timed out, 0 stillborn
-/
#guard_msgs in
#assay Forms.Uncompared.shift
