import Assay
import Examples.Forms.Recursive

/--
info: theorems, run on the original functions:
  T1 columns_column: 1000/1000 random inputs satisfy the hypotheses
  T2 columns_relation: 1000/1000 random inputs satisfy the hypotheses
  T3 depthOf_get: 419/1000 random inputs satisfy the hypotheses
  T4 depth_child: 115/1000 random inputs satisfy the hypotheses
  T5 size_mirror: 1000/1000 random inputs satisfy the hypotheses

mutant                                                                                   T1  T2  T3  T4  T5   verdict
columns := fun _ => default                                                              ✗   ·   -   -   -    killed
columns := fun _ => zero                                                                 ✗   ·   -   -   -    killed
columns: 11:29: | .relation _ children => columnsOf children ↦ 1                         ·   ✗   -   -   -    killed
columns: 10:18: 1 ↦ 2                                                                    ✗   ·   -   -   -    killed
columns: 10:18: 1 ↦ 0                                                                    ✗   ·   -   -   -    killed
columnsOf := fun _ => default                                                            ?   ?   -   -   -    untested
columnsOf := fun _ => zero                                                               ?   ?   -   -   -    untested
columnsOf: 15:21: | node :: rest => node.columns + columnsOf rest ↦ 0                    ·   ✗   -   -   -    killed
columnsOf: 14:11: 0 ↦ 1                                                                  ·   ·   -   -   -    HOLE
columnsOf: 15:34: + ↦ -                                                                  ·   ✗   -   -   -    killed
depth := fun _ => default                                                                -   -   ?   ✗   -    killed
depth := fun _ => zero                                                                   -   -   ?   ✗   -    killed
depth: 34:39: + ↦ -                                                                      -   -   ·   ✗   -    killed
depth: 34:41: 1 ↦ 2                                                                      -   -   ·   ·   -    HOLE
depth: 34:41: 1 ↦ 0                                                                      -   -   ·   ✗   -    killed
depthOf := fun _ => default                                                              -   -   ?   ?   -    untested
depthOf := fun _ => zero                                                                 -   -   ?   ?   -    untested
depthOf: 38:26: | selection :: rest => max selection.depth (depthOf rest) ↦ 0            -   -   ✗   ✗   -    killed
depthOf: 37:11: 0 ↦ 1                                                                    -   -   ·   ·   -    HOLE
depthOf: 38:26: max ↦ min                                                                -   -   ✗   ✗   -    killed
mirror := fun _ => leaf                                                                  -   -   -   -   ✗    killed
mirror := fun x => x                                                                     -   -   -   -   ·    HOLE
mirror: 69:31: | .node left value right => .node right.mirror value left.mirror ↦ .leaf  -   -   -   -   ✗    killed

27 mutants: 15 killed, 4 holes, 4 untested, 0 equivalent, 0 timed out, 4 stillborn
---
warning: hole: `columnsOf: 14:11: 0 ↦ 1` satisfies every theorem but changes the output on an input that satisfies the hypotheses of columns_relation: table := "", node := Forms.Recursive.Node.column "", rest := []
---
warning: hole: `depth: 34:41: 1 ↦ 2` satisfies every theorem but changes the output on an input that satisfies the hypotheses of depthOf_get: selections := [{ field := "", children := [] }], i := 0
---
warning: hole: `depthOf: 37:11: 0 ↦ 1` satisfies every theorem but changes the output on an input that satisfies the hypotheses of depthOf_get: selections := [{ field := "", children := [] }], i := 0
---
warning: hole: `mirror := fun x => x` satisfies every theorem but changes the output on an input that satisfies the hypotheses of size_mirror: tree := Forms.Recursive.Tree.node
  (Forms.Recursive.Tree.node (Forms.Recursive.Tree.leaf) 1 (Forms.Recursive.Tree.leaf))
  0
  (Forms.Recursive.Tree.leaf)
-/
#guard_msgs in
#assay Forms.Recursive.Node.columns Forms.Recursive.columnsOf Forms.Recursive.Selection.depth Forms.Recursive.depthOf Forms.Recursive.Tree.mirror
