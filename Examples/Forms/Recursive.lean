namespace Forms.Recursive

inductive Node where
  | column (name : String)
  | relation (table : String) (children : List Node)

mutual

def Node.columns : Node → Nat
  | .column _ => 1
  | .relation _ children => columnsOf children

def columnsOf : List Node → Nat
  | [] => 0
  | node :: rest => node.columns + columnsOf rest

end

theorem columns_column (name : String) : (Node.column name).columns = 1 := by
  simp [Node.columns]

theorem columns_relation (table : String) (node : Node) (rest : List Node) :
    (Node.relation table (node :: rest)).columns
      = node.columns + (Node.relation table rest).columns := by
  simp [Node.columns, columnsOf]

structure Selection where
  field : String
  children : List Selection

mutual

def Selection.depth : Selection → Nat
  | ⟨_, children⟩ => depthOf children + 1

def depthOf : List Selection → Nat
  | [] => 0
  | selection :: rest => max selection.depth (depthOf rest)

end

theorem depthOf_get (selections : List Selection) (i : Nat) (h : i < selections.length) :
    selections[i].depth ≤ depthOf selections := by
  induction selections generalizing i with
  | nil => simp at h
  | cons selection rest ih =>
    cases i with
    | zero => simp [depthOf]; omega
    | succ i =>
      have := ih i (by simpa using h)
      simp [depthOf]; omega

theorem depth_child (selection : Selection) (i : Nat) (h : i < selection.children.length) :
    selection.children[i].depth < selection.depth := by
  have := depthOf_get selection.children i h
  cases selection
  simp [Selection.depth] at *; omega

inductive Tree where
  | leaf
  | node (left : Tree) (value : Nat) (right : Tree)

def Tree.size : Tree → Nat
  | .leaf => 0
  | .node left _ right => left.size + right.size + 1

def Tree.mirror : Tree → Tree
  | .leaf => .leaf
  | .node left value right => .node right.mirror value left.mirror

theorem size_mirror (tree : Tree) : tree.mirror.size = tree.size := by
  induction tree with
  | leaf => rfl
  | node left value right ihl ihr => simp [Tree.mirror, Tree.size, ihl, ihr]; omega

end Forms.Recursive
