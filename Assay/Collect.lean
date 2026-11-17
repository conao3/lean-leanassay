import Lean
import Assay.Check

/-!
Finding the theorems about the audited functions, and giving the types they quantify over the
instances a check needs (`Repr`, `DecidableEq`, plausible's `Arbitrary` and `Shrinkable`).
-/

open Lean Meta Elab Command

namespace Assay

/-- The module a constant comes from, or the current module. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Whether a theorem is one that Lean generated (equation lemmas, induction principles, …). -/
def isGenerated (env : Environment) (fns : Array Name) (n : Name) : Bool :=
  n.isInternalDetail || fns.contains n.getPrefix || isReservedName env n || isAuxRecursor env n
    || isNoConfusion env n

/-- The definitions of propositions (`def P : Prop`, `def Q (x : α) : Prop`) in the given modules. -/
def propDefsIn (mods : Array Name) : MetaM NameSet := do
  let env ← getEnv
  let mut out : NameSet := {}
  for (n, info) in env.constants.toList do
    let .defnInfo d := info | continue
    if n.isInternalDetail || !mods.contains (moduleOf env n) then continue
    if ← forallTelescope d.type fun _ ret => return ret.isProp then
      out := out.insert n
  return out

/-- Unfolds the propositions defined in the audited modules that a statement's conclusion is,
under its binders and hypotheses, so that `theorem p_proven : P` with `def P : Prop := ∀ x, …`
states `∀ x, …`. The propositions inside the conclusion are left folded, so that their `Decidable`
instances still apply. -/
partial def unfoldHead (propDefs : NameSet) (e : Expr) : MetaM Expr :=
  forallTelescope e fun xs body => do
    let body := body.headBeta
    let .const c us := body.getAppFn | mkForallFVars xs body
    let some (.defnInfo d) := (← getEnv).find? c | mkForallFVars xs body
    if !propDefs.contains c then return ← mkForallFVars xs body
    let v := (d.value.instantiateLevelParams d.levelParams us).beta body.getAppArgs
    mkForallFVars xs (← unfoldHead (propDefs.erase c) v)

/-- A theorem's statement with its conclusion unfolded as `unfoldHead` does. -/
def statementOf (propDefs : NameSet) (thm : Name) : MetaM Expr := do
  unfoldHead propDefs (← getConstInfo thm).type

/-- The theorems in the audited functions' modules whose statement, with the modules' propositions
unfolded, mentions one of the functions, in the order they were declared. -/
def theoremsAbout (fns : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mods := fns.map (moduleOf env)
  let propDefs ← propDefsIn mods
  let mut found : Array (Name × Nat) := #[]
  for (n, info) in env.constants.toList do
    let .thmInfo _ := info | continue
    if isGenerated env fns n || !mods.contains (moduleOf env n) then continue
    let expanded ← deltaExpand (← getConstInfo n).type propDefs.contains
    if !expanded.getUsedConstants.any fns.contains then continue
    let line := (← findDeclarationRanges? n).map (·.range.pos.line) |>.getD 0
    found := found.push (n, line)
  return found.qsort (fun a b => a.2 < b.2 || (a.2 == b.2 && a.1.lt b.1)) |>.map (·.1)

/-- The inductive types of data (not propositions, without indices), declared in modules whose
root is one of `roots`, that occur in an expression. -/
def localInductives (roots : Array Name) (e : Expr) : CoreM (Array Name) := do
  let env ← getEnv
  return e.getUsedConstants.filter fun c =>
    match env.find? c with
    | some (.inductInfo i) =>
      let ret := i.type.getForallBody
      i.numIndices == 0 && ret.isSort && !ret.isProp && roots.contains (moduleOf env c).getRoot
    | _ => false

/-- The inductive types that `localInductives` finds in the expressions, and those in the types of
their constructors, each after the types of its fields. -/
partial def inductiveClosure (roots : Array Name) (es : Array Expr) : CoreM (Array Name) := do
  let mut out := #[]
  let mut seen : NameSet := {}
  for e in es do
    for i in ← localInductives roots e do
      (out, seen) ← visit i out seen
  return out
where
  visit (i : Name) (out : Array Name) (seen : NameSet) : CoreM (Array Name × NameSet) := do
    if seen.contains i then return (out, seen)
    let mut seen := seen.insert i
    let mut out := out
    let .inductInfo info ← getConstInfo i | return (out, seen)
    for c in info.ctors do
      for j in ← localInductives roots (← getConstInfo c).type do
        if j != i then (out, seen) ← visit j out seen
    return (out.push i, seen)

open TSyntax.Compat in
/-- The commands that define a generator for a recursive type (a constructor field's type mentions
the type or one declared with it in a `mutual` block) and make it the `Arbitrary` instance, or
`none` for a type that is not recursive. The generator shrinks the size on the way to every
recursive field (`Gen.direct`, `Gen.nested`), including the fields that hold the type inside
another one, such as `children : List Node`, so it stops; plausible's derived generator spends its
fuel only on the fields whose type is the type itself, and draws the others at the full size. -/
def recursiveArbitrary (ty : Name) : TermElabM (Option (Array Syntax)) := do
  let info ← getConstInfoInduct ty
  let block := info.all.toArray
  let genOf (t : Name) := mkIdent (t ++ `assayArbitrary)
  let fuel := mkIdent `fuel
  let mut recursive := false
  let mut defs : Array Command := #[]
  let mut inst := none
  for t in block do
    let ti ← getConstInfoInduct t
    let argNames ← Deriving.mkInductArgNames ti
    let binders := (← Deriving.mkImplicitBinders argNames)
      ++ (← Deriving.mkInstImplicitBinders ``Plausible.Arbitrary ti argNames)
    let target ← Deriving.mkInductiveApp ti argNames
    let mut leaves : Array Term := #[]
    let mut recs : Array Term := #[]
    for c in ti.ctors do
      let kinds ← forallTelescopeReducing (← getConstInfoCtor c).type fun xs _ =>
        (xs.extract ti.numParams xs.size).mapM fun x => do
          let fieldType ← inferType x
          if fieldType.getAppFn.constName?.any block.contains then return some true
          if fieldType.getUsedConstants.any block.contains then return some false
          return none
      let k := (kinds.filter (·.isSome)).size
      let mut doElems := #[]
      let mut fields := #[]
      for kind in kinds, i in [0:kinds.size] do
        let field := mkIdent (.mkSimple s!"a{i}")
        fields := fields.push field
        let gen ← match kind with
          | some true => `(Assay.Gen.direct $(quote k) Plausible.Arbitrary.arbitrary)
          | some false => `(Assay.Gen.nested Plausible.Arbitrary.arbitrary)
          | none => `(Plausible.Arbitrary.arbitrary)
        doElems := doElems.push (← `(doElem| let $field:ident ← $gen:term))
      let params := Array.replicate ti.numParams (← `(_))
      doElems := doElems.push (← `(doElem| return @$(mkCIdent c) $params* $fields*))
      let body ← `((do $[$doElems:doElem]*))
      if k == 0 then leaves := leaves.push body else recs := recs.push body
    if !recs.isEmpty then recursive := true
    let mut body ← `(Assay.Gen.pick #[$leaves,*] #[$recs,*])
    for u in block do
      let instType ← `(Plausible.Arbitrary $(← Deriving.mkInductiveApp (← getConstInfoInduct u) argNames))
      body ← `(let _ : $instType := ⟨Assay.Gen.step $(genOf u) $fuel⟩; $body)
    defs := defs.push (← `(partial def $(genOf t):ident $binders:bracketedBinder* ($fuel : Nat) :
      Plausible.Gen $target := $body))
    if t == ty then
      inst := some (← `(instance $binders:implicitBinder* : Plausible.Arbitrary $target :=
        ⟨$(genOf t) Assay.floorFuel⟩))
  if !recursive then return none
  let some instCmd := inst | return none
  if (← getEnv).contains (ty ++ `assayArbitrary) then return some #[instCmd]
  return some #[← `(mutual $defs:command* end), instCmd]

/-- Gives a type that lacks them `Repr`, `DecidableEq`, `Arbitrary` and `Shrinkable`: the deriving
handler's instance where one applies, and for the `Arbitrary` of a recursive type the generator of
`recursiveArbitrary`. A type left without an instance makes the checks that need it not executable,
which the report says. -/
def ensureInstances (ty : Name) : CommandElabM Unit := do
  let id := mkIdent ty
  let missing (cls : Name) : CommandElabM Bool := liftTermElabM do
    try
      let inst ← mkAppM cls #[mkConst ty]
      return (← trySynthInstance inst) matches .none
    catch _ => return true
  let arbitrary ← match ← liftTermElabM (recursiveArbitrary ty) with
    | some cmds => pure (cmds.map (⟨·⟩ : Syntax → Command))
    | none => pure #[← `(deriving instance Plausible.Arbitrary for $id)]
  for (cls, cmds) in [
      (``Repr, #[← `(deriving instance Repr for $id)]),
      (``DecidableEq, #[← `(deriving instance DecidableEq for $id)]),
      (``Plausible.Arbitrary, arbitrary),
      (``Plausible.Shrinkable, #[← `(instance : Plausible.Shrinkable $id := {})])] do
    if ← missing cls then
      let before := (← get).messages
      let env ← getEnv
      modify fun s => { s with messages := {} }
      cmds.forM elabCommand
      if (← get).messages.hasErrors then setEnv env
      modify fun s => { s with messages := before }

end Assay
