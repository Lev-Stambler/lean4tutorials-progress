/--
## Exercises
--/

/-
1. [**Metavariables**] Create a metavariable with type `Nat`, and assign to it value `3`.
Notice that changing the type of the metavariable from `Nat` to, for example, `String`, doesn't raise any errors - that's why, as was mentioned, we must make sure *"(a) that `val` must have the target type of `mvarId` and (b) that `val` must only contain `fvars` from the local context of `mvarId`"*.
-/



/-
2. [**Metavariables**] What would `instantiateMVars (Lean.mkAppN (Expr.const 'Nat.add []) #[mkNatLit 1, mkNatLit 2])` output?
3. [**Metavariables**] Fill in the missing lines in the following code.

  ```
  #eval show MetaM Unit from do
    let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
    let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

    -- Create `mvar1` with type `Nat`
    -- let mvar1 ← ...
    -- Create `mvar2` with type `Nat`
    -- let mvar2 ← ...
    -- Create `mvar3` with type `Nat`
    -- let mvar3 ← ...

    -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
    -- ...

    -- Assign `mvar3` to `1`
    -- ...

    -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
    ...
  ```
4. [**Metavariables**] Consider the theorem `red`, and tactic `explore` below.  
  a) What would be the `type` and `userName` of metavariable `mvarId`?  
  b) What would be the `type`s and `userName`s of all local declarations in this metavariable's local context?  
  Print them all out.

  ```
  elab "explore" : tactic => do
    let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
    let metavarDecl : MetavarDecl ← mvarId.getDecl

    IO.println "Our metavariable"
    -- ...

    IO.println "All of its local declarations"
    -- ...

  theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
    explore
    sorry
  ```
5. [**Metavariables**] Write a tactic `solve` that proves the theorem `red`.
6. [**Computation**] What is the normal form of the following expressions:  
  **a)** `fun x => x` of type `Bool → Bool`  
  **b)** `(fun x => x) ((true && false) || true)` of type `Bool`  
  **c)** `800 + 2` of type `Nat`
7. [**Computation**] Show that `1` created with `Expr.lit (Lean.Literal.natVal 1)` is definitionally equal to an expression created with `Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])`.
8. [**Computation**] Determine whether the following expressions are definitionally equal. If `Lean.Meta.isDefEq` succeeds, and it leads to metavariable assignment, write down the assignments.  
  **a)** `5 =?= (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))`  
  **b)** `2 + 1 =?= 1 + 2`  
  **c)** `?a =?= 2`, where `?a` has a type `String`  
  **d)** `?a + Int =?= "hi" + ?b`, where `?a` and `?b` don't have a type  
  **e)** `2 + ?a =?= 3`  
  **f)** `2 + ?a =?= 2 + 1`
9. [**Computation**] Write down what you expect the following code to output.

```
@[reducible] def reducibleDef     : Nat := 1 -- same as `abbrev`
@[instance] def instanceDef       : Nat := 2 -- same as `instance`
def defaultDef                    : Nat := 3
@[irreducible] def irreducibleDef : Nat := 4

@[reducible] def sum := [reducibleDef, instanceDef, defaultDef, irreducibleDef]

#eval show MetaM Unit from do
  let constantExpr := Expr.const `sum []

  Meta.withTransparency Meta.TransparencyMode.reducible do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  Meta.withTransparency Meta.TransparencyMode.instances do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  Meta.withTransparency Meta.TransparencyMode.default do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  Meta.withTransparency Meta.TransparencyMode.all do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  let reducedExpr ← Meta.reduce constantExpr
  dbg_trace (← ppExpr reducedExpr) -- ...
```
10. [**Constructing Expressions**] Create expression `fun x, 1 + x` in two ways:  
  **a)** not idiomatically, with loose bound variables  
  **b)** idiomatically.  
  In what version can you use `Lean.mkAppN`? In what version can you use `Lean.Meta.mkAppM`?
11. [**Constructing Expressions**] Create expression `∀ (yellow: Nat), yellow`.
12. [**Constructing Expressions**] Create expression `∀ (n : Nat), n = n + 1` in two ways:  
  **a)** not idiomatically, with loose bound variables  
  **b)** idiomatically.  
  In what version can you use `Lean.mkApp3`? In what version can you use `Lean.Meta.mkEq`?
13. [**Constructing Expressions**] Create expression `fun (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)` idiomatically.
14. [**Constructing Expressions**] What would you expect the output of the following code to be?

```
#eval show Lean.Elab.Term.TermElabM _ from do
  let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
  let expr ← Elab.Term.elabTermAndSynthesize stx none

  let (_, _, conclusion) ← forallMetaTelescope expr
  dbg_trace conclusion -- ...

  let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
  dbg_trace conclusion -- ...

  let (_, _, conclusion) ← lambdaMetaTelescope expr
  dbg_trace conclusion -- ...
```
15. [**Backtracking**] Check that the expressions `?a + Int` and `"hi" + ?b` are definitionally equal with `isDefEq` (make sure to use the proper types or `Option.none` for the types of your metavariables!).
Use `saveState` and `restoreState` to revert metavariable assignments.
-/
