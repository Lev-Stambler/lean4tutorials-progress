import Lean
import Mathlib.Lean.Meta
import IncrRuntimeAttr
import Lean.Parser.Command
open Lean Elab Command Term Meta

open Bool
open Lean Meta Elab 
open Nat

-- def prod_make (α : Type) (β : Type) (a : α) (b : β) : Prod α β := Prod.mk a b

def add_three (x y z : Nat) := x + y + z

namespace BigO2
end BigO2

-- Ok, so we may want to use something "monoid esque" but also maybe not
-- It may be better to instead just accumulate on a global variable?
-- def RuntimeFun : α → β × Nat 
-- structure RuntimeFun where
--   f : α → β
--   runtime: Nat

#check Prod.mk Nat Nat

inductive RuntimeFun {α β : Type}  where
  | func (g : α → (Nat × β)) : RuntimeFun
  | nil : RuntimeFun

-- inductive RuntimeFun {inp out : Type} where
  -- |
-- type RuntimeFun := Prod Nat (Nat → Nat)

def myTestBoy := 1

-- def samp: Expr := .lam `a  (.const `Nat .nil) (mkAppN (.const `and []) #[.const `Bool.false [], .const `Bool.true []]) .default

-- def counting : Nat → Bool := fun n => false

-- def counting : Nat → Bool := fun n => match n with
--   | 0 => false
--   | n + 1 => counting n

def aaa (n : Nat) := match n with
  | 0 => false
  | n + 1 => aaa n

def aaaRuntime (n : Nat) : (Nat × Bool) := match n with
  | 0 => (0, false)
  | n + 1 => let qq := aaaRuntime n; (qq.1 + 1, qq.2)

-- declare_syntax_cat runtime_def
syntax (name := createRuntimeFunc) "#createRuntimeFunc" : command

#check Expr

elab "#defO " s:ident " : " c:term  cc:term : command => do
  let macroRes ← liftMacroM <| expandMacroImpl? (←getEnv) c


private def ensureValidNamespace (name : Name) : MacroM Unit := do
  match name with
  | .str p s =>
    if s == "_root_" then
      Macro.throwError s!"invalid namespace '{name}', '_root_' is a reserved namespace"
    ensureValidNamespace p
  | .num .. => Macro.throwError s!"invalid namespace '{name}', it must not contain numeric parts"
  | .anonymous => return ()

/-- Return `true` if `stx` is a `Command.declaration`, and it is a definition that always has a name. -/
private def isNamedDef (stx : Syntax) : Bool :=
  if !stx.isOfKind ``Lean.Parser.Command.declaration then
    false
  else
    let decl := stx[1]
    let k := decl.getKind
    k == ``Lean.Parser.Command.abbrev ||
    k == ``Lean.Parser.Command.def ||
    k == ``Lean.Parser.Command.theorem ||
    k == ``Lean.Parser.Command.opaque ||
    k == ``Lean.Parser.Command.axiom ||
    k == ``Lean.Parser.Command.inductive ||
    k == ``Lean.Parser.Command.classInductive ||
    k == ``Lean.Parser.Command.structure

/-- Return `true` if `stx` is an `instance` declaration command -/
private def isInstanceDef (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Command.declaration &&
  stx[1].getKind == ``Lean.Parser.Command.instance


/-- Return `some name` if `stx` is a definition named `name` -/
private def getDefName? (stx : Syntax) : Option Name := do
  if isNamedDef stx then
    let (id, _) := expandDeclIdCore stx[1][1]
    some id
  else if isInstanceDef stx then
    let optDeclId := stx[1][3]
    if optDeclId.isNone then none
    else
      let (id, _) := expandDeclIdCore optDeclId[0]
      some id
  else
    none


private def setDeclIdName (declId : Syntax) (nameNew : Name) : Syntax :=
  let (id, _) := expandDeclIdCore declId
  -- We should not update the name of `def _root_.` declarations
  assert! !(`_root_).isPrefixOf id
  let idStx := mkIdent nameNew |>.raw.setInfo declId.getHeadInfo
  if declId.isIdent then
    idStx
  else
    declId.setArg 0 idStx


/--
Update the name of the given definition.
This function assumes `stx` is not a nameless instance.
-/
private def setDefName (stx : Syntax) (name : Name) : Syntax :=
  if isNamedDef stx then
    stx.setArg 1 <| stx[1].setArg 1 <| setDeclIdName stx[1][1] name
  else if isInstanceDef stx then
    -- We never set the name of nameless instance declarations
    assert! !stx[1][3].isNone
    stx.setArg 1 <| stx[1].setArg 3 <| stx[1][3].setArg 0 <| setDeclIdName stx[1][3][0] name
  else
    stx




private def expandDeclNamespace? (stx : Syntax) : MacroM (Option (Name × Syntax)) := do
  let some name := getDefName? stx | return none
  if (`_root_).isPrefixOf name then
    ensureValidNamespace (name.replacePrefix `_root_ Name.anonymous)
    return none
  let scpView := extractMacroScopes name
  match scpView.name with
  | .str .anonymous _ => return none
  | .str pre shortName => return some (pre, setDefName stx { scpView with name := shortName }.review)
  | _ => return none


-- def «def1»            := leading_parser
  
@[command_parser] def def1 := leading_parser
  Lean.Parser.Command.declId >> Lean.Parser.ppIndent Lean.Parser.Command.optDeclSig >> Lean.Parser.Command.declVal >> Lean.Parser.Command.optDefDeriving >> Lean.Parser.Command.terminationSuffix

@[command_elab def1]
def elabDeclaration1 : CommandElab := fun stx: Syntax => do
  elabMutualDef #[stx] (getTerminationHints stx)

  -- match (← liftMacroM <| expandDeclNamespace? stx) with
  -- | some (ns, newStx) => do
  --   let ns := mkIdentFrom stx ns
  --   let newStx ← `(namespace $ns $(⟨newStx⟩) end $ns)
  --   withMacroExpansion stx newStx <| elabCommand newStx
  -- | none => do
  --   let decl     := stx[1]
  --   let declKind := decl.getKind
  --   if declKind == ``Lean.Parser.Command.«axiom» then
  --     let modifiers ← elabModifiers stx[0]
  --     elabAxiom modifiers decl
  --   else if declKind == ``Lean.Parser.Command.«inductive» then
  --     let modifiers ← elabModifiers stx[0]
  --     elabInductive modifiers decl
  --   else if declKind == ``Lean.Parser.Command.classInductive then
  --     let modifiers ← elabModifiers stx[0]
  --     elabClassInductive modifiers decl
  --   else if declKind == ``Lean.Parser.Command.«structure» then
  --     let modifiers ← elabModifiers stx[0]
  --     elabStructure modifiers decl
  --   else if isDefLike decl then
  --   else
  --     throwError "unexpected declaration"
  
def1 aa (n : Nat) := 0 if n = 1 else aa n - 1
-- def1 aa : Nat → Nat
-- | 0 => 1
--   | n + 1 => aa n

@[command_elab createRuntimeFunc]
def createRuntimeFuncImpl : CommandElab := fun stx => do
  -- logInfo "AAA"
  if let some str := stx[1].isStrLit? then
    logInfo s!"Specially elaborated string literal!: {str} : String"
  else
    throwUnsupportedSyntax


elab "#findCElab " c:command : command => do
  let macroRes ← liftMacroM <| expandMacroImpl? (←getEnv) c
  match macroRes with
  | some (name, synt) => logInfo s!"Next step is a macro: {name.toString}"
  | none =>
    let kind := c.raw.getKind
    let elabs := commandElabAttribute.getEntries (←getEnv) kind
    match (elabs : List (KeyedDeclsAttribute.AttributeEntry CommandElab)) with
    | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
    | _ =>
      -- logInfo s!"{Lean.Elab.Command.elabDeclaration c}"
      logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)} {elabs.map (fun el => el.declName.toString)}"

#findCElab def counting (n : Nat) := match n with
  | 0 => false
  | n + 1 => counting n

#check Lean.Elab.Command.elabDeclaration 


-- Read this Elab stuff...
-- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/master/md/main/elaboration.md


@[incr_runtime]
def counting (n : Nat) := match n with
  | 0 => false
  | n + 1 => counting n

#print counting

def counting3 : Nat → Bool
  | 0 => false
  | n + 1 => counting3 n

#print counting
-- #print counting2
#eval Lean.Meta.getEqnsFor? (nonRec := false) `counting
#eval Lean.Meta.getEqnsFor? (nonRec := true) `counting2
#eval Lean.Meta.getEqnsFor? (nonRec := false) `counting3

#check counting._eq_1
#print counting._eq_1

#print counting3._eq_1
#print counting3._eq_2

#print counting._eq_1
#print counting._eq_2

def addDeclTest : MetaM Unit := do
  -- let .some rec_funs ← Lean.Meta.getEqnsFor? (nonRec := true) (Name.str (.anonymous) "counting") |
    -- throwError "No recursive definition"; -- TODO: throw?
    -- TODO: false?
  -- IO.println <| "Rec funs " ++ toString rec_funs

  -- let aa ← getConstInfo (Array.get! rec_funs 1)

  -- IO.println <| "_eq_ed: " ++ aa

  let .defnInfo defVal ← getConstInfo `counting | -- TODO: on def only
    throwError "incr_runtime applies only to `def` functions"
  ;
  let retType := mkAppN (.const `Prod [
         (.zero),
         (.zero)
      ]) #[.const `Nat [], .const `Bool []]
  
  -- TODO:
  -- let inpType := defVal.type

  let fnType :=  Expr.forallE `a (.const `Nat .nil) 
      retType
    .default --runtime_type -- Want this type to be correct
    
  let check_runtime_def (f_space : Name) (f : String) : MetaM Bool := do
    match (← getEnv).find? $ Name.str f_space (f ++ "Runtime") with
    | some _ => pure true
    | none      => pure false
  
  -- mutual
  -- TODO: rip this is mutual **outside def needed**
  let rec make_recurse (f args : Expr) (runtime_f : Expr → Bool → MetaM Expr) : MetaM Expr := do
    pure (
      Expr.letE `_tmp_rec retType (← runtime_f args true) 
        (
          mkAppN (.const `Prod.mk [.zero, .zero]) #[
          .const `Nat [],
          .const `Bool [],
          -- Add the runtime accumulated in `f`
          mkAppN (.const `Nat.add [])
          #[
            mkNatLit 1,
            -- Add the runtime accumalated in `args`
            .proj `Prod 0 (.bvar 0)
          ],
          -- .proj `Prod 1 (.bvar 0)
          .app f args
        ])
    false)

  let rec runtime_value : Expr → Bool → MetaM Expr
  |   Expr.app f args, true => do
        match f with
        | .const (.str f_space f_str)  _ => do
          if ((← check_runtime_def f_space f_str) || (Name.eqStr (.str f_space f_str) "counting")) then
             pure (
              .letE `tmpRuntime (
                retType
              ) (
                .app (.const (.str f_space (f_str ++ "Runtime")) []) args
              ) (
                mkAppN (.const `Prod.mk [.zero, .zero]) #[
                .const `Nat [],
                .const `Bool [],
                -- Add the runtime accumulated in `f`
                mkAppN (.const `Nat.add [])
                  #[
                    mkNatLit 1,
                    .proj `Prod 0 (.bvar 0)
                  ],
                .proj `Prod 1 (.bvar 0)
          ]
            ) false)
          else
            make_recurse f args runtime_value
        | _ =>
            make_recurse f args runtime_value
          
  |   Expr.app f args, false => do
          -- Add the runtime accumulated in `f`
          pure (mkAppN (.const `Nat.add .nil)
          #[
            mkNatLit 1,
            -- Add the runtime accumalated in `args`
            ← runtime_value args false
          ])
  |   Expr.lam argName argType body _, true => do
          IO.println "Lambda body"
          IO.println (← (eraseRecAppSyntaxExpr body))
          pure (.lam argName argType (← runtime_value body true) .default )
  |   _, false => do
    IO.println "AAA"
    pure (mkNatLit 0)
  |   _, true => do
    throwError "Should not get to caught case with true flag";
    pure (mkNatLit 0)


  addDecl $ .defnDecl {
    value  :=  ← (runtime_value defVal.value true)
    hints  := .abbrev
    safety := .safe -- not quite sure about how to do saftey but should be exact same
    levelParams := []
    --type := runtime_type
    type := fnType
    name := Name.str Name.anonymous "countingRuntime" 
  }



#print counting
#eval addDeclTest

#print countingRuntime



-- example : (counting 10).1 = 2 := by
  -- simp [counting]
  
-- #eval (counting 1)
def aa : MetaM Unit := do 
    let aq := match (← getEnv).find? $ Name.str Name.anonymous "myTestBoya" with
  | some info => true
  | none      => false;

#eval aa