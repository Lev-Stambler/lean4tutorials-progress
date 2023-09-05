import Lean
import Mathlib.Lean.Meta
open Lean Meta Elab
open Nat

def prod_make (α : Type) (β : Type) (a : α) (b : β) : Prod α β := Prod.mk a b
/-- Implementation for both `mk_iff` and `mk_iff_of_inductive_prop`.y
-/
def mkRuntimePropImpl (ind : Name) (rel : Name) (relStx : Syntax) : MetaM Unit := do
  let .defnInfo defVal ← getConstInfo ind | -- TODO: on def only
    throwError "incr_runtime applies only to `def` functions"
  ;
  IO.print "Def Val Value: "
  IO.println defVal.value
  -- Def Val Value!!fun (n : Nat) =>
    -- aaa.match_1.{1} (fun (n._@.bigO2._hyg.144 : Nat) => Bool) n (fun (_ : Unit) => Bool.false) (fun (n : Nat) => aaa n)


  -- let (thmTy,shape) ← Meta.forallTelescope type fun fvars ty ↦ do
  --   if !ty.isProp then throwError "mk_iff only applies to prop-valued declarations"
  --   let lhs := mkAppN (mkConst ind univs) fvars
  --   let fvars' := fvars.toList
  --   let shape_rhss ← constrs.mapM (constrToProp univs (fvars'.take params) (fvars'.drop params))
  --   let (shape, rhss) := shape_rhss.unzip
  --   pure (←mkForallFVars fvars (mkApp2 (mkConst `Iff) lhs (mkOrList rhss)),
  --         shape)

  -- let mvar ← mkFreshExprMVar (some thmTy)
  -- let mvarId := mvar.mvarId!
  -- let (fvars, mvarId') ← mvarId.intros
  -- let [mp, mpr] ← mvarId'.apply (mkConst `Iff.intro) | throwError "failed to split goal"

  -- toCases mp shape

  -- -- let ⟨mprFvar, mpr'⟩ ← mpr.intro1
  -- -- toInductive mpr' constrs ((fvars.toList.take params).map .fvar) shape mprFvar
 
  -- -- TODO: get rid of return type?
  -- -- TODO: I dont think that this is right
  -- -- #print defVal.type
  -- -- TODO: type reinforcement
  -- let runtime_type := match defVal.type with
  -- | Expr.forallE a inpType resType _ => Expr.forallE a inpType 
  --     (mkAppN (.const ``Prod.mk [Level.succ .zero, Level.succ .zero])
  --            #[Expr.sort (Level.succ .zero), Expr.sort (Level.succ .zero),  .const ``Nat [], resType]) .default
  -- | _ => Expr.const ``Nat [] -- TODO: put in error throw
  -- -- TODO: put in error throw
  -- -- | _ => throwError "The input type must be a function with a →"

  -- -- := Expr.lam `args defVal.type (match defVal.value with
  -- -- ) .default
  -- -- TODO:?

  let rec runtime_value : Expr → Bool → MetaM Expr
  |   Expr.app f args, true => do
          IO.print "App true: "
          IO.println f
          pure (
          mkAppN (.const ``prod_make .nil) #[
            .const `Nat List.nil,
            .const `Bool List.nil,
            -- Add the runtime accumulated in `f`
            mkAppN (.const `Nat.add .nil)
            #[
              mkNatLit 1,
              -- Add the runtime accumalated in `args`
              ← runtime_value args false -- TODO: change to add with **projection**
              -- TODO: have let and then return adding of proj and other
            ],
            -- Value: TODO HERE WE CAN RECURSE OR SOMETHING
            .app f args
          ])
  |   Expr.app f args, false => do
          IO.print "App false: "
          IO.println f
          -- Add the runtime accumulated in `f`
          pure (mkAppN (.const `Nat.add .nil)
          #[
            mkNatLit 1,
            -- Add the runtime accumalated in `args`
            ← runtime_value args false -- TODO: change to add with **projection**
            -- TODO: have let and then return adding of proj and other
          ])
  |   Expr.lam argName argType body _, true => do
          IO.print "Lam true: "
          IO.println body
          pure (.lam argName argType (← runtime_value body true) .default )
  |   Expr.lam argName argType body _, false => do
          IO.print "Lam false: "
          IO.println body
          pure (.lam argName argType (← runtime_value body false) .default)
  -- | .const `a ℓ => --.const ``Nat.zero []
  --      mkAppN (.const ``prod_make .nil) #[
  --         .const `Nat List.nil,
  --         .const `Nat .nil,
  --         mkNatLit 0,
  --         .const `a ℓ
  --      ]
  |   e, true => do
          IO.print "catch: "
          IO.println e
          pure (mkAppN (.const ``prod_make .nil) #[.const `Nat [], .const `Bool [], mkNatLit 10, .const `Bool.false []])
  |   e, false => do
        IO.print "catch: "
        IO.println e
        pure (mkNatLit 0)
 
  -- Add decleration of Runtime Function
  addDecl $ .defnDecl {
    value  := ← runtime_value defVal.value true-- want this value to be correct
    hints  := defVal.hints
    safety := defVal.safety -- not quite sure about how to do saftey but should be exact same
    levelParams := defVal.levelParams
    --type := runtime_type
    type := .forallE `a (.const `Nat []) (mkAppN (.const ``Prod.mk [Level.succ .zero, Level.succ .zero]) #[Expr.sort (Level.succ .zero), Expr.sort (Level.succ .zero), Expr.const ``Nat [], Expr.const ``Bool []]) .default --runtime_type -- Want this type to be correct
    name := rel
  }
  -- addDeclarationRanges rel {
  --   range := ← getDeclarationRange (← getRef)
  --   selectionRange := ← getDeclarationRange relStx
  -- }
  -- addConstInfo relStx rel


initialize registerBuiltinAttribute {
  name := `incr_runtime,
  descr := ""
  add := fun decl stx _ => Lean.Meta.MetaM.run' do
  let (tgt, idStx) ← match stx with
    -- | `(attr| incr_runtime $tgt:ident) =>
    --   pure ((← mkDeclName (← getCurrNamespace) {} tgt.getId).1, tgt.raw)
    | `(attr| incr_runtime) => 
        pure (decl.appendAfter "Runtime", stx)
    | _ => throwError "unrecognized syntax"
  IO.print "Syntax: "
  IO.println stx
  IO.println ""
  mkRuntimePropImpl decl tgt idStx
  }


