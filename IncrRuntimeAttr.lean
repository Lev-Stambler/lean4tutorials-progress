import Lean
import Mathlib.Lean.Meta

open Lean Meta Elab
open Nat

/-- Implementation for both `mk_iff` and `mk_iff_of_inductive_prop`.y
-/
def mkRuntimePropImpl (ind : Name) (rel : Name) (relStx : Syntax) : MetaM Unit := do
  let .defnInfo defVal ← getConstInfo ind | -- TODO: on def only
    throwError "incr_runtime applies only to `def` functions"
  ;

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

  -- let ⟨mprFvar, mpr'⟩ ← mpr.intro1
  -- toInductive mpr' constrs ((fvars.toList.take params).map .fvar) shape mprFvar
 
  -- TODO: get rid of return type?
  -- TODO: I dont think that this is right
  let runtime_type := Expr.lam `args defVal.type (.app defVal.value (.bvar 0)) .default

  -- := Expr.lam `args defVal.type (match defVal.value with
  -- ) .default
  -- TODO:?
  let rec runtime_value : Expr → Expr 
    | Expr.app f args => mkAppN (.const ``Nat.add []) #[.app (.const ``Nat.succ []) (.const ``Nat.zero []),
        runtime_value f] 
    | _ => .const ``Nat.zero []

  -- Add decleration of Runtime Function
  addDecl $ .defnDecl {
    value  := defVal.value -- want this value to be correct
    hints  := defVal.hints
    safety := defVal.safety -- not quite sure about how to do saftey but should be exact same
    levelParams := defVal.levelParams
    type := runtime_type -- Want this type to be correct
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
    | `(attr| incr_runtime) => pure (decl.appendAfter "Runtime", stx)
    | _ => throwError "unrecognized syntax"
  mkRuntimePropImpl decl tgt idStx
  }

