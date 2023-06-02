import Lean
import Mathlib.Lean.Meta

open Lean Meta Elab

/-- Implementation for both `mk_iff` and `mk_iff_of_inductive_prop`.y
-/
def mkIffOfInductivePropImpl (ind : Name) (rel : Name) (relStx : Syntax) : MetaM Unit := do
  let .defnInfo defVal ← getConstInfo ind | -- TODO: on def only
    throwError "incr_runtime applies only to functions!"
  
  

  addDecl $ .defnDecl {
    value  := defVal.value -- want this value to be correct
    hints  := defVal.hints
    safety := defVal.safety -- not quite sure about how to do saftey but should be exact same
    levelParams := defVal.levelParams
    type := defVal.type -- Want this type to be correct
    name := rel
  }
  addDeclarationRanges rel {
    range := ← getDeclarationRange (← getRef)
    selectionRange := ← getDeclarationRange relStx
  }
  addConstInfo relStx rel


initialize registerBuiltinAttribute {
  name := `incr_runtime,
  descr := ""
  add := fun decl stx _ => Lean.Meta.MetaM.run' do
  let (tgt, idStx) ← match stx with
    | `(attr| mk_iff $tgt:ident) =>
      pure ((← mkDeclName (← getCurrNamespace) {} tgt.getId).1, tgt.raw)
    | `(attr| mk_iff) => pure (decl.appendAfter "runtime", stx)
    | _ => throwError "unrecognized syntax"
  mkIffOfInductivePropImpl decl tgt idStx
  }

