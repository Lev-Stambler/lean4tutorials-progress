import Lean
import Mathlib.Lean.Meta

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

def samp: Expr := .lam `a  (.const `Nat .nil) (mkAppN (.const `and []) #[.const `Bool.false [], .const `Bool.true []]) .default

def addDeclTest : MetaM Unit := do
    -- let ddd := match (← getConstInfo $ Name.str Name.anonymous "myTestBoy")? with
    --   | some x => x
    --   | none => panic! "nope"
    
  let check_runtime_def (f : String) : MetaM Bool := do
    match (← getEnv).find? $ Name.str Name.anonymous (f ++ "Runtime") with
    | some _ => pure true
    | none      => pure false

  let rec runtime_value : Expr → Bool → MetaM Expr
  |   Expr.app f args, true => do
        match f with
        | .const (.str _ f_str)  _ => do
          if (← check_runtime_def f_str) then
            -- TODO: ADD 1 somehow
             pure $ mkAppN (.const (f_str ++ "Runtime") []) #[
              -- Add the runtime accumalated in `args`
              args
            ]
          else
            pure (mkAppN (.const `Prod.mk [.zero, .zero]) #[
            .const `Nat [],
            .const `Bool [],
            -- Add the runtime accumulated in `f`
            mkAppN (.const `Nat.add .nil)
            #[
              mkNatLit 1,
              -- Add the runtime accumalated in `args`
              ← runtime_value args false 
            ],
            -- Value: TODO HERE WE CAN RECURSE OR SOMETHING
            .app f args
          ])
        | _ =>
          pure (mkAppN (.const `Prod.mk [.zero, .zero]) #[
            .const `Nat [],
            .const `Bool [],
            -- Add the runtime accumulated in `f`
            mkAppN (.const `Nat.add .nil)
            #[
              mkNatLit 1,
              -- Add the runtime accumalated in `args`
              ← runtime_value args false 
            ],
            -- Value: TODO HERE WE CAN RECURSE OR SOMETHING
            .app f args
          ])
  |   Expr.app f args, false => do
          -- Add the runtime accumulated in `f`
          pure (mkAppN (.const `Nat.add .nil)
          #[
            mkNatLit 1,
            -- Add the runtime accumalated in `args`
            ← runtime_value args false
          ])
  |   Expr.lam argName argType body _, b => do
          pure (.lam argName argType (← runtime_value body b) .default )
  |   _, _ => do pure (mkNatLit 1)
 

    addDecl $ .defnDecl {

    value  :=  ← (runtime_value samp true)
      -- .lam `a (.const `Nat [])
      --   (
      --     (mkAppN (.const `Prod.mk [
      --      (.zero),
      --      (.zero)
      --     ]) #[
      --       .const `Nat [],
      --       .const `Bool [],
      --       mkNatLit 0,
      --       .const `Bool.false []
      --     ]
      --  )
      -- ) .default
    hints  := .abbrev
    safety := .safe -- not quite sure about how to do saftey but should be exact same
    levelParams := []
    --type := runtime_type
    type :=
      .forallE `a (.const `Nat .nil) 
      -- mkAppN (.const ``RuntimeFun []) #[Expr.const ``Nat [], Expr.const ``Bool []]
      -- (.const ``Prod [Level.succ Level.zero, Level.succ Level.zero])
        (mkAppN (.const `Prod [
           (.zero),
           (.zero)
        ]) #[.const `Nat [], .const `Bool []])
      .default --runtime_type -- Want this type to be correct
    name := Name.str Name.anonymous "counting" 
}

#eval addDeclTest

#check counting
#print counting
example : (counting 10).1 = 2 := by
  simp [counting]
  
-- #eval (counting 1)
def aa : MetaM Unit := do 
    let aq := match (← getEnv).find? $ Name.str Name.anonymous "myTestBoya" with
  | some info => true
  | none      => false;
    IO.println aq

#eval aa