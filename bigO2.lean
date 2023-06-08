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



def runtime_value : Expr → Bool → Expr
|   Expr.app f args, true => 
        mkAppN (.const `Prod.mk [.zero, .zero]) #[
          .const `Nat [],
          .const `Bool [],
          -- Add the runtime accumulated in `f`
          mkAppN (.const `Nat.add .nil)
          #[
            mkNatLit 1,
            -- Add the runtime accumalated in `args`
            runtime_value args false -- TODO: change to add with **projection**
            -- TODO: have let and then return adding of proj and other
          ],
          -- Value: TODO HERE WE CAN RECURSE OR SOMETHING
          .app f args
        ]
|   Expr.app f args, false => 
        -- Add the runtime accumulated in `f`
        mkAppN (.const `Nat.add .nil)
        #[
          mkNatLit 1,
          -- Add the runtime accumalated in `args`
          runtime_value args false -- TODO: change to add with **projection**
          -- TODO: have let and then return adding of proj and other
        ]
|   Expr.lam argName argType body _, b => 
        .lam argName argType (runtime_value body b) .default 
-- | .const `a ℓ => --.const ``Nat.zero []
--      mkAppN (.const ``prod_make .nil) #[
--         .const `Nat List.nil,
--         .const `Nat .nil,
--         mkNatLit 0,
--         .const `a ℓ
--      ]
|   _, _ => mkNatLit 1
 

def myTestBoy := 1

def samp: Expr := .lam `a  (.const `Nat .nil) (mkAppN (.const `and []) #[.const `Bool.false [], .const `Bool.true []]) .default

def addDeclTest : MetaM Unit := do
    -- let ddd := match (← getConstInfo $ Name.str Name.anonymous "myTestBoy")? with
    --   | some x => x
    --   | none => panic! "nope"
    let ddd := match (← getEnv).find? $ Name.str Name.anonymous "myTestBoy" with
  | some info => true
  | none      => false

    let .defnInfo defVal ← getConstInfo $ Name.str Name.anonymous "myTestBoy" | -- TODO: on def only
      throwError "ITS NOT THERE!"
    ;
    -- TODO: figure out how to get

    addDecl $ .defnDecl {

    value  := runtime_value samp true 
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