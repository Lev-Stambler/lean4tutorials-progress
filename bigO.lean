import Lean
import Mathlib
-- import IncrRuntimeAttr
open Lean Meta Elab PrettyPrinter Delaborator
open Nat
open List

namespace BigO

-- Ok, so we may want to use something "monoid esque" but also maybe not
-- It may be better to instead just accumulate on a global variable?
-- def RuntimeFun : α → β × Nat 
-- structure RuntimeFun where
--   f : α → β
--   runtime: Nat

#check Prod.mk Nat Nat

inductive RuntimeFun where
  | func {α β : Type } (runtime : Nat) (g : α → β) : RuntimeFun  


-- instance : Monad RuntimeFun where
--   pure f  := RuntimeFun.func 0  f
--   bind runtime_f next :=
--     match runtime_f with
--     | RuntimeFun.func runtime _ => next (runtime + 1)

-- instance : Coe RuntimeFun (α → β) where  
--   coe F := match F with
--   | RuntimeFun.func _ g => g
-- This is what I'd like
-- def lin_ex_2 : Nat → Bool
--   | 0 => false
--   | n + 1 => lin_ex_2 n
-- @[incr_runtime]
-- def lin_ex_2 (n : Nat) : Bool := false

def runtime_value : Expr → Expr 
    | Expr.app f args => 
        mkAppN (.const ``Prod.mk .nil) #[
          .const ``Nat List.nil,
          .const ``Bool List.nil,
          -- Runtime
          mkAppN (.const ``Nat.add List.nil) #[
            -- Add the runtime accumulated in `f`
            mkAppN (.const ``Nat.add .nil) #[
              .app (
                mkAppN (.const
                  ``Nat.add .nil) #[
                    .app (.const ``Nat.succ List.nil) (.const ``Nat.zero List.nil),
                    runtime_value f -- TODO: change to add with **projection**
                  ] 
              ) (runtime_value f),
              (runtime_value args)],
            -- Add the runtime accumalated in `args`
            runtime_value args
          ],
          -- Value
          Expr.app f args
        ]
      
    | Expr.lam argName argType body _ => 
      .lam argName argType (runtime_value body) .default 
    | .const `a ℓ => --.const ``Nat.zero []
         mkAppN (.const ``Prod.mk .nil) #[
            .const ``Nat List.nil,
            .const ``Bool .nil,
           .const ``Nat.zero .nil,
          .bvar 0--  .const `a ℓ
          --  .const `Bool.true .nil
         ]
    | _ => mkNatLit 69
  
#check runtime_value
def lin_ex_2 (n : Nat) : Bool := false
-- Hmmm... I guess we can j write a macro
#eval Expr.const ``lin_ex_2 .nil

#eval (runtime_value (.lam `a  (.const `Nat .nil) (.const `a .nil) .default))

def ee : Expr := 
  (runtime_value (.lam `a  (.const `Nat .nil) (.const `a .nil) .default))
-- #check ee

@[delab app.foo]
def dee : Delab := (delab ee)

#check (foo)
#eval (foo) false
-- #eval ee false



-- #check let dd := mkPatternWithRef (.const ``Nat.zero []) `(fun n : Nat => false); dd
-- #check Lean.LocalDecl.toExpr 

-- #check dd -->>=  fun x => x
-- #eval 10 + 1
-- #check lin_ex_2Runtime
-- #print lin_ex_2Runtime
-- #eval lin_ex_2Runtime 10

-- #eval lin_ex_2 10

syntax term "^^ " term : term

macro_rules
  | `($f^^ $x) => `(((↑$f) $x).1)

def lin_ex : Nat → (Bool × Nat)
  | 0 => ⟨true, 1⟩ 
  | n + 1 => let b := lin_ex n; ⟨!b.1, 1 + b.2⟩

def quad_ex : Nat → (Bool × Nat)
  | 0 => ⟨true, 1⟩   
  | n + 1 => let b := lin_ex n
    let q := quad_ex n
    ⟨(!b.1 && q.1) || (b.1 && !q.1), b.2 + q.2⟩ 

end BigO