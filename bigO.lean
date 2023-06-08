import Lean
import Mathlib
import IncrRuntimeAttr
open Lean Meta Elab PrettyPrinter Delaborator 
open Nat Meta

-- def prod_make (α : Type) (β : Type) (a : α) (b : β) : Prod α β := Prod.mk a b

def add_three (x y z : Nat) := x + y + z

namespace BigO

-- Ok, so we may want to use something "monoid esque" but also maybe not
-- It may be better to instead just accumulate on a global variable?
-- def RuntimeFun : α → β × Nat 
-- structure RuntimeFun where
--   f : α → β
--   runtime: Nat

#check Prod.mk Nat Nat

-- inductive RuntimeFun where
--   | func {α β : Type } (runtime : Nat) (g : α → β) : RuntimeFun  


def addDeclBoy := addDecl $ .defnDecl {
    value  := .const `sorry .nil-- runtime_value defVal.value true-- want this value to be correct
    hints  := defVal.hints
    safety := defVal.safety -- not quite sure about how to do saftey but should be exact same
    levelParams := defVal.levelParams
    --type := runtime_type
    type := .forallE `a (.const `Nat .nil) (mkAppN (.const ``Prod.mk [Level.succ .zero, Level.succ .zero]) #[Expr.sort (Level.succ .zero), Expr.sort (Level.succ .zero), Expr.const ``Nat [], Expr.const ``Bool []]) .default --runtime_type -- Want this type to be correct
    name := rel
}


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


def runtime_value : Expr → Bool → Expr
|   Expr.app f args, true => 
        mkAppN (.const `prod_make .nil) #[
          .const `Nat List.nil,
          .const `Nat List.nil,
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
  
#check runtime_value
def lin_ex_2 (n : Nat) : Nat := 1 + n
-- Hmmm... I guess we can j write a macro
#eval  (Expr.const `lin_ex_2 .nil)

#eval (runtime_value (.lam `a  (.const `Nat .nil) (.const `a .nil) .default) true)


def aaa [Monad m] : MetaM DefinitionVal := do 
    let .defnInfo defVal ← getConstInfo (`runtime_value)
        | throwError "aaa";
    pure defVal

#check aaa


def ee : Expr := 
   --  TODO: mkAppN is too powerful!!!
   (runtime_value (.lam `a  (.const ``Nat .nil) (mkAppN (.const `Nat.add .nil) #[.bvar 0, mkNatLit 13] ) .default) true)
-- #eval elabEval ee

@[delab app.foo]
def dee : Delab := do (delab ee)

@[delab app.goo]
def deee : Delab := do (delab (Expr.app ee (mkNatLit 2)))

#check (foo)

#check (foo)
#eval (foo) 2
#eval goo

def fff (a : Nat) : Nat := 
  prod_make ℕ ℕ
    (Nat.add 1
      (prod_make ℕ ℕ (
        Nat.add 1 (
          prod_make ℕ ℕ (
            Nat.add 1 (prod_make ℕ ℕ 1 1).1) (1)).1) 1).1)
    (Nat.add 2 1)

#eval fff 1



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

def kk : ℕ → ℕ × ℕ := fun a =>
  prod_make ℕ ℕ
    (Nat.add
      (Nat.add (succ zero)
        (prod_make ℕ ℕ
            (Nat.add (Nat.add (succ zero) (prod_make ℕ ℕ (succ zero) (succ zero)).1)
              (prod_make ℕ ℕ
                  (Nat.add
                    (Nat.add (succ zero)
                      (prod_make ℕ ℕ
                          (Nat.add
                            (Nat.add (succ zero)
                              (prod_make ℕ ℕ
                                  (Nat.add (Nat.add (succ zero) (prod_make ℕ ℕ (succ zero) (succ zero)).1)
                                    (prod_make ℕ ℕ (succ zero) (succ zero)).1)
                                  1).1)
                            (prod_make ℕ ℕ (succ zero) (succ zero)).1)
                          (2)).1)
                    (prod_make ℕ ℕ
                        (Nat.add (Nat.add (succ zero) (prod_make ℕ ℕ (succ zero) (succ zero)).1)
                          (prod_make ℕ ℕ (succ zero) (succ zero)).1)
                        (22)).1)
                  2).1)
            (2)).1)
      (prod_make ℕ ℕ
          (Nat.add
            (Nat.add (succ zero)
              (prod_make ℕ ℕ
                  (Nat.add
                    (Nat.add (succ zero)
                      (prod_make ℕ ℕ
                          (Nat.add (Nat.add (succ zero) (prod_make ℕ ℕ (succ zero) (succ zero)).1)
                            (prod_make ℕ ℕ (succ zero) (succ zero)).1)
                          1).1)
                    (prod_make ℕ ℕ (succ zero) (succ zero)).1)
                  (1)).1)
            (prod_make ℕ ℕ
                (Nat.add (Nat.add (succ zero) (prod_make ℕ ℕ (succ zero) (succ zero)).1)
                  (prod_make ℕ ℕ (succ zero) (succ zero)).1)
                (1)).1)
          1).1)
    (Nat.add 2 1)

#eval kk 10