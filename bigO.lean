import Lean
import Mathlib
import IncrRuntimeAttr

open Lean
namespace BigO

-- Ok, so we may want to use something "monoid esque" but also maybe not
-- It may be better to instead just accumulate on a global variable?
-- def RuntimeFun : α → β × Nat 
-- structure RuntimeFun where
--   f : α → β
--   runtime: Nat

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
@[incr_runtime] def lin_ex_2 : Nat → Bool
  | 0 => true
  | n + 1 => lin_ex_2 n

#eval 10 + 1
#check lin_ex_2runtime

#eval lin_ex_2 10

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