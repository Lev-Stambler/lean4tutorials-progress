import Lean
import Mathlib

open Lean
namespace BigO

-- def BoundedFun {α β : Type } := 
--   { f : α  → β  // true  } 

/- A function wrapper which will keep track of the number of steps -/
-- structure RuntimeFun (α β : Type) where 
--   f : α → β   
--   n_steps : Nat

-- instance {α β : Type } : CoeFun (RuntimeFun α β) (fun _ => α → β) where    
--   coe F := F.f

-- instance {α β : Type } : CoeFun (α → β) (fun _ => RuntimeFun α β) where    
--   coe f := ⟨f, 0⟩

-- def RuntimeFun {α β : Type} := α → β × Nat

-- We need to set quotPrecheck to false as __numb_computation_steps is not a valid term 
set_option quotPrecheck false
/-
-/
-- notation:200 "^^" f x => (f (1 + __numb_computation_steps) x) 
-- macro:200 
syntax:10 (name := incr_runtime) "^^" term:10 term:11 : term

-- @[macro incr_runtime] def incr_runtime_impl : Macro
--   | `(^^ $l:term $r:term) => `($l (1 + __numb_computation_steps) $r) -- we can use the quotation mechanism to create `Syntax` in macros
--   | _ => Macro.throwUnsupported
set_option pp.rawOnError true

-- macro "^^" : term => do
--  `(fun f exx => f (1 + __numb_computation_steps) exx)
syntax term "^^ " term : term

macro_rules
  | `($f^^ $x) => `($f (1 + __numb_computation_steps) $x)
--  $f (1 + __numb_computation_steps) $x)

  -- fun (y, __numb_computation_steps_new) => let __numb_computation_steps := __numb_computation_steps + __numb_computation_steps_new

set_option quotPrecheck true

structure BoundedFun where 
  inp : Type u
  out: Type u
  f : inp → out
  n_comp_steps : Nat

instance (α β : Type) : CoeFun (α → β) (fun _ => BoundedFun) where
  coe f := ⟨α, β, f, 0⟩

instance : Monad BoundedFun where
  pure f := ↑f 
  bind bounded_fun next_g := (let b :BoundedFun := ↑g 
    ⟨b.inp, b.out, b.f, b.n_comp_steps + bounded_fun.n_comp_steps⟩ )
            

def square_it : Nat → Nat × Nat
  | 0 => (0, 0) 
  | n + 1 =>
  let (a, b) := lin_it (n + 1)
  let (c, d) := square_it n
  (a + c, b + d)

theorem square_it_O_n : (fun n: Nat => (square_it n).snd) ∈ O(fun n => n * n):= 
  let f := fun n: Nat => (square_it n).snd
  have h : ∀ n : Nat, (n ≥ 10 → f n ≤ 4 * n * n) := by
    intros n hn
    simp [square_it, lin_it]
    induction n
    . simp [square_it, lin_it]
    . rename_i n hnn
      cases Nat.le_or_eq_or_le_succ hn with
      | inl hgt =>
        simp [square_it, lin_it]
        repeat (rw [Nat.mul_succ])
        repeat (rw [Nat.add_mul])
        have : 4 * n * n + 4 * n + (4 * n + 4) = (8 * n + 4) + 4 * n *n :=
          by ring
        rw [this]
        apply Nat.add_le_add
        exact (Nat.recOn (motive := fun n => (lin_it n).snd + 1 ≤ 8*n + 4) n 
        (show 0 + 1 ≤ 8 * 0 + 4 from by simp)
        (fun (n : Nat) ih => by
          simp at *; simp [lin_it]; rw [Nat.mul_succ];
          show  _ ≤ 8 * n + 4 + 8
          apply Nat.add_le_add
          . exact ih
          . simp
        ))
        . exact hnn hgt
      | inr he => rw [← he]; simp [square_it, lin_it]
  Exists.intro 4 (Exists.intro 10 h)

end BigO