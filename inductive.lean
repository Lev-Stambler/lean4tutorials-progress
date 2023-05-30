namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl
theorem append_nil (as : List α) : append as nil = as := 
  List.recOn (motive := fun as => append as nil = as) as
    (show append nil nil = nil from rfl)
    (fun a as (ih : append as nil = as) =>
      calc append (cons a as) nil = cons a (append as nil) := rfl
        _ = cons a as := by rw [ih]
    )
   
theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  List.recOn (motive := fun as => append (append as bs) cs = append as (append bs cs)) as
    -- (by simp [nil_append])
    rfl
    (
      fun a as ih => show append (append (cons a as) bs) cs = append (cons a as) (append bs cs) from
      calc
        append (append (cons a as) bs) cs = cons a (append (append as bs) cs) := by simp [cons_append]
        _  = cons a (append as (append bs cs)) := by rw [ih]
        _  = append (cons a as) (append bs cs) := rfl
    )

def length (as : List α) : Nat :=    
  match as with
  | nil => Nat.zero
  | cons _ as => Nat.succ (length as)

def reverse (t : List α) : List α :=
  match t with
  | nil => nil
  | cons t' ts => append (reverse ts) (cons t' nil)

example (t : List α) : length (reverse t) = length t := sorry 

theorem length_append (as bs : List α) : length (append as bs) = length as + length bs := 
  List.recOn (motive := fun as : List α  => length (append as bs) = length as + length bs) as
    (
      by
        simp [append_nil, nil_append]
        show length bs = 0 + length bs
        rw [Nat.zero_add]
    )
    (
      fun a as ih => calc
        length (append (cons a as) bs) = length (cons a (append as bs)) := rfl
        _  = Nat.succ (length (append as bs)) := rfl
        _  = Nat.succ (length as + length bs) := by rw [ih]
        _  = Nat.succ (length as) + length bs := by rw [← Nat.succ_add]
        _  = length (cons a as) + length bs  := rfl
    )

end List
end Hidden


-- ## Exercises
-- # 1
-- Try defining other operations on the natural numbers, such as multiplication, the predecessor function (with pred 0 = 0), truncated subtraction (with n - m = 0 when m is greater than or equal to n), and exponentiation. Then try proving some of their basic properties, building on the theorems we have already proved.
-- Since many of these are already defined in Lean's core library, you should work within a namespace named Hidden, or something like that, in order to avoid name clashes.

namespace Hidden
  inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

  namespace Nat
    def add (a b : Nat) : Nat :=
      match a with
      | zero => b
      | succ a => succ (add a b)

    infixl:65 " + " => add

    def multiply (a b : Nat) : Nat :=
      match a with
        | zero => zero
        -- We have 1, return a
        | succ zero => b
        | succ a' => b + (multiply a' b)
  
    infixl:65 " * " => multiply

    -- theorem mul_left_assoc {a b c : Nat} : (a * b) * c = a * (b * c) := by
    --   induction a with
    --   | zero => 
    --     calc (zero * b) * c = zero * c := by rfl
    --     _ = zero := by rfl
    --   | succ a ih => calc
    --       ((succ a) * b) * c = (b + a * b) * c := by rfl
    --       _ = a * c + (a * b) * c := by sorry
    --       _ = a * c + a * (b * c) := by rw [ih]
    --       -- _ = succ a 
  end Nat
end Hidden

namespace Hidden
-- #3 Define an inductive data type consisting of terms built up from the following constructors:

-- const n, a constant denoting the natural number n
-- var n, a variable, numbered n
-- plus s t, denoting the sum of s and t
-- times s t, denoting the product of s and t
inductive Arith where 
| const : Nat → Arith 
| var : Nat → Arith 
| plus : Arith → Arith → Arith
| times : Arith → Arith → Arith  

namespace Arith
open List
open Nat

def lookup (n : Nat) (assignment : List Nat) : Nat := 
  match assignment with
    | nil => Nat.zero
    | cons a as => match n with
      | zero => a
      | succ n => lookup n as

def eval (expr : Arith) (assignment : List Nat) : Nat :=
  match expr with
    | const n => n
    | var n => lookup n assignment
    | plus a b => (eval a assignment) + (eval b assignment)
    | times a b => (eval a assignment) * (eval b assignment)



end Arith
end Hidden