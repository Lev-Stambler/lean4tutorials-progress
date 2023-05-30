/-
1. Open a namespace Hidden to avoid naming conflicts, and use the equation compiler to define addition, multiplication, and exponentiation on the natural numbers. Then use the equation compiler to derive some of their basic properties.
-/
namespace Hidden
  def add : Nat → Nat → Nat
  | 0, b => b
  | a + 1, b => add a b

  def mul : Nat → Nat → Nat  
  | 0, _ => 0
  | 1, b => b
  | a + 1, b => b + (mul a b)

  def exp : Nat → Nat → Nat  
  | 0, _ => 1
  | a + 1, b => mul b (exp a b)

end Hidden

/-
4. Following the examples in Section Dependent Pattern Matching, define a function that will append two vectors. This is tricky; you will have to define an auxiliary function.
-/
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

def append {α : Type u} : {n₁ : Nat} → Vector α n₁ → {n₂ : Nat} → Vector α n₂ → Vector α (n₂ + n₁)
  | 0, nil, _, v₂ => v₂
  | n₁ + 1, cons a v₁, _, v₂ => cons a (append v₁ v₂)
-- TODO: where is aux funciton?
end Vector

/-
  5. Consider the following type of arithmetic expressions. The idea is that var n is a variable, vₙ, and const n is the constant whose value is n.
-/
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => (eval v e₁) + (eval v e₂)
  | times e₁ e₂ => (eval v e₁) * (eval v e₂)

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
#eval eval sampleVal sampleExpr

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr := (fun e => match e with
  | plus (const _) (const _)  => simpConst e
  | times (const _) (const _) => simpConst e
  | plus (e₁ : Expr) (e₂ : Expr) => plus (fuse e₁) (fuse e₂)
  | times e₁ e₂ => times (fuse e₁) (fuse e₂)
  | e => e
)

#check Expr.noConfusion

theorem simpConst_eq_exp (v : Nat → Nat) : ∀ e₁ e₂ : Expr, e₁ = e₂ → eval v e₁ = eval v e₂ := by
  intro e₁ e₂ h
  rw [h]

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e := by
    intro e 
    -- apply simpConst_eq_exp
    -- simp [simpConst]
    unfold simpConst
    split <;> rfl

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e := by
    intro e 
    -- apply simpConst_eq_exp
    unfold fuse
    split
    . rfl
    . rfl
    . rename_i e₁ e₂ h
      simp [eval]
      rw [fuse_eq v e₁]
      rw [fuse_eq v e₂]
    . rename_i e₁ e₂ h
      simp [eval]
      rw [fuse_eq v e₁]
      rw [fuse_eq v e₂]
    . rfl
