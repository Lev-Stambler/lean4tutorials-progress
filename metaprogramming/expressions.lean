 import Lean
 open Nat
 open Lean
 /-
	Create expression 1 + 2 with Expr.app.
	Create expression 1 + 2 with Lean.mkAppN.
	Create expression fun x => 1 + x.
	[De Bruijn Indexes] Create expression fun a, fun b, fun c, (b * a) + c.
	Create expression fun x y => x + y.
	Create expression fun x, String.append "hello, " x.
	Create expression ∀ x : Prop, x ∧ x.
	Create expression Nat → String.
	Create expression fun (p : Prop) => (λ hP : p => hP).
	[Universe levels] Create expression Type 6.
 -/

set_option pp.universes true in
#check @List.map

-- Refers to some constant: `. `` Refers to some constant but fully qualifies
def add_1_2 := mkAppN (.const ``Nat.add [levelOne]) #[
  (Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])),
  (Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])) 
]

-- 3
def add_1 := Expr.lam `x (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[
  .const `x [], 
  (Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero []))
])

-- 4
-- TODO: not quite gotten
def debrujn := Expr.lam `a (.const ``Nat []) (
  Expr.lam `b _ (
    Expr.lam `c _ (mkAppN (.const ``Nat.add []) #[
      (mkAppN (.const ``Nat.add []) #[#1, #2]), #0
    ])
  )
)

-- 7
-- Create expression ∀ x : Prop, x ∧ x.
def forallhabib := Expr.forallE `x (.sort .zero) (mkAppN (.const ``And []) #[(.const `x []), (.const `x [])]) BinderInfo.default
#check forallhabib
#eval forallhabib

