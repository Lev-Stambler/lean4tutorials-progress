instance : Inhabited (List a) where
  default := []

def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check foo
#eval foo.add 10 20
#check @inferInstance
-- {α : Sort u} → [α] → α

#check (inferInstance : Add Nat)