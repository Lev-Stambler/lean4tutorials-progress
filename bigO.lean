import Mathlib 

inductive BigO where
| base : BigO
| recurse : BigO → BigO

namespace BigO

-- def nLin : Nat → BigO
--   | 0 => base
--   | n + 1 => recurse (nLin n)

def is_square (f : Nat → Nat) :=
  ∃ c b : Nat, ∀ n :Nat, (n ≥ b → f n ≤ c * n * n)

def lin_it : Nat → Nat × Nat 
  | 0 => (0, 0)
  | n + 1 => ((lin_it n).1 + 1, (lin_it n).2 + 1)

def square_it : Nat → Nat × Nat
  | 0 => (0, 0) 
  | n + 1 =>
  let (a, b) := lin_it (n + 1)
  let (c, d) := square_it n
  (a + c, b + d)

theorem square_it_O_n : is_square (fun n: Nat => (square_it n).snd) := 
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
          linarith
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