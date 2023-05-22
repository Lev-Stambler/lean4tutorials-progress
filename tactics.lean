-- 1. Go back to the exercises in Chapter Propositions and Proofs and Chapter Quantifiers and Equality and redo as many as you can now with tactic proofs, using also rw and simp as appropriate.
  
-- 2. Use tactic combinators to obtain a one line proof of the following:
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat(apply And.intro)

  -- exact ⟨(apply Or.inl; assumption),  repeat(apply Or.inl); assumption, apply Or.inr; apply Or.inr; assumption⟩