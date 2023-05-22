variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := Iff.intro
  (fun h : p ∧ q => 
    show q ∧ p from ⟨h.right, h.left⟩
  )
  (fun h : q ∧ p => 
    show p ∧ q from ⟨h.right, h.left⟩
  )

example : p ∨ q ↔ q ∨ p := Iff.intro
  (fun h : p ∨ q => 
    Or.elim h (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq)
  )
  (fun h : q ∨ p => 
    Or.elim h (fun hq : q => Or.inr hq) (fun hp : p => Or.inl hp)
  )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := Iff.intro
  (fun h =>
    show p ∧ (q ∧ r) from ⟨h.left.left, ⟨h.left.right, h.right⟩⟩
  )
  (fun h =>
    show (p ∧ q) ∧ r from ⟨⟨h.left, h.right.left⟩, h.right.right⟩
  )
  
-- example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := Iff.intro

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := Iff.intro
  (fun h : p ∧ (q ∨ r) =>
    Or.elim h.right (fun hq : q => Or.inl ⟨h.left, hq⟩) (fun hr : r => Or.inr ⟨h.left, hr⟩)
  )
  (fun h =>
    Or.elim h (fun hpq : p ∧ q => ⟨hpq.left, Or.inl hpq.right⟩) (fun hpr : p ∧ r => ⟨hpr.left, Or.inr hpr.right⟩)
  )
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := Iff.intro
  (fun h : p ∨ (q ∧ r) =>  
    Or.elim h (fun hp : p => ⟨Or.inl hp, Or.inl hp⟩) (fun hqr : q ∧ r => ⟨Or.inr hqr.left, Or.inr hqr.right⟩)   
  )
  (fun h : (p ∨ q) ∧ (p ∨ r) =>
    Or.elim h.left (fun hp : p => Or.inl hp)
      (fun hq : q => Or.elim h.right
        (fun hp : p => Or.inl hp)
        (fun hr : r => Or.inr ⟨hq, hr⟩) 
      )
  )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := Iff.intro
  (fun h : (p → (q → r)) => 
    (fun hpq : p ∧ q => 
      show r from h hpq.left hpq.right)
  )
  (fun h : (p ∧ q → r) =>
    (fun hp : p => fun hq : q => show r from h ⟨hp, hq⟩)
  )

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    sorry

  . intro ⟨hp, hq⟩
    intro pOrQ
    exact (Or.elim pOrQ (fun hpp => hp hpp) (fun hqq => hq hqq))
    
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := Iff.intro
  (fun h : p ∨ q → False  =>
    ⟨fun hp : p => show False from h (Or.inl hp),
     fun hq => show False from h (Or.inr hq)⟩ 
  )
  (fun h : ¬p ∧ ¬q =>
    fun pq : p ∨ q => 
      Or.elim pq (fun hp => h.left hp) (fun hq => h.right hq)
  )   

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (fun npnq : ¬p ∨ ¬q =>
    fun pq : p ∧ q => 
      Or.elim npnq (fun np => np pq.left) (fun nq => nq pq.right)
  )

example : ¬(p ∧ ¬p) := fun h : p ∧ ¬p  => absurd h.left h.right

example : p ∧ ¬q → ¬(p → q) := 
  (fun hpnq : p ∧ ¬q => 
    fun hpImpQ : p → q => 
      show False from hpnq.right (hpImpQ hpnq.left)
  )

example : ¬p → (p → q) := fun hnp : ¬p => fun p => absurd p hnp

example : (¬p ∨ q) → (p → q) := by
  intros h hp
  exact Or.elim h (fun hpp : ¬p => absurd hp hpp) (fun hq => hq)

example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . intro hp; assumption
    . intro hf
      contradiction
  . intro hp
    exact Or.inl hp

example : p ∧ False ↔ False := by
  apply Iff.intro
  . intro ⟨_hp, hfalse⟩
    exact hfalse  
  . intro hfalse
    exact ⟨(by contradiction), hfalse⟩ 

example : (p → q) → (¬q → ¬p) := by
  intros hpq hNq
  intro hp
  exact absurd (hpq hp) hNq
