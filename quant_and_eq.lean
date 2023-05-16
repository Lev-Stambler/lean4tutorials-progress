open Classical
variable (α : Type) (p q : α → Prop)

-- ## 1: Prove equivalences
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := Iff.intro
  (fun h : ∀ x, p x ∧ q x => 
    ⟨fun y : α => (h y).left, fun y : α => (h y).right⟩  
  )
  (fun h : (∀x, p x) ∧ (∀ x, q x) =>   
    fun y : α => 
      ⟨h.left y, h.right y⟩   
  )

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
  fun hpq: ∀ x, p x → q x =>
    fun hp => fun y : α  => (hpq y) (hp y)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
    fun y : α =>  
      Or.elim h (fun hp: ∀x, p x => Or.inl (hp y)) 
        (fun hq: ∀x, q x => Or.inr (hq y))

-- ## 2
-- It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic):
variable (r : Prop)

theorem aaa : α → ((∀ x : α, r) ↔ r) := 
  (fun x  =>
    Iff.intro 
      (fun h : ∀ _ : α, r =>
        h x 
      ) 
      (fun h : r =>
        fun _ : α => h
      )
  )

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := Iff.intro
  (fun h : ∀ x, p x ∨ r => 
    show (∀ x, p x) ∨ r from  
    byCases
      (fun hr : r  => Or.inr hr)
      (fun hnr : ¬r =>
      	sorry -- :((
        -- Or.inl (fun x => Or.resolve_left (h x) hnr)
      )
  )
  (fun h : (∀ x, p x) ∨ r => 
    Or.elim h (fun h : ∀ x, p x => fun x => Or.inl (h x))
      (fun r => fun x => Or.inr r)
  ) 

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := Iff.intro
  (fun h : ∀ x, r → p x => 
    fun hr : r => fun y => (h y) hr
  )
  (fun h : r → ∀ x, p x => 
    fun x => fun hr : r => h hr x 
  )

-- ## 3
-- Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction:
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry

-- ## 4
-- Remember that, without any parameters, an expression of type Prop is just an assertion. Fill in the definitions of prime and Fermat_prime below, and construct each of the given assertions. For example, you can say that there are infinitely many primes by asserting that for every natural number n, there is a prime number greater than n. Goldbach's weak conjecture states that every odd number greater than 5 is the sum of three primes. Look up the definition of a Fermat prime or any of the other statements, if necessary.
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry

-- ## 5
-- Prove as many of the identities listed in the Existential Quantifier section as you can.

