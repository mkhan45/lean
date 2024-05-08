import «Idk»

/- def sumRangeClosed (start : Nat) (end' : Nat) : Nat := -/
/-   ((start + end') / 2) * (end' - start + 1) -/

/- def sumRange (start : Nat) (end' : Nat) : Nat := -/
/-     if start >= end' then 0 -/
/-     else sumRange (start + 1) end' -/
/- termination_by (end' - start) -/

/- theorem sumRangeEq (start : Nat) (end' : Nat) -/
/-   : sumRange start end' = sumRangeClosed start end' := -/
/-   sorry -/

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro 
    (λ p_and_q => And.intro p_and_q.right p_and_q.left)
    (λ q_and_p => And.intro q_and_p.right q_and_p.left)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (show p ∨ q → q ∨ p
     from λ p_or_q ↦
      Or.elim p_or_q (λ p => Or.inr p) (λ q => Or.inl q))
    (show q ∨ p → p ∨ q
     from λ q_or_p ↦
      Or.elim q_or_p (λ q => Or.inr q) (λ p => Or.inl p))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro 
    (show (p ∧ q) ∧ r → (p ∧ (q ∧ r))
     from λ pqr ↦ 
      let ⟨ ⟨p, q⟩, r ⟩ := pqr
      And.intro p (And.intro q r))
    (show (p ∧ (q ∧ r)) → (p ∧ q) ∧ r
     from λ pqr ↦
      let ⟨ p, ⟨ q, r ⟩ ⟩ := pqr
      And.intro (And.intro p q) r)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry


def main : IO Unit :=
  IO.println "Hello world"
  /- let start := 1 -/
  /- let end' := 100 -/
  /- let sum1 := sumRangeClosed start end' -/
  /- let sum2 := sumRange start end' -/
  /- IO.println s!"Sum of range [{start}variables lean, {end'}] (closed) is {sum1}, and (recursive) is {sum2}" -/
