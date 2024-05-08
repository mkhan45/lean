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

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (show (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) 
     from λ h ↦ And.intro 
      (show ∀ x, p x from λ a ↦ (h a).left)
      (show ∀ x, q x from λ a ↦ (h a).right))
    (show ((∀ x, p x) ∧ (∀ x, q x)) → (∀ x, p x ∧ q x)
     from λ ⟨ p, q ⟩ ↦ λ a ↦ And.intro (p a) (q a))

example : (∀ x, p x → q x) → ((∀ x, p x) → (∀ x, q x)) :=
  λ h1 h2 ↦ λ x ↦
    have h1x : p x → q x := h1 x
    have px : p x := h2 x
    h1x px

-- better with tactics?
-- i dont understand what to info pane is showing me
-- i think tactics are worse here
example : (∀ x, p x → q x) → ((∀ x, p x) → (∀ x, q x)) := by
  intros h1 h2 x
  apply h1 x
  apply h2

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ disjunct ↦ Or.elim disjunct
    (λ (apx : ∀ x, p x) x ↦ Or.inl (apx x))
    (λ (aqx : ∀ x, q x) x ↦ Or.inr (aqx x))

-- still worse with tactics imo
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  apply Or.elim h
  case left => intro apx; apply Or.inl (apx x)
  case right => intro aqx; apply Or.inr (aqx x)

def BoundedInt (low : Int) (high : Int) : Type :=
  { n : Int // low <= n ∧ n <= high }

instance : LT (BoundedInt low high) where
  lt a b := a.val < b.val

-- idk how this works
instance (a b : BoundedInt l h) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.val < b.val))

/- instance : GT (BoundedInt low high) where -/
/-   gt a b := a.val > b.val -/

def guessingGame 
  (hp : Nat) (low : Int) (high : Int) (x : BoundedInt low high) 
  : IO Unit := do
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    if hp > 0 then
      stdout.putStrLn s!"Guess a number from {low} to {high}"
      let inp ← stdin.getLine
      match inp |> String.trim |> String.toNat? with
      | some n => 
        if n == x.val then
          stdout.putStrLn "good job"
        else if b : low <= n ∧ n <= high then 
          let boundedN : (BoundedInt low high) := ⟨ n, b ⟩
          let msg := if boundedN < x then "too low" else "too high"
          stdout.putStrLn msg
          guessingGame (hp-1) low high x
        else 
          stdout.putStrLn 
            s!"Please input a number from {low} to {high}"
      | none => 
        stdout.putStrLn "Please input a number"
        guessingGame (hp-1) low high x
    else
      stdout.putStrLn "ran out of hp"
    termination_by hp

def main : IO Unit := do
  let n : BoundedInt 0 100 := ⟨ 50, by simp ⟩
  guessingGame 100 0 100 n
  /- IO.println "Hello world" -/
  /- let start := 1 -/
  /- let end' := 100 -/
  /- let sum1 := sumRangeClosed start end' -/
  /- let sum2 := sumRange start end' -/
  /- IO.println s!"Sum of range [{start}variables lean, {end'}] (closed) is {sum1}, and (recursive) is {sum2}" -/
