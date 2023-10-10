--An intro to propositional logic in lean

variables P Q R : Prop 

#check P → Q

-- → = \ to

#check P ∧ Q

-- ∧ = \ and

#check P ∨ Q

-- ∨ = \ or

#check ¬P

-- ¬ = \ neg

#check P ↔ Q

-- ↔ = \ iff

-- theorem used to define a prop 

theorem I : P → P :=
begin
  assume h,
  exact h,
end

-- We Prove an implication by assuming the left

theorem C : (P → Q) → (Q → R) → (P → R) :=
begin
  assume pq qr p,
  apply qr,
  apply pq,
  exact p,
end

-- Lean stores theorems as trees