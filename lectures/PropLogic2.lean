/-
Algebra and logic 

- = -> ↔ 
- + -> ∨
- * -> ∧

- x+y = y+x Comutativity
- x+(y+z) = (x+y)+z Associativity
- x*(y+z) = (x*y)+(x*z) Distributivity
-/

variables P Q R : Prop

lemma lem : P ∧ Q → Q ∧ P :=
begin
  assume pq,
  cases pq with p q,
  constructor,
  assumption,
  assumption,
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  constructor,
  apply lem,
  apply lem,
end

-- Proving Distributivity

example : P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R :=
begin
  -- prove from left to right 
  constructor, 
  assume pqr,
  cases pqr with p qr,
  cases qr with q r,
  left,
  constructor,
  assumption,
  assumption,
  right,
  constructor,
  assumption,
  assumption,
  -- prove right to left
  assume pqpr,
  cases pqpr with pq pr,
  cases pq with p q,
  constructor,
  exact p,
  left,
  exact q,
  cases pr with p r,
  constructor,
  exact p,
  right,
  exact r,
end

/-

- ^ = →   P^Q = Q → P
- x^(y+z) = (x^y)(x^z)
- x^(y*z) = (x^y)^z

-/

-- proving line 67

example : (P ∧ Q) → R ↔ P → Q → R :=
begin
  sorry, -- apply currry as this is the same 
end

-- x^(y+z) = (x^y)*(x^z)

theorem index : P ∨ Q → R ↔ (P → R) ∧ (Q → R) :=
begin
  constructor,
  -- solve left to right
  assume pqr,
  constructor, -- split disjunction
  assume p,
  apply pqr,
  left,
  exact p,
  assume q,
  apply pqr,
  right,
  exact q,

  -- solve right to left
  assume prqr,
  cases prqr with pr qr,
  assume pq,
  cases pq with p q,
  apply pr,
  exact p,
  apply qr,
  exact q,
end

