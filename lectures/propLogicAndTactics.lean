
-- Tactics are what we use within proofs
-- assume x : to prove an implication
-- apply x : to use an assumed implication
-- exact x : to use an assumption as it is

-- proofs are stored as functional programs
-- props are types

variables P Q R : Prop

theorem swap : (P → Q → R) → (Q → P → R) :=
begin
  assume pqr q p,
  apply pqr,
  exact p,
  exact q,
end

-- line 15 gave us two subgoals P and Q

-- Conjunction

example : P → Q → P ∧ Q :=
begin
  assume p q,
  constructor,
  exact p,
  exact q,
end

-- constructor splits conjunction into two subgoals

example : P ∧ Q → P :=
begin
  assume h,
  cases h with p q,
  exact p,
end

-- cases allows us to split an assumption into two seperate ones

theorem curry : (P → Q → R) ↔ (P ∧ Q → R) :=
begin
  constructor, -- split the equivelance
  assume pqr pq,
  cases pq with p q,
  apply pqr,
  exact p,
  exact q,

  assume pqr p q,
  apply pqr,
  constructor,
  exact p,
  exact q,
end

-- Disjunction 
-- we use cases to split the disjunction

example : P → P ∨ Q :=
begin
  assume p,
  left, -- sets goal of the disjunction to the left side, can use right
  exact p,
end

example : (P → R) → (Q → R) → P ∨ Q → R :=
begin
  assume pr qr pq,
  cases pq with p q,
  apply pr,
  exact p,
  apply qr,
  exact q,
end

-- constants

-- like an empty disjunction

example : false → P :=
begin
  assume pigs_can_fly,
  cases pigs_can_fly,
end

-- like an empty conjunction

example : true :=
begin
  constructor,
end