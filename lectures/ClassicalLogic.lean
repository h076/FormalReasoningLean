variables P Q R : Prop

/-

Classical vs Intuitional Logic

- logic of truth (classical)
- logic of evidence (intuitional)

explaining the difference between truth and evidence using demorgans law

- ¬(P ∨ Q) ↔ ¬P ∧ ¬Q
- ¬(P ∧ Q) ↔ ¬P ∨ ¬Q

- ¬P ↔ p → false

-/

theorem efq : false → P :=
begin
  assume f,
  cases f,
end

theorem dm1 : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
begin
  sorry, -- apply index law, swap false for R when neg changed to → e.g P ∨ Q → false
end

-- must open classical libray to solve the following dm2
-- this imports an axiom called the law of excluded middle
open classical

theorem dm2 : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
begin
  constructor,
  -- solve left to right using classical axiom em
  assume npq,
  cases (em P) with p np,
  right,
  assume q,
  apply npq,
  constructor,
  exact p,
  exact q,
  left,
  exact np,

  -- solve right to left
  assume npnq,
  assume pq,
  cases pq with p q,
  cases npnq with np nq,
  apply np, -- apply not P
  exact p, -- contradict with P
  apply nq, -- apply not Q
  exact q, -- contradict with Q
end

-- dm2 uses reduction ad absurdo / indirect proof
-- we want to prove p so we assume ¬p and derive a contradiction
-- ¬P → false
-- ¬¬P

example : P ∨ ¬P :=
begin
  apply em, -- solved by law of excluded middle
end

theorem raa : ¬¬P → P :=
begin
  assume nnp,
  cases (em P) with p np, -- assume ¬P
  assumption, -- assume p
  apply efq,
  apply nnp,
  exact np,
end

theorem nnem : ¬ ¬ (P ∨ ¬P) :=
begin
  assume npnp,
  apply npnp,
  right, -- prove ¬ P
  assume p,
  apply npnp,
  left,
  exact p,
end

theorem em' : P ∨ ¬P :=
begin
  apply raa,
  apply nnem,
end

-- em → raa → em