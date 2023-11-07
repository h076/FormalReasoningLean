
/-
Primitive/Structural recursion is the only type of recursion that is used in lean
- its answer is derived from the previous result

Induction is used when solving primitive recursion,
giving cases 0 and n', n' being the continuation of recursion

-/

namespace l11
set_option pp.structure_projections false
open nat

/- 

Addition in lean

-/

def add : ℕ → ℕ → ℕ 
| n zero := n
| n (succ m) := succ (add n m) -- pattern matching on the second argument

local notation (name := add) m + n := add m n

def mult : ℕ → ℕ → ℕ
| n zero := zero
| n (succ m) := add (mult n m) n

#eval mult 3 5

local notation (name := mult) m * n := mult m n

-- Algebra

theorem lneutr : ∀ n : ℕ, 0 + n = n :=
begin
  assume n,
  induction n with n' ih,
  refl,
  dsimp [(+),add],
  rewrite ih,
end 

theorem rneutr : ∀ n : ℕ, n + 0 = n :=
begin
  assume n,
  dsimp [(+),add],
  refl,
end

-- associativity
theorem assoc : ∀ l m n : ℕ, (l + m) + n = l + (m + n) := 
begin
  assume l m n,
  induction n with n' ih,
  refl,
  dsimp [(+),add],
  rewrite ih,
end

-- lneutr+rneutr+assoc = monoid

lemma add_succ : ∀ m n : ℕ,
  (succ m) + n = succ (m + n) :=
begin
  assume m n,
  induction n with n' ih,
  refl,
  dsimp [(+),add],
  rewrite ih,
end

-- commutativity
theorem comm : ∀ m n : ℕ, m + n = n + m :=
begin
  assume m n,
  induction n with n' ih,
  dsimp [(+),add],
  rewrite lneutr,
  dsimp [(+),add],
  rewrite add_succ,
  rewrite ih,
end 

-- monoid+comm = commutative monoid


end l11