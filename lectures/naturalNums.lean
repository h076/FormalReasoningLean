/-
 Natural numbers

 \ bn ℕ = {0,1,2,3,4,5,....}

 Guiseppe Peano
 peano arithmetic 189x
-/

namespace l10
set_option pp.structure_projections false
open nat

/-
bools

tt ≠ ff
∀ x : bool, x=ff ∨ x=tt

P : bool → Prop
P ff → P tt → ∀ x : bool, P x  
-/

/-
inductive ℕ : Type
| zero : ℕ
| succ : ℕ → ℕ

∀ n : ℕ , zero ≠ succ n
-/

example : ∀ n : ℕ , zero ≠ succ n :=
begin
  assume n h,
  contradiction,
end

def pred : ℕ → ℕ
| zero := zero
| (succ m) := m 

-- succ is injective 
example : ∀ m n : ℕ , succ m = succ n → m = n :=
begin
  assume m n h,
  change pred (succ m) = n,
  rewrite h,
  dsimp [pred],
  refl,
end

example : ∀ m n : ℕ , succ m = succ n → m = n :=
begin
  assume m n h,
  injection h,
end

variable P : ℕ → Prop

-- induction
example : P zero → (∀ n : ℕ, P n → P (succ n)) → ∀ i : ℕ , P i :=   
begin
  assume p0 ps i,
  induction i with j ih,
  assumption,
  apply ps,
  assumption,
end

def double : ℕ → ℕ
| zero := zero
| (succ m) := succ (succ (double m))
-- double 3 = double (succ 2) = succ ( succ (double 2)) = succ (succ 4) = 6 
#eval (double 7)

def half : ℕ → ℕ 
| zero := zero
| (succ zero) := zero
| (succ (succ m)) := succ (half m)
-- half 3 = half (succ (succ 1)) = succ (half 1) = succ 0 = 1
#eval (half 876654)

example : ∀ n : ℕ, half (double n) = n :=
begin
  assume n,
  induction n with n' ih, -- to prove for 0 and succ
  dsimp [half, double],
  refl,
  dsimp [double],
  dsimp [half],
  rewrite ih, -- rewrite for induction hypothesis 
end


end l10