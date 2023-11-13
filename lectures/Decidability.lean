
open nat 


/-
  equality on natural numbers is decidable 
-/

def Eq_nat : ℕ → ℕ → Prop := λ m n , m = n

def eq_nat : ℕ → ℕ → bool
| zero zero := tt
| (succ m) zero := ff
| zero (succ n) := ff
| (succ m) (succ n) := eq_nat m n -- recursion don to zero zero

-- complete, if it is true, i say yes

lemma eq_nat_compl : ∀ m : ℕ, eq_nat m m = tt := -- same as below
-- ∀ m n : ℕ , m = n → eq_nat m n = tt :=
begin
  assume m,
  induction m with m' ih,
  -- dsimp [eq_nat],
  refl,
  dsimp [eq_nat],
  assumption,
end

-- sound, if i say yes it is true

lemma eq_nat_sound : ∀ m n : ℕ, eq_nat m n = tt → m = n :=
begin
  assume m,
  induction m with m' ih,
  assume n h,
  cases n with n',
  refl,
  dsimp [eq_nat] at h,
  -- only allowed to say contradiction when we have ff=tt
  contradiction,

  assume n h,
  cases n with n',
  contradiction,
  dsimp [eq_nat] at h,
  apply congr_arg succ,
  apply ih,
  assumption,
end

theorem eq_nat_ok : ∀ m n : ℕ , m = n ↔ eq_nat m n = tt :=
begin
  assume m n,
  constructor,
  assume h,
  rewrite h,
  apply eq_nat_compl,
  apply eq_nat_sound,
end

-- eq_nat decides Eq_nat, ie the equality.
-- equality on natural numbers is decidable

/-
A predicate PP : A → Prop is decidable
if there is a function p : A → bool such that
∀ a : A, PP a ↔ p a = tt

Prime : ℕ → Prop is decidable 
≤ : ℕ → ℕ → Prop is decidable

Halt : Program → Prop
Halt p = program will stops

-/

def Tricky (f : ℕ → bool) : Prop := ∀ n : ℕ, f n = tt
-- not decidable