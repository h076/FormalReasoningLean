-- lecture 8


set_option pp.structure_projections false

variables P Q R : Prop
variables A B C : Type
variables PP QQ : A → Prop
variable RR : A → A → Prop 

open classical

theorem efq : false → P :=
begin
  assume f,
  cases f,
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

/-
There are predcicate logic counterparts of de morgans law which now say
that you can move negation through a quantifier by negating the component and switching the quantifier
-/

-- proving this intuitionistically

theorem dm1_pred : ¬ (∃ x : A, PP x) ↔ ∀ x : A, ¬ PP x :=
begin
  constructor,
  -- left to right
  assume h x p,
  apply h,
  existsi x,
  exact p,
  -- right to left
  assume h p,
  cases p with a pa,
  apply h,
  exact pa,
end

-- proving this classicaly

theorem dm2_pred : ¬ (∀ x : A, PP x) ↔ ∃ x : A, ¬ PP x :=
begin
  constructor,
  -- left to right
  assume h,
  apply raa, -- goal is now double negation
  assume ne,
  apply h,
  assume a,
  apply raa,
  assume np,
  apply ne,
  existsi a,
  exact np,
  -- right to left
  assume h na,
  cases h with a np,
  apply np,
  apply na,
end

/-
  Bool in lean 

  defined as ...

  inductive bool : Type
| tt := ff
| ff := tt

  can use bool to define functions

  def band : bool → bool :=
  | tt b := b
  | ff b := ff

  infix notation can be written as 
  x && y := band x y
-/

variable x : bool

#reduce band tt x
#reduce bor tt x

-- using pred logic to prove basic bool properties

example : ∀ x : bool, x = tt ∨ x = ff :=
begin
  assume x,
  cases x,
  right,
  refl,
  left,
  refl,
end

def is_tt : bool → Prop
| tt := true
| ff := false

theorem cons : tt ≠ ff :=
begin
  assume h,
  change is_tt ff,
  rewrite← h,
  trivial,
end

-- could have solved above with contradiction

-- proving distributivity with bools

theorem distr_b : ∀ x y z : bool, x && (y || z) = x && y || x && z :=
begin
  sorry,
end

theorem dm1_b : ∀ x y : bool, bnot (x || y) = bnot x && bnot y :=
begin
  assume x y,
  cases x,
  cases y,
  dsimp [bnot],
  refl,
  dsimp [bnot],
  refl,
  cases y,
  dsimp [bnot],
  refl,
  dsimp [bnot],
  refl,
end

theorem dm2_b : ∀ x y : bool, bnot (x && y) = bnot x || bnot y :=
begin
  assume x y,
  cases x,
  cases y,
  dsimp [bnot],
  refl,
  dsimp [bnot],
  refl,
  cases y,
  dsimp [bnot],
  refl,
  dsimp [bnot],
  refl,
end

-- can use is_tt to relate ∧ and &&

theorem and_thm : ∀ x y : bool, is_tt x ∧ is_tt y ↔ is_tt (x && y) :=
begin
  assume x y,
  constructor,
  assume h,
  cases h with xtt ytt,
  cases x,
  cases xtt,
  cases y,
  cases ytt,
  constructor,

  assume h,
  cases x,
  cases h,
  cases y,
  cases h,
  constructor,
  constructor,
  constructor,
end

theorem not_thm : ∀ x : bool, ¬ (is_tt x) ↔ is_tt (bnot x) :=
begin
  assume x,
  constructor,
  assume nh,
  cases x,
  dsimp [bnot],
  constructor,
  dsimp [bnot],
  sorry,
end

theorem or_thm : ∀ x y : bool, is_tt x ∨ is_tt y ↔ is_tt (x || y) :=
begin
  sorry,
end