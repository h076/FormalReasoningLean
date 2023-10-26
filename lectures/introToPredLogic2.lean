variables P Q R : Prop
variables A B C : Type
variables PP QQ : A → Prop 
variable RR : A → B → Prop

/-
(∀ x : A , PP x) ∨ (∀ x : A, QQ x) → (∀ x : A , PP x ∨ QQ x) - tautalogy 
-/

-- ∃ is like conjunction 

example : (∃ x : A, PP x) → (∀ x : A , PP x → QQ x) → ∃ x : A , QQ x :=
begin
  assume pp ppqq,
  cases pp with a pa,
  existsi a,
  apply ppqq,
  exact pa,
end 

/- 
To prove an exterstential we must have a witness,
we derive our witness from existsi a : A 
now it is enough to prove PP a using our witness

to use h : ∃ x : A , PP x we say,
cases h with a ppa,
we have two assumptions:
a : A
ppa : PP a
-/

example : (∃ x : A , PP x ∨ QQ x) ↔ (∃ x : A , PP x) ∨ (∃ x : A, QQ x) :=
begin
  constructor,
  assume h,
  cases h with a ppqqa,
  cases ppqqa with ppa qqa,
  left,
  existsi a,
  apply ppa,
  right,
  existsi a,
  apply qqa,

  assume h,
  cases h with pp qq,
  cases pp with a ppa,
  existsi a,
  left,
  apply ppa,
  cases qq with a qqa,
  existsi a,
  right,
  apply qqa,
end 

/-
a b : A
a = b : Prop

= : A → A → Prop

how to prove an eqaulity ?
how to use an assumed equalty ?
-/

example : ∀ x : A, x = x :=
begin 
  assume a,
  reflexivity, -- to prove an equality
end 

example : ∀ x y : A, x = y → PP y → PP x :=
begin 
  assume a b,
  assume ab ppa,
  rewrite ab,
  assumption,
end 

example : ∀ x y : A, x = y → PP x → PP y :=
begin 
  assume a b,
  assume ab ppa,
  rewrite← ab, --←
  assumption,
end 

-- equality is symetric 

example : ∀ x y : A, x = y → y = x :=
begin
  assume a b ab,
  rewrite ab,
  -- automatically applies reflexivity
end

example : ∀ x y z : A, x = y → y = z → x = z :=
begin
  assume a b c ab bc,
  rewrite← bc,
  assumption,
end

-- eqaulity is reflexive, symmetric and transitive 
-- equivelance relation