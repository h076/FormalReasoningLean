variables P Q R : Prop

/-

Predicate Logic

Types (sets)

types are static, sets are more dynamic -- basically same

-/

#check bool -- this is a type, as a set it would be {true, false}
#check ℕ -- {0,1,2,...}
#check list ℕ 
#check ℕ → bool -- functions and implication in lean are the same

variables A B C : Type

/- Prediactes and relations -/

/-
Even : ℕ → Prop
Even 2
Even 3

Prime : ℕ → Prop
-- relations n-ary prediactes

≤ : ℕ → ℕ → Prop

holds : Program → Prop

occurs : A → list A → Prop

occurs 1 [1,2,3] is true

= : A → A → Prop
-- equality, part of predicate logic

-/

variables PP QQ : A → Prop 
variable RR : A → B → Prop 

/- Quantifiers: ∀ (\ forall), ∃ (\ ex) -/

-- A = Students, PP x = x is clever

#check ∀ x : A , PP x
-- all are clever
#check ∃ x : A , PP x 
-- there is clever student

#check ∀ x : A , PP x ∧ Q  

#check ∀ x : A , PP x ∧ ∃ x : A, QQ x
-- this is shadowing

#check ∀ x : A , PP x ∧ ∃ y : A, QQ y
-- avoids shadowing

-- how to prove ∀ 
example : (∀ x : A, PP x) → (∀ x : A , PP x → QQ x) → ∀ x : A , QQ x :=
begin
  assume pp ppqq,
  assume harry,
  apply ppqq,
  apply pp,
end 

/-
to prove ∀ x : A , PP x
we assume a,
we then add an assumption a : A
an it remains to show PP a.
if we know 
h : ∀ x : A , PP x → QQ x
and we have to prove QQ a then we say apply h 
and it remains to show PP a
if we know 
h : ∀ x : A, PP x
we want to show PP a 
-/

example : (∀ x : A , PP x ∧ QQ x) ↔ (∀ x : A , PP x) ∧ (∀ x : A, QQ x) :=
begin
  constructor,
  assume h, 
  constructor,
  assume a,
  have stone : PP a ∧ QQ a,
  apply h,
  cases stone with pa qa,
  exact pa,
  assume a,
  have stone : PP a ∧ QQ a,
  apply h,
  cases stone with pa qa,
  exact qa,

  -- now prove other direction
  assume h, 
  cases h with ppx qqx,
  assume a,
  constructor,
  apply ppx,
  apply qqx,
end