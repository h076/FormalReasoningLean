/-
COMP2065-IFR Exercise 04
(Booleans) 

    This exercise has 2 parts.

    The first part is "logic chess" which has slightly different rules
    than logic poker but see below. The 2nd part asks you to prove that
    orb on booleans corresponds to the logical or and define an operation
    to compute existential quantification on booleans and prove it correct. 

    Don't worry, if you can't do the existential quantification part. 
    This is intended as a challenge and only counts for 20% of the 
    exercise. 
-/

namespace ex04
def bnot : bool → bool 
| tt := ff
| ff := tt 

def band : bool → bool → bool 
| tt b := b
| ff b := ff

def bor : bool → bool → bool 
| tt b := tt
| ff b := b

def is_tt : bool → Prop 
| tt := true
| ff := false

/- --- Do not add/change anything above this line --- -/


local notation (name := band) x && y := band x y 
local notation (name := bor) x || y := bor x y

--local notation x && y := band x y 
--local notation x || y := bor x y



prefix `!`:90 := bnot

/-
PART I (60%)
============
Logic chess

Unlike logic poker in logic chess there is no guessing. You either
prove the proposition or you prove its negation.

Consider the following examples:
-/
def Ch0 := ∀ x : bool, x=x
def Ch00 := ∀ x : bool, x ≠ x

/- the first one is provable, hence we prove it -/

theorem ch0 : Ch0 :=
begin
  assume x,
  reflexivity
end

/- the second one is false, hence we prove its negation -/

theorem ch00 : ¬ Ch00 :=
begin
  assume h,
  have g : tt ≠ tt,
  apply h,
  apply g,
  reflexivity,
end


def Ch01 := ∀ x : bool, ! x = x
def Ch02 := ∀ x:bool,∃ y:bool, x = y
def Ch03 := ∃ x:bool,∀ y:bool, x = y
def Ch04 := ∀ x y : bool, x = y → ! x = ! y
def Ch05 := ∀ x y : bool, !x = !y → x = y
def Ch06 := ∀ x y z : bool, x=y ∨ y=z 
def Ch07 := ∃ b : bool, ∀ y:bool, b || y = y 
def Ch08 := ∃ b : bool, ∀ y:bool, b || y = b
def Ch09 := ∀ x : bool, (∀ y : bool, x && y = y) ↔ x = tt 
def Ch10 := ∀ x y : bool, x && y = y ↔ x = ff

/-
Name your theorems ch01, ch02, ..., ch10. chXX should either
be a proof of ChXX or a proof of ¬ ChXX, so either delete the
? or replace it by a ¬.
-/

theorem ch01 : ¬ Ch01 :=
begin
  dsimp [Ch01],
  assume all,
  have nt : !tt = tt,
  apply all,
  dsimp [bnot] at nt,
  contradiction,
end

theorem ch02 : Ch02 :=
begin
  dsimp [Ch02],
  assume x,
  cases x,
  existsi ff,
  refl,
  existsi tt,
  refl,
end

theorem ch03 : ¬ Ch03 :=
begin
  dsimp [Ch03],
  assume all,
  cases all with b h,
  cases b,
  have hff := h tt,
  contradiction,
  have htt := h ff,
  contradiction,
end

theorem ch04 : Ch04 :=
begin
  dsimp [Ch04],
  assume x y,
  assume eq,
  cases x,
  cases y,
  refl,
  contradiction,
  cases y,
  contradiction,
  refl,
end

theorem ch05 : Ch05 :=
begin
  dsimp [Ch05],
  assume x y,
  assume neq,
  cases x,
  cases y,
  refl,
  contradiction,
  cases y,
  contradiction,
  refl,
end

theorem ch06 : ¬ Ch06 :=
begin
  dsimp [Ch06],
  assume all,
  have contra : ff = tt ∨ tt = ff,
  apply all,
  cases contra,
  contradiction,
  contradiction,
end

theorem ch07 : Ch07 :=
begin
  dsimp [Ch07],
  existsi ff,
  assume y,
  dsimp [bor],
  cases y,
  refl,
  refl,
end

theorem ch08 : Ch08 :=
begin
  dsimp [Ch08],
  existsi tt,
  assume y,
  dsimp [bor],
  cases y,
  refl,
  refl,
end

theorem ch09 : Ch09 :=
begin
  dsimp [Ch09],
  assume x,
  constructor,
  cases x,
  assume y,
  apply y tt,
  assume y,
  refl,
  cases x,
  contradiction,
  assume t,
  assume y,
  dsimp [band],
  cases y,
  refl,
  refl,
end

theorem ch10 : ¬ Ch10 :=
begin
  dsimp [Ch10],
  assume all,
  have contra : tt && ff = ff ↔ tt = ff,
  apply all,
  dsimp [band] at contra,
  cases contra with lr rl,
  have h : tt = ff,
  apply lr,
  refl,
  contradiction,
end


/- 
PART II (40%)
=============

a) Show the correctness of or:
-/
theorem orb_ok : ∀ x y : bool, is_tt x ∨ is_tt y ↔ is_tt (x || y) :=
begin
  assume x y,
  cases x,
  cases y,
  dsimp [is_tt,bor],
  constructor,
  assume ff,
  cases ff,
  assumption,
  assumption,
  assume f,
  left,
  assumption,
  dsimp [is_tt,bor],
  constructor,
  assume ft,
  cases ft,
  contradiction,
  assumption,
  assume t,
  right,
  assumption,
  cases y,
  dsimp [is_tt,bor],
  constructor,
  assume tf,
  cases tf,
  assumption,
  contradiction,
  assume t,
  left,
  assumption,
  dsimp [is_tt,bor],
  constructor,
  assume tt,
  cases tt,
  assumption,
  assumption,
  assume t,
  left,
  assumption,
end
/-
b) Define an operation 
-/
def exb  (f : bool → bool) : bool
    := (f tt) || (f ff)

/-
here you can use boolean operations 
which have been defined already.

Prove that it computes existential quantification:
-/
theorem exb_ok : ∀ f : bool → bool, is_tt (exb f) ↔ ∃ x : bool, is_tt (f x) :=
begin
  assume f,
  dsimp [exb],
  have lem : is_tt (f tt) ∨ is_tt (f ff) ↔ ∃ x : bool, is_tt (f x),
  constructor,
  assume tf,
  cases tf with t f,
  existsi tt,
  assumption,
  existsi ff,
  assumption,
  assume e,
  cases e with b isb,
  cases b,
  right,
  assumption,
  left,
  assumption,

  rewrite<- lem,
  symmetry,
  apply orb_ok,
end
/-
(*) the exb part is difficult, you only loose 20% if you don't do it.
-/


/- --- Do not add/change anything below this line --- -/
end ex04
