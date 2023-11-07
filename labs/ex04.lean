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
/-
If you get an error update your lean or use:
local notation x && y := band x y 
local notation x || y := bor x y
-/


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

-- theorem ch01 : ? Ch01 :=

-- theorem ch02 : ? Ch02 :=

-- theorem ch03 : ? Ch03 :=

-- theorem ch04 : ? Ch04 :=

-- theorem ch05 : ? Ch05 :=

-- theorem ch06 : ? Ch06 :=

-- theorem ch07 : ? Ch07 :=

-- theorem ch08 : ? Ch08 :=

-- theorem ch09 : ? Ch09 :=

-- theorem ch10 : ? Ch10 :=


/- 
PART II (40%)
=============

a) Show the correctness of or:
-/
theorem orb_ok : ∀ x y : bool, is_tt x ∨ is_tt y ↔ is_tt (x || y) :=
begin
  sorry,
end
/-
b) Define an operation 
-/
def exb  (f : bool → bool) : bool
    := sorry

/-
here you can use boolean operations 
which have been defined already.

Prove that it computes existential quantification:
-/
theorem exb_ok : ∀ f : bool → bool, is_tt (exb f) ↔ ∃ x : bool, is_tt (f x) :=
begin
  sorry,
end
/-
(*) the exb part is difficult, you only loose 20% if you don't do it.
-/


/- --- Do not add/change anything below this line --- -/
end ex04
