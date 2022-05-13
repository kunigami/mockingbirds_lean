import tactic

inductive Bird
| Call : Bird -> Bird -> Bird
open Bird

reserve infix ` ⬝ ` : 99

universes u
class has_call (α : Type u) := (call : α → α → α)
infix ⬝ := has_call.call

instance : has_call Bird := ⟨Call⟩

/-
 Problem 1: The significance of the Mockingbird
-/

def composes(a b c: Bird): Prop := ∀ x, c ⬝ x = a ⬝ (b ⬝ x)
def is_mocking(m: Bird): Prop := ∀ x, m ⬝ x = x ⬝ x
def is_fond(a b: Bird): Prop := a ⬝ b = b

theorem fondness

  -- Composition condition
  (C₁: ∀ a b: Bird, ∃ c: Bird, composes a b c)
  -- A mocking bird exists
  (C₂: ∃ m: Bird, is_mocking m)

  : ∀ a: Bird, ∃ b, is_fond a b :=
begin
  intro a,
  cases C₂ with m Hm,
  cases (C₁ a m) with c Hc,
  -- CC:  c c = a (m c)
  have CC := Hc c,
  -- bind x with c
  -- Hmc: m c = c c
  have Hmc := Hm c,
  -- replace c c = a (m c) with
  -- c c = a (c c)
  rw Hmc at CC,
  -- bind x in the goal with c c
  -- ⊢ is_fond a (c ⬝ c)
  existsi c ⬝ c,
  -- ⊢  = c ⬝ c
  rw is_fond,
  -- ⊢ c ⬝ c = a ⬝ (c ⬝ c)
  symmetry,
  exact CC,
end

/-
 Problem 2: Egocentric?
-/

def is_egocentric(a: Bird): Prop := is_fond a a

theorem egocentric_exists

  -- Composition condition
  (C₁: ∀ a b: Bird, ∃ c: Bird, composes a b c)
  -- A mocking bird exists
  (C₂: ∃ m: Bird, is_mocking m)

  : ∃ x, is_egocentric x :=
begin
  cases C₂ with m Hm,
  cases (C₁ m m) with c Hc,
  have Hcc := Hc c,
  repeat {rw Hm at Hcc},
  existsi c ⬝ c,
  rw is_egocentric,
  rw is_fond,
  symmetry,
  exact Hcc,
end

/-
 Problem 3: Story of the Agrreable Bird
-/

def is_agreeable(a: Bird): Prop := ∀ b: Bird, ∃ x: Bird, a ⬝ x = b ⬝ x

theorem fondness_with_aggreable

  -- Composition condition
  (C₁: ∀ a b: Bird, ∃ c: Bird, composes a b c)
  -- A aggreable bird exists
  (C₂: ∃ a: Bird, is_agreeable a)

  : ∀ a: Bird, ∃ b, is_fond a b :=

begin
  intro a,
  cases C₂ with g Hg,
  rw is_agreeable at Hg,
  cases (C₁ a g) with c Hc,
  have Hgc := Hg c,
  cases Hgc with x₁ Hgcx,
  have Hcx := Hc x₁,
  rw Hgcx at Hcx,

  existsi c ⬝ x₁,
  rw is_fond,
  symmetry,
  exact Hcx,
end

/-
 Problem 4: A Question on Aggreable Birds

 This is not an easy one.
-/

theorem aggreableness (a b c: Bird)
  -- Composition condition
  (C₁: ∀ a₁ b₁: Bird, ∃ c₁: Bird, composes a₁ b₁ c₁)
  -- a b c particular instance
  (C₂: composes a b c)

  : is_agreeable c → is_agreeable a

:=
begin
  intro H_c_agr,
  -- Arbitrary bird which 'a' will agree with
  intro d,
  -- This is the main gotcha: introduce variable 'e'
  -- connecting 'd' and 'b'
  cases C₁ d b with e C_e,
  cases H_c_agr e with x_e Cagr_e,
  have Ce' := C_e x_e,
  have Ce'' := C₂ x_e,
  -- We show that 'a' and 'd' agree on bird 'b x_e'
  existsi b ⬝ x_e,
  rw← Ce',
  rw← Ce'',
  exact Cagr_e,
end

/-
 Problem 5: An exercise in composition
-/
theorem composition3 (a b c: Bird)

  -- Composition condition
  (C₁: ∀ a b: Bird, ∃ c: Bird, composes a b c)

  : ∃ d: Bird, ∀ x, d ⬝ x = a ⬝ (b ⬝ (c ⬝ x))
:=
begin
  cases C₁ b c with e C_e,
  rw composes at C_e,
  cases C₁ a e with d C_d,
  rw composes at C_d,
  existsi d,
  intro x',
  rw← C_e x',
  exact C_d x',
end

/-
 Problem 6: Compatible birds
-/
def is_compatible(a b: Bird): Prop := ∃ x y: Bird, a ⬝ y = x ∧ b ⬝ x = y

theorem compatible (a b: Bird)

  -- Composition condition
  (C₁: ∀ a b: Bird, ∃ c: Bird, composes a b c)
  -- A mocking bird exists
  (C₂: ∃ m: Bird, is_mocking m)

  : is_compatible a b
:=
begin
  cases C₂ with m C_m,
  -- Use solution to Problem 5
  cases composition3 a b m C₁ with d H,
  have H_d := H d,
  rw is_mocking at C_m,
  rw C_m at H_d,
  rw is_compatible,
  existsi d ⬝ d, -- x
  existsi b ⬝ (d ⬝ d), -- y
  split,

  -- Goal 1: a y = x
  symmetry,
  exact H_d,

  -- Goal 2: b x = y
  reflexivity,
end

/-
 Problem 7: Happy Birds
-/

def is_happy(a: Bird): Prop := is_compatible a a

def is_normal(a: Bird): Prop := ∃ x: Bird, is_fond a x

theorem normal_is_happy (a: Bird)
  (C₁: is_normal a)

  : ∃ x: Bird, is_happy x
:=
begin
  cases C₁ with x' C',
  existsi a,
  existsi x',
  existsi x',
  split,
  repeat {exact C'},
end


/-
 Problem 8: Normal Birds
-/

theorem happy_may_be_normal (h: Bird)
  (C₁: ∀ a b: Bird, ∃ c: Bird, composes a b c)
  (C₂: is_happy h)

  : ∃ x: Bird, is_normal x
:=
begin
  -- In human terms: if h is a happy bird,
  -- we can show that the bird c that composes
  -- h and h is normal
  cases C₂ with x' C₂,
  cases C₂ with y' C₂,
  have C₁hh := C₁ h h,
  cases C₁hh with c C₁hh,
  rw composes at C₁hh,
  have C₁hh' := C₁hh x',
  cases C₂ with C₂x C₂y,
  rw C₂y at C₁hh',
  rw C₂x at C₁hh',
  existsi c,
  rw is_normal,
  existsi x',
  exact C₁hh',
end

/-
 Problem 9: Hopelessly Egocentric
-/

def is_fixated(a b: Bird): Prop := ∀ x: Bird, a ⬝ x = b

def is_hopelessly_egocentric(a: Bird): Prop := is_fixated a a

def is_kestrel(k: Bird): Prop := ∀ x y: Bird, (k ⬝ x) ⬝ y = x

theorem hopelessly_egocentric
  (C₁: ∀ a b: Bird, ∃ c: Bird, composes a b c)
  (C₂: ∃ m, is_mocking m)
  (C₃: ∃ k, is_kestrel k)

  : ∃ x: Bird, is_hopelessly_egocentric x
:=
begin
  have T₁ := fondness C₁ C₂,
  cases C₃ with k C₃,
  have T₁ := T₁ k,
  cases T₁ with x' T₁',
  rw is_fond at T₁',
  rw is_kestrel at C₃,
  have C₃' := C₃ x',
  rw T₁' at C₃',
  existsi x',
  rw is_hopelessly_egocentric,
  rw is_fixated,
  exact C₃',
end


/-
 Problem 10: Fixation
-/
theorem fixation (a b: Bird)
  (C₁: is_fixated a b)
  : is_fond a b
:=
begin
  rw is_fixated at C₁,
  have C₁b := C₁ b,
  exact C₁b,
end

/-
 Problem 11: A Fact About Kestrels
-/
theorem hopelessly_egocentric_kestrel (k: Bird)
  (C₁: is_kestrel k)
  (C₂: is_egocentric k)
  : is_hopelessly_egocentric k
:=
begin
  rw is_kestrel at C₁,
  have C₁k := C₁ k,
  rw is_egocentric at C₂,
  rw is_fond at C₂,
  rw C₂ at C₁k,
  exact C₁k,
end

/-
 Problem 12: Another Fact About Kestrels
-/
theorem fond_kestrel (k a: Bird)
  (C₁: is_kestrel k)
  (C₂: is_egocentric (k ⬝ a))
  : is_fond k a
:=
begin
  rw is_kestrel at C₁,
  have C₁a := C₁ a (k ⬝ a),
  rw is_egocentric at C₂,
  rw is_fond at C₂,
  rw C₂ at C₁a,
  exact C₁a,
end

/-
 Problem 13: A Simple Exercise
-/
theorem simple_exercise (a: Bird)
  (C₁: is_hopelessly_egocentric a)
  : ∀ x y, a ⬝ x = a ⬝ y
:=
begin
  rw is_hopelessly_egocentric at C₁,
  rw is_fixated at C₁,
  intro x',
  intro y',
  have C₁x := C₁ x',
  have C₁y := C₁ y',
  rw C₁x,
  rw C₁y,
end

/-
 Problem 14: Another Exercise
-/
theorem another_exercise (a: Bird)
  (C₁: is_hopelessly_egocentric a)
  : ∀ x y, (a ⬝ x) ⬝ y = a
:=
begin
  rw is_hopelessly_egocentric at C₁,
  rw is_fixated at C₁,
  intro x',
  intro y',
  have C₁x := C₁ x',
  have C₁y := C₁ y',
  rw C₁x,
  rw C₁y,
end -- exact same proof as in simple_exercise!

/-
 Problem 15: Hopeless Egocentricity Is Contagious!
-/
theorem hopeless_egocentricity_is_contagious (a: Bird)
  (C₁: is_hopelessly_egocentric a)
  : ∀ x, is_hopelessly_egocentric (a ⬝ x)
  :=
begin
  intro x',
  rw C₁ x',
  exact C₁,
end

/-
 Problem 16: Another Fact About Kestrels
-/
theorem kestrel_left_cancellation (k a b: Bird)
  (C₁: is_kestrel k)
  (C₂: k ⬝ a = k ⬝ b)
  : a = b
:=
begin
  have C₁bb := C₁ b b,
  rw← C₂ at C₁bb,
  have C₁ab := C₁ a b,
  rw← C₁bb,
  rw C₁ab,
end

/-
 Problem 17: A Fact About Fixation
-/
theorem uniqueness_fixation (a b c: Bird)
  (C₁: is_fixated a b)
  (C₂: is_fixated a c)
  : b = c
:=
begin
  have C₁b := C₁ b,
  have C₂b := C₂ b,
  rw← C₁b,
  rw C₂b,
end

/-
 Problem 18: A Fact About Fixation
-/
theorem fond_kestrel_2 (k a: Bird)
  (C₁: is_kestrel k)
  (C₂: is_fond k (k ⬝ a))
  : is_fond k a
:=
begin
  rw is_kestrel at C₁,
  have C₁ka := C₁ (k ⬝ a) a,
  rw is_fond at C₂,
  rw C₂ at C₁ka,
  have C₁a := C₁ a a,
  rw C₁a at C₁ka,
  rw is_fond,
  symmetry,
  exact C₁ka,
end

/-
 Problem 19: A Riddle
-/
theorem egocentric_kestrel (k: Bird)
  (C₁: is_kestrel k)
  (C₂: is_egocentric k)
  : ∀ x: Bird, x = k
:=
begin
  have C₁k := C₁ k,
  rw is_egocentric at C₂,
  rw is_fond at C₂,
  rw C₂ at C₁k,
  intro x',
  have C₁' := C₁ x' k,
  rw C₁k at C₁',
  rw C₁k at C₁',
  symmetry,
  exact C₁',
end
