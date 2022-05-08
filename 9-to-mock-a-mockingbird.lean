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
  -- a₁ b₁ c₁ particular instance
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
  -- We show that 'a' and 'd' agree of bind 'b x_e'
  existsi b ⬝ x_e,
  rw← Ce',
  rw← Ce'',
  exact Cagr_e,
end
