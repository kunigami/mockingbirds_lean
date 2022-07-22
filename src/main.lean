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
 Problem 9.1: The significance of the Mockingbird
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
 Problem 9.2: Egocentric?
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
 Problem 9.3: Story of the Agrreable Bird
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
 Problem 9.4: A Question on Aggreable Birds

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
 Problem 9.5: An exercise in composition
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
 Problem 9.6: Compatible birds
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
  -- Use solution to Problem 9.5
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
 Problem 9.7: Happy Birds
-/

def is_happy(a: Bird): Prop := is_compatible a a

def is_normal(a: Bird): Prop := ∃ x: Bird, is_fond a x

theorem normal_is_happy (a: Bird)
  (C₁: is_normal a)
  : is_happy a
:=
begin
  cases C₁ with x' C',
  rw is_happy,
  rw is_compatible,
  existsi x',
  existsi x',
  split,
  repeat {exact C'},
end


/-
 Problem 9.8: Normal Birds
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
 Problem 9.9: Hopelessly Egocentric
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
 Problem 9.10: Fixation
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
 Problem 9.11: A Fact About Kestrels
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
 Problem 9.12: Another Fact About Kestrels
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
 Problem 9.13: A Simple Exercise
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
 Problem 9.14: Another Exercise
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
 Problem 9.15: Hopeless Egocentricity Is Contagious!
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
 Problem 9.16: Another Fact About Kestrels
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
 Problem 9.17: A Fact About Fixation
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
 Problem 9.18: A Fact About Fixation
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
 Problem 9.19: A Riddle
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


/-
 Problem 9.20
-/
def is_identity(i: Bird): Prop := ∀ x: Bird, i ⬝ x = x

theorem agreeable_identity(i: Bird)
  (C₁: is_identity i)
  (C₂: is_agreeable i)
:  ∀ x: Bird, is_normal x
:=
begin
  rw is_agreeable at C₂,
  rw is_identity at C₁,
  intro a,
  have C₂a := C₂ a,
  cases C₂a with x' C₂a',
  have C₁' := C₁ x',
  rw C₁' at  C₂a',
  rw is_normal,
  existsi x',
  rw is_fond,
  symmetry,
  exact C₂a',
end

/-
 Problem 9.21
-/
theorem identity_and_normals(i: Bird)
  (C₁: is_identity i)
  (C₂: ∀ x: Bird, is_normal x)
: is_agreeable i
:=
begin
  rw is_agreeable,
  intro b,
  have C₂b := C₂ b,
  rw is_normal at C₂b,
  cases C₂b with x' C₂b',
  rw is_fond at C₂b',
  existsi x',
  rw C₂b',
  rw C₁,
end

/-
 Problem 9.22
-/
theorem identity_and_compatibles(i: Bird)
  (C₁: is_identity i)
  (C₂: ∀ x y: Bird, is_compatible x y)
: (∀ x: Bird, is_normal x) ∧ (is_agreeable i)
:=
begin
  rw is_identity at C₁,

  split,

  -- Goal 1
  intro b,
  rw is_normal,
  have C₂bi := C₂ b i,
  rw is_compatible at C₂bi,
  cases C₂bi with x' C₂bi',
  cases C₂bi' with y' C₂bi',
  cases C₂bi' with C₂byx C₂iyx,
  rw C₁ at C₂iyx,
  rw C₂iyx at C₂byx,
  existsi y',
  rw is_fond,
  exact C₂byx,

  -- Goal 2
  rw is_agreeable,
  intro b,
  -- TODO: the next 8 lines are the same as for Goal 1
  -- except for a different 'b'. How to reuse?
  have C₂bi := C₂ b i,
  rw is_compatible at C₂bi,
  cases C₂bi with x' C₂bi',
  cases C₂bi' with y' C₂bi',
  cases C₂bi' with C₂byx C₂iyx,
  rw C₁ at C₂iyx,
  rw C₂iyx at C₂byx,
  existsi y',
  have C₁y := C₁ y',
  rw C₁ y',
  symmetry,
  exact C₂byx,
end

/-
 Problem 9.23 - Why?
-/
theorem hopelessly_egocentric_identity(i: Bird)
  (C₁: is_identity i)
  (C₂: is_hopelessly_egocentric i)
  : ∀ x, x = i
:=
begin
  rw is_hopelessly_egocentric at C₂,
  rw is_fixated at C₂,
  rw is_identity at C₁,
  intro x',
  have C₁x := C₁ x',
  have C₂x := C₂ x',
  rw ←C₁x,
  rw C₂x,
end

/-
 Problem 9.24
-/

def is_lark(l: Bird): Prop := ∀ x y: Bird, (l ⬝ x) ⬝ y = x ⬝ (y ⬝ y)

theorem lark_and_identity(i l: Bird)
  (C₁: is_identity i)
  (C₂: is_lark l)
  : ∃ m, is_mocking m
:=
begin
  existsi (l ⬝ i),
  rw is_mocking,
  intro x',

  rw is_lark at C₂,
  have C₂ix := C₂ i x',
  rw is_identity at C₁,
  have C₁xx := C₁ (x' ⬝ x'),
  rw C₁xx at C₂ix,
  exact C₂ix,
end

/-
 Problem 9.25
-/

lemma lark_and_fondness(l: Bird)
  (C₁: is_lark l)
  : ∀ x, is_fond x ((l ⬝ x) ⬝ (l ⬝ x))
:=
begin
  intro x',
  rw is_fond,
  have C₁x := C₁ x',
  have C₁xlx := C₁x (l ⬝ x'),
  symmetry,
  exact C₁xlx,
end

theorem lark_and_happy(l: Bird)
  (C₁: is_lark l)
  : ∀ x, is_happy x
:=
begin
  have LF := lark_and_fondness l C₁,
  intro x',
  -- reduce Problem 9.to proving ∀ x, is_normal x.
  apply (normal_is_happy x'),
  rw is_normal,
  existsi ((l ⬝ x') ⬝ (l ⬝ x')),
  have LF' := LF  x',
  exact LF',
end

/-
 Problem 9.26
-/
theorem hopelessly_egocentric_lark(l: Bird)
  (C₁: is_lark l)
  (C₂: is_hopelessly_egocentric l)
  : ∀ x, is_fond x l
:=
begin
  intro x',
  rw is_fond,
  rw is_lark at C₁,
  rw is_hopelessly_egocentric at C₂,
  rw is_fixated at C₂,
  have C₁xl := C₁ x' l,
  repeat {rw C₂ at C₁xl},
  symmetry,
  exact C₁xl
end

/-
 Problem 9.27
-/

-- If lark is fond of kestrel, then all birds are egocentric
lemma lark_fond_of_kestrel_all_egocentric(k l: Bird)
  (C₁: is_kestrel k)
  (C₂: is_lark l)
  (C₃: is_fond l k)
  : ∀ x, is_egocentric x
:=
begin
  intro x',
  rw is_kestrel at C₁,
  rw is_lark at C₂,
  rw is_fond at C₃,

  have C₂kx' := C₂ k x',
  rw C₃ at C₂kx',

  have C₁xxk := C₁ (x' ⬝ x') k,
  rw← C₂kx' at C₁xxk,

  have C₁lk := C₁ x' k,
  rw C₁xxk at C₁lk,

  rw is_egocentric,
  rw is_fond,
  exact  C₁lk,
end

theorem lark_fond_of_kestrel_same(k l: Bird)
  (C₁: is_kestrel k)
  (C₂: is_lark l)
  (C₃: is_fond l k)
  : l = k
:=
begin
  rw is_kestrel at C₁,

  -- Goal 1: is_hopelessly_egocentric k
  let hego_k: is_hopelessly_egocentric k,
  intro x',
  have C₁kl := C₁ k x',
  have all_ego := lark_fond_of_kestrel_all_egocentric k l C₁ C₂ C₃,
  have ego_k := all_ego k,
  rw is_egocentric at ego_k,
  rw is_fond at ego_k,
  rw ego_k at C₁kl,
  exact C₁kl,

  -- Goal 2
  have C₁k := C₁ l k,
  repeat {rw hego_k at C₁k},
  symmetry,
  exact C₁k
end

/-
 Problem 9.28
-/
theorem kestrel_fond_of_lark(k l: Bird)
  (C₁: is_kestrel k)
  (C₂: is_lark l)
  (C₃: is_fond k l)
  : ∀ x, is_fond x l
:=
begin
  rw is_kestrel at C₁,
  rw is_fond at C₃,
  rw is_lark at C₂,
  intro x',
  rw is_fond,
  have C₁l := C₁ l,
  rw C₃ at C₁l,
  -- C₁l : l is hopelessly ego.
  have C₂x'l := C₂ x' l,
  rw C₁l x' at C₂x'l,
  rw C₁l l at C₂x'l,
  symmetry,
  exact C₂x'l,
end

/-
 Problem 10: Is There a Sage Bird
 (hard)
-/

lemma lark_exists(l m: Bird)
  (C₂: is_mocking m)
  (C₃: ∀ a: Bird, composes a m (l ⬝ a))
  : is_lark l
:=
begin
  rw is_lark,
  intro x,
  intro y,
  have C₃x := C₃ x,
  rw composes at C₃x,
  have C₃xy := C₃x y,
  rw C₂ at C₃xy,
  exact C₃xy,
end

def is_sage(θ: Bird): Prop := ∀ x: Bird, x ⬝ (θ ⬝ x) = θ ⬝ x

theorem sage_exists(m: Bird)
  (C₁: ∀ a b: Bird, ∃ c: Bird, composes a b c)
  (C₂: is_mocking m)
  (C₃: ∃ r, ∀ a: Bird, composes a m (r ⬝ a))
  : ∃ θ: Bird, is_sage θ
:=
begin
  -- We'll prove that the bird that composes m and l
  -- is the sage bird θ

  -- given C₂ C₃, a lark exists
  cases C₃ with l C₃l,
  have L := lark_exists l m C₂ C₃l,

  -- By definition: θ x = m (l x)
  have C₁ml := C₁ m l,
  cases C₁ml with θ C₁ml,
  existsi θ,
  rw is_sage,

  intro x',

  -- Use result that
  -- x' is fond of (l x' (l x'))
  have LF := lark_and_fondness l L,
  have LF' := LF x',
  rw is_fond at LF',

  -- Remove duplicates by using xx -> mx
  rw is_mocking at C₂,
  have C₂' := C₂ (l ⬝ x'),
  rw← C₂' at LF',

  -- Replace m (l x) by θ x
  rw composes at C₁ml,
  have C₁ml' := C₁ml x',
  rw← C₁ml' at LF',

  exact LF',
end

/-
 Problem 11.1
-/

def is_blue(b: Bird): Prop := ∀ x y z: Bird, b ⬝ x ⬝ y ⬝ z = x ⬝ (y ⬝ z)

theorem blue_implies_composition(b: Bird)
  (C₁: is_blue b)
  : ∀ x y: Bird, ∃ z: Bird, composes x y z :=
begin
  intro x,
  intro y,
  rw is_blue at C₁,
  existsi b ⬝ x ⬝ y,
  rw composes,
  intro z,
  exact C₁ x y z,
end

/-
 Problem 11.2 - blue birds and mocking birds
-/

theorem fond_of_blue_and_mocking(b m: Bird)
  (C₁: is_blue b)
  (C₂: is_mocking m)
  : ∀ x: Bird, is_fond x (m ⬝ (b ⬝ x ⬝ m)) :=
begin
  intro x,
  rw is_fond,
  rw is_mocking at C₂,
  rw is_blue at C₁,
  rw C₂ (b ⬝ x ⬝ m),

  have C' := C₁ x m (b ⬝ x ⬝ m),
  rw C₂ (b ⬝ x ⬝ m) at C',
  symmetry,
  exact C',
end

/-
 Problem 11.3 - egocentric
 (hard)

  Idea:
    From 11.2 we have
    x (m ⬝ (b ⬝ x ⬝ m)) = m ⬝ (b ⬝ x ⬝ m)

    [key step] Replace x with m:
    m (m ⬝ (b ⬝ m ⬝ m)) = m ⬝ (b ⬝ m ⬝ m)

    let e = m ⬝ (b ⬝ m ⬝ m):
    me = e

    using mx = xx:
    ee = e

    So m ⬝ (b ⬝ m ⬝ m) is egocentric
-/

theorem egocentric_from_blue_and_mocking(b m: Bird)
  (C₁: is_blue b)
  (C₂: is_mocking m)
  : is_egocentric (m ⬝ (b ⬝ m ⬝ m)) :=
begin
  have C₃ := fond_of_blue_and_mocking b m C₁ C₂,
  have C₃m := C₃ m,
  rw is_fond at C₃m,
  rw C₂ at C₃m,
  exact C₃m,
end

/-
 Problem 11.4 - hopelessly egocentric

  From 11.2 we have
  x (m (b x m)) = m (b x m)

  [key step] Replace x with k:
  k (m (b k m)) = m (b k m)

  let h = m (b k m)
  k h = h

  By kestrel
  k h y = h
  h y = h

-/
theorem hopelessly_egocentric_from_blue_kestrel_mocking(b k m: Bird)
  (C₁: is_blue b)
  (C₂: is_kestrel k)
  (C₃: is_mocking m)
  : is_hopelessly_egocentric (m ⬝ (b ⬝ k ⬝ m)) :=
begin
  have C₄ := fond_of_blue_and_mocking b m C₁ C₃,
  have C₄k := C₄ k,
  rw is_fond at C₄k,

  rw is_kestrel at C₂,
  have C₂' := C₂ (m ⬝ (b ⬝ k ⬝ m)),

  rw is_hopelessly_egocentric,
  rw is_fixated,
  intro x',

  have C₂x' := C₂' x',
  rw C₄k at C₂x',
  exact C₂x',
end

/-
 Problem 11.5 - doves
 -/
def is_dove(d: Bird): Prop :=
  ∀ x y z w: Bird, d ⬝ x ⬝ y ⬝ z ⬝ w = x ⬝ y ⬝ (z ⬝ w)

/-
  Prove that d = bb
-/
theorem dove_from_blue(b: Bird)
  (C₁: is_blue b)
  : is_dove(b ⬝ b) :=
begin
  rw is_dove,
  intro x',
  intro y',
  intro z',
  intro w',

  have H₁ := C₁ (x' ⬝ y') z' w',
  rw ←C₁,

  have H₂ := C₁ b x' y',
  rw H₂,
end

/-
 Problem 11.6 - blackbird
 -/
def is_blackbird(b₁: Bird): Prop :=
  ∀ x y z w: Bird, b₁ ⬝ x ⬝ y ⬝ z ⬝ w = x ⬝ (y ⬝ z ⬝ w)

/-
  Prove that b₁ = db
-/
theorem blackbird_from_blue(b: Bird)
  (C₁: is_blue b)
  : is_blackbird(b ⬝ b ⬝ b) :=
begin
  rw is_blackbird,
  intro x',
  intro y',
  intro z',
  intro w',

  have C₂ := dove_from_blue b C₁,
  rw is_dove at C₂,

  have H₁ := C₂ b x' y' z',
  rw H₁,

  have H₂ := C₁ x' (y' ⬝ z') w',
  exact H₂,
end

/-
 Problem 11.7 - eagle
 -/
def is_eagle(e: Bird): Prop :=
  ∀ x y z w v: Bird, e ⬝ x ⬝ y ⬝ z ⬝ w ⬝ v = x ⬝ y ⬝ (z ⬝ w ⬝ v)

/-
  Prove that e = b b₁
-/
theorem eagle_from_blue(b b₁: Bird)
  (C₁: is_blue b)
  (C₂: is_blackbird b₁)
  : is_eagle(b ⬝ b₁) :=
begin
  rw is_eagle,
  intro x',
  intro y',
  intro z',
  intro w',
  intro v',

  rw is_blackbird at C₂,
  have C₂ := C₂ (x' ⬝ y') z' w' v',

  rw is_blue at C₁,
  have C₁ := C₁ b₁ x' y',

  rw C₁,
  rw C₂,
end

/-
 Problem 11.8 - bunting
 -/
def is_bunting(b₂: Bird): Prop :=
  ∀ x y z w v: Bird, b₂ ⬝ x ⬝ y ⬝ z ⬝ w ⬝ v = x ⬝ (y ⬝ z ⬝ w ⬝ v)

/-
  Prove that b₂ = e b
-/
theorem bunting_from_blue(b e: Bird)
  (C₁: is_blue b)
  (C₂: is_eagle e)
  : is_bunting(e ⬝ b) :=
begin
  rw is_bunting,
  intro x',
  intro y',
  intro z',
  intro w',
  intro v',

  rw is_eagle at C₂,
  have C₂ := C₂ b x' y' z' w',

  rw is_blue at C₁,
  have C₁ := C₁ x' (y' ⬝ z' ⬝ w') v',

  rw C₂,
  rw C₁,
end

/-
 Problem 11.9 - dickcissel
 -/
def is_dickcissel(d₁: Bird): Prop :=
  ∀ x y z w v: Bird, d₁ ⬝ x ⬝ y ⬝ z ⬝ w ⬝ v = x ⬝ y ⬝ z ⬝ (w ⬝ v)

/-
  Prove that d₁ = b d
-/
theorem dickcissel_from_blue(b d: Bird)
  (C₁: is_blue b)
  (C₂: is_dove d)
  : is_dickcissel(b ⬝ d) :=
begin
  rw is_dickcissel,
  intro x',
  intro y',
  intro z',
  intro w',
  intro v',

  rw is_blue at C₁,
  have C₁ := C₁ d x' y',

  rw is_dove at C₂,
  have C₂ := C₂ (x' ⬝ y') z' w' v',

  rw C₁,
  rw C₂,
end

/-
 Problem 11.10 - becards
 -/
def is_becard(b₃: Bird): Prop :=
  ∀ x y z w: Bird, b₃ ⬝ x ⬝ y ⬝ z ⬝ w = x ⬝ (y ⬝ (z ⬝ w))


/-
  Prove that b₃ = d₁ b
-/
theorem becard_from_blue(b d₁: Bird)
  (C₁: is_blue b)
  (C₂: is_dickcissel d₁)
  : is_becard(d₁ ⬝ b) :=
begin
  rw is_becard,
  intro x',
  intro y',
  intro z',
  intro w',

  rw is_blue at C₁,
  have C₁ := C₁ x' y' (z' ⬝ w'),

  rw is_dickcissel at C₂,
  have C₂ := C₂ b x' y' z' w',

  rw C₂,
  rw C₁,
end

/-
 Problem 11.11 - dovekies
 -/
def is_dovekie(d₂: Bird): Prop :=
  ∀ x y z w v: Bird, d₂ ⬝ x ⬝ y ⬝ z ⬝ w ⬝ v = x ⬝ (y ⬝ z) ⬝ (w ⬝ v)

theorem dovekie_from_dove(d: Bird)
  (C₁: is_dove d) :
  is_dovekie(d ⬝ d) :=
begin
  rw is_dovekie,
  intro x',
  intro y',
  intro z',
  intro w',
  intro v',

  rw is_dove at C₁,
  have C₁' := C₁ x' (y' ⬝ z') w' v',

  have C₁'' := C₁ d x' y' z',

  rw C₁'',
  rw C₁',
end

/-
 Problem 11.12 - Bald eagles
 -/
def is_bald_eagle(e₁: Bird): Prop :=
  ∀ x y₁ y₂ y₃ z₁ z₂ z₃: Bird, e₁ ⬝ x ⬝ y₁ ⬝ y₂ ⬝ y₃ ⬝ z₁ ⬝ z₂ ⬝ z₃ = x ⬝ (y₁ ⬝ y₂ ⬝ y₃) ⬝ (z₁ ⬝ z₂ ⬝ z₃)

theorem bald_eagle_from_eagle(e: Bird)
  (C₁: is_eagle e) :
  is_bald_eagle(e ⬝ e) :=
begin
  rw is_bald_eagle,
  intro x',
  intro y₁',
  intro y₂',
  intro y₃',
  intro z₁',
  intro z₂',
  intro z₃',

  rw is_eagle at C₁,
  have C₁' := C₁ x' (y₁' ⬝ y₂' ⬝ y₃') z₁' z₂' z₃',

  have C₁'' := C₁ e x' y₁' y₂' y₃',

  rw C₁'',
  rw C₁',
end


def is_warbler(w: Bird): Prop :=
  ∀ x y: Bird, w ⬝ x ⬝ y = x ⬝ y ⬝ y

/-
 Problem 11.14
 -/
theorem mocking_from_warbler_and_identity(w i: Bird)
  (C₁: is_warbler w)
  (C₂: is_identity i) :
  is_mocking(w ⬝ i) :=
begin
  rw is_mocking,
  intro x,
  have C₁' := C₁ i x,
  rw C₁',
  rw C₂,
end

/-
 Problem 11.15
 -/
theorem identity_from_warbler_and_kestrel(w k: Bird)
  (C₁: is_warbler w)
  (C₂: is_kestrel k) :
  is_identity(w ⬝ k) :=
begin
  rw is_identity,
  intro x,
  have C₁' := C₁ k x,
  have C₂' := C₂ x x,
  rw C₁',
  exact C₂',
end

/-
  Problem 11.13 - warblers
 -/
theorem mocking_from_warbler_and_krestel(w k: Bird)
  (C₁: is_warbler w)
  (C₂: is_kestrel k) :
  is_mocking(w ⬝ (w ⬝ k)) :=
begin
  have I := identity_from_warbler_and_kestrel w k C₁ C₂,
  have M := mocking_from_warbler_and_identity w (w ⬝ k) C₁ I,
  exact M,
end

/-
 Problem 11.16
 -/
def is_cardinal(c: Bird): Prop :=
  ∀ x y z: Bird, c ⬝ x ⬝ y ⬝ z = x ⬝ z ⬝ y

theorem identity_from_cardinal_and_krestel(c k: Bird)
  (C₁: is_cardinal c)
  (C₂: is_kestrel k) :
  is_identity(c ⬝ k ⬝ k) :=
begin
  rw is_identity,
  intro x,
  have C₁' :=  C₁ k k x,
  have C₂' :=  C₂ x k,
  rw C₁',
  exact C₂',
end
