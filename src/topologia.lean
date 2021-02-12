import tactic
import data.set.finite
import data.real.basic -- for metrics

/-
# (Re)-Building topological spaces in Lean
 -- Credit: Alex Best
-/

/-
First a little setup, we will be making definitions involving the real numbers,
the theory of which is not computable, and we'll use sets.
-/
noncomputable theory
open set

/-!
## What is a topological space:

There are many definitions: one from Wikipedia:
  A topological space is an ordered pair (X, τ), where X is a set and τ is a
  collection of subsets of X, satisfying the following axioms:
  - The empty set and X itself belong to τ.
  - Any arbitrary (finite or infinite) union of members of τ still belongs to τ.
  - The intersection of any finite number of members of τ still belongs to τ.

We can formalize this as follows: -/

class topological_space_wiki :=
  (X : Type)  -- the underlying Type that the topology will be on
  (τ : set (set X))  -- the set of open subsets of X
  (empty_mem : ∅ ∈ τ)  -- empty set is open
  (univ_mem : univ ∈ τ)  -- whole space is open
  (union : ∀ B ⊆ τ, ⋃₀ B ∈ τ)  -- arbitrary unions (sUnions) of members of τ are open
  (inter : ∀ (B ⊆ τ) (h : finite B), ⋂₀ B ∈ τ)  -- finite intersections of
                                                -- members of τ are open

/-
Before we go on we should be sure we want to use this as our definition.
-/


@[ext]
class topological_space (X : Type) :=
  (is_open : set X → Prop) -- why set X → Prop not set (set X)? former plays
                           -- nicer with typeclasses later
  --(empty_mem : is_open ∅)
  (univ_mem : is_open univ)
  (union : ∀ (Y : set (set X)) (h : ∀ B ∈ Y, is_open B), is_open (⋃₀ Y))
  (inter : ∀ (A B : set X) (hA : is_open A) (hB : is_open B), is_open (A ∩ B))

namespace topological_space

lemma empty_is_open (X : Type) [topological_space X] : is_open (∅ : set X) :=
begin
  rw ←sUnion_empty,
  apply union,
  tauto,
end

/- We can now work with topological spaces like this. -/
example (X : Type) [topological_space X] (U V W : set X) (hU : is_open U) (hV : is_open V)
  (hW : is_open W) : is_open (U ∩ V ∩ W) :=
begin
  apply inter _ _ _ hW,
  exact inter _ _ hU hV,
end

/- ## Exercise 0 [short]:
One of the axioms of a topological space we have here is unnecessary, it follows
from the others. If we remove it we'll have less work to do each time we want to
create a new topological space so:

1. Identify and remove the unneeded axiom, make sure to remove it throughout the file.
2. Add the axiom back as a lemma with the same name and prove it based on the
   others, so that the _interface_ is the same. -/


/- Defining a basic topology now works like so: -/
def discrete (X : Type) : topological_space X :=
{ is_open := λ U, true, -- everything is open
  univ_mem := trivial,
  union := begin intros B h, trivial, end,
  inter := begin intros A hA B hB, trivial, end }

/- ## Exercise 1 [medium]:
One way me might want to create topological spaces in practice is to take
the coarsest possible topological space containing a given set of is_open.
To define this we might say we want to define what `is_open` is given the set
of generators.
So we want to define the predicate `is_open` by declaring that each generator
will be open, the intersection of two opens will be open, and each union of a
set of opens will be open, and finally the empty and whole space (`univ`) must
be open. The cleanest way to do this is as an inductive definition.

The exercise is to make this definition of the topological space generated by a
given set in Lean.
-/

/-- The open sets of the least topology containing a collection of basic sets. -/
inductive generated_open (X : Type) (g : set (set X)) : set X → Prop
| univ : generated_open univ
| generating : ∀ A : set X,  A ∈ g → generated_open A
| sUnion : ∀ τ : set(set X), (∀ t, t ∈ τ → generated_open t) →
          generated_open ⋃₀ τ 
| inter : ∀ U V : set X,  generated_open U → generated_open V →
            generated_open (U ∩ V)

/-- The smallest topological space containing the collection `g` of basic sets -/
def generate_from (X : Type) (g : set (set X)) : topological_space X :=
{ is_open   := generated_open X g,
  univ_mem  := generated_open.univ,
  inter     := generated_open.inter,
  union     := generated_open.sUnion, }


lemma generated_open_is_coarsest' {X : Type} (g : set (set X)) [topological_space X]
(h : ∀ U ∈ g,  is_open U) : ∀ U : set X, generated_open X g U → is_open U :=
begin
  intros U hU,
  induction hU with a b c d e V W hV1 hW1 hV2 hW2,
  { exact univ_mem },
  { apply h, assumption },
  { apply union; assumption },
  { apply inter; assumption },
end

def is_coarser {X : Type} (τ : topological_space X) (τ' : topological_space X) :=
  ∀ (U : set X), @is_open _ τ U → @is_open _ τ' U

instance top_has_le {X : Type} : has_le (topological_space X) := ⟨is_coarser⟩

lemma generated_open_is_coarsest {X : Type} (g : set (set X)) [τ : topological_space X]
(h : ∀ U ∈ g,  is_open U) : (generate_from X g) ≤ τ := λ U, generated_open_is_coarsest' g h U

/- ## Exercise 2 [short]:
Define the indiscrete topology on any type using this.
(To do it without this it is surprisingly fiddly to prove that the set `{∅, univ}`
actually forms a topology) -/
def indiscrete (X : Type) : topological_space X := generate_from X {∅, univ}

end topological_space

open topological_space
/- Now it is quite easy to give a topology on the product of a pair of
   topological spaces. -/
instance prod.topological_space (X Y : Type) [topological_space X]
  [topological_space Y] : topological_space (X × Y) :=
topological_space.generate_from (X × Y) {U | ∃ (Ux : set X) (Uy : set Y)
  (hx : is_open Ux) (hy : is_open Uy), U = set.prod Ux Uy}


-- the proof of this is bit long so I've left it out for the purpose of this file!
lemma is_open_prod_iff (X Y : Type) [topological_space X] [topological_space Y]
  {s : set (X × Y)} :
is_open s ↔ (∀a b, (a, b) ∈ s → ∃u v, is_open u ∧ is_open v ∧
                                  a ∈ u ∧ b ∈ v ∧ set.prod u v ⊆ s) := sorry

/- # Metric spaces -/

open_locale big_operators

class metric_space_basic (X : Type) :=
  (dist : X → X → ℝ)
  (dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y)
  (dist_symm : ∀ x y, dist x y = dist y x)
  (triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)

namespace metric_space_basic
open topological_space

/- ## Exercise 3 [short]:
We have defined a metric space with a metric landing in ℝ, and made no mention of
nonnegativity, (this is in line with the philosophy of using the easiest axioms for our
definitions as possible, to make it easier to define individual metrics). Show that we
really did define the usual notion of metric space. -/
lemma dist_nonneg {X : Type} [metric_space_basic X] (x y : X) : 0 ≤ dist x y :=
begin
  have h1 : dist x x = 0,
    rw (dist_eq_zero_iff x x).2, refl,
  suffices : 0 ≤ dist x y + dist x y,
  { linarith },
  rw ← h1,
  nth_rewrite_rhs 1 dist_symm x y,
  exact triangle _ _ _,
end

/- From a metric space we get an induced topological space structure like so: -/

instance {X : Type} [metric_space_basic X] : topological_space X :=
generate_from X { B | ∃ (x : X) r, B = {y | dist x y < r} }

end metric_space_basic

open metric_space_basic

/- So far so good, now lets define the product of two metric spaces:

## Exercise 4 [medium]:
Fill in the proofs here.
Hint: the computer can do boring casework you would never dream of in real life.
`max` is defined as `if x < y then y else x` and the `split_ifs` tactic will
break apart if statements. -/
instance prod.metric_space_basic (X Y : Type) [metric_space_basic X] [metric_space_basic Y] :
metric_space_basic (X × Y) :=
{ dist := λ u v, max (dist u.fst v.fst) (dist u.snd v.snd),
  dist_eq_zero_iff :=
  begin
    intro xy1,
    intro xy2,
    split,
    {
      intro h,
      have h1: dist xy1.fst xy2.fst ≥ 0 := dist_nonneg _ _,
      have h2: dist xy1.snd xy2.snd ≥ 0 := dist_nonneg _ _,
      have h3: dist xy1.fst xy2.fst = 0, 
      begin
        have h5 : max (dist xy1.fst xy2.fst) (dist xy1.snd xy2.snd) ≤ 0 :=
          by linarith,
        have h4 := max_le_iff.mp h5,
        linarith,
      end,

      have h6: dist xy1.snd xy2.snd = 0, 
      begin
        have h5 : max (dist xy1.fst xy2.fst) (dist xy1.snd xy2.snd) ≤ 0 := by linarith,
        have h4 := max_le_iff.mp h5,
        linarith,
      end,

       ext;
       {
         rw [←dist_eq_zero_iff _ _],
         tauto,
       },
 
     },
    {
      intro h,
      -- how to extract `xy1.fst = xy2.snd` from h??
      subst h,  -- is it possible to skip this step?? 
      rw (dist_eq_zero_iff xy1.fst xy1.fst).mpr (refl _),
      rw (dist_eq_zero_iff xy1.snd xy1.snd).mpr (refl _),
      exact max_self 0,
    },
  end,
  dist_symm := 
  begin
    intros xy1 xy2,
    simp only [dist_symm],
  end,
  triangle :=
   begin
    intros x y z,
 
    let  xy_X := (dist x.fst y.fst),
    let  yz_X := (dist y.fst z.fst),
    let  xy_Y := (dist x.snd y.snd),
    let  yz_Y :=  (dist y.snd z.snd),

    -- We introduce a refinement.
    calc  max (dist x.fst z.fst) (dist x.snd z.snd) ≤ (max (xy_X + yz_X) ( xy_Y + yz_Y)): by { apply max_le_max; exact triangle _ _ _ }
        ... ≤ max (dist x.fst y.fst) (dist x.snd y.snd) + max (dist y.fst z.fst) (dist y.snd z.snd):
     begin
      refine max_le_iff.mpr _,
      split;
      {
        apply add_le_add;
        finish,
      }, 
    end,
   end,
}

/- ## Exercise 5 [short]: -/

/- (Bonus exercises [medium], the world is your oyster: prove the correct
version of the above lemma `diag_closed`, prove that the discrete topology is t2,
or that any metric topology is t2, ). -/


/- Let's fix the broken example from earlier, by redefining the topology on a metric space.
We have unfortunately created two topologies on `X × Y`, one via `prod.topology`
that we defined earlier as the product of the two topologies coming from the
respective metric space structures. And one coming from the metric on the product.

These are equal, i.e. the same topology (otherwise mathematically the product
would not be a good definition). However they are not definitionally equal, there
is as nontrivial proof to show they are the same. The typeclass system (which finds
the relevant topological space instance when we use lemmas involving topological
spaces) isn't able to check that topological space structures which are equal
for some nontrivial reason are equal on the fly so it gets stuck.

We can use `extends` to say that a metric space is an extra structure on top of
being a topological space so we are making a choice of topology for each metric space.
This may not be *definitionally* equal to the induced topology, but we should add the
axiom that the metric and the topology are equal to stop us from creating a metric
inducing a different topology to the topological structure we chose. -/
class metric_space (X : Type) extends topological_space X, metric_space_basic X :=
  (compatible : ∀ U, is_open U ↔ generated_open X { B | ∃ (x : X) r, B = {y | dist x y < r}} U)

namespace metric_space

open topological_space

/- This might seem a bit inconvenient to have to define a topological space each time
we want a metric space.

We would still like a way of making a `metric_space` just given a metric and some
properties it satisfies, i.e. a `metric_space_basic`, so we should setup a metric space
constructor from a `metric_space_basic` by setting the topology to be the induced one. -/

def of_basic {X : Type} (m : metric_space_basic X) : metric_space X :=
{ compatible := begin intros, refl, /- this should work when the above parts are complete -/ end,
  ..m,
  ..metric_space_basic.topological_space}

/- Now lets define the product of two metric spaces properly -/
instance {X Y : Type} [metric_space X] [metric_space Y] : metric_space (X × Y) :=
{ compatible :=
  begin
    intro U,
    split,
    {
      intro hU,
      induction hU with V h g h₁ h₂ V W h1 h2 h3 h4,
      { exact generated_open.univ },
      {
        simp at *,
        obtain ⟨Ux,hUx,Uy,⟨hUy,hprod⟩⟩ := h,
        subst hprod,
        
        sorry
      },
      { exact generated_open.sUnion g h₂ },
      { exact generated_open.inter V W h3 h4 },
    },
    {
      intro h,
      induction h,
      {apply univ_mem,},
      {
        sorry
      },
      {sorry},
      {sorry},
    },
  end,
  ..prod.topological_space X Y,
  ..prod.metric_space_basic X Y, }

/- unregister the bad instance we defined earlier -/
local attribute [-instance] metric_space_basic.topological_space

/- Now this will work, there is only one topological space on the product, we can
rewrite like we tried to before a lemma about topologies our result on metric spaces,
as there is only one topology here.

## Exercise 6 [long?]:
Complete the proof of the example (you can generalise the 100 too if it makes it
feel less silly). -/

example (X : Type) [metric_space X] : is_open {xy : X × X | dist xy.fst xy.snd < 100 } :=
begin
  rw is_open_prod_iff X X,
  sorry
end

end metric_space


namespace topological_space

noncomputable theory

/-
Show that {∅, univ, (-∞, a) : a : ℝ} is a topology on ℝ
-/
open real

lemma union_of_intervals {α : set ℝ} (hne : ∃ a : ℝ, a ∈ α) (h : ∃ (C : ℝ), ∀ a ∈ α, a ≤ C) :
  (⋃ a ∈ α, Iio a) = Iio (Sup α) :=
begin
  simp only [←Iio_def],
  ext,
  simp [lt_Sup α hne h],
end

def left_ray_topology : topological_space ℝ := {
  is_open := λ (X : set ℝ),  X = ∅ ∨ X = univ ∨ (∃ a : ℝ, X = Iio a),
  univ_mem := by tauto,
  union := 
  begin
    intro I,
    intro h,
    by_cases hempty : ∀ B ∈ I, B = ∅,
    {
      left,
      simp,
      exact hempty,
    },
    push_neg at hempty,
    right,
    by_cases huniv : ∃ B ∈ I, B = univ,
    {
      left,
      simp at *,
      ext1,
      norm_num,
      use univ,
      exact ⟨huniv, mem_univ x⟩,
    },
    push_neg at huniv,
    let α := {a | ∃ B ∈ I, B = Iio a},
    have hαne : ∃ a : ℝ, a ∈ α,
    {
      simp*,
      cases hempty with T hT,
      specialize h T hT.1,
      rcases h with h1 | h2 | h3,
      {
        by_contradiction,
        exact hT.2 h1,
      },
      {
        by_contradiction,
        exact (huniv T hT.1) h2,
      },
      {
        cases h3 with a ha,
        use a,
        rw ← ha, 
        exact hT.1,
      },
    },
    by_cases hbounded : ∃ c : ℝ, ∀ a ∈ α, a ≤ c,
    {
      right,
      use Sup α,
      rw ←union_of_intervals hαne hbounded,
      {
        dsimp,
        ext1,
        dsimp,
        split,
        {
          intro hx,
          simp,
          obtain ⟨B, ⟨hBI, hxB⟩⟩ := hx,
          specialize h B hBI,
          replace h : ∃ (a : ℝ), B = Iio a,
          {
            rcases h with h1 | h2 | h3,
            {
              finish,
            },
            {
              finish,
            },
            exact h3,
          },
          obtain ⟨a, ha⟩ := h,
          use a,
          rw ←ha,
          finish,
        },
        intro hx,
        simp at hx,
        obtain ⟨a, ha⟩ := hx,
        use Iio a,
        simpa using ha,
      },
    },
    push_neg at hbounded,
    left,
    sorry
  end,
  inter :=
  begin
    intros A B,
    intros hA hB,
    rcases hA with hA  | hA | hA,
    {
      left,
      subst hA,
      exact empty_inter B,
    },
    {
      subst hA,
      simp,
      exact hB,
    },
    {
      rcases hB with hB  | hB | hB,
      {
        left,
        subst hB,
        exact inter_empty A,
      },
      {
        subst B,
        simp,
        right,right,
        exact hA,
      },
      {
        obtain ⟨a, ha⟩ := hA,
        subst ha,
        obtain ⟨b, hb⟩ := hB,
        subst hb,
        right,right,
        use min a b,
        exact Iio_inter_Iio,
      },
    }
  end
   }

def is_closed {X : Type} [topological_space X] := λ (C : set X), @is_open X _ (compl C)

def mk_closed_sets
  (X : Type)
  (σ : set (set X))
  (empty_mem : ∅ ∈ σ)
  (inter : ∀ B ⊆ σ, ⋂₀ B ∈ σ)
  (union : ∀ (A ∈ σ) (B ∈ σ), A ∪ B ∈ σ) :
topological_space X := {
  is_open := λ U, U ∈ compl '' σ, -- λ U, compl U ∈ σ
  univ_mem := sorry,
  union := sorry,
  inter := sorry}

end topological_space

namespace topological_space

variables {X : Type}

def is_basis [topological_space X] (I : set (set X)) : Prop :=
(∀ (B : set X), B ∈ I → is_open B) ∧ 
(∀ U, ∀ x, is_open U → x ∈ U → ∃ B ∈ I, x ∈ B ∧ B ⊆ U)

def basis_condition (I : set (set X)) :=
⋃₀I = univ ∧ ∀ U V ∈ I, ∀ x : X, ∃ W ∈ I, x ∈ W ∧ W ⊆ U ∩ V

lemma basis_has_basis_condition [topological_space X] {I : set (set X)} (h: is_basis I):
  basis_condition I :=
begin
  sorry
end

lemma prop22 (I : set (set X)) (h: basis_condition I) :
  @is_basis _ (generate_from X I) I :=
begin
  unfold is_basis,
  sorry
end

/-
Define the family of intervals of the form [a, b)
-/
def Icos := {B : set ℝ | ∃ a b : ℝ, B = Ico a b }

example : basis_condition Icos :=
begin
  unfold basis_condition,
  split,
  {
    ext,
    split,
    {
      intro h,
      trivial,
    },
    {
      intro h,
      fconstructor,
      use Ico (x - 1) (x + 1),
      norm_num,
      use x-1,
      use x+1,     
    }
  },
  {
    intros U V hU hV x,

    sorry,
  }
end

example (a b : ℝ) : @is_open _ (generate_from ℝ Icos) (Ico a b) :=
begin
  fconstructor,
  use a, use b,
end

example (a b : ℝ) : @is_open _ (generate_from ℝ Icos) (Ico a b) :=
begin
  sorry
end

end topological_space

