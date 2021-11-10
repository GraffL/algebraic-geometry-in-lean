import order.galois_connection

universe u
variables X Y : Type u

def VR {X Y} (R: X → Y → Prop) (S : set X) : set Y := {y : Y | ∀ (s ∈ S), R s y}
def IR {X Y} (R: X → Y → Prop) (T : set Y) : set X := {x : X | ∀ (t ∈ T), R x t}

def subsetrel {X} : preorder (set X) := {
  le := λ A B, A ⊆ B,
  le_refl := set.subset.refl,
  le_trans := begin
    intros A B C,
      dsimp,
      exact set.subset.trans,
  end,
}
def supsetrel {Y} : preorder (set Y) := {
  le := λ A B, A ⊇ B,
  le_refl := set.subset.refl,
  le_trans := begin
    intros A B C,
      dsimp,
      intros hAB hBC,
      apply set.subset.trans,
      exact hBC,
      exact hAB,
  end,
}

-- exercise 1a
-- use @galois_connection to be able to provide all arguments explicitly
-- in particular we want to provide the preorders that way to be able to use different ones on P(X) and P(Y)
lemma ex1a (R : X → Y → Prop): @galois_connection (set X) (set Y) subsetrel supsetrel (VR R) (IR R) := begin
  intros S T,
  split,
  {
    show VR R S ⊇ T → S ⊆ IR R T,
    intro h,
    intros s hs,
    intros t ht,
    specialize h ht,
    specialize h s hs,
    exact h,
  },
  {
    show S ⊆ IR R T → VR R S ⊇ T,
    intro h,
    intros t ht,
    intros s hs,
    specialize h hs,
    specialize h t ht,
    exact h,
  },  
end