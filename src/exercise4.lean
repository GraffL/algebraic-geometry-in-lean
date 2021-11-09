import tactic

variable A : Type 

-- Exercise 4(a): Show that meet and join are unique (if they exist)
def isUpperBound {A} [partial_order A] (M : set A) (a : A) : Prop :=
  ∀ m ∈ M, m ≤ a

def isJoin {A} [partial_order A] (M : set A) (a : A) : Prop :=
  isUpperBound M a ∧ ∀ a' : A, (∀ m ∈ M, m ≤ a') → a ≤ a' 

lemma join_is_unique [partial_order A] {M : set A} {a b : A} (aM : isJoin M a) (bM : isJoin M b) : a = b :=
begin
  apply le_antisymm,
  {
    apply aM.right,
    exact bM.left,
  },
  {
    apply bM.right,
    exact aM.left,
  },
end

def isLowerBound {A} [partial_order A] (M : set A) (a : A) : Prop :=
  ∀ m ∈ M, m ≥ a

def isMeet {A} [partial_order A] (M : set A) (a : A) : Prop :=
  isLowerBound M a ∧ ∀ a' : A, (∀ m ∈ M, m ≥ a') → a ≥ a' 


lemma meet_is_unique [partial_order A] {M : set A} {a b : A} (aM : isMeet M a) (bM : isMeet M b) : a = b :=
begin
  apply le_antisymm,
  {
    apply bM.right,
    exact aM.left,
  },
  {
    apply aM.right,
    exact bM.left,
  },
end

-- Exercise 4(b)
-- Show that for a poset to be a complete lattice it suffices to show that every subset has a join (or every subset has a meet)
def hasAllJoins (A : Type) [partial_order A] : Prop :=
  ∀ M : set A, ∃ a : A, isJoin M a

def hasAllMeets (A : Type) [partial_order A] : Prop :=
  ∀ M : set A, ∃ a : A, isMeet M a

lemma allJoins_iff_allMeets {A} [partial_order A] : (hasAllJoins A) ↔ (hasAllMeets A) :=
begin
  split,
  {
    show hasAllJoins A → hasAllMeets A,
    sorry,
  },
  {
    show hasAllMeets A → hasAllJoins A,
    intro hAllMeets,
    intro M,
    let N := {a : A | ∀ m ∈ M, m ≤ a},
    cases hAllMeets N with meetN hMeetN,
    use meetN,
    split,
    {
      show ∀ m ∈ M, m ≤ meetN,
      intro m,
      intro hmM,
      have h : ∀ n ∈ N, m ≤ n :=
      begin
        intro n,
        intro hnN,
        simp at hnN,
        exact hnN m hmM,
      end,
      exact hMeetN.right m h,
    },
    {
      show ∀ a' : A, (∀ m ∈ M, m ≤ a') → meetN ≤ a',
      intro a',
      intro h,
      exact hMeetN.left a' h,
    },
  },
end