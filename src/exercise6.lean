import ring_theory.ideal.basic

import exercise2 -- For ideal generated by subset of a ring/radical of ideal

-- ###################################
-- Aufgabe 6

def ideal_sum {R : Type} [comm_semiring R] (I : ideal R) (J : ideal R) : 
  ideal R := ⟨ I.carrier ∪ J.carrier ⟩ 

notation I `+` J := ideal_sum I J

lemma ideal_sum_mem_iff {R : Type} [comm_semiring R] {I : ideal R} {J : ideal R} {x : R}: 
  x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, x = a + b := 
begin
  split,
  {
    sorry,
  },
  {
    intro h,
    cases h with a h,
    cases h with ha h,
    cases h with b h,
    cases h with hb h,
    suffices h' : a ∈ I+J ∧ b ∈ I+J,
    {
      rw h,
      apply (I+J).add_mem,
      exact h'.left,
      exact h'.right,
    },
    split,
    {
      apply ideal_of_extensive,
      left,
      exact ha,
    },
    {
      apply ideal_of_extensive,
      right,
      exact hb,
    },
  },
end

def ideal_product {R : Type} [comm_semiring R] (I : ideal R) (J : ideal R) : 
  ideal R := ⟨ {ab | ∃ a ∈ I, ∃ b ∈ J, ab = a*b} ⟩

notation I `⬝` J := ideal_product I J

-- Aufgabe 6a)
def ideal_intersection {R : Type} [comm_semiring R] (I : ideal R) (J : ideal R) : 
  ideal R := {
    carrier := I.carrier ∩ J.carrier,
    zero_mem' := begin
        rw set.inter_def,
        split,
        exact I.zero_mem',
        exact J.zero_mem',
      end,
    add_mem' := begin
        rw set.inter_def,
        intros a b aInInter bInInter,
        split,
        apply I.add_mem',
        exact aInInter.left,
        exact bInInter.left,
        apply J.add_mem',
        exact aInInter.right,
        exact bInInter.right,
      end,
    smul_mem' := begin
        rw set.inter_def,
        intros c x xInInter,
        split,
        apply I.smul_mem',
        exact xInInter.left,
        apply J.smul_mem',
        exact xInInter.right,
      end
  }

notation I `∩` J := ideal_intersection I J


-- Aufgabe b)
def ideal_quotient {R : Type} [comm_semiring R] (I : ideal R) (J : ideal R) : 
  ideal R := {
    carrier := {r : R | {r' | ∃ j : J, r' = r*j} ⊆ I},
    zero_mem' := begin
        intros r' hr',
        have h: r' = 0 := begin
          cases hr' with j hj,
          rw hj,
          ring,
        end,
        rw h,
        exact I.zero_mem',
      end,
    add_mem' := begin
        sorry,
      end,
    smul_mem' := begin
        sorry,
      end
  }

notation I `:` J := ideal_quotient I J


  -- Aufgabe c)
  lemma ideal_prod_sub_cap {R : Type} [comm_semiring R] {I : ideal R} {J : ideal R} : 
    (I ⬝ J).carrier ⊆ (I ∩ J).carrier := begin
      rw ← ideal_of_ideal (I ∩ J),
      apply ideal_of_mono,
      intros ab hab,
      cases hab with a hab,
      cases hab with ha hab,
      cases hab with b hab,
      cases hab with hb h,
      rw h,
      split,
      {
        show a*b ∈ I,
        rw mul_comm,
        exact I.smul_mem b ha,
      },
      {
        show a*b ∈ J,
        exact J.smul_mem a hb,
      },
  end

  lemma ideal_cap_sub_sum {R : Type} [comm_semiring R] (I : ideal R) (J : ideal R) : 
    (I ∩ J).carrier ⊆ (I + J).carrier := begin
      sorry,
  end

  -- Aufgabe d)
  lemma radical_prod_eq_cap {R : Type} [comm_semiring R] (I : ideal R) (J : ideal R) : 
    (√(I ⬝ J)) = √(I ∩ J) := begin
      sorry,
  end

  lemma radical_cap_eq_cap_radical {R : Type} [comm_semiring R] (I : ideal R) (J : ideal R) : 
    (√(I ∩ J)) = (√I) ∩ (√J) := begin
      sorry,
  end

  -- Aufgabe e)
  lemma radical_sum {R : Type} [comm_semiring R] (I : ideal R) (J : ideal R) : 
    (√(I + J)) = √((√I) + (√J)) := begin
      sorry,
  end
