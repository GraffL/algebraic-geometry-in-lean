import ring_theory.ideal.basic
import exercise6

-- The Chinese remainder theorem

def ideals_are_comaximal {R : Type} [comm_semiring R] (A : ideal R) (B : ideal R) : Prop :=
  R = (A + B).carrier
  
-- 7a)
lemma prod_eq_cap_of_comaximal {R : Type} [comm_semiring R] {A : ideal R} {B : ideal R} [ideals_are_comaximal A B] :
  (A ⬝ B) = (A ∩ B) := 
begin
  ext,
  split,
  {
    intro h,
    apply ideal_prod_sub_cap,
    exact h,
  },
  {
    sorry,
  }
end