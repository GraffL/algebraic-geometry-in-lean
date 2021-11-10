import ring_theory.ideal.basic
import exercise6

-- The Chinese remainder theorem

def ideal_are_comaximal {R : Type} [comm_semiring R] (A : ideal R) (B : ideal R) : Prop :=
  R = (A + B).carrier
  
-- 7a)
