import ring_theory.ideal.basic

-- ###################################
-- Aufgabe 6
-- Aufgabe 6a)
def ideal.intersection {R : Type} [comm_semiring R] (I : ideal R) (J : ideal R) : 
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
