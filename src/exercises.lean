import tactic
import ring_theory.ideal.basic
import order.galois_connection
import data.nat.choose.sum  -- for add_pow
import order.closure        -- for closure_operator
import set_theory.zfc       -- for powerset



universe u 

-- ###################################
-- Aufgabe 2
-- Aufgabe 2a)
def exercise2a {A: Type u} {B : Type u} [partial_order A] [partial_order B] 
  (f: A → B) (g : B → A) [galois_connection f g] :
  closure_operator A := {
    to_fun := g ∘ f,
    monotone' := begin
      apply monotone.comp,
      apply galois_connection.monotone_u,
      exact _inst_3,
      apply galois_connection.monotone_l,
      exact _inst_3,
    end,
    le_closure' := begin
      intro x,
      simp,
      apply galois_connection.le_u _inst_3,
      refl,  
    end,
    idempotent' := begin
      simp,
      intro x,
      apply partial_order.le_antisymm,
      apply galois_connection.monotone_u _inst_3,
      apply galois_connection.l_le _inst_3,
      refl,
      apply galois_connection.le_u _inst_3,
      refl,
    end
    ,
  }
  -- Aufgabe 2b)
  -- --> analog zu 2a)

  -- ###################################
-- Aufgabe 6
-- Aufgabe 6a)
def ideal.intersection {R : Type u} [comm_semiring R] (I : ideal R) (J : ideal R) : 
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


-- Unfertig

variable {R : Type u}

def ideal.root {R : Type u} [comm_semiring R] (I : ideal R) :
  ideal R :=
    {
      carrier := {x : R | ∃ (n : ℕ), x^n ∈ I},
      zero_mem' := begin
        use 1,
        rw pow_one,
        apply I.zero_mem',
      end,
      add_mem' := begin
        intros a b,  
        intros aInRadical bInRadical,
        cases aInRadical with n aPownInI,
        cases bInRadical with m bPownInI,
        use n+m,
        rw add_pow a b (n+m),
        sorry
      end,
      smul_mem' := sorry
    }