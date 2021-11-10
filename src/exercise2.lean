import tactic
import order.galois_connection
import order.closure        -- for closure_operator
import ring_theory.ideal.basic
import algebra.big_operators.basic
import data.nat.choose.sum



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



open_locale big_operators
-- Aufgabe 2c)
def ideal_of_subset {R : Type} [comm_semiring R] (S : set R) : ideal R :=
{
  carrier := {lin_comb | ∃ n : finset ℕ, ∃ r : ℕ → R, ∃ s : ℕ → S, lin_comb = ∑ i in n, r i * s i},
  zero_mem' := begin
    sorry,  
  end,
  add_mem' := sorry,
  smul_mem' := sorry,
}

notation `⟨` S `⟩` := ideal_of_subset S 

-- Aufgabe 2d)
def radical_of_ideal {R : Type} [comm_semiring R] (I : ideal R) : ideal R :=
{
  carrier := {r : R | ∃ n : ℕ, r^n ∈ I},
  zero_mem' := begin
    use 1,
    ring,
    exact I.zero_mem',
  end,
  add_mem' := begin
    intros a b ha hb,
    cases ha with k ha,
    cases hb with l hb,
    use k+l,
    rw add_pow,
    sorry
  end,
  smul_mem' := begin
    intros c x,
    intro h,
    cases h with n h,
    use n,
    dsimp,
    rw mul_pow,
    apply I.smul_mem,
    assumption,
  end,
}

notation `√` I := radical_of_ideal I