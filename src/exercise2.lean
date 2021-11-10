import tactic
import order.galois_connection
import order.closure        -- for closure_operator



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




