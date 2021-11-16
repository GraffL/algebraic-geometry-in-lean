import tactic
import order.galois_connection
import order.closure        -- for closure_operator
import ring_theory.ideal.basic
import algebra.big_operators.basic
import data.nat.choose.sum



universe u 

def f: empty → empty := begin
  intro h,
  cases h,
end

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
  --carrier := {lin_comb | ∃ n : ℕ, ∃ r : ℕ → R, ∃ s : ℕ → S, lin_comb = ∑ i in finset.range(n), r i * s i},
  carrier := {x : R | ∀ I : ideal R, S ⊆ I → x ∈ I},
  zero_mem' := begin
    intros I _,
    exact I.zero_mem',
  end,
  add_mem' := begin
    intros a b ha hb,
    intros I hSI,
    specialize ha I hSI,
    specialize hb I hSI,
    exact I.add_mem' ha hb,  
  end,
  smul_mem' := begin
    intros c x hx,
    intros I hSI,
    specialize hx I hSI,
    exact I.smul_mem' c hx,
  end,
}

-- the unique map from the empty set (type) to any type:
def fempty (N : Type) : (empty → N) :=
begin
  intro h,
  cases h,
end

/-
def ideal_of_subset' {R : Type} [comm_semiring R] (S : set R) : ideal R :=
{
  carrier := {lin_comb | ∃ N : Type, ∃ r : N → R, ∃ s : N → S, ∃ n : finset N, lin_comb = ∑ i in n, r i * s i},
  zero_mem' := begin
    use empty,
    use fempty R,
    use fempty S,
    use ⊤,
    ring_nf,
  end,
  add_mem' := begin
    intros a b ha hb,
    cases ha with Na ha,
    cases ha with ra ha,
    cases ha with sa ha,
    cases ha with na ha,
    cases hb with Nb hb,
    cases hb with rb hb,
    cases hb with sb hb,
    cases hb with nb hb,
    use sum Na Nb,
    have r : sum Na Nb → R := {
      λ x,
      | sum.inl x = ra x
      | sum.inr x = rb x
    },
    use (λ x, r x ),
  end,
  smul_mem' := begin
    intros c x hx,
    intros I hSI,
    specialize hx I hSI,
    exact I.smul_mem' c hx,
  end,
}
-/

notation `⟨` S `⟩` := ideal_of_subset S 

lemma mem_ideal_of_iff {R : Type} [comm_semiring R] {S : set R} {x : R} : 
  x ∈ ⟨S⟩ ↔ ∃ N : Type, ∃ r : N → R, ∃ s : N → S, ∃ n : finset N, x = ∑ i in n, r i * s i :=
begin
  split,
  {
    sorry,
  },
  {
    intro h,
    intros I hSI,
    sorry
  }
end

lemma ideal_of_extensive {R : Type} [comm_semiring R] (S : set R) : S ⊆ ⟨S⟩ :=
begin
  intros s hs,
  intros I hSI,
  apply hSI,
  assumption,
end

lemma ideal_of_mono {R : Type} [comm_semiring R] {S : set R} {T : set R} : S ⊆ T → ⟨S⟩.carrier ⊆ ⟨T⟩.carrier :=
begin
  intro hST,
  intro x,
  intro hx,
  intros I hTI,
  have hSI : S ⊆ I := begin
    exact set.subset.trans hST hTI,
  end,
  specialize hx I hSI,
  assumption,
end

lemma ideal_of_ideal {R : Type} [comm_semiring R] {I : ideal R} : ⟨I.carrier⟩ = I :=
begin
  ext,
  split,
  {
    intro h,
    specialize h I,
    apply h,
    refl,
  },
  {
    intro h,
    intros J hIJ,
    apply hIJ,
    assumption,
  },
end

lemma ideal_of_idempotent {R : Type} [comm_semiring R] {S : set R} : ⟨S⟩ = ⟨⟨S⟩.carrier⟩ :=
begin
  rw ideal_of_ideal,
end

-- The previous three lemmas together show that ⟨_⟩ is a closure operator
--lemma ideal_of_is_clos_op {R : Type} [comm_semiring R] : (closure_operator (λ S, (ideal_of_subset S).carrier))


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

def is_radical {R : Type} [comm_semiring R] (I : ideal R) : Prop :=
  ∀x : R, (∃ n : ℕ, x^n ∈ I) → x ∈ I

lemma radical_of_ideal_is_radical {R : Type} [comm_semiring R] (I : ideal R) : (is_radical √I) := 
begin
  intros x h,
  cases h with n h,
  cases h with m h,
  use n*m,
  rwa pow_mul,
end

lemma radical_of_is_extensive {R : Type} [comm_semiring R] (I : ideal R) : I.carrier ⊆ √ I :=
begin
  intros x hxI,
  use 1,
  simp,
  assumption,
end

lemma radical_of_is_mono {R : Type} [comm_semiring R] {I : ideal R} {J : ideal R} : 
  I.carrier ⊆ J → (√I).carrier ⊆ √J :=
begin
  intro hIJ,
  intros x hxRI,
  cases hxRI with n hxI,
  use n,
  apply hIJ,
  assumption,
end

lemma radical_of_radical {R : Type} [comm_semiring R] {I : ideal R}: (is_radical I) → (√I) = I :=
begin
  intro h,
  ext,
  split,
  {
    intro hxRI,
    apply h,
    exact hxRI,
  },
  {
    apply radical_of_is_extensive I,
  },
end

lemma radical_of_is_idempotent {R : Type} [comm_semiring R] {I : ideal R} : (√I) = √√I :=
begin
  rw radical_of_radical (radical_of_ideal_is_radical I),
end

-- The previous three lemmas together show that √_ is a closure operator
--lemma radical_is_closure_op {R : Type} [comm_semiring R] : (closure_operator (λ (I : ideal R), radical_of_ideal I))

